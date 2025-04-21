from typing import Tuple

from polygon.ast.expressions.literal import Literal
from polygon.ast.filter import Filter
from polygon.ast.group_by import GroupBy
from polygon.ast.join import Join
from polygon.ast.node import MutatedNode
from polygon.ast.order_by import OrderBy
from polygon.ast.project import Project
from polygon.ast.query import Query
from polygon.ast.scan import Scan
from polygon.formulas.distinct import FDistinct
from polygon.formulas.filter import FFilter
from polygon.formulas.group_by import FGroupBy
from polygon.formulas.join import *
#from polygon.formulas.mutation import FMutation
from polygon.formulas.order_by import FOrderBy
from polygon.formulas.project import FProject
from polygon.formulas.scan import FScan
from polygon.formulas.union import FUnion
from polygon.schemas import TableSchema
from polygon.smt.ast import Bool
from polygon.utils import copy_group_by_mapping


class Visitor:
    def __init__(self, mutation_type, env):
        self.mutation_type = mutation_type
        self.env = env
        self.original_output_table = None
        self.mutant_output_table = None

    def visit_Query(self, node: Query) -> Tuple[TableSchema, TableSchema]:
        # Query order of execution:

        # 1. FROM
        self.original_output_table, self.mutant_output_table = node.from_clause.accept(self)

        # 2. WHERE
        if node.where_clause is not None:
            self.original_output_table, self.mutant_output_table = node.where_clause.accept(self)

        # 3. GROUP BY / HAVING
        if node.group_by_clause is not None:
            self.original_output_table, self.mutant_output_table = node.group_by_clause.accept(self)

        # 4. SELECT
        self.original_output_table, self.mutant_output_table = node.select_clause.accept(self)

        # 5. ORDER BY
        if self.mutation_type == 'drop_orderby':
            if node.order_by_clause is not None:
                self.original_output_table, self.mutant_output_table = node.order_by_clause.accept(self)

        # alias
        if node.alias is not None:
            self.original_output_table = self.original_output_table.as_aliased(node.alias, self.env)
            if self.original_output_table == self.mutant_output_table:
                self.mutant_output_table = self.original_output_table
            else:
                self.mutant_output_table = self.mutant_output_table.as_aliased(node.alias, self.env)

        return self.original_output_table, self.mutant_output_table

    def visit_Union(self, node) -> Tuple[TableSchema, TableSchema]:
        original_output_tables = []
        mutant_output_tables = []
        for query in node.queries:
            subquery_visitor = Visitor(self.mutation_type, self.env)

            original_output_table, mutant_output_table = query.accept(subquery_visitor)

            original_output_tables.append(original_output_table)
            mutant_output_tables.append(mutant_output_table)

        k = self.env.formulas.under_config[node.label]

        f = FUnion(
            original_output_tables,
            mutant_output_tables,
            node,
            self.env,
            k
        )

        self.original_output_table, self.mutant_output_table = f.original_output, f.mutant_output

        # alias
        if node.alias is not None:
            self.original_output_table = self.original_output_table.as_aliased(node.alias, self.env)
            if self.original_output_table == self.mutant_output_table:
                self.mutant_output_table = self.original_output_table
            else:
                self.mutant_output_table = self.mutant_output_table.as_aliased(node.alias, self.env)

        return self.original_output_table, self.mutant_output_table

    def visit_Scan(self, node: Scan) -> Tuple[TableSchema, TableSchema]:
        output_table = FScan(node.table, self.env).output_table

        # alias
        if node.alias is not None:
            output_table = output_table.as_aliased(node.alias, self.env)

        return output_table, output_table

    def visit_Join(self, node: Join) -> Tuple[TableSchema, TableSchema]:
        original_left, mutant_left = node.left.accept(self)
        original_right, mutant_right = node.right.accept(self)

        match node.join_type:
            case 'join' | 'inner join':
                formula_name = 'FInnerJoin'
            case 'left join' | 'left outer join':
                formula_name = 'FLeftJoin'
            case 'right join' | 'right outer join':
                formula_name = 'FRightJoin'
            case 'full join' | 'full outer join':
                formula_name = 'FFullJoin'
            case 'cross join':
                formula_name = 'FProduct'
            case _:
                raise NotImplementedError(f"Join type {node.join_type} not supported")

        k = self.env.formulas.under_config[node.label]
        # k = max(k, max(original_left.bound, mutant_left.bound))

        def lower_bound(val, minimum):
            if val < minimum:
                return minimum
            return val

        def upper_bound(val, maximum):
            if val > maximum:
                return maximum
            return val

        match formula_name:
            case 'FLeftJoin':
                k = lower_bound(k, min(original_left.bound, mutant_left.bound))
                k = upper_bound(k, max(original_left.bound * original_right.bound, mutant_left.bound * mutant_right.bound))
            case 'FRightJoin':
                k = lower_bound(k, max(original_right.bound, mutant_right.bound))
                k = upper_bound(k, max(original_left.bound * original_right.bound, mutant_left.bound * mutant_right.bound))
            case 'FFullJoin':
                k = lower_bound(k, max(original_left.bound + original_right.bound, mutant_left.bound + mutant_right.bound))
                k = upper_bound(k, max(
                    max(original_left.bound + original_right.bound, mutant_left.bound + mutant_right.bound),
                    max(original_left.bound * original_right.bound, mutant_left.bound * mutant_right.bound)
                ))
            case 'FCrossJoin':
                k = upper_bound(k, max(original_left.bound * original_right.bound, mutant_left.bound * mutant_right.bound))
            case 'FInnerJoin':
                k = upper_bound(k, max(original_left.bound * original_right.bound, mutant_left.bound * mutant_right.bound))
                # print(k)

        if node.condition is None:
            node.condition = Literal(True)

        f = globals()[formula_name](
            original_left, mutant_left,
            original_right, mutant_right,
            node,
            self.env,
            k
        )
        return f.original_output, f.mutant_output

    def visit_GroupBy(self, node: GroupBy) -> Tuple[TableSchema, TableSchema]:
        k = self.env.formulas.under_config[node.label]
        groups_considered = list(range(k + 1))

        f = FGroupBy(self.original_output_table, self.mutant_output_table, node, self.env, groups_considered)
        f.original_output.ctx['groups_considered'] = f.mutant_output.ctx['groups_considered'] = groups_considered
        return f.original_output, f.mutant_output

    def visit_Filter(self, node: Filter) -> Tuple[TableSchema, TableSchema]:
        f = FFilter(self.original_output_table, self.mutant_output_table, node, self.env)
        return f.original_output, f.mutant_output

    def visit_Project(self, node: Project) -> Tuple[TableSchema, TableSchema]:
        f = FProject(self.original_output_table, self.mutant_output_table, node, self.env)
        if node.distinct:
            f = FDistinct(f.original_output, f.mutant_output, self.env)
        return f.original_output, f.mutant_output

    def visit_OrderBy(self, node: OrderBy) -> Tuple[TableSchema, TableSchema]:
        k = self.env.formulas.under_config[node.label]

        f = FOrderBy(self.original_output_table, self.mutant_output_table, node, self.env, k)
        return f.original_output, f.mutant_output

    def visit_MutatedNode(self, node: MutatedNode) -> Tuple[TableSchema, TableSchema]:
        # encode both original and mutant nodes semantics
        original_output_table, _ = node.original.accept(self)
        mutant_output_table, _ = node.mutant.accept(self)

        FMutation(original_output_table, mutant_output_table, node, self.env)

        return original_output_table, mutant_output_table
