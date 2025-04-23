import sys

from polygon.ast.expressions.attribute import Attribute
from polygon.ast.expressions.expression import Expression
from polygon.ast.expressions.literal import Literal
from polygon.sql_parser import SQLParser
from polygon.visitors.expression_encoder import ExpressionEncoder
from polygon.visitors.group_expression_encoder import GroupExpressionEncoder
from polygon.smt.ast import EnsureBool, EnsureInt, SMTNode
from polygon.ast.node import Node
from polygon.smt.ast import If, And, Or, Not, Gt, Plus, Eq, Div, Neg, Xor, Implies, Choice, Int, Bool



def main():
    query_text = """
    SELECT
        SUM(col_a) FILTER (WHERE col_b > 10),
        COUNT(*) FILTER (WHERE col_c IS NOT NULL),
        col_c
    FROM T
    WHERE col_d < 15
    HAVING (SUM(col_a) FILTER (WHERE col_b > 0)) > 0
    ORDER BY SUM(col_a) FILTER (WHERE col_c IS NOT NULL)
    """
    # query_text = '''
    #     SELECT SUM(col_a) FILTER (WHERE col_b > 10) AS total
    #     FROM   Sales
    # '''
    # ORDER BY SUM(col_a) FILTER (WHERE col_c IS NOT NULL)
    # GROUP BY col_c
    parser = SQLParser()
    query_str = parser.parse(query_text)
    query_ast = parser.parse_query(query_str)

    print("=== PARSED QUERY AST ===")
    print(query_str)

    #query_ast = parser.parse_query(query_str)
    print("\n=== PARSED QUERY OBJECT ===")
    print(query_ast)
    print("\n")


    class MockColumn:
        def __init__(self, cid):
            self.column_id = cid
    
    class MockSchema:
        def __init__(self):
            self.table_id = 1
            self.bound = 7

        def __getitem__(self, col_name):
            if col_name == "col_a": return MockColumn(0)
            if col_name == "col_b": return MockColumn(1)
            if col_name == "col_c": return MockColumn(2)
            if col_name == "col_d": return MockColumn(3)
            raise KeyError(f"No mock column for '{col_name}'")
        
    class MockCell:
        def __init__(self, table_id, row_id, col_id):
            self.table_id = table_id
            self.row_id   = row_id
            self.col_id   = col_id

        def accept(self, visitor):
            return Int(8), Bool(False)

    class MockDB:
        def __init__(self):
            self.cells = {}

        def __getitem__(self, key):
            if key not in self.cells:
                self.cells[key] = MockCell(*key)
            return self.cells[key]


        def find_table_by_name(self, table_name, env):
            class FakeTable:
                table_id = 1
                bound = 7
            return FakeTable()

    class MockEnv:
        def __init__(self):
            self.db = MockDB()

        def string_hash(self, s:str) -> int:
            return sum(ord(ch) for ch in s)

    schema = MockSchema()
    env    = MockEnv()
    
    aggregator_expr = Expression(
        operator="sum",
        args=[False, Attribute("col_a")],
        agg_filter=Expression(operator="gt", args=[
            Attribute("col_b"),
            Literal(10)
        ])
    )

    aggregator_encoder = ExpressionEncoder(schema, env)
    to_be_aggregated = []
    for row_id in range(schema.bound):
        
        val, null = aggregator_encoder.expression_for_tuple(aggregator_expr.args[1], row_id)
        val = EnsureInt(val)

        
        f_val, f_null = aggregator_encoder.expression_for_tuple(aggregator_expr.agg_filter, row_id)
        f_val = EnsureBool(f_val)

        
        row_included = And([Not(f_null), f_val])
        
        deleted = Not(row_included)

        
        ret = (val, null, deleted)
        to_be_aggregated.append(ret)

        print(f"Row {row_id}: val={val}, null={null}, filter_included={row_included}, deleted={deleted}")

    
    sum_expr = Int(0)
    for (val, null, deleted) in to_be_aggregated:
        sum_expr = sum_expr + If(Or([deleted, null]), Int(0), val)

    print("\nFinal aggregator result expression =>", sum_expr)
    #print("Because all col_b=12 => filter col_b>10 => always true => sum of col_a for all rows => 7*12 => 84")

    




if __name__ == "__main__":
    main()
