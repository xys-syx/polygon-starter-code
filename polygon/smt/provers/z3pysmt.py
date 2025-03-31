import time

from pysmt.exceptions import SolverRedefinitionError
from pysmt.logics import *
from pysmt.shortcuts import *

QF_UFNIRA = Logic(name="QF_UFNIRA",
                  description='',
                  integer_arithmetic=True,
                  real_arithmetic=True,
                  linear=False,
                  quantifier_free=True,
                  uninterpreted=True)

# uninterpreted function definitions
CELL = Symbol('cell', FunctionType(INT, (INT, INT, INT)))
NULL = Symbol('null', FunctionType(BOOL, [INT, INT, INT]))
GROUPING = Symbol('grouping', FunctionType(BOOL, [INT, INT, INT]))
SIZE = Symbol('size', FunctionType(INT, [INT]))


class SMTLIBv2:
    def __init__(self, formula, name, executable_path, executable_options=None):
        if executable_options is None:
            executable_options = []

        env = get_env()
        try:
            env.factory.add_generic_solver(name, [executable_path, *executable_options], [QF_UFNIRA])
        except SolverRedefinitionError:
            pass

        self.formula = formula

        self.visitor = Z3PySMTVisitor()
        self.solver = Solver(name=name)

    def run(self):
        self.solver.add_assertion(self.formula.accept(self.visitor))
        return self.solver.solve()

    def evaluate(self, table_id, db):
        size = self.solver.get_value(SIZE(table_id)).constant_value()
        table = []

        # table header
        table.append([column.column_name for column in db.schemas[table_id]])

        for row_id in range(size):
            row = []
            for column in db.schemas[table_id]:
                if self.solver.get_value(NULL(table_id, row_id, column.column_id)).constant_value():
                    row.append(None)
                else:
                    row.append(
                        self.solver.get_value(CELL(table_id, row_id, column.column_id)).constant_value()
                    )
            table.append(row)
        return table


class Z3PySMTVisitor:
    def visit_SMTCell(self, node):
        return CELL(node.table_id, node.row_id, node.column_id)

    def visit_SMTNull(self, node):
        return NULL(node.table_id, node.row_id, node.column_id)

    def visit_SMTGrouping(self, node):
        return GROUPING(node.table_id, node.tuple_id, node.group_id)

    def visit_SMTSize(self, node):
        return SIZE(node.table_id)

    def visit_And(self, node):
        return And(*[x.accept(self) for x in node.conjunct])

    def visit_Or(self, node):
        return Or(*[x.accept(self) for x in node.disjunct])

    def visit_Xor(self, node):
        return Xor(node.a.accept(self), node.b.accept(self))

    def visit_Not(self, node):
        return Not(node.node.accept(self))

    def visit_Implies(self, node):
        return Implies(node.premise.accept(self), node.conclusion.accept(self))

    def visit_If(self, node):
        return Ite(node.a.accept(self), node.b.accept(self), node.c.accept(self))

    def visit_Gt(self, node):
        return GT(node.a.accept(self), node.b.accept(self))

    def visit_Gte(self, node):
        return GE(node.a.accept(self), node.b.accept(self))

    def visit_Lt(self, node):
        return LT(node.a.accept(self), node.b.accept(self))

    def visit_Lte(self, node):
        return LE(node.a.accept(self), node.b.accept(self))

    def visit_Eq(self, node):
        lhs = node.a.accept(self)
        rhs = node.b.accept(self)
        if str(lhs.get_type()) == 'Bool' and str(rhs.get_type()) == 'Bool':
            return Iff(lhs, rhs)
        return Equals(lhs, rhs)

    def visit_Neq(self, node):
        lhs = node.a.accept(self)
        rhs = node.b.accept(self)
        if str(lhs.get_type()) == 'Bool' and str(rhs.get_type()) == 'Bool':
            return Xor(lhs, rhs)
        return Not(Equals(lhs, rhs))

    def visit_Plus(self, node):
        return Plus(node.a.accept(self), node.b.accept(self))

    def visit_Div(self, node):
        return Div(node.a.accept(self), node.b.accept(self))

    def visit_Int(self, node):
        return Int(node.x)

    def visit_Bool(self, node):
        return Bool(node.x)

    def visit(self, node):
        raise TypeError(node, type(node))
