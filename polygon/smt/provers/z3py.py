from z3 import *


class Z3Py:
    def __init__(self):
        self.cell = Function('cell', IntSort(), IntSort(), IntSort(), IntSort())
        self.null = Function('null', IntSort(), IntSort(), IntSort(), BoolSort())
        self.size = Function('size', IntSort(), IntSort())

    def visit_SMTCell(self, node):
        return self.cell(node.table_id, node.row_id, node.column_id)

    def visit_SMTNull(self, node):
        return self.null(node.table_id, node.row_id, node.column_id)

    def visit_SMTSize(self, node):
        return self.size(node.table_id)

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
        return If(node.a.accept(self), node.b.accept(self), node.c.accept(self))

    def visit_Gt(self, node):
        return node.a.accept(self) > node.b.accept(self)

    def visit_Gte(self, node):
        return node.a.accept(self) >= node.b.accept(self)

    def visit_Lt(self, node):
        return node.a.accept(self) < node.b.accept(self)

    def visit_Lte(self, node):
        return node.a.accept(self) <= node.b.accept(self)

    def visit_Eq(self, node):
        return node.a.accept(self) == node.b.accept(self)

    def visit_Neq(self, node):
        return node.a.accept(self) != node.b.accept(self)

    def visit_Int(self, node):
        return node.x

    def visit(self, node):
        print(type(node))
