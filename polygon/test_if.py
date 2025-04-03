import sys

from polygon.sql_parser import SQLParser
from polygon.visitors.expression_encoder import ExpressionEncoder
from polygon.smt.ast import SMTNode
from polygon.ast.node import Node
from polygon.smt.ast import If, And, Or, Not, Gt, Plus, Eq, Div, Neg, Xor, Implies, Choice, Int, Bool

def print_smt_ast(node: SMTNode, indent=0):
    prefix = "  " * indent
    print(f"{prefix}{node}")

    
    if isinstance(node, If):
        print_smt_ast(node.a, indent+1)
        print_smt_ast(node.b, indent+1)
        print_smt_ast(node.c, indent+1)
    elif isinstance(node, And):
        for c in node.conjunct:
            print_smt_ast(c, indent+1)
    elif isinstance(node, Or):
        for d in node.disjunct:
            print_smt_ast(d, indent+1)



def main():
    query_text = """
    SELECT
      IF(col_a > 10, col_b, 0) AS expr_b,
      col_c
    FROM T
    WHERE col_d < 100
    GROUP BY col_c
    HAVING SUM(col_a) > 50
    """

    parser = SQLParser()
    query_str = parser.parse(query_text)
    #query_ast = parser.parse_query(query_str)

    print("=== PARSED QUERY AST ===")
    print(query_str)

    query_ast = parser.parse_query(query_str)
    print("\n=== PARSED QUERY OBJECT ===")
    print(query_ast)

    class MockColumn:
        def __init__(self, cid):
            self.column_id = cid
    
    class MockSchema:
        def __init__(self):
            self.table_id = 1
            self.bound = 3

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
            return Int(999), Bool(False)

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
                bound = 3
            return FakeTable()

    class MockEnv:
        def __init__(self):
            self.db = MockDB()

        def string_hash(self, s):
            return sum(ord(ch) for ch in s)

    schema = MockSchema()
    env    = MockEnv()
    encoder = ExpressionEncoder(schema, env)


    select_project = query_ast.select_clause
    if not select_project:
        print("No SELECT clause found - unexpected.")
        return

    print("\n=== SMT AST FOR SELECT CLAUSE ===")
    for expr in select_project.target_list:
        val_ast, null_ast = encoder.expression_for_tuple(expr, idx=0)
        print(f"--- SELECT Expression: {expr}")
        print("val AST:")
        print_smt_ast(val_ast, 1)
        print("null AST:")
        print_smt_ast(null_ast, 1)
        print()

    if query_ast.group_by_clause and query_ast.group_by_clause.having:
        having_expr = query_ast.group_by_clause.having
        val_ast, null_ast = encoder.expression_for_tuple(having_expr, idx=0)
        print("=== SMT AST FOR HAVING CLAUSE ===")
        print("HAVING Expression val:")
        print_smt_ast(val_ast, 1)
        print("HAVING null flag:")
        print_smt_ast(null_ast, 1)
    else:
        print("No HAVING clause found or no group_by_clause.")

    print("\nDone.")

if __name__ == "__main__":
    main()
