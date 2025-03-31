from polygon.ast.expressions.expression import Expression
from polygon.ast.expressions.literal import Literal
from polygon.ast.node import Node


class Filter(Node):
    def __init__(self, predicate: Expression | Literal):
        super().__init__()
        self.predicate = predicate

    def __str__(self):
        return str(self.predicate)

    def __repr__(self):
        return f"Filter(predicate={repr(self.predicate)})"
