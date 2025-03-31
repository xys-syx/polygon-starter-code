from typing import Optional, List

from polygon.ast.expressions.attribute import Attribute
from polygon.ast.expressions.expression import Expression
from polygon.ast.expressions.literal import Literal
from polygon.ast.node import Node


class GroupBy(Node):
    def __init__(self,
                 expressions: List[Attribute | Literal | Expression],
                 having: Optional[Expression | Literal] = None):
        super().__init__()
        self.expressions = expressions
        self.having = having

    def __str__(self):
        group_by_str = ', '.join([str(expression) for expression in self.expressions])
        if self.having is not None:
            group_by_str = f"{group_by_str} HAVING {self.having}"
        return group_by_str

    def __repr__(self):
        return f"GroupBy(expressions={repr(self.expressions)}, having={repr(self.having)})"
