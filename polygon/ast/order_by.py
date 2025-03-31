from typing import Optional, List

from polygon.ast.expressions.attribute import Attribute
from polygon.ast.expressions.expression import Expression
from polygon.ast.expressions.literal import Literal
from polygon.ast.node import Node


class OrderBy(Node):
    def __init__(self,
                 expressions: List[Attribute | Literal | Expression],
                 sort_orders: List[bool],
                 limit: Optional[int] = None):
        super().__init__()
        if not isinstance(expressions, list):
            expressions = [expressions]
        if not isinstance(sort_orders, list):
            sort_orders = [sort_orders]
        self.expressions = expressions
        self.sort_orders = sort_orders
        self.limit = limit

    def __str__(self):
        return ', '.join([str(expression) for expression in self.expressions])

    def __repr__(self):
        return f"OrderBy(expressions={repr(self.expressions)}, sort_orders={repr(self.sort_orders)}, limit={repr(self.limit)})"
