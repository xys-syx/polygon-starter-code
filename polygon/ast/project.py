from typing import (
    List, Optional,
)

from polygon.ast.expressions.attribute import Attribute
from polygon.ast.expressions.expression import Expression
from polygon.ast.expressions.literal import Literal
from polygon.ast.node import Node


class Project(Node):
    def __init__(self, target_list: List[Attribute | Expression | Literal], distinct: Optional[bool] = False):
        super().__init__()
        self.target_list = target_list
        self.distinct = distinct
        self.group_by_label = None
        self.distinct_label = None

    def __str__(self):
        return ('DISTINCT ' if self.distinct else '') + ', '.join([str(target) for target in self.target_list])

    def __repr__(self):
        return f"Project(target_list={repr(self.target_list)}, distinct={repr(self.distinct)})"
