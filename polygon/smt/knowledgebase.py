from collections import defaultdict

from polygon.smt.ast import *


class KnowledgeBase:
    def __init__(self):
        self.conflicts_learned = {}
        self.next_id = 0

    def add_conflict(self, conflict: dict, labels):
        if not conflict:
            return
        labels = list(filter(lambda x: '$' in x and 'conflict' not in x, labels))
        self.next_id += 1
        f = []
        for table_id, vec in conflict.items():
            vec_f = []
            for bit_id, bit_val in enumerate(vec):
                if bit_val != 'T':
                    vec_f.append(Choice(table_id, bit_id) == Int(bit_val))
            f.append(And(vec_f))
        self.conflicts_learned[f'conflict{self.next_id}_{"&".join(labels)}'] = Not(And(f))

    def get_block_formula(self):
        pass
