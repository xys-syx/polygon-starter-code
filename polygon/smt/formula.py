import itertools
import random

from bidict import bidict
from copy import deepcopy

from polygon.logger import logger
from polygon.smt.ast import *
from polygon.smt.knowledgebase import KnowledgeBase
from polygon.smt.provers.smtlibv2 import SMTLIBv2Visitor, SMTLIBv2


class FormulaManager:
    def __init__(self, env):
        self.formulas = {}
        self.label_to_node = {}
        self.next_label = 0
        self.node_cur_label = 0
        self.env = env
        self.kb = KnowledgeBase()
        self.timeout = 120

        self.label_to_table_id = None
        self.current_under = {}
        self.labels_considered = set()

        self.under_table_id_to_original = {}
        self.under_config = {}
        self.table_bound = {}

        self.visited_formula_cache = {}

        self.ret = None

    def append(self, f: SMTNode, label: str = None):
        if label is None:
            label = f'f_{self.next_label}'
            self.next_label += 1

        if label in self.formulas:
            # label = f'{label}_{self.next_label}'
            # self.formulas[label] = f
            self.formulas[label] = And([self.formulas[label], f])
            # self.next_label += 1
        else:
            self.formulas[label] = f

    def init_label_table_id_bidict(self):
        label_to_table_id = {}
        for table in self.env.db.schemas.values():
            # print(table.table_id, table.node, table.node.label if table.node is not None else None)
            if table.lineage is not None:
                if 'Duplicate' in table.lineage:
                    assert table.node is not None
                    table_id = table.table_id
                    if table_id in self.under_table_id_to_original:
                        table_id = self.under_table_id_to_original[table.table_id]

                    label_to_table_id[table.node.distinct_label] = table_id
                elif 'Group' in table.lineage:
                    assert table.node is not None
                    table_id = table.table_id
                    if table_id in self.under_table_id_to_original:
                        table_id = self.under_table_id_to_original[table.table_id]

                    label_to_table_id[table.node.label] = table_id
                    label_to_table_id[table.node.group_by_label] = table_id
                elif table.node is not None:
                    table_id = table.table_id
                    if table_id in self.under_table_id_to_original:
                        table_id = self.under_table_id_to_original[table.table_id]

                    label_to_table_id[table.node.label] = table_id

        self.label_to_table_id = label_to_table_id
        logger.debug(self.label_to_table_id)

    def search_naive(self, outputs, ret):
        self.ret = ret
        ret['iters'] = 0
        ret['backtracks'] = 0
        ret['type_2_backtracks'] = 0
        ret['unsat_core_sizes'] = []
        ret['M_sizes'] = []
        ret['solving_time_per_iter'] = []
        ret['num_nodes_changed'] = []
        self.init_label_table_id_bidict()
        ret['ast_size'] = len(self.label_to_table_id)

        prover = SMTLIBv2(
            executable_path='z3',
            executable_options=['--in', f'-T:{self.timeout}'],
        )

        self.labels_considered = list(self.formulas.keys())

        all_nodes = []
        for label in self.formulas.keys():
            if '$' in label:
                all_nodes.append(label)

        node_to_cover_ua = {}
        for label in all_nodes:
            if label in self.label_to_table_id:
                # (1.1)
                # node_to_cover_ua[self.label_to_table_id[label]] = self.cover_ua(label, left_tops=0)
                # (1.2)
                node_to_cover_ua[self.label_to_table_id[label]] = self.cover_ua(label, tops_ratio=0.25)
                # (1.3)
                # node_to_cover_ua[self.label_to_table_id[label]] = self.cover_ua(label)

        labels, cover_ua = zip(*node_to_cover_ua.items())
        for ua_comb in itertools.product(*cover_ua):
            ret['iters'] += 1
            self.current_under = dict(zip(labels, ua_comb))
            # print(self.current_under)
            self.encode_current_under()
            if prover.check(self.dump()):
                for node_label in all_nodes:
                    if node_label not in self.label_to_table_id:
                        continue
                    table = self.env.db.schemas[self.label_to_table_id[node_label]]
                    vec = prover.evaluate_choice_vector(table)
                    self.current_under[table.table_id] = vec
                return prover

        return None

    def search(self, outputs, ret):
        self.ret = ret
        ret['iters'] = 0
        ret['backtracks'] = 0
        ret['type_2_backtracks'] = 0
        ret['unsat_core_sizes'] = []
        ret['M_sizes'] = []
        ret['solving_time_per_iter'] = []
        ret['num_nodes_changed'] = []
        self.init_label_table_id_bidict()
        prover = SMTLIBv2(
            executable_path='z3',
            executable_options=['--in', f'-T:{self.timeout}'],
        )

        ret['ast_size'] = len(self.label_to_table_id)

        remaining = [list(self.formulas.keys())]
        worklist = []
        num_backtracks = 0

        # add formulas that are not operator's encoding
        for label in self.formulas.keys():
            if '$' not in label:
                self.labels_considered.add(label)
                remaining[0].remove(label)

        # init for the first round - add AST root nodes to worklist
        for output in outputs:
            if 'Duplicate' in output.lineage:
                label = output.node.distinct_label
            else:
                label = output.node.label
            remaining = [
                *remaining[0:len(remaining) - 1],
                remaining[len(remaining) - 1][:remaining[len(remaining) - 1].index(label) + 1],
                remaining[len(remaining) - 1][remaining[len(remaining) - 1].index(label) + 1:],
            ]
        remaining = remaining[:-1]
        logger.debug(remaining)
        num_queries = len(remaining)

        if len(remaining) > len(remaining[0]):
            # disambiguation
            for ast_labels in remaining:
                if ast_labels:
                    num_nodes_added = 0
                    for _ in range(len(ast_labels)):
                        label_to_add = ast_labels[-1]
                        num_nodes_added += 1
                        if num_nodes_added > 1:
                            break
                        self.labels_considered.add(label_to_add)
                        worklist.append(label_to_add)
                        # if label_to_add in self.label_to_table_id:
                        #     self.current_under[self.label_to_table_id[label_to_add]] = [0] * 99
                        del ast_labels[-1]
            for _ in range(1):
                for label in remaining[0]:
                    self.labels_considered.add(label)
                    # if label in self.label_to_table_id:
                    #     self.current_under[self.label_to_table_id[label]] = [0] * 99
                for label in remaining[-1]:
                    self.labels_considered.add(label)
                    # if label in self.label_to_table_id:
                    #     self.current_under[self.label_to_table_id[label]] = [0] * 99
                del remaining[0]
                del remaining[-1]
        else:
            for ast_labels in remaining:
                if ast_labels:
                    num_nodes_added = 0
                    for _ in range(len(ast_labels)):
                        if num_nodes_added >= 1:
                            break
                        label_to_add = ast_labels[-1]
                        num_nodes_added += 1
                        self.labels_considered.add(label_to_add)
                        worklist.append(label_to_add)
                        # if label_to_add in self.label_to_table_id:
                        #     self.current_under[self.label_to_table_id[label_to_add]] = [0] * 99
                        del ast_labels[-1]

                        # if 'project' in label_to_add and 'group' in ast_labels[-1]:
                        #     label_to_add = ast_labels[-1]
                        #     self.labels_considered.add(label_to_add)
                        #     worklist.append(label_to_add)
                        #     del ast_labels[-1]

        while worklist:
            ret['iters'] += 1
            # print(worklist, self.labels_considered, remaining)
            self.encode_current_under()
            logger.debug(f'current under: {self.current_under}')
            # for table_id in self.label_to_table_id.values():
            #     table = self.env.db.schemas[table_id]
            #     try:
            #         vec = prover.evaluate_choice_vector(table)
            #         print(table_id, vec)
            #     except:
            #         pass

            logger.debug(1)
            if not prover.check(self.dump()):
                logger.debug(2)
                # backtrack
                logger.debug('backtrack')

                # record experiment data
                ret['backtracks'] += 1
                ret['unsat_core_sizes'] = [*deepcopy(ret['unsat_core_sizes']), len(list(filter(lambda x: '$' in x, prover.unsat_core)))]
                ret['M_sizes'] = [*deepcopy(ret['M_sizes']), len([v for v in self.labels_considered if '$' in v])]
                if 'neq' in prover.unsat_core or 'disambiguation' in prover.unsat_core:
                    ret['type_2_backtracks'] += 1
                num_backtracks += 1

                unsat_core = []
                for label in prover.unsat_core:
                    if 'conflict' in label:
                        conflict_node_labels = label[label.index('_') + 1:].split('&')
                        unsat_core.extend(conflict_node_labels)
                    else:
                        unsat_core.append(label)

                self.add_kb(unsat_core)
                # self.add_kb(self.labels_considered)
                # if self.backtrack(self.labels_considered, ret) is None:
                if self.backtrack(unsat_core, ret) is None:
                    logger.debug('backtrack failed')
                    return None
                continue

            # print('solving time', prover.checking_time)
            ret['solving_time_per_iter'] = [*deepcopy(ret['solving_time_per_iter']), prover.checking_time]

            for node_to_get_choice in worklist:
                table = self.env.db.schemas[self.label_to_table_id[node_to_get_choice]]
                vec = prover.evaluate_choice_vector(table)
                # heuristics to consider a subset
                # vec = ['T' if bit == 0 else bit for bit in vec]
                self.current_under[table.table_id] = vec

            worklist = []
            # for ast_labels in remaining:
            #     if ast_labels:
            #         label_to_add = ast_labels[-1]
            #         self.labels_considered.add(label_to_add)
            #         worklist.append(label_to_add)
            #         del ast_labels[-1]
            for _ in range(max(25, 1)):
                if remaining:
                    for label in remaining[0]:
                        self.labels_considered.add(label)
                        worklist.append(label)
                        # if label in self.label_to_table_id:
                        #     self.current_under[self.label_to_table_id[label]] = [0] * 99
                    del remaining[0]
                if remaining:
                    for label in remaining[-1]:
                        self.labels_considered.add(label)
                        worklist.append(label)
                        # if label in self.label_to_table_id:
                        #     self.current_under[self.label_to_table_id[label]] = [0] * 99
                    del remaining[-1]
                else:
                    break

        # for table_id in self.label_to_table_id.values():
        #     table = self.env.db.schemas[table_id]
        #     vec = prover.evaluate_choice_vector(table)
        #     print(table_id, vec)
        logger.debug(f'Final under: {self.current_under}')
        logger.debug(f'#Backtracks: {num_backtracks}')
        return prover

    def backtrack(self, unsat_core, ret):
        logger.debug(f'unsat core: {unsat_core}')
        prover = SMTLIBv2(
            executable_path='z3',
            executable_options=['--in', f'-T:{self.timeout}'],
        )

        prev_labels_considered = deepcopy(self.labels_considered)

        # for node_label in unsat_core:
        #     if node_label not in self.label_to_table_id:
        #         continue
        #     table = self.env.db.schemas[self.label_to_table_id[node_label]]
        #     if table.table_id in self.current_under:
        #         del self.current_under[table.table_id]
        prev_under = deepcopy(self.current_under)
        self.current_under = {}

        # if 'under' in self.formulas:
        #     del self.formulas['under']
        self.labels_considered = unsat_core

        node_to_cover_ua = {}
        for label in unsat_core:
            if label in self.label_to_table_id:
                node_to_cover_ua[self.label_to_table_id[label]] = self.cover_ua(label, left_tops=8)

        labels, cover_ua = zip(*node_to_cover_ua.items())
        for ua_comb in itertools.product(*cover_ua):
            self.current_under = dict(zip(labels, ua_comb))
            logger.debug(f'trying partition {self.current_under}')
            # print(self.current_under)
            self.encode_current_under()
            if prover.check(self.dump()):
                for node_label in unsat_core:
                    if node_label not in self.label_to_table_id:
                        continue
                    table = self.env.db.schemas[self.label_to_table_id[node_label]]
                    vec = prover.evaluate_choice_vector(table)
                    # heuristics to consider a subset
                    # vec = ['T' if bit == 0 else bit for bit in vec]
                    self.current_under[table.table_id] = vec
                self.labels_considered = prev_labels_considered
                self.encode_current_under()

                all_keys = set(prev_under.keys()) | set(self.current_under.keys())

                changes = 0

                for key in all_keys:
                    if key not in prev_under:
                        changes += 1
                    elif key not in self.current_under:
                        changes += 1
                    elif prev_under[key] != self.current_under[key]:
                        changes += 1
                ret['num_nodes_changed'] = [*deepcopy(ret['num_nodes_changed']), changes]

                return True
            self.add_kb(unsat_core)

        return None
        # all_top = False
        # while not all_top:
        #     logger.debug(3)
        #     self.encode_current_under()
        #     if prover.check(self.dump()):
        #         logger.debug(4)
        #         for node_label in unsat_core:
        #             if node_label not in self.label_to_table_id:
        #                 continue
        #             table = self.env.db.schemas[self.label_to_table_id[node_label]]
        #             vec = prover.evaluate_choice_vector(table)
        #             # heuristics to consider a subset
        #             # vec = ['T' if bit == 0 else bit for bit in vec]
        #             self.current_under[table.table_id] = vec
        #
        #         self.labels_considered = prev_labels_considered
        #         self.encode_current_under()
        #         return True
        #
        #     unsat_core = prover.unsat_core
        #     self.add_kb(unsat_core)
        #     # partition
        #     all_top = True
        #     for table_id, vec in self.current_under.items():
        #         if any(bit != 'T' for bit in vec):
        #             all_top = False
        #             num_turned_into_t = 0
        #             for bit_id in range(len(vec)):
        #                 if vec[bit_id] != 'T':
        #                     vec[bit_id] = 'T'
        #                     num_turned_into_t += 1
        #                 if num_turned_into_t >= len(vec) / 3:
        #                     break
            # self.add_kb(self.labels_considered)
            #
            # del self.formulas['under']
            #
            # logger.debug(3)
            # if prover.check(self.dump()):
            #     logger.debug(4)
            #     for node_label in unsat_core:
            #         if node_label not in self.label_to_table_id:
            #             continue
            #         table = self.env.db.schemas[self.label_to_table_id[node_label]]
            #         vec = prover.evaluate_choice_vector(table)
            #         # heuristics to consider a subset
            #         vec = ['T' if bit == 1 else bit for bit in vec]
            #         self.current_under[table.table_id] = vec
            # else:
            #
            #     return None

        # self.labels_considered = prev_labels_considered
        # self.encode_current_under()
        # return True

    def cover_ua(self, node_label, left_tops=None, right_tops=None, left_right_tops=None, tops_ratio=None):
        table = self.env.db.schemas[self.label_to_table_id[node_label]]
        vec_size = table.bound

        if 'Sorted' in table.lineage:
            yield ['T'] * vec_size
        elif left_right_tops is not None and left_right_tops * 2 < vec_size:
            for cover in [list(x) for x in itertools.product([0, 1], repeat=vec_size - left_right_tops * 2)]:
                vec = ['T'] * left_right_tops + cover + ['T'] * left_right_tops
                if table.lineage is not None and 'Grouped' in table.lineage:
                    vec = vec * 2
                yield vec
        elif left_tops is not None and left_tops < vec_size:
            for cover in [list(x) for x in itertools.product([0, 1], repeat=vec_size - left_tops)]:
                vec = ['T'] * left_tops + cover
                if table.lineage is not None and 'Grouped' in table.lineage:
                    vec = vec * 2
                yield vec
        elif right_tops is not None and right_tops < vec_size:
            for cover in [list(x) for x in itertools.product([0, 1], repeat=vec_size - right_tops)]:
                vec = cover + ['T'] * right_tops
                if table.lineage is not None and 'Grouped' in table.lineage:
                    vec = vec * 2
                yield vec
        elif tops_ratio is not None:
            random.seed(123456)
            num_tops = int(vec_size * tops_ratio)
            top_indices = random.sample(range(0, vec_size), num_tops)
            for cover in [list(x) for x in itertools.product([0, 1], repeat=vec_size - num_tops)]:
                cover = list(cover)
                next_cover_idx = 0
                vec = []
                for i in range(vec_size):
                    if i in top_indices:
                        vec.append('T')
                    else:
                        vec.append(cover[next_cover_idx])
                        next_cover_idx += 1
                if table.lineage is not None and 'Grouped' in table.lineage:
                    vec = vec * 2
                yield vec
        else:
            yield ['T'] * vec_size

    def add_kb(self, unsat_core):
        conflict = {}
        for node_label in unsat_core:
            if node_label not in self.label_to_table_id:
                continue
            table = self.env.db.schemas[self.label_to_table_id[node_label]]
            if table.table_id in self.current_under:
                conflict[table.table_id] = self.current_under[table.table_id]

        self.kb.add_conflict(conflict, labels=unsat_core)
        logger.debug(f'new conflict learned: {conflict}, {unsat_core}')

    def encode_current_under(self):
        if not self.current_under:
            if 'under' in self.formulas:
                del self.formulas['under']
            return
        f = []
        for table_id, vec in self.current_under.items():
            for bit_id, bit_val in enumerate(vec):
                if bit_val != 'T':
                    f.append(Choice(table_id, bit_id) == Int(bit_val))
        self.formulas['under'] = And(f)

    def solve_precise(self, ret):
        self.ret = ret
        ret['backtracks'] = 0
        ret['type_2_backtracks'] = 0
        ret['unsat_core_sizes'] = []
        ret['M_sizes'] = []
        ret['solving_time_per_iter'] = []
        self.init_label_table_id_bidict()
        prover = SMTLIBv2(
            executable_path='z3',
            executable_options=['--in', f'-T:300'],
        )

        # self.current_under = {
        #     1: ['T', 'T', 0, 0, 'T', 'T', 0, 0],
        #     2: ['T', 'T', 'T', 'T'],
        #     3: [1, 'T', 0, 0],
        #     4: ['T', 'T', 0, 0, 'T', 'T', 0, 0]
        #     # 4: [1, 0, 0, 0, 1, 0, 0, 0]
        # }
        # self.encode_current_under()

        for label in self.formulas:
            self.labels_considered.add(label)

        if prover.check(self.dump()):
            for table_id in self.label_to_table_id.values():
                table = self.env.db.schemas[table_id]
                vec = prover.evaluate_choice_vector(table)
                print(table_id, vec)
            return prover
        else:
            pass
            # print(prover.unsat_core)
        return None

    def dump(self):
        visitor = SMTLIBv2Visitor()
        out = ''
        for label, formula in self.formulas.items():
            if '$' in label and label not in self.labels_considered:
                continue
            # print(label)

            # cache operator encodings since they will not change
            if '$' in label or 'scan' in label or label in ['ic', 'neq', 'disambiguation']:
                if label not in self.visited_formula_cache:
                    self.visited_formula_cache[label] = formula.accept(visitor)
                formula_smt_lib = self.visited_formula_cache[label]
            else:
                formula_smt_lib = formula.accept(visitor)
            out = f'{out}\n(assert (! {formula_smt_lib} :named {label}))'

        for conflict_name, formula in self.kb.conflicts_learned.items():
            out = f'{out}\n(assert (! {formula.accept(visitor)} :named {conflict_name}))'

        return out

    def next_node_label(self):
        self.node_cur_label += 1
        return self.node_cur_label
