import datetime
import traceback
import multiprocess.pool
import numpy as np

from functools import cache
from typing import Tuple

from polygon.ast.expressions.attribute import Attribute
from polygon.ast.expressions.literal import Literal
from polygon.formulas.integrity_constraint import encode_integrity_constraints
from polygon.logger import logger
#from polygon.mutation import generate_mutants
from polygon.schemas import *
from polygon.smt.ast import *
from polygon.smt.formula import FormulaManager
from polygon.smt.provers.smtlibv2 import SMTLIBv2
from polygon.sql_parser import SQLParser
from polygon.utils import create_empty_table
from polygon.variables import *
from polygon.visitors.expression_encoder import ExpressionEncoder
from polygon.visitors.initializer import Initializer
from polygon.visitors.query_encoder import QueryEncoder
from polygon.visitors.underapproximator import Underapproximator
from polygon.visitors.visitor import Visitor


class Environment:
    def __init__(self, schema, constraints, bound=2, time_budget=60, default_k=None):
        self.db = Database()
        self.bound_size = bound
        self.table_id_counter = -1

        self.schema = schema
        self.constraints = constraints

        self.time_budget = time_budget
        self.integrity_constraints = []
        self.formulas = FormulaManager(self)
        self.formulas.timeout = self.time_budget

        # z3 variables
        self.cell = SMTCell
        self.null = SMTNull
        self.size = SMTSize
        self.grouping = SMTGrouping

        self.string_hash_table = {}
        self.hash_string_table = {}
        self.curr_query_id = None

        # for testing
        self.unsat_mutants = []
        self.mutants = None
        self.groundtruth = None
        self.databases = None

        self.stats = {}

        self.load_schema(schema)

        self.underapproximator = Underapproximator(self)
        self.initialized = False
        if default_k is not None:
            self.default_k = default_k
        else:
            # self.default_k = {
            #     'filter': 3,
            #     'project': 3,
            #     'union': 3,
            #     'inner join': 3,
            #     'left join': 3,
            #     'right join': 3,
            #     'full join': 3,
            #     'product': 3,
            #     'order by': 3
            # }
            self.default_k = {
                'filter': 2,
                'project': 2,
                'union': 2,
                'inner join': 2,
                'left join': 2,
                'right join': 2,
                'full join': 2,
                'product': 2,
                'order by': 2
            }

        self.formulas.append(encode_integrity_constraints(self.constraints, self), label='ic')

    def next_table_id(self) -> int:
        self.table_id_counter += 1
        return self.table_id_counter

    def string_hash(self, string: str) -> int:
        if not isinstance(string, str):
            string = str(string)

        if string in self.string_hash_table:
            return self.string_hash_table[string]

        try:
            h = int(string)
        except:
            h = hash(string)
        self.string_hash_table[string] = h
        self.hash_string_table[h] = string

        return h

    def lookup_string(self, string_hash: int) -> str:
        if string_hash in self.hash_string_table:
            return self.hash_string_table[string_hash]

        candidates = list(self.hash_string_table.values())
        if len(candidates) > 0:
            return candidates[string_hash % len(candidates)] + str(string_hash)
        return str(string_hash)

    def load_schema(self, schema: list):
        self.integrity_constraints = []
        enum_constraints = []
        for idx, table in enumerate(schema):
            table_id = self.next_table_id()
            table_name = table["TableName"].lower()
            table_bound = self.bound_size
            table_schema = TableSchema(table_id, table_name, table_bound)
            column_id = 0
            for col in table['PKeys']:
                column_name = col['Name'].lower()
                data_type = col['Type'].split(',')[0]
                if data_type == 'enum':
                    enum = col['Type'].split(',')[1:]
                    enum_constraints.append({'enum': [f'{table_name}.{column_name}', enum]})
                    data_type = 'varchar'
                column_schema = ColumnSchema(column_id, column_name, data_type, table_name=table_name)
                column_id += 1
                table_schema.append(column_schema)
            for col in table['FKeys']:
                column_name = col['FName'].lower()
                has_column = False
                for column in table_schema.columns:
                    if column.column_name == column_name:
                        has_column = True
                        break
                if has_column:
                    continue
                p_table = int(col["PTable"])
                p_name = col["PName"]
                p_cols = schema[p_table]["PKeys"]
                data_type = None
                for p_col in p_cols:
                    if p_col["Name"] == p_name:
                        data_type = p_col["Type"].split(',')[0]
                        break
                if data_type == 'enum':
                    enum = col['Type'].split(',')[1:]
                    enum_constraints.append({'enum': [f'{table_name}.{column_name}', enum]})
                    data_type = 'varchar'
                column_schema = ColumnSchema(column_id, column_name, data_type, table_name=table_name)
                if column_schema in table_schema:
                    continue
                column_id += 1
                table_schema.append(column_schema)
            for col in table['Others']:
                column_name = col['Name'].lower()
                has_column = False
                for column in table_schema.columns:
                    if column.column_name == column_name:
                        has_column = True
                        break
                if has_column:
                    continue
                data_type = col['Type'].split(',')[0]
                if data_type == 'enum':
                    enum = col['Type'].split(',')[1:]
                    enum_constraints.append({'enum': [f'{table_name}.{column_name}', enum]})
                    data_type = 'varchar'
                column_schema = ColumnSchema(column_id, column_name, data_type, table_name=table_name)
                if column_schema in table_schema:
                    continue
                column_id += 1
                table_schema.append(column_schema)
            self.db.add_table(table_schema)
            # self.formulas.append(And([self.size(table_id) >= Int(1), self.size(table_id) <= Int(table_bound)]), label=f'size_{table_name}')
            self.constraints.extend(enum_constraints)

        # add integrity constraints from schema
        for idx, table in enumerate(schema):
            table_name = table["TableName"].lower()
            if len(table['PKeys']) > 0:
                self.constraints.append(
                    {'primary': [f"{table_name}.{column['Name'].lower()}" for column in table['PKeys']]}
                )

            for col in table['FKeys']:
                column_name = col['FName'].lower()
                p_table_name = schema[int(col["PTable"])]["TableName"].lower()
                p_name = col["PName"].lower()
                self.constraints.append(
                    {'eq': [f"{table_name}.{column_name}", f"{p_table_name}.{p_name}"]}
                )

    def gen_db(self, query: str):
        # parse
        parser = SQLParser()
        json = parser.parse(query)
        ast = parser.parse_query(json)

        # mutate
        self.mutants = generate_mutants(ast)

        databases = []

        num_mutants = 0
        num_relax_coll = []
        total_time_coll = []
        unsat_core_time_coll = []
        other_time_coll = []
        size_unsat_core_coll = []
        size_raw_unsat_core_coll = []
        size_ast_coll = []

        num_timeout = 0

        num_relax_timeout_coll = []
        size_unsat_core_timeout_coll = []

        for mutation_type in self.mutants:
            for mutated in self.mutants[mutation_type]:
                num_mutants += 1
                # if 'HAVING COUNT(*) > ' not in str(mutated):
                #     continue
                print(mutation_type, mutated)

                # encode
                initializer = Initializer(self)
                visitor = Visitor(mutation_type, self)

                # start = time.time()
                mutated.accept(initializer)
                size_ast_coll.append(initializer.cur_label + len(self.db.schemas))
                # o1_neq_o2 = []
                # for size in range(1, min(o1.bound, o2.bound) + 1):
                #     case = []
                #     for idx in range(size):
                #         for column in o1:
                #             case.append(Or([
                #                 self.null(o1.table_id, idx, column.column_id) != self.null(o2.table_id, idx,
                #                                                                            column.column_id),
                #                 self.cell(o1.table_id, idx, column.column_id) != self.cell(o2.table_id, idx,
                #                                                                            column.column_id)
                #             ]))
                #     case = Implies(
                #         self.size(o1.table_id) == Int(size),
                #         Or(case)
                #     )
                #     o1_neq_o2.append(case)
                # self.formulas.append(
                #     Or([
                #         self.size(o1.table_id) != self.size(o2.table_id),
                #         And([And(o1_neq_o2), ])
                #     ]),
                #     label='o1neqo2'
                # )

                # self.formulas.append(And([
                #     self.size(len(self.db.tables) - 2) > Int(0)
                # ]))
                # end = time.time()
                # print(f'traversing time: {end - start}')

                # model check

                # prover = SMTLIBv2(
                #     formula=And(self.formulas),
                #     name='z3-cli',
                #     executable_path='z3',
                #     executable_options=['--in']
                # )

                # self.formulas.append(self.size(2) > Int(1))
                # self.formulas.append(Not(self.null(0, 0, 5)))
                # self.formulas.append(Not(self.null(0, 1, 5)))

                time_budget = 5
                prover = SMTLIBv2(
                    self.formulas,
                    executable_path='z3',
                    executable_options=['--in', f'-T:{time_budget}'],
                )

                def task(queue, num_relax_timeout, unsat_core_sizes):
                    start = datetime.datetime.now()

                    unsat_core_time = 0
                    max_rounds = 10000
                    cur_rounds = 0
                    size_unsat_core = 0
                    raw_size_unsat_core = 0

                    relaxation_enabled = True
                    # relaxation_enabled = False

                    while True:
                        # mutated.accept(visitor)

                        try:
                            o1, o2 = mutated.accept(visitor)
                            # print(o1.table_id, o2.table_id)

                            o1_neq_o2 = []
                            for size in range(1, min(o1.bound, o2.bound) + 1):
                                case = []
                                for idx in range(size):
                                    for column in o1:
                                        case.append(Or([
                                            self.null(o1.table_id, idx, column.column_id) != self.null(o2.table_id, idx, column.column_id),
                                            self.cell(o1.table_id, idx, column.column_id) != self.cell(o2.table_id, idx, column.column_id)
                                        ]))
                                case = Implies(
                                    self.size(o1.table_id) == Int(size),
                                    Or(case)
                                )
                                o1_neq_o2.append(case)
                            self.formulas.append(
                                Or([
                                    self.size(o1.table_id) != self.size(o2.table_id),
                                    And([Or([self.size(o1.table_id) > Int(0), self.size(o2.table_id) > Int(0)]), And(o1_neq_o2)])
                                ]),
                                label='o1neqo2'
                            )
                        except Exception as e:
                            logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                            break

                        self.formulas.append(And(self.underapproximator.underapproximation_constraints), label='op_under')

                        if prover.run():
                            # mutated.str_mutant_only = False
                            # mutated.from_clause.where_clause.str_mutant_only = False

                            # print(prover.evaluate_table(o1.table_id, self.db, self))
                            # print(prover.evaluate_table(o2.table_id, self.db, self))

                            database = {}
                            try:
                                for table_idx in range(len(self.schema)):
                                    database[self.schema[table_idx]["TableName"].lower()] = prover.evaluate_table(table_idx, self.db, self)

                                total_time = (datetime.datetime.now() - start).total_seconds()
                                queue.put({
                                    'database': database,
                                    'unsat_core_time': unsat_core_time,
                                    'other_time': total_time - unsat_core_time,
                                    'num_relax': cur_rounds,
                                    'size_unsat_core': size_unsat_core / cur_rounds if cur_rounds != 0 else None,
                                    'size_raw_unsat_core': raw_size_unsat_core / cur_rounds if cur_rounds != 0 else None,
                                })
                                logger.info(database)
                                # databases.append(database)
                                # return database
                            except Exception as e:
                                pass

                            # print(mutated)
                            # print(self.db)
                            # logger.debug(database)
                            # print(prover.evaluate(1, self.db))
                            # print(prover.evaluate(2, self.db))
                            # print(prover.evaluate_table(3, self.db, self))
                            # print(prover.evaluate_table(4, self.db, self))
                            # print(prover.evaluate(5, self.db))
                            # print(prover.evaluate(6, self.db))
                            # print(prover.evaluate(7, self.db))
                            # print(prover.solver.get_value(GROUPING(1, 0, 0)).constant_value())
                            # print(prover.solver.get_value(GROUPING(1, 0, 1)).constant_value())
                            break
                        else:
                            if relaxation_enabled and cur_rounds <= max_rounds and prover.unsat_core is not None:
                                unsat_core_time += prover.unsat_core_time
                                num_relax_timeout.value = cur_rounds

                                cur_rounds += 1

                                len_unsat_core = 0
                                for x in self.formulas.under_config:
                                    if x in self.formulas.under_config or 'size' in x:
                                        len_unsat_core += 1
                                    else:
                                        if 'size' not in x and self.formulas.label_to_node[x].parent is not None:
                                            for node2 in self.formulas.label_to_node[x].parent:
                                                if node2.label in self.formulas.under_config or 'size' in node2.label:
                                                    len_unsat_core += 1
                                                    break

                                # size_unsat_core += len(list(filter(lambda x: x in self.formulas.under_config or 'size' in x, prover.unsat_core)))
                                # unsat_core_sizes.append(len(list(filter(lambda x: x in self.formulas.under_config or 'size' in x, prover.unsat_core))))
                                size_unsat_core += len_unsat_core
                                unsat_core_sizes.append(len_unsat_core)

                                self.formulas.relax(prover.unsat_core)

                                # reset
                                self.formulas.formulas = {}
                                self.formulas.next_label = 0

                                self.db = Database()
                                self.table_id_counter = -1
                                self.string_hash_table = {}
                                self.hash_string_table = {}
                                self.load_schema(self.schema)
                                self.add_integrity_constraints(self.constraints)
                                # self.formulas.append(And(self.integrity_constraints), label='ic')
                                self.underapproximator = Underapproximator(self)
                            else:
                                self.unsat_mutants.append(str(mutated))
                                logger.debug(f"Formula unsat for mutant: {mutated}")
                                break

                # try:
                #     task()
                # except TimeoutError:
                #     print('mutant timeout')

                # try:

                with multiprocess.Manager() as manager:
                    num_relax_timeout = manager.Value(int, 0)
                    unsat_core_sizes = manager.list()

                    queue = multiprocess.Queue()
                    process = multiprocess.Process(target=task, args=(queue, num_relax_timeout, unsat_core_sizes))
                    process.start()

                    process.join(time_budget)

                    while not queue.empty():
                        result = queue.get()
                        databases.append(result['database'])

                        num_relax_coll.append(result['num_relax'])
                        total_time_coll.append(result['unsat_core_time'] + result['other_time'])
                        unsat_core_time_coll.append(result['unsat_core_time'])
                        other_time_coll.append(result['other_time'])
                        size_unsat_core_coll.append(result['size_unsat_core'])
                        size_raw_unsat_core_coll.append(result['size_raw_unsat_core'])

                    if process.is_alive():
                        process.terminate()
                        num_timeout += 1
                        num_relax_timeout = num_relax_timeout.value
                        unsat_core_sizes = list(unsat_core_sizes)
                        num_relax_timeout_coll.append(num_relax_timeout)
                        size_unsat_core_timeout_coll.append(sum(unsat_core_sizes) / len(unsat_core_sizes) if len(unsat_core_sizes) > 0 else None)
                        print('mutant timeout')

                self.clear()

                # break
            # break

        self.groundtruth = query
        self.databases = databases

        total_time_coll = np.array([x for x in total_time_coll if x is not None])
        num_relax_coll = np.array([x for x in num_relax_coll if x is not None])
        size_ast_coll = np.array([x for x in size_ast_coll if x is not None])
        size_unsat_core_coll = np.array([x for x in size_unsat_core_coll if x is not None])
        size_raw_unsat_core_coll = np.array([x for x in size_raw_unsat_core_coll if x is not None])
        unsat_core_time_coll = np.array([x for x in unsat_core_time_coll if x is not None])
        other_time_coll = np.array([x for x in other_time_coll if x is not None])

        num_relax_timeout_coll = np.array([x for x in num_relax_timeout_coll if x is not None])
        size_unsat_core_timeout_coll = np.array([x for x in size_unsat_core_timeout_coll if x is not None])

        self.stats = {
            'num_mutants': num_mutants,
            'num_timeout': num_timeout,
            'total_time_avg': np.mean(total_time_coll) if total_time_coll.size > 0 else None,
            'total_time_25th': np.percentile(total_time_coll, 25) if total_time_coll.size > 0 else None,
            'total_time_50th': np.percentile(total_time_coll, 50) if total_time_coll.size > 0 else None,
            'total_time_75th': np.percentile(total_time_coll, 75) if total_time_coll.size > 0 else None,
            'total_time_min': np.min(total_time_coll) if total_time_coll.size > 0 else None,
            'total_time_max': np.max(total_time_coll) if total_time_coll.size > 0 else None,

            'num_relax_avg': np.mean(num_relax_coll) if num_relax_coll.size > 0 else None,
            'num_relax_25th': np.percentile(num_relax_coll, 25) if num_relax_coll.size > 0 else None,
            'num_relax_50th': np.percentile(num_relax_coll, 50) if num_relax_coll.size > 0 else None,
            'num_relax_75th': np.percentile(num_relax_coll, 75) if num_relax_coll.size > 0 else None,
            'num_relax_min': np.min(num_relax_coll) if num_relax_coll.size > 0 else None,
            'num_relax_max': np.max(num_relax_coll) if num_relax_coll.size > 0 else None,

            'size_ast_avg': np.mean(size_ast_coll) if size_ast_coll.size > 0 else None,

            'size_unsat_core_avg': np.mean(size_unsat_core_coll) if size_unsat_core_coll.size > 0 else None,
            'size_unsat_core_25th': np.percentile(size_unsat_core_coll, 25) if size_unsat_core_coll.size > 0 else None,
            'size_unsat_core_50th': np.percentile(size_unsat_core_coll, 50) if size_unsat_core_coll.size > 0 else None,
            'size_unsat_core_75th': np.percentile(size_unsat_core_coll, 75) if size_unsat_core_coll.size > 0 else None,
            'size_unsat_core_min': np.min(size_unsat_core_coll) if size_unsat_core_coll.size > 0 else None,
            'size_unsat_core_max': np.max(size_unsat_core_coll) if size_unsat_core_coll.size > 0 else None,

            'size_raw_unsat_core_avg': np.mean(size_raw_unsat_core_coll) if size_raw_unsat_core_coll.size > 0 else None,
            'size_raw_unsat_core_25th': np.percentile(size_raw_unsat_core_coll, 25) if size_raw_unsat_core_coll.size > 0 else None,
            'size_raw_unsat_core_50th': np.percentile(size_raw_unsat_core_coll, 50) if size_raw_unsat_core_coll.size > 0 else None,
            'size_raw_unsat_core_75th': np.percentile(size_raw_unsat_core_coll, 75) if size_raw_unsat_core_coll.size > 0 else None,
            'size_raw_unsat_core_min': np.min(size_raw_unsat_core_coll) if size_raw_unsat_core_coll.size > 0 else None,
            'size_raw_unsat_core_max': np.max(size_raw_unsat_core_coll) if size_raw_unsat_core_coll.size > 0 else None,

            'unsat_core_time_avg': np.mean(unsat_core_time_coll) if unsat_core_time_coll.size > 0 else None,
            'unsat_core_time_25th': np.percentile(unsat_core_time_coll, 25) if unsat_core_time_coll.size > 0 else None,
            'unsat_core_time_50th': np.percentile(unsat_core_time_coll, 50) if unsat_core_time_coll.size > 0 else None,
            'unsat_core_time_75th': np.percentile(unsat_core_time_coll, 75) if unsat_core_time_coll.size > 0 else None,
            'unsat_core_time_min': np.min(unsat_core_time_coll) if unsat_core_time_coll.size > 0 else None,
            'unsat_core_time_max': np.max(unsat_core_time_coll) if unsat_core_time_coll.size > 0 else None,

            'other_time_avg': np.mean(other_time_coll) if other_time_coll.size > 0 else None,
            'other_time_25th': np.percentile(other_time_coll, 25) if other_time_coll.size > 0 else None,
            'other_time_50th': np.percentile(other_time_coll, 50) if other_time_coll.size > 0 else None,
            'other_time_75th': np.percentile(other_time_coll, 75) if other_time_coll.size > 0 else None,
            'other_time_min': np.min(other_time_coll) if other_time_coll.size > 0 else None,
            'other_time_max': np.max(other_time_coll) if other_time_coll.size > 0 else None,

            'timeout_num_relax_avg': np.mean(num_relax_timeout_coll) if num_relax_timeout_coll.size > 0 else None,
            'timeout_num_relax_25th': np.percentile(num_relax_timeout_coll, 25) if num_relax_timeout_coll.size > 0 else None,
            'timeout_num_relax_50th': np.percentile(num_relax_timeout_coll, 50) if num_relax_timeout_coll.size > 0 else None,
            'timeout_num_relax_75th': np.percentile(num_relax_timeout_coll, 75) if num_relax_timeout_coll.size > 0 else None,
            'timeout_num_relax_min': np.min(num_relax_timeout_coll) if num_relax_timeout_coll.size > 0 else None,
            'timeout_num_relax_max': np.max(num_relax_timeout_coll) if num_relax_timeout_coll.size > 0 else None,

            'timeout_size_unsat_core_avg': np.mean(size_unsat_core_timeout_coll) if size_unsat_core_timeout_coll.size > 0 else None,
            'timeout_size_unsat_core_25th': np.percentile(size_unsat_core_timeout_coll, 25) if size_unsat_core_timeout_coll.size > 0 else None,
            'timeout_size_unsat_core_50th': np.percentile(size_unsat_core_timeout_coll, 50) if size_unsat_core_timeout_coll.size > 0 else None,
            'timeout_size_unsat_core_75th': np.percentile(size_unsat_core_timeout_coll, 75) if size_unsat_core_timeout_coll.size > 0 else None,
            'timeout_size_unsat_core_min': np.min(size_unsat_core_timeout_coll) if size_unsat_core_timeout_coll.size > 0 else None,
            'timeout_size_unsat_core_max': np.max(size_unsat_core_timeout_coll) if size_unsat_core_timeout_coll.size > 0 else None,
        }

        if len(databases) == 0:
            print('warning!!!! len database =0')

        return databases

    def check(self, q1, q2, use_precise_encoding=False):
        # parse
        parser = SQLParser()

        jsons = []
        for query in [q1, q2]:
            jsons.append(parser.parse(query))

        asts = []
        for j in jsons:
            asts.append(parser.parse_query(j))

        # initializer = Initializer(self)
        #
        # for ast in asts:
        #     ast.accept(initializer)

        def task(ret):
            start = datetime.datetime.now()

            checking_time = 0
            unsat_core_time = 0
            max_rounds = 9000
            cur_rounds = 0
            size_unsat_core = 0
            raw_size_unsat_core = 0

            while True:
                try:
                    outputs = []
                    for query_id, ast in enumerate(asts):
                        self.curr_query_id = query_id
                        # print(repr(ast))
                        encoder = QueryEncoder(self)
                        output = ast.accept(encoder)
                        outputs.append(output)
                        # print(output.node.label)
                    self.initialized = True

                    self.formulas.append(Not(self.o1_eq_o2(outputs[0], outputs[1])), label='neq')
                except Exception as e:
                    logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                    ret['status'] = 'ERR'
                    return

                # self.formulas.append(And(self.underapproximator.underapproximation_constraints), label='op_under')

                try:
                    if not use_precise_encoding:
                        succeed_prover = self.formulas.search(outputs, ret)
                    else:
                        succeed_prover = self.formulas.solve_precise(ret)

                    total_time = (datetime.datetime.now() - start).total_seconds()
                    ret['complete_time'] = datetime.datetime.now()
                    ret['total_time'] = total_time
                    if succeed_prover is None:
                        ret['status'] = 'EQU'
                        return
                    checking_time += succeed_prover.checking_time
                except Exception as e:
                    logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                    ret['status'] = 'ERR'
                    return

                # debug: print final outputs
                for output in outputs:
                    logger.debug(succeed_prover.evaluate_table(output, self.db, self))

                # debug: print all intermediate table outputs
                # for table in self.db.schemas.values():
                #     print(table.table_id, table.lineage)
                #     print(succeed_prover.evaluate_choice_vector(table))
                #     print(succeed_prover.evaluate_table(table, self.db, self))
                #     print('=' * 30)

                database = {}
                try:
                    for table_idx, _ in enumerate(self.schema):
                        database[self.schema[table_idx]["TableName"].lower()] = succeed_prover.evaluate_table(
                            self.db.schemas[table_idx],
                            self.db,
                            self
                        )

                    ret['status'] = 'NEQ'
                    ret['cex'] = database

                except Exception as e:
                    logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                    ret['status'] = 'ERR'
                    return

                break

        with multiprocess.Manager() as manager:
            ret = manager.dict()

            process = multiprocess.Process(target=task, args=(ret,))
            process.start()

            start = datetime.datetime.now()
            process.join(self.time_budget)

            if process.is_alive():
                process.terminate()
                ret['status'] = 'TMO'
                ret['complete_time'] = datetime.datetime.now()

            if ret['status'] == 'ERR':
                return None, None, None, None, dict(ret)

            total_time = (ret['complete_time'] - start).total_seconds()

            self.clear()

            # print(ret)

            if ret['status'] == 'NEQ':
                return False, ret['cex'], None, total_time, dict(ret)
            elif ret['status'] == 'TMO':
                return None, None, None, total_time, dict(ret)
            else:
                return True, None, None, total_time, dict(ret)

    def disambiguate(self, queries, group_range, use_precise_encoding=False):
        parser = SQLParser()

        jsons = []
        for query in queries:
            jsons.append(parser.parse(query))

        asts = []
        for j in jsons:
            asts.append(parser.parse_query(j))

        # initializer = Initializer(self)
        #
        # for ast in asts:
        #     ast.accept(initializer)

        def task(ret):
            start = datetime.datetime.now()

            checking_time = 0

            try:
                outputs = []
                for query_id, ast in enumerate(asts):
                    self.curr_query_id = query_id
                    # print(repr(ast))
                    encoder = QueryEncoder(self)
                    output = ast.accept(encoder)
                    outputs.append(output)
                    # print(output.node.label)
                self.initialized = True

                disambiguation_cond = []

                num_groups = 2

                pre_created_o = [
                    create_empty_table(
                        row=max(outputs, key=lambda o: o.bound).bound,
                        col=len(max(outputs, key=lambda o: len(o.columns)).columns),
                        env=self)
                    for _ in range(num_groups)
                ]

                for q_output in outputs:
                    disambiguation_cond.append(
                        Or([SMTBelongsToGroup(q_output.table_id, g) for g in range(num_groups)])
                    )

                    indicators = []
                    for g in range(num_groups):
                        disambiguation_cond.append(
                            Implies(
                                SMTBelongsToGroup(q_output.table_id, g),
                                self.o1_eq_o2(q_output, pre_created_o[g])
                            )
                        )
                        indicators.append(If(SMTBelongsToGroup(q_output.table_id, g), Int(1), Int(0)))
                    disambiguation_cond.append(Sum(indicators) == Int(1))

                for g in range(num_groups):
                    indicators = []
                    for q_output in outputs:
                        indicators.append(If(SMTBelongsToGroup(q_output.table_id, g), Int(1), Int(0)))
                    disambiguation_cond.append(
                        And([
                            Sum(indicators) >= Int(max(len(outputs) / num_groups - group_range, 1)),
                            Sum(indicators) <= Int(len(outputs) / num_groups + group_range),
                        ])
                    )

                for g in range(num_groups):
                    for another_g in range(num_groups):
                        if another_g == g:
                            continue
                        disambiguation_cond.append(Not(self.o1_eq_o2(pre_created_o[g], pre_created_o[another_g])))

                self.formulas.append(And(disambiguation_cond), label='disambiguation')
            except Exception as e:
                logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                ret['status'] = 'ERR'
                return

            # self.formulas.append(And(self.underapproximator.underapproximation_constraints), label='op_under')

            try:
                if not use_precise_encoding:
                    succeed_prover = self.formulas.search(outputs, ret)
                else:
                    succeed_prover = self.formulas.solve_precise(ret)

                total_time = (datetime.datetime.now() - start).total_seconds()
                ret['complete_time'] = datetime.datetime.now()
                ret['total_time'] = total_time
                if succeed_prover is None:
                    ret['status'] = 'EQU'
                    return
                checking_time += succeed_prover.checking_time
            except Exception as e:
                logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                ret['status'] = 'ERR'
                return

            database = {}
            try:
                for table_idx, _ in enumerate(self.schema):
                    database[self.schema[table_idx]["TableName"].lower()] = succeed_prover.evaluate_table(
                        self.db.schemas[table_idx],
                        self.db,
                        self
                    )

                ret['status'] = 'NEQ'
                ret['cex'] = database

            except Exception as e:
                logger.error(''.join(traceback.format_tb(e.__traceback__)) + str(e))
                ret['status'] = 'ERR'
                return

        with multiprocess.Manager() as manager:
            ret = manager.dict()

            process = multiprocess.Process(target=task, args=(ret,))
            process.start()

            start = datetime.datetime.now()
            process.join(self.time_budget)

            if process.is_alive():
                process.terminate()
                ret['status'] = 'TMO'
                ret['complete_time'] = datetime.datetime.now()

            total_time = (ret['complete_time'] - start).total_seconds()

            self.clear()

            # print(ret)

            if ret['status'] == 'ERR':
                return None, None, None, total_time, dict(ret)
            else:
                if ret['status'] == 'NEQ':
                    return False, ret['cex'], None, total_time, dict(ret)
                elif ret['status'] == 'TMO':
                    return None, None, None, total_time, dict(ret)
                else:
                    return True, None, None, total_time, dict(ret)

    def o1_eq_o2(self, o1, o2):
        def f_multiplicity(r, t):
            indicators = []
            for tuple_idx in range(r.bound):
                tuple_eq = [Not(Deleted(r.table_id, tuple_idx))]
                for column_idx, column in enumerate(r):
                    tuple_eq.append(Or([
                        And([self.null(r.table_id, tuple_idx, column.column_id), self.null(*t[column_idx])]),
                        And([
                            Not(Or([self.null(r.table_id, tuple_idx, column.column_id), self.null(*t[column_idx])])),
                            self.cell(r.table_id, tuple_idx, column.column_id) == self.cell(*t[column_idx])
                        ])
                    ]))
                indicators.append(If(And(tuple_eq), Int(1), Int(0)))
            return Sum(indicators)

        o1_size = Sum([If(Not(Deleted(o1.table_id, tuple_id)), Int(1), Int(0)) for tuple_id in range(o1.bound)])
        o2_size = Sum([If(Not(Deleted(o2.table_id, tuple_id)), Int(1), Int(0)) for tuple_id in range(o2.bound)])

        if len(o1.columns) == len(o2.columns):
            lateral_bag_eq = []
            for tuple_id in range(o1.bound):
                lateral_bag_eq.append(
                    Implies(
                        Not(Deleted(o1.table_id, tuple_id)),
                        f_multiplicity(o1, [(o1.table_id, tuple_id, column.column_id) for column in o1]) ==
                        f_multiplicity(o2, [(o1.table_id, tuple_id, column.column_id) for column in o1])
                    )
                )
            f = [o1_size == o2_size, And(lateral_bag_eq)]

            # sorted columns are equivalent under list semantics
            if o1.lineage is not None and o2.lineage is not None and 'Sorted' in o1.lineage and 'Sorted' in o2.lineage:
                sorted_columns_list_eq = []
                o1_encoder = ExpressionEncoder(o1, self)
                o2_encoder = ExpressionEncoder(o2, self)
                for tuple_id in range(min(o1.bound, o2.bound)):
                    for expression_idx, expression in enumerate(o1.node.expressions):
                        if isinstance(expression, Literal):
                            if isinstance(expression.value, bool):
                                continue
                            o1_cell = self.db[o1.table_id, tuple_id, expression.value - 1]
                            o1_cell = o1_cell.VAL, o1_cell.NULL
                            o2_cell = self.db[o2.table_id, tuple_id, expression.value - 1]
                            o2_cell = o2_cell.VAL, o2_cell.NULL
                        else:
                            if isinstance(expression, Attribute) and '.' in expression.name:
                                expression = Attribute(expression.name.split('.')[1])
                            o1_cell = o1_encoder.expression_for_tuple(expression, tuple_id)
                            o2_cell = o2_encoder.expression_for_tuple(expression, tuple_id)

                        VAL, NULL = 0, 1
                        sorted_columns_list_eq.append(
                            Implies(
                                Not(Deleted(o1.table_id, tuple_id)),
                                Or([
                                    And([o1_cell[NULL], o2_cell[NULL]]),
                                    And([
                                        Not(Or([o1_cell[NULL], o2_cell[NULL]])),
                                        o1_cell[VAL] == o2_cell[VAL]
                                    ])
                                ])
                            )
                        )
                f.append(And(sorted_columns_list_eq))
            return And(f)
        else:
            return Or([o1_size > Int(0), o2_size > Int(0)])

    def copy_cell(self, original_cell, new_cell):
        return And([
            new_cell.NULL == original_cell.NULL,
            new_cell.VAL == original_cell.VAL,
        ])

    def clear(self):
        self.db = Database()
        self.table_id_counter = -1
        self.string_hash_table = {}
        self.hash_string_table = {}

        self.formulas = FormulaManager(self)

        self.unsat_mutants = []

        self.load_schema(self.schema)
        self.formulas.append(encode_integrity_constraints(self.constraints, self), label='ic')
        # self.formulas.append(And(self.integrity_constraints), label='ic')

        self.underapproximator = Underapproximator(self)
