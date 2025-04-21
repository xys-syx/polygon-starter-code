"""
Goal: decide whether two aggregate queries that differ only in their
`FILTER (WHERE col_b > 10)` predicate vs. `FILTER (WHERE col_b >= 10)`
are semantically equivalent under a bounded database.
"""

import logging

from polygon.sql_parser import SQLParser
from polygon.testers.mysql_tester import MySQLTester, DB_CONFIG
from polygon.environment import Environment
from polygon.logger import logger


def main() -> None:
    logger.setLevel(logging.DEBUG)


    schema = [
        {
            "TableName": "Sales",
            "PKeys": [
                {"Name": "id", "Type": "int"}
            ],
            "FKeys": [],
            "Others": [
                {"Name": "col_a", "Type": "int"},
                {"Name": "col_b", "Type": "int"}
            ]
        }
    ]

    constraints = [{'distinct': ['Sales.id']}]


    env = Environment(
        schema=schema,
        constraints=constraints,
        bound=2,          
        time_budget=60   
    )


    queries = [
        """
        SELECT SUM(col_a) FILTER (WHERE col_b > 10) AS total
        FROM   Sales
        """,

        """
        SELECT SUM(col_a) FILTER (WHERE col_b >= 10) AS total
        FROM   Sales
        """
    ]
    parser = SQLParser()
    query_str0 = parser.parse(queries[0])
    query_ast0 = parser.parse_query(query_str0)
    print(query_str0)
    print(query_ast0)

    parser = SQLParser()
    query_str1 = parser.parse(queries[1])
    query_ast1 = parser.parse_query(query_str1)
    print(query_str1)
    print(query_ast1)


    eq, cex, checking_time, total_time, ret = env.check(*queries)
    print(ret)
    print("=== Solver stats ===")
    for k, v in ret.items():
        print(f"{k:>18s}: {v}")
    print()

    if eq is None:
        print("ERR")
        return

    if not eq:
        print("NEQ", total_time)
        logger.info(cex)

        with MySQLTester(DB_CONFIG, schema) as tester:
            tester.create_all_databases([cex], constraints)
            rejected = tester.test_pair(*queries)   
            print(rejected)
    else:
        print("EQ")


if __name__ == "__main__":
    main()