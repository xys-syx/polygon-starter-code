import logging

from polygon.testers.mysql_tester import MySQLTester
from polygon.testers.mysql_tester import DB_CONFIG
from polygon.environment import Environment
from polygon.logger import logger


def main():
    logger.setLevel(logging.DEBUG)

    schema = [
        {
            "TableName": "Employees",
            "PKeys": [
                {
                    "Name": "emp_id",
                    "Type": "int"
                }
            ],
            "FKeys": [],
            "Others": [
                {
                    "Name": "name",
                    "Type": "varchar"
                },
                {
                    "Name": "age",
                    "Type": "int"
                }
            ]
        }
    ]
    constraints = [{'distinct': ['Employees.emp_id']}]

    env = Environment(schema, constraints, bound=2, time_budget=60)

    queries = [
        """
        SELECT emp_id FROM Employees WHERE age > 30
        """,

        """
        SELECT emp_id FROM Employees WHERE age >= 30
        """
    ]

    eq, cex, checking_time, total_time, ret = env.check(*queries)
    print(ret)
    if eq is None:
        print('ERR')
    else:
        if not eq:
            print('NEQ', total_time)
            logger.info(cex)
            with MySQLTester(DB_CONFIG, schema) as tester:
                tester.create_all_databases([cex], constraints)
                rejected = tester.test_pair(*queries)
                print(rejected)
        else:
            print('EQ')


if __name__ == '__main__':
    main()
