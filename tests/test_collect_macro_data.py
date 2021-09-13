import os
from typing import Tuple

from macro_data_collector.collect_macro_data import collect_macro_data
from macro_data_collector.directives import ObjectDefine

TEST_INPUT_DIRNAME = "c_files"

TEST_INPUT_DIRPATH = os.path.abspath(os.path.join(
    os.path.dirname(__file__), TEST_INPUT_DIRNAME))


def get_test_file_paths(fn: str) -> Tuple[str, str]:
    return (os.path.join(TEST_INPUT_DIRPATH, fn + ".txt"),
            os.path.join(TEST_INPUT_DIRPATH, fn + ".c"))


def test_collect_macros_with_comments():
    stat_file, c_file = get_test_file_paths("macros_with_comments")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'A', '1'),
        ObjectDefine(c_file, 2, 2, 1, 1, 'B', "'C'"),
        ObjectDefine(c_file, 3, 3, 1, 1, 'C', '"String literal"'),
        ObjectDefine(c_file, 4, 4, 1, 1, 'D', '2.0'),
        ObjectDefine(c_file, 5, 6, 1, 1, 'E', '"A B C ""D E F"'),
    ]


def test_collect_unary_op_macros():
    stat_file, c_file = get_test_file_paths("unary_op_macros")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'A', '-1'),
        ObjectDefine(c_file, 2, 2, 1, 1, 'B', '+1'),
        ObjectDefine(c_file, 3, 3, 1, 1, 'C', '-1L'),
        ObjectDefine(c_file, 4, 4, 1, 1, 'D', '+1L'),
        ObjectDefine(c_file, 5, 5, 1, 1, 'E', '-1LL'),
        ObjectDefine(c_file, 6, 6, 1, 1, 'F', '+1LL'),
        ObjectDefine(c_file, 7, 7, 1, 1, 'G', '-1.0'),
        ObjectDefine(c_file, 8, 8, 1, 1, 'H', '+1.0'),
        ObjectDefine(c_file, 9, 9, 1, 1, 'I', '-1.0L'),
        ObjectDefine(c_file, 10, 10, 1, 1, 'J', '+1.0L'),
    ]
