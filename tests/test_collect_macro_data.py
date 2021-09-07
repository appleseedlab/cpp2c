import os
from typing import Tuple

from macro_data_collector.collect_macro_data import collect_macro_data
from macro_data_collector.directives import MacroDataList, ObjectDefine

TEST_INPUT_DIRNAME = "c_files"

TEST_INPUT_DIRPATH = os.path.abspath(os.path.join(
    os.path.dirname(__file__), TEST_INPUT_DIRNAME))


def get_test_file_paths(fn: str) -> Tuple[str, str]:
    return (os.path.join(TEST_INPUT_DIRPATH, fn + ".txt"),
            os.path.join(TEST_INPUT_DIRPATH, fn + ".c"))


def test_collect_positive_ints():
    stat_file, c_file = get_test_file_paths("positive_int_macros")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'A', '1'),
        ObjectDefine(c_file, 2, 2, 1, 1, 'B', '2'),
    ]


def test_collect_negative_ints():
    stat_file, c_file = get_test_file_paths("negative_int_macros")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'A', '-1'),
        ObjectDefine(c_file, 2, 2, 1, 1, 'B', '-2'),
    ]


def test_collect_positive_floats():
    stat_file, c_file = get_test_file_paths("positive_float_macros")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'A', '1.0'),
        ObjectDefine(c_file, 2, 2, 1, 1, 'B', '2.0'),
    ]


def test_collect_negative_floats():
    stat_file, c_file = get_test_file_paths("negative_float_macros")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'A', '-1.0'),
        ObjectDefine(c_file, 2, 2, 1, 1, 'B', '-2.0'),
    ]


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
