import os
from typing import Tuple
from unittest import TestCase

from macro_data_collector.collect_macro_data import collect_macro_data
from macro_data_collector.directives import MacroDataList, ObjectDefine

TEST_INPUT_DIRNAME = "c_files"

TEST_INPUT_DIRPATH = os.path.abspath(os.path.join(
    os.path.dirname(__file__), TEST_INPUT_DIRNAME))


def test_file_paths(fn: str) -> Tuple[str, str]:
    return (os.path.join(TEST_INPUT_DIRPATH, fn + ".txt"),
            os.path.join(TEST_INPUT_DIRPATH, fn + ".c"))


class CollectMacroDataTests(TestCase):
    # Note: SuperC does not seem to return the correct definition counts...

    def setUp(self) -> None:
        self.maxDiff = 10_000
        return super().setUp()

    def test_collect_positive_ints(self):
        stat_file, c_file = test_file_paths("positive_int_macros")
        result = collect_macro_data(stat_file, c_file)
        self.assertEqual(
            result,
            [
                ObjectDefine(c_file, 1, 1, 1, 1, 'A', '1'),
                ObjectDefine(c_file, 2, 2, 1, 1, 'B', '2'),
            ]
        )

    def test_collect_negative_ints(self):
        stat_file, c_file = test_file_paths("negative_int_macros")
        result = collect_macro_data(stat_file, c_file)
        self.assertEqual(
            result,
            [
                ObjectDefine(c_file, 1, 1, 1, 1, 'A', '-1'),
                ObjectDefine(c_file, 2, 2, 1, 1, 'B', '-2'),
            ]
        )

    def test_collect_positive_floats(self):
        stat_file, c_file = test_file_paths("positive_float_macros")
        result = collect_macro_data(stat_file, c_file)
        self.assertEqual(
            result,
            [
                ObjectDefine(c_file, 1, 1, 1, 1, 'A', '1.0'),
                ObjectDefine(c_file, 2, 2, 1, 1, 'B', '2.0'),
            ]
        )

    def test_collect_negative_floats(self):
        stat_file, c_file = test_file_paths("negative_float_macros")
        result = collect_macro_data(stat_file, c_file)
        self.assertEqual(
            result,
            [
                ObjectDefine(c_file, 1, 1, 1, 1, 'A', '-1.0'),
                ObjectDefine(c_file, 2, 2, 1, 1, 'B', '-2.0'),
            ]
        )

    def test_collect_macros_with_comments(self):
        stat_file, c_file = test_file_paths("macros_with_comments")
        result = collect_macro_data(stat_file, c_file)
        self.assertEqual(
            result,
            [
                ObjectDefine(c_file, 1, 1, 1, 1, 'A', '1'),
                ObjectDefine(c_file, 2, 2, 1, 1, 'B', "'C'"),
                ObjectDefine(c_file, 3, 3, 1, 1, 'C', '"String literal"'),
                ObjectDefine(c_file, 4, 4, 1, 1, 'D', '2.0'),
                ObjectDefine(c_file, 5, 6, 1, 1, 'E', '"A B C ""D E F"'),
            ]
        )

    # def test_collect_simple_constants(self):
    #     stat_file, c_file = test_file_paths("simple_constant_macros")
    #     result = collect_macro_data(stat_file, c_file)
    #     self.assertEqual(
    #         result,
    #         [
    #             ObjectDefine(file=c_file, line=2, column=1,
    #                          definition_count=1, identifier='A', body='1  //  int'),
    #             ObjectDefine(file=c_file, line=3, column=1,
    #                          definition_count=1, identifier='B', body='-1 //  int')
    #         ]
    #     )
