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
        ObjectDefine(c_file, 7, 12, 1, 1, 'F',
                     '"This"" is"" a"" multi""-line"" string"'),
        ObjectDefine(c_file, 13, 14, 1, 1, 'G', '12'),
        ObjectDefine(c_file, 15, 15, 1, 1, 'H',
                     '"This // has // comment // starters // in // it"'),
        ObjectDefine(c_file, 16, 16, 1, 1, 'I',
                     '"This // has // comment // starters // in // it"'),
        ObjectDefine(c_file, 17, 18, 1, 1, 'J',
                     '"This // has // comment // ""starters // in // it // across // multiple // lines"'),
        ObjectDefine(c_file, 19, 19, 1, 1, 'K',
                     '"Multiple strings"  " with comments"  " between them"'),
        ObjectDefine(c_file, 20, 21, 1, 1, 'L',
                     '"Multiple strings"  " ""with comments and lines"  " between them"'),
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


def test_collect_binary_op_macros():
    stat_file, c_file = get_test_file_paths("binary_op_macros")
    result = collect_macro_data(stat_file, c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 1, 1, 'IDENT1', "1.0L + 1.0L"),
        ObjectDefine(c_file, 2, 2, 1, 1, 'IDENT2', "1.0L + 1.0"),
        ObjectDefine(c_file, 3, 3, 1, 1, 'IDENT3', "1.0L + 1ULL"),
        ObjectDefine(c_file, 4, 4, 1, 1, 'IDENT4', "1.0L + 1LL"),
        ObjectDefine(c_file, 5, 5, 1, 1, 'IDENT5', "1.0L + 1UL"),
        ObjectDefine(c_file, 6, 6, 1, 1, 'IDENT6', "1.0L + 1L"),
        ObjectDefine(c_file, 7, 7, 1, 1, 'IDENT7', "1.0L + 1U"),
        ObjectDefine(c_file, 8, 8, 1, 1, 'IDENT8', "1.0L + 1"),
        ObjectDefine(c_file, 9, 9, 1, 1, 'IDENT9', "1.0L + 'a'"),
        ObjectDefine(c_file, 10, 10, 1, 1, 'IDENT10', "1.0 + 1.0"),
        ObjectDefine(c_file, 11, 11, 1, 1, 'IDENT11', "1.0 + 1ULL"),
        ObjectDefine(c_file, 12, 12, 1, 1, 'IDENT12', "1.0 + 1LL"),
        ObjectDefine(c_file, 13, 13, 1, 1, 'IDENT13', "1.0 + 1UL"),
        ObjectDefine(c_file, 14, 14, 1, 1, 'IDENT14', "1.0 + 1L"),
        ObjectDefine(c_file, 15, 15, 1, 1, 'IDENT15', "1.0 + 1U"),
        ObjectDefine(c_file, 16, 16, 1, 1, 'IDENT16', "1.0 + 1"),
        ObjectDefine(c_file, 17, 17, 1, 1, 'IDENT17', "1.0 + 'a'"),
        ObjectDefine(c_file, 18, 18, 1, 1, 'IDENT18', "1ULL + 1ULL"),
        ObjectDefine(c_file, 19, 19, 1, 1, 'IDENT19', "1ULL + 1LL"),
        ObjectDefine(c_file, 20, 20, 1, 1, 'IDENT20', "1ULL + 1UL"),
        ObjectDefine(c_file, 21, 21, 1, 1, 'IDENT21', "1ULL + 1L"),
        ObjectDefine(c_file, 22, 22, 1, 1, 'IDENT22', "1ULL + 1U"),
        ObjectDefine(c_file, 23, 23, 1, 1, 'IDENT23', "1ULL + 1"),
        ObjectDefine(c_file, 24, 24, 1, 1, 'IDENT24', "1ULL + 'a'"),
        ObjectDefine(c_file, 25, 25, 1, 1, 'IDENT25', "1LL + 1LL"),
        ObjectDefine(c_file, 26, 26, 1, 1, 'IDENT26', "1LL + 1UL"),
        ObjectDefine(c_file, 27, 27, 1, 1, 'IDENT27', "1LL + 1L"),
        ObjectDefine(c_file, 28, 28, 1, 1, 'IDENT28', "1LL + 1U"),
        ObjectDefine(c_file, 29, 29, 1, 1, 'IDENT29', "1LL + 1"),
        ObjectDefine(c_file, 30, 30, 1, 1, 'IDENT30', "1LL + 'a'"),
        ObjectDefine(c_file, 31, 31, 1, 1, 'IDENT31', "1UL + 1UL"),
        ObjectDefine(c_file, 32, 32, 1, 1, 'IDENT32', "1UL + 1L"),
        ObjectDefine(c_file, 33, 33, 1, 1, 'IDENT33', "1UL + 1U"),
        ObjectDefine(c_file, 34, 34, 1, 1, 'IDENT34', "1UL + 1"),
        ObjectDefine(c_file, 35, 35, 1, 1, 'IDENT35', "1UL + 'a'"),
        ObjectDefine(c_file, 36, 36, 1, 1, 'IDENT36', "1L + 1L"),
        ObjectDefine(c_file, 37, 37, 1, 1, 'IDENT37', "1L + 1U"),
        ObjectDefine(c_file, 38, 38, 1, 1, 'IDENT38', "1L + 1"),
        ObjectDefine(c_file, 39, 39, 1, 1, 'IDENT39', "1L + 'a'"),
        ObjectDefine(c_file, 40, 40, 1, 1, 'IDENT40', "1U + 1U"),
        ObjectDefine(c_file, 41, 41, 1, 1, 'IDENT41', "1U + 1"),
        ObjectDefine(c_file, 42, 42, 1, 1, 'IDENT42', "1U + 'a'"),
        ObjectDefine(c_file, 43, 43, 1, 1, 'IDENT43', "1 + 1"),
        ObjectDefine(c_file, 44, 44, 1, 1, 'IDENT44', "1 + 'a'"),
        ObjectDefine(c_file, 45, 45, 1, 1, 'IDENT45', "'a' + 'a'"),
    ]
