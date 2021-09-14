'''
test_collect_macro_data.py

Test cases for collecting data on macro definitions.
'''

from tests import get_test_file_path
from macro_data_collector.collect_macro_data import collect_macro_data
from macro_data_collector.directives import ObjectDefine


def test_collect_macros_with_comments():
    c_file = get_test_file_path("macros_with_comments")
    result = collect_macro_data(c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 9, 1, 'A', '1'),
        ObjectDefine(c_file, 2, 2, 9, 1, 'B', "'C'"),
        ObjectDefine(c_file, 3, 3, 9, 1, 'C', '"String literal"'),
        ObjectDefine(c_file, 4, 4, 9, 1, 'D', '2.0'),
        ObjectDefine(c_file, 5, 6, 9, 1, 'E', '"A B C ""D E F"'),
        ObjectDefine(c_file, 7, 12, 9, 1, 'F',
                     '"This"" is"" a"" multi""-line"" string"'),
        ObjectDefine(c_file, 13, 14, 9, 1, 'G', '12'),
        ObjectDefine(c_file, 15, 15, 9, 1, 'H',
                     '"This // has // comment // starters // in // it"'),
        ObjectDefine(c_file, 16, 16, 9, 1, 'I',
                     '"This // has // comment // starters // in // it"'),
        ObjectDefine(c_file, 17, 18, 9, 1, 'J',
                     '"This // has // comment // ""starters // in // it // across // multiple // lines"'),
        ObjectDefine(c_file, 19, 19, 9, 1, 'K',
                     '"Multiple strings"  " with comments"  " between them"'),
        ObjectDefine(c_file, 20, 21, 9, 1, 'L',
                     '"Multiple strings"  " ""with comments and lines"  " between them"'),
    ]


def test_collect_unary_op_macros():
    c_file = get_test_file_path("unary_op_macros")
    result = collect_macro_data(c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 9, 1, 'A', '-1'),
        ObjectDefine(c_file, 2, 2, 9, 1, 'B', '+1'),
        ObjectDefine(c_file, 3, 3, 9, 1, 'C', '-1L'),
        ObjectDefine(c_file, 4, 4, 9, 1, 'D', '+1L'),
        ObjectDefine(c_file, 5, 5, 9, 1, 'E', '-1LL'),
        ObjectDefine(c_file, 6, 6, 9, 1, 'F', '+1LL'),
        ObjectDefine(c_file, 7, 7, 9, 1, 'G', '-1.0'),
        ObjectDefine(c_file, 8, 8, 9, 1, 'H', '+1.0'),
        ObjectDefine(c_file, 9, 9, 9, 1, 'I', '-1.0L'),
        ObjectDefine(c_file, 10, 10, 9, 1, 'J', '+1.0L'),
    ]


def test_collect_binary_op_macros():
    c_file = get_test_file_path("binary_op_macros")
    result = collect_macro_data(c_file)
    assert result == [
        ObjectDefine(c_file, 1, 1, 9, 1, 'IDENT1', "1.0L + 1.0L"),
        ObjectDefine(c_file, 2, 2, 9, 1, 'IDENT2', "1.0L + 1.0"),
        ObjectDefine(c_file, 3, 3, 9, 1, 'IDENT3', "1.0L + 1ULL"),
        ObjectDefine(c_file, 4, 4, 9, 1, 'IDENT4', "1.0L + 1LL"),
        ObjectDefine(c_file, 5, 5, 9, 1, 'IDENT5', "1.0L + 1UL"),
        ObjectDefine(c_file, 6, 6, 9, 1, 'IDENT6', "1.0L + 1L"),
        ObjectDefine(c_file, 7, 7, 9, 1, 'IDENT7', "1.0L + 1U"),
        ObjectDefine(c_file, 8, 8, 9, 1, 'IDENT8', "1.0L + 1"),
        ObjectDefine(c_file, 9, 9, 9, 1, 'IDENT9', "1.0L + 'a'"),
        ObjectDefine(c_file, 10, 10, 9, 1, 'IDENT10', "1.0 + 1.0"),
        ObjectDefine(c_file, 11, 11, 9, 1, 'IDENT11', "1.0 + 1ULL"),
        ObjectDefine(c_file, 12, 12, 9, 1, 'IDENT12', "1.0 + 1LL"),
        ObjectDefine(c_file, 13, 13, 9, 1, 'IDENT13', "1.0 + 1UL"),
        ObjectDefine(c_file, 14, 14, 9, 1, 'IDENT14', "1.0 + 1L"),
        ObjectDefine(c_file, 15, 15, 9, 1, 'IDENT15', "1.0 + 1U"),
        ObjectDefine(c_file, 16, 16, 9, 1, 'IDENT16', "1.0 + 1"),
        ObjectDefine(c_file, 17, 17, 9, 1, 'IDENT17', "1.0 + 'a'"),
        ObjectDefine(c_file, 18, 18, 9, 1, 'IDENT18', "1ULL + 1ULL"),
        ObjectDefine(c_file, 19, 19, 9, 1, 'IDENT19', "1ULL + 1LL"),
        ObjectDefine(c_file, 20, 20, 9, 1, 'IDENT20', "1ULL + 1UL"),
        ObjectDefine(c_file, 21, 21, 9, 1, 'IDENT21', "1ULL + 1L"),
        ObjectDefine(c_file, 22, 22, 9, 1, 'IDENT22', "1ULL + 1U"),
        ObjectDefine(c_file, 23, 23, 9, 1, 'IDENT23', "1ULL + 1"),
        ObjectDefine(c_file, 24, 24, 9, 1, 'IDENT24', "1ULL + 'a'"),
        ObjectDefine(c_file, 25, 25, 9, 1, 'IDENT25', "1LL + 1LL"),
        ObjectDefine(c_file, 26, 26, 9, 1, 'IDENT26', "1LL + 1UL"),
        ObjectDefine(c_file, 27, 27, 9, 1, 'IDENT27', "1LL + 1L"),
        ObjectDefine(c_file, 28, 28, 9, 1, 'IDENT28', "1LL + 1U"),
        ObjectDefine(c_file, 29, 29, 9, 1, 'IDENT29', "1LL + 1"),
        ObjectDefine(c_file, 30, 30, 9, 1, 'IDENT30', "1LL + 'a'"),
        ObjectDefine(c_file, 31, 31, 9, 1, 'IDENT31', "1UL + 1UL"),
        ObjectDefine(c_file, 32, 32, 9, 1, 'IDENT32', "1UL + 1L"),
        ObjectDefine(c_file, 33, 33, 9, 1, 'IDENT33', "1UL + 1U"),
        ObjectDefine(c_file, 34, 34, 9, 1, 'IDENT34', "1UL + 1"),
        ObjectDefine(c_file, 35, 35, 9, 1, 'IDENT35', "1UL + 'a'"),
        ObjectDefine(c_file, 36, 36, 9, 1, 'IDENT36', "1L + 1L"),
        ObjectDefine(c_file, 37, 37, 9, 1, 'IDENT37', "1L + 1U"),
        ObjectDefine(c_file, 38, 38, 9, 1, 'IDENT38', "1L + 1"),
        ObjectDefine(c_file, 39, 39, 9, 1, 'IDENT39', "1L + 'a'"),
        ObjectDefine(c_file, 40, 40, 9, 1, 'IDENT40', "1U + 1U"),
        ObjectDefine(c_file, 41, 41, 9, 1, 'IDENT41', "1U + 1"),
        ObjectDefine(c_file, 42, 42, 9, 1, 'IDENT42', "1U + 'a'"),
        ObjectDefine(c_file, 43, 43, 9, 1, 'IDENT43', "1 + 1"),
        ObjectDefine(c_file, 44, 44, 9, 1, 'IDENT44', "1 + 'a'"),
        ObjectDefine(c_file, 45, 45, 9, 1, 'IDENT45', "'a' + 'a'"),
    ]
