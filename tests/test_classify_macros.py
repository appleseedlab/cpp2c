'''
test_classify_macros.py

Test cases for classifying macros so that they may be converted to
a C language construct.
'''

from macro_classifier.classifications import (SimpleConstantMacro,
                                              SimpleExpressionMacro)
from macro_classifier.classify_macros import check_macro_usage, classify_macro
from macro_data_collector.collect_macro_data import collect_macro_data
from macro_data_collector.directives import ObjectDefine

from tests import get_test_file_path


def test_classify_simple_object_macros():
    macros = [
        ObjectDefine('', 1, 1, 1, 1, 'A', '1'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1U'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1L'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1UL'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1LL'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1ULL'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1.0'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '1.0L'),
        ObjectDefine('', 1, 1, 1, 1, 'A', "'C'"),
        ObjectDefine('', 1, 1, 1, 1, 'A', '"String"'),
    ]
    result = [classify_macro(macro) for macro in macros]
    assert result == [
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1'), 'int'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1U'), 'unsigned int'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1L'), 'long int'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1UL'), 'unsigned long int'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1LL'), 'long long int'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1ULL'), 'unsigned long long int'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1.0'), 'double'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '1.0L'), 'long double'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', "'C'"), 'char'),
        SimpleConstantMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '"String"'), 'string'),
    ]


def test_classify_simple_expression_macros_unary_ops():
    macros = [
        ObjectDefine('', 1, 1, 1, 1, 'A', '-1'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '+1'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '-1.0'),
        ObjectDefine('', 1, 1, 1, 1, 'A', '+1.0'),
    ]
    result = [classify_macro(macro) for macro in macros]
    assert result == [
        SimpleExpressionMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '-1'), 'int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '+1'), 'int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '-1.0'), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'A', '+1.0'), 'double'),
    ]


def test_classify_simple_expression_macros_binary_ops():
    macros = [
        ObjectDefine('', 1, 1, 1, 1, 'IDENT1', "1.0L + 1.0L"),
        ObjectDefine('', 2, 2, 1, 1, 'IDENT2', "1.0L + 1.0"),
        ObjectDefine('', 3, 3, 1, 1, 'IDENT3', "1.0L + 1ULL"),
        ObjectDefine('', 4, 4, 1, 1, 'IDENT4', "1.0L + 1LL"),
        ObjectDefine('', 5, 5, 1, 1, 'IDENT5', "1.0L + 1UL"),
        ObjectDefine('', 6, 6, 1, 1, 'IDENT6', "1.0L + 1L"),
        ObjectDefine('', 7, 7, 1, 1, 'IDENT7', "1.0L + 1U"),
        ObjectDefine('', 8, 8, 1, 1, 'IDENT8', "1.0L + 1"),
        ObjectDefine('', 9, 9, 1, 1, 'IDENT9', "1.0L + 'a'"),
        ObjectDefine('', 10, 10, 1, 1, 'IDENT10', "1.0 + 1.0"),
        ObjectDefine('', 11, 11, 1, 1, 'IDENT11', "1.0 + 1ULL"),
        ObjectDefine('', 12, 12, 1, 1, 'IDENT12', "1.0 + 1LL"),
        ObjectDefine('', 13, 13, 1, 1, 'IDENT13', "1.0 + 1UL"),
        ObjectDefine('', 14, 14, 1, 1, 'IDENT14', "1.0 + 1L"),
        ObjectDefine('', 15, 15, 1, 1, 'IDENT15', "1.0 + 1U"),
        ObjectDefine('', 16, 16, 1, 1, 'IDENT16', "1.0 + 1"),
        ObjectDefine('', 17, 17, 1, 1, 'IDENT17', "1.0 + 'a'"),
        ObjectDefine('', 18, 18, 1, 1, 'IDENT18', "1ULL + 1ULL"),
        ObjectDefine('', 19, 19, 1, 1, 'IDENT19', "1ULL + 1LL"),
        ObjectDefine('', 20, 20, 1, 1, 'IDENT20', "1ULL + 1UL"),
        ObjectDefine('', 21, 21, 1, 1, 'IDENT21', "1ULL + 1L"),
        ObjectDefine('', 22, 22, 1, 1, 'IDENT22', "1ULL + 1U"),
        ObjectDefine('', 23, 23, 1, 1, 'IDENT23', "1ULL + 1"),
        ObjectDefine('', 24, 24, 1, 1, 'IDENT24', "1ULL + 'a'"),
        ObjectDefine('', 25, 25, 1, 1, 'IDENT25', "1LL + 1LL"),
        ObjectDefine('', 26, 26, 1, 1, 'IDENT26', "1LL + 1UL"),
        ObjectDefine('', 27, 27, 1, 1, 'IDENT27', "1LL + 1L"),
        ObjectDefine('', 28, 28, 1, 1, 'IDENT28', "1LL + 1U"),
        ObjectDefine('', 29, 29, 1, 1, 'IDENT29', "1LL + 1"),
        ObjectDefine('', 30, 30, 1, 1, 'IDENT30', "1LL + 'a'"),
        ObjectDefine('', 31, 31, 1, 1, 'IDENT31', "1UL + 1UL"),
        ObjectDefine('', 32, 32, 1, 1, 'IDENT32', "1UL + 1L"),
        ObjectDefine('', 33, 33, 1, 1, 'IDENT33', "1UL + 1U"),
        ObjectDefine('', 34, 34, 1, 1, 'IDENT34', "1UL + 1"),
        ObjectDefine('', 35, 35, 1, 1, 'IDENT35', "1UL + 'a'"),
        ObjectDefine('', 36, 36, 1, 1, 'IDENT36', "1L + 1L"),
        ObjectDefine('', 37, 37, 1, 1, 'IDENT37', "1L + 1U"),
        ObjectDefine('', 38, 38, 1, 1, 'IDENT38', "1L + 1"),
        ObjectDefine('', 39, 39, 1, 1, 'IDENT39', "1L + 'a'"),
        ObjectDefine('', 40, 40, 1, 1, 'IDENT40', "1U + 1U"),
        ObjectDefine('', 41, 41, 1, 1, 'IDENT41', "1U + 1"),
        ObjectDefine('', 42, 42, 1, 1, 'IDENT42', "1U + 'a'"),
        ObjectDefine('', 43, 43, 1, 1, 'IDENT43', "1 + 1"),
        ObjectDefine('', 44, 44, 1, 1, 'IDENT44', "1 + 'a'"),
        ObjectDefine('', 45, 45, 1, 1, 'IDENT45', "'a' + 'a'"),
    ]
    result = [classify_macro(macro) for macro in macros]
    assert result == [
        SimpleExpressionMacro(ObjectDefine(
            '', 1, 1, 1, 1, 'IDENT1', "1.0L + 1.0L"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 2, 2, 1, 1, 'IDENT2', "1.0L + 1.0"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 3, 3, 1, 1, 'IDENT3', "1.0L + 1ULL"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 4, 4, 1, 1, 'IDENT4', "1.0L + 1LL"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 5, 5, 1, 1, 'IDENT5', "1.0L + 1UL"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 6, 6, 1, 1, 'IDENT6', "1.0L + 1L"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 7, 7, 1, 1, 'IDENT7', "1.0L + 1U"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 8, 8, 1, 1, 'IDENT8', "1.0L + 1"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 9, 9, 1, 1, 'IDENT9', "1.0L + 'a'"), 'long double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 10, 10, 1, 1, 'IDENT10', "1.0 + 1.0"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 11, 11, 1, 1, 'IDENT11', "1.0 + 1ULL"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 12, 12, 1, 1, 'IDENT12', "1.0 + 1LL"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 13, 13, 1, 1, 'IDENT13', "1.0 + 1UL"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 14, 14, 1, 1, 'IDENT14', "1.0 + 1L"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 15, 15, 1, 1, 'IDENT15', "1.0 + 1U"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 16, 16, 1, 1, 'IDENT16', "1.0 + 1"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 17, 17, 1, 1, 'IDENT17', "1.0 + 'a'"), 'double'),
        SimpleExpressionMacro(ObjectDefine(
            '', 18, 18, 1, 1, 'IDENT18', "1ULL + 1ULL"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 19, 19, 1, 1, 'IDENT19', "1ULL + 1LL"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 20, 20, 1, 1, 'IDENT20', "1ULL + 1UL"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 21, 21, 1, 1, 'IDENT21', "1ULL + 1L"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 22, 22, 1, 1, 'IDENT22', "1ULL + 1U"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 23, 23, 1, 1, 'IDENT23', "1ULL + 1"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 24, 24, 1, 1, 'IDENT24', "1ULL + 'a'"), 'unsigned long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 25, 25, 1, 1, 'IDENT25', "1LL + 1LL"), 'long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 26, 26, 1, 1, 'IDENT26', "1LL + 1UL"), 'long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 27, 27, 1, 1, 'IDENT27', "1LL + 1L"), 'long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 28, 28, 1, 1, 'IDENT28', "1LL + 1U"), 'long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 29, 29, 1, 1, 'IDENT29', "1LL + 1"), 'long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 30, 30, 1, 1, 'IDENT30', "1LL + 'a'"), 'long long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 31, 31, 1, 1, 'IDENT31', "1UL + 1UL"), 'unsigned long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 32, 32, 1, 1, 'IDENT32', "1UL + 1L"), 'unsigned long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 33, 33, 1, 1, 'IDENT33', "1UL + 1U"), 'unsigned long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 34, 34, 1, 1, 'IDENT34', "1UL + 1"), 'unsigned long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 35, 35, 1, 1, 'IDENT35', "1UL + 'a'"), 'unsigned long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 36, 36, 1, 1, 'IDENT36', "1L + 1L"), 'long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 37, 37, 1, 1, 'IDENT37', "1L + 1U"), 'long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 38, 38, 1, 1, 'IDENT38', "1L + 1"), 'long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 39, 39, 1, 1, 'IDENT39', "1L + 'a'"), 'long int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 40, 40, 1, 1, 'IDENT40', "1U + 1U"), 'unsigned int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 41, 41, 1, 1, 'IDENT41', "1U + 1"), 'unsigned int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 42, 42, 1, 1, 'IDENT42', "1U + 'a'"), 'unsigned int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 43, 43, 1, 1, 'IDENT43', "1 + 1"), 'int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 44, 44, 1, 1, 'IDENT44', "1 + 'a'"), 'int'),
        SimpleExpressionMacro(ObjectDefine(
            '', 45, 45, 1, 1, 'IDENT45', "'a' + 'a'"), 'char')
    ]


def test_classify_simple_expression_macros_type_casts():
    typenames = [
        '   long    double  ',
        '   double ',
        '   unsigned    long long int',
        '   long    long   int',
        '   unsigned    long    int',
        '   long int  ',
        'unsigned int',
        '   int        ',
        '   char ',
    ]
    macros = [
        ObjectDefine('', 1, 1, 1, 1, 'A', f'({typename}) 1')
        for typename in typenames
    ]
    result = [classify_macro(m) for m in macros]
    assert result == [
        SimpleExpressionMacro(m, ' '.join(t for t in typename.split()))
        for m, typename in zip(macros, typenames)]


def test_fully_classify_case_label_expression_macros():
    c_file = get_test_file_path('case_labels')
    macro_data = collect_macro_data(c_file)
    classified_macros = [classify_macro(macro) for macro in macro_data]
    check_macro_usage(classified_macros, c_file)

    assert classified_macros == [
        SimpleConstantMacro(
            ObjectDefine(c_file, 1, 1, 9, 1, 'RED', '1'), 'int', True, 'Switch2CaseLabels'),
        SimpleConstantMacro(
            ObjectDefine(c_file, 2, 2, 9, 1, 'GREEN', '2'), 'int', True, 'Switch1CaseLabels'),
        SimpleConstantMacro(
            ObjectDefine(c_file, 3, 3, 9, 1, 'BLUE', '3'), 'int', True, 'Switch1CaseLabels'),
        SimpleConstantMacro(
            ObjectDefine(c_file, 4, 4, 9, 1, 'MAGENTA', '4'), 'int', True, 'Switch3CaseLabels'),
        SimpleConstantMacro(
            ObjectDefine(c_file, 5, 5, 9, 1, 'CYAN', '5'), 'int', True, 'Switch4CaseLabels'),
        SimpleConstantMacro(
            ObjectDefine(c_file, 6, 6, 9, 1, 'YELLOW', '6'), 'int', True, 'Switch4CaseLabels'),
    ]
