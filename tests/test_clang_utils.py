'''
test_clang_utils.py

Test cases for utility functions used when working with Clang.
'''

import pytest
from clang.cindex import Cursor, CursorKind, Index
from macro_classifier.clang_utils import count_nested_case_statements, get_file_line_col


def test_get_file_line_col_file_is_none():
    '''
    Test that calling get_file_line_col raises a ValueError
    when the location file is None.
    '''

    c_code = '''int main(void) {return 0;}'''

    index = Index.create()
    tu = index.parse('tmp.c', None, [('tmp.c', c_code)])
    cursor = tu.cursor
    with pytest.raises(ValueError):
        get_file_line_col(cursor)


def test_get_file_line_col():
    '''
    Test that calling a get_file_line_col on a cursor with a valid
    file, line, and column returns the expected 3-tuple.
    '''

    c_code = '''int main(void) {return 0;}'''

    index = Index.create()
    tu = index.parse('tmp.c', None, [('tmp.c', c_code)])
    cursor = tu.cursor
    cur: Cursor
    for cur in cursor.walk_preorder():
        if cur.displayname == 'main()':
            assert get_file_line_col(cur) == ('tmp.c', 1, 5)
            return


def test_count_nested_case_statements():
    c_code = '''
    int main() {
        switch (0) {
            case 1:
                case 2:
                    case 3:
                        break;
        case 4:
            switch (0) {
                case 1:
                    case 2:
                        break;
            }
        case 5:
            break;
        default:
        break;
        }
        return 0;
    }
    '''

    expected_results = {
        ('tmp.c', 4, 13): 3,
        ('tmp.c', 5, 17): 2,
        ('tmp.c', 6, 21): 1,
        ('tmp.c', 8, 9): 1,
        ('tmp.c', 10, 17): 2,
        ('tmp.c', 11, 21): 1,
        ('tmp.c', 14, 9): 1,
    }

    index = Index.create()
    tu = index.parse('tmp.c', None, [('tmp.c', c_code)])
    cursor = tu.cursor
    cur: Cursor
    for cur in cursor.walk_preorder():
        if cur.kind == CursorKind.CASE_STMT:
            flc = get_file_line_col(cur)
            assert expected_results[flc] == count_nested_case_statements(cur)
