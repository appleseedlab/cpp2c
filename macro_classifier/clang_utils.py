'''
clang_utils.py

Helper functions for working with Clang.
'''

from typing import Tuple

from clang.cindex import Cursor, CursorKind, SourceLocation

# A FileLineCol summarizes a SourceLocation object into a hashable tuple
FileLineCol = Tuple[str, int, int]


def get_file_line_col(cursor: Cursor) -> FileLineCol:
    '''
    Extract the location of a cursor into a 3-tuple.

    Args:
        cursor: The cursor whose location to extract.

    Returns:    A 3-tuple containing the filename, line number, and column
                of the given cursor.

    Raises:
        ValueError: If the cursor does not have a location or the filename
                    of the cursor's location is not a str.
    '''

    location: SourceLocation = cursor.location
    if location.file is None:
        raise ValueError("Cursor location file is None")
    if not isinstance(location.file.name, str):
        raise ValueError("Cursor location file name is not a str")

    return (location.file.name, location.line, location.column)


def count_nested_case_statements(root: Cursor) -> int:
    '''
    Clang returns a parse tree, not an AST.
    This causes an issue when parsing switch statements
    that have case statements without breaks between them.

    If a case statement X has another case statement Y following it without
    a break statement between them, then Y will be parsed as a *child*
    of X, not as the immediately following sibling.
    This causes problems when trying to correctly enumerate case statements
    in a given switch statement.
    pycparser fixes this problem, but I'd rather fix this to work with
    Clang so that I can possibly remove the pycparser dependency
    in the future.

    See https://tinyurl.com/3jd82sx6 for more information

    Args:
        root:   The root cursor to begin counting nested case statements
                at.

    Returns:    The count of case statements at and below the root.
    '''
    if root is None or root.kind != CursorKind.CASE_STMT:
        return 0
    child: Cursor
    for child in root.get_children():
        # If there is a nested case label, it will be
        # the only case statement child of this cursor
        if child.kind == CursorKind.CASE_STMT:
            return 1 + count_nested_case_statements(child)

    return 1
