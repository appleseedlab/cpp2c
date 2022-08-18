'''abstractometer.py
    
measures abstraction factor
'''

from typing import List, Set, Dict

import clang.cindex


def depth(c: clang.cindex.Cursor) -> int:
    '''typical tree depth algorithm'''
    return 0 if c is None else max([1 + depth(ch) for ch in c.get_children()], default=0)


def get_expr_depths(c: clang.cindex.Cursor) -> List[int]:
    '''
    counts the depths of all the expression nodes under a node
    and returns them as a list
    '''
    if c is None:
        return []
    result = []
    k: clang.cindex.CursorKind = c.kind
    if k.is_expression():
        # print(' '.join([t.spelling for t in c.get_tokens()]))
        result += [depth(c)]
    else:
        for ch in c.get_children():
            result += get_expr_depths(ch)
    return result


def get_func_var_names(c: clang.cindex.Cursor) -> Set[str]:
    '''
    returns the set of all declared function and variable names in the program
    '''
    assert(c is not None)
    k: clang.cindex.CursorKind = c.kind
    assert(k == clang.cindex.CursorKind.TRANSLATION_UNIT)

    result = set()
    for ch in c.get_children():
        ck = ch.kind

        # function names
        if ck == clang.cindex.CursorKind.FUNCTION_DECL:
            # print(c.mangled_name, c.location)
            result.add(ch.mangled_name)

        # variable names
        elif ck == clang.cindex.CursorKind.VAR_DECL:
            # print(c.mangled_name, c.location)
            result.add(ch.mangled_name)
    return result


def get_unique_decls_refd(c: clang.cindex.Cursor) -> Set[str]:
    '''
    returns the set of all unique decls referenced under a node
    '''
    if c is None:
        return set()
    result = set()
    k: clang.cindex.CursorKind = c.kind
    if k == clang.cindex.CursorKind.DECL_REF_EXPR:
        result.add(c.displayname)
    else:
        for ch in c.get_children():
            result |= get_unique_decls_refd(ch)
    return result


def get_unique_decls_refd_in_function_definitions(
    c: clang.cindex.Cursor) -> Dict[str, Set[str]]:
    '''
    maps the name of each function and global variable to the set of
    all unique symbols that appear in its definition/initializer.
    '''
    assert(c is not None)
    k: clang.cindex.CursorKind = c.kind
    assert(k == clang.cindex.CursorKind.TRANSLATION_UNIT)

    result = {}
    for ch in c.get_children():
        ck: clang.cindex.CursorKind = ch.kind

        # function definitions
        # this gets both decls and defs, but we only want to look at defs
        if ck == clang.cindex.CursorKind.FUNCTION_DECL:
            ts = [t for t in ch.get_tokens()]
            # if the last token is a closing curly brace, then this must
            # be a def and not a decl
            if ts[-1].spelling == '}':
                # print(' '.join([t.spelling for t in ts]))
                result[ch.mangled_name] = get_unique_decls_refd(ch)
                

        # global variable initializations
        # this gets both decls and inits, but we only want inits
        elif ck == clang.cindex.CursorKind.VAR_DECL:
            ts = [t for t in ch.get_tokens()]
            # if the token list contains an assignment, then this must
            # be an init, and not a decl
            if any(['=' == t.spelling for t in ts]):
                result[ch.mangled_name] = get_unique_decls_refd(ch)
    return result


if __name__ == '__main__':
    main()
