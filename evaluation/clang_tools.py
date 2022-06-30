from collections import defaultdict
import json
from typing import Dict, Set

import clang.cindex


def collect_annotations_of_func_and_var_decls_emitted_by_cpp2c(filepath: str) -> Dict[str, Dict]:
    '''
    Returns a dict mapping decl name's to their- parsed Cpp2C JSON annotations
    '''
    result = {}
    idx: clang.cindex.Index = clang.cindex.Index.create()
    tu: clang.cindex.TranslationUnit = idx.parse(filepath)
    cur: clang.cindex.Cursor = tu.cursor

    for child in cur.walk_preorder():
        ck: clang.cindex.CursorKind = child.kind
        # Only consider function declarations and variable declarations
        if ck in [clang.cindex.CursorKind.FUNCTION_DECL, clang.cindex.CursorKind.VAR_DECL]:
            for subchild in child.walk_preorder():
                sck: clang.cindex.CursorKind = subchild.kind
                if sck.is_attribute():
                    # print(subchild.displayname)
                    if 'CPP2C' in subchild.displayname:
                        result[child.displayname] = json.loads(
                            subchild.displayname)
    return result


def map_macro_hashes_to_unique_transformed_invocations(
        filepath: str,
        transformed_decl_names_to_macro_hashes: Dict[str, str],
        canonical_transformed_decl_names: Set[str]) -> Dict[str, int]:
    '''
    Returns a dict mapping hashes of macros to the number of
    unique transformed invocations found for them in the given
    source file
    '''
    result: Dict[str, int] = defaultdict(int)
    idx: clang.cindex.Index = clang.cindex.Index.create()
    tu: clang.cindex.TranslationUnit = idx.parse(filepath)
    cur: clang.cindex.Cursor = tu.cursor

    transformed_decl_names = transformed_decl_names_to_macro_hashes.keys()

    for node in cur.walk_preorder():
        # Visit each function definition and variable initialization
        k: clang.cindex.CursorKind = node.kind
        if k.is_declaration():
            if node.is_definition():
                name = node.displayname
                if (name not in transformed_decl_names or
                        (name in transformed_decl_names and name in canonical_transformed_decl_names)):
                    for subchild in node.walk_preorder():
                        if subchild.kind == clang.cindex.CursorKind.DECL_REF_EXPR:
                            referenced_name = subchild.displayname
                            if referenced_name in transformed_decl_names:
                                mhash = transformed_decl_names_to_macro_hashes[referenced_name]
                                result[mhash] += 1
                                # Remove this name from the set of canonical names so we don't
                                # visit it again (can happen if this definition is #included)
                                # in multiple compilation units
                                # Use `discard` because a canon def may contain multiple
                                # transformed invocations
                                canonical_transformed_decl_names.discard(name)
    return result
