'''
__init__.py

This file needs to exist for pytest to be able to correctly
identify import paths.

Also contains constants and utility functions used across different
sets of test cases.
'''

import os
from typing import Tuple

TEST_INPUT_DIRNAME = "c_files"

TEST_INPUT_DIRPATH = os.path.abspath(os.path.join(
    os.path.dirname(__file__), TEST_INPUT_DIRNAME))


def get_test_file_paths(fn: str) -> Tuple[str, str]:
    return (os.path.join(TEST_INPUT_DIRPATH, fn + ".txt"),
            os.path.join(TEST_INPUT_DIRPATH, fn + ".c"))
