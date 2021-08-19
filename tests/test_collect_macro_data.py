import os
from typing import Tuple
from unittest import TestCase

from macro_data_collector.collect_macro_data import collect_macro_data
from macro_data_collector.directives import ObjectDefine


def test_file_paths(fn: str) -> Tuple[str, str]:
    cur_dir = os.path.dirname(__file__)
    return (os.path.join(cur_dir, fn + ".txt"),
            os.path.join(cur_dir, fn + ".c"))


class CollectMacroDataTests(TestCase):

    def test_collect_simple_constants(self):
        stats_file, c_file = test_file_paths("simple_constants")
        result = collect_macro_data(stats_file, c_file)
        self.assertEqual(
            result,
            [ObjectDefine(file='/home/bpappas/cpp_to_c/tests/simple_constants.c', line=2, column=1, definition_count=1, identifier='A', body='1  //  int'),
             ObjectDefine(file='/home/bpappas/cpp_to_c/tests/simple_constants.c', line=3, column=1, definition_count=1, identifier='B', body='-1 //  int')]
        )
