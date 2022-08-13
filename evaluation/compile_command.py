import json
from dataclasses import dataclass
from typing import List

CPP2C_SO_PATH = r'/home/bpappas/cpp2c/implementation/build/lib/libCpp2C.so'


@dataclass
class CompileCommand:
    arguments: List[str]
    directory: str
    file: str


def load_compile_commands_from_file(file: str) -> List[CompileCommand]:
    with open(file) as fp:
        return [CompileCommand(**cc) for cc in json.load(fp)]


def cpp2c_command_from_compile_command(cc: CompileCommand, cpp2c_commands: List[str]) -> str:
    # Shallow copy arguments (shallow is fine since they're strings)
    arguments = cc.arguments[:]
    # Replace '-flto=auto' argument with '-flto=full'
    # This is because Clang does not support this flag
    # This specifically fixes an issue with building remind 4.00.01
    arguments = ['-flto=full' if a == '-flto=auto' else a for a in arguments]
    # Escape spaces in ghostscript's arguments
    # This is because Clang will interpret an argument with spaces in it
    # as multiple arguments
    # This specifically fixes an issue with ghostscript 9.56.1
    arguments = ["-DGX_COLOR_INDEX_TYPE=unsigned\\ long\\ long"
                    if a == "-DGX_COLOR_INDEX_TYPE=unsigned long long"
                    else a
                    for a in arguments]
    # Replace first command (compiler) with clang-11
    arguments[0] = 'clang-11'
    # Add Cpp2C plugin path
    arguments.insert(1, f'-fplugin={CPP2C_SO_PATH}')
    # Remove the file from the arguments list (last argument)
    file = arguments.pop()
    # Add Cpp2C transformer options before the file
    for cmd in cpp2c_commands:
        arguments.extend([
            '-Xclang',
            '-plugin-arg-cpp2c',
            '-Xclang',
            cmd,
        ])
    arguments.append('-fsyntax-only')
    arguments.append(file)
    # Join the arguments to create the command
    return ' '.join(arguments)
