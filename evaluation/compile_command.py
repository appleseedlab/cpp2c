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
    arguments.append(file)
    # Join the arguments to create the command
    return ' '.join(arguments)
