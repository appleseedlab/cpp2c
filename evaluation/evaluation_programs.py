import os
from dataclasses import dataclass

EXTRACTED_EVALUATION_PROGRAMS_DIR = r'extracted_evaluation_programs/'
LUA_TESTS_ZIP = 'lua-5.4.4-tests.tar.gz'
LUA_TESTS_DIR = 'lua-5.4.4-tests'


@dataclass
class EvaluationProgram:
    name: str
    link_to_archive_file: str
    src_dir: str

    configure_script: str
    '''
    Script to configure the program.
    Assumes it is run inside the top-level directory of the
    extracted archive.
    '''

    test_script: str
    '''
    Script to test that the program works.
    Assumes it is run inside the top-level directory of the
    extracted archive.
    '''

    @property
    def archive_file(self) -> str:
        '''Where the archive file should be after downloading'''
        return self.link_to_archive_file[self.link_to_archive_file.rfind(r'/')+1:]

    @property
    def extract_dir(self) -> str:
        '''Where the archive file should be extracted to'''
        return EXTRACTED_EVALUATION_PROGRAMS_DIR

    @property
    def extracted_archive_path(self) -> str:
        '''Path to the top-level directory of the extracted archive'''
        return os.path.join(EXTRACTED_EVALUATION_PROGRAMS_DIR, self.name)


EVALUATION_PROGRAMS = [
    EvaluationProgram(
        r'bc-1.07',
        r'https://mirrors.kernel.org/gnu/bc/bc-1.07.tar.gz',
        r'bc',
        r'bash configure',
        r'''
        make clean                  &&
        make                        &&
        make check                  &&
        cd Test                     &&
        bash timetest 1>/dev/null
        '''
    ),

    EvaluationProgram(
        r'gzip-1.10',
        r'https://gnu.mirror.constant.com/gzip/gzip-1.10.tar.gz',
        r'.',
        r'bash configure',
        r'''
        make clean  &&
        make        &&
        make check
        '''
    ),

    EvaluationProgram(
        r'remind-03.04.02',
        r'https://dianne.skoll.ca/projects/remind/download/OLD/remind-03.04.02.tar.gz',
        r'src',
        r'bash configure',
        r'''
        make clean      &&
        make            &&
        make test
        '''
    ),

    EvaluationProgram(
        r'lua-5.4.4',
        r'https://www.lua.org/ftp/lua-5.4.4.tar.gz',
        r'src',
        r'',
        f'''
        make                        &&
        if [[ -e {LUA_TESTS_DIR} ]]; then rm -fr {LUA_TESTS_DIR}; fi    &&
        cd ../                      &&
        tar -xvf ../{LUA_TESTS_ZIP} &&
        cd {LUA_TESTS_DIR}          &&
        ../lua-5.4.4/src/lua -e"_U=true" all.lua 1>/dev/null
        '''
    ),

    # EvaluationProgram(
    #     r'test',
    #     r'test.zip',
    #     r'.',
    #     r'',
    #     r''
    # )
]
