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

    configure_compile_commands_script: str
    '''
    Script to configure the program and generate its compile_commands.json.
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

    # EvaluationProgram(
    #     r'test',
    #     r'test.zip',
    #     r'.',
    #     r'bear make',
    #     r''
    # ),

    # works
    EvaluationProgram(
        r'gzip-1.12',
        r'https://mirrors.tripadvisor.com/gnu/gzip/gzip-1.12.tar.gz',
        r'.',
        r'bash configure && bear make',
        r'''
        make clean  &&
        make        &&
        make check
        '''
    ),

    # works
    EvaluationProgram(
        r'remind-04.00.01',
        r'https://dianne.skoll.ca/projects/remind/download/remind-04.00.01.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean      &&
        make            &&
        make test
        '''
    ),

    # works
    EvaluationProgram(
        r'bc-1.07.1',
        r'https://gnu.mirror.constant.com/bc/bc-1.07.1.tar.gz',
        r'bc',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check                  &&
        cd Test                     &&
        bash timetest 1>/dev/null
        '''
    ),

    # works
    EvaluationProgram(
        r'lua-5.4.4',
        r'https://www.lua.org/ftp/lua-5.4.4.tar.gz',
        r'src',
        r'bear make',
        f'''
        make clean                  &&
        make                        &&
        if [[ -e {LUA_TESTS_DIR} ]]; then rm -fr {LUA_TESTS_DIR}; fi    &&
        cd ../                      &&
        tar -xvf ../{LUA_TESTS_ZIP} &&
        cd {LUA_TESTS_DIR}          &&
        ../lua-5.4.4/src/lua -e"_U=true" all.lua 1>/dev/null
        '''
    ),

    # works
    EvaluationProgram(
        r'gnuchess-6.2.9',
        r'https://gnu.mirror.constant.com/chess/gnuchess-6.2.9.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # works
    EvaluationProgram(
        r'gawk-5.1.1',
        r'https://ftp.gnu.org/gnu/gawk/gawk-5.1.1.tar.gz',
        r'.',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # EvaluationProgram(
    #     r'perl-5.36.0',
    #     r'https://www.cpan.org/src/5.0/perl-5.36.0.tar.gz',
    #     r'.',
    #     r'bash Configure && bear make',
    #     r'''
    #     bash Configure 	&&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'zephyr-main',
    #     r'https://github.com/zephyrproject-rtos/zephyr/archive/refs/heads/main.zip',
    #     r'',
    #     r'',
    #     f'''
    #     '''
    # ),

    # EvaluationProgram(
    #     r'bash-5.2-rc1',
    #     r'https://mirror.us-midwest-1.nexcess.net/gnu/bash/bash-5.2-rc1.tar.gz',
    #     r'.',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'ghostscript-9.56.1',
    #     r'https://github.com/ArtifexSoftware/ghostpdl-downloads/releases/download/gs9561/ghostscript-9.56.1.tar.gz',
    #     r'',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'gnuplot-5.4.3',
    #     r'https://sourceforge.net/projects/gnuplot/files/gnuplot/5.4.3/gnuplot-5.4.3.tar.gz/download',
    #     r'src/win',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'emacs-28.1',
    #     r'https://ftp.snt.utwente.nl/pub/software/gnu/emacs/emacs-28.1.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'rcs-5.10.1',
    #     r'https://mirror.koddos.net/gnu/rcs/rcs-5.10.1.tar.lz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'm4-1.4.19',
    #     r'https://ftp.gnu.org/gnu/m4/m4-1.4.19.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'flex-2.6.4',
    #     r'https://github.com/westes/flex/files/981163/flex-2.6.4.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # EvaluationProgram(
    # #     r'rasmol-2.7.5.2',
    # #     r'https://www.rasmol.org/software/RasMol_Latest.tar.gz',
    # #     r'src',
    # #     r'',
    # #     r'''
    # #     '''
    # # ),

    # EvaluationProgram(
    #     r'cvs-1.11.21',
    #     r'https://sourceforge.net/projects/ccvs/files/latest/download',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'fvwm-2.6.9',
    #     r'https://github.com/fvwmorg/fvwm/releases/download/2.6.9/fvwm-2.6.9.tar.gz',
    #     r'fvwm',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     cd  tests                   &&
    #     bash test_options
    #     '''
    # ),

    # EvaluationProgram(
    #     r'zsh-5.9',
    #     r'https://sourceforge.net/projects/zsh/files/latest/download',
    #     r'Src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'gv-3.7.4',
    #     r'https://mirrors.sarata.com/gnu/gv/gv-3.7.4.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     '''
    # ),

    # EvaluationProgram(
    #     r'gcc-12.1.0',
    #     r'https://bigsearcher.com/mirrors/gcc/releases/gcc-12.1.0/gcc-12.1.0.tar.gz',
    #     r'gcc',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'bison-3.8.2',
    #     r'https://mirrors.nav.ro/gnu/bison/bison-3.8.2.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # EvaluationProgram(
    #     r'xfig-3.2.8a',
    #     r'https://sourceforge.net/projects/mcj/files/latest/download',
    #     r'fig2dev',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),
]
