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

    # transforms
    # takes 75 sec
    # passes tests
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

    # transforms
    # takes 7 sec
    # passes tests
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

    # transforms
    # takes 5 sec
    # passes tests
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

    # transforms
    # takes ...
    # passes tests
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

    # transforms
    # takes 7 min
    # passes all expected tests
    # fails some tests, but only the ones it failed before transforming
    # requires help2man
    EvaluationProgram(
        r'm4-1.4.19',
        r'https://ftp.gnu.org/gnu/m4/m4-1.4.19.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # takes 1 min
    # passes tests
    EvaluationProgram(
        r'bash-5.2-rc1',
        r'https://mirror.us-midwest-1.nexcess.net/gnu/bash/bash-5.2-rc1.tar.gz',
        r'.',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # takes 11 sec
    # passes tests
    EvaluationProgram(
        r'flex-2.6.4',
        r'https://github.com/westes/flex/files/981163/flex-2.6.4.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # requires xaw3dg-dev
    # transforms
    # takes 17 sec
    # passes tests
    EvaluationProgram(
        r'gv-3.7.4',
        r'https://mirrors.sarata.com/gnu/gv/gv-3.7.4.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean  &&
        make        &&
        make check
        '''
    ),

    # note: this is genscript from the ernst study
    # the g stands for GNU
    # transforms
    # takes 10 sec
    # passes tests
    EvaluationProgram(
        r'enscript-1.6.6',
        r'https://ftp.gnu.org/gnu/enscript/enscript-1.6.6.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean      &&
        make            &&
        make check
        ''',
    ),

    # found it!
    # do you know how hard it is to find something on the Internet
    # with such a generic name as "plan" ? :-)

    # requires libmotif-dev
    # transforms
    # takes 23 sec
    # no tests - but manually ran the program after
    # transforming and it seems to work
    EvaluationProgram(
        r'plan-1.12',
        r'ftp://ftp.bitrot.de/pub/plan/plan-1.12.tar.gz',
        r'src',
        '''
        cd src                          &&
        echo "\\n" | bash configure     &&
        bear make linux64               &&
        mv compile_commands.json ..     &&
        cd ..
        ''',
        r''
    ),

    # mosaic
    # requires  build-essential libmotif-dev libjpeg62-dev
    #           libxmu-headers libxpm-dev libxmu-dev
    # transforms
    # takes 34 sec
    # TODO: fails tests - definition heuristic
    # no tests - but ran the program manually after transforming
    # and it seems to work
    EvaluationProgram(
        r'ncsa-mosaic-af1c9aaaa299da3540faa16dcab82eb681cf624e',
        r'https://github.com/alandipert/ncsa-mosaic/archive/af1c9aaaa299da3540faa16dcab82eb681cf624e.zip',
        r'src',
        r'bear make linux',
        r''
    ),

    # # transforms
    # takes less than a second
    # fails tests due to definition location heuristic
    # TODO: fix definition location heuristic
    # EvaluationProgram(
    #     r'cvs-1.11.21',
    #     r'https://cfhcable.dl.sourceforge.net/project/ccvs/CVS%20Stable%20Source%20Release/1.11.21/cvs-1.11.21.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # transforms
    # # takes 70 sec
    # # fails tests because in term.c, term.h is included *inside* the
    # # definition of the struct term_tbl
    # # TODO: Maybe we can fix with smarter definition locations?
    # EvaluationProgram(
    #     r'gnuplot-5.4.4',
    #     r'https://cytranet.dl.sourceforge.net/project/gnuplot/gnuplot/5.4.4/gnuplot-5.4.4.tar.gz',
    #     r'src/win',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # transforms
    # # takes 70 sec
    # # fails tests due to definition location heuristic
    # # TODO: fix definition location heuristic
    # EvaluationProgram(
    #     r'zsh-5.9',
    #     r'https://cfhcable.dl.sourceforge.net/project/zsh/zsh/5.9/zsh-5.9.tar.xz',
    #     r'Src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # transforms
    # # takes 2 min
    # # fails tests because of deanonymizer breaking on nested typedefs
    # # TODO: fix deanonymizer to work with nested typedefs
    # EvaluationProgram(
    #     r'fvwm-2.6.9',
    #     r'https://github.com/fvwmorg/fvwm/releases/download/2.6.9/fvwm-2.6.9.tar.gz',
    #     r'fvwm',
    #     r'bash configure --disable-png && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     cd  tests                   &&
    #     bash test_options
    #     '''
    # ),

    # # transforms
    # # takes a few mins
    # # fails tests due to definition location heuristic
    # # TODO: fix definition location heuristic
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

    # # NOTE: There is a more up to date version of rcs available,
    # # but it's in a tar.lz file.
    # # TODO: Automate extraction of tar.lz files

    # # TODO: design a correct way of finding a definition location
    # # transforms
    # # does not pass tests because definition location heuristic does not work
    # # takes 1 sec
    # EvaluationProgram(
    #     r'rcs-5.8',
    #     r'https://mirror.koddos.net/gnu/rcs/rcs-5.8.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # TODO: design a correct way of finding a definition location
    # # transforms
    # # does not pass tests because definition location heuristic does not work
    # # takes 7 min
    # EvaluationProgram(
    #     r'gawk-5.1.1',
    #     r'https://ftp.gnu.org/gnu/gawk/gawk-5.1.1.tar.gz',
    #     r'.',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # TODO: either remove or fix issue with .cc files
    # # transforms
    # # does not pass tests because of .cc files
    # # takes 26 sec
    # EvaluationProgram(
    #     r'gnuchess-6.2.9',
    #     r'https://gnu.mirror.constant.com/chess/gnuchess-6.2.9.tar.gz',
    #     r'src',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # requires xaw3dg-dev
    # # transforms
    # # takes 50 sec
    # # TODO: fails tests because of deanonymizer issue
    # EvaluationProgram(
    #     r'xfig-3.2.8b',
    #     r'https://cytranet.dl.sourceforge.net/project/mcj/xfig%2Bfig2dev-3.2.8b.tar.xz',
    #     r'fig2dev',
    #     r'bash configure && bear make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),



    # # TODO: Takes more than an hour to run (or more)
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

    # TODO: Will take a very long time to run
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

    # # TODO: install GMP 4.2+, MPFR 3.1.0+ and MPC 0.8.0+
    # # May take 4 hr
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

    # # TODO: install GTK+ libXpm libjpeg libpng libgif/libungif libtiff gnutls
    # # for emacs to configure and build
    # # May take about 20 min
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

    # TODO: remove? has manual install instructions...
    # EvaluationProgram(
    #     r'rasmol-2.7.5.2',
    #     r'https://www.rasmol.org/software/RasMol_Latest.tar.gz',
    #     r'src',
    #     r'',
    #     r'''
    #     '''
    # ),

    # TODO: remove? has lengthy instructions and not easy to intercept
    #       its build system
    # EvaluationProgram(
    #     r'zephyr-main',
    #     r'https://github.com/zephyrproject-rtos/zephyr/archive/refs/heads/main.zip',
    #     r'',
    #     r'',
    #     f'''
    #     '''
    # ),

    # can't get to work
    # this was made for sun solaris systems, not for linux, and I cannot
    # install one of the packages its requires (xview)
    # transforms?
    # takes ...
    # passes tests?
    # EvaluationProgram(
    #     r'workman-1.3.4',
    #     r'https://web.mit.edu/kolya/.f/root/net.mit.edu/sipb/user/zacheiss/workman-1.3.4.tar.gz',
    #     r'',
    #     r'',
    #     r''
    # ),
]
