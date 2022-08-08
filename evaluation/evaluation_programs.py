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
    # no tests - but ran the program manually after transforming
    # and it seems to work
    EvaluationProgram(
        r'ncsa-mosaic-af1c9aaaa299da3540faa16dcab82eb681cf624e',
        r'https://github.com/alandipert/ncsa-mosaic/archive/af1c9aaaa299da3540faa16dcab82eb681cf624e.zip',
        r'src',
        r'bear make linux',
        r''
    ),

    # transforms
    # takes less than a second
    # failed tests.
    # problem:  stdio's getline is redeclared in lib/getline.c and
    #           redefined in lib/getline.h.
    #           this is actually a problem with cvs itself and not cpp2c.
    # fix:      i changed the name of cvs's getline function to getline_cvs
    #           i was then able to build cvs and run its tests.
    #           it still failed one test, basicb-21.
    #           i ran this test on the untransformed code and it failed
    #           as well.
    #           since it fails in both the untransformed and transformed
    #           program, i consider the transformation working as expected.
    # now passes tests.
    EvaluationProgram(
        r'cvs-1.11.21',
        r'https://cfhcable.dl.sourceforge.net/project/ccvs/CVS%20Stable%20Source%20Release/1.11.21/cvs-1.11.21.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # takes 70 sec
    # failed tests.
    # problem:  in term.c, some headers were included inside of a struct
    #           definition.
    #           after transforming, some transformed decls were emitted to
    #           the top of these header files.
    #           this ultimately meant that in the transformed code,
    #           after preprocessing some decls were being placed
    #           inside the struct definition, which of course is invalid C.
    # fix:      move the problematic decls outside of the struct definition.
    #           gnuplot then passed all tests.
    # now passes tests.
    EvaluationProgram(
        r'gnuplot-5.4.4',
        r'https://cytranet.dl.sourceforge.net/project/gnuplot/gnuplot/5.4.4/gnuplot-5.4.4.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # takes 2 min
    # fails tests.
    # problem:  in Fft.h, there is an anonymous struct typedef'd to
    #           the name XftPatternElt.
    #           XftPatternElt is then typedef'd to FftPatternElt.
    #           this causes the deanonymizer to emit both names before the
    #           struct definition for some reason, which is invalid C code.
    # fix:      remove the XftPatternElt part of the struct name emitted by
    #           the deanonymizer.
    # problem:  in FSMlib.h, the enum IceCloseStatus is typedef'd to
    #           FIceCloseStatus.
    #           cpp2c uses the base enum name,
    #           not the typedef, in transformed decl at the top of the
    #           file and the def in another file.
    # fix:      replace the enum with the typedef in the decl and def,
    #           and move the decl after the the typedef.
    # problem:  ditto IceProcessMessagesStatus/FIceProcessMessagesStatus
    # problem:  ditto IceConnectStatus/FIceConnectStatus;
    # problem:  some macros returned anonymous nested structs.
    #           the deanonymizer did not deanonymize these, and clang
    #           emitted a name for them that was invalid c.
    #           e.g. MenuRootDynamic::(anonymous at ./menuroot.h:143:2)
    # fix:      manually deanonymize these nested structs and use these
    #           names in the transformed function signatures.
    # problem:  nested typedefs issue
    EvaluationProgram(
        r'fvwm-2.6.9',
        r'https://github.com/fvwmorg/fvwm/releases/download/2.6.9/fvwm-2.6.9.tar.gz',
        r'fvwm',
        r'bash configure --disable-png && bear make',
        r'''
        make clean                  &&
        make                        &&
        cd  tests                   &&
        bash test_options
        '''
    ),

    # transforms
    # takes a few mins
    # failed tests.
    # problem:  for some reason, a series of function names were emitted
    #           before the invocation of ARGMATCH_DEFINE_GROUP in
    #           complain.c.
    # fix:      commented out the extra type names.
    # problem:  ditto in getargs.c, except for multiple invocations of
    #           ARGMATCH_DEFINE_GROUP, not just one.
    # problem:  an invocation of YY_INITIAL_VALUE in parse-gram.c
    #           was not transformed correctly.
    # fix:      manually fixed the invocation.
    # problem:  ditto PACIFY_CC in tables.c
    # now passes tests.
    EvaluationProgram(
        r'bison-3.8.2',
        r'https://mirrors.nav.ro/gnu/bison/bison-3.8.2.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # NOTE: There is a more up to date version of rcs available,
    # but it's in a tar.lz file.
    # TODO: Automate extraction of tar.lz files

    # transforms
    # takes 1 sec
    # failed tests.
    # problem:  gets is used where fgets should be used instead.
    #           this is a problem with rcs itself.
    # fix:      followed this solution:
    #           https://www.fatalerrors.org/a/gets-undeclared-here-not-in-a-function.html
    # problem:  program tests failed after fixing compilation issues.
    # fix:      ran make clean, make distclean, ./configure, and make again.
    #           finally ran make check again; all tests passed.
    # now passes tests.
    EvaluationProgram(
        r'rcs-5.8',
        r'https://mirror.koddos.net/gnu/rcs/rcs-5.8.tar.gz',
        r'src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # takes 7 min
    # failed tests.
    # problem:  in builtin.c, the macro INITIAL_OUT_SIZE was used in
    #           a transformed definition of GIVE_BACK_SIZE before
    #           INITIAL_OUT_SIZE was defined.
    # fix:      moved the transformed def of GIVE_BACK_SIZE after the
    #           definition of the macro INITIAL_OUT_SIZE.
    # problem:  in testext.c, some transformed function parameters were
    #           named scalar_cookie, which was the name of a macro defined in
    #           gawkapi.h.
    # fix:      changed the name of the function parameter to a fresh name.
    # now passes tests.
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

    # requires xaw3dg-dev
    # transforms
    # takes 50 sec
    # failed tests.
    # problem:  nested typedefs and anonymous structs issue.
    #           in resources.h, PR_SIZE and RECT.
    # fix:      fix emitted deanonymized names.
    # problem:  in some files, the transformed definition of max_char_height
    #           referenced the anonymous, typedef'd struct XFontStruct
    #           before it was defined.
    #           the deanonymizer didn't catch this because it's defined
    #           in a system header (X11), which we don't emit rewrites to.
    # fix:      remove the struct keyword from function definitions and use
    #           the typedef instead.
    # NOTE:     we could automatically handle these cases by not deanonymizing
    #           system header structs/unions/enums, and using their typedefs
    #           instead.
    # now passes tests.
    EvaluationProgram(
        r'xfig-3.2.8b',
        r'https://cytranet.dl.sourceforge.net/project/mcj/xfig%2Bfig2dev-3.2.8b.tar.xz',
        r'fig2dev',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # takes 70 sec
    # fails tests.
    # requires: autoconf
    # problem:  definition heuristic emitted a function that returned an
    #           anonymous typedef'd struct, __sigset_t.
    #           normally the deanonymizer would fix this by making the struct
    #           not anonymous, but since the struct is defined in a standard
    #           header, the deanonymizer wasn't able to rewrite it.
    # fix:      change all the functions that returned this type to
    #           the typedef instead of the struct
    # problem:  in the original code, some part of the build system
    #           generates .pro files with function forward declarations.
    #           after transforming, thes .pro files aren't generated
    #           correctly, and lacks some of these declarations.
    #           consequently, man files have undeclared reference errors.
    # fix:      add the required decls back to the .pro files.
    #           there are 80+ of these files, so to speed this process up
    #           i first built zsh before transforming it, and committed
    #           the result to a fresh git repo.
    #           then i ran the transformer, built again, and reverted all
    #           the .epro and .pro to their contents prior transformation.
    #           as i modified source files to fix other problems, make would
    #           regenerate these .epro and .pro files, but i would always
    #           revert them back to their prior-transformation state.
    # problem:  a series of macros defined in pattern.c, patinstart through
    #           globdots, are defined to expand to struct fields of the
    #           same name.
    #           the transformed definitions use the names as struct fields,
    #           however they are emitted after the macro definitions, so
    #           the preprocessor thinks they are referring to the macro
    #           definitions, and expand them.
    #           this expands to incorrect code.
    # fix:      comment out these macro definitions.
    # problem:  after fixing the last problem, invocation of these macros
    #           broke.
    # fix:      inline broken macro invocations.
    # problem:  macro ZF_BUFSIZE undeclared before use in zftp.c
    # fix:      move macro definition above first use
    #           (trivial since it was defined as an integer constant)
    # now passes tests.
    EvaluationProgram(
        r'zsh-5.9',
        r'https://cfhcable.dl.sourceforge.net/project/zsh/zsh/5.9/zsh-5.9.tar.xz',
        r'Src',
        r'bash configure && bear make',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

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

    # # TODO: Will take a very long time to run
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

    # # TODO: remove? has manual install instructions...
    # EvaluationProgram(
    #     r'rasmol-2.7.5.2',
    #     r'http://www.rasmol.org/software/RasMol_Latest.tar.gz',
    #     r'src',
    #     r'',
    #     r'''
    #     '''
    # ),

    # # TODO: remove? has lengthy instructions and not easy to intercept
    # #       its build system
    # EvaluationProgram(
    #     r'zephyr-main',
    #     r'https://github.com/zephyrproject-rtos/zephyr/archive/refs/heads/main.zip',
    #     r'',
    #     r'',
    #     f'''
    #     '''
    # ),

    # # can't get to work
    # # this was made for sun solaris systems, not for linux, and I cannot
    # # install one of the packages its requires (xview)
    # # transforms?
    # # takes ...
    # # passes tests?
    # EvaluationProgram(
    #     r'workman-1.3.4',
    #     r'https://web.mit.edu/kolya/.f/root/net.mit.edu/sipb/user/zacheiss/workman-1.3.4.tar.gz',
    #     r'',
    #     r'',
    #     r''
    # ),

    # # transforms
    # # takes 26 sec
    # # failed tests.
    # # problem:  GNU chess is written in a mix of c and c++ code.
    # #           we don't support transforming c++ code.
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

]
