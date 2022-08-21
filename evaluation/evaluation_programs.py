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
    #     r'intercept-build make',
    #     r''
    # ),

    # # manual fixes: 0
    # EvaluationProgram(
    #     r'gzip-1.12',
    #     r'https://mirrors.tripadvisor.com/gnu/gzip/gzip-1.12.tar.gz',
    #     r'.',
    #     r'./configure && intercept-build make -j',
    #     r'''
    #     make clean  &&
    #     make        &&
    #     make check
    #     '''
    # ),

    # # manual fixes: 0
    # EvaluationProgram(
    #     r'remind',
    #     r'https://git.skoll.ca/Skollsoft-Public/Remind/archive/04.00.01.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean      &&
    #     make            &&
    #     make test
    #     '''
    # ),

    # # requires makeinfo
    # # manual fixes: ?
    # # TODO: test
    # EvaluationProgram(
    #     r'bc-1.07.1',
    #     r'https://gnu.mirror.constant.com/bc/bc-1.07.1.tar.gz',
    #     r'bc',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check                  &&
    #     cd Test                     &&
    #     bash timetest 1>/dev/null
    #     '''
    # ),

    # # requires help2man
    # # failed same tests it failed before transforming
    # # manual fixes: ?
    # # TODO: transform and test
    # EvaluationProgram(
    #     r'm4-1.4.19',
    #     r'https://ftp.gnu.org/gnu/m4/m4-1.4.19.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # manual fixes: 0
    # EvaluationProgram(
    #     r'bash-5.2-rc1',
    #     r'https://mirror.us-midwest-1.nexcess.net/gnu/bash/bash-5.2-rc1.tar.gz',
    #     r'.',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # manual fixes: 0
    # EvaluationProgram(
    #     r'flex-2.6.4',
    #     r'https://github.com/westes/flex/files/981163/flex-2.6.4.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # requires xaw3dg-dev
    # # manual fixes: 0
    # # TODO: transform and test
    # EvaluationProgram(
    #     r'gv-3.7.4',
    #     r'https://mirrors.sarata.com/gnu/gv/gv-3.7.4.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean  &&
    #     make        &&
    #     make check
    #     '''
    # ),

    # # note: this is genscript from the ernst study
    # # the g stands for GNU
    # # manual fixes: 0
    # EvaluationProgram(
    #     r'enscript-1.6.6',
    #     r'https://ftp.gnu.org/gnu/enscript/enscript-1.6.6.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean      &&
    #     make            &&
    #     make check
    #     ''',
    # ),

    # # found it!
    # # do you know how hard it is to find something on the Internet
    # # with such a generic name as "plan" ? :-)

    # # requires libmotif-dev
    # # no tests - but manually ran the program after
    # # transforming and it seems to work
    # # manual fixes: 0
    # # TODO: transform and test
    # EvaluationProgram(
    #     r'plan-1.12',
    #     r'ftp://ftp.bitrot.de/pub/plan/plan-1.12.tar.gz',
    #     r'src',
    #     '''
    #     cd src                          &&
    #     echo "\\n" | bash configure     &&
    #     intercept-build make linux64               &&
    #     mv compile_commands.json ..     &&
    #     cd ..
    #     ''',
    #     r''
    # ),

    # # requires  build-essential libmotif-dev libjpeg62-dev
    # #           libxmu-headers libxpm-dev libxmu-dev
    # # no tests - but ran the program manually after transforming
    # # and it seems to work
    # # manual fixes: 0
    # # TODO: transform and test
    # EvaluationProgram(
    #     r'ncsa-mosaic-af1c9aaaa299da3540faa16dcab82eb681cf624e',
    #     r'https://github.com/alandipert/ncsa-mosaic/archive/af1c9aaaa299da3540faa16dcab82eb681cf624e.zip',
    #     r'src',
    #     r'intercept-build make linux',
    #     r''
    # ),

    # # cvs redeclares stdio's getline function in lib/getline.h,
    # # and redefines it in lib/getline.c.
    # # to get cvs to compile, i had to rename the function's declaration
    # # and definition to something else.
    # # this has nothing to do with cpp2c, so i don't count it as a manual fix.
    # # cvs has one failing test, but it fails this test before and after
    # # transforming.
    # # manual fixes: 0
    # EvaluationProgram(
    #     r'cvs-1.11.21',
    #     r'https://cfhcable.dl.sourceforge.net/project/ccvs/CVS%20Stable%20Source%20Release/1.11.21/cvs-1.11.21.tar.gz',
    #     r'src',
    #     r'''
    #     sed -i 's/getline __PROTO/getline_cvs __PROTO/' lib/getline.h                               &&
    #     sed -i 's/getline (lineptr, n, stream)/getline_cvs (lineptr, n, stream)/' lib/getline.c     &&
    #     bash configure  &&
    #     intercept-build make
    #     ''',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # transforms
    # # takes 70 sec
    # # manual fixes: 0
    # EvaluationProgram(
    #     r'gnuplot-5.4.4',
    #     r'https://cytranet.dl.sourceforge.net/project/gnuplot/gnuplot/5.4.4/gnuplot-5.4.4.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # requires X11 libraries
    # # TODO: transform and test
    # # manual fixes: ?
    # EvaluationProgram(
    #     r'fvwm-2.6.9',
    #     r'https://github.com/fvwmorg/fvwm/releases/download/2.6.9/fvwm-2.6.9.tar.gz',
    #     r'fvwm',
    #     r'bash configure --disable-png && intercept-build make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     cd  tests                   &&
    #     bash test_options
    #     '''
    # ),

    # # manual fixes: 1 SLOC
    # # problem:  an invocation of YY_INITIAL_VALUE in src/parse-gram.c
    # #           was not transformed correctly.
    # # fix:      undid the transformation.
    # #           1 SLOC.
    # EvaluationProgram(
    #     r'bison-3.8.2',
    #     r'https://mirrors.nav.ro/gnu/bison/bison-3.8.2.tar.gz',
    #     r'src',
    #     r'bash configure && intercept-build make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # when i try to compile rcs, i get a warning that gets is used
    # # where fgets should be used instead.
    # # i fixed this problem changing lib/stdio.in.h
    # # https://www.fatalerrors.org/a/gets-undeclared-here-not-in-a-function.html
    # # this was not an error due to cpp2c.
    # # manual fixes: 0
    # EvaluationProgram(
    #     r'rcs-5.8',
    #     r'https://mirror.koddos.net/gnu/rcs/rcs-5.8.tar.gz',
    #     r'src',
    #     r'''
    #         sed -i 's/_GL_WARN_ON_USE (gets, "gets is a security hole - use fgets instead");/\#if defined(__GLIBC__) \&\& !defined(__UCLIBC__) \&\& !__GLIBC_PREREQ(2, 16)\n_GL_WARN_ON_USE (gets, "gets is a security hole - use fgets instead");\n\#endif/' lib/stdio.in.h  &&
    #         bash configure  &&
    #         intercept-build make''',
    #     r'''
    #     make clean                  &&
    #     make distclean              &&
    #     bash configure              &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # manual fixes: 2. 3 SLOC.
    # # problem:  in builtin.c, the macro INITIAL_OUT_SIZE was used in
    # #           a transformed definition of GIVE_BACK_SIZE before
    # #           INITIAL_OUT_SIZE was defined.
    # # fix:      moved the transformed def of GIVE_BACK_SIZE after the
    # #           definition of the macro INITIAL_OUT_SIZE.
    # #           2 SLOC.
    # # problem:  for some reason, in extension/intdiv.c, the definition of
    # #           the macro MPFR_RNDZ throws an error.
    # #           this only occurs in the tranformed code.
    # # fix:      MPFR_RNDZ was already defined in the usr header mpfr.h
    # #           as an enum, so i just commented out the erroneous macro
    # #           definition.
    # #           1 SLOC.
    # EvaluationProgram(
    #     r'gawk-5.1.1',
    #     r'https://ftp.gnu.org/gnu/gawk/gawk-5.1.1.tar.gz',
    #     r'.',
    #     r'./configure && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make distclean              &&
    #     bash configure              &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # requires cqrlib
    # TODO: transform on local machine, just point it out in evaluation
    EvaluationProgram(
        r'RasMol-2.7.5.2',
        r'http://www.rasmol.org/software/RasMol_Latest.tar.gz',
        r'src',
        r'''
        cd src                      &&
        ./rasmol_build_options.sh   &&
        xmkmf                       &&
        intercept-build make -j
        ''',
        r'''
        '''
    ),

    # # TODO
    # # requires xaw3dg-dev
    # # transforms
    # # takes 50 sec
    # # failed tests.
    # # problem:  nested typedefs and anonymous structs issue.
    # #           in resources.h, PR_SIZE and RECT.
    # # fix:      fix emitted deanonymized names.
    # # problem:  in some files, the transformed definition of max_char_height
    # #           referenced the anonymous, typedef'd struct XFontStruct
    # #           before it was defined.
    # #           the deanonymizer didn't catch this because it's defined
    # #           in a system header (X11), which we don't emit rewrites to.
    # # fix:      remove the struct keyword from function definitions and use
    # #           the typedef instead.
    # # NOTE:     we could automatically handle these cases by not deanonymizing
    # #           system header structs/unions/enums, and using their typedefs
    # #           instead.
    # # now passes tests.
    # EvaluationProgram(
    #     r'xfig-3.2.8b',
    #     r'https://cytranet.dl.sourceforge.net/project/mcj/xfig%2Bfig2dev-3.2.8b.tar.xz',
    #     r'fig2dev',
    #     r'bash configure && intercept-build make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # TODO
    # # transforms
    # # takes 70 sec
    # # fails tests.
    # # requires: autoconf
    # # problem:  definition heuristic emitted a function that returned an
    # #           anonymous typedef'd struct, __sigset_t.
    # #           normally the deanonymizer would fix this by making the struct
    # #           not anonymous, but since the struct is defined in a standard
    # #           header, the deanonymizer wasn't able to rewrite it.
    # # fix:      change all the functions that returned this type to
    # #           the typedef instead of the struct
    # # problem:  in the original code, some part of the build system
    # #           generates .pro files with function forward declarations.
    # #           after transforming, thes .pro files aren't generated
    # #           correctly, and lacks some of these declarations.
    # #           consequently, man files have undeclared reference errors.
    # # fix:      add the required decls back to the .pro files.
    # #           there are 80+ of these files, so to speed this process up
    # #           i first built zsh before transforming it, and committed
    # #           the result to a fresh git repo.
    # #           then i ran the transformer, built again, and reverted all
    # #           the .epro and .pro to their contents prior transformation.
    # #           as i modified source files to fix other problems, make would
    # #           regenerate these .epro and .pro files, but i would always
    # #           revert them back to their prior-transformation state.
    # # problem:  a series of macros defined in pattern.c, patinstart through
    # #           globdots, are defined to expand to struct fields of the
    # #           same name.
    # #           the transformed definitions use the names as struct fields,
    # #           however they are emitted after the macro definitions, so
    # #           the preprocessor thinks they are referring to the macro
    # #           definitions, and expand them.
    # #           this expands to incorrect code.
    # # fix:      comment out these macro definitions.
    # # problem:  after fixing the last problem, invocation of these macros
    # #           broke.
    # # fix:      inline broken macro invocations.
    # # problem:  macro ZF_BUFSIZE undeclared before use in zftp.c
    # # fix:      move macro definition above first use
    # #           (trivial since it was defined as an integer constant)
    # # now passes tests.
    # EvaluationProgram(
    #     r'zsh-5.9',
    #     r'https://cfhcable.dl.sourceforge.net/project/zsh/zsh/5.9/zsh-5.9.tar.xz',
    #     r'Src',
    #     r'bash configure && intercept-build make',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # TODO
    # # configured without gnutls
    # # after these manual fixes i could not get make check to work,
    # # but i was able to build and run emacs successfully.
    # # manual fixes: ?
    # # problem:  transformed definition of Qframep was called in
    # #           frame.c before it was defined.
    # #           normally this would not be a problem, since a declaration
    # #           for this transformed macro would have been emitted prior
    # #           to its first use.
    # #           the declaration was not emitted, however, because the
    # #           the file containing the macro definition was generated by the
    # #           build system.
    # #           the transformed definition must have been emitted at one point
    # #           though, otherwise cpp2c would have failed.
    # #           therefore, i think the build system must have overwritten the
    # #           transformed definition by regenerating the macro definition
    # #           file (globals.h).
    # # fix:      moved the transformed definition above its first call.
    # # problem:  transformed definition of pure_list had the wrong number of
    # #           parameters.
    # #           we shouldn't transform variadic macros; i think we need to add
    # #           a check for this.
    # # fix:      replaced all calls to the transformed macro across 9 files
    # #           with the original macro.
    # # problem:  ditto list_1660157865057390146function.
    # # fix:      replaced transformed calls with original invocations
    # #           across 2 files.
    # # problem:  transformed definition of QCignore_defface called before
    # #           definition.
    # # fix:      moved transformed definition above first call in 1 file.
    # # problem:  transformed definition of DIRECTORY_SEP called before
    # #           definition.
    # # fix:      move transformed definition above first call.
    # # problem:  in alloc.c, there is a a struct named sdata, and an anonymous
    # #           typedef'd to the name sdata.
    # #           this broke the deanonmyizer and several transformed function
    # #           signatures.
    # # fix:      undid deanonymization in one file and fixed 2 transformed
    # #           signatures in the same file.
    # #           also removed forward decls of sdata union.
    # # problem:  variadic macros list and pure_list ere transformed in alloc.c.
    # # fix:      undid 2 transformations in alloc.c.
    # # problem:  in editfns.c, macro COMBINING_BEFORE was invoked before
    # #           it was defined in the transformed definition of COMBINING_BOTH.
    # # fix:      moved transformed definition below macro definition.
    # # problem:  in process.c, transformed definition of Qpipe was called before
    # #           it was defined.
    # # fix:      moved transformed definition above first use.
    # # problem:  ditto Qserial, Qnetwork.
    # # fix:      see above.
    # # in total, 16 files were edited.
    # EvaluationProgram(
    #     r'emacs-28.1',
    #     r'https://ftp.snt.utwente.nl/pub/software/gnu/emacs/emacs-28.1.tar.gz',
    #     r'src',
    #     r'bash configure --with-gnutls=ifavailable && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # TODO: try to transform?
    # # configured with all default options
    # # manual fixes: ?
    # # - file included inside struct, so some transformed decl inside struct.
    # #   + moved decls outside of struct.
    # # - for some reason, the transformed def of OPSLOT_HEADER was not emitted.
    # #   clang's error messages are not very informative.
    # #   perl must be doing a lot of metaprogramming or something.
    # #   i have not seen these sort of issues with any other program.
    # EvaluationProgram(
    #     r'perl-5.36.0',
    #     r'https://www.cpan.org/src/5.0/perl-5.36.0.tar.gz',
    #     r'.',
    #     r'./Configure -d -e -s && intercept-build make -j',
    #     r'make clean -j && make check -j'
    # ),

    # # contains c++ code.
    # # we do not transform c++ code.
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'ghostscript-9.56.1',
    #     r'https://github.com/ArtifexSoftware/ghostpdl-downloads/releases/download/gs9561/ghostscript-9.56.1.tar.gz',
    #     r'',
    #     r'bash configure && intercept-build make -j',
    #     r'''
    #     make clean -j     &&
    #     make -j           &&
    #     make check -j
    #     '''
    # ),

    # # contains c++ code.
    # # we do not transform c++ code.
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'gcc-12.1.0',
    #     r'https://bigsearcher.com/mirrors/gcc/releases/gcc-12.1.0/gcc-12.1.0.tar.gz',
    #     r'gcc',
    #     r'./configure --disable-multilib && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # zephyr's build system is not easy to intercept.
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'zephyr-main',
    #     r'https://github.com/zephyrproject-rtos/zephyr/archive/refs/heads/main.zip',
    #     r'',
    #     r'',
    #     f'''
    #     '''
    # ),

    # # this was made for sun solaris systems, not for linux, and I cannot
    # # install one of the packages its requires (xview)
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'workman-1.3.4',
    #     r'https://web.mit.edu/kolya/.f/root/net.mit.edu/sipb/user/zacheiss/workman-1.3.4.tar.gz',
    #     r'',
    #     r'',
    #     r''
    # ),

    # # requires help2man
    # # GNU chess is written in a mix of c and c++ code.
    # # we don't transform c++ code.
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'gnuchess-6.2.9',
    #     r'https://gnu.mirror.constant.com/chess/gnuchess-6.2.9.tar.gz',
    #     r'src',
    #     r'./configure && intercept-build make -j',
    #     r'''
    #     make clean                  &&
    #     make                        &&
    #     make check
    #     '''
    # ),

    # # we can transform lua nicely, but unfortunately it is not
    # # one of ernst et al.'s 26 programs, so i can't justify including
    # # it in the study.
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'lua-5.4.4',
    #     r'https://www.lua.org/ftp/lua-5.4.4.tar.gz',
    #     r'src',
    #     r'intercept-build make -j',
    #     f'''
    #     make clean                  &&
    #     make                        &&
    #     if [[ -e {LUA_TESTS_DIR} ]]; then rm -fr {LUA_TESTS_DIR}; fi    &&
    #     cd ../                      &&
    #     tar -xvf ../{LUA_TESTS_ZIP} &&
    #     cd {LUA_TESTS_DIR}          &&
    #     ../lua-5.4.4/src/lua -e"_U=true" all.lua 1>/dev/null
    #     '''
    # ),

]
