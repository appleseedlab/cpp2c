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
    #     r'intercept-build make -j',
    #     r''
    # ),

    # manual fixes: 0
    EvaluationProgram(
        r'gzip-1.12',
        r'https://mirrors.tripadvisor.com/gnu/gzip/gzip-1.12.tar.gz',
        r'.',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean  &&
        make        &&
        make check
        '''
    ),

    # manual fixes: 0
    EvaluationProgram(
        r'remind',
        r'https://git.skoll.ca/Skollsoft-Public/Remind/archive/04.00.01.tar.gz',
        r'src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean      &&
        make            &&
        make test
        '''
    ),

    # requires makeinfo
    # manual fixes: 0
    EvaluationProgram(
        r'bc-1.07.1',
        r'https://gnu.mirror.constant.com/bc/bc-1.07.1.tar.gz',
        r'bc',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check                  &&
        cd Test                     &&
        bash timetest 1>/dev/null
        '''
    ),

    # requires help2man
    # failed same test it failed before transforming: ./198.sysval:err
    # manual fixes: 0
    EvaluationProgram(
        r'm4-1.4.19',
        r'https://ftp.gnu.org/gnu/m4/m4-1.4.19.tar.gz',
        r'src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # manual fixes: 0
    EvaluationProgram(
        r'bash-5.2-rc1',
        r'https://mirror.us-midwest-1.nexcess.net/gnu/bash/bash-5.2-rc1.tar.gz',
        r'.',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # manual fixes: 0
    EvaluationProgram(
        r'flex-2.6.4',
        r'https://github.com/westes/flex/files/981163/flex-2.6.4.tar.gz',
        r'src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # requires xaw3dg-dev
    # intercept-build didn't initially work because some of the files in gv
    # had utf-8 characters, but were not utf-8 encoded.
    # i fixed this by changing the file encodings to utf-8.
    # i do not count theses as fixes because they are not directly
    # related to cpp2c.
    # manual fixes: 0
    EvaluationProgram(
        r'gv-3.7.4',
        r'https://mirrors.sarata.com/gnu/gv/gv-3.7.4.tar.gz',
        r'src',
        r'''
        iconv -f ISO-8859-1 -t UTF-8 src/Makefile.am -o tmp && mv -f tmp src/Makefile.am    &&
        iconv -f ISO-8859-1 -t UTF-8 src/Makefile.in -o tmp && mv -f tmp src/Makefile.in    &&
        for FN in src/gv_copyright.dat src/gv_font_res.dat src/gv_font_res-I18N_mb.dat src/gv_layout_res.dat src/gv_misc_res.dat src/gv_spartan.dat src/gv_user_res.dat src/gv_widgetless.dat; do iconv -f US-ASCII -t UTF-8 $FN -o tmp && mv -f tmp $FN; done  &&
        ./configure                                                                         &&
        intercept-build make -j
        ''',
        r'''
        make clean  &&
        make        &&
        make check
        '''
    ),

    # note: this is genscript from the ernst study
    # the g stands for GNU
    # manual fixes: 0
    EvaluationProgram(
        r'enscript-1.6.6',
        r'https://ftp.gnu.org/gnu/enscript/enscript-1.6.6.tar.gz',
        r'src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
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
    # i had a hard time installing this one the remote machine.
    # my solution was to download it using wget --no-passive on my local
    # machine, then scp it over to the remote machine.
    # no tests - but manually ran the program after transforming it and
    # it seems to work.
    # i transformed the files on the remote machine, then copied them over
    # to my machine, then recompiled and ran the tests.
    # for some reason, when after configuring and making plan, i run into
    # a redefinition error. yylineno is redefined in lex.yy.c.
    # this occurs in the original, untransformed program.
    # i fixed this by changing the definition of int yylineno in holiday.c
    # to an extern int.
    # manual fixes: 0
    EvaluationProgram(
        r'plan-1.12',
        r'ftp://ftp.bitrot.de/pub/plan/plan-1.12.tar.gz',
        r'src',
        r'''
        cd src                                                  &&
        sed -i 's/int yylineno/extern int yylineno/' holiday.c  &&
        ./configure 4                                           &&
        make clean                                              &&
        intercept-build make linux64                            &&
        mv compile_commands.json ..                             &&
        cd ..
        ''',
        r''
    ),

    # requires  build-essential libmotif-dev libjpeg62-dev
    #           libxmu-headers libxpm-dev libxmu-dev libpng-dev
    # no tests - but ran the program manually after transforming
    # and it seems to work
    # won't compile with gcc-11.
    # need to use gcc-9 or gcc-10.
    # manual fixes: 0
    EvaluationProgram(
        r'ncsa-mosaic-af1c9aaaa299da3540faa16dcab82eb681cf624e',
        r'https://github.com/alandipert/ncsa-mosaic/archive/af1c9aaaa299da3540faa16dcab82eb681cf624e.zip',
        r'src',
        r'intercept-build make CC=gcc-9 linux -j',
        r''
    ),

    # cvs redeclares stdio's getline function in lib/getline.h,
    # and redefines it in lib/getline.c.
    # to get cvs to compile, i had to rename the function's declaration
    # and definition to something else.
    # this has nothing to do with cpp2c, so i don't count it as a manual fix.
    # cvs has one failing test, but it fails this test before and after
    # transforming.
    # manual fixes: 0
    EvaluationProgram(
        r'cvs-1.11.21',
        r'https://cfhcable.dl.sourceforge.net/project/ccvs/CVS%20Stable%20Source%20Release/1.11.21/cvs-1.11.21.tar.gz',
        r'src',
        r'''
        sed -i 's/getline __PROTO/getline_cvs __PROTO/' lib/getline.h                               &&
        sed -i 's/getline (lineptr, n, stream)/getline_cvs (lineptr, n, stream)/' lib/getline.c     &&
        bash configure          &&
        intercept-build make
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # transforms
    # manual fixes: 0
    EvaluationProgram(
        r'gnuplot-5.4.4',
        r'https://cytranet.dl.sourceforge.net/project/gnuplot/gnuplot/5.4.4/gnuplot-5.4.4.tar.gz',
        r'src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # requires X11 libraries (i think libx11-dev)
    # manual fixes: 0
    EvaluationProgram(
        r'fvwm-2.6.9',
        r'https://github.com/fvwmorg/fvwm/releases/download/2.6.9/fvwm-2.6.9.tar.gz',
        r'fvwm',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean      &&
        make            &&
        make check
        '''
    ),

    # manual fixes: 1 SLOC
    # problem:  an invocation of YY_INITIAL_VALUE in src/parse-gram.c
    #           was not transformed correctly.
    # fix:      undid the transformation.
    #           1 SLOC.
    EvaluationProgram(
        r'bison-3.8.2',
        r'https://mirrors.nav.ro/gnu/bison/bison-3.8.2.tar.gz',
        r'src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # when i try to compile rcs, i get a warning that gets is used
    # where fgets should be used instead.
    # i fixed this problem changing lib/stdio.in.h
    # https://www.fatalerrors.org/a/gets-undeclared-here-not-in-a-function.html
    # this was not an error due to cpp2c.
    # manual fixes: 0
    EvaluationProgram(
        r'rcs-5.8',
        r'https://mirror.koddos.net/gnu/rcs/rcs-5.8.tar.gz',
        r'src',
        r'''
        sed -i 's/_GL_WARN_ON_USE (gets, "gets is a security hole - use fgets instead");/\#if defined(__GLIBC__) \&\& !defined(__UCLIBC__) \&\& !__GLIBC_PREREQ(2, 16)\n_GL_WARN_ON_USE (gets, "gets is a security hole - use fgets instead");\n\#endif/' lib/stdio.in.h  &&
        ./configure          &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make distclean              &&
        bash configure              &&
        make                        &&
        make check
        '''
    ),

    # manual fixes: 3 SLOC.
    # problem:  in builtin.c, the macro INITIAL_OUT_SIZE was used in
    #           a transformed definition of GIVE_BACK_SIZE before
    #           INITIAL_OUT_SIZE was defined.
    # fix:      moved the transformed def of GIVE_BACK_SIZE after the
    #           definition of the macro INITIAL_OUT_SIZE.
    #           2 SLOC.
    # problem:  for some reason, in extension/intdiv.c, the definition of
    #           the macro MPFR_RNDZ throws an error.
    #           this only occurs in the tranformed code.
    # fix:      MPFR_RNDZ was already defined in the usr header mpfr.h
    #           as an enum, so i just commented out the erroneous macro
    #           definition.
    #           1 SLOC.
    EvaluationProgram(
        r'gawk-5.1.1',
        r'https://ftp.gnu.org/gnu/gawk/gawk-5.1.1.tar.gz',
        r'.',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make distclean              &&
        bash configure              &&
        make                        &&
        make check
        '''
    ),

    # requires xaw3dg-dev
    # manual fixes: 0
    EvaluationProgram(
        r'xfig-3.2.8b',
        r'https://cytranet.dl.sourceforge.net/project/mcj/xfig%2Bfig2dev-3.2.8b.tar.xz',
        r'fig2dev',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # requires: autoconf
    # manual fixes: 230 SLOC.
    # problem:  in the original code, some part of the build system
    #           generates .pro and .epro files with function forward
    #           declarations.
    #           it seems that this part of the build system infers
    #           what forward decls to generate by checking which functions have
    #           comments directly above them.
    #           the transformation moves some of these comments around,
    #           so the build system doesn't generate all the forward
    #           declarations that it should.
    # fix:      move the comments back where they belong.
    #           File                    Function                SLOC
    #           Src/parse.c             bin_zcompile            2
    #           Src/lex.c               gettok                  2
    #           Src/math.c              mathparse               2
    #           Src/options.c           optlookupc              2
    #           Src/params.c            printparamnode          2
    #           Src/parse.c             par_cmd                 2
    #           Src/parse.c             load_dump_header        2
    #           Src/parse.c             check_dump_file         2
    #           Src/pattern.c           patcompswitch           2
    #           Src/pattern.c           patcomppiece            2
    #           Src/pattern.c           patoptail               2
    #           Src/pattern.c           patmatch                2
    #           Src/pattern.c           patcompile              2
    #           Src/subst.c             stringsubst             2
    #           Src/Modules/mathfunc.c  math_func               2
    #           Src/Modules/watch.c     watchlog2               2
    #           Src/Zle/compctl.c       get_xcompctl.c          2
    #           Src/Zle/compctl.c       makecomplistctl         2
    #           Src/Zle/compcore.c      do_completion           2
    #           Src/Zle/complist.c      clprintm                2
    #           Src/Zle/zle_hist.c      doisearch               2
    #           Src/Zle/zle_move.c      backwardmetafiedchar    2
    #           Src/Zle/zle_keymap.c    bin_bindkey_list        2
    #           Src/Zle/zle_refresh.c   refreshline             2
    #           Src/Zle/zle_refresh.c   tcoutarg                2
    #           Src/Zle/zle_refresh.c   singmoveto              2
    #           Src/Zle/zle_tricky.c    docomplete              2
    #           Src/mem.c               zhalloc                 2
    #           Src/mem.c               zheapptr                2
    #                                   bindkey                 2
    #                                   expandjobtab            2
    #                                   freeheap                2
    #                                   hbegin                  2
    #                                   inpush                  2
    #                                   moveto                  2
    #                                   patgetglobflags         2
    #                                   shinbufalloc            2
    #                                   tcout                   2
    #                                   wait_for_processes      2
    #                                   zglob                   2
    #                                   executenamedcommand     2
    #                                   zrefresh                2
    #                                   init_io                 2
    #                                   initlextabs             2
    #                                   setblock_fd             2
    #                                   pattryrefs              2
    #                                   unlinkkeymap            2
    #                                   findcmd                 2
    #                                   hist_in_word            2
    #                                   new_optarg              2
    #                                   closemn                 2
    #                                   zexecve                 2
    #                                   addpath                 2
    #                                   insert                  2
    #                                   setupvals               2
    #                                   zzlex                   2
    #                                   checkunary              2
    #                                   push                    2
    #                                   printoptionnode         2
    #                                   setemulate              2
    #                                   init_parse              2
    #                                   bin_ln                  2
    #                                   setpmmapfile            2
    #                                   bin_sysread             2
    #                                   zfstats                 2
    #                                   zfsenddata              2
    #                                   get_compctl             2
    #                                   do_comp_vars            2
    #                                   bin_compset             2
    #                                   compprintlist           2
    #                                   set_isrch_spot          2
    #                                   scanfindfunc            2
    #                                   resetvideo              2
    #                                   insert_glob_match       8
    #                                   mmap_heap_alloc         8
    #                                   wait_for_processes      12
    #                                   cfp_test_exact          30
    # problem:  a series of macros defined in pattern.c, patinstart through
    #           globdots, are defined to expand to struct fields of the
    #           same name.
    #           the transformed definitions use the names as struct fields,
    #           however they are emitted after the macro definitions, so
    #           the preprocessor thinks they are referring to the macro
    #           definitions, and expand them.
    #           this expands to incorrect code.
    # fix:      comment out these macro definitions.
    #           9 SLOC.
    # problem:  after fixing the last problem, invocation of these macros
    #           broke.
    # fix:      inline broken macro invocations.
    #           Macro           SLOC
    #           patinstart      9
    #           patinend        19
    #           patinput        40
    #           patinpath       3
    #           patinlen        4
    #           patbeginp       3
    #           patendp         3
    #           parsfound       4
    #           globdots        3
    # problem:  macro ZF_BUFSIZE undeclared before use in zftp.c
    # fix:      move macro definition above first use.
    #           trivial since it was defined as an integer constant.
    #           2 SLOC.
    EvaluationProgram(
        r'zsh-5.9',
        r'https://cfhcable.dl.sourceforge.net/project/zsh/zsh/5.9/zsh-5.9.tar.xz',
        r'Src',
        r'''
        ./configure             &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # requires gnutls libjpeg libgif/libungif libtiff gnutls
    # but these requirements can be circumvented with configuration options.
    # manual fixes: 4 SLOC.
    # problem:  in src/editfns.c, the transformed definition of
    #           COMBINING_BOTH invoked the macros COMBINING_BEFORE and
    #           COMBINING_AFTER before they were defined.
    # fix:      moved the definitions of COMBINING_BEFORE and COMBINING_AFTER
    #           above the transformed def of COMBINING_BOTH.
    #           4 SLOC.
    EvaluationProgram(
        r'emacs-28.1',
        r'https://ftp.snt.utwente.nl/pub/software/gnu/emacs/emacs-28.1.tar.gz',
        r'src',
        r'''
        ./configure --with-gnutls=ifavailable --with-gif=ifavailable --with-tiff=ifavailable    &&
        intercept-build make -j
        ''',
        r'''
        make clean                  &&
        make                        &&
        make check
        '''
    ),

    # Failed 2 tests out of 2527, 99.92% okay.
    # Test Summary Report
    # -------------------
    # re/speed.t                                                         (Wstat: 0 Tests: 59 Failed: 16)
    #   Failed tests:  42-57
    # ../ext/re/t/regop.t                                                (Wstat: 0 Tests: 52 Failed: 2)
    #   Failed tests:  1, 51
    #   Parse errors: Bad plan.  You planned 55 tests but ran 52.
    # 
    # to test, run these commands inside the perl directory
    #   export LD_LIBRARY_PATH=`pwd`; cd t; ./perl harness re/speed.t
    #   export LD_LIBRARY_PATH=`pwd`; cd t; ./perl harness ../ext/re/t/regop.t
    # 
    # i tried running both tests on a fresh perl install to see if they fail
    # normally.
    # when i run perl's test sute, it says that the first test passes.
    # however, when i run the test individually in the clean install, it fails
    # the same way it does in the transformed version.
    # 
    # configured with all default options
    # manual fixes: 16 SLOC.
    # problem:  in regcomp.c, the transformed definition of WASTED_GC
    #           invoked WASTED_G and WASTED_C before they were defined.
    # fix:      moved macro definitions above transformed definition.
    #           4 SLOC.
    # problem:  in util.c, transformed definitions invoked DAYS_PER_YEAR,
    #           DAYS_PER_QYEAR, DAYS_PER_CENT, MONTH_TO_DAYS, and SECS_PER_HOUR
    #           before they were defined.
    # fix:      move these macro defs up.
    #           10 SLOC.
    # problem:  in regcomp.c, the transformed def of IS_OPERAND invoked
    #           IS_OPERATOR before it was defined.
    # fix:      copied macro definition and corresponding undef
    #           above transformed definition.
    #           2 SLOC.
    EvaluationProgram(
        r'perl-5.36.0',
        r'https://www.cpan.org/src/5.0/perl-5.36.0.tar.gz',
        r'.',
        r'''
        ./Configure -d -e -s        &&
        intercept-build make -j
        ''',
        r'''
        make clean -j   &&
        make check -j
        '''
    ),

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

    # # requires libcqrlib-dev libcneartree-dev libcvector-dev libforms-dev
    # # compiles successfully, but cannot get the original version to run,
    # # and there is not make check, so no way of testing.
    # # manual fixes: N/A
    # EvaluationProgram(
    #     r'RasMol-2.7.5.2',
    #     r'http://www.rasmol.org/software/RasMol_Latest.tar.gz',
    #     r'src',
    #     r'''
    #     cd src                      &&
    #     ./rasmol_build_options.sh --cbflib_local    &&
    #     xmkmf                       &&
    #     intercept-build make -j     &&
    #     mv compile_commands.json .. &&
    #     mv ..
    #     ''',
    #     r'''
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
