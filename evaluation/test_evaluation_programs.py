import os
import shutil
import subprocess

from run_evaluation import EXTRACTED_EVALUATION_PROGRAMS_DIR

LUA_TESTS_ZIP = 'lua-5.4.4-tests.tar.gz'
LUA_TESTS_DIR = 'lua-5.4.4-tests'


def test_bc():
    temp = os.getcwd()
    os.chdir(EXTRACTED_EVALUATION_PROGRAMS_DIR+'bc-1.07/')
    cmd = '''
    make clean                  &&
    make                        &&
    make check                  &&
    cd Test                     &&
    bash timetest 1>/dev/null
    '''
    subprocess.run(cmd, shell=True)
    os.chdir(temp)


def test_gzip():
    temp = os.getcwd()
    os.chdir(EXTRACTED_EVALUATION_PROGRAMS_DIR+'gzip-1.10/')
    cmd = '''
    make clean  &&
    make        &&
    make check
    '''
    subprocess.run(cmd, shell=True)
    os.chdir(temp)


def test_remind():
    temp = os.getcwd()
    os.chdir(EXTRACTED_EVALUATION_PROGRAMS_DIR+'remind-03.04.02/')
    cmd = '''
    make clean      &&
    make            &&
    make test
    '''
    subprocess.run(cmd, shell=True)
    os.chdir(temp)


def test_lua():
    temp = os.getcwd()
    os.chdir(EXTRACTED_EVALUATION_PROGRAMS_DIR+'lua-5.4.4/')
    subprocess.run('make', shell=True)

    if (os.path.exists(LUA_TESTS_DIR)):
        shutil.rmtree(LUA_TESTS_DIR)
    os.chdir(temp)
    shutil.unpack_archive(LUA_TESTS_ZIP, EXTRACTED_EVALUATION_PROGRAMS_DIR)

    os.chdir(os.path.join(EXTRACTED_EVALUATION_PROGRAMS_DIR, LUA_TESTS_DIR))
    print(os.getcwd())
    subprocess.run('../lua-5.4.4/src/lua -e"_U=true" all.lua 1>/dev/null', shell=True)
    os.chdir(temp)


def main():
    test_bc()
    test_gzip()
    test_remind()
    test_lua()


if __name__ == '__main__':
    main()
