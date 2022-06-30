import os
import subprocess

from evaluation_programs import EVALUATION_PROGRAMS


def main():
    for program in EVALUATION_PROGRAMS:
        temp = os.getcwd()
        os.chdir(program.extracted_archive_path)
        subprocess.run(program.test_script, shell=True)
        os.chdir(temp)


if __name__ == '__main__':
    main()
