import os
import sys
from subprocess import CompletedProcess, run
from tempfile import mkstemp
from typing import Dict

from ruamel import yaml
from ruamel.yaml.dumper import RoundTripDumper
from ruamel.yaml.loader import RoundTripLoader


def preprocess_example(filename: str) -> str:
    un_preprocessed: str
    preprocessed: str
    data: Dict

    with open(filename) as fp:
        data = yaml.load(fp, Loader=RoundTripLoader)

    _, tempfile_name = mkstemp(dir='.', suffix='.c')

    try:
        for triad in data['triads']:
            un_preprocessed = triad['un-preprocessed']

            with open(tempfile_name, 'w') as fp:
                fp.write(un_preprocessed)

            output: CompletedProcess = run(f'cpp {fp.name}',
                                           shell=True, capture_output=True)

            if output.stderr:
                preprocessed = "Does not preprocess"
                print(f"Errors preprocessing: {output.stderr}", sys.stderr)
            else:
                preprocessed = str(output.stdout, encoding='ascii')
                main_start: int = preprocessed.find('int main')
                preprocessed = preprocessed[main_start:].strip()

            triad['preprocessed'] = preprocessed

    except Exception as e:
        print(e, file=sys.stderr)
    finally:
        os.remove(tempfile_name)

    y = yaml.YAML()
    y.indent(sequence=4, offset=2)

    # Removes the trailing whitespace between preprocessed and
    # converted code snippets
    def tr(s: str) -> str:
        return s.replace("}\n\n    converted", "}\n    converted")

    with open(filename, 'w') as fp:
        y.dump(data, fp, transform=tr)


def main():
    if len(sys.argv) != 2:
        print(f"Usage: FILENAME | (-a --all)", file=sys.stderr)
        return
    filename: str = sys.argv[1]
    if filename.casefold() in ['-a,', '-all', '--a', '--all']:
        for file in os.listdir(os.curdir):
            if file.endswith('.yaml'):
                preprocess_example(file)
    else:
        preprocess_example(filename)


if __name__ == '__main__':
    main()
