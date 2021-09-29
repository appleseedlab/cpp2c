import ruamel.yaml
import os


def main():
    count = 0
    for fn in os.listdir('.'):
        if fn.endswith('.yaml'):
            with open(fn) as fp:
                data = ruamel.yaml.safe_load(fp)
                count += len(data['triads'])
    print(count)


if __name__ == '__main__':
    main()
