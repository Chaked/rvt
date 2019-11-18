import os
import sys
import random
import string


PATH_SUFFIX = 'temp'
MAIN_REPLACEMENT = ' {}('.format(''.join(random.choice(string.ascii_lowercase) for i in range(15)))


def create(path0, path1, fun_name0, fun_name1):
    new_path0 = '{}{}'.format(path0, PATH_SUFFIX)
    new_path1 = '{}{}'.format(path1, PATH_SUFFIX)
    with open(path0, "rt") as fin:
        with open(new_path0, "wt") as fout0:
            for line in fin:
                fout0.write(line.replace(' main(', MAIN_REPLACEMENT).replace(fun_name0, ' main('))
    with open(path1, "rt") as fin:
        with open(new_path1, "wt") as fout1:
            for line in fin:
                fout1.write(line.replace(' main(', MAIN_REPLACEMENT).replace(fun_name1, ' main('))


def delete(path0, path1):
    new_path0 = '{}{}'.format(path0, PATH_SUFFIX)
    new_path1 = '{}{}'.format(path1, PATH_SUFFIX)
    os.remove(new_path0)
    os.remove(new_path1)


if __name__ == '__main__':
    try:
        if sys.argv[1] == '-create':
            create(sys.argv[2], sys.argv[3], ' {}('.format(sys.argv[4]), ' {}('.format(sys.argv[5]))
            exit(0)
        if sys.argv[1] == '-delete':
            delete(sys.argv[2], sys.argv[3])
            exit(0)
        else:
            print('Command not supported: {}'.format(sys.argv[1]))
    except Exception as e:
        print(e)
