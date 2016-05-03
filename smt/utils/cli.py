import argparse

from config.enums import Mode, Cipher, Logic


# ##### argparse enum type callables #####

def mode(string):
    try:
        value = Mode[string]
    except KeyError:
        msg = '{} is not a valid mode type'.format(string)
        raise argparse.ArgumentTypeError(msg)
    return value


def cipher(string):
    try:
        value = Cipher[string]
    except KeyError:
        msg = '{} is not a valid cipher type'.format(string)
        raise argparse.ArgumentTypeError(msg)
    return value


def logic(string):
    try:
        value = Logic[string]
    except KeyError:
        msg = '{} is not a valid logic type'.format(string)
        raise argparse.ArgumentTypeError(msg)
    return value


def custom_checks(args):
    # check for valid cipher-logic combinations
    # currently, spritz-auflia is not (and probably will not be) implemented
    if (args.cipher is Cipher.spritz and args.logic is Logic.auflia):
        parser.error(
            'Combinatrion of cipher {0} and logic {1} is not supported'
            .format(Cipher.spritz, Logic.auflia)
        )


# ##### parser settings #####

def parse_solve_args():
    parser = argparse.ArgumentParser(
        description='SMT description of stream ciphers tester'
    )

    # positional arguments
    parser.add_argument(
        'states',
        type=argparse.FileType('r'),
        help='file, inital states as python arrays'
    )

    # optional arguments
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        '-s', '--solve',
        type=str,
        help='solve inital state by SMT solver, takes path to SMT solver'
    )
    group.add_argument(
        '-e', '--encrypt',
        type=str,
        help=(
            'test SMT description by generating keystream, '
            'takes path to SMT solver'
        )
    )
    group.add_argument(
        '-g', '--generate',
        type=mode,
        choices=list(Mode),
        help='generate SMT programs only, don\'t start solver'
    )

    parser.add_argument(
        '-c', '--cipher',
        type=cipher,
        default=Cipher.default(),
        choices=list(Cipher),
        help='type of cipher (={})'.format(Cipher.default())
    )
    parser.add_argument(
        '-l', '--logic',
        type=logic,
        default=Logic.default(),
        choices=list(Logic),
        help='type of SMT logic (={})'.format(Logic.default())
    )

    parser.add_argument(
        '-k', '--kslength',
        type=int,
        default=10,
        help='length of keystream to generate from states (=10)'
    )
    parser.add_argument(
        '-f', '--forbidden',
        type=argparse.FileType('r'),
        help='file with forbidden states to SMT solver'
    )
    parser.add_argument(
        '-n', '--nounique',
        action='store_true',
        help='no uniqueness testing'
    )
    parser.add_argument(
        '-v', '--verbosity',
        type=int,
        default=1,
        help='level of verbosity (=1)'
    )
    parser.add_argument(
        '-a', '--sargs',
        type=str,
        default=[],
        nargs=argparse.REMAINDER,
        help=(
            'additional arguments passed to SMT solver, '
            'this switch (if used) should be last (=[])'
        )
    )

    args = parser.parse_args()
    custom_checks(args)
    return args
