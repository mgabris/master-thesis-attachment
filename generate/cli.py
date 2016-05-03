import argparse

def parse_args():
    parser = argparse.ArgumentParser(
        description='Generator of Spritz cipher test files, prints everything to stdout'
    )

    parser.add_argument(
        '-i', '--input',
        action='store_true',
        help='read states from stdin instead of generating them'
    ) 

    cipher = parser.add_mutually_exclusive_group()
    cipher.add_argument(
        '--rc4',
        action='store_true',
        help='generate RC4 states'
    )
    cipher.add_argument(
        '--spritz',
        action='store_true',
        help='generate Spritz states'
    )

    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        '-r', '--reveal',
        action='store_true',
        help='reveal values in backtrack '
             'state in random positions (discard previous revealed values) '
             'and write modified file to stdout'
    )
    mode.add_argument(
        '-rr', '--reveal_random',
        action='store_true',
        help='reveal random values in backtrack '
             'state in random positions (discard any previous revealed values) '
             'and write modified file to stdout'
    )

    parser.add_argument(
        '--special',
        action='store_true',
        help='generate Spritz special state (i.e. even values on odd indices '
             'and odd values on even indices)'
    )
    parser.add_argument(
        '--smt',
        action='store_true',
        help='generate/print only initial fully revealed state, format for SMT '
             'code, not backtracking'
    )

    # parameters of generated states
    parser.add_argument(
        '-s', '--size',
        type=int,
        default=8,
        help='size of randomly generated permutation (=8)'
    )
    parser.add_argument(
        '-p', '--preselected',
        type=int,
        default=0,
        help='number of preselected randomly generated permutation values (=0)'
    )
    parser.add_argument(
        '-pe', '--preselected_even',
        type=int,
        default=0,
        help='number of preselected values on even indices (=0)'
    )
    parser.add_argument(
        '-po', '--preselected_odd',
        type=int,
        default=0,
        help='number of preselected values on odd indices (=0) '
    )
    parser.add_argument(
        '-a', '--amount',
        type=int,
        default=1000,
        help='number of states to generate (=1000)'
    )
    parser.add_argument(
        '-l', '--prefix_length',
        type=int,
        default=0,
        help='length of keystream from start after which the starting state of '
             'backtrack is (=0) '
    )
    
    args = parser.parse_args()
    return args
    