import argparse


def parse_benchmark_args():
    parser = argparse.ArgumentParser(
        description='Spritz KPA state extraction benchmark, reads states from stdin'
    )


    parser.add_argument(
        '-ns', '--no_stop',
        action='store_true',
        help='don\'t stop backtrack when corect state is found, but continue '
             'search for every possibility'
    )

    # heuristics, optimalizations of backtrack
    parser.add_argument(
        '-pc', '--prefix_check',
        action='store_true',
        help='enables check for consistency with skipped prefix of keystream, '
             'check is performed at start of every backtrack call'
    )
    parser.add_argument(
        '-pcc', '--prefix_check_continue',
        action='store_true',
        help='in prefix check, don\'t stop when missing value in computation '
             'of z'
    )
    parser.add_argument(
        '-pccw', '--prefix_check_continue_write',
        action='store_true',
        help='in prefix check, write z to permutation when index is known and '
             'value at that index is None and continue'
    )
    parser.add_argument(
        '-pcg', '--prefix_check_guess',
        action='store_true',
        help='prefix check is performed after each guess'
    )
    parser.add_argument(
        '-kgo', '--keystream_guess_order',
        action='store_true',
        help='change order of guesses from range(N) to numbers in keystream '
             'first, missing values after'
    )
    parser.add_argument(
        '-lgo', '--last_guess_order',
        action='store_true',
        help='check for z_t in state before guessing last '
             'value (SiSzk)'
    )
    parser.add_argument(
        '-slg', '--skip_last_guess',
        action='store_true',
        help='only with -lgo, optimization from Knudsen\'s paper, when known_z is in S and '
             'all values other than SiSzk next step are alredy guessed, skip '
             'guessing position of known_z'
    )
    parser.add_argument(
        '-sp', '--special',
        action='store_true',
        help='use of special state in backtracking, WARNING: intended to use '
             'only with basic backtracking (nothing from -pc,-pcc,-pccw,-pcg,'
             '-kgo,-lgo,-slg'
    )

    parser.add_argument(
        '-v', '--verbosity',
        type=int,
        default=3,
        help='level of verbosity (=3)'
    )
    parser.add_argument(
        '-nsl', '--no_stats_log',
        action='store_true',
        help='disable pickling of stats class after experiment'
    )

    args = parser.parse_args()
    return args


def parse_stats_printer_args():
    parser = argparse.ArgumentParser(
        description='Loads and prints pickled stats object'
    )
    parser.add_argument(
        'file',
        type=argparse.FileType('rb'),
        help='pickled stats file to load'
    )
    parser.add_argument(
        '-c', '--command',
        action='store_true',
        help='print also filename and parameters of benchmark'
    )
    parser.add_argument(
        '-v', '--verbosity',
        type=int,
        default=3,
        help='level of verbosity (=3)'
    )

    args = parser.parse_args()
    return args
