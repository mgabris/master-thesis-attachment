#!/usr/bin/python3

import sys
import os
import random
import datetime
import pickle

import backtrack
import cli
from ciphers.spritz import Spritz
from states import SpritzState
from stats import Stats


def read_states(input_file):
    states = []
    while True:
        initial = input_file.readline()
        if initial == '':
            break
        revealed = input_file.readline()
        shift = int(input_file.readline())
        states.append((
            SpritzState(string=initial), 
            SpritzState(string=revealed),
            shift
        ))
    return states


class Settings:
    def __init__(self, args):
        self.__dict__ = args.__dict__.copy()


def main(args):
    states = read_states(sys.stdin)

    stats = Stats(sys.argv)
    cipher = Spritz()

    settings = Settings(args)

    prompt_step = max(1, len(states) // 20)
    i = 0
    for initial_state, revealed_state, prefix_length in states:
        if args.verbosity >= 3 and i % prompt_step == 0:
            print('test #:', i)
        i += 1

        KNOWN_KEYSTREAM_SIZE = 3 * initial_state.size + 1
        cipher.initialize_state(initial_state.state)
        known_keystream = cipher.keystream(prefix_length + KNOWN_KEYSTREAM_SIZE)
        settings.prefix_length = prefix_length

        cipher.initialize_state(initial_state.state)
        cipher.keystream(prefix_length)
        found_state, round_stats = backtrack.kpa(
            known_keystream,
            revealed_state,
            settings,
        )

        if found_state and initial_state != found_state:
            print('incorrect result, this should not happen')
            assert False

        stats.add(round_stats)

    stats.print_stats(args.verbosity)
    # dump pickled stats object
    if not args.no_stats_log:
        timestamp = datetime.datetime.today().strftime('%y%m%d_%H%M%S_%f')
        os.makedirs('stats/', exist_ok=True)
        with open('stats/' + timestamp, 'wb') as f:
            pickle.dump(stats, f)

if __name__ == '__main__':
    main(cli.parse_benchmark_args())
