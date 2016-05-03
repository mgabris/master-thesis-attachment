#!/usr/bin/python3

import random
import sys
import subprocess

from pathlib import Path

import utils.cli as cli

from utils.writers import SMTWriter
from utils.solvers import SolverWrapper, OutputParser

from ciphers.rc4 import RC4
from ciphers.spritz import Spritz
from descriptions.rc4_auflia import rc4_auflia
from descriptions.rc4_abv import rc4_abv
from descriptions.spritz_abv import spritz_abv

from config.settings import TEST_FOLDER, TEMPFILE_PREFIX, MAX_OTHER_SOLUTIONS
from config.enums import Mode, Cipher, Logic


def prepare_test_folder(folder):
    path = Path(folder)
    try:
        path.mkdir()
    except FileExistsError:
        # it's ok, we still want to use that directory
        pass

    for f in path.glob('_*.smt2'):
        if f.is_file():
            f.unlink()
        else:
            # there is directory with potential confict name
            raise FileExistsError(
                'directory with conflicting name in \'./_tests\' exists'
            )
    return path


def load_forbidden_states(forbidden_file):
    forbidden = []
    for line in forbidden_file:
        forbidden.append(eval(line))
    return forbidden


def other_solutions(smt_file, in_state, keystream, forbidden):
    global writer, solver, output_parser

    other_states = 0
    satisfied = True
    while satisfied and other_states < MAX_OTHER_SOLUTIONS:
        writer.write(smt_file, in_state, keystream, forbidden)
        if args.verbosity >= 3:
            print('searching for other solutions...')
        out, err = solver.run(smt_file)
        time = output_parser.parse_time(err)
        satisfied, correct, values = output_parser.parse_output(
            out, in_state, keystream
        )
        if satisfied:
            other_states += 1
            forbidden.append(values)
            if args.verbosity >= 3:
                print('{0} - solution found, in time {1}, correct? {2}'.format(other_states, time, correct))
        else:
            if args.verbosity >= 3:
                print('no other solution...')

    return other_states


def print_round_results(args, data):
    if args.verbosity < 1:
        print()
        return

    print('case #', data.order + 1, end=': ')
    print('time:', data.time, 'sec', end=', ')
    print('satisfied:', data.satisfied, end='')
    if data.other_states > 0:
        s = '{}'
        if data.other_states == MAX_OTHER_SOLUTIONS:
            s = '{}+'
        print(',', s.format(data.other_states), 'more state(s)', end='')
    elif not args.nounique:
        print(', unique', end='')
    if data.satisfied:
        if data.correct:
            print(', correct')
            if args.verbosity >= 3:
                if args.encrypt:
                    print('keystream:', data.keystream)
        else:
            print(', not correct')
            if args.verbosity >= 2:
                if args.solve:
                    print('state:', data.in_state)
                    print('from solver:', data.solver_values)
                elif args.encrypt:
                    print('keystream:', data.keystream)
                    print('from solver:', data.solver_values)
    else:
        print()

def print_results(args, stats):
    if args.generate:
        return
    if args.verbosity >= 1:
        print()
        print('correct:', stats.correct_states, 'out of', stats.num_states,
              ',', (stats.correct_states / stats.num_states * 100), '%')
        if not args.nounique:
            print(
                'unique:',
                stats.unique_states, 'out of', stats.num_states, ',',
                (stats.unique_states / stats.num_states * 100), '%'
            )
        print(
            'avg time:', round(stats.overall_time / stats.num_states, 2),
            'sec'
        )
    else:
        print(round(stats.correct_states / stats.num_states * 100))
        print(round(stats.unique_states / stats.num_states * 100))
        print(round(stats.overall_time / stats.num_states, 2))


class RoundData:
    pass


class Stats:
    overall_time = 0
    num_states = 0
    correct_states = 0
    unique_states = 0


def main(args):
    global writer, solver, output_parser

    # set cipher and SMT description generator
    if args.cipher is Cipher.rc4:
        cipher = RC4()
    elif args.cipher is Cipher.spritz:
        cipher = Spritz()

    if args.logic is Logic.auflia:
        description = rc4_auflia()
    elif args.logic is Logic.abv:
        description = rc4_abv() if args.cipher is Cipher.rc4 else spritz_abv()

    if args.solve or args.generate is Mode.solve:
        solver_path = args.solve
    elif args.encrypt or args.generate is Mode.encrypt:
        solver_path = args.encrypt
    else:
        assert False
    writer = SMTWriter(args, description)
    solver = SolverWrapper(solver_path, args.sargs)
    output_parser = OutputParser(args)

    forbidden = []
    if args.forbidden:
        forbidden = load_forbidden_states(args.forbidden)
    test_folder = prepare_test_folder(TEST_FOLDER)

    stats = Stats()

    # test every state in file
    for i, line in enumerate(args.states):
        stats.num_states += 1

        in_state = eval(line)

        cipher.initialize_state(in_state)
        keystream = cipher.keystream(args.kslength)

        # file to write description to
        smt_file = test_folder / (TEMPFILE_PREFIX + str(i+1).zfill(3) + '.smt2')
        writer.write(smt_file, in_state, keystream, forbidden)

        # skip all testing if generating
        if args.generate:
            continue

        if args.verbosity >= 3:
            print('solving...')
        out, err = solver.run(smt_file)
        if args.verbosity >= 3:
            print('finished...')

        time = output_parser.parse_time(err)
        satisfied, correct, solver_values = output_parser.parse_output(
            out, in_state, keystream
        )

        stats.overall_time += time
        if correct:
            stats.correct_states += 1

        # uniqueness of state
        other_states = 0
        if not args.nounique and satisfied:
            f = forbidden[:]
            f.append(solver_values)
            other_states = other_solutions(
                smt_file, in_state, keystream, f
            )

        if other_states == 0:
            stats.unique_states += 1

        # Arrange round data to object
        data = RoundData()
        data.order = i
        data.time = time
        data.satisfied = satisfied
        data.other_states = other_states
        data.correct = correct
        data.keystream = keystream
        data.in_state = in_state
        data.solver_values = solver_values

        # print round info
        print_round_results(args, data)

    # print overall results
    print_results(args, stats)


if __name__ == '__main__':
    args = cli.parse_solve_args()
    main(args)
