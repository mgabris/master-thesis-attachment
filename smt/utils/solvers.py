import subprocess
import re
import sys

from config.enums import Cipher, Logic


class SolverWrapper:
    _timefile = '_time'

    """Constructor
    Initialize class with path to solver and list of solver arguments
    solver_path: string containing path to solver
    solver_args: list containing commandline arguments as strings, e.g. '-in'
    """
    def __init__(self, solver_path, solver_args=[]):
        self._solver_path = solver_path
        self._solver_args = solver_args

    """
    stdin: Path class to solver input
    """
    # '-o ' + self._timefile
    # '-f %U\\n%S'
    def run(self, path):
        stdin = path.open('r')
        solver = subprocess.Popen(
            ['/usr/bin/time', '-p', self._solver_path] + self._solver_args,
            stdin=stdin,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        solver.wait()
        stdin.close()
        out, err = solver.communicate()

        # debug
        # print(out.decode().split('\n'))
        # print('-----')
        # print(err.decode().split('\n'))

        out = out.decode()
        err = err.decode()

        return out, err


class OutputParser:
    def __init__(self, options):
        self._options = options

    def extract_select_value(self, string):
        # print(string)
        if self._options.logic is Logic.auflia:
            match = re.search(
                '.*[^0-9a-zA-Z]([0-9]+)[^0-9a-zA-Z].*[^0-9a-zA-Z]([0-9]+)[^0-9a-zA-Z].*',
                string
            )
            assert(match is not None)
            return int(match.group(2))
        elif self._options.logic is Logic.abv:
            match = re.search('.*#b([01]+).*#b([01]+)', string)
            if match:
                return int(match.group(2), base=2)
            match = re.search('.*#x([0-9a-f]+).*#x([0-9a-f]+)', string)
            if match:
                return int(match.group(2), base=16)
            match = re.search('.*#x([0-9a-f]+).*#b([01]+)', string)
            if match:
                return int(match.group(2), base=2)
            match = re.search('.*#b([01]+).*#x([0-9a-f]+)', string)
            if match:
                return int(match.group(2), base=16)
            assert False
        assert False        

    def extract_first_value(self, string):
        # print(string)
        if self._options.logic is Logic.auflia:
            match = re.search('.*[^0-9a-zA-Z]([0-9]+)[^0-9a-zA-Z].*', string)
            assert(match is not None)
            return int(match.group(1))
        elif self._options.logic is Logic.abv:
            match = re.search('.*#b([01]+).*', string)
            if match:
                return int(match.group(1), base=2)
            match = re.search('.*#x([0-9a-f]+).*', string)
            if match:
                return int(match.group(1), base=16)

            assert False
        assert False

    def extract_spritz_registers(self, output):
        regs = []
        for i in range(5):
            line = output[-5+i]
            regs.append(self.extract_first_value(line))
        # insert value of register a, which is 0 in all SMT experiments
        regs.insert(-1, 0)
        return regs

    def extract(self, lines):
        if self._options.encrypt:
            extracted = [self.extract_first_value(line) for line in lines]
        elif self._options.solve:
            if self._options.cipher is Cipher.rc4:
                permutation = [
                    self.extract_select_value(line) for line in lines
                ]
                registers = [0,0]
            elif self._options.cipher is Cipher.spritz:
                permutation = [
                    self.extract_select_value(line) for line in lines[:-5]
                ]
                registers = self.extract_spritz_registers(lines)
            extracted = [registers, permutation]
        return extracted

    def correct(self, data, state, keystream):
        if self._options.solve:
            return data == state
        elif self._options.encrypt:
            return data == keystream

    def parse_time(self, string):
        string = string.split('\n')
        user = float(string[-3].split()[1])
        sys = float(string[-2].split()[1])
        return user + sys

    """Parses and validates solver output
    return: satisfied?, correct?, extracted values if satisfied
    (None otherwise)
    """
    def parse_output(self, string, state, keystream):
        output = string.split('\n')
        sat = output[0]
        if sat != 'sat':
            return False, False, None

        # strip string 'sat'/'unsat' and ending newline
        extracted = self.extract(output[1:-1])
        return True, self.correct(extracted, state, keystream), extracted
