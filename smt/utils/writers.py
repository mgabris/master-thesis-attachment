import sys

from config.enums import Mode, Cipher


class SMTWriter:
    def __init__(self, options, description):
        self._options = options
        self._description = description

    def write(self, path, state, keystream=[], forbidden=[]):
        sys.stdout = path.open('w')

        print('; from state:', state)
        if self._options.encrypt or self._options.generate is Mode.encrypt:
            self._description.print_extract_keystream(
                state, self._options.kslength, forbidden
            )
        elif self._options.solve or self._options.generate is Mode.solve:
            perm_length = len(state[1])
            registers = state[0]
            self._description.print_extract_state(
                perm_length, keystream, registers, forbidden
            )
        else:
            assert False

        sys.stdout.close()
        sys.stdout = sys.__stdout__
