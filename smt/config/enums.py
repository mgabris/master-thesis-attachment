from enum import Enum


class Mode(Enum):
    solve = 1
    encrypt = 2

    def default():
        return Mode.solve

    def __str__(self):
        return self.name


class Cipher(Enum):
    rc4 = 1
    spritz = 2

    def default():
        return Cipher.rc4

    def __str__(self):
        return self.name


class Logic(Enum):
    auflia = 1
    abv = 2

    def default():
        return Logic.abv

    def __str__(self):
        return self.name
