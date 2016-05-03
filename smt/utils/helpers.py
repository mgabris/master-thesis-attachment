def gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a


def n2b(number, length):
    return "#b" + bin(number)[2:].zfill(length)

