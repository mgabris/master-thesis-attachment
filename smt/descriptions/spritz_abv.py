import math

from utils.helpers import n2b, gcd

# def n2b(number, length):
#     return "#b" + bin(number)[2:].zfill(length)

# def gcd(a, b):
#     while b != 0:
#         a, b = b, a%b
#     return a

class spritz_abv:
    
    var = ["i", "j", "k", "z"]

    def print_extract_state(self, perm_size, keystream, registers, forbidden = []):
        self.N = perm_size
        self.R = len(keystream)
        # size of registers 
        self.n = math.ceil(math.log(self.N, 2))
      
        print("(set-option :produce-models true)")
        print("(set-logic QF_ABV)")
        print()

        self.print_declarations()
        self.print_S0_permutation()

        # before first output, so z0 must be 0
        print("(assert (= z0 {0}))".format(self.n2b(0)))

        i, w = registers[0], registers[-1]
        print("(assert (= i0 {0}))".format(self.n2b(i)))        
        print("(assert (= w {0}))".format(self.n2b(w)))
        
        self.print_keystream_fixed(keystream)
        self.print_forbidden_states(forbidden)

        print("; rounds of cipher")
        for r in range(1, self.R+1):
            self.print_round(r)
        print()


        print("(check-sat)")
        self.print_get_start()
        print("(exit)")

    
    def print_extract_keystream(self, state, kslength, forbidden = []):
        self.N = len(state[1])
        self.R = kslength
        # size of registers 
        self.n = math.ceil(math.log(self.N, 2))

        print("(set-option :produce-models true)")
        print("(set-logic QF_ABV)")
        print()

        self.print_declarations()
        self.print_S0_permutation()
        self.print_start_fixed(state)
        self.print_forbidden_keystreams(forbidden)

        print("; rounds of cipher")
        for r in range(1, self.R+1):
            self.print_round(r)
        print()

        print("(check-sat)")
        self.print_get_keystream()
        print("(exit)")


    def n2b(self, number):
        return n2b(number, self.n)

    def print_declarations(self):
        print("; declaration of w")
        print("(declare-fun w () (_ BitVec {0}))".format(self.n))
        print("; declaration of state variables for each round")
        for i in range(self.R+1):
            print(
                "(declare-fun S{0} () (Array (_ BitVec {1}) (_ BitVec {1})))"
                .format(i, self.n)
            )
        for v in self.var:
            for i in range(self.R+1):
                print(
                    "(declare-fun {0}{1} () (_ BitVec {2}))"
                    .format(v, i, self.n)
                )
        print()


    def print_S0_permutation(self):
        print("; asserting S0 is permutation on {} elements".format(self.N))
        for i in range(self.N):
            for j in range(i+1, self.N):
                print(
                    "(assert (not (= (select S0 {0}) (select S0 {1}) )))"
                    .format(self.n2b(i), self.n2b(j))
                )
        print()


    def print_start_fixed(self, state):
        print("; asserting S0 is fixed starting state")
        print("; S0", state[1])
        row = ["(assert "]
        for i in range(self.N-1):
            row.append(
                " (and (= (select S0 {0}) {1})"
                .format(self.n2b(i), self.n2b(state[1][i]))
            )
        row += [
            " (= (select S0 {0}) {1})"
            .format(self.n2b(self.N-1), self.n2b(state[1][self.N-1]))
        ]
        row += [")"*(self.N-1), ")"]
        print("".join(row))
        print()

        print("; asserting starting values for variables")
        print(";", state[0])
        for i, v in enumerate(self.var):
            print("(assert (= {0}0 {1}))".format(v, self.n2b(state[0][i])))
        print("(assert (= w {0}))".format(self.n2b(state[0][-1])))
        print()

    def print_start_forbidden(self, state):
        assert len(state[1]) == self.N
        print("; forbidden start", state)
        row = ["(assert (not "]
        for i in range(self.N):
            row.append(
                " (and (= (select S0 {0}) {1})"
                .format(self.n2b(i), self.n2b(state[1][i]))
            )
        for i, v in enumerate(self.var):
            row.append(
                " (and (= {0}0 {1})"
                .format(v, self.n2b(state[0][i]))
            )
        row += [
            " (= w {0})".format(self.n2b(state[0][-1])), 
            ")"*(self.N+6)
        ]
        print("".join(row))

    def print_keystream_fixed(self, stream):
        print("; fixed keystream", stream)
        assert len(stream) == self.R
        for i in range(self.R):
            print(
                "(assert (= z{0} {1}))"
                .format(i+1, self.n2b(stream[i]))
            )
        print()

    def print_keystream_forbidden(self, stream):
        assert len(stream) == self.R
        print("; forbidden keystream", stream)
        row = ["(assert (not "]
        for i in range(self.R-1):
            row.append(" (and (= z{0} {1})".format(i+1, self.n2b(stream[i])))
        row += [" (= z{0} {1})".format(self.R, self.n2b(stream[self.R-1]))]
        row += [")"*(self.R-1), "))"]
        print("".join(row))

    
    def print_forbidden_states(self, forbidden):
        if len(forbidden) > 0:
            print("; forbidden starting states")
        for state in forbidden:
            self.print_start_forbidden(state)
        print()

    def print_forbidden_keystreams(self, forbidden):
        if len(forbidden) > 0:
            print("; forbidden keystream")
        for stream in forbidden:
            self.print_keystream_forbidden(stream)
        print()

            
    def print_round(self, r):
        print("; round {}".format(r))
        # i = i + w
        print("(assert (= i{1} (bvadd i{0} w)))".format(r-1, r))
        # j = k + S[j + S[i]]
        inner = "(bvadd j{0} (select S{0} i{1}))".format(r-1, r)
        print(
            "(assert (= j{1} (bvadd k{0} (select S{0} {2}))))"
            .format(r-1, r, inner)
        )
        # k = i + k + S[j]
        sel = "(select S{0} j{1})".format(r-1, r)
        print(
            "(assert (= k{1} (bvadd i{1} (bvadd k{0} {2}))))"
            .format(r-1, r, sel)
        )
        # swap(S[i], S[j])
        print(
            "(assert (= S{1} (store "
            "(store S{0} j{1} (select S{0} i{1})) i{1} (select S{0} j{1}))))"
            .format(r-1, r)
        )
        # z = S[j + S[i + S[z+k]]]
        z = "(select S{1} (bvadd j{1} (select S{1} (bvadd i{1} (select S{1} (bvadd z{0} k{1}))))))".format(r-1, r)
        print("(assert (= z{0} {1}))".format(r, z))
        print()

    def print_get_start(self):
        print("; getting values of starting state")
        for i in range(self.N):
            print("(get-value ((select S0 {})))".format(self.n2b(i)))
        for v in self.var:
            print("(get-value ({0}0))".format(v))
        print("(get-value (w))")
        print()

    def print_get_keystream(self):
        print("; getting values of keystream (z_i)")
        for i in range(1, self.R+1):
            print("(get-value (z{}))".format(i))

