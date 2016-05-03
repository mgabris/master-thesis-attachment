import math

from utils.helpers import n2b

# def n2b(number, length):
#     return "#b" + bin(number)[2:].zfill(length)

class rc4_abv:
    
    def print_extract_state(self, perm_size, keystream, registers, forbidden = []):
        self.N = perm_size
        self.R = len(keystream)
        # size of registers (j and elements of S)
        self.n = math.ceil(math.log(self.N, 2))
        
        print("(set-option :produce-models true)")
        print("(set-logic QF_ABV)")
        print()
              
        self.print_declarations()
        self.print_S0_permutation()
        self.print_constrains()
        self.print_forbidden(forbidden)
        print("; rounds of cipher")
        for r in range(1, self.R+1):
            self.print_round(r, keystream[r-1])
        print()
        print("(check-sat)")
        self.print_get_S0()
        print("(exit)")
        
    def print_extract_keystream(self, state, kslength, forbidden = []):
        self.N = len(state[1])
        self.R = kslength
        # size of registers (j and elements of S)
        self.n = math.ceil(math.log(self.N, 2))
        
        print("(set-option :produce-models true)")
        print("(set-logic QF_ABV)")
        print()
       
        self.print_declarations()
        self.print_declarations_ks()
        self.print_constrains()
        self.print_S0_fixed(state[1])
        self.print_forbidden_keystream(forbidden)
        print("; rounds of cipher")
        for r in range(1, self.R+1):
            self.print_round_extract(r)
        print()
        print("(check-sat)")
        self.print_get_keystream()
        print("(exit)")
    
    def n2b(self, number):
        return n2b(number, self.n)
    
    def print_declarations(self):
        print("; declarations of variables for each round")
        for i in range(self.R+1):
            print("(declare-fun j{0} () (_ BitVec {1}))".format(i, self.n))
        for i in range(self.R+1):
            print("(declare-fun S{0} () (Array (_ BitVec {1}) (_ BitVec {1})))".format(i, self.n))
        print()
        
    def print_declarations_ks(self):
        print("; delarations of variables for output stream")
        for i in range(1, self.R+1):
            print("(declare-fun z{0} () (_ BitVec {1}))".format(i, self.n))
        print()    
        
    def print_constrains(self):
        print("(assert (= j0 {}))".format(self.n2b(0)))
        print()
        
    def print_S0_permutation(self):
        # every element from {0..N-1} exactly once
        print("; asserting S0 is permutation on {} elements".format(self.N))
        for i in range(self.N):
            for j in range(i+1, self.N):
                print("(assert (not "
                    "(= (select S0 {0}) (select S0 {1}) )))".format(
                        self.n2b(i), self.n2b(j)))
                #print("(assert (not (= {0} {1} S0) )))".format(self.ex(0, i), self.ex(0, j))
        print()
        
    def print_S0_fixed(self, permutation):
        print("; asserting S0 is fixed starting permutation")
        print("; S0", permutation)
        row = ["(assert "]
        for i in range(self.N-1):
            row.append(" (and (= (select S0 {0}) {1})".format(
                self.n2b(i), self.n2b(permutation[i])))
        row += [" (= (select S0 {0}) {1})".format(
            self.n2b(self.N-1), self.n2b(permutation[self.N-1]))]
        row += [")"*(self.N-1), ")"]
        print("".join(row))
        print()    
        
    def print_forbidden(self, forbidden):
        if len(forbidden) > 0:
            print("; forbidden starting states")
        for state in forbidden:
            self.print_forbid_start(state[1])
        print()
    
    def print_forbid_start(self, permutation):
        assert len(permutation) == self.N
        row = ["(assert (not "]
        for i in range(self.N-1):
            row.append(" (and (= (select S0 {0}) {1})".format(self.n2b(i), self.n2b(permutation[i])))
        row += [" (= (select S0 {0}) {1})".format(self.n2b(self.N-1), self.n2b(permutation[self.N-1])), ")"*(self.N-1), "))"]
        print("".join(row))

    def print_forbidden_keystream(self, forbidden):
        if len(forbidden) > 0:
            print("; forbidden keystream")
        for stream in forbidden:
            self.print_forbid_stream(stream)
        print()    
        
    def print_forbid_stream(self, stream):
        assert len(stream) == self.R
        print("; forbidden", stream)
        row = ["(assert (not "]
        for i in range(self.R-1):
            row.append(" (and (= z{0} {1})".format(i+1, self.n2b(stream[i])))
        row += [" (= z{0} {1})".format(self.R, self.n2b(stream[self.R-1]))]
        row += [")"*(self.R-1), "))"]
        print("".join(row))
        

    def print_round(self, r, z):
        print("; round {}".format(r))
        # j = j + S[i]
        next_j = "(bvadd j{0} (select S{0} {1}))".format(r-1, self.n2b(r%self.N))
        print("(assert (= j{0} {1}))".format(r, next_j))
        # swap(S[i], S[j])
        print("(assert (= S{1} (store (store S{0} j{1} (select S{0} {2})) {2} (select S{0} j{1}))))".format(r-1, r, self.n2b(r%self.N)))
        # z = S[S[i]+S[j]]
        inner = "(bvadd (select S{0} {1}) (select S{0} j{0}))".format(r, self.n2b(r%self.N))
        print("(assert (= {2} (select S{0} {1})))".format(r, inner, self.n2b(z)))
        print()
       
    def print_round_extract(self, r):
        print("; round {}".format(r))
        # j = j + S[i]
        next_j = "(bvadd j{0} (select S{0} {1}))".format(r-1, self.n2b(r%self.N))
        print("(assert (= j{0} {1}))".format(r, next_j))
        # swap(S[i], S[j])
        print("(assert (= S{1} (store (store S{0} j{1} (select S{0} {2})) {2} (select S{0} j{1}))))".format(r-1, r, self.n2b(r%self.N)))
        # z = S[S[i]+S[j]]
        inner = "(bvadd (select S{0} {1}) (select S{0} j{0}))".format(r, self.n2b(r%self.N))
        print("(assert (= z{0} (select S{0} {1})))".format(r, inner))
        print()
       
    def print_get_S0(self):
        print("; getting values of S0")
        for i in range(self.N):
            print("(get-value ((select S0 {})))".format(self.n2b(i)))
        print()
        
    def print_get_keystream(self):
        print("; getting values of keystream (z_i)")
        for i in range(1, self.R+1):
            print("(get-value (z{}))".format(i))