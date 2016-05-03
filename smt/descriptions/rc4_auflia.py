class rc4_auflia:

    def print_extract_state(self, perm_size, keystream, registers, forbidden = []):
        self.N = perm_size
        self.R = len(keystream)
    
        print("(set-option :produce-models true)")
        print("(set-logic QF_AUFLIA)")
        print()
        
        self.print_declarations()
        self.print_constrains()
        self.print_S0_permutation()
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
        
        print("(set-option :produce-models true)")
        print("(set-logic QF_AUFLIA)")
        print()
       
        self.print_declarations()
        self.print_declarations_ks()
        self.print_constrains()
        self.print_constrains_ks()
        self.print_S0_fixed(state[1])
        self.print_forbidden_keystream(forbidden)
        print("; rounds of cipher")
        for r in range(1, self.R+1):
            self.print_round_extract(r)
        print()
        print("(check-sat)")
        self.print_get_keystream()
        print("(exit)")
        
            
    def print_declarations(self):
        print("; declaration of modulo function")
        print("(define-fun modulo "
            "((x Int) (y Int)) Int (ite (>= x y) (- x y) x))")
        print()
        print("; declarations of variables for each round")
        for i in range(self.R+1):
            print("(declare-fun j{0} () Int)".format(i))
        for i in range(self.R+1):
            print("(declare-fun S{0} () (Array Int Int))".format(i))
        print()
        
    def print_declarations_ks(self):
        print("; delarations of variables for output stream")
        for i in range(1, self.R+1):
            print("(declare-fun z{0} () Int)".format(i))
        print()
        
    def print_constrains(self):
        print("; constraints on registers")
        print("(assert (= j0 0))")
        for i in range(1, self.R+1):
            print("(assert (>= j{0} 0))".format(i))
            print("(assert (< j{0} {1}))".format(i, self.N))
        print("; constraints on S0")
        for i in range(self.N):
            print("(assert (>= (select S0 {0}) 0))".format(i))
            print("(assert (< (select S0 {0}) {1}))".format(i, self.N))
        print()
        
    def print_constrains_ks(self):
        print("; constraints on variables for output stream")
        for i in range(1, self.R+1):
            print("(assert (>= z{0} 0))".format(i))
            print("(assert (< z{0} {1}))".format(i, self.N))
        print()
        
    def print_S0_permutation(self):
        print("; asserting S0 is permutation on {} elements".format(self.N))
        # sum of lements in S is self.N*(self.N-1)/2
        row = ["(assert (= ", str(self.N*(self.N-1)//2), " "]
        for i in range(self.N-1):
            row.append(" (+ (select S0 {})".format(i))
        row += [" (select S0 {})".format(self.N-1), ")"*(self.N-1), "))"]
        print("".join(row))
        # every element from {0..N-1} exactly once
        for i in range(self.N):
            for j in range(i+1, self.N):
                print("(assert (not "
                    "(= (select S0 {0}) (select S0 {1}) )))".format(i, j))
        print()
    
    def print_S0_fixed(self, permutation):
        print("; asserting S0 is fixed starting permutation")
        print("; S0", permutation)
        row = ["(assert "]
        for i in range(self.N-1):
            row.append(" (and (= (select S0 {0}) {1})".format(i, permutation[i]))
        row += [" (= (select S0 {0}) {1})".format(self.N-1, permutation[self.N-1])]
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
        print("; forbidden", permutation)
        row = ["(assert (not "]
        for i in range(self.N-1):
            row.append(" (and (= (select S0 {0}) {1})".format(i, permutation[i]))
        row += [" (= (select S0 {0}) {1})".format(self.N-1, permutation[self.N-1])]
        row += [")"*(self.N-1), "))"]
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
            row.append(" (and (= z{0} {1})".format(i+1, stream[i]))
        row += [" (= z{0} {1})".format(self.R, stream[self.R-1])]
        row += [")"*(self.R-1), "))"]
        print("".join(row))
                
    def print_round(self, r, z):
        print("; round {}".format(r))
        # j = j + S[i]
        next_j = "(modulo (+ j{0} (select S{0} {1})) {2})".format(
            r-1, r%self.N, self.N)
        print("(assert (= j{0} {1}))".format(r, next_j))
        # swap(S[i], S[j])
        print("(assert (= S{1} "
            "(store (store S{0} j{1} (select S{0} {2})) {2} "
            "(select S{0} j{1}))))".format(r-1, r, r%self.N))
        # z = S[S[i]+S[j]]
        s = "(+ (select S{0} {1}) (select S{0} j{0}))".format(r, r%self.N)
        mod_s = "(modulo {0} {1})".format(s, self.N)
        print("(assert (= {2} (select S{0} {1})))".format(r, mod_s, z))
        print()
        
    def print_round_extract(self, r):
        print("; round {}".format(r))
        # j = j + S[i]
        next_j = "(modulo (+ j{0} (select S{0} {1})) {2})".format(
            r-1, r%self.N, self.N)
        print("(assert (= j{0} {1}))".format(r, next_j))
        # swap(S[i], S[j])
        print("(assert (= S{1} "
            "(store (store S{0} j{1} (select S{0} {2})) {2} "
            "(select S{0} j{1}))))".format(r-1, r, r%self.N))
        # z = S[S[i]+S[j]]
        s = "(+ (select S{0} {1}) (select S{0} j{0}))".format(r, r%self.N)
        mod_s = "(modulo {0} {1})".format(s, self.N)
        print("(assert (= z{0} (select S{0} {1})))".format(r, mod_s))
        print()
        
    def print_get_S0(self):
        print("; getting values of S0")
        for i in range(self.N):
            print("(get-value ((select S0 {})))".format(i))
        """
        print("(get-value (", end="")
        for i in range(self.N):
            print("(select S0 {})".format(i), end=" ")
        print("))")
        """
        
    def print_get_keystream(self):
        print("; getting values of keystream (z_i)")
        for i in range(1, self.R+1):
            print("(get-value (z{}))".format(i))