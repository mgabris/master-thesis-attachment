prec = 30

cvars = []

def cvar(u,v,x,y):
    return cvars[u-1][v][x][y]

def c1(v,x,y):
    return cvar(1,v,x,y)
def c2(v,x,y):
    return cvar(2,v,x,y)
def c3(v,x,y):
    return cvar(3,v,x,y)
def c4(v,x,y):
    return cvar(4,v,x,y)
def c5(v,x,y):
    return cvar(5,v,x,y)
def c6(v,x,y):
    return cvar(6,v,x,y)
    

def generate_spritz_special_variables(N):
    cvars = [[[[var('c_'+str(u)+'_'+str(v)+'_'+str(x)+'_'+str(y)) 
                for y in range(N/2+2)] for x in range(N/2+2)] for v in range(4)] for u in range(6)]
    return cvars
    
def get_spritz_special_boundary_conditions(N):
    N2 = N/2
    KB = {}
    # Boundary conditions
    for u in range(1,7):
        for v in range(4):
            KB[cvar(u,v,N2,N2)] = 0
            for i in range(N2+1):
                KB[cvar(u,v,i,N2+1)] = 0
                KB[cvar(u,v,N2+1,i)] = 0
    return KB
    

def generate_spritz_special_equations(N, x, y, KB):
    N2 = N/2
    eq = []
    va = [c1(j,x,y) for j in range(4)]
    va += [c2(j,x,y) for j in range(4)]
    va += [c3(j,x,y) for j in range(4)]
    va += [c4(j,x,y) for j in range(4)]
    va += [c5(j,x,y) for j in range(4)]
    va += [c6(j,x,y) for j in range(4)]
    
    # STEP 1 (guessing S[i], parity of the index: 1,0,1,0)
    eq.append(c1(0,x,y) == y/N2*c2(0,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c2(0,x,y+1))))
    eq.append(c1(1,x,y) == x/N2*c2(1,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c2(1,x+1,y))))
    eq.append(c1(2,x,y) == y/N2*c2(2,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c2(2,x,y+1))))
    eq.append(c1(3,x,y) == x/N2*c2(3,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c2(3,x+1,y))))
    
    # STEP 2 (guessing S[j+S[i]], parity of the index: 0,0,0,0)
    for v in range(4):
        eq.append(c2(v,x,y) == x/N2*c3(v,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c3(v,x+1,y))))

    # STEP 3 (guessing S[j], parity of the index: 1,0,1,0)
    eq.append(c3(0,x,y) == y/N2*c4(0,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c4(0,x,y+1))))
    eq.append(c3(1,x,y) == x/N2*c4(1,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c4(1,x+1,y))))
    eq.append(c3(2,x,y) == y/N2*c4(2,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c4(2,x,y+1))))
    eq.append(c3(3,x,y) == x/N2*c4(3,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c4(3,x+1,y))))

    # STEP 4 (guessing S[z+k], parity of the index: 1,0,0,1)
    eq.append(c4(0,x,y) == y/N2*c5(0,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c5(0,x,y+1))))
    eq.append(c4(1,x,y) == x/N2*c5(1,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c5(1,x+1,y))))
    eq.append(c4(2,x,y) == x/N2*c5(2,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c5(2,x+1,y))))
    eq.append(c4(3,x,y) == y/N2*c5(3,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c5(3,x,y+1))))

    # STEP 5 (guessing S[i+S[z+k]], parity of the index: 1,1,0,0)
    eq.append(c5(0,x,y) == y/N2*c6(0,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c6(0,x,y+1))))
    eq.append(c5(1,x,y) == y/N2*c6(1,x,y) + (1-y/N2)*(N2-y)*(1+KB.get(c6(1,x,y+1))))
    eq.append(c5(2,x,y) == x/N2*c6(2,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c6(2,x+1,y))))
    eq.append(c5(3,x,y) == x/N2*c6(3,x,y) + (1-x/N2)*(N2-x)*(1+KB.get(c6(3,x+1,y))))

    # STEP 6 (guessing S[j+S[i+S[z+k]]], parity of the index: 1,0,0,1)
    eq.append(c6(0,x,y) == y/N2*1/N2*c1(1,x,y) + (1-y/N2)^2*(1+KB.get(c1(1,x,y+1))))
    eq.append(c6(1,x,y) == x/N2*1/N2*c1(2,x,y) + (1-x/N2)^2*(1+KB.get(c1(2,x+1,y))))
    eq.append(c6(2,x,y) == x/N2*1/N2*c1(3,x,y) + (1-x/N2)^2*(1+KB.get(c1(3,x+1,y))))
    eq.append(c6(3,x,y) == y/N2*1/N2*c1(0,x,y) + (1-y/N2)^2*(1+KB.get(c1(0,x,y+1))))

    return (eq, va)


def compute_spritz_special_complexity(N, even=0, odd=0, ticks=False):
    global cvars
    cvars = generate_spritz_special_variables(N)
    
    KB = get_spritz_special_boundary_conditions(N)

    N2 = N/2
    for x in range(N2,-1,-1):
        if ticks:
            print 'x=', x, '-> y: ',
        for y in range(N2,x-1,-1):
            if ticks:
                print y,
            # get equations for x, y
            eqs, eqvars = generate_spritz_special_equations(N, x, y, KB)
            sol = solve(eqs, eqvars, solution_dict=True)[0]
            # expand KB
            for v in eqvars:
                KB[v] = sol[v].n(prec)
            if y == x:
                if ticks:
                    print
                break
            # get equations for y, x
            eqs, eqvars = generate_spritz_special_equations(N, y, x, KB)
            sol = solve(eqs, eqvars, solution_dict=True)[0]
            # expand KB
            for v in eqvars:
                KB[v] = sol[v].n(prec)
    
    return KB[c1(0,even,odd)]


def test():
    N, even, odd = 10, 0, 0
    result = compute_spritz_special_complexity(N, even, odd)
    print '{:g}'.format( float(result) )
    print '{:.2f}'.format( float(log(result, 2).n(prec)) )

def table():
    params = [(16,0,0), (18,0,0), (20,0,0), (64,22,22), (128,50,50), (256,110,110), (64,0,0), (128,0,0), (256,0,0)]
    for N, x, y in params:
        result = compute_spritz_special_complexity(N, x, y)
        print '{},{:3},{:3}: {:>7.2f}'.format(N, x, y, float(log(result, 2).n(prec)) )

test()