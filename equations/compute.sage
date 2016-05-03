prec = 30

cvars = []

def cvar(u,x):
    return cvars[u-1][x]

def c1(x):
    return cvar(1,x)
def c2(x):
    return cvar(2,x)
def c3(x):
    return cvar(3,x)
def c4(x):
    return cvar(4,x)
def c5(x):
    return cvar(5,x)
def c6(x):
    return cvar(6,x)


def compute_complexity(N, x,
                       generate_variables,
                       get_boundary_conditions, 
                       generate_equations, 
                       ticks=False, start=None, return_kb=False):
    global cvars
    cvars = generate_variables(N)
    # Knowledge base -- dynamic programming memory
    KB = get_boundary_conditions(N)
    
    if ticks:
        print 'x     log(guesses)'
        print '-' * 30
    
    if start is None:
        start = N-1    
    
    for i in range(start, x-1, -1):
        equations, variables = generate_equations(N, i, KB)
        solutions = solve(equations, variables, solution_dict=True)[0]
        # add computed values
        for v in variables:
            KB[v] = solutions[v]
        if ticks:
            print '{:3d} {:10.2f}'.format(i, float(log(KB[c1(i)], 2).n(prec)))
    
    if return_kb:
        return KB
        
    return KB[cvar(1, x)]
