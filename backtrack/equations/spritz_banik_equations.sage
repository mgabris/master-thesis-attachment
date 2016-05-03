load('compute.sage')


def generate_spritz_banik_variables(N):
    variables = [[var('c_' + str(u) + '_' + str(x)) for x in range(N/2+2)] for u in range(14)]
    return variables
    
def get_spritz_banik_boundary_conditions(N):
    KB = {}
    for i in range(14):
        KB[cvar(i,N/2-1)] = 1
        KB[cvar(i,N/2)] = 0
    return KB    
    

def generate_spritz_special_T1_equations(N, x, KB):
    N2 = N/2
    eqs = []
    for i in set(range(1,11))-set([5,10]):
        eqs.append(
            cvar(i,x) == x/N2 * cvar(i+1,x) + (1 - x/N2) * (N2-x) * KB[cvar(i+1,x+1)]
        )
    eq5 = cvar(5,x) == (x/N2)^2 * cvar(6,x) + (1 - x/N2)^2 * KB[cvar(6,x+1)]
    eq10 = cvar(10,x) == (x/N2)^2 * cvar(1,x) + (1 - x/N2)^2 * KB[cvar(1,x+1)]
    eqs += [eq5,eq10]
    return (eqs, [cvar(i,x) for i in range(1, 11)])
    
def generate_spritz_special_T2_equations(N, x, KB):
    N2 = N/2
    eqs = []
    for i in set(range(1,14))-set([6,10]):
        eqs.append(
            cvar(i,x) == x/N2 * cvar(i+1,x) + (1 - x/N2) * (N2-x) * KB[cvar(i+1,x+1)]
        )
    eq14 = cvar(14,x) == x/N2 * cvar(1,x) + (1 - x/N2) * (N2-x) * KB[cvar(1,x+1)]
    eq6 = cvar(6,x) == (x/N2)^2 * cvar(7,x) + (1 - x/N2)^2 * KB[cvar(7,x+1)]
    eq10 = cvar(10,x) == (x/N2)^2 * cvar(11,x) + (1 - x/N2)^2 * KB[cvar(11,x+1)]
    eqs += [eq6,eq10,eq14]
    return (eqs, [cvar(i,x) for i in range(1, 15)])


def test():
    N, x = 16, 0
    t1 = compute_complexity(
        N, x,
        generate_spritz_banik_variables,
        get_spritz_banik_boundary_conditions,
        generate_spritz_special_T1_equations,
        start=N/2-2
    )
    t2 = compute_complexity(
        N, x,
        generate_spritz_banik_variables,
        get_spritz_banik_boundary_conditions,
        generate_spritz_special_T2_equations,
        start=N/2-2
    )
    print '{:g}'.format( float(t1*t2) )
    print '{:.2f}'.format( float(log(t1*t2, 2).n(prec)) )

def table():
    params = [(16,0), (18,0), (20,0), (64,22), (128,50), (256,110), (64,0), (128,0), (256,0)]
    for N, x in params:
        t1 = compute_complexity(
            N, x,
            generate_spritz_banik_variables,
            get_spritz_banik_boundary_conditions,
            generate_spritz_special_T1_equations,
            start=N/2-2
        )
        t2 = compute_complexity(
            N, x,
            generate_spritz_banik_variables,
            get_spritz_banik_boundary_conditions,
            generate_spritz_special_T2_equations,
            start=N/2-2
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, x, float(log(t1*t2, 2).n(prec)) )

test()