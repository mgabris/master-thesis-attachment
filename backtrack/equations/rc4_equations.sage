load("compute.sage")


def generate_rc4_variables(N):
    variables = [[var('c_' + str(u) + '_' + str(x)) for x in range(N+2)] for u in range(3)]
    return variables
    
def get_rc4_boundary_conditions(N):
    KB = {}
    for i in range(3):
        KB[cvar(i,N)] = 0
        KB[cvar(i,N+1)] = 0
    return KB

    
def generate_rc4_simple_equations(N, x, KB):
    eq1 = c1(x) == x/N * c2(x) + (1 - x/N) * (N-x) * (1 + KB[c2(x+1)])
    eq2 = c2(x) == x/N * c3(x) + (1 - x/N) * (N-x) * (1 + KB[c3(x+1)])
    eq3 = c3(x) == x/N * (1/N * c1(x)) + (1 - x/N)^2 * (1 + KB[c1(x+1)])
    return ([eq1, eq2, eq3], [cvar(i,x) for i in range(1, 4)])
             
def generate_rc4_change_order_equations(N, x, KB):
    eq1 = c1(x) == x/N * c2(x) + (1 - x/N) * (N-x) * (1 + KB[c2(x+1)])
    eq2 = c2(x) == x/N * ((1 - x/N)^2 * (1 + KB[c1(x+1)]) + x/N * 1/N * c1(x)) + (1 - x/N) * c3(x)
    
    Sj_unknown = 1 + 1/N * KB[c1(x+1)] + (N-x-1) * (1 - (x+1)/N) * (1 + KB[c1(x+2)])
    Sj_known = (1 + KB[c1(x+1)])
    eq3 = c3(x) == (1 - x/N) *  Sj_unknown + x/N * (1 - x/N) * Sj_known
    
    return ([eq1, eq2, eq3], [cvar(i,x) for i in range(1, 4)])
    
def e(N, x):
    return (1 - (x+1)/N) * (1 - 1/(N-x))

def f(N, x):
    return (N-x) * (1 + e(N,x)) + x/N 
    
def generate_rc4_knudsen_equations(N, x, KB):
    eq1 = c1(x) == x/N * c2(x) + (1 - x/N) * (N-x) * KB[c2(x+1)]
    eq2 = c2(x) == x/N * ((1 - x/N)^2 * (1 + KB[c1(x+1)]) + 1/N * c1(x)) + (1 - x/N) * c3(x)
    eq3 = c3(x) == (1 - x/N) * (f(N,x) + (2*x+1)/N * KB[c1(x+1)] + (N-x) * e(N,x) * KB[c1(x+2)])
    return ([eq1, eq2, eq3], [cvar(i,x) for i in range(1, 4)])


def test():
    N, x = 4, 3
    result = compute_complexity(
        N, x,
        generate_rc4_variables,
        get_rc4_boundary_conditions,
        generate_rc4_simple_equations
    )
    print '{:g}'.format( float(result) )
    print '{:.2f}'.format( float(log(result, 2).n(prec)) )

def table():
    params = [8, 12, 16, 64, 128, 256]
    print 'simple'
    for N in params:
        result = compute_complexity(
            N, 0,
            generate_rc4_variables,
            get_rc4_boundary_conditions,
            generate_rc4_simple_equations
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, 0, float(log(result, 2).n(prec)) )
    
    print 'change order'
    for N in params:
        result = compute_complexity(
            N, 0,
            generate_rc4_variables,
            get_rc4_boundary_conditions,
            generate_rc4_change_order_equations
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, 0, float(log(result, 2).n(prec)) )
    
    print 'knudsen'
    for N in params:
        result = compute_complexity(
            N, 0,
            generate_rc4_variables,
            get_rc4_boundary_conditions,
            generate_rc4_knudsen_equations
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, 0, float(log(result, 2).n(prec)) )

test()