load("compute.sage")


def generate_spritz_variables(N):
    variables = [[var('c_' + str(u) + '_' + str(x)) for x in range(N+2)] for u in range(6)]
    return variables
  
def get_spritz_boundary_conditions(N):
    KB = {}
    for i in range(6):
        KB[cvar(i,N)] = 0
        KB[cvar(i,N+1)] = 0
    return KB
              
                
def generate_spritz_simple_equations(N, x, KB):
    eqs = []
    for i in range(1, 6):
        eqs.append(
            cvar(i,x) == x/N * cvar(i+1,x) + (1 - x/N) * (N-x) * (1 + KB[cvar(i+1,x+1)])
        )
    eq6 = c6(x) == x/N * (1/N * c1(x)) + (1 - x/N)^2 * (1 + KB[c1(x+1)])
    eqs.append(eq6)
    return (eqs, [cvar(i,x) for i in range(1, 7)])
             
def generate_spritz_change_order_equations(N, x, KB):
    eqs = []
    for i in range(1, 5):
        eqs.append(
            cvar(i,x) == x/N * cvar(i+1,x) + (1 - x/N) * (N-x) * (1 + KB[cvar(i+1,x+1)])
        )
    eq5 = c5(x) == x/N * ((1 - x/N)^2 * (1 + KB[c1(x+1)]) + x/N * 1/N * c1(x)) + (1 - x/N) * c6(x)
    eq6 = c6(x) == (1 - x/N) * (1 + 1/N * KB[c1(x+1)] + (N-x-1) * (1 - (x+1)/N) * (1 + KB[c1(x+2)])) + x/N * (1 - x/N) * (1 + KB[c1(x+1)])
    eqs += [eq5, eq6]
    return (eqs, [cvar(i,x) for i in range(1, 7)])

def generate_spritz_ankele_equations(N, x, KB):
    eqs = []
    for i in range(1, 6):
        eqs.append(
            cvar(i,x) == x/N * cvar(i+1,x) + (1 - x/N) * (N-x) * KB[cvar(i+1,x+1)]
        )
    eq6 = c6(x) == x/N * ((1 - x/N) + c1(x)) + (1 - x/N) * (x/N + KB[c1(x+1)])
    eqs.append(eq6)
    return (eqs, [cvar(i,x) for i in range(1, 7)])


def test():
    N, x = 16, 0
    result = compute_complexity(
        N, x,
        generate_spritz_variables,
        get_spritz_boundary_conditions,
        generate_spritz_change_order_equations
    )
    print '{:g}'.format( float(result) )
    print '{:.2f}'.format( float(log(result, 2).n(prec)) )

def table():
    params = [(8,0), (10,0), (16,5), (64,48), (128,114), (256,240), (64,0), (128,0), (256,0)]
    print 'simple'
    for N, x in params:
        result = compute_complexity(
            N, x,
            generate_spritz_variables,
            get_spritz_boundary_conditions,
            generate_spritz_simple_equations
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, x, float(log(result, 2).n(prec)) )
    
    print 'ankele'
    for N, x in params:
        result = compute_complexity(
            N, x,
            generate_spritz_variables,
            get_spritz_boundary_conditions,
            generate_spritz_ankele_equations
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, x, float(log(result, 2).n(prec)) )
    
    print 'change order'
    for N, x in params:
        result = compute_complexity(
            N, x,
            generate_spritz_variables,
            get_spritz_boundary_conditions,
            generate_spritz_change_order_equations
        )
        print '{:3},{:3}: {:>7.2f}'.format(N, x, float(log(result, 2).n(prec)) )

# test()