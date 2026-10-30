from pysat.solvers import Cadical300

with Cadical300() as solver:
    solver.add_clause([1, 2, 3])
    solver.add_clause([-1, 2, -3])
    print(solver.solve())   
    print(solver.get_model())