from .csp import *
from .sugar import *

class SatResult():
    def __init__(self, i):
        self.i = i
    
    def __eq__(self, other):
        return self.i == other.i
    
    def __ne__(self, other):
        return self.i != other.i
    
    def __str__(self):
        if self.i == 1:
            return 'SAT'
        elif self.i == -1:
            return 'UNSAT'
        else:
            return str(self.i)
    
    def __repr__(self):
        if self.i == 1:
            return 'sat'
        elif self.i == -1:
            return 'unsat'
        else:
            return str(self.i)

sat = SatResult(1)
unsat = SatResult(-1)

solver = None
__solution = None
__solutions = []
defaultSolver = 'sat4j'

# def init():
#     global csp, solver, __solution, __solutions
#     csp = CSP()
#     solver= Solver(solver.solverName, solver.optNum)
#     __solution = None
#     __solutions = []

def add(*c):
    return csp.add(*c)

def commit():
    csp.commit()

def cancel():
    csp.cancel()

def minimize(x):
    csp.minimize(x)

def maximize(x):
    csp.maximize(x)

def isMinimize():
    return csp.isMinimize()

def isMaximize():
    return csp.isMaximize()

def objective():
    return csp.objective

def clearObjective():
    csp.clearObjective()

def satisfiedBy(solution):
    return csp.satisfiedBy(solution)

def show():
    print(csp.output(), end='')

#####################

def solve(solverName=defaultSolver, optNum=1):
    global __solution
    global __solutions
    global solver
    if not solver:
        solver = Solver(solverName, optNum)
    if csp.objective:
        __solution = None
        v = csp.objective
        lb = csp.dom[v].lb()
        ub = csp.dom[v].ub()
        solver.encode(csp)
        csp.commit()
        solver.commit()
        __solution = solver.satSolve()
        if __solution:
            lastSolution = __solution
            if isMinimize():
                ub = solution(v)
                while lb < ub:
                    mid = (lb + ub) // 2
                    csp.cancel()
                    solver.cancel()
                    add(And(lb <= v, v <= mid))
                    solver.encodeDelta(csp)
                    __solution = solver.satSolve()
                    if __solution:
                        ub = solution(v)
                        lastSolution = __solution
                    else:
                        lb = mid + 1
            else:
                lb = solution(v)
                while lb < ub:
                    mid = (lb + ub + 1) // 2
                    csp.cancel()
                    solver.cancel()
                    add(And(mid <= v, v <= ub))
                    solver.encodeDelta(csp)
                    __solution = solver.satSolve()
                    if __solution:
                        lb = solution(v)
                        lastSolution = __solution
                    else:
                        ub = mid - 1
            __solution = lastSolution
            return solution(v)
        else:
            return unsat
    else:
        if len(__solutions) == 0:
            res = solver.encode(csp)
            if not res:
                __solution = None
                return unsat
        else:
            csp.commit()
            solver.commit()
            cs1 = [Eq(x, Num(__solution.getValue(x))) for x in csp.variables if not x.aux]
            cs2 = [p if __solution.getValue(p) else Not(p) for p in csp.bools if not p.aux]
            if len(cs1) == 0:
                csp.add(Not(And(cs2)))
            elif len(cs2) == 0:
                csp.add(Not(And(cs1)))
            else:
                csp.add(Not(And(And(cs1), And(cs2))))
            solver.encodeDelta(csp)
        __solution = solver.satSolve()
        if __solution:
            __solutions.append(__solution)
            return sat
        else:
            __solution = None
            solver.renewSugar()
            return unsat

def solveAll(solverName=defaultSolver, optNum=1):
    global __solutions
    __solutions = []
    varsSize, boolsSize, consSize = csp.size()
    while solve(solverName, optNum) == sat:
        pass
    csp.cancel(varsSize, boolsSize, consSize)
    return __solutions

def use(solverName, optNum=1):
    global solver
    if not solver:
        solver = Solver(solverName, optNum)
    solver = Solver(solverName, optNum)

def dump(fileName, format='csp'):
    global solver
    if not solver:
        solver = Solver(defaultSolver, 1)
    solver.dump(csp, fileName, format)

def solution(*args):
    global __solution
    if len(args) == 0:
        return allSolution()
    if len(args) == 1:
        if __solution:
            return __solution.getValue(args[0])
        else:
            return None
    elif len(args) == 2:
        return args[0].getValue(args[1])

def allSolution(*args):
    global __solution
    global __solutions
    if len(args) == 0:
        sol = __solution
    elif len(args) == 1 and isinstance(args[0], Solution):
        sol = args[0]
    else:
        return None
    return sol.getAllValue()

def bitSolution(*args):
    global __solution
    if len(args) == 1:
        if __solution:
            return __solution.getBitValue(args[0])
        else:
            None
    elif len(args) == 2:
        return args[0].getBitValue(args[1])
