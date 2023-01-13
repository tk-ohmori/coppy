from .csp import *

import os
from tempfile import gettempdir
from random import randint
import subprocess
import functools

jarLibDir = os.path.dirname(__file__) + '/lib/'
sugarPath = jarLibDir + 'sugar-2.3.4.jar'
sat4jPath = jarLibDir + 'org.sat4j.core.jar'
import jpype
import jpype.imports
from jpype.types import *
jpype.startJVM(classpath=[sugarPath, sat4jPath])
# jpype.startJVM(classpath=['../../prog-sugar/build/sugar-2.3.4.jar'])
from jp.kobe_u import sugar as javaSugar
from jp.kobe_u.sugar.expression import Expression as SugarExpr
import java

tmpDir = gettempdir()

class Solver():
    def __init__(self, solverName='sat_solver', optNum=1):
        self.solverName = solverName
        self.optNum = optNum
        self.tmpNum = randint(10**9, 10**10-1)
        self.satFileName = f'{tmpDir}/sugar{self.tmpNum}.cnf'
        self.mapFileName = f'{tmpDir}/sugar{self.tmpNum}.map'
        self.outFileName = f'{tmpDir}/sugar{self.tmpNum}.out'
        # self.logFileName = f'{tmpDir}/sugar{self.tmpNum}.log'
        javaSugar.SugarMain().init()
        self.encoder = Encoder(self.satFileName, self.mapFileName)
        self.stats = dict()
    
    def renewSugar(self):
        javaSugar.SugarMain().init()
        self.encoder = Encoder(self.satFileName, self.mapFileName)
    
    def encode(self, csp):
        return self.encoder.encode(csp)
    
    def encodeDelta(self, csp):
        return self.encoder.encodeDelta(csp)

    def satSolve(self):
        self.stats['variables'] = self.encoder.encoder.getSatVariablesCount()
        self.stats['clauses'] = self.encoder.encoder.getSatClausesCount()
        self.stats['size'] = self.encoder.encoder.getSatFileSize()
        if self.solverName == 'sat4j':
            from org.sat4j.minisat import SolverFactory
            from org.sat4j.reader import DimacsReader
            from org.sat4j.specs import ContradictionException
            sat4jSolver = SolverFactory.newDefault()
            reader = DimacsReader(sat4jSolver)
            writer = open(self.outFileName, 'w')
            try:
                problem = reader.parseInstance(self.satFileName)
                if problem.isSatisfiable():
                    writer.write('SAT\n')
                    model = problem.model()
                    sb = ''
                    for i in range(model.length):
                        sb += str(model[i]) + ' '
                    sb += '0\n'
                    writer.write(sb)
                else:
                    writer.write('UNSAT\n')
            except ContradictionException:
                writer.write('UNSAT\n')
            writer.close()
            sat4jSolver.reset()
        elif self.optNum == 1:
            res = subprocess.run([self.solverName, self.satFileName], stdout=subprocess.PIPE)
            f = open(self.outFileName, 'wb')
            f.write(res.stdout)
            f.close()
        elif self.optNum == 2:
            subprocess.run([self.solverName, self.satFileName, self.outFileName])
        else:
            raise('Invalid sat solver information are set')
        self.encoder.commit()
        return self.encoder.decode(self.outFileName, csp)
    
    def commit(self):
        self.encoder.commit()
    
    def cancel(self):
        self.encoder.cancel()
    
    def dumpCsp(self, csp, fileName):
        translator = Translator()
        expressions = translator.toSugar(csp)
        f = open(fileName, 'w')
        for expression in expressions:
            f.write(str(expression) + '\n')
        f.close()
    
    def dumpCnf(self, csp, fileName):
        self.encode(csp)
        inputFile = open(self.satFileName, 'r')
        outputFile = open(fileName, 'w')
        outputFile.write(inputFile.read())
        inputFile.close()
        outputFile.close()

    def dump(self, csp, fileName, format='csp'):
        if format == 'csp':
            self.dumpCsp(csp, fileName)
        elif format == 'cnf':
            self.dumpCnf(csp, fileName)

class Translator:
    def __init__(self):
        self.sugarVarNameMap = dict()
        self.sugarBoolNameMap = dict()
    
    def createSugarExpr(self, x, *xs):
        lst = java.util.ArrayList()
        for xx in xs:
            lst.add(xx)
        return SugarExpr.create(x, lst)
    
    def toSugarName(self, arg):
        if isinstance(arg, Var):
            sugarName = self.sugarVarNameMap.get(arg)
            if not sugarName:
                sugarName = self.toSugarName(arg.name)
                self.sugarVarNameMap[arg] = sugarName
            return sugarName
        elif isinstance(arg, BOOL):
            sugarName = self.sugarBoolNameMap.get(arg)
            if not sugarName:
                sugarName = self.toSugarName(arg.name)
                self.sugarBoolNameMap[arg] = sugarName
            return sugarName
        elif isinstance(arg, str):
            res = ''
            for c in arg:
                if 'A' <= c <= 'Z' or 'a' <= c <= 'z' or '0' <= c <= '9' or c in '_+-*/%=<>!&|':
                    res += c
                elif 0x80 <= ord(c) <= 0x10ffff:
                    res += c
                elif ord(c) < 0x100:
                    res += '${:02x}'.format(ord(c))
                else:
                    res += '${04x}'.format(ord(c))
            return res

    def toSugarTerm(self, x):
        if isinstance(x, NIL):
            return SugarExpr.NIL
        elif isinstance(x, Num):
            return SugarExpr.create(x.v)
        elif isinstance(x, Var):
            return SugarExpr.create(self.toSugarName(x.name))
        elif isinstance(x, Abs):
            return self.createSugarExpr(SugarExpr.ABS, self.toSugarTerm(x.x0))
        elif isinstance(x, Neg):
            return self.createSugarExpr(SugarExpr.NEG, self.toSugarTerm(x.x0))
        elif isinstance(x, Add):
            return self.createSugarExpr(SugarExpr.ADD, *map(lambda _: self.toSugarTerm(_), x.xs))
        elif isinstance(x, Sum):
            return self.createSugarExpr(SugarExpr.ADD, *map(lambda _: self.toSugarTerm(_), x.xs))
        elif isinstance(x, Sub):
            return self.createSugarExpr(SugarExpr.SUB, *map(lambda _: self.toSugarTerm(_), x.xs))
        elif isinstance(x, Mul):
            return functools.reduce(lambda x0, x1: self.createSugarExpr(SugarExpr.MUL, self.toSugarTerm(x0), self.toSugarTerm(x1)), x.xs)
        elif isinstance(x, Div):
            return self.createSugarExpr(SugarExpr.DIV, self.toSugarTerm(x.x0), self.toSugarTerm(x.x1))
        elif isinstance(x, Mod):
            return self.createSugarExpr(SugarExpr.MOD, self.toSugarTerm(x.x0), self.toSugarTerm(x.x1))
        elif isinstance(x, Max):
            return functools.reduce(lambda x0, x1: self.createSugarExpr(SugarExpr.MAX, self.toSugarTerm(x0), self.toSugarTerm(x1)), x.xs)
        elif isinstance(x, Min):
            return functools.reduce(lambda x0, x1: self.createSugarExpr(SugarExpr.MIN, self.toSugarTerm(x0), self.toSugarTerm(x1)), x.xs)
        elif isinstance(x, If):
            return self.createSugarExpr(SugarExpr.IF, self.toSugarConstraint(x.c), self.toSugarTerm(x.x0), self.toSugarTerm(x.x1))

    def toSugarConstraint(self, c):
        if isinstance(c, FALSE):
            return SugarExpr.FALSE
        elif isinstance(c, TRUE):
            return SugarExpr.TRUE
        elif isinstance(c, BOOL):
            return SugarExpr.create(self.toSugarName(c.name))
        elif isinstance(c, Not):
            return self.createSugarExpr(SugarExpr.NOT, self.toSugarConstraint(c.c0))
        elif isinstance(c, And):
            return self.createSugarExpr(SugarExpr.AND, *map(lambda _: self.toSugarConstraint(_), c.cs))
        elif isinstance(c, Or):
            return self.createSugarExpr(SugarExpr.OR, *map(lambda _: self.toSugarConstraint(_), c.cs))
        elif isinstance(c, Imp):
            return self.createSugarExpr(SugarExpr.IMP, self.toSugarConstraint(c.c0), self.toSugarConstraint(c.c1))
        elif isinstance(c, Xor):
            return self.createSugarExpr(SugarExpr.XOR, self.toSugarConstraint(c.c0), self.toSugarConstraint(c.c1))
        elif isinstance(c, Iff):
            return self.createSugarExpr(SugarExpr.IFF, self.toSugarConstraint(c.c0), self.toSugarConstraint(c.c1))
        elif isinstance(c, Eq):
            return self.createSugarExpr(SugarExpr.EQ, self.toSugarTerm(c.x0), self.toSugarTerm(c.x1))
        elif isinstance(c, Ne):
            return self.createSugarExpr(SugarExpr.NE, self.toSugarTerm(c.x0), self.toSugarTerm(c.x1))
        elif isinstance(c, Le):
            return self.createSugarExpr(SugarExpr.LE, self.toSugarTerm(c.x0), self.toSugarTerm(c.x1))
        elif isinstance(c, Lt):
            return self.createSugarExpr(SugarExpr.LT, self.toSugarTerm(c.x0), self.toSugarTerm(c.x1))
        elif isinstance(c, Ge):
            return self.createSugarExpr(SugarExpr.GE, self.toSugarTerm(c.x0), self.toSugarTerm(c.x1))
        elif isinstance(c, Gt):
            return self.createSugarExpr(SugarExpr.GT, self.toSugarTerm(c.x0), self.toSugarTerm(c.x1))
        elif isinstance(c, Alldifferent):
            return self.createSugarExpr(SugarExpr.ALLDIFFERENT, *map(lambda _: self.toSugarTerm(_), c.xs))
        # ## unimplement
        # ## branch for global constraints
        # elif isinstance(c, ):
        #     return 

    # ## unimplement
    # ## method for global constraints
    # def toSugarAny(self, a):
    #     pass

    def toSugarInt(self, x, d):
        if isinstance(d, IntervalDomain):
            lo = SugarExpr.create(d.lo)
            hi = SugarExpr.create(d.hi)
            return SugarExpr.create(SugarExpr.INT_DEFINITION, self.toSugarTerm(x), lo, hi)
        elif isinstance(d, SetDomain):
            dom = sorted(d.values)
            xs = [self.toSugarTerm(x), SugarExpr.create(dom)]
            return SugarExpr.create(SugarExpr.INT_DEFINITION, xs)

    def toSugarBool(self, p):
        return SugarExpr.create(SugarExpr.BOOL_DEFINITION, self.toSugarConstraint(p))

    def toSugar(self, csp):
        expressions = java.util.ArrayList()
        for v in csp.variables:
            expressions.add(self.toSugarInt(v, csp.dom[v]))
        for p in csp.bools:
            expressions.add(self.toSugarBool(p))
        if csp.objective:
            x = self.createSugarExpr(SugarExpr.OBJECTIVE_DEFINITION, SugarExpr.MINIMIZE if csp.isMinimize() else SugarExpr.MAXIMIZE, self.toSugarTerm(csp.objective))
            expressions.add(x)
        for c in csp.constraints:
            expressions.add(self.toSugarConstraint(c))
        return expressions

    def toSugarDelta(self, csp):
        expressions = java.util.ArrayList()
        for v in csp.variablesDelta():
            expressions.add(self.toSugarInt(v, csp.dom[v]))
        for p in csp.boolsDelta():
            expressions.add(self.toSugarBool(p))
        for c in csp.constraintsDelta():
            expressions.add(self.toSugarConstraint(c))
        return expressions

class Encoder:
    def __init__(self, satFileName, mapFileName):
        self.satFileName = satFileName
        self.mapFileName = mapFileName
        self.translator = Translator()
        self.sugarCsp = javaSugar.csp.CSP()
        self.converter = javaSugar.converter.Converter(self.sugarCsp)
        self.encoder = javaSugar.encoder.Encoder(self.sugarCsp)
    
    def commit(self):
        self.sugarCsp.commit()
        if not self.sugarCsp.isUnsatisfiable():
            self.encoder.commit()
    
    def cancel(self):
        self.sugarCsp.cancel()
        self.encoder.cancel()
        self.encoder.outputMap(self.mapFileName)
    
    def encode(self, csp):
        expressions = self.translator.toSugar(csp)
        javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = True
        self.converter.convert(expressions)
        expressions.clear()
        SugarExpr.clear()
        self.sugarCsp.propagate()
        if self.sugarCsp.isUnsatisfiable():
            return False
        else:
            simplifier = javaSugar.converter.Simplifier(self.sugarCsp)
            simplifier.simplify()
            self.encoder.encode(self.satFileName, False)
            self.encoder.outputMap(self.mapFileName)
            return True

    def encodeDelta(self, csp):
        self.sugarCsp.cancel()
        expressions = self.translator.toSugarDelta(csp)
        javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = False
        self.converter.convert(expressions)
        javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = True
        SugarExpr.clear()
        self.encoder.cancel()
        self.encoder.encodeDelta()
        self.encoder.outputMap(self.mapFileName)

    def decode(self, outFileName, csp):
        if self.encoder.decode(outFileName):
            intNameValues = dict()
            for v in self.sugarCsp.getIntegerVariables():
                if not v.isAux():
                    intNameValues[v.getName()] = v.getValue()
            intValues = dict()
            for x in csp.variables:
                s = self.translator.toSugarName(x)
                if s in intNameValues:
                    intValues[x] = intNameValues[s]
            boolNameValues = dict()
            for v in self.sugarCsp.getBooleanVariables():
                if not v.isAux():
                    boolNameValues[v.getName()] = v.getValue()
            boolValues = dict()
            for p in csp.bools:
                s = self.translator.toSugarName(p)
                if s in boolNameValues:
                    boolValues[p] = boolNameValues[s]
            return Solution(intValues, boolValues)
        else:
            None
