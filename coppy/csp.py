import functools
import operator
from abc import ABCMeta, abstractmethod

class Expr(metaclass=ABCMeta):
    def __init__(self):
        pass

#######################################
'''
Term Class
'''

class Term(Expr, metaclass=ABCMeta):
    def __init__(self):
        super().__init__()
        self.containsBitVec = False
        self.n = None
        self.signed = None

    def __add__(self, x):
        return Add(self, x)

    def __radd__(self, x):
        return Add(x, self)
    
    def __sub__(self, x):
        return Sub(self, x)

    def __rsub__(self, x):
        return Sub(x, self)
    
    def __mul__(self, x):
        return Mul(self, x)
    
    def __rmul__(self, x):
        return Mul(x, self)

    def __truediv__(self, x):
        return Div(self, x)

    def __rtruediv__(self, x):
        return Div(x, self)

    def __floordiv__(self, x):
        return Div(self, x)

    def __rfloordiv__(self, x):
        return Div(x, self)

    def __mod__(self, x):
        return Mod(self, x)

    def __rmod__(self, x):
        return Mod(x, self)
        
    # def __pow__(self, x):
    #     return Pow(self, x)

    def __and__(self, x):
        return BitAnd(self, x)

    def __rand__(self, x):
        return BitAnd(x, self)
        
    def __or__(self, x):
        return BitOr(self, x)
        
    def __ror__(self, x):
        return BitOr(x, self)
        
    def __xor__(self, x):
        return BitXor(self, x)
        
    def __rxor__(self, x):
        return BitXor(x, self)
    
    def __lshift__(self, x):
        return AshL(self, x)
    
    def __rshift__(self, x):
        if self.signed:
            return AshR(self, x)
        else:
            return LshR(self, x)
        
    # def max(self, x):
    #     return Max(self, x)
        
    # def min(self, x):
    #     return Min(self, x)
        
    def __eq__(self, x):
        return Eq(self, x)
        
    def __ne__(self, x):
        return Ne(self, x)
        
    def __le__(self, x):
        return Le(self, x)
        
    def __lt__(self, x):
        return Lt(self, x)
        
    def __ge__(self, x):
        return Ge(self, x)
        
    def __gt__(self, x):
        return Gt(self, x)

    def __neg__(self):
        return Neg(self)
        
    @abstractmethod
    def value(solution):
        raise NotImplementedError()
    
    def __repr__(self):
        return str(self)
    
    @abstractmethod
    def trueRepr(self):
        pass

class NIL(Term):
    def __init__(self):
        super().__init__()

    def value(self, solution):
        raise('NIL: value of NIL is not defined')
    
    def __str__(self):
        return 'nil'

class Num(Term):
    def __init__(self, value):
        super().__init__()
        assert isinstance(value, int)
        self.v = value
    
    def value(self, solution):
        return self.v
    
    def variables(self):
        return []
    
    def bools(self):
        return []
    
    def __str__(self):
        return str(self.v)
    
    def trueRepr(self):
        return repr(self)
    
class ZERO(Num):
    def __init__(self):
        super().__init__(0)
    
class ONE(Num):
    def __init__(self):
        super().__init__(1)
    
class Var(Term):
    __count = 0

    def __init__(self, name):
        super().__init__()
        if name:
            self.name = name
        else:
            self.__count += 1
            self.name = '__I_' + str(self.__count)
        self.aux = False

    def variables(self):
        return [self]

    def bools(self):
        return []
    
    def value(self, solution):
        return solution.intValues[self]
    
    def __str__(self):
        return self.name
    
    def __repr__(self):
        return 'Int("' + self.name + '",' + repr(csp.dom[self]) + ')'
    
    def trueRepr(self):
        return repr(self)
    
    def __hash__(self):
        return hash(self.name)

class Abs(Term):
    def __init__(self, x0):
        super().__init__()
        self.x0 = x0
        self.containsBitVec = x0.containsBitVec
        self.n = x0.n
        self.signed = x0.signed
    
    def variables(self):
        return self.x0.variables()
    
    def bools(self):
        return self.x0.bools()
    
    def value(self, solution):
        return abs(self.x0.value(solution))
    
    def __str__(self):
        return 'Abs(' + str(self.x0) + ')'
    
    def trueRepr(self):
        return 'Abs(' + self.x0.trueRepr() + ')'
    
class Neg(Term):
    def __init__(self, x0):
        super().__init__()
        self.x0 = x0
        self.containsBitVec = x0.containsBitVec
        self.n = x0.n
        self.signed = x0.signed
    
    def variables(self):
        return self.x0.variables()
    
    def bools(self):
        return self.x0.bools()
    
    def value(self, solution):
        return -self.x0.value(solution)
    
    def __str__(self):
        return 'Neg(' + str(self.x0) + ')'
    
    def trueRepr(self):
        return 'Neg(' + self.x0.trueRepr() + ')'

def xsToTermForm(xs):
    res = xs[0] if isinstance(xs[0], list) else list(xs)
    return list(map(lambda x: x if isinstance(x, Term) else Num(x), res))

class Add(Term):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)
        self.containsBitVec, self.n, self.signed = bitVecInfo(self.xs)
    
    def variables(self):
        return sum([x.variables() for x in self.xs], [])
    
    def bools(self):
        return sum([x.bools() for x in self.xs], [])
    
    def value(self, solution):
        return sum([x.value(solution) for x in self.xs])
    
    def __str__(self):
        return 'Add(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Add(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

class Sum(Term):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)
        self.containsBitVec, self.n, self.signed = bitVecInfo(self.xs)
    
    def variables(self):
        return sum([x.variables() for x in self.xs], [])
    
    def bools(self):
        return sum([x.bools() for x in self.xs], [])
    
    def value(self, solution):
        return sum([x.value(solution) for x in self.xs])
    
    def __str__(self):
        return 'Sum(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Sum(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

class Sub(Term):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)
        self.containsBitVec, self.n, self.signed = bitVecInfo(self.xs)
    
    def variables(self):
        return sum([x.variables() for x in self.xs], [])
    
    def bools(self):
        return sum([x.bools() for x in self.xs], [])
    
    def value(self, solution):
        ys = [x.value(solution) for x in self.xs]
        l = len(ys)
        if l == 0:
            return 0
        elif l == 1:
            return ys[0]
        else:
            return ys[0] - sum(ys[1:])
    
    def __str__(self):
        return 'Sub(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Sub(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

class Mul(Term):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)
        self.containsBitVec, self.n, self.signed = bitVecInfo(self.xs)
    
    def variables(self):
        return sum([x.variables() for x in self.xs], [])
    
    def bools(self):
        return sum([x.bools() for x in self.xs], [])
    
    def value(self, solution):
        return functools.reduce(operator.mul, [x.value(solution) for x in self.xs])
    
    def __str__(self):
        return 'Mul(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Mul(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

class Div(Term):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
        self.containsBitVec, self.n, self.signed = bitVecInfo([x0, x1])

    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        a0 = self.x0.value(solution)
        a1 = self.x1.value(solution)
        if a1 > 0:
            if a0 >= 0:
                return a0 // a1
            else:
                return (a0 - a1 + 1) // a1
        else:
            if a0 >= 0:
                return (a0 - a1 - 1) // a1
            else:
                a0 // a1
    
    def __str__(self):
        return 'Div(' + str(self.x0) + ',' + str(self.x1) + ')'
    
    def trueRepr(self):
        return 'Div(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Mod(Term):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
        self.containsBitVec, self.n, self.signed = bitVecInfo([x0, x1])

    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        r = self.x0.value(solution) % self.x1.value(solution)
        if r > 0:
            return r
        else:
            r + self.x1.value(solution)
    
    def __str__(self):
        return 'Mod(' + str(self.x0) + ',' + str(self.x1) + ')'
    
    def trueRepr(self):
        return 'Mod(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

# class Pow(Term):
#     ###
#     unimplemented
#     ###

class Max(Term):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)
        self.containsBitVec, self.n, self.signed = bitVecInfo(xs)
    
    def variables(self):
        return sum([x.variables() for x in self.xs], [])
    
    def bools(self):
        return sum([x.bools() for x in self.xs], [])
    
    def value(self, solution):
        return max([x.value(solution) for x in self.xs])
    
    def __str__(self):
        return 'Max(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Max(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

class Min(Term):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)
        self.containsBitVec, self.n, self.signed = bitVecInfo(xs)
    
    def variables(self):
        return sum([x.variables() for x in self.xs], [])
    
    def bools(self):
        return sum([x.bools() for x in self.xs], [])
    
    def value(self, solution):
        return min([x.value(solution) for x in self.xs])
    
    def __str__(self):
        return 'Min(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Min(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

class If(Term):
    def __init__(self, c, x0, x1):
        super().__init__()
        self.c = c
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
        self.containsBitVec, self.n, self.signed = bitVecInfo([x0, x1])
    
    def variables(self):
        return self.c.variables() + self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.c.bools() + self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        if self.c.value(solution):
            return self.x0.value(solution)
        else:
            return self.x1.value(solution)
    
    def __str__(self):
        return 'If(' + str(self.c) + ',' + str(self.x0) + ',' + str(self.x1) + ')'
    
    def trueRepr(self):
        return 'If(' + self.c.trueRepr() + ',' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

'''
Constraint Class
'''

class Constraint(Expr, metaclass=ABCMeta):
    def __init__(self):
        super().__init__()

    def toInt(self):
        return If(self, ONE, ZERO)
    
    def __invert__(self):
        return Not(self)
    
    def __and__(self, c):
        return And(self, c)
    
    def __rand__(self, c):
        return And(c, self)
        
    def __or__(self, c):
        return Or(self, c)
        
    def __ror__(self, c):
        return Or(c, self)
        
    def __xor__(self, c):
        return Xor(self, c)
        
    def __rxor__(self, c):
        return Xor(c, self)
    
    @abstractmethod
    def value(self, solution):
        pass

    def __repr__(self):
        return str(self)
    
    @abstractmethod
    def trueRepr(self):
        pass

class FALSE(Constraint):
    def __init__(self):
        super().__init__()
    
    def value(self, soution):
        return False
    
    def __str__(self):
        return 'False'
    
    def trueRepr(self):
        return repr(self)

class TRUE(Constraint):
    def __init__(self):
        super().__init__()
    
    def value(self, soution):
        return True
    
    def __str__(self):
        return 'True'
    
    def trueRepr(self):
        return repr(self)
    
class BOOL(Constraint):
    def __init__(self, name):
        super().__init__()
        self.name = name
        self.aux = False
    
    def variables(self):
        return []

    def bools(self):
        return [self]
    
    def value(self, solution):
        return solution.boolValues[self]
    
    def __str__(self):
        return self.name
    
    def __repr__(self):
        return 'Bool("' + self.name + '")'
    
    def trueRepr(self):
        return repr(self)
    
    def __hash__(self):
        return hash(self.name)
    
class Not(Constraint):
    def __init__(self, c0):
        super().__init__()
        self.c0 = c0
    
    def variables(self):
        return self.c0.variables()

    def bools(self):
        return self.c0.bools()

    def value(self, solution):
        return not self.c0.value(solution)
    
    def __str__(self):
        return 'Not(' + str(self.c0) + ')'
    
    def trueRepr(self):
        return 'Not(' + self.c0.trueRepr() + ')'

class And(Constraint):
    def __init__(self, *cs):
        super().__init__()
        self.cs = cs[0] if isinstance(cs[0], list) else list(cs)
    
    def variables(self):
        return sum([c.variables() for c in self.cs], [])
    
    def bools(self):
        return sum([c.bools() for c in self.cs], [])

    def value(self, solution):
        return all([c.value(solution) for c in self.cs])
    
    def __str__(self):
        return 'And(' + ','.join([str(c) for c in self.cs]) + ')'
    
    def trueRepr(self):
        return 'And(' + ','.join([c.trueRepr() for c in self.cs]) + ')'

class Or(Constraint):
    def __init__(self, *cs):
        super().__init__()
        self.cs = cs[0] if isinstance(cs[0], list) else list(cs)
    
    def variables(self):
        return sum([c.variables() for c in self.cs], [])
    
    def bools(self):
        return sum([c.bools() for c in self.cs], [])

    def value(self, solution):
        return any([c.value(solution) for c in self.cs])
    
    def __str__(self):
        return 'Or(' + ','.join([str(c) for c in self.cs]) + ')'
    
    def trueRepr(self):
        return 'Or(' + ','.join([c.trueRepr() for c in self.cs]) + ')'

class Imp(Constraint):
    def __init__(self, c0, c1):
        super().__init__()
        self.c0 = c0
        self.c1 = c1
    
    def variables(self):
        return self.c0.variables() + self.c1.variables()
    
    def bools(self):
        return self.c0.bools() + self.c1.bools()
    
    def value(self, solution):
        return not self.c0.value(solution) or self.c1.value(solution)
    
    def __str__(self):
        return 'Imp(' + str(self.c0) + ',' + str(self.c1) + ')'
    
    def trueRepr(self):
        return 'Imp(' + self.c0.trueRepr() + ',' + self.c1.trueRepr() + ')'

class Xor(Constraint):
    def __init__(self, c0, c1):
        super().__init__()
        self.c0 = c0
        self.c1 = c1
    
    def variables(self):
        return self.c0.variables() + self.c1.variables()
    
    def bools(self):
        return self.c0.bools() + self.c1.bools()
    
    def value(self, solution):
        return self.c0.value(solution) ^ self.c1.value(solution)
    
    def __str__(self):
        return 'Xor(' + str(self.c0) + ',' + str(self.c1) + ')'
    
    def trueRepr(self):
        return 'Xor(' + self.c0.trueRepr() + ',' + self.c1.trueRepr() + ')'

class Iff(Constraint):
    def __init__(self, c0, c1):
        super().__init__()
        self.c0 = c0
        self.c1 = c1
    
    def variables(self):
        return self.c0.variables() + self.c1.variables()
    
    def bools(self):
        return self.c0.bools() + self.c1.bools()
    
    def value(self, solution):
        return self.c0.value(solution) == self.c1.value(solution)
    
    def __str__(self):
        return 'Iff(' + str(self.c0) + ',' + str(self.c1) + ')'
    
    def trueRepr(self):
        return 'Iff(' + self.c0.trueRepr() + ',' + self.c1.trueRepr() + ')'

class Eq(Constraint):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
    
    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        return not self.x0.value(solution) or self.x1.value(solution)

    def __str__(self):
        return 'Eq(' + str(self.x0) + ',' + str(self.x1) + ')'

    def trueRepr(self):
        return 'Eq(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Ne(Constraint):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
    
    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        return self.x0.value(solution) != self.x1.value(solution)

    def __str__(self):
        return 'Ne(' + str(self.x0) + ',' + str(self.x1) + ')'

    def trueRepr(self):
        return 'Ne(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Le(Constraint):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
    
    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        return self.x0.value(solution) <= self.x1.value(solution)

    def __str__(self):
        return 'Le(' + str(self.x0) + ',' + str(self.x1) + ')'

    def trueRepr(self):
        return 'Le(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Lt(Constraint):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
    
    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        return self.x0.value(solution) < self.x1.value(solution)

    def __str__(self):
        return 'Lt(' + str(self.x0) + ',' + str(self.x1) + ')'

    def trueRepr(self):
        return 'Lt(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Ge(Constraint):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
    
    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        return self.x0.value(solution) >= self.x1.value(solution)

    def __str__(self):
        return 'Ge(' + str(self.x0) + ',' + str(self.x1) + ')'

    def trueRepr(self):
        return 'Ge(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Gt(Constraint):
    def __init__(self, x0, x1):
        super().__init__()
        self.x0 = x0 if isinstance(x0, Term) else Num(x0)
        self.x1 = x1 if isinstance(x1, Term) else Num(x1)
    
    def variables(self):
        return self.x0.variables() + self.x1.variables()
    
    def bools(self):
        return self.x0.bools() + self.x1.bools()
    
    def value(self, solution):
        return self.x0.value(solution) > self.x1.value(solution)

    def __str__(self):
        return 'Gt(' + str(self.x0) + ',' + str(self.x1) + ')'

    def trueRepr(self):
        return 'Gt(' + self.x0.trueRepr() + ',' + self.x1.trueRepr() + ')'

class Alldifferent(Constraint):
    def __init__(self, *xs):
        super().__init__()
        self.xs = xsToTermForm(xs)

    def variables(self):
        return sum([x.variables() for x in self.xs], [])

    def bools(self):
        return sum([x.bools() for x in self.xs], [])

    def value(self, solution):
        a = [x.value(solution) for x in self.xs]
        return all([all([a[i] != a[j] for j in range(i+1, len(a))]) for i in range(len(a))])
    
    def __str__(self):
        return 'Alldifferent(' + ','.join([str(x) for x in self.xs]) + ')'
    
    def trueRepr(self):
        return 'Alldifferent(' + ','.join([x.trueRepr() for x in self.xs]) + ')'

#######################################

'''
Domain class
'''

class Domain:
    def __init__(self, *args):
        if len(args) == 2 and all([isinstance(arg, int) for arg in args]):
            self = IntervalDomain(args[0], args[1])
        elif len(args) == 1 and isinstance(args[0], int):
            self = IntervalDomain(args[0], args[0])
        elif len(args) == 1 and isinstance(args[0], set) and all([isinstance(a, int) for a in list(args[0])]):
            self = SetDomain(args[0])

class IntervalDomain(Domain):
    def __init__(self, lo, hi):
        super().__init__()
        self.lo = lo
        self.hi = hi
    
    def lb(self):
        return self.lo
    
    def ub(self):
        return self.hi
    
    def contains(self, a):
        return self.lo <= a and a <= self.hi
    
    def __str__(self):
        return  f'Domain(lo:{self.lo},hi:{self.hi})'
    
    def __repr__(self):
        return  f'IntervalDomain(lo={self.lo},hi={self.hi})'

class SetDomain(Domain):
    def __init__(self, values):
        super().__init__()
        self.values = values
    
    def lb(self):
        return min(self.values)

    def ub(self):
        return max(self.values)

    def contains(self, a):
        return a in self.values
    
    def __str__(self):
        return 'Domain(' + ','.join([str(v) for v in self.values]) + ')'
    
    def __repr__(self):
        return 'SetDomain(' + repr(self.values) + ')' 
    
class EnumDomain(Domain):
    def __init__(self, values):
        super().__init__()
        self.values = values
        self.size = len(values)

    def contains(self, value):
        return value in self.values
    
    def __str__(self):
        return  'Domain(' + ','.join([str(v) for v in self.values]) + ')'
    
    def __repr__(self):
        return 'EnumDomain(' + repr(self.values) + ')'

#######################################
'''
CSP Class
'''

class CSP:
    def __init__(self, variables=[], bools=[], dom=dict(), constraints=[], objective=None, target=0):
        self.variables = variables
        self.bools = bools
        self.dom = dom
        self.constraints = constraints

        self.objective = objective
        self.target = target
    
    def Int(self, x, d):
        if all([x.name != y.name for y in self.variables]):
            self.variables.append(x)
            self.dom[x] = d
        return x

    def Bool(self, p):
        if all([p.name != q.name for q in self.bools]):
            self.bools.append(p)
        return p

    # def Real():
    #     ###
    #     unimplemented
    #     ###

    def Bit(self, x):
        self.Int(x, IntervalDomain(0, 1))
        return x
        
    def getAll(self):
        return (self.variables, self.bools, self.dom, self.constraints)

    def add(self, *cs):
        if len(cs) == 1 and isinstance(cs[0], list) and all([isinstance(c, Constraint) for c in cs[0]]):
            cs = cs[0]
        assert all([isinstance(c, Constraint) for c in cs]), 'only constraints are allowed'
        badVariables = list(filter(lambda _: not _ in self.variables, sum([c.variables() for c in cs], [])))
        badBools = list(filter(lambda _: not _ in self.bools, sum([c.bools() for c in cs], [])))
        if len(badVariables):
            raise('undeclared int varialbles ' + ','.join(list(badVariables)))
        if len(badBools):
            raise('undeclared bool varialbles ' + ','.join(list(badBools)))
        if len(cs) == 1:
            self.constraints.append(cs[0])
        else:
            self.constraints += cs
    
    def size(self):
        return len(self.variables), len(self.bools), len(self.constraints)

    def commit(self):
        self.variablesSizeCommit = len(self.variables)
        self.boolsSizeCommit = len(self.bools)
        self.constraintsSizeCommit = len(self.constraints)

    def cancel(self, *args):
        if len(args) == 0:
            self.variables = self.variables[:self.variablesSizeCommit]
            self.bools = self.bools[:self.boolsSizeCommit]
            self.constraints = self.constraints[:self.constraintsSizeCommit]
        elif len(args) == 3:
            self.variables = self.variables[:args[0]]
            self.bools = self.bools[:args[1]]
            self.constraints = self.constraints[:args[2]]
        else:
            raise('Invalid arguments')
    
    def variablesDelta(self):
        return self.variables[self.variablesSizeCommit:]
    
    def boolsDelta(self):
        return self.bools[self.boolsSizeCommit:]
    
    def constraintsDelta(self):
        return self.constraints[self.constraintsSizeCommit:]
    
    def minimize(self, x):
        self.objective = x
        self.target = -1

    def maximize(self, x):
        self.objective = x
        self.target = 1

    def isMinimize(self):
        return self.target < 0

    def isMaximize(self):
        return self.target > 0
    
    def clearObjective(self):
        self.objective = None
        self.target = 0
    
    def satisfiedBy(self, solution):
        return all([self.dom[x].contains(x.value(solution)) for x in self.variables]) and all([c.value(solution) for c in self.constraints])

    def output(self):
        res = ''
        for x in self.variables:
            d = self.dom[x]
            if isinstance(d, IntervalDomain):
                res += 'int(' + str(x) + ',' + str(d.lo) + ',' + str(d.hi) + ')\n'
            elif isinstance(d, SetDomain):
                res += 'int(' + str(x) + ',' + str(d.values) + ')\n'
        for p in self.bools:
            res += 'bool(' + str(p) + ')\n'
        for c in self.constraints:
            res += str(c) + '\n'
        if self.isMinimize():
            res += 'minimize(' + str(self.objective) + ')\n'
        elif self.isMaximize():
            res += 'maximize(' + str(self.objective) + ')\n'
        return res
    
    def __str__(self):
        res = 'CSP('
        res += 'variables:' + str(self.dom) + ','
        res += 'bools:' + str(self.bools) + ','
        res += 'constraints:' + str(self.constraints) + ')'
        return res
    
    def __repr__(self):
        res =  'CSP('
        res += 'variables=' + repr(self.variables)
        res += ',bools=' + repr(self.bools)
        res += ',dom=' + repr(self.dom)
        res += ',constraints=[' + ', '.join([c.trueRepr() for c in self.constraints]) + ']'
        # res += ',constraints=' + repr(self.constraints)
        if self.objective:
            res += ',objective=' + repr(self.objective)
            res += ',target=' + repr(self.target)
        res += ')'
        return res

##########################

class Solution:
    def __init__(self, intValues, boolValues):
        self.intValues = intValues
        self.boolValues = boolValues
    
    def getValue(self, *args):
        if len(args) == 1:
            x = args[0]
            if isinstance(x, Term):
                if isinstance(x, Var):
                    return self.intValues[x]
                else:
                    return x.value(self)
            elif isinstance(x, Constraint):
                if isinstance(x, BOOL):
                    return self.boolValues[x]
                else:
                    return x.value(self)
            elif isinstance(x, list):
                return [self.getValue(a) for a in x]
        if len(args) > 1:
            return [self.getValue(a) for a in args]
    
    def getAllValue(self):
        return {**self.intValues, **self.boolValues}

    def getBitValue(self, *args):
        if len(args) == 1:
            bv = args[0]
            if isinstance(bv, list):
                return [self.getBitValue(b) for b in bv]
            elif isinstance(bv, Term) and bv.containsBitVec:
                _, n, signed = bitVecInfo([bv])
                v = self.getValue(bv)
                if signed and v < 0:
                    v =  ((-v) ^ int('1'*n, 2)) + 1
                res = []
                for i in range(n):
                    res.append(v & 1)
                    v >>= 1
                return res
        if len(args) > 1:
            return [self.getBitValue(bv) for bv in args]
    
    def __str__(self):
        return 'Solution(' + str(self.intValues)  + ',' + str(self.boolValues) + ')'
    
    def __repr__(self):
        return 'Solution(' + str(self.intValues)  + ',' + str(self.boolValues) + ')'

##########################

csp = CSP()

'''

'''
__intNameCount = 0
def Int(*args):
    """
    Generate Int varialble
    args = (name, lo, hi)
    args = (lo, hi)
    args = (name, v) --┬--> (v < 0) lo = v, hi = 0
    args = (v) --------┘    (v >= 0) lo = 0, hi = v
    args = (name, set(int))
    args = (set(int))
    args = (name, domain)
    args = (domain)
    """
    global __intNameCount
    if len(args) == 3 and isinstance(args[0], str) and isinstance(args[1], int) and isinstance(args[2], int):
        name = args[0]
        lo = min(args[1:])
        hi = max(args[1:])
        dom = IntervalDomain(lo, hi)
    elif len(args) == 2 and isinstance(args[0], int) and isinstance(args[1], int):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        lo = min(args)
        hi = max(args)
        dom = IntervalDomain(lo, hi)
    elif len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], int):
        name = args[0]
        lo = min(args[1], 0)
        hi = max(args[1], 0)
        dom = IntervalDomain(lo, hi)
    elif len(args) == 1 and isinstance(args[0], int):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        lo = min(args[0], 0)
        hi = max(args[0], 0)
        dom = IntervalDomain(lo, hi)
    elif len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], set) and all([isinstance(arg, int) for arg in args[1]]):
        name = args[0]
        dom = SetDomain(args[1])
    elif len(args) == 1 and isinstance(args[0], set) and all([isinstance(arg, int) for arg in args[0]]):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        dom = SetDomain(args[0])
    elif len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], Domain):
        name = args[0]
        dom = args[1]
    elif len(args) == 1 and isinstance(args[0], Domain):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        dom = args[0]
    else:
        raise('Invalid arguments')
    return csp.Int(Var(name), dom)

def Ints(names, *args):
    if isinstance(names, str):
        names = names.split()
    return [Int(name, *args) for name in names]

def IntList(*args):
    """
    Generate Int variables list
    args = (name, size, lo, hi)
    args = (size, lo, hi)
    args = (size, v)
    args = (name, size, set(int))
    args = (size, set(int))
    """
    global __intNameCount
    if len(args) == 4 and isinstance(args[0], str) and all([isinstance(a, int) for a in args[1:]]):
        name, size, lo, hi = args
        return [Int(f'{name}_{i}', lo, hi) for i in range(size)]
    elif len(args) == 3 and all([isinstance(a, int) for a in args]):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        size, lo, hi = args
        return [Int(f'{name}_{i}', lo, hi) for i in range(size)]
    elif len(args) == 2 and isinstance(args[0], int) and isinstance(args[1], int):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        size, v = args
        lo = min(v, 0)
        hi = max(v, 0)
        return [Int(f'{name}_{i}', lo, hi) for i in range(size)]
    elif len(args) == 3 and isinstance(args[0], str) and isinstance(args[1], int) and isinstance(args[2], set) and all([isinstance(a, int) for a in args[2]]):
        name, size, dset = args
        return [Int(f'{name}_{i}', dset) for i in range(size)]
    elif len(args) == 2 and isinstance(args[0], int) and isinstance(args[1], set) and all([isinstance(a, int) for a in args[1]]):
        __intNameCount += 1
        name = f'__I_{__intNameCount}'
        size, dset = args
        return [Int(f'{name}_{i}', dset) for i in range(size)]
    else:
        raise('Invalid arguments')

__boolNameCount = 0
def Bool(*args):
    """
    Generate Bool variable
    args = (name)
    args = ()
    """
    global __boolNameCount
    if len(args) == 1 and isinstance(args[0], str):
        name = args[0]
    elif len(args) == 0:
        __boolNameCount += 1
        name = f'__B_{__boolNameCount}'
    else:
        raise('Invalid arguments')
    return csp.Bool(BOOL(name))

def Bools(names):
    if isinstance(names, str):
        names = names.split()
    return [Bool(name) for name in names]

def BoolList(*args):
    """
    Generate Bool variables list
    args = (name, size)
    args = (size)
    """
    global __boolNameCount
    if len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], int):
        name, size = args
    elif len(args) == 1 and isinstance(args[0], int):
        __boolNameCount += 1
        name = f'__B_{__boolNameCount}'
        size = args[0]
    else:
        raise('Invalid arguments')
    return [Bool(f'{name}_{i + 1}') for i in range(size)]

# def Real():
#     ###
#     unimplemented
#     ###

# def Reals():
#     ###
#     unimplemented
#     ###

# def RealVector():
#     ###
#     unimplemented
#     ###

__bitNameCount = 0
def Bit(*args):
    """
    Generate Bit (Int(0,1)) variable
    args = (name)
    args = ()
    """
    global __bitNameCount
    if len(args) == 1 and isinstance(args[0], str):
        name = args[0]
    elif len(args) == 0:
        __bitNameCount += 1
        name = f'__BI_{__bitNameCount}'
    else:
        raise('Invalid arguments')
    return csp.Bit(Var(name))

def Bits(names):
    if isinstance(names, str):
        names = names.split()
    return [Bit(name) for name in names]

def BitList(*args):
    """
    Generate Bit variables list
    args = (name, size)
    args = (size)
    """
    global __bitNameCount
    if len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], int):
        name, size = args
    elif len(args) == 1 and isinstance(args[0], int):
        __bitNameCount += 1
        name = f'__BI_{__bitNameCount}'
        size = args[0]
    return [Bit(f'{name}_{i + 1}') for i in range(size)]

'''
BitVec class

bits = b[0], b[1], ... , b[n-1]
        LSB <--        --> MSB
'''

def bitVecInfo(xs):
    lst = [(x.n, x.signed) for x in xs if isinstance(x, Term) and x.containsBitVec]
    if len(lst) == 0:
        return False, None, None
    elif len(lst) == 1:
        return True, lst[0][0], lst[0][1] 
    elif all([l[0] == lst[0][0] for l in lst[1:]]):
        if all([l[1] == lst[0][1] for l in lst[1:]]):
            return True, lst[0][0], lst[0][1]
        else:
            raise(f'Sign of BitVecs must be same ({lst})')
    else:
        raise(f'Bits length of BitVecs must be same ({lst})')

__bitVecNameCount = 0
def BitVec(*args, signed=False):
    """
    Generate BitVec variable
    args = (name, bit_amount)
    args = (bit_amount)
    """
    global __bitVecNameCount
    if len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], int):
        name, n = args
    elif len(args) == 1 and isinstance(args[0], int):
        __bitVecNameCount += 1
        name = f'__BV_{__bitVecNameCount}'
        n = args[0]
    else:
        raise('Invalid arguments')
    if n > 0:
        if signed:
            itg = csp.Int(Var(name), IntervalDomain(-2**(n - 1), 2**(n - 1) - 1))
        else:
            itg = csp.Int(Var(name), IntervalDomain(0, 2**n - 1))
        itg.containsBitVec = True
        itg.n = n
        itg.signed = signed
        return itg
    else:
        raise('Error: Bit length must be greater than 0')

def BitVecWithBits(*args, signed=False, value=None):
    """
    Generate BitVec varialbe with bits expression
    bits = b[0], b[1], ... , b[n-1]
           LSB <--          --> MSB
    (if signed = True, b[n-1] is sign bit)
    args = (name, bit)
    args = (name)

    Parameters
    ----------
    value : Term
        generate BitVec such that BitVec == value (mod 2**n)
    """
    global __bitVecNameCount
    if len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], int):
        name, n = args
    elif len(args) == 1 and isinstance(args[0], int):
        __bitVecNameCount += 1
        name = f'__BV_{__bitVecNameCount}'
        n = args[0]
    else:
        raise('Invalid arguments')
    if n > 0:
        bits = [Bit(f'{name}_{k + 1}') for k in range(n)]
        if signed:
            itg = Sum([b * (2**i) for i, b in enumerate(bits[:-1])]) - bits[-1] * (2**(n - 1))
        else:
            itg = Sum([b * (2**i) for i, b in enumerate(bits)])
        if value:
            N = 2**n
            if signed:
                csp.add(Imp(value % N < (N//2), value % N == itg))
                csp.add(Imp(value % N >= (N//2), (value % N) - N == itg))
            else:
                csp.add(value % N == itg)
        itg.containsBitVec = True
        itg.n = n
        itg.signed = signed
        return itg, bits
    else:
        raise('Error: Bit length must be greater than 0')

def BitVecs(names, n, signed=False):
    if isinstance(names, str):
        names = names.split()
    return [BitVec(name, n, signed)[0] for name in names]

######################

def BitAnd(x0, x1):
    if not (x0.containsBitVec or x1.containsBitVec):
        raise('Error: Either variable must be BitVec')
    if isinstance(x0, int):
        return Bit(And(x1, x0))
    _, n, signed = bitVecInfo([x0, x1])
    N = 2**n
    _, bits0 = BitVecWithBits(n, signed=signed, value=x0)
    bv2, bits2 = BitVecWithBits(n, signed=signed)
    for b in bits0 + bits2:
        for v in b.variables():
            v.aux = True
    if isinstance(x1, int):
        for i in range(n):
            if x1 & (1 << i):
                csp.add(bits0[i] == bits2[i])
    else:
        _, bits1 = BitVecWithBits(n, signed=signed, value=x1)
        for b in bits1:
            for v in b.variables():
                v.aux = True
        for i in range(n):
            csp.add(bits0[i] * bits1[i] == bits2[i])
    return bv2
    
def BitOr(x0, x1):
    if not (x0.containsBitVec or x1.containsBitVec):
        raise('Error: Either variable must be BitVec')
    if isinstance(x0, int):
        return Bit(And(x1, x0))
    _, n, signed = bitVecInfo([x0, x1])
    N = 2**n
    _, bits0 = BitVecWithBits(n, signed=signed, value=x0)
    bv2, bits2 = BitVecWithBits(n, signed=signed)
    for b in bits0 + bits2:
        for v in b.variables():
            v.aux = True
    if isinstance(x1, int):
        for i in range(n):
            if x1 & (1 << i):
                csp.add(bits2[i] == 1)
            else:
                csp.add(bits0[i] == bits2[i])
    else:
        _, bits1 = BitVecWithBits(n, signed=signed, value=x1)
        for b in bits1:
            for v in b.variables():
                v.aux = True
        for i in range(n):
            csp.add(Imp((bits0[i] + bits1[i] > 0), bits2[i] == 1))
    return bv2
    
def BitXor(x0, x1):
    if not (x0.containsBitVec or x1.containsBitVec):
        raise('Error: Either variable must be BitVec')
    if isinstance(x0, int):
        return Bit(And(x1, x0))
    _, n, signed = bitVecInfo([x0, x1])
    N = 2**n
    _, bits0 = BitVecWithBits(n, signed=signed, value=x0)
    bv2, bits2 = BitVecWithBits(n, signed=signed)
    for b in bits0 + bits2:
        for v in b.variables():
            v.aux = True
    if isinstance(x1, int):
        for i in range(n):
            if x1 & (1 << i):
                csp.add(bits0[i] + bits2[i] == 1)
            else:
                csp.add(bits0[i] == bits2[i])
    else:
        _, bits1 = BitVecWithBits(n, signed=signed, value=x1)
        for b in bits1:
            for v in b.variables():
                v.aux = True
        for i in range(n):
            csp.add((bits0[i] + bits1[i]) % 2 == bits2[i])
    return bv2
    
def AshL(x, sw):
    if not x.containsBitVec:
        raise('Error: Varialbe must be BitVec')
    if not isinstance(sw, int):
        raise('Error: shift value must be int')
    if sw < 1 or x.n - 1 < sw:
        raise('Error: invalide shift amount')
    n = x.n
    signed = x.signed
    N = 2**n
    if signed:
        _, xbits = BitVecWithBits(n, signed=signed, value=x)
        bv, bits = BitVecWithBits(n, signed=signed)
        for b in xbits + bits:
            for v in b.variables():
                v.aux = True
        for i in range(n - sw):
            csp.add(bits[sw + i] == xbits[i])
        for i in range(sw):
            csp.add(bits[i] == 0)
    else:
        bv = BitVec(n, signed=signed)
        for v in bv.variables():
            v.aux = True
        csp.add((x * (2**sw)) % N == bv)
    return bv

def AshR(x, sw):
    if not x.containsBitVec:
        raise('Error: varialbe must be BitVec')
    if not isinstance(sw, int):
        raise('Error: shift value must be int')
    if sw < 1 or x.n - 1 < sw:
        raise('Error: invalide shift amount')
    n = x.n
    signed = x.signed
    N = 2**n
    if signed:
        xbv, xbits = BitVecWithBits(n, signed=signed, value=x)
        bv, bits = BitVecWithBits(n, signed=signed)
        for b in xbits + bits:
            for v in b.variables():
                v.aux = True
        csp.add(Imp(xbv >= 0, And(And([xbits[sw + i] == bits[i] for i in range(n - sw -1)]), And([bits[i] == 0 for i in range(n - sw - 1, n)]))))
        csp.add(Imp(xbv < 0, And(And([xbits[sw + i] == bits[i] for i in range(n - sw -1)]), And([bits[i] == 1 for i in range(n - sw - 1, n)]))))
        return bv
    else:
        return LshR(x, sw)

def LshR(x, sw):
    if not x.containsBitVec:
        raise('Error: Varialbe must be BitVec')
    if not isinstance(sw, int):
        raise('Error: shift value must be int')
    if sw < 1 or x.n - 1 < sw:
        raise('Error: invalide shift amount')
    n = x.n
    signed = x.signed
    bv, bits = BitVecWithBits(n, signed=signed)
    # print(bv)
    # print(type(bv))
    # print(bv.variables())
    # for b in bits:
    #     print('bbbb:', type(b))
    for v in bv.variables():
        v.aux = True
    N = 2**n
    csp.add(x % N - x % (2**sw) == Sum([bits[i] * (2**(i + sw)) for i in range(n - sw)]))
    for i in range(n - sw, n):
        csp.add(bits[i] == 0)
    return bv
