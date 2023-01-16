# Coppy
* Constraint Programming in Python
* This program uses CSP encoder [Sugar](https://gitlab.com/cspsat/prog-sugar.git) and is made on the basis of [Copris](https://gitlab.com/cspsat/prog-copris.git).

## Installation
* ```pip install git+https://github.com/tk-ohmori/coppy.git```
* Clone the repository and ```pip install path/to/coppy/dist/coppy-0.1-py3-none-any.whl```

## Usage
### Import
```py
from coppy import *
```

### Define CSP
* Define integer variable
    ```py
    # Integer variable x where lo <= x <= hi
    x = Int('x', lo, hi)

    # Integer variables where lo <= x, y, z <= hi
    xs = Ints('x y z', lo, hi)
    xs = Ints(['x', 'y', 'z'], lo, hi)

    # Integer variables where lo <= x <= hi
    # The name is numbered (x_1, x_2, ..., x_n)
    xs = IntList('x', size, lo, hi)

    # Integer variable(s) where x in {0, 1}
    x = Bit('x')
    xs = Bits('x y z')
    xs = BitList('x', size)
    ```
    * If no name is given, it is automatically named.
    * Only one integer value is given, if it is greater than 0, then 0 <= x <= v. Otherwise, if it is smaller than 0, v <= x <= 0.
    * Instead of giving upper and lower bounds, a set of integers can be given.
* Define boolean variable
    ```py
    p = Bool('p')
    p, q = Bools('p q')
    ps = BoolList('p', size)
    ```
* Add constraint
    ```py
    add(x + 3 == y)
    add(Sum(xs) < 300)
    add(Max(x, y, z) >= k)
    add(Imp(p & ~q, r))
    ```
* Show CSP
    * Show CSP
        ```py
        show()
        ```
    * Output CSP to the file
        ```py
        dump('filename.csp')
        ```
    * Output CNF to the file
        ```py
        dump('filename.cnf', 'cnf')
        ```

### Search solutions
```py
res = solve() # -> return sat or unsat
if res == sat:
    print(solution(x))
    print(solution([x, y, z]))

# Get all solution
sol = allSolution()
print(sol[x])

# Search all solutions
sols = solveAll()
for sol in sols:
    print(solution(sol, x))
    print(solution(sol, [x, y]))
```
* Use 'solve' method repeatedly to obtain the next solution.

### Set optimization
```py
maximize(x)
# or minimize(x)

res = solve() # return optimum value of x
```

## SAT Solver
You can use any SAT solver (command) by using 'use' method.  
(Specify '2' for a SAT solver taking two arguments.)  
Default solver is sat4j.
```py
use('clasp')
use('minisat', 2)
```

## Bitwise operation
Use BitVec method to define pseudo variable with bitwise operations.
```py
x = BitVec('x', n) # n is bit length
y = BitVec('y', n)

add(x & y == 12)
add(x >> 2 == y & 3)

if solve() == sat:
    print('x:', solution(x))
    print('y:', solution(y))
```
* Use 'bitSolution' method to obtain bit form solution.  
    (The head of the list is LSB.)
* Set ```signed=true``` to arguent of BitVec method to define signed bit variable.

## Example
Consider the following example.  
* Solve all integers x and y such that : $7x + 11y = 1$ where $-100 \le x, y \le 100$  
    ```py
    from coppy import *
    x = Int('x', -100, 100)
    y = Int('y', -100, 100)
    add(7 * x + 11 * y == 1)

    while solve() == sat:
        print(f'(x, y) = ({solution(x)}, {solution(y)})')
    ```