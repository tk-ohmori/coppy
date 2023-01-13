from coppy import *

a = Int('a', 4)
b = Int('b', 4)
add(a + b == 3)

# # solve
if solve() == sat:
    print('a:', solution(a))
    print('b:', solution(b))

# # solve all
# while solve() == sat:
#     print('-' * 10)
#     print('a:', solution(a))
#     print('b:', solution(b))

# # solve all
# sols = solveAll()
# for s in sols:
#     print('a:', solution(s, a))
#     print('b:', solution(s, b))

# # optimize
# maximize(a)
# res = solve()
# print(res)

# # bit
# c = BitVec('c', 4)
# d = BitVec('d', 4)
# add(c & d == 0b1100)
# add(c >> 2 == d & 0b11)
# if solve() == sat:
#     print('c:', solution(c))
#     print('d:', solution(d))