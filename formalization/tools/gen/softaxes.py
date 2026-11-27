import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
D = ('R', 'comp.door')
a = norm(slot(6910, D))
def seq(n, k):
    out = []
    n = norm(n)
    for _ in range(k - 1):
        assert n[0] == 'C', n
        out.append(norm(n[1]))
        n = norm(n[2])
    out.append(n)
    return out
op, push, rest = seq(a, 3)
assert op == ('A', 8)
q1, bq = seq(rest, 2)
q, gbat = seq(q1, 2)
assert q == ('A', 1)
# gbat = [8 [1 0] [8 [1 1] [8 [1 TRAP] [9 2 0 1]]]]
op, p0, r1 = seq(gbat, 3)
op2, p1, r2 = seq(r1, 3)
op3, p2, r3 = seq(r2, 3)
assert p2[0]=='C' and norm(p2[1])==('A',1)
trap = norm(p2[2])
print('BUNT', lean(push))
print('TRAP', lean(trap))
print('R3', lean(r3))
print('P0', lean(p0), 'P1', lean(p1))
# trap pieces
op, t1, tnone, rest = seq(trap, 4)
print('T1', show(t1,names=False))
op, t2, tthis, rest2 = seq(rest, 4)
print('THIS', lean(tthis))
op, t3, tpair, rest3 = seq(rest2, 4)
print('T3', show(t3, names=False))
print('PAIR', lean(tpair))
print('BOTH', lean(rest3))
