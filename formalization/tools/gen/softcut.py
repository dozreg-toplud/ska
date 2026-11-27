"""+soft-cut (battery axis 220588 of comp.door) and +soft-axis (4062) cut at their branches,
and the trap of seCut.  Writes OUT/softcut_defs.lean."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
OUT = sys.argv[1]
D = ('R', 'comp.door')

def seq(n, k):
    out = []
    n = norm(n)
    for _ in range(k - 1):
        assert n[0] == 'C', n
        out.append(norm(n[1]))
        n = norm(n[2])
    out.append(n)
    return out

def atom(n, v):
    n = norm(n)
    assert n == ('A', v), (show(n, maxd=3, names=False)[:100], v)

def gate(arm):
    op, push, rest = seq(arm, 3)
    atom(op, 8)
    q1, bq = seq(rest, 2)
    q, bat = seq(q1, 2)
    atom(q, 1)
    assert eqn(bq, ('C', ('A', 0), ('A', 1)))
    p1, bunt = seq(push, 2)
    atom(p1, 1)
    return bunt, bat

NONE, THIS, ANY = 0x656e6f6e, 0x73696874, 0x796e61
# soft-axis
saArm = norm(slot(4062, D))
saBunt, saBat = gate(saArm)
op, t1, b1, r1 = seq(saBat, 4); atom(op, 6)
assert show(t1, names=False) == '[5 [1 %s] 0 24]' % hex(NONE), show(t1, names=False)
assert show(b1, names=False) == '[1 %s]' % hex(ANY)
op, t2, saThis, saCell = seq(r1, 4); atom(op, 6)
assert show(t2, names=False) == '[5 [1 %s] 0 24]' % hex(THIS)
# soft-cut
scArm = norm(slot(220588, D))
scBunt, scBat = gate(scArm)
op, scAx, r = seq(scBat, 3); atom(op, 8)
op, tA, bA, r = seq(r, 4); atom(op, 6)
assert show(tA, names=False) == '[5 [1 %s] 0 2]' % hex(ANY)
scNil = bA
assert show(bA, names=False) == '[[1 0 0] 0 62]', show(bA, names=False)
op, scT2, scTop, r = seq(r, 4); atom(op, 6)
op, tN, bN, r = seq(r, 4); atom(op, 6)
assert show(tN, names=False) == '[5 [1 %s] 0 116]' % hex(NONE)
assert eqn(bN, scNil)
op, tT, scThis, scCell = seq(r, 4); atom(op, 6)
assert show(tT, names=False) == '[5 [1 %s] 0 116]' % hex(THIS)
# the seCut trap
src = open('/home/kirill/work/ska-scratch/wt/ska-formalization-i/formalization/lemmas/Compiler/CompSccLoopSoftEmitCut.lean').read()
m = re.search(r'def seCut : Noun :=\n  (.*)\n', src)
seCut = parse(m.group(1))
op, a, r = seq(seCut, 3); atom(op, 7)
assert eqn(a, ('C', ('A', 0), ('A', 1)))
op, a, r = seq(r, 3); atom(op, 8)
assert show(a, names=False) == '[1 0 0]'
op, a, r = seq(r, 3); atom(op, 8)
assert show(a, names=False) == '[0 0x1efff]', show(a, names=False)
op, a, r = seq(r, 3); atom(op, 8)
q, scTrap = seq(a, 2); atom(q, 1)
assert show(r, names=False) == '[9 2 0 1]'
op, tq, bq, r = seq(scTrap, 4); atom(op, 6)
assert show(tq, names=False) == '[5 [1 0] 0 6]'
assert show(bq, names=False) == '[[0 14] 0 510]'
op, a, r = seq(r, 3); atom(op, 7)
assert eqn(a, ('C', ('A', 0), ('A', 1)))
op, scCall, r = seq(r, 3); atom(op, 8)
op, a, r = seq(r, 3); atom(op, 7)
assert show(a, names=False) == '[10 [1022 0 5] 0 1]'
op, a, r = seq(r, 3); atom(op, 7)
assert show(a, names=False) == '[[0 4] 0 3]'
op, two, r = seq(r, 3); atom(op, 9); atom(two, 2)
op, ed, r = seq(r, 3); atom(op, 10)
fourteen, scWelds = seq(ed, 2); atom(fourteen, 14)
assert show(r, names=False) == '[10 [6 0 29] 0 3]'

parts = [
    ('saBunt', saBunt), ('saThis', saThis), ('saCell', saCell),
    ('scBunt', scBunt), ('scAx', scAx), ('scT2', scT2), ('scTop', scTop), ('scThis', scThis), ('scCell', scCell),
    ('scCall', scCall), ('scWelds', scWelds),
]
with open(os.path.join(OUT, 'softcut_defs.lean'), 'w') as f:
    for name, n in parts:
        f.write('def %s : Noun :=\n  %s\n\n' % (name, lean(n)))
    print('cells')
    def cells(n):
        n = norm(n)
        return 0 if n[0] == 'A' else 1 + cells(n[1]) + cells(n[2])
    for name, n in parts:
        print(name, cells(n), show(n, names=False)[:300])
