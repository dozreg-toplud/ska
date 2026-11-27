"""Cut the battery of `+sect` (door arm `6906`, the gate's formula) into
named parts and write them as Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/sect.py OUTFILE

The battery is `[6 [3 0 222] scB [0 0]]` (`?>  ?=(^ region-branch)`).
`scB` is the chain of the two `=^` of `+emit` and the two `=.` of
`+set-tag`, then `=.  gen  scThr` and the tail `scTail` (the two asserts and
the product).  `scThr` is `?:  dropping  gen  scND`; `scND` pushes
`made-0`, `made-1`, `o-target` (`scOt`), `inside-branch`, `tars` and `args`
(`scArgs`), then the two `=>` of `~(rep by ..)` (`scRep0`, `scRep1`, with
the gate batteries `scG0`, `scG1` and the bunt of their sample, whose
`(list @uxid)` is `scLB`) and the three `+jab:by` (`scJabs`).  The gates'
branches when `tars` has no target are `scG0Y`, `scG1Y`; the branch with a
target, the same in both, is `scGS`.  Writes OUTFILE between
`-- BEGIN sect` and `-- END sect`; the parts are substituted by structural
equality, so `scBat` unfolds to the pill's noun (`sc_at` is a kernel fact)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm
OUT = sys.argv[1]

def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    return ('C', full(n[1]), full(n[2]))

def sl(ax, n):
    for b in bin(ax)[3:]:
        assert n[0] == 'C'
        n = n[1] if b == '0' else n[2]
    return n

def A(v):
    return ('A', v)

def C(*xs):
    n = xs[-1]
    for x in reversed(xs[:-1]):
        n = ('C', x, n)
    return n

arm = full(slot(6906, ('R', 'comp.door')))
assert arm[1] == A(7)
gate = sl(6, arm)                       # [8 [1 BUNT] [1 BAT] 0 1]
BUNT = sl(13, gate)
BAT = sl(29, gate)
assert sl(6, BAT) == C(A(3), A(0), A(222)) and sl(15, BAT) == C(A(0), A(0))
scB = sl(14, BAT)

def after_eqk(n):
    """[7 [0 1] [8 E [7 [10 ..] [7 [[0 4] 0 3] REST]]]] -> REST"""
    assert sl(2, n) == A(7) and sl(6, n) == C(A(0), A(1)) and sl(14, n) == A(8)
    r = sl(31, n)
    assert sl(2, r) == A(7) and sl(12, r) == A(10)
    r = sl(7, r)
    assert sl(6, r) == C(C(A(0), A(4)), C(A(0), A(3)))
    return sl(7, r)

def after_dot(n):
    """[7 [10 ..] REST] -> REST"""
    assert sl(2, n) == A(7) and sl(12, n) == A(10)
    return sl(7, n)

r = after_eqk(scB)
r = after_eqk(r)
r = after_dot(r)
r = after_dot(r)
assert sl(2, r) == A(7) and sl(6, r)[0] == 'C'
thrE = sl(6, r)                          # [10 [126 THR] 0 1]
assert sl(2, thrE) == A(10) and sl(12, thrE) == A(126) and sl(7, thrE) == C(A(0), A(1))
scThr = sl(13, thrE)
scTail = sl(7, r)
assert sl(2, scThr) == A(6) and sl(6, scThr) == C(A(9), A(1398), A(0), A(31))
assert sl(14, scThr) == C(A(0), A(126))
scND = sl(15, scThr)

def push(n):
    assert sl(2, n) == A(8)
    return sl(6, n), sl(7, n)

made0, r = push(scND)
made1, r = push(r)
scOt, r = push(r)
ins, r = push(r)
tars, r = push(r)
assert tars == C(A(1), A(0))
scArgs, r = push(r)
assert sl(2, r) == A(7)
scRep0 = sl(6, r)
r = sl(7, r)
assert sl(2, r) == A(7)
scRep1 = sl(6, r)
scJabs = sl(7, r)

def rep_parts(rep):
    # [7 [0 1] [8 REPDOOR [9 2 [10 [6 [7 [0 3] [8 BUNTF [[1 G] 0 1]]]] 0 2]]]]
    assert sl(2, rep) == A(7) and sl(6, rep) == C(A(0), A(1))
    k = sl(7, rep)
    assert sl(2, k) == A(8)
    sl9 = sl(7, k)
    assert sl(2, sl9) == A(9) and sl(6, sl9) == A(2)
    e = sl(7, sl9)
    assert sl(2, e) == A(10) and sl(12, e) == A(6) and sl(7, e) == C(A(0), A(2))
    g = sl(13, e)
    assert sl(2, g) == A(7) and sl(6, g) == C(A(0), A(3))
    g8 = sl(7, g)
    assert sl(2, g8) == A(8)
    buntf = sl(6, g8)
    assert sl(14, g8) == C(A(1), sl(29, g8)) and sl(15, g8) == C(A(0), A(1))
    G = sl(29, g8)
    # BUNTF = [[[1 0] [[1 0] LB]] [0 1]]
    assert sl(4, buntf) == C(A(1), A(0)) and sl(10, buntf) == C(A(1), A(0)) and sl(3, buntf) == C(A(0), A(1))
    return G, sl(11, buntf)

scG0, scLB = rep_parts(scRep0)
scG1, lb1 = rep_parts(scRep1)
assert lb1 == scLB

def gate_parts(G):
    # [7 [10 [7 0 13] 0 1] [6 INS [0 7] [8 GET [6 ISATOM Y S]]]]
    assert sl(6, G) == C(A(10), C(A(7), A(0), A(13)), A(0), A(1))
    b = sl(7, G)
    assert sl(2, b) == A(6) and sl(14, b) == C(A(0), A(7))
    n = sl(15, b)
    assert sl(2, n) == A(8)
    t = sl(7, n)
    assert sl(2, t) == A(6) and sl(6, t) == C(A(6), C(A(3), A(0), A(2)), C(A(1), A(1)), A(1), A(0))
    return sl(14, t), sl(15, t)

scG0Y, scGS = gate_parts(scG0)
scG1Y, gs1 = gate_parts(scG1)
assert gs1 == scGS

# the gates that the three `+jab:by` take: `|=(blob +<(par tar.args))`
# (`scParG`), and the gate `lens-hop` (`scLensB`) that builds `scInner`
BOMB = C(A(1), C(A(0), A(0), A(0x6d6f62), A(0)))
found = []
def walk(n):
    if n[0] != 'C':
        return
    if n[1] == A(8) and sl(6, n) == BOMB and sl(7, n)[0] == 'C' and sl(14, n)[0] == 'C' \
            and sl(28, n) == A(1) and sl(15, n) == C(A(0), A(1)):
        found.append((sl(29, n), n))
    walk(n[1]); walk(n[2])
walk(scJabs)
assert len(found) == 2, len(found)
(scParG, _), (scInner, scLensB) = found
assert scParG == C(A(10), C(A(2), A(0), A(59)), A(0), A(6))

parts = [('scParG', scParG), ('scInner', scInner), ('scLensB', scLensB), ('scLB', scLB), ('scGS', scGS), ('scG0Y', scG0Y), ('scG1Y', scG1Y), ('scG0', scG0),
         ('scG1', scG1), ('scRep0', scRep0), ('scRep1', scRep1), ('scJabs', scJabs),
         ('scArgs', scArgs), ('scOt', scOt), ('scND', scND), ('scThr', scThr), ('scTail', scTail),
         ('scB', scB), ('scBat', BAT), ('scBunt', BUNT)]
names = {}

def show(n, top):
    if n in names and not top:
        return names[n]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1], False), show(n[2], False))

out = []
for nm, n in parts:
    out.append('def %s : Noun :=\n  %s' % (nm, show(n, True)))
    names[n] = nm
text = '\n\n'.join(out) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN sect\n') + len('-- BEGIN sect\n')
e = src.index('-- END sect')
open(OUT, 'w').write(src[:b] + '\n' + text + '\n' + src[e:])
print('-- wrote', len(out), 'definitions,', len(text), 'characters')
