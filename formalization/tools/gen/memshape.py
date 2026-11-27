"""The map of the gate `member` of `+compile-scc-in` (README Gaps 21.14): the
branch of the shape passes (`?.  done`, `memShape` of `CompMember.lean`) cut
at its pushes, and the cell counts of every part of the gate and of the arms
each mode pulls.

    tools/capped.sh -m 3G python3 tools/gen/memshape.py OUTDIR

writes `OUTDIR/memshape.lean` (the parts, each named inside the larger ones,
so that `memShape` is their assembly by `rfl`) and prints the table of cells
(a cell is a pair, counted in the tree, shared parts counted again)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
K = ('C', ('R', 'nhe0b859c3d8aa'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))


def seq(n, k):
    """[a b c ... z] as a list of k elements, the last the rest (as in member.py)."""
    out = []
    n = norm(n)
    for _ in range(k - 1):
        assert n[0] == 'C', n
        out.append(norm(n[1]))
        n = norm(n[2])
    out.append(n)
    return out


def emit(f, defs):
    """As in member.py: later definitions name the earlier ones."""
    subs = []
    for name, n, doc in defs:
        if doc:
            f.write('/-- %s -/\n' % doc)
        f.write('def %s : Noun :=\n  %s\n\n' % (name, lean(n, subs)))
        subs.insert(0, (name, n))
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'

memo = {}


def cells(n):
    if n[0] == 'R':
        k = n[1]
        if k not in memo:
            memo[k] = cells(get(k))
        return memo[k]
    if n[0] == 'A':
        return 0
    return 1 + cells(n[1]) + cells(n[2])


marm = slot(358182910, K)
_, mcore, mhint = seq(marm, 3)
_, mbunt, mb = seq(mcore, 3)
mbody = norm(norm(mb[1])[2])
_, mdone, mtest = seq(mbody, 3)
_, _, memX, _ = seq(mtest, 4)
_, memComp, memR1 = seq(memX, 3)
_, _, r1 = seq(memR1, 3)
_, memInl, memR2 = seq(r1, 3)
r2 = seq(memR2, 3)[2]
r2 = seq(r2, 3)[2]
_, gbunt, r2 = seq(r2, 3)
memR3 = seq(r2, 3)[2]
r3 = seq(memR3, 3)[2]
r3 = seq(r3, 3)[2]
_, memRes, memAfter = seq(r3, 3)
_, _, rsel = seq(memRes, 3)
_, _, memFinal, memShape = seq(rsel, 4)

# memShape = [7 [0 1] [8 RS SH1]]: the `=^ l gen` of +run-shape
s1 = seq(memShape, 3)[2]
_, msRun, msR1 = seq(s1, 3)
# msR1 = [7 [10 [6 0 5] 0 1] [7 [[0 4] 0 3] [8 SHAPE TUPLE]]]
_, msGen, msR2 = seq(msR1, 3)
_, msPin, msR3 = seq(msR2, 3)
_, msShape, msTuple = seq(msR3, 3)
# msShape = [8 COLL BNO]: `collapsed`, then +bake-need-ord
_, msColl, msBno = seq(msShape, 3)
# msColl = [6 TEST MUST MAY]
_, msTest, msMust, msMay = seq(msColl, 4)
# msTuple = [[[0 2] [[1 lazy] [[1 need] [[1 baked] [[1 0] SUR]]]]] [0 14]]
th = norm(msTuple[1])
tl = th
for _ in range(5):
    tl = norm(tl[2])
msSur = tl

parts = [
    ('msRun', msRun, '`(~(run-shape comp gen) nomm [%done ~] ~)` (door arm `0xabee`).'),
    ('msTest', msTest, '`?=(%must mode)`.'),
    ('msMust', msMust, '`(laze-collapse l cape.less.b)` (arm `0x15d7a` of `K`).'),
    ('msMay', msMay, '`(laze-may l cape.less.b)` (arm `0x2eeeb` of `K`).'),
    ('msBno', msBno, '`(bake-need-ord collapsed less.b)` (arm `1398` of `K`).'),
    ('msColl', msColl, '`collapsed`: `+laze-collapse` on `%must`, else `+laze-may`.'),
    ('msShape', msShape, '`shape`: `collapsed`, then `+bake-need-ord`.'),
    ('msSur', msSur, '`(sure-of sure.l cape.less.b)` (arm `0x2bae` of `K`).'),
    ('msTuple', msTuple, '`[[shape *need-lazy *need *baked 0 sur] gen]`.'),
    ('msR3', msR3, 'The push of `shape`, then the tuple.'),
    ('msR2', msR2, 'After the `=^` into `gen`.'),
    ('msR1', msR1, 'The `=^` of `l` into `gen` and the rest.'),
]

with open(os.path.join(OUT, 'memshape.lean'), 'w') as f:
    emit(f, parts)
    f.write('/-- **The cut**: the branch of the shape passes is the run of `+run-shape` and its parts. -/\n')
    f.write('theorem memShape_cut : memShape = C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C msRun msR1))) := rfl\n')

# the table of cells
def arm(ax):
    return slot(ax, K)

door = ('C', ('R', 'comp.door'), ('C', ('A', 0), ('A', 0)))
rows = [
    ('member body (memBody)', mbody),
    ('memComp (the door comp)', memComp),
    ('memInl (+inlined call)', memInl),
    ('memRes (both branches)', memRes),
    ('  memFinal (%done)', memFinal),
    ('  memShape (%may, %must)', memShape),
    ('    msRun (+run-shape call)', msRun),
    ('    msColl (laze-collapse / laze-may)', msColl),
    ('    msBno (+bake-need-ord call)', msBno),
    ('    msSur (+sure-of call)', msSur),
    ('memAfter (was, sur, moved, finish, product)', memAfter),
]
for name, n in rows:
    print('%-45s %6d' % (name, cells(n)))
for name, ax in [('+laze-collapse K 0x15d7a', 0x15d7a), ('+laze-may K 0x2eeeb', 0x2eeeb),
                 ('+bake-need-ord K 1398', 1398), ('+bake-need K 0x5ddd4', 0x5ddd4),
                 ('+sure-of K 0x2bae', 0x2bae), ('+msg-need-ord K 20', 20),
                 ('+inlined K 0x5dde', 0x5dde), ('+shape-collapse? K (scBody)', None)]:
    if ax is None:
        continue
    a = arm(ax)
    print('%-45s %6s' % (name, cells(a) if a else '?'))
for name, ax in [('+run-shape door 0xabee', 0xabee), ('+run door 3071', 3071),
                 ('+collapse-shape door 1526', 1526)]:
    a = slot(ax, door)
    print('%-45s %6s' % (name, cells(a) if a else '?'))
