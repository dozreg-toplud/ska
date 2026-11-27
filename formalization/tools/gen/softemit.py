"""The map of `+soft-emit` (README Gaps 21.17): the arm (battery axis 13660 of the door `comp`,
core axis 0x555c, 2136 cells) cut at the pushes of its gate, and the cell counts.

    tools/capped.sh -m 3G python3 tools/gen/softemit.py OUTDIR

writes `OUTDIR/softemit.lean` (the parts, later ones naming earlier ones, and `seBat_cut`,
`seArm_cut` by `rfl`) and prints the table of cells (a cell is a pair, shared parts counted
again).

The gate's battery (`seBat`), on the subject `[bat [[o s] core]]`, `core = [door [gen ctx]]`:

    [6 seT0 [0 30]                              ?~  req.s  gen
     [8 seAxs                                   =/  axs  (soft-axes ned.s)
      [7 [0 1] [8 seCut                         =^  cut  gen  (the trap over req.s)
       [7 seGenP [7 sePin                         (gen of the product, then cut at the head)
        [8 seOps                                =/  ops  (weld ops.cut (murn tops.cut ..))
         [8 seTries                             =/  tries  (murn tops.cut ..)
          [8 seHed                              =/  hed  (~(got by blocks.gen) head.s)
           [6 seHedT seRest [0 0]]]]]]]]]]       ?>  ?=([~ ~ %hop ~ *] hed)

    seRest = [6 seTriesT seEmir seTryPath]       ?~  tries  (emir head.s ~ ops fin.hed)  ...
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

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


def emit(f, defs):
    subs = []
    for name, n, doc in defs:
        if doc:
            f.write('/-- %s -/\n' % doc)
        f.write('def %s : Noun :=\n  %s\n\n' % (name, lean(n, subs)))
        if cells(n) >= 8:  # small parts ([0 30], [[0 4] 0 3]) are not named inside others
            subs.insert(0, (name, n))


D = ('R', 'comp.door')
seArm = norm(slot(13660, D))
# seArm = [8 [1 BUNT] [1 BAT] [0 1]]
op, push, rest = seq(seArm, 3)
atom(op, 8)
seBunt = push
q1, bq = seq(rest, 2)
q, seBat = seq(q1, 2)
atom(q, 1)
assert norm(bq) == norm(('C', ('A', 0), ('A', 1)))

op, seT0, seNil, r1 = seq(seBat, 4)
atom(op, 6)
op, seAxs, r2 = seq(r1, 3)
atom(op, 8)
op, sub1, r3 = seq(r2, 3)
atom(op, 7)
assert norm(sub1) == norm(('C', ('A', 0), ('A', 1)))
op, seCut, r4 = seq(r3, 3)
atom(op, 8)
op, seGenP, r5 = seq(r4, 3)
atom(op, 7)
op, sePin, r6 = seq(r5, 3)
atom(op, 7)
op, seOps, r7 = seq(r6, 3)
atom(op, 8)
op, seTries, r8 = seq(r7, 3)
atom(op, 8)
op, seHed, r9 = seq(r8, 3)
atom(op, 8)
op, seHedT, seRest, crash = seq(r9, 4)
atom(op, 6)
assert norm(crash) == norm(('C', ('A', 0), ('A', 0)))
op, seTriesT, seEmir, seTryPath = seq(seRest, 4)
atom(op, 6)

parts = [
    ('seBunt', seBunt, 'The push of the bunt of `[o=@uwoo s=soft-call]`.'),
    ('seT0', seT0, '`?=(~ req.s)`.'),
    ('seNil', seNil, '`gen` (`[0 30]`).'),
    ('seAxs', seAxs, '`(soft-axes ned.s)` (core axis `0x2afe`).'),
    ('seCut', seCut, 'The trap over `req.s`: `+soft-cut` at each requirement, the lists in front of `acc`.'),
    ('seGenP', seGenP, 'The `=^`: `gen` of the product.'),
    ('sePin', sePin, 'The `=^`: `cut` at the head.'),
    ('seOps', seOps, '`ops`: `(weld ops.cut (murn tops.cut ..))`, the moves of the parts taken whole.'),
    ('seTries', seTries, '`tries`: `(murn tops.cut ..)`, the parts under each noun.'),
    ('seHed', seHed, '`hed`: `(~(got by blocks.gen) head.s)`.'),
    ('seHedT', seHedT, 'The `?>` test `?=([~ ~ %hop ~ *] hed)`.'),
    ('seTriesT', seTriesT, '`?=(~ tries)`.'),
    ('seEmir', seEmir, '`(emir head.s ~ ops fin.hed)`: the path without tries.'),
    ('seTryPath', seTryPath, 'The path with tries (not linked).'),
]

with open(os.path.join(OUT, 'softemit.lean'), 'w') as f:
    emit(f, parts)
    def L(t):
        if t[0] == 'N':
            return t[1]
        if t[0] == 'A':
            return '(A %d)' % t[1]
        return '(C %s %s)' % (L(t[1]), L(t[2]))

    def lst(*xs):
        out = xs[-1]
        for x in reversed(xs[:-1]):
            out = ('C', x, out)
        return out
    N = lambda s: ('N', s)
    A_ = lambda v: ('A', v)
    rest = lst(A_(6), N('seHedT'), lst(A_(6), N('seTriesT'), N('seEmir'), N('seTryPath')), lst(A_(0), A_(0)))
    rest = lst(A_(8), N('seHed'), rest)
    rest = lst(A_(8), N('seTries'), rest)
    rest = lst(A_(8), N('seOps'), rest)
    rest = lst(A_(7), N('sePin'), rest)
    rest = lst(A_(7), N('seGenP'), rest)
    rest = lst(A_(8), N('seCut'), rest)
    rest = lst(A_(7), lst(A_(0), A_(1)), rest)
    rest = lst(A_(8), N('seAxs'), rest)
    bat = lst(A_(6), N('seT0'), N('seNil'), rest)
    f.write('/-- `+soft-emit`\'s gate battery cut at its pushes. -/\n')
    f.write('def seBat : Noun :=\n  %s\n\n' % L(bat))
    f.write('/-- `+soft-emit`: the gate `[8 [1 bunt] [1 seBat] [0 1]]`. -/\n')
    f.write('def seArm : Noun :=\n  C (A 8) (C seBunt (C (C (A 1) seBat) (C (A 0) (A 1))))\n\n')
    f.write('/-- `+soft-emit` in the pill (battery axis 13660 of the door). -/\n')
    f.write('theorem se_at : slot? 13660 comp.door = some seArm := by kernel_rfl\n')

rows = [('+soft-emit arm (seArm)', seArm), ('  seBat', seBat)] + [('    ' + n, x) for n, x, _ in parts]
for name, n in rows:
    print('%-40s %6d' % (name, cells(n)))
for name, ax in [('+soft-axes door 6910', 6910), ('+soft-cut door 220588', 220588),
                 ('+soft-axis door 4062', 4062), ('+soft-pair door 13652', 13652)]:
    a = slot(ax, D)
    print('%-40s %6s' % (name, cells(a) if a else '?'))
