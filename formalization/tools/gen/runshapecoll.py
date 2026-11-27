"""The nouns of `+laze-to-inter1` (arm `5598` of `K`), `+laze-collapse`
(arm `0x15d7a`) and `+laze-may` (arm `0x2eeeb`), cut for their links (README
Gaps 26, track A).

`+laze-to-inter1` has the shape of `+lazy-to-inter1` (`shapecoll2i.py`)
without `+need-to-ordered`: its body is `[7 [0 1] [6 TEST YES NO]]` with

    NO = [8 ROLL [9 2 [10 [6 [0 59] [7 [0 3] [8 TURN
           [8 [[[1 0] LZB] [0 28] [0 2]] [[1 BG] [0 1]]]]]] [0 2]]]]

`TURN` the `+turn` over `fork.laz` (gate `TG`, sample bunt `TB`), `LZB` the
bunt of `laze` (arm `0x575ee` of `K`, at axis `15`) and `BG` the gate of the
`+roll` over `bond.laz`.  `+laze-collapse` is `+shape-collapse` with arm
`5598` in place of `6006`.

    tools/capped.sh -m 3G python3 tools/gen/runshapecoll.py OUTDIR

writes `OUTDIR/runshapecoll.lean`."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
K = ('C', ('R', 'nh5592f9d7750f'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))


def seq(n, k):
    out = []
    n = norm(n)
    for _ in range(k - 1):
        assert n[0] == 'C', n
        out.append(norm(n[1]))
        n = norm(n[2])
    out.append(n)
    return out


def gate(ax):
    arm = slot(ax, K)
    _, core, hint = seq(arm, 3)
    _, bunt, b = seq(core, 3)
    assert norm(bunt)[1] == ('A', 1)
    body = norm(norm(b[1])[2])
    return norm(bunt)[2], body, hint


def emit(f, defs):
    subs = []
    for name, n, doc in defs:
        f.write('/-- %s -/\ndef %s : Noun :=\n  %s\n\n' % (doc, name, lean(n, subs)))
        subs.insert(0, (name, n))


defs = []
# +laze-to-inter1
tBunt, tBody, tHint = gate(5598)
_, _, t1 = seq(tBody, 3)             # [7 [0 1] T1]
_, _, tYes, tNo = seq(t1, 4)         # [6 TEST YES NO]
assert show(tYes, names=False) == '[[0 12] 1 0]', show(tYes, names=False)
_, roll_arm, slam = seq(tNo, 3)      # [8 ROLL SLAM]
assert show(roll_arm, names=False) == '[9 0x2fbdfc 0 0x3ffff]'
_, _, s10 = seq(slam, 3)             # [9 2 S10]
_, s6, s02 = seq(s10, 3)             # [10 S6 [0 2]]
sample = norm(norm(s6)[2])           # [[0 59] [7 [0 3] INNER]]
assert show(slot(2, sample), names=False) == '[0 59]'
gate_f = norm(slot(3, sample))
assert show(slot(6, gate_f), names=False) == '[0 3]'
inner = norm(slot(7, gate_f))        # [8 TURN R1]
_, turn, r1 = seq(inner, 3)
_, smp, bgc = seq(r1, 3)             # [8 SMP [[1 BG] [0 1]]]
lzb = slot(5, smp)
assert show(slot(3, smp), names=False) == '[[0 28] 0 2]', show(slot(3, smp), names=False)
bg = slot(5, bgc)
assert show(slot(3, bgc), names=False) == '[0 1]'
# TURN = [8 ARM [9 2 [10 [6 [0 58] [7 [0 3] [8 [1 TB] [[1 TG] [0 1]]]]] [0 2]]]]
_, _, tx = seq(slot(7, turn), 3)    # [9 2 X]
_, t6, _ = seq(tx, 3)                # [10 [6 SAM] [0 2]]
tsam = norm(norm(t6)[2])
tmk = norm(slot(7, norm(slot(3, tsam))))
assert norm(slot(2, tmk)) == ('A', 8), show(tmk)
tb = norm(slot(13, tmk)); tg = norm(slot(29, tmk))
assert eqn(slot(6, tmk), ('C', ('A', 1), tb))
defs += [
    ('lztTB', tb, 'The sample bunt of the gate of the `+turn` over `fork.laz`.'),
    ('lztTG', tg, 'The gate of the `+turn` over `fork.laz`: `[(laze-to-inter laz-y) (laze-to-inter laz-n)]`.'),
    ('lztTurn', turn, '`fork-new`: the `+turn` over `fork.laz`.'),
    ('lztLzb', lzb, 'The bunt of `laze` in the sample of the gate of the `+roll`.'),
    ('lztBG', bg, 'The gate of the `+roll` over `bond.laz`.'),
    ('lztNo', tNo, 'The `+roll` over the bonds, with forks or bonds.'),
    ('lztBody', tBody, 'The gate body of `+laze-to-inter1`.'),
    ('lztBunt', tBunt, 'Its sample bunt.'),
    ('lztHint', tHint, 'Its `%fast` hint.'),
]
# +laze-collapse
cBunt, cBody, cHint = gate(0x15d7a)
defs += [
    ('lcoBody', cBody, 'The gate body of `+laze-collapse`.'),
    ('lcoBunt', cBunt, 'Its sample bunt.'),
    ('lcoHint', cHint, 'Its `%fast` hint.'),
]
with open(os.path.join(OUT, 'runshapecoll.lean'), 'w') as f:
    emit(f, defs)
print(show(turn, names=False))
print(show(tb, names=False)); print(show(tg, names=False)); print(show(lzb, names=False))
