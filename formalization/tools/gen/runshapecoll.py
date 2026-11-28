"""The nouns of `+laze-to-inter1` (arm `5598` of `K`), `+laze-collapse`
(arm `0x15d7a`) and `+laze-may` (arm `0x2eeeb`), cut for their links (README
Gaps 26, track A).

`+laze-to-inter1` has the shape of `+lazy-to-inter1` (`shapecoll2i.py`)
without `+need-to-ordered`: its body is `[7 [0 1] [6 TEST YES NO]]` with

    NO = [8 ROLL [9 2 [10 [6 [0 59] [7 [0 3] [8 TURN
           [8 [[[1 0] LZB] [0 28] [0 2]] [[1 BG] [0 1]]]]]] [0 2]]]]

`TURN` the `+turn` over `fork.laz` (gate `TG`, sample bunt `TB`), `LZB` the
bunt of `laze` (arm `0xaebde` of `K`, at axis `15`) and `BG` the gate of the
`+roll` over `bond.laz`.  `+laze-collapse` is `+shape-collapse` with arm
`5598` in place of `6006`.  `+laze-may` is

    [8 INTR [8 [1 TRAP] [9 2 0 1]]]
    TRAP = [8 ROLL [9 2 [10 [6 [0 29] [7 [0 3] [8 [[B B] [0 12]] [[1 GATE] [0 1]]]]]] [0 2]]]]

`INTR` the push of `(inter1-to-inter2 (laze-to-inter1 laz) less)`, `B` the
bunt of `need-inter2` (arm `0x575f` of `K`, at axis `31`), `GATE` the gate of
the `+roll` over `fork.intr`, which runs `TRAP` again at axis `7` of its
subject on both branches.

    tools/capped.sh -m 3G python3 tools/gen/runshapecoll.py OUTDIR

writes `OUTDIR/runshapecoll.lean` and `OUTDIR/runshapemay.lean`."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
K = ('C', ('R', 'nh290d8f32435a'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))


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

# +laze-may
mBunt, mBody, mHint = gate(0x2eeeb)
_, mIntr, m1 = seq(mBody, 3)         # [8 INTR M1]
_, mtq, m9 = seq(m1, 3)              # [8 [1 TRAP] [9 2 0 1]]
assert show(m9, names=False) == '[9 2 0 1]', show(m9, names=False)
mTrap = norm(norm(mtq)[2])
_, mroll, mslam = seq(mTrap, 3)
assert show(mroll, names=False) == '[9 0x2fbdfc 0 0xfffff]', show(mroll, names=False)
_, _, m10 = seq(mslam, 3)
_, m6, _ = seq(m10, 3)
msam = norm(norm(m6)[2])             # [[0 29] [7 [0 3] [8 SMP [[1 GATE] [0 1]]]]]
assert show(slot(2, msam), names=False) == '[0 29]'
mmk = norm(slot(7, norm(slot(3, msam))))
assert norm(slot(2, mmk)) == ('A', 8)
msmp = norm(slot(6, mmk))
mB = norm(slot(4, msmp))
assert eqn(slot(5, msmp), mB)
assert show(slot(3, msmp), names=False) == '[0 12]'
assert show(slot(15, mmk), names=False) == '[0 1]'
mGate = norm(slot(29, mmk))
assert show(slot(28, mmk), names=False) == '1'
mdefs = [
    ('lmyB', mB, 'The bunt of `need-inter2` in the sample of the gate of the `+roll` (arm `0x575f` of `K`, at axis `31`).'),
    ('lmyGate', mGate, 'The gate of the `+roll` over `fork.intr`: `(uni-need-ord (uni-need-ord acc ^$(intr y)) ^$(intr n))`.'),
    ('lmyTrap', mTrap, 'The trap of `+laze-may`: the `+roll` over `fork.intr` from `sure.intr`.'),
    ('lmyBody', mBody, 'The gate body of `+laze-may`.'),
    ('lmyBunt', mBunt, 'Its sample bunt.'),
    ('lmyHint', mHint, 'Its `%fast` hint.'),
]
with open(os.path.join(OUT, 'runshapemay.lean'), 'w') as f:
    emit(f, mdefs)
