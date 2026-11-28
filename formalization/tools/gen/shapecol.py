"""The nouns of `+shape-collapse` (arm `682` of `K`) and of the arms it runs
on a fork-free lazy need, cut into named parts, as Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/shapecol.py OUTDIR

writes `OUTDIR/shapecol.lean`: for each of `+uni-need-ord` (`2794`, `uno`),
`+lazy-to-inter1` (`6006`, `l2i`), `+inter2-fix-round` (`0x15d7bf`, `fr`),
`+inter2-orig` (`1367`, `oi`), `+inter2-collapse` (`1406`, `ic`) and
`+shape-collapse` (`682`, `sc`), the sample bunt, the gate body and the
`%fast` hint of its arm `[7 [8 [1 BUNT] [1 BODY] 0 1] HINT]`, and the parts
of the bodies that the proofs keep folded."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
K = ('C', ('R', 'nh290d8f32435a'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))


def seq(n, k):
    """[a b c ... z] as a list of k elements, the last the rest."""
    out = []
    n = norm(n)
    for _ in range(k - 1):
        assert n[0] == 'C', n
        out.append(norm(n[1]))
        n = norm(n[2])
    out.append(n)
    return out


def emit(f, defs):
    """defs: list of (name, noun, doc), smallest first; later ones name
    the earlier ones."""
    subs = []
    for name, n, doc in defs:
        if doc is not False:
            if doc:
                f.write('/-- %s -/\n' % doc)
            f.write('def %s : Noun :=\n  %s\n\n' % (name, lean(n, subs)))
        subs.insert(0, (name, n))


def gate(ax):
    arm = slot(ax, K)
    _, core, hint = seq(arm, 3)
    _, bunt, b = seq(core, 3)
    assert norm(bunt)[1] == ('A', 1)
    body = norm(norm(b[1])[2])
    return norm(bunt)[2], body, hint


defs = []
# +uni-need-ord
uBunt, uBody, uHint = gate(2794)
_, _, _, u1 = seq(uBody, 4)          # [6 T [0 12] U1]
_, _, _, unoRest = seq(u1, 4)        # [6 T [0 13] REST]
defs += [
    ('unoRest', unoRest, 'The branches of `+uni-need-ord` after `?:  ?=(%none -.a)  b`.'),
    ('unoBody', uBody, 'The gate body of `+uni-need-ord`.'),
    ('unoBunt', uBunt, 'Its sample bunt.'),
    ('unoHint', uHint, 'Its `%fast` hint.'),
]
# +lazy-to-inter1
lBunt, lBody, lHint = gate(6006)
_, _, l1 = seq(lBody, 3)             # [7 [0 1] L1]
_, _, l2iYes, l2iNo = seq(l1, 4)
defs += [
    ('l2iYes', l2iYes, '`[[(need-to-ordered ned.sure.laz) lok.sure.laz] ~]`.'),
    ('l2iNo', l2iNo, 'The `+roll` over the bonds, with forks or bonds.'),
    ('l2iBody', lBody, 'The gate body of `+lazy-to-inter1`.'),
    ('l2iBunt', lBunt, 'Its sample bunt.'),
    ('l2iHint', lHint, 'Its `%fast` hint.'),
]
# +inter2-fix-round
fBunt, fBody, fHint = gate(0x15d7bf)
_, _, f1 = seq(fBody, 3)             # [8 [1 none] F1]
_, trapq, _ = seq(f1, 3)             # [8 [1 TRAP] [9 2 0 1]]
frTrap = norm(norm(trapq)[2])
_, _, t1 = seq(frTrap, 3)            # [7 [0 1] T1]
_, frUni, t2 = seq(t1, 3)            # [7 [10 [6 UNI] 0 1] T2]
_, frTurn, t3 = seq(t2, 3)           # [8 TURN [ROLL [0 2]]]
frRoll = norm(t3[1])
_, _, rslam = seq(frRoll, 3)         # [8 ARM [9 2 [10 [6 SAM] 0 2]]]
_, _, r10 = seq(rslam, 3)
_, r6, _ = seq(r10, 3)
rsam = norm(norm(r6)[2])             # [[0 6] [7 [0 3] [8 BUNT [[1 GATE] [0 1]]]]]
_, _, rmk = seq(norm(rsam[2]), 3)
_, frRBunt, rpair = seq(rmk, 3)
frGate = norm(norm(norm(rpair[1])[2]))
frBuntF = norm(norm(norm(frRBunt[1]))[1])
defs += [
    ('frBuntF', frBuntF, 'The bunt of `need-inter2`, from the mold at arm `0x575f` of `K` (axis `63`).'),
    ('frGate', frGate, 'The gate of the `+roll` over `kids`.'),
    ('frRBunt', frRBunt, 'Its sample bunt: two bunts of `need-inter2` and `parent`.'),
    ('frUni', frUni, '`=.  parent  (uni-need-ord parent sure.prev)`.'),
    ('frTurn', frTurn, '`kids`: the `+turn` over `fork.prev`.'),
    ('frRoll', frRoll, 'The `+roll` over `kids` from `parent`.'),
    ('frTrap', frTrap, 'The trap `round` of `+inter2-fix-round`.'),
    ('frBody', fBody, 'The gate body of `+inter2-fix-round`.'),
    ('frBunt', fBunt, 'Its sample bunt.'),
    ('frHint', fHint, 'Its `%fast` hint.'),
]
# +inter2-orig
oBunt, oBody, oHint = gate(1367)
o = seq(oBody, 3)[2]                 # [7 [0 1] O]
o = seq(o, 3)[2]                     # [8 [0 24] O]
o = seq(o, 3)[2]                     # [8 [0 57] O]
o = seq(o, 3)[2]                     # [8 [0 245] O]
_, otq, _ = seq(o, 3)                # [8 [1 TRAP] [9 2 0 1]]
oiTrap = norm(norm(otq)[2])
_, _, _, ot1 = seq(oiTrap, 4)        # [6 T [0 30] OT1]
_, _, oiFork, _ = seq(ot1, 4)        # [6 [3 0 6] FORK [0 0]]
defs += [
    ('oiFork', oiFork, 'The step of the loop of `+inter2-orig` on a fork.'),
    ('oiTrap', oiTrap, 'The loop of `+inter2-orig` over `forks` and `fixes`.'),
    ('oiBody', oBody, 'The gate body of `+inter2-orig`.'),
    ('oiBunt', oBunt, 'Its sample bunt.'),
    ('oiHint', oHint, 'Its `%fast` hint.'),
]
# +inter2-collapse
cBunt, cBody, cHint = gate(1406)
_, _, c1 = seq(cBody, 3)             # [8 [0 12] C1]
_, c10, _ = seq(c1, 3)               # [7 [10 [2 FIX] 0 1] ORIG]
_, c10a, _ = seq(c10, 3)             # [10 [2 FIX] [0 1]]
fixl = norm(norm(c10a)[2])           # [8 [1 TRAP] [9 2 0 1]]
_, ctq, _ = seq(fixl, 3)
icTrap = norm(norm(ctq)[2])
defs += [
    ('icTrap', icTrap, 'The fixed point loop of `+inter2-collapse`.'),
    ('icBody', cBody, 'The gate body of `+inter2-collapse`.'),
    ('icBunt', cBunt, 'Its sample bunt.'),
    ('icHint', cHint, 'Its `%fast` hint.'),
]
# +shape-collapse
sBunt, sBody, sHint = gate(682)
defs += [
    ('scBodyN', sBody, 'The gate body of `+shape-collapse`.'),
]
with open(os.path.join(OUT, 'shapecol.lean'), 'w') as f:
    emit(f, defs)
print('ok')
