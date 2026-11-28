"""The nouns of `+msg-need-ord` (arm `20` of `K`) cut into its branches, and
of the arms it and `+msg-need-ord-fix-aware` (`1502`) call: `+need-ord-regs`
(`1396`), `split-max` (`0x5dd6`), `+hed-need-ord` (`374`), `+tel-need-ord`
(`92`), as Lean definitions (README Gaps 9).

    tools/capped.sh -m 3G python3 tools/gen/shapecolmsg.py OUTDIR

writes `OUTDIR/shapecolmsg.lean`.  `msgRest` (of `CompMemOld.lean`) is
`[11 [%memo 1 0] [6 T1 [1 this 0] [6 T2 [1 this 0] [6 OR4 ONE CELLS]]]]`:
both sides `%this`/`%none`; `less` an atom and one side `%this`/`%none`;
one side `%this`/`%none` (`ONE`: seven pushes); both sides cells or `%both`
(`CELLS`: four branches)."""
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
    subs = []
    for name, n, doc in defs:
        if doc is not False:
            if doc:
                f.write('/-- %s -/\n' % doc)
            f.write('def %s : Noun :=\n  %s\n\n' % (name, lean(n, subs)))
        subs.insert(0, (name, n))


def plain_gate(ax):
    """[8 [1 BUNT] [1 BODY] 0 1]"""
    arm = norm(slot(ax, K))
    _, bunt, b = seq(arm, 3)
    assert norm(bunt)[1] == ('A', 1)
    body = norm(norm(b[1])[2])
    return norm(bunt)[2], body


defs = []
# +need-ord-regs
rBunt, rBody = plain_gate(1396)
_, _, rb1 = seq(rBody, 3)             # [8 [1 0] RB1]
_, rtq, _ = seq(rb1, 3)               # [8 [1 TRAP] [9 2 0 1]]
norTrap = norm(norm(rtq)[2])
_, _, _, norSw = seq(norTrap, 4)      # [6 GTH [0 6] SWITCH]
defs += [
    ('norSw', norSw, 'The `?-` of the trap of `+need-ord-regs`.'),
    ('norTrap', norTrap, 'The trap of `+need-ord-regs`.'),
    ('norBody', rBody, 'The gate body of `+need-ord-regs`.'),
    ('norBunt', rBunt, 'Its sample bunt.'),
]
# +hed-need-ord, +tel-need-ord
hBunt, hBody = plain_gate(374)
tBunt, tBody = plain_gate(92)
defs += [
    ('honBody', hBody, 'The gate body of `+hed-need-ord`.'),
    ('tonBody', tBody, 'The gate body of `+tel-need-ord`.'),
]
# +msg-need-ord
arm = slot(20, K)
_, core, hint = seq(arm, 3)
_, bunt, b = seq(core, 3)
body = norm(norm(b[1])[2])
_, _, b1 = seq(body, 3)              # [7 [0 1] B1]
_, _, _, rest = seq(b1, 4)           # [6 T [0 12] REST]
_, _, r1 = seq(rest, 3)              # [11 [memo 1 0] R1]
_, t1, y1, r2 = seq(r1, 4)           # [6 T1 [1 this 0] R2]
_, t2, y2, r3 = seq(r2, 4)           # [6 T2 [1 this 0] R3]
_, or4, one, cells = seq(r3, 4)      # [6 OR4 ONE CELLS]
assert show(y1, names=False) == '[1 0x73696874 0]'
assert show(y2, names=False) == '[1 0x73696874 0]'
# ONE: [8 SD [8 HD [8 TD [8 L [8 R [8 RES FIN]]]]]]
_, oSD, o1 = seq(one, 3)
_, oHD, o2 = seq(o1, 3)
_, oTD, o3 = seq(o2, 3)
_, oL, o4 = seq(o3, 3)
_, oR, o5 = seq(o4, 3)
_, oRes, oFin = seq(o5, 3)
_, oGth, _, _ = seq(oFin, 4)         # [6 GTH [1 this 0] [0 2]]
# CELLS: [6 [5 [1 both] 0 24] [6 B52 BB BP] [6 B52 PB PP]]
_, _, cB, cP = seq(cells, 4)
_, _, cBB, cBP = seq(cB, 4)
_, _, cPB, cPP = seq(cP, 4)
defs += [
    ('msgOr4', or4, '`?|(?=(%this -.a) ?=(%none -.a) ?=(%this -.b) ?=(%none -.b))`.'),
    ('msgT1', t1, 'Both sides `%this` or `%none`.'),
    ('msgT2', t2, '`less` an atom and one side `%this` or `%none`.'),
    ('msgSD', oSD, '`[single double]`.'),
    ('msgHD', oHD, '`h-double`.'),
    ('msgTD', oTD, '`t-double`.'),
    ('msgL', oL, '`l`: `(msg none+~ h-double -.less)`.'),
    ('msgR', oR, '`r`: `(msg none+~ t-double +.less)`.'),
    ('msgRes', oRes, '`res`: `[%both l r]` or `(cons-need l r)`.'),
    ('msgGth', oGth, '`(gth (need-ord-regs res split-max) split-max)`.'),
    ('msgFin', oFin, 'The cap on the registers of `res`.'),
    ('msgOneR', o1, 'The case of one side `%this` or `%none` after `[single double]`.'),
    ('msgOneN', one, 'The case of one side `%this` or `%none`, `less` a cell.'),
    ('msgBB', cBB, 'Both `%both`.'),
    ('msgBP', cBP, '`a` `%both`, `b` a cell.'),
    ('msgPB', cPB, '`a` a cell, `b` `%both`.'),
    ('msgPP', cPP, 'Both cells.'),
    ('msgCells', cells, 'The case of both sides cells or `%both`.'),
    ('msgRestN', rest, 'The branches of `+msg-need-ord` after `?:  =(a b)  a`, cut.'),
]
# +msg-need-ord-fix-aware
farm = slot(1502, K)
_, fcore, fhint = seq(farm, 3)
_, fbunt, fb = seq(fcore, 3)
fbody = norm(norm(fb[1])[2])
_, _, f1 = seq(fbody, 3)             # [11 [memo 1 0] F1]
_, _, f2 = seq(f1, 3)                # [7 [0 1] F2]
_, _, _, f3 = seq(f2, 4)             # [6 [5 [0 12] 0 26] [0 12] F3]
_, ft1, fy1, f4 = seq(f3, 4)         # [6 FIX-ATOM MSG F4]
_, ft2, _, f5 = seq(f4, 4)           # [6 A-NONE [0 26] F5]
_, ft3, _, f6 = seq(f5, 4)           # [6 B-NONE [0 12] F6]
_, fHere, f7 = seq(f6, 3)            # [8 HERE F7]
_, fCons, fEnd = seq(f7, 3)          # [8 CONS END]
defs += [
    ('fxMsg', fy1, '`(msg-need-ord a b less)`.'),
    ('fxT2', ft2, '`&(?=(%none -.a) =(b fix))`.'),
    ('fxT3', ft3, '`&(?=(%none -.b) =(a fix))`.'),
    ('fxHere', fHere, '`need-here`.'),
    ('fxCons', fCons, 'The `+cons-need` of the two recursive calls.'),
    ('fxEnd', fEnd, 'The end: `%both`, `%this`, `%none` or the cell.'),
    ('fxRest', f4, 'After the test on `fix`.'),
    ('fxBody', fbody, 'The gate body of `+msg-need-ord-fix-aware`.'),
    ('fxBunt', norm(fbunt)[2], 'Its sample bunt.'),
    ('fxHint', fhint, 'Its `%fast` hint.'),
]
with open(os.path.join(OUT, 'shapecolmsg.lean'), 'w') as f:
    emit(f, defs)
print('ok')
