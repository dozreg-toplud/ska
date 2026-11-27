#!/usr/bin/env python3
"""The case `%12` of `+run` (README Gaps 25): `crLast` (door axis
144095121988648959, 318 cells) is `[11 [tag CLUE] BODY]`, a hint whose clue
`CLUE` tests the nomm (`[6 [3 0 58] [5 [1 12] 0 116] [1 1]]`, it never
crashes) around `BODY` (305 cells), which has the pushes of the indirect call
(`tools/gen/runtwo.py`): `+simple-next`, `+kerf`, two `+re`, `+emit` of the
block `[%spy r-ref r-path pro]`, `$` of `q` under `(lazy-from-reg r-path)`,
`+past`, `$` of `p` under `(lazy-from-reg r-ref)`, `+copy`.

    tools/capped.sh -m 3G python3 tools/gen/runhint12.py [OUTDIR]

Writes `OUTDIR/k12.lean`: `c12Clue`, `c12T3`, `c12T2`, `c12Tail`, `c12Kf`,
`c12Ind`, `c12Head`, each later part named inside the earlier ones, so that
`crLast = c12Head` is a `kernel_rfl` fact.  The pushes that are the indirect
call's (`+simple-next`, `+kerf`, the two `+re`, `+past`, `+copy`) are
asserted equal to its; the others are asserted by shape."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from runhintk import full, sl, cells, show, A, C, pushes, slot, door, comp, SCRATCH
OUT = sys.argv[1] if len(sys.argv) > 1 else SCRATCH
L = full(slot(144095121988648959, door))
assert cells(L) == 318
assert sl(2, L) == A(11)
TAG = sl(12, L)
assert TAG == A(0x73736f74), TAG
CLUE = sl(13, L)
assert CLUE == C(A(6), C(C(A(3), C(A(0), A(58))), C(C(A(5), C(C(A(1), A(12)), C(A(0), A(116)))), C(A(1), A(1))))), CLUE
B = sl(7, L)
assert cells(B) == 305
IND = sl(14, full(slot(8588738558, door)))
bp, blast = pushes(B, 8)
ip, ilast = pushes(IND, 8)
for i in [0, 1, 2, 3, 6]:
    assert bp[i][0] == ip[i][0], i
assert blast == ilast
# the %spy block: [%spy r-ref r-path pro] (r-ref the second +re, at 2; r-path at 6)
assert show(bp[4][0], {}) == show(ip[4][0], {}).replace(
    '(C (C (A 1) (A 0x6b6f6e)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 29)))))',
    '(C (C (A 1) (A 0x797073)) (C (C (A 0) (A 2)) (C (C (A 0) (A 6)) (C (A 0) (A 29)))))')
# the runs of q and p under (lazy-from-reg r): arm 92 of K at 0xffff/0x3fff on the register
for k, reg, ax in [(5, 30, 0x3fff), (7, 62, 0xffff)]:
    s = show(bp[k][0], {})
    assert '(C (A 9) (C (A 92) (C (A 0) (A %s))))' % hex(ax) in s, (k, s[:300])
    assert '(C (C (A 6) (C (A 0) (A %d))) (C (A 0) (A 2)))' % reg in s, (k, s[:300])
defs = [
    'def c12Clue : Noun :=\n  ' + show(CLUE, {}),
    'def c12T3 : Noun :=\n  ' + show(bp[7][1], {}),
    'def c12T2 : Noun :=\n  ' + show(bp[6][1], {id(bp[7][1]): 'c12T3'}),
    'def c12Tail : Noun :=\n  ' + show(bp[5][1], {id(bp[6][1]): 'c12T2'}),
    'def c12Kf : Noun :=\n  ' + show(bp[1][1], {id(bp[5][1]): 'c12Tail'}),
    'def c12Ind : Noun :=\n  ' + show(B, {id(bp[1][1]): 'c12Kf'}),
    'def c12Head : Noun := C (A 11) (C (C (A 0x73736f74) c12Clue) c12Ind)',
]
open(os.path.join(OUT, 'k12.lean'), 'w').write('\n\n'.join(defs) + '\n')
print('wrote', os.path.join(OUT, 'k12.lean'))
