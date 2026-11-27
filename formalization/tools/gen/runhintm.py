"""The case `%mean` of `+run` (README Gaps 25): `crKmean` (door axis
144095121988648958, 577 cells) and `+mean-konst` (door axis 252, 47 cells).

    tools/capped.sh -m 3G python3 tools/gen/runhintm.py [OUTDIR]

OUTDIR defaults to the scratch directory of track Q.  Writes `OUTDIR/kmean.lean`:
* `mkBat`, `mkArm`: `+mean-konst` is `[8 [1 BUNT] [1 mkBat] 0 1]`, `mkBat`
  `[6 [5 [1 0] [0 13]] [1 0] [6 mkPure [0 13] [1 0]]]` (`?~  k  ~`, then
  `?.  pure:(~(got by code.long-ska) b)  ~  k`), `mkPure` `[7 GOT [0 6]]`;
* `cmKonst`, `cmTest`, `cmYes`, `cmHead`: `crKmean` is `[8 cmKonst [6 cmTest
  cmYes NO]]` (`=/  konst  (mean-konst b.nomm k.nomm)`, `?:  &(mono ?=(~
  konst))`, `$(nomm [%11 [%mean p] q body])`);
* `cmN11`, `cmN10`, `cmN7`, `cmN5`, `cmN4`, `cmNo`: NO from the run of `p`, from
  the push of `nex-arg`, from the run of `q`, from `+past-if`, from
  `+simple-next`, and whole.  Its pushes (`=^` unless said): `b-ned`,
  `sub-ned` (`+need-ord-alloc-regs`), `=/ sub-v` (`+flatten-need`), `=/
  [prol-op epil-op]`, `+simple-next`, `+past-if`, `+emit` (epilogue), `$` of
  `q`, `+lazy-bound`, `+emit` (prologue), `nex-arg`, `$` of `p`, then `+copy`.
Each later part is named inside the earlier ones.  Every shape is asserted."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot
from runhintk import sl, cells, show, full, A, C, comp, door, after_push, SCRATCH
OUT = sys.argv[1] if len(sys.argv) > 1 else SCRATCH

AM = 144095121988648958
M = full(slot(AM, door))
assert cells(M) == 577
assert sl(2, M) == A(8)
KON = sl(6, M)
assert KON == C(A(8), C(C(A(9), C(A(380), C(A(0), A(15)))), C(A(9), C(A(2), C(A(10), C(C(A(6), C(C(A(0), A(982)),
    C(A(0), A(3935)))), C(A(0), A(2))))))))
assert comp(2, 252) == 380
B = sl(7, M)
assert sl(2, B) == A(6)
TEST, YES, NO = sl(6, B), sl(14, B), sl(15, B)
assert TEST == C(A(6), C(C(A(0), A(60)), C(C(A(6), C(C(A(5), C(C(A(1), A(0)), C(A(0), A(2)))), C(C(A(1), A(0)),
    C(A(1), A(1))))), C(A(1), A(1)))))
MEAN = 0x6e61656d
assert YES == C(A(9), C(A(5), C(A(10), C(C(A(58), C(C(A(1), A(11)), C(C(C(A(1), A(MEAN)), C(A(0), A(490))),
    C(C(A(0), A(1966)), C(A(0), A(3934)))))), C(A(0), A(3))))))
assert cells(YES) == 15 and cells(NO) == 529
# +mean-konst
MK = full(slot(252, door))
assert cells(MK) == 47
assert sl(2, MK) == A(8) and sl(12, MK) == A(1) and sl(28, MK) == A(1) and sl(15, MK) == C(A(0), A(1))
MKBUNT, MKBAT = sl(13, MK), sl(29, MK)
assert MKBUNT == C(C(C(A(1), A(0)), C(A(0), A(0))), A(0))
assert sl(2, MKBAT) == A(6) and sl(6, MKBAT) == C(A(5), C(C(A(1), A(0)), C(A(0), A(13))))
assert sl(14, MKBAT) == C(A(1), A(0))
MKR = sl(15, MKBAT)
assert sl(2, MKR) == A(6) and sl(7, MKR) == C(C(A(0), A(13)), C(A(1), A(0)))
MKPURE = sl(6, MKR)
assert MKPURE == C(A(7), C(C(A(8), C(C(A(8), C(C(A(9), C(A(6103), C(A(0), A(0x3fffff)))), C(A(9), C(A(701),
    C(A(10), C(C(A(6), C(A(0), A(2036))), C(A(0), A(2)))))))), C(A(9), C(A(2), C(A(10), C(C(A(6), C(A(0), A(28))),
    C(A(0), A(2)))))))), C(A(0), A(6))))
# NO, cut at its pushes
def push_eq(n):
    """`[7 [0 1] [8 X [7 E [7 F REST]]]]` -> (X, REST)"""
    return after_push(n)
def push_ts(n):
    """`[8 X REST]` (one `=/`) -> (X, REST)"""
    assert sl(2, n) == A(8)
    return sl(6, n), sl(7, n)
kinds = ['^', '^', '/', '/', '^', '^', '^', '^', '^', '^', '^', '^']
parts = []
cur = NO
for kd in kinds:
    x, r = push_eq(cur) if kd == '^' else push_ts(cur)
    parts.append((x, cur))
    cur = r
LAST = cur
# the pushes
X = [p[0] for p in parts]
assert X[0] == C(A(7), C(C(A(0), A(1)), C(A(6), C(C(A(6), C(C(A(3), C(A(0), A(2))), C(C(A(1), A(1)), C(A(1), A(0))))),
    C(C(A(8), C(C(A(9), C(A(0x55ffc), C(A(0), A(31)))), C(A(9), C(A(2), C(A(10), C(C(A(6), C(A(0), A(2006))),
    C(A(0), A(2)))))))), C(C(A(1), C(A(0x656e6f6e), A(0))), C(A(0), A(126))))))))
assert X[1] == C(A(7), C(C(A(0), A(1)), C(A(8), C(C(A(9), C(A(comp(2, 446)), C(A(0), A(63)))), C(A(9), C(A(2),
    C(A(10), C(C(A(6), C(A(0), A(6))), C(A(0), A(2))))))))))
assert X[2] == C(A(8), C(C(A(9), C(A(comp(2, 220)), C(A(0), A(127)))), C(A(9), C(A(2), C(A(10), C(C(A(6),
    C(A(0), A(6))), C(A(0), A(2))))))))
assert cells(X[3]) == 36
assert X[4] == C(A(7), C(C(A(0), A(1)), C(A(9), C(A(4), C(A(0), A(63))))))
assert sl(30, X[5]) == C(A(9), C(A(comp(2, 882366)), C(A(0), A(1023))))
assert sl(30, X[8]) == C(A(9), C(A(comp(2, 884726)), C(A(0), A(8191))))
assert cells(X[10]) == 109
assert X[11] == C(A(7), C(C(A(0), A(1)), C(A(9), C(A(5), C(A(10), C(C(A(118), C(A(0), A(2))), C(A(10), C(C(A(58),
    C(A(0), A(0xfffea))), C(A(0), A(8191))))))))))
assert LAST == C(A(8), C(C(A(9), C(A(comp(2, 220590)), C(A(0), A(0x1ffff)))), C(A(9), C(A(2), C(A(10), C(C(A(6),
    C(C(A(0), A(6)), C(A(0), A(250)))), C(A(0), A(2))))))))
defs = [
    'def mkPure : Noun :=\n  ' + show(MKPURE, {}),
    'def mkBat : Noun := C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 1) (A 0)) (C (A 6) (C mkPure (C (C (A 0) (A 13)) (C (A 1) (A 0)))))))',
    'def mkArm : Noun := C (A 8) (C (C (A 1) ' + show(MKBUNT, {}) + ') (C (C (A 1) mkBat) (C (A 0) (A 1))))',
    'def cmKonst : Noun :=\n  ' + show(KON, {}),
    'def cmTest : Noun :=\n  ' + show(TEST, {}),
    'def cmYes : Noun :=\n  ' + show(YES, {}),
    'def cmN11 : Noun :=\n  ' + show(parts[11][1], {}),
    'def cmN10 : Noun :=\n  ' + show(parts[10][1], {id(parts[11][1]): 'cmN11'}),
    'def cmN7 : Noun :=\n  ' + show(parts[7][1], {id(parts[10][1]): 'cmN10'}),
    'def cmN5 : Noun :=\n  ' + show(parts[5][1], {id(parts[7][1]): 'cmN7'}),
    'def cmN4 : Noun :=\n  ' + show(parts[4][1], {id(parts[5][1]): 'cmN5'}),
    'def cmNo : Noun :=\n  ' + show(NO, {id(parts[4][1]): 'cmN4'}),
    'def cmHead : Noun := C (A 8) (C cmKonst (C (A 6) (C cmTest (C cmYes cmNo))))',
]
open(os.path.join(OUT, 'kmean.lean'), 'w').write('\n\n'.join(defs) + '\n')
for i, x in enumerate(X):
    print('push', i, kinds[i], cells(x), show(x, {})[:300])
print('nex-arg', show(X[10], {}))
print('ops', show(X[3], {}))
