"""Cut the case `%11` of `+run` (door axis 18011890248581118) into named
parts (README Gaps 25).

    tools/capped.sh -m 3G python3 tools/gen/runhint.py OUTDIR

The body is `[6 T ST DY]`: `T` the test `?@  p.nomm`, `ST` the atom tag
`[6 TS KEPT REC]` (`TS` the test `?=(hint-static p.nomm)`, `KEPT` the kept
static tag, `REC` the recursion `$(nomm q.nomm)`), `DY` the cell tag
`[6 TD DKEPT NDYN]`.  Writes `OUTDIR/k11.lean` with the parts that are
written out and the others read from the pill as `(slot? k comp.door).getD
(A 0)`, so that `crK11 = cr11Head` is a `kernel_rfl` fact.  Every shape is
asserted."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'

def comp(a, b):
    k = b.bit_length() - 1
    return (a << k) | (b - (1 << k))

def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    return ('C', full(n[1]), full(n[2]))

def sl(ax, n):
    for b in bin(ax)[3:]:
        assert n[0] == 'C', ax
        n = n[1] if b == '0' else n[2]
    return n

def cells(n):
    return 0 if n[0] == 'A' else 1 + cells(n[1]) + cells(n[2])

def show(n):
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1]), show(n[2]))

def A(v): return ('A', v)
def C(a, b): return ('C', a, b)

AK11 = 18011890248581118
door = ('R', 'comp.door')
K = full(slot(AK11, door))
assert cells(K) == 823, cells(K)
assert sl(2, K) == A(6)
T = sl(6, K)
assert T == C(A(6), C(C(A(3), C(A(0), A(234))), C(C(A(1), A(1)), C(A(1), A(0))))), T
ST = sl(14, K)
assert sl(2, ST) == A(6)
TS = sl(6, ST)
XRAY, BOUT = 0x79617278, 0x74756f62
assert TS == C(A(6), C(C(A(5), C(C(A(1), A(XRAY)), C(A(0), A(234)))),
                C(C(A(1), A(0)), C(A(5), C(C(A(1), A(BOUT)), C(A(0), A(234))))))), TS
REC = sl(15, ST)
assert REC == C(A(9), C(A(5), C(A(10), C(C(A(58), C(A(0), A(470))), C(A(0), A(1)))))), REC
assert cells(sl(14, ST)) == 245
DY = sl(15, K)
assert sl(2, DY) == A(6)
TD = sl(6, DY)
assert cells(sl(14, DY)) == 325 and cells(sl(15, DY)) == 134
AKEPT, ADKEPT, ANDYN = comp(AK11, 118), comp(AK11, 126), comp(AK11, 127)
for a, b in [(118, AKEPT), (126, ADKEPT), (127, ANDYN)]:
    assert full(slot(b, door)) == sl(a, K), a
defs = [
    'def cr11T : Noun :=\n  ' + show(T),
    'def cr11TS : Noun :=\n  ' + show(TS),
    'def cr11Rec : Noun :=\n  ' + show(REC),
    'def cr11Kept : Noun := (slot? %d comp.door).getD (A 0)' % AKEPT,
    'def cr11St : Noun := C (A 6) (C cr11TS (C cr11Kept cr11Rec))',
    'def cr11TD : Noun :=\n  ' + show(TD),
    'def cr11DKept : Noun := (slot? %d comp.door).getD (A 0)' % ADKEPT,
    'def cr11NDyn : Noun := (slot? %d comp.door).getD (A 0)' % ANDYN,
    'def cr11Dy : Noun := C (A 6) (C cr11TD (C cr11DKept cr11NDyn))',
    'def cr11Head : Noun := C (A 6) (C cr11T (C cr11St cr11Dy))',
]
open(os.path.join(OUT, 'k11.lean'), 'w').write('\n\n'.join(defs) + '\n')
print('kept', AKEPT, 'dkept', ADKEPT, 'ndyn', ANDYN)
