"""The kept hints of the case `%11` of `+run` (README Gaps 25): `+past-if`
(door axis 882366) and the kept static and dynamic branches cut at their
`=^` pushes.

    tools/capped.sh -m 3G python3 tools/gen/runhintk.py [OUTDIR]

OUTDIR defaults to the scratch directory of track Q.  Writes
`OUTDIR/k11k.lean`:
* `piLok`, `piSnd`, `piRest`, `piBat`, `piArm`: `+past-if` is
  `[8 [1 BUNT] [1 piBat] 0 1]` with `piBat = [6 [6 piLok piSnd [1 1]] [[0 12]
  [0 30]] piRest]` (the test of the lock, then `+sound`, else the `%hop`
  block, `+set-tag` and the bond);
* `ckP3`, `ckP1`, `ckHead`: the kept static branch (`cr11Kept`) from the run
  of `q`, from `+past-if`, and whole (pushes: `+simple-next`, `+past-if`,
  `+emit`, `$` of `q`, `+lazy-bound`, `+emit`, then the result);
* `cdP7`, `cdP4`, `cdP1`, `cdHead`: the kept dynamic branch (`cr11DKept`)
  from the run of `h`, from the run of `q`, from `+past-if`, and whole
  (pushes: `+simple-next`, `+past-if`, `+re`, `+emit`, `$` of `q`,
  `+lazy-bound`, `+emit`, `$` of `h`, then `+copy`).
Each later part is named inside the earlier ones, so that `cr11Kept =
ckHead` and `cr11DKept = cdHead` are `kernel_rfl` facts.  Every shape is
asserted."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm
SCRATCH = '/tmp/claude-1000/-home-kirill-work-ska-scratch-wt-ska-formalization/f82d372f-f0b4-4933-9658-7b962d5dfef8/scratchpad/track-q'
OUT = sys.argv[1] if len(sys.argv) > 1 else SCRATCH

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

def show(n, subs):
    if id(n) in subs:
        return subs[id(n)]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1], subs), show(n[2], subs))

def A(v): return ('A', v)
def C(a, b): return ('C', a, b)

def after_push(n):
    """`[7 [0 1] [8 X [7 E [7 F REST]]]]` (one `=^`) -> (X, REST)."""
    assert sl(2, n) == A(7) and sl(6, n) == C(A(0), A(1))
    e8 = sl(7, n)
    assert sl(2, e8) == A(8)
    X = sl(6, e8)
    r = sl(7, e8)
    assert sl(2, r) == A(7) and sl(2, sl(6, r)) == A(10)
    assert sl(2, sl(7, r)) == A(7) and sl(6, sl(7, r)) == C(C(A(0), A(4)), C(A(0), A(3)))
    return X, sl(7, sl(7, r))

def pushes(n, k):
    parts = []
    cur = n
    for i in range(k):
        x, r = after_push(cur)
        parts.append((x, cur))
        cur = r
    return parts, cur

door = ('R', 'comp.door')
NEXT = 0x7478656e
# +past-if
PI = full(slot(882366, door))
assert cells(PI) == 188, cells(PI)
assert sl(2, PI) == A(8) and sl(12, PI) == A(1) and sl(28, PI) == A(1) and sl(15, PI) == C(A(0), A(1))
BUNT = sl(13, PI)
assert BUNT == C(C(A(NEXT), C(C(C(C(A(0x656e6f6e), A(0)), A(0)), C(A(0), A(0))), C(A(0), A(0)))), C(C(A(0), A(0)), A(0)))
PB = sl(29, PI)
assert sl(2, PB) == A(6) and sl(14, PB) == C(C(A(0), A(12)), C(A(0), A(30)))
PT = sl(6, PB)
assert sl(2, PT) == A(6) and sl(15, PT) == C(A(1), A(1))
LOK, SND, REST = sl(6, PT), sl(14, PT), sl(15, PB)
# the slam of +sound (door arm 13654, at 21846 of the core at 7) on [nom (need-to-ordered ned)]
assert sl(2, SND) == A(6) and sl(7, SND) == C(C(A(1), A(0)), C(A(1), A(1)))
SL = sl(6, SND)
assert sl(6, SL) == C(A(9), C(A(comp(2, 13654)), C(A(0), A(7))))
assert sl(253, SL) == C(C(A(0), A(58)), C(A(7), C(C(A(0), A(3)), C(A(8), C(C(A(9), C(A(44732), C(A(0), A(127)))),
    C(A(9), C(A(2), C(A(10), C(C(A(6), C(A(0), A(456))), C(A(0), A(2))))))))))), sl(253, SL)
# kept static
AK11 = 18011890248581118
KEPT = full(slot(comp(AK11, 118), door))
assert cells(KEPT) == 245
kp, klast = pushes(KEPT, 6)
assert klast == C(C(C(A(1), A(NEXT)), C(C(A(0), A(26)), C(C(A(1), A(0)), C(A(0), A(2))))), C(A(0), A(4094))), klast
assert kp[0][0] == C(A(7), C(C(A(0), A(1)), C(A(9), C(A(4), C(A(0), A(1))))))
assert sl(30, kp[1][0]) == C(A(9), C(A(comp(2, 882366)), C(A(0), A(31))))
assert sl(30, kp[4][0]) == C(A(9), C(A(comp(2, 884726)), C(A(0), A(255))))
DKEPT = full(slot(comp(AK11, 126), door))
assert cells(DKEPT) == 325
dp, dlast = pushes(DKEPT, 8)
assert dp[0][0] == kp[0][0] and dp[1][0] == kp[1][0]
assert dp[2][0] == C(A(7), C(C(A(0), A(1)), C(A(9), C(A(comp(2, 3538943)), C(A(0), A(63))))))
assert sl(30, dp[5][0]) == C(A(9), C(A(comp(2, 884726)), C(A(0), A(511))))
assert sl(2, dlast) == A(8) and sl(6, dlast) == C(A(9), C(A(comp(2, 220590)), C(A(0), A(4095)))), dlast
defs = [
    'def piLok : Noun :=\n  ' + show(LOK, {}),
    'def piSnd : Noun :=\n  ' + show(SND, {}),
    'def piRest : Noun :=\n  ' + show(REST, {}),
    'def piBat : Noun := C (A 6) (C (C (A 6) (C piLok (C piSnd (C (A 1) (A 1))))) (C (C (C (A 0) (A 12)) (C (A 0) (A 30))) piRest))',
    'def piArm : Noun := C (A 8) (C (C (A 1) ' + show(BUNT, {}) + ') (C (C (A 1) piBat) (C (A 0) (A 1))))',
    'def ckP3 : Noun :=\n  ' + show(kp[3][1], {}),
    'def ckP1 : Noun :=\n  ' + show(kp[1][1], {id(kp[3][1]): 'ckP3'}),
    'def ckHead : Noun :=\n  ' + show(KEPT, {id(kp[1][1]): 'ckP1'}),
    'def cdP7 : Noun :=\n  ' + show(dp[7][1], {}),
    'def cdP4 : Noun :=\n  ' + show(dp[4][1], {id(dp[7][1]): 'cdP7'}),
    'def cdP1 : Noun :=\n  ' + show(dp[1][1], {id(dp[4][1]): 'cdP4'}),
    'def cdHead : Noun :=\n  ' + show(DKEPT, {id(dp[1][1]): 'cdP1'}),
]
open(os.path.join(OUT, 'k11k.lean'), 'w').write('\n\n'.join(defs) + '\n')
for i, (x, c) in enumerate(kp):
    print('kept push', i, show(x, {})[:200])
for i, (x, c) in enumerate(dp):
    print('dkept push', i, show(x, {})[:200])
print('dlast', show(dlast, {}))
