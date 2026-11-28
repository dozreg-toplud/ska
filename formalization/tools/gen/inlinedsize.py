"""The nouns of `+nomm-size` (arm `0x5ddd5` of `K`), as Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/inlinedsize.py OUTDIR

writes `OUTDIR/nsize.lean`.  The arm is `[8 [1 0 0] [1 BODY] [0 1]]` (a gate
with the bunt `[0 0]`); `BODY` is `[8 [1 0] [8 [1 TRAP] [9 2 0 1]]]` (`=|  n`
and the trap `|-`).  The trap tests `(gth n inline-max)` and then runs the
`?-` over the nomm, one branch per head; the last branch, `%mean`, is under a
`%toss` hint.  Shape asserts check the cut; `inline-max` is arm `0x5ddc`."""
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


arm = norm(slot(0x5ddd5, K))
op8, bunt, gate = seq(arm, 3)
assert op8 == ('A', 8) and eqn(bunt, ('C', ('A', 1), ('C', ('A', 0), ('A', 0))))
q1, body = seq(norm(gate[1]), 2)
assert q1 == ('A', 1) and eqn(gate[2], ('C', ('A', 0), ('A', 1)))
_, n0, b1 = seq(body, 3)
assert eqn(n0, ('C', ('A', 1), ('A', 0)))
_, trq, call = seq(b1, 3)
trap = norm(trq[2])
assert eqn(slot(0x5ddc, K), ('C', ('A', 1), ('A', 48)))
subs = []
with open(os.path.join(OUT, 'nsize.lean'), 'w') as f:
    for name, n, doc in [('nszTrap', trap, 'The trap of `+nomm-size`.'),
                         ('nszBody', body, 'The gate body of `+nomm-size`.')]:
        f.write('/-- %s -/\ndef %s : Noun :=\n  %s\n\n' % (doc, name, lean(n, subs)))
        subs.insert(0, (name, n))
print('ok')
