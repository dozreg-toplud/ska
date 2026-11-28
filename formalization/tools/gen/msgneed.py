"""The nouns of `+msg-need-ord` (arm `20` of `K`): the sample bunt, the
`%fast` hint and the gate body cut into its first test, as Lean
definitions.

    tools/capped.sh -m 3G python3 tools/gen/msgneed.py OUTDIR

writes `OUTDIR/msgneed.lean`.  The body is `[7 [0 1] [6 [5 [0 12] [0 26]]
[0 12] REST]]`: `?:  =(a b)  a`, the rest (`msgRest`) under a `~+` memo
hint."""
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


arm = slot(20, K)
_, core, hint = seq(arm, 3)
_, bunt, b = seq(core, 3)
body = norm(norm(b[1])[2])
_, _, b1 = seq(body, 3)              # [7 [0 1] B1]
_, test, yes, rest = seq(b1, 4)      # [6 T [0 12] REST]
assert show(test, names=False) == '[5 [0 12] 0 26]', show(test, names=False)
assert show(yes, names=False) == '[0 12]'
with open(os.path.join(OUT, 'msgneed.lean'), 'w') as f:
    emit(f, [
        ('msgRest', rest, 'The branches of `+msg-need-ord` after `?:  =(a b)  a`.'),
        ('msgBody', body, 'The gate body of `+msg-need-ord`.'),
        ('msgBunt', norm(bunt)[2], 'Its sample bunt.'),
        ('msgHint', hint, 'Its `%fast` hint.'),
    ])
print('ok')
