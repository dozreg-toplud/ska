"""The nouns of the gate body of `+inlined` (arm `0x5dde` of `K`), cut into
named parts, as Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/inlined.py OUTDIR

writes `OUTDIR/inlbody.lean`.  The body is `[7 [0 1] [8 GET [6 T MISS HIT]]]`:
`GET` is `(~(get by inl.cache) b)`, `HIT` returns `[u.n cache]`, and `MISS`
pushes the gate `hot`, takes the nomm of `(~(got by code.long-ska) b)`, tests
`inline-off` (arm `84` of `K`) and runs the trap `|-` over the nomm, then puts
the result into `inl.cache` (`AFTER`).  The trap is a chain of `?-` cases,
one branch per head of the nomm; each branch is named."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
K = ('C', ('R', 'nhe0b859c3d8aa'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))


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

iarm = slot(0x5dde, K)
body = norm(slot(109, iarm))
_, _, b1 = seq(body, 3)            # [7 [0 1] B1]
_, getinl, b2 = seq(b1, 3)         # [8 GET B2]
_, isatom, miss, hit = seq(b2, 4)  # [6 T MISS HIT]
_, hot, m1 = seq(miss, 3)          # [8 HOT M1]
_, inner, after = seq(m1, 3)       # [8 INNER AFTER]
_, gotx, i1 = seq(inner, 3)        # [8 [7 GOT [0 2]] I1]
_, off, offy, trapcall = seq(i1, 4)
_, trapq, call = seq(trapcall, 3)
trap = norm(norm(trapq)[2])
# the chain of cases
names = ['inlBCons', 'inlB0', 'inlB1', 'inlB2', 'inlB3', 'inlB4', 'inlB5', 'inlB6', 'inlB7', 'inlB10',
         'inlB11', 'inlB12']
docs = ['cons', '`%0`', '`%1`', '`%2`', '`%3`', '`%4`', '`%5`', '`%6`', '`%7`', '`%10`', '`%11`', '`%12`']
branches = []
n = trap
for nm in names:
    _, t, y, rest = seq(n, 4)
    branches.append((nm, y))
    n = rest
mean = n
defs = []
for (nm, y), d in zip(branches, docs):
    if nm in ('inlB0', 'inlB1'):
        continue
    defs.append((nm, y, 'The branch %s of the trap of `+inlined`.' % d))
defs.append(('inlBMean', mean, 'The branch `%mean` of the trap of `+inlined` (under a `%toss` hint).'))
defs += [
    ('inlTrap', trap, 'The trap of `+inlined` over the nomm: the `?-` over its head.'),
    ('inlGet', getinl, '`(~(get by inl.cache) b)`.'),
    ('inlHit', hit, '`[u.n cache]`.'),
    ('inlHot', hot, 'The gate `hot`.'),
    ('inlGot', gotx, '`nomm:(~(got by code.long-ska) b)`.'),
    ('inlAfter', after, '`[new cache(inl (~(put by inl.cache) b new))]`.'),
    ('inlInner', inner, 'The nomm, the test of `inline-off` and the trap.'),
    ('inlMiss', miss, 'The branch where `inl.cache` has no nomm of `b`.'),
    ('inlBodyN', body, 'The gate body of `+inlined`.'),
]
with open(os.path.join(OUT, 'inlbody.lean'), 'w') as f:
    emit(f, defs)
print('ok')
