"""The noun of `+lazy-to-inter1` (arm `6006` of `K`) cut for the link with
forks and bonds (README Gaps 9): the `l2iNo` branch of `CompShapeCol.lean` is

    [8 ROLL [9 2 [10 [6 [0 59] [7 [0 3] [8 NTA [8 TURN [8 [[0 6] [0 121]]
      [8 [[[1 0] LZB] [0 2] [0 6]] [[1 BG] [0 1]]]]]]]] [0 2]]]]

with `TURN` the `+turn` over `fork.laz` (gate `TG`, sample bunt `TB`), `LZB`
the bunt of `need-lazy` (arm `191` of the core at axis `127`) and `BG` the
gate body of the `+roll` over `bond.laz`.

    tools/capped.sh -m 3G python3 tools/gen/shapecoll2i.py OUTDIR

writes `OUTDIR/shapecoll2i.lean`."""
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


arm = norm(slot(6006, K))
# [7 [8 [1 BUNT] [1 BODY] 0 1] HINT]
body = norm(slot(29, norm(slot(6, arm))))
# [7 [0 1] [6 TEST YES NO]]
six = norm(slot(7, body))
no = norm(slot(15, six))
roll_arm = slot(6, no)
sample = norm(slot(13, norm(slot(7, norm(slot(7, no))))))
assert show(slot(2, sample), names=False) == '[0 59]', show(slot(2, sample))
gate_f = norm(slot(3, sample))      # [7 [0 3] INNER]
assert show(slot(6, gate_f), names=False) == '[0 3]'
inner = norm(slot(7, gate_f))       # [8 NTA R1]
nta = slot(6, inner)
r1 = norm(slot(7, inner))
turn = slot(6, r1)
r2 = norm(slot(7, r1))
sn = slot(6, r2)
assert show(sn, names=False) == '[[0 6] 0 121]', show(sn, names=False)
r3 = norm(slot(7, r2))
smp = slot(6, r3)
lzb = slot(5, smp)
bgc = norm(slot(7, r3))
bg = slot(5, bgc)
assert show(slot(3, bgc), names=False) == '[0 1]'
# TURN = [8 ARM [9 2 [10 [6 [0 122] [7 [0 3] [8 [1 TB] [[1 TG] [0 1]]]]] [0 2]]]]
# find [8 [1 TB] [[1 TG] [0 1]]]
def find8(n):
    n = norm(n)
    if n[0] != 'C': return None
    h = norm(n[1])
    if h == ('A', 8):
        a = norm(slot(6, n)); b = norm(slot(7, n))
        if a[0] == 'C' and norm(a[1]) == ('A', 1) and b[0] == 'C':
            bh = norm(b[1])
            if bh[0] == 'C' and norm(bh[1]) == ('A', 1):
                return norm(a[2]), norm(bh[2])
    for c in (n[1], n[2]):
        r = find8(c)
        if r: return r
    return None
tb, tg = find8(turn)
with open(os.path.join(OUT, 'shapecoll2i.lean'), 'w') as f:
    subs = []
    for name, n, doc in [
            ('l2iTB', tb, 'The sample bunt of the gate of the `+turn` over `fork.laz`.'),
            ('l2iTG', tg, 'The gate of the `+turn` over `fork.laz`: `[(lazy-to-inter laz-y) (lazy-to-inter laz-n)]`.'),
            ('l2iTurn', turn, '`fork-new`: the `+turn` over `fork.laz`.'),
            ('l2iLzb', lzb, 'The bunt of `need-lazy` in the sample of the gate of the `+roll`.'),
            ('l2iBG', bg, 'The gate of the `+roll` over `bond.laz`.'),
            ('l2iNoN', no, '`l2iNo` with its parts named.')]:
        f.write('/-- %s -/\ndef %s : Noun :=\n  %s\n\n' % (doc, name, lean(n, subs)))
        subs.insert(0, (name, n))
print(show(nta, names=False)); print(show(roll_arm, names=False)); print(show(smp, names=False)); print(show(turn, names=False))
