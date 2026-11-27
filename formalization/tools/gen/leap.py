"""Cut the batteries of the `+leap` family into named parts and write them as
Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/leap.py OUTFILE

The arms: `+need-from` (door `14`, prefix `ndf`), `+need-cut` (door
`16375`, `ndc`), `+pass-bomb` (K `715742`, `pbo`), `+pass` (K `340`,
`pas`), `+pass-then` (K `86`, `pth`), `+pass-edit` (K `48046`, `ped`),
`+pass-both` (K `94`, `pbt`), `+lazy-leap` (door `442366`, `lzl`), `+leap`
(door `441179`, `lpx`; the same nouns as `lp6Arm`, cut further).  A door
arm `d` is `slot? d comp.door` (it is called as `[9 d' ..]`, `d'` being `d`
with a `0` put after its leading bit); a K arm `k` is `slot? k compK`.

Each arm is the gate `[8 [1 BUNT] [1 BAT] 0 1]`: `<p>Bunt`, `<p>Bat`,
`<p>Arm` and the kernel fact `<p>_at`.  Inside `BAT` every gate built in
place, `[8 [1 S] [1 G] 0 1]`, gets the name `<p>G<i>` for `G`, and every trap
`[8 [1 L] 9 2 0 1]` the name `<p>L<i>` for `L`, numbered innermost first in
the order of a walk head first.  The parts are substituted by structural
equality, so `<p>Bat` unfolds to the pill's noun.  Writes OUTFILE between
`-- BEGIN leap` and `-- END leap`."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm
OUT = sys.argv[1]

K = ('C', ('R', 'nhe0b859c3d8aa'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))
DOOR = ('R', 'comp.door')
ARMS = [('need-from', 'door', 14, 'ndf'), ('need-cut', 'door', 16375, 'ndc'),
        ('pass-bomb', 'K', 715742, 'pbo'), ('pass', 'K', 340, 'pas'), ('pass-then', 'K', 86, 'pth'),
        ('pass-edit', 'K', 48046, 'ped'), ('pass-both', 'K', 94, 'pbt'),
        ('lazy-leap', 'door', 442366, 'lzl'), ('leap', 'door', 441179, 'lpx')]

# Parts of a battery named by their axis in it, innermost first: in
# `lzlBat` = [7 [0 1] 8 cut 8 Sur R2], `Sur` is the `?~ cut` (axis 126),
# `R2` the turns and the prunes (127), `Pr` the two prunes (2047).
EXTRA = {'lzl': [('Pr', 2047, 'The two `+lazy-prune` of `+lazy-leap`.'),
                 ('R2', 127, 'The turns over the forks and the bonds of `+lazy-leap`, then the prunes.'),
                 ('Sur', 126, 'The `?~ cut` of `+lazy-leap`: the sure needs of `by` and `rec`.')]}

memo = {}
def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    k = id(n)
    if k not in memo:
        memo[k] = ('C', full(n[1]), full(n[2]))
    return memo[k]

A = lambda v: ('A', v)
def C(*xs):
    n = xs[-1]
    for x in reversed(xs[:-1]):
        n = ('C', x, n)
    return n

def gate_of(n):
    """[8 [1 S] [1 G] 0 1] -> (S, G)"""
    if n[0] == 'C' and n[1] == A(8) and n[2][0] == 'C':
        a, b = n[2][1], n[2][2]
        if a[0] == 'C' and a[1] == A(1) and b[0] == 'C' and b[2] == C(A(0), A(1)) \
                and b[1][0] == 'C' and b[1][1] == A(1):
            return a[2], b[1][2]
    return None

def trap_of(n):
    """[8 [1 L] 9 2 0 1] -> L"""
    if n[0] == 'C' and n[1] == A(8) and n[2][0] == 'C':
        a, b = n[2][1], n[2][2]
        if a[0] == 'C' and a[1] == A(1) and b == C(A(9), A(2), A(0), A(1)):
            return a[2]
    return None

out = []
names = {}

def show(n, top):
    if n in names and not top:
        return names[n]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1], False), show(n[2], False))

def emit(nm, n, doc):
    out.append('/-- %s -/\ndef %s : Noun :=\n  %s' % (doc, nm, show(n, True)))
    names[n] = nm

for hoon, where, ax, p in ARMS:
    base = DOOR if where == 'door' else K
    arm = full(slot(ax, base))
    g = gate_of(arm)
    assert g is not None, hoon
    bunt, bat = g
    cnt = {'G': 0, 'L': 0}
    def walk(n):
        if n[0] != 'C':
            return
        walk(n[1]); walk(n[2])
        gg = gate_of(n)
        if gg is not None and gg[1] not in names:
            cnt['G'] += 1
            emit('%sG%d' % (p, cnt['G']), gg[1], 'A gate built in `+%s`.' % hoon)
        t = trap_of(n)
        if t is not None and t not in names:
            cnt['L'] += 1
            emit('%sL%d' % (p, cnt['L']), t, 'A trap of `+%s`.' % hoon)
    walk(bat)
    for nm, sax, doc in EXTRA.get(p, []):
        emit(p + nm, full(slot(sax, bat)), doc)
    emit('%sBat' % p, bat, 'The battery of `+%s` (%s arm `%d`).' % (hoon, where, ax))
    out.append('def %sBunt : Noun :=\n  %s' % (p, show(bunt, True)))
    out.append('def %sArm : Noun := C (A 8) (C (C (A 1) %sBunt) (C (C (A 1) %sBat) (C (A 0) (A 1))))'
               % (p, p, p))
    lname = 'comp.door' if where == 'door' else 'compK'
    out.append('theorem %s_at : slot? %d %s = some %sArm := by kernel_rfl' % (p, ax, lname, p))
    out.append('theorem %s_arm (d : Noun) : nock d %sArm = some (C %sBat (C %sBunt d)) := by\n'
               '  unfold %sArm; simp only [nock_exec]' % (p, p, p, p, p))

text = '\n\n'.join(out) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN leap\n') + len('-- BEGIN leap\n')
e = src.index('-- END leap')
open(OUT, 'w').write(src[:b] + '\n' + text + '\n' + src[e:])
print('-- wrote', len(out), 'items,', len(text), 'characters')
