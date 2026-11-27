"""Cut the body of the case `%6` of `+run` (door axis 35179473141758) into
named parts.

    tools/capped.sh -m 3G python3 tools/gen/runsix.py OUTFILE

The body is `[8 LEP [6 [6 [3 0 2] [1 1] 1 0] NOLEP PHL]]`: the push of
`lep` (`+leap` of the goal under `%next`, else `~`), the test `?^  lep`,
phase L (`PHL`) and the rest `NOLEP = [6 T2 [6 TK PHK PHF] PHS]`: the test
`&(?=(%next -.goal) !(none-equivalent ..))`, the test of `+kerf`, phases K,
F and S.  Each phase is a chain of pushes (`=^`: `[7 [0 1] [8 A [7 E [7 F
REST]]]]`; `=/`: `[8 A REST]`; `=.`: `[7 [10 ..] REST]`); the rest after
each push is named `cr6<phase><i>` inside the earlier ones, so that
`crK6 = cr6Head` is a `kernel_rfl` fact.  The pushed computations of the
chains are named `cr6<phase>A<i>` when they are not small.  Writes the
definitions to OUTFILE between `-- BEGIN runsix` and `-- END runsix` (the
file must hold both lines) and prints the chains."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm
OUT = sys.argv[1]

def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    return ('C', full(n[1]), full(n[2]))

def size(n):
    return 1 if n[0] == 'A' else size(n[1]) + size(n[2])

def sl(ax, n):
    for b in bin(ax)[3:]:
        if n is None or n[0] != 'C':
            return None
        n = n[1] if b == '0' else n[2]
    return n

def isA(n, v):
    return n is not None and n[0] == 'A' and n[1] == v

def show(n, subs):
    if id(n) in subs:
        return subs[id(n)]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1], subs), show(n[2], subs))

def brief(n, lim=160):
    def s(n):
        if n[0] == 'A':
            return hex(n[1]) if n[1] > 9999 else str(n[1])
        parts = []
        while n[0] == 'C':
            parts.append(s(n[1])); n = n[2]
        parts.append(s(n))
        return '[' + ' '.join(parts) + ']'
    t = s(n)
    return t if len(t) <= lim else t[:lim] + '...'

def step(n):
    """One push of a chain: ('=^', A, REST), ('=/', A, REST), ('=.', E, REST) or None."""
    if isA(sl(2, n), 7) and sl(6, n) == ('C', ('A', 0), ('A', 1)) and isA(sl(14, n), 8):
        A = sl(30, n); r = sl(31, n)
        if isA(sl(2, r), 7) and isA(sl(14, r), 7) and sl(30, r) == ('C', ('C', ('A', 0), ('A', 4)), ('C', ('A', 0), ('A', 3))):
            return ('=^', A, sl(31, r))
    if isA(sl(2, n), 8):
        return ('=/', sl(6, n), sl(7, n))
    if isA(sl(2, n), 7) and sl(6, n) is not None and isA(sl(12, n), 10):
        return ('=.', sl(6, n), sl(7, n))
    return None

AK6 = 35179473141758
K6 = full(slot(AK6, ('R', 'comp.door')))
assert isA(sl(2, K6), 8)
LEP = sl(6, K6)
REST = sl(7, K6)
assert isA(sl(2, REST), 6)
assert sl(6, REST) == full(('C', ('A', 6), ('C', ('C', ('A', 3), ('C', ('A', 0), ('A', 2))), ('C', ('C', ('A', 1), ('A', 1)), ('C', ('A', 1), ('A', 0))))))
NOLEP = sl(14, REST)
PHL = sl(15, REST)
assert isA(sl(2, NOLEP), 6)
T2 = sl(6, NOLEP)
KF = sl(14, NOLEP)
PHS = sl(15, NOLEP)
assert isA(sl(2, KF), 6)
TK = sl(6, KF)
PHK = sl(14, KF)
PHF = sl(15, KF)

defs = []      # (name, noun) in the order of definition (later parts first)
subs = {}      # id -> name

def chain(prefix, n, stop=None):
    """Name the rests of the chain from n; returns the list of steps."""
    steps = []
    cur = n
    while True:
        if stop is not None and len(steps) == stop:
            break
        s = step(cur)
        if s is None:
            break
        steps.append((s[0], s[1], cur))
        cur = s[2]
    print('-- chain', prefix, len(steps), 'steps, last', brief(cur, 300))
    # the last rest gets the next index
    names = []
    for i, (k, a, c) in enumerate(steps):
        nm = '%s%d' % (prefix, i)
        print('--   %s %s %s' % (nm, k, brief(a, 200)))
        names.append((nm, c, a))
    last = ('%s%d' % (prefix, len(steps)), cur)
    return names, last

def emit_chain(prefix, n, stop=None, name_as=None):
    names, last = chain(prefix, n, stop)
    # define from the last rest backwards
    order = [last] + [(nm, c) for (nm, c, a) in reversed(names)]
    for nm, c in order:
        if name_as is not None and c is n:
            nm = name_as
        defs.append((nm, c))
        subs_c = dict(subs)
        subs[id(c)] = nm
    for (nm, c, a) in names:
        if size(a) > 40:
            an = prefix + 'A' + nm[len(prefix):]
            defs.append((an, a))
    return names, last

# the pushed computations that are named get their own entries before use
def name_noun(nm, n):
    defs.append((nm, n))
    subs[id(n)] = nm

# phase S
sn, slast = emit_chain('cr6S', PHS)
# phase F
fn, flast = emit_chain('cr6F', PHF)
# phase K
kn, klast = emit_chain('cr6K', PHK)
# phase L
ln, llast = emit_chain('cr6L', PHL)

def render(nm, n):
    # a part's own text must not substitute itself
    own = subs.get(id(n))
    if own is not None:
        del subs[id(n)]
    t = show(n, subs)
    if own is not None:
        subs[id(n)] = own
    return 'def %s : Noun :=\n  %s' % (nm, t)

# pushed computations: name the big ones so the chain parts mention them
for nm, n in list(defs):
    pass
ordered = []
named_A = [(nm, n) for (nm, n) in defs if 'A' in nm[4:]]
named_R = [(nm, n) for (nm, n) in defs if 'A' not in nm[4:]]
for nm, n in named_A:
    subs[id(n)] = nm
# A-parts may contain later chain parts?  They do not (they are pushed
# computations), but they may contain each other's subterms; render them
# without chain names
out = []
for nm, n in named_A:
    del subs[id(n)]
    saved = dict(subs)
    subs.clear()
    out.append(render(nm, n))
    subs.update(saved)
    subs[id(n)] = nm
for nm, n in named_R:
    out.append(render(nm, n))
name_noun_list = [('cr6Lep', LEP), ('cr6T2', T2), ('cr6TK', TK)]
for nm, n in name_noun_list:
    saved = dict(subs); subs.clear()
    out.append(render(nm, n))
    subs.update(saved)
    subs[id(n)] = nm
subs[id(PHS)] = 'cr6S0'; subs[id(PHF)] = 'cr6F0'; subs[id(PHK)] = 'cr6K0'; subs[id(PHL)] = 'cr6L0'
out.append('def cr6KF : Noun :=\n  C (A 6) (C cr6TK (C cr6K0 cr6F0))')
out.append('def cr6NoLep : Noun :=\n  C (A 6) (C cr6T2 (C cr6KF cr6S0))')
out.append('def cr6Head : Noun :=\n  C (A 8) (C cr6Lep (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) '
           '(C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C cr6NoLep cr6L0))))')
text = '\n\n'.join(out) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN runsix\n') + len('-- BEGIN runsix\n')
e = src.index('-- END runsix')
open(OUT, 'w').write(src[:b] + '\n' + text + '\n' + src[e:])
print('-- wrote', len(out), 'definitions,', len(text), 'characters')
