"""Cut the long bodies of the cases of `+run` into named parts.

    tools/capped.sh -m 3G python3 tools/gen/split.py OUTDIR

reads the bodies `crK5`, `crK10`, `crKc` from
`lemmas/Compiler/CompRunLink.lean` (one line after `def NAME : Noun :=`) and
writes `OUTDIR/k5.lean`, `OUTDIR/k10.lean`, `OUTDIR/kc.lean`: the parts as
Lean definitions, each later part named inside the earlier ones, so that
`crK5 = cr5Head` (and so on) is a `kernel_rfl` fact.  It prints the pushes
of each body.  `after_push` takes apart the Nock of one `=^`:
`[7 [0 1] [8 A [7 E [7 F REST]]]]`, the computation `A` and the rest."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import parse
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '..', '..', 'lemmas', 'Compiler', 'CompRunLink.lean')
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
rc = open(SRC).read().split('\n')

def body(name):
    for i, l in enumerate(rc):
        if l == 'def %s : Noun :=' % name:
            return parse(rc[i + 1])
    raise KeyError(name)

def sl(ax, n):
    bits = bin(ax)[3:]
    for b in bits:
        assert n[0] == 'C', (ax, n)
        n = n[1] if b == '0' else n[2]
    return n

def show(n, subs):
    """The noun as a Lean literal, the nodes in `subs` (by `id`) named."""
    if id(n) in subs:
        return subs[id(n)]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    if n[0] == 'R':
        return n[1]
    return '(C %s %s)' % (show(n[1], subs), show(n[2], subs))

def sh(n, d=0):
    """A short sketch of the noun, four levels deep."""
    if n[0] == 'A':
        return str(n[1]) if n[1] < 10000 else hex(n[1])
    if d > 3:
        return '..'
    return '[' + sh(n[1], d + 1) + ' ' + sh(n[2], d + 1) + ']'

def after_push(n):
    """`[7 [0 1] [8 A [7 E [7 F REST]]]]` (one `=^`) -> (A, REST)."""
    assert sl(2, n) == ('A', 7)
    e8 = sl(7, n)
    assert sl(2, e8) == ('A', 8)
    A = sl(6, e8)
    r = sl(7, e8)
    REST = sl(7, sl(7, r))
    return A, REST

def pushes(n):
    """The `=^` pushes of a body: a list of (computation, body from it)."""
    out = []
    cur = n
    while True:
        try:
            a, r = after_push(cur)
        except AssertionError:
            break
        out.append((a, cur))
        cur = r
    return out, cur

def write(name, defs):
    open(os.path.join(OUT, name), 'w').write('\n\n'.join(defs) + '\n')

# %5: two registers, the branch over the goal, the tail.
K5 = body('crK5')
A1, Y = after_push(K5)
A2, Z = after_push(Y)
BRw, TAIL = after_push(Z)
BR = sl(7, BRw)
Aq, T2 = after_push(TAIL)
Apast, T3 = after_push(T2)
Ap, COPY = after_push(T3)
write('k5.lean', [
    'def cr5Br : Noun :=\n  ' + show(BR, {}),
    'def cr5T3 : Noun :=\n  ' + show(T3, {}),
    'def cr5T2 : Noun :=\n  ' + show(T2, {id(T3): 'cr5T3'}),
    'def cr5Tail : Noun :=\n  ' + show(TAIL, {id(T2): 'cr5T2'}),
    'def cr5Head : Noun :=\n  ' + show(K5, {id(BR): 'cr5Br', id(TAIL): 'cr5Tail'})])

# %10: +simple-next, +into, the tail.
K10 = body('crK10')
pcs, last = pushes(K10)
print('==== K10 pushes', len(pcs))
for i, (a, c) in enumerate(pcs):
    print('-- push', i, show(a, {})[:300])
T10 = pcs[2][1]
write('k10.lean', [
    'def cr10Tail : Noun :=\n  ' + show(T10, {}),
    'def cr10Head : Noun :=\n  ' + show(K10, {id(T10): 'cr10Tail'})])

# cons: the `=>` for %done, the branch %pick, +split and the tail for %next.
Kc = body('crKc')
print('==== Kc', sh(Kc))
BODY = sl(7, Kc)
PICK = sl(14, BODY)
HN = sl(15, BODY)
NEXT = sl(7, HN)
pcs, _ = pushes(NEXT)
print('next pushes', len(pcs))
for i, (a, c) in enumerate(pcs):
    print('-- push', i, show(a, {})[:250])
NT = pcs[1][1]
pp, _ = pushes(PICK)
print('pick pushes', len(pp))
for i, (a, c) in enumerate(pp):
    print('-- ppush', i, show(a, {})[:250])
write('kc.lean', [
    'def crcNTail : Noun :=\n  ' + show(NT, {}),
    'def crcPick : Noun :=\n  ' + show(PICK, {}),
    'def crcHead : Noun :=\n  ' + show(Kc, {id(NT): 'crcNTail', id(PICK): 'crcPick'})])
