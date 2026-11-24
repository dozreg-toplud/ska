"""Cut the body of the case `%2` of `+run` (door axis 8588738558) into
named parts.

    tools/capped.sh -m 3G python3 tools/gen/runtwo.py OUTDIR

The body is `[6 [5 [1 0] [0 471]] IND DIR]`: the test `?~  info.nomm` (the
`info` of the nomm at axis `58` is at `471` of the subject), the indirect
call `IND` and the direct call `DIR`.  Writes `OUTDIR/k2.lean`: `IND` cut at
its `=^` pushes (`+simple-next`, `+kerf`, two `+re`, `+emit`, the run of
`q`, `+past`, the run of `p`, then `+copy`), each later part named inside
the earlier ones, so that `crK2 = cr2Head` is a `kernel_rfl` fact, with `DIR`
read from the pill as `(slot? k comp.door).getD (A 0)`.  Prints the pushes."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm, lean as lean_n
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'

def comp(a, b):
    k = b.bit_length() - 1
    return (a << k) | (b - (1 << k))

def full(n):
    """The noun with every reference resolved, as nested tuples."""
    n = norm(n)
    if n[0] == 'A':
        return n
    return ('C', full(n[1]), full(n[2]))

def sl(ax, n):
    bits = bin(ax)[3:]
    for b in bits:
        assert n[0] == 'C', (ax, n)
        n = n[1] if b == '0' else n[2]
    return n

def show(n, subs):
    if id(n) in subs:
        return subs[id(n)]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1], subs), show(n[2], subs))

def after_push(n):
    """`[7 [0 1] [8 A [7 E [7 F REST]]]]` (one `=^`) -> (A, REST)."""
    assert sl(2, n) == ('A', 7)
    e8 = sl(7, n)
    assert sl(2, e8) == ('A', 8)
    A = sl(6, e8)
    r = sl(7, e8)
    REST = sl(7, sl(7, r))
    return A, REST

AK2 = 8588738558
door = ('R', 'comp.door')
K2 = full(slot(AK2, door))
assert sl(2, K2) == ('A', 6)
TEST = sl(6, K2)
IND = sl(14, K2)
ADIR = comp(AK2, 15)
print('-- test', show(TEST, {}))
print('-- dir axis', ADIR)
parts = []
cur = IND
while True:
    try:
        a, r = after_push(cur)
    except AssertionError:
        break
    parts.append((a, cur))
    cur = r
print('-- pushes', len(parts))
for i, (a, c) in enumerate(parts):
    print('-- push', i, show(a, {})[:300])
print('-- last', show(cur, {})[:300])
# parts: 0 simple-next, 1 kerf, 2 re, 3 re, 4 emit, 5 run q, 6 past, 7 run p
T1 = parts[1][1]
TAIL = parts[5][1]
T2 = parts[6][1]
T3 = parts[7][1]
defs = [
    'def cr2T3 : Noun :=\n  ' + show(T3, {}),
    'def cr2T2 : Noun :=\n  ' + show(T2, {id(T3): 'cr2T3'}),
    'def cr2Tail : Noun :=\n  ' + show(TAIL, {id(T2): 'cr2T2'}),
    'def cr2Kf : Noun :=\n  ' + show(T1, {id(TAIL): 'cr2Tail'}),
    'def cr2Ind : Noun :=\n  ' + show(IND, {id(T1): 'cr2Kf'}),
    'def cr2Dir : Noun := (slot? %d comp.door).getD (A 0)' % ADIR,
    'def cr2Head : Noun :=\n  C (A 6) (C ' + show(TEST, {}) + ' (C cr2Ind cr2Dir))',
]
open(os.path.join(OUT, 'k2.lean'), 'w').write('\n\n'.join(defs) + '\n')
