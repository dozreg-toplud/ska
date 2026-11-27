"""Cut the direct call of the case `%2` of `+run` (`cr2Dir`, door axis
`comp(8588738558, 15)`) into named parts.

    tools/capped.sh -m 3G python3 tools/gen/direct.py OUTDIR

`cr2Dir` is `[7 [0 1] [7 [0 1] [8 PURE [6 TEST DROP CALL]]]]`: the two `=*`
(`b-callee`, `key`), the push of `callee-pure`, the test of the drop, the
dropped call `DROP` and the call `CALL`.  Writes `OUTDIR/kd.lean`: `PURE`,
`TEST`, `DROP` cut at its `=^` pushes (`crDNf`, the run of `q` under `+safe-fol-fol`,
`+past`, the run of `p`, then `+copy`), each later part named inside the
earlier ones, with `CALL` read from the pill as `(slot? k comp.door).getD
(A 0)`, so that `cr2Dir = crDHead` is a `kernel_rfl` fact.  Prints the map
of `CALL`: each push with its cell count and the arms it pulls (core axis,
battery axis)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)
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

def show(n, subs):
    if id(n) in subs:
        return subs[id(n)]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (show(n[1], subs), show(n[2], subs))

def bat(a):
    """The battery axis of the core axis `a` (`a` in the head)."""
    k = a.bit_length() - 1
    assert (a >> (k - 1)) == 2, a
    return (1 << (k - 1)) | (a - (1 << k))

def pulls(n, out):
    if n[0] == 'A':
        return
    if n[1] == ('A', 9) and n[2][0] == 'C' and n[2][1][0] == 'A':
        f = n[2][2]
        core = f[2][1] if f[0] == 'C' and f[1] == ('A', 0) else None
        out.append((n[2][1][1], core))
    pulls(n[1], out)
    pulls(n[2], out)

def is_push(n):
    """`[7 [0 1] [8 A [7 E [7 F REST]]]]` (one `=^`)."""
    try:
        return (sl(2, n) == ('A', 7) and sl(6, n) == ('C', ('A', 0), ('A', 1)) and sl(14, n) == ('A', 8)
                and sl(62, n) == ("A", 7) and sl(254, n) == ("A", 7))
    except AssertionError:
        return False

AK2 = 8588738558
ADIR = comp(AK2, 15)
door = ('R', 'comp.door')
DIR = full(slot(ADIR, door))
assert sl(2, DIR) == ('A', 7) and sl(6, DIR) == ('C', ('A', 0), ('A', 1))
X = sl(7, DIR)
assert sl(2, X) == ('A', 7) and sl(6, X) == ('C', ('A', 0), ('A', 1))
P8 = sl(7, X)
assert sl(2, P8) == ('A', 8)
PURE = sl(6, P8)
IF = sl(7, P8)
assert sl(2, IF) == ('A', 6)
TEST = sl(6, IF)
DROP = sl(14, IF)
CALL = sl(15, IF)
ACALL = comp(ADIR, 1023)
assert full(slot(ACALL, door)) == CALL
print('-- cells: dir', cells(DIR), 'pure', cells(PURE), 'test', cells(TEST), 'drop', cells(DROP),
      'call', cells(CALL), 'call axis', ACALL)
# the dropped call
d = [DROP]
while is_push(d[-1]):
    d.append(sl(511, d[-1]))
assert len(d) == 4, len(d)
print('-- drop pushes', [cells(sl(30, x)) for x in d[:3]], 'last', cells(d[3]))
# the map of CALL
cur = CALL
ax = ACALL
i = 0
while True:
    if is_push(cur):
        A = sl(30, cur)
        tag, nxt, step = "=^", sl(511, cur), 511
    elif sl(2, cur) == ('A', 8):
        A = sl(6, cur)
        tag, nxt, step = '=/', sl(7, cur), 7
    elif sl(2, cur) == ('A', 7) and sl(6, cur) == ('C', ('A', 0), ('A', 1)):
        print('-- call', i, '=*  (alias)')
        cur, ax, i = sl(7, cur), comp(ax, 7), i + 1
        continue
    else:
        A, tag, nxt = cur, 'end', None
    ps = []
    pulls(A, ps)
    print('-- call', i, tag, 'cells', cells(A), 'axis', ax, 'pulls',
          sorted(set((a, c) for a, c in ps if a != 2)))
    if nxt is None:
        break
    cur, ax, i = nxt, comp(ax, step), i + 1
D1, D2, D3 = d[1], d[2], d[3]
defs = [
    'def crDD3 : Noun :=\n  ' + show(D3, {}),
    'def crDD2 : Noun :=\n  ' + show(D2, {id(D3): 'crDD3'}),
    'def crDD1 : Noun :=\n  ' + show(D1, {id(D2): 'crDD2'}),
    'def crDNf : Noun :=\n  ' + show(sl(30, DROP), {}),
    'def crDDrop : Noun :=\n  ' + show(DROP, {id(D1): 'crDD1', id(sl(30, DROP)): 'crDNf'}),
    'def crDPure : Noun :=\n  ' + show(PURE, {}),
    'def crDTest : Noun :=\n  ' + show(TEST, {}),
    'def crDCall : Noun := (slot? %d comp.door).getD (A 0)' % ACALL,
    'def crDHead : Noun :=\n  C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDPure '
    '(C (A 6) (C crDTest (C crDDrop crDCall))))))))',
]
open(os.path.join(OUT, 'kd.lean'), 'w').write('\n\n'.join(defs) + '\n')
