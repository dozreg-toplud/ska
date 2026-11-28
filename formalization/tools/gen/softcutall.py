"""The nouns of `+soft-cut` on every need (README Gaps 21.22), for `CompSccLoopSoftCutAll.lean`:
`+sure-at` (line 7682, arm `0x2bbe` of the core `compK`), `+soft-pair` (line 5582, battery slot
13652 of `comp.door`), and the cell parts of `+soft-axis` (`sxCell`) and `+soft-cut` (`skCell`,
`CompSccLoopSoftEmitTrap.lean`) cut at their pushes.  Prints the Lean definitions to paste between
`-- BEGIN softcutall` and `-- END softcutall` (with OUTFILE: writes them there).

    tools/capped.sh -m 3G python3 tools/gen/softcutall.py [OUTFILE]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(1000000)
import nouns
from nouns import slot, norm, lean, eqn

door = nouns.get('comp.door')
kbat = nouns.get('nh5592f9d7750f')


def sl(a, n):
    r = slot(a, n)
    assert r is not None, a
    return norm(r)


def cells(n):
    n = norm(n)
    return 0 if n[0] == 'A' else 1 + cells(n[1]) + cells(n[2])


out = []
sub = []


def emit(nm, n):
    out.append('def %s : Noun :=\n  %s\n' % (nm, lean(n, sub)))
    sub.insert(0, (nm, norm(n)))


def gate(nm, arm):
    # [8 [1 bunt] [1 bat] [0 1]]
    assert sl(2, arm) == ('A', 8) and sl(12, arm) == ('A', 1) and sl(28, arm) == ('A', 1)
    assert sl(15, arm) == ('C', ('A', 0), ('A', 1))
    return sl(13, arm), sl(29, arm)


def chain(pre, cur):
    """the pushes (7 / 8) of cur, the rests named pre0 pre1 .., heads preHi when big"""
    parts = []
    while True:
        cur = norm(cur)
        if cur[0] == 'C' and norm(cur[1])[0] == 'A' and norm(cur[1])[1] in (7, 8) and norm(cur[2])[0] == 'C':
            parts.append((norm(cur[1])[1], norm(cur[2])[1]))
            cur = norm(cur[2])[2]
        else:
            break
    emit('%s%d' % (pre, len(parts)), cur)
    for i in range(len(parts) - 1, -1, -1):
        op, h = parts[i]
        if cells(h) > 3:
            emit('%sH%d' % (pre, i), h)
        cur = ('C', ('A', op), ('C', h, cur))
        emit('%s%d' % (pre, i), cur)
    return len(parts)


# +sure-at
sa = sl(0x2bbe, ('C', kbat, ('A', 0)))  # arm 0x2bbe of compK: battery slot of the head
sa_bunt, sa_bat = gate('sa', sa)
assert cells(sa_bat) < 200, cells(sa_bat)
emit('sqSaBunt', sa_bunt)
emit('sqSaBat', sa_bat)
emit('sqSaArm', sa)
# +soft-pair
sp = sl(13652, door)
sp_bunt, sp_bat = gate('sp', sp)
emit('sqSpBunt', sp_bunt)
# sp_bat = [6 T [1 no] [8 QH [8 QT FIN]]]
assert sl(2, sp_bat) == ('A', 6) and sl(14, sp_bat) == ('C', ('A', 1), ('A', 0x6f6e))
emit('sqSpNo', sl(6, sp_bat))
rest = sl(15, sp_bat)
assert sl(2, rest) == ('A', 8)
emit('sqSpQh', sl(6, rest))
r2 = sl(7, rest)
assert sl(2, r2) == ('A', 8)
emit('sqSpQt', sl(6, r2))
emit('sqSpFin', sl(7, r2))
emit('sqSpBat', sp_bat)
emit('sqSpArm', sp)
# +soft-axis, cells: sxCell = [6 [3 0 24] PAIR [11 HINT BOTH]]
sxbat = sl(29, sl(4062, door))
sxcell = sl(127, sxbat)
assert sl(2, sxcell) == ('A', 6) and sl(30, sxcell) == ('A', 11)
emit('sqSxPair', sl(14, sxcell))
emit('sqSxHint', sl(62, sxcell))
chain('sqSxB', sl(63, sxcell))
# +soft-cut: skT2 at 254 of the battery, skCell at 32767
skbat = sl(29, sl(220588, door))
skcell = sl(32767, skbat)
assert sl(2, skcell) == ('A', 6) and sl(30, skcell) == ('A', 11)
emit('sqCHint', sl(62, skcell))
print('-- pair pushes', chain('sqCP', sl(14, skcell)), file=sys.stderr)
both = sl(63, skcell)
assert sl(2, both) == ('A', 6) and sl(14, both) == ('C', ('A', 0), ('A', 0))
emit('sqCBTest', sl(6, both))
print('-- both pushes', chain('sqCB', sl(15, both)), file=sys.stderr)
text = '\n'.join(out)
if len(sys.argv) > 1:
    src = open(sys.argv[1]).read()
    b = src.index('\n-- BEGIN softcutall\n') + len('\n-- BEGIN softcutall\n')
    e = src.index('\n-- END softcutall\n', b) + 1
    open(sys.argv[1], 'w').write(src[:b] + '\n' + text + '\n' + src[e:])
else:
    print(text)
