#!/usr/bin/env python3
# usage: splitmax-order.py OUT.txt      (a run of a splitmax.py --trace copy, NOT --small)
# Track S (README Gaps 30): what orders the need-new of a member across the sweeps.  For each
# member, its %must compiles in order (need-new of each), and every consecutive pair n -> n'
# compared by the axes it splits (inner nodes, P) and the axes it holds in a register (%this and
# %both nodes, R): n' loses parts (P' a subset of P), gains parts, is equal, or neither; and the
# step of the stored entry e -> e' = msg n' e in the uncut order (e' = msg-uncut e e'), which a
# climb satisfies.
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(D, 'splitmax-sum.py')).read().replace('\nmain()\n', '\n')
g = {'__file__': os.path.join(D, 'splitmax-sum.py')}
exec(src, g)


def axes(n, ax=1, P=None, R=None):
    if P is None: P, R = set(), set()
    if n[0] == 'T': R.add(ax)
    elif n[0] in 'PB':
        P.add(ax)
        if n[0] == 'B': R.add(ax)
        axes(n[1], 2 * ax, P, R); axes(n[2], 2 * ax + 1, P, R)
    return P, R


seqs = {}; cap = {}; steps = []
for e in g['records'](sys.argv[1]):
    if not isinstance(e, tuple) or not isinstance(e[0], int): continue
    t = g['cord'](e[0])
    if t == 's0':
        S, (b, (mode, (nn, c))) = e[1]
        if mode != g['MUST']: continue
        seqs[(S, b)] = [g['need'](nn)]; cap[(S, b)] = g['cape'](c)
    elif t == 'sm':
        S, (b, (mode, (nn, (prev, np)))) = e[1]
        if mode != g['MUST'] or (S, b) not in seqs: continue
        seqs[(S, b)].append(g['need'](nn))
        steps.append((g['need'](prev), g['need'](np), cap[(S, b)]))
k = dict(equal=0, loses=0, gains=0, neither=0)
kr = dict(equal=0, loses=0, gains=0, neither=0)
for key, sq in seqs.items():
    for a, b in zip(sq, sq[1:]):
        (Pa, Ra), (Pb, Rb) = axes(a), axes(b)
        for (x, y, kk) in ((Pa, Pb, k), (Ra, Rb, kr)):
            kk['equal' if x == y else 'loses' if y < x else 'gains' if y > x else 'neither'] += 1
climb = sum(1 for (p, n, c) in steps if p == n or g['msg'](p, n, c, False) == n)
print('members %d, consecutive need-new pairs %d' % (len(seqs), sum(k.values())))
print('  by split axes P:', k)
print('  by register axes R:', kr)
print('entry steps %d: climbs in the uncut order %d, falls %d' % (len(steps), climb, len(steps) - climb))
