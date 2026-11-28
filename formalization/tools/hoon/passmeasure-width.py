#!/usr/bin/env python3
# usage: passmeasure-width.py OUT.txt...                                (track F, README Gaps 16)
# WidthFin on traces of a library instrumented by passmeasure.py (lines
#   [%pm-new mug index depth]  [%pm-pass mug pass members next depth]  [%pm-case n name]).
# A pass loop of root r runs from a [%pm-pass r 1 ...] to the last [%pm-pass r ...] before the
# next [%pm-pass r 1 ...] or the end of the case.  For each loop: the pushes (%pm-new) between
# its first and its last pass start (the pushes made by the runs of the loop, nested loops
# included), the growth of the stack between them (the new members: with dab8478 the stack
# only grows on top between pass starts), and their difference, the pushes that did not stay
# on the stack (finished, popped into done, or dropped by a nested +cull): an upper bound on
# the identities that WidthFin bounds (in the graph, not in it at the loop's entry, not on the
# stack).  Prints the largest counts per loop and the passes of that loop.
import sys

def num(s):
    s = s.strip(']').replace('.', '')
    return int(s, 16) if s.startswith('0x') else int(s)

def loops(path):
    out = []
    ev = []          # (kind, mug, pass, depth) in order, per case
    def flush():
        # pass starts per root, split at pass 1
        open_ = {}
        for k, (kind, mug, p, d) in enumerate(ev):
            if kind != 'pass':
                continue
            if p == 1 or mug not in open_:
                if mug in open_:
                    out.append(open_[mug])
                open_[mug] = [mug, k, k, d, d, 1]
            else:
                L = open_[mug]
                L[2] = k; L[4] = d; L[5] = max(L[5], p)
        for L in open_.values():
            out.append(L)
        res = []
        for mug, k0, k1, d0, d1, np in out:
            pushes = sum(1 for e in ev[k0:k1] if e[0] == 'new')
            res.append((pushes - (d1 - d0), pushes, d1 - d0, np, mug))
        out.clear()
        return res
    res = []
    for line in open(path, errors='replace'):
        if line.startswith('[%pm-case'):
            res += flush(); ev = []
            continue
        if line.startswith('[%pm-new'):
            t = line.split()
            if num(t[2]) == 0 and num(t[3]) == 0:
                res += flush(); ev = []
            ev.append(('new', t[1], 0, num(t[3])))
        elif line.startswith('[%pm-pass'):
            t = line.split()
            ev.append(('pass', t[1], num(t[2]), num(t[5])))
    res += flush()
    return res

allr = []
for p in sys.argv[1:]:
    r = loops(p)
    allr += [(x, p) for x in r]
print('loops', len(allr))
print('loops with a push that did not stay', sum(1 for (x, _) in allr if x[0] > 0))
for (w, pushes, grow, np, mug), p in sorted(allr, reverse=True)[:8]:
    print(f'width<={w} pushes={pushes} new-members={grow} passes={np} root={mug} {p.split("/")[-1]}')
