#!/usr/bin/env python3
# usage: splitmax-climb.py K KC [--cut]
# Track S (README Gaps 30.4): the measure of the uncut join, by enumeration.  For every entry e and
# new need n with at most K inner nodes ([none none] left out: cons-need never makes it) and every
# cape with at most KC, e' = msg n e (msgpy.py, split-max infinite; --cut: 6) climbs:
#   at a node where the cape is a cell, the kind of e' (none 0, this or split 1, both 2) is not
#   below that of e, and this never becomes a split nor a split this;
#   at a node where the cape is an atom, e' is e's leaf if e is this, none or this if e is none,
#   and else this, or a split/both whose children climb in the same sense, both staying both.
# So with mu = (the kinds over the cell nodes of the cape, minus the weight of the parts under atom
# nodes: 3 per split, 2 per both, 1 per none leaf), every change raises mu lexicographically.
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(D, '..', 'msgord'))
import msgpy  # noqa: E402
from msgpy import N, T  # noqa: E402

K, KC = int(sys.argv[1]), int(sys.argv[2])
msgpy.SPLIT = 6 if '--cut' in sys.argv else 10 ** 9
KIND = {'N': 0, 'T': 1, 'P': 1, 'B': 2}


def ch(x, i): return x[i] if x[0] in 'PB' else N


def ok(e, e2, c):
    if isinstance(c, tuple):
        if KIND[e2[0]] < KIND[e[0]]: return False
        if {e[0], e2[0]} == {'T', 'P'}: return False
        return ok(ch(e, 1), ch(e2, 1), c[1]) and ok(ch(e, 2), ch(e2, 2), c[2])
    if e == T: return e2 == T
    if e == N: return e2 in (N, T)
    if e2 == T: return True
    if e2[0] == 'P' and e[0] == 'B': return False
    if e2[0] not in 'PB': return False
    return ok(e[1], e2[1], c) and ok(e[2], e2[2], c)


def nonn(x):
    return x[0] not in 'PB' or (not (x[1] == N and x[2] == N) and nonn(x[1]) and nonn(x[2]))


sh = [s for k in range(K + 1) for s in msgpy.shapes(k) if nonn(s)]
cs = [c for k in range(KC + 1) for c in msgpy.capes(k)]
bad = 0; tot = 0
for c in cs:
    msgpy.msg.cache_clear(); msgpy.mnone.cache_clear()
    for e in sh:
        for n in sh:
            tot += 1
            if not ok(e, msgpy.msg(n, e, c), c):
                bad += 1
                if bad <= 3:
                    print('FAIL cape %s e %s n %s -> %s' % (msgpy.show(c), msgpy.show(e), msgpy.show(n),
                                                          msgpy.show(msgpy.msg(n, e, c))))
print('%d triples, %d fail (split-max %s)' % (tot, bad, msgpy.SPLIT))
