# Python port of msgOrd (lemmas/Ska/ShapeCol.lean), line for line.
import sys, itertools
from functools import lru_cache
sys.setrecursionlimit(10000)
N = ('N',); T = ('T',)
def P(a, b): return ('P', a, b)
def B(a, b): return ('B', a, b)
SPLIT = 6

def regs(mx, n, acc):
    if acc > mx: return acc
    if n == N: return acc
    if n == T: return acc + 1
    if n[0] == 'B': return regs(mx, n[2], regs(mx, n[1], acc + 1))
    return regs(mx, n[2], regs(mx, n[1], acc))

def cap(r): return T if regs(SPLIT, r, 0) > SPLIT else r
def cons(a, b): return N if (a == N and b == N) else P(a, b)
def hed(d): return d[1] if d[0] in 'PB' else N
def tel(d): return d[2] if d[0] in 'PB' else N
def ch(c): return c[1] if isinstance(c, tuple) else c
def ct(c): return c[2] if isinstance(c, tuple) else c

@lru_cache(maxsize=None)
def mnone(d, c):
    if d == N: return N
    if d == T: return T
    if isinstance(c, tuple):
        if d[0] == 'P': return cap(cons(mnone(d[1], c[1]), mnone(d[2], c[2])))
        return cap(B(mnone(d[1], c[1]), mnone(d[2], c[2])))
    return T

def mone(s, d, c):
    if isinstance(c, tuple):
        l = mnone(hed(d), c[1]); r = mnone(tel(d), c[2])
        isb = d[0] == 'B'
        return cap(B(l, r) if (s == T or isb) else cons(l, r))
    return T

@lru_cache(maxsize=None)
def msg(a, b, c):
    if a == b: return a
    la = a[0] in 'TN'; lb = b[0] in 'TN'
    if la and lb: return T
    if la: return mone(a, b, c)
    if lb: return mone(b, a, c)
    if a[0] == 'B' or b[0] == 'B':
        return B(msg(a[1], b[1], ch(c)), msg(a[2], b[2], ct(c)))
    return cons(msg(a[1], b[1], ch(c)), msg(a[2], b[2], ct(c)))

def shapes(k):
    """All shapes with exactly k inner nodes."""
    if k == 0: return [N, T]
    out = []
    for i in range(k):
        for l in shapes(i):
            for r in shapes(k - 1 - i):
                out.append(P(l, r)); out.append(B(l, r))
    return out

def capes(k, leaves=('n',)):
    if k == 0: return list(leaves)
    out = []
    for i in range(k):
        for l in capes(i, leaves):
            for r in capes(k - 1 - i, leaves):
                out.append(('c', l, r))
    return out

def show(x):
    if x == N: return 'none'
    if x == T: return 'this'
    if isinstance(x, str): return {'y': '&', 'n': '|'}[x]
    if x[0] == 'c': return '[%s %s]' % (show(x[1]), show(x[2]))
    if x[0] == 'P': return '[%s %s]' % (show(x[1]), show(x[2]))
    return '[%%both %s %s]' % (show(x[1]), show(x[2]))

def lean(x):
    if x == N: return '.none'
    if x == T: return '.this'
    if x == 'y': return '.yes'
    if x == 'n': return '.no'
    if x[0] == 'c': return '(.cell %s %s)' % (lean(x[1]), lean(x[2]))
    if x[0] == 'P': return '(.pair %s %s)' % (lean(x[1]), lean(x[2]))
    return '(.both %s %s)' % (lean(x[1]), lean(x[2]))

def hoon(x):
    if x == N: return '[%none ~]'
    if x == T: return '[%this ~]'
    if x == 'y': return '&'
    if x == 'n': return '|'
    if x[0] == 'c': return '[%s %s]' % (hoon(x[1]), hoon(x[2]))
    if x[0] == 'P': return '[%s %s]' % (hoon(x[1]), hoon(x[2]))
    return '[%%both %s %s]' % (hoon(x[1]), hoon(x[2]))
