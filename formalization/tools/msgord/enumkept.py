"""The kept join `+msg-need-ord-kept` (2a5b618, `msgOrdKept` of lemmas/Ska/ShapeColKept.lean),
line for line over `msgpy.msg`, and the enumeration of what ShapeColKept.lean proves:

  climb  OrdLe old (kept new old less)              (kept_climbs, on a canonical entry)
  canon  Canon old -> Canon (kept new old less)     (kept_canon)
  pot    kept = old  or  pot less kept < pot less old   (kept_pot)

and, for the record, how often plain `msg` falls (old <= msg fails) and the non-canonical
entries on which the kept join falls.  Run from this directory:

    python3 enumkept.py K KC     # shapes up to K inner nodes, capes up to KC

(`enumkept.py 3 3`: 2,359,296 triples of canonical shapes.)"""
import sys
sys.path.insert(0, '.')
from msgpy import *

def kept(new, old, c):
    if new == old: return new
    if old == T: return old
    if old == N or new == N or new == T: return msg(new, old, c)
    if new[0] == 'B':
        if old[0] == 'B': return B(kept(new[1], old[1], ch(c)), kept(new[2], old[2], ct(c)))
        return B(kept(new[1], old[1], ch(c)), kept(new[2], old[2], ct(c)))
    if old[0] == 'B': return B(kept(new[1], old[1], ch(c)), kept(new[2], old[2], ct(c)))
    return cons(kept(new[1], old[1], ch(c)), kept(new[2], old[2], ct(c)))

def le(x, y):            # OrdLe
    if x == N: return True
    if y == T: return True
    if x == T or y == N: return False
    if x[0] == 'B' and y[0] == 'P': return False
    return le(x[1], y[1]) and le(x[2], y[2])

def canon(x):            # Canon
    if x in (N, T): return True
    if x[0] == 'P' and x[1] == N and x[2] == N: return False
    return canon(x[1]) and canon(x[2])

def topc(c):             # topC
    return 3 + topc(c[1]) + topc(c[2]) if isinstance(c, tuple) else 1

def pot(c, x):           # pot
    if x == T: return 0
    if x == N: return topc(c)
    return (2 if x[0] == 'P' else 1) + pot(ch(c), x[1]) + pot(ct(c), x[2])

if __name__ == '__main__':
    K, KC = int(sys.argv[1]), int(sys.argv[2])
    allsh = [s for k in range(K + 1) for s in shapes(k)]
    sh = [s for s in allsh if canon(s)]
    cp = [c for k in range(KC + 1) for c in capes(k)]
    tot = bad = {'climb': 0, 'canon': 0, 'pot': 0}
    bad = {'climb': 0, 'canon': 0, 'pot': 0}; tot = msgdown = 0; ex = {}
    for c in cp:
        for o in sh:
            for n in sh:
                tot += 1
                r = kept(n, o, c)
                if not le(o, r): bad['climb'] += 1; ex.setdefault('climb', (n, o, c, r))
                if not canon(r): bad['canon'] += 1; ex.setdefault('canon', (n, o, c, r))
                if not (r == o or pot(c, r) < pot(c, o)): bad['pot'] += 1; ex.setdefault('pot', (n, o, c, r))
                if not le(o, msg(n, o, c)): msgdown += 1
    nc = sum(1 for c in cp for o in allsh if not canon(o) for n in allsh
             if not le(o, kept(n, o, c)))
    print('canonical shapes', len(sh), 'capes', len(cp), 'triples', tot)
    print('failures', bad, '; plain msg falls on', msgdown)
    print('non-canonical entries (all new shapes) where kept falls:', nc)
    for k, (n, o, c, r) in ex.items(): print(k, show(n), show(o), show(c), '->', show(r))
