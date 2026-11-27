"""The map of `+scc-of` (README Gaps 23, track P): the gate that arm `96127`
of axis `7` of the library (`corLib`, axis `15` of `cor`) builds, its `$`
arm cut into the chain of its pushes (`%8`, `%7`), each part with its cells
and the arms it calls (`[9 a [0 x]]`) and hints; then `+tarjan` (the arm the
roll calls) sized the same way.

    tools/capped.sh -m 3G python3 tools/gen/sccof.py tools/gen
"""
import sys
sys.path.insert(0, sys.argv[1])
from nouns import *
memo = {}
def cells(n):
    def go(n):
        if n[0] == 'R':
            k = n[1]
            if k not in memo: memo[k] = go(get(k))
            return memo[k]
        if n[0] == 'A': return 0
        return 1 + go(n[1]) + go(n[2])
    return go(n)
def calls(x):
    st=[x]; seen=set(); out=[]
    while st:
        y=st.pop()
        if y[0]=='R':
            if y[1] in seen: continue
            seen.add(y[1]); st.append(get(y[1])); continue
        if y[0]=='A': continue
        hh=norm(y[1]); tt=norm(y[2])
        if hh==('A',9) and tt[0]=='C':
            a=norm(tt[1]); r=norm(tt[2])
            if a[0]=='A' and r[0]=='C' and norm(r[1])==('A',0) and norm(r[2])[0]=='A':
                out.append((a[1], norm(r[2])[1]))
        if hh==('A',11) and tt[0]=='C':
            hn=norm(tt[1])
            if hn[0]=='C' and norm(hn[1])[0]=='A': out.append(('hint',norm(hn[1])[1]))
            elif hn[0]=='A': out.append(('hint',hn[1]))
        st.append(y[1]); st.append(y[2])
    return out
def nm(v):
    try:
        return bytes.fromhex(hex(v)[2:]).decode()[::-1] if v>255 else v
    except Exception: return v
def show_chain(n, depth=0, lim=60):
    n = norm(n); k = 0
    while n[0]=='C' and k < lim:
        h = norm(n[1]); t = norm(n[2])
        if h[0]=='A' and h[1] in (7,8) and t[0]=='C':
            b = t[1]; c = t[2]; cl = calls(b)
            print('  '*depth + f'op{h[1]} part cells {cells(b)}  calls {[(a,b2) for a,b2 in cl if a!="hint"][:10]} hints {[nm(b2) for a,b2 in cl if a=="hint"][:6]}')
            n = norm(c); k += 1
        else:
            print('  '*depth + f'rest cells {cells(n)} head {show(n, maxd=3)[:200]}'); return n
    print('  '*depth + f'rest cells {cells(n)}'); return n
cor = ('R','cor')
lib = slot(15, cor)
c7 = slot(7, lib)
arm = slot(96127, c7)
print('arm 96127 of axis 7 of corLib: cells', cells(arm), 'head', show(arm, maxd=4)[:300])
bat = slot(109, arm)
print('battery ($ arm) cells', cells(bat))
print('-- the chain of the battery:')
rest = show_chain(bat)
# the ?^ : [6 test yes no]
r = norm(rest)
if r[0]=='C' and norm(r[1])==('A',6):
    t = norm(r[2]); test = t[1]; yn = norm(t[2]); yes = yn[1]; no = yn[2]
    print('?^ test cells', cells(test), show(test, maxd=6)[:200])
    print('yes branch (the test is ?=(@ s): the cache miss) cells', cells(yes), show(yes, maxd=6)[:200])
    print('no branch (the cache hit [u.s sccs]) cells', cells(no))
    print('-- the chain of the hit branch:')
    show_chain(no, 1)
    print('-- the chain of the miss branch:')
    r2 = show_chain(yes, 1)
    # +tarjan: arm the roll calls; find [9 a [0 x]] calls with big arms in the miss branch
    for (a, x) in sorted(set(calls(yes))):
        if a == 'hint': continue
        print('  call arm', a, 'of axis', x)
# the roll's sample calls [9 2815 [0 255]] on the subject [sub [s gate]]:
# the gate's context c is at 31 there, so the core is axis 15 of c
y = norm(yes)
tc = slot(15, c7); ta = slot(2815, tc)
print('-- +tarjan: arm 2815 of axis 15 of c (axis 255 of the subject [sub [s gate]]): arm cells', cells(ta), show(ta, maxd=3)[:160])
print('   its calls:', sorted(set(x for x in calls(ta) if x[0] != 'hint')))
print('-- the sub loop (222 cells): its calls', sorted(set(x for x in calls(slot(6, y)) if x[0] != 'hint')))
