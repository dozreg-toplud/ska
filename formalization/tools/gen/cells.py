import sys
sys.path.insert(0, sys.argv[1])
from nouns import *
memo = {}
def cells(n):
    stack = [n]; 
    def go(n):
        if n[0] == 'R':
            k = n[1]
            if k not in memo: memo[k] = go(get(k))
            return memo[k]
        if n[0] == 'A': return 0
        return 1 + go(n[1]) + go(n[2])
    return go(n)
def calls(n, acc):
    # collect [9 ax [0 k]] patterns
    seen=set(); st=[n]
    while st:
        x=st.pop()
        if x[0]=='R':
            if x[1] in seen: continue
            seen.add(x[1]); st.append(get(x[1])); continue
        if x[0]=='A': continue
        h=norm(x[1]); t=norm(x[2])
        if h==('A',9) and t[0]=='C':
            a=norm(t[1]); r=norm(t[2])
            if a[0]=='A' and r[0]=='C' and norm(r[1])==('A',0) and norm(r[2])[0]=='A':
                acc.add((a[1], norm(r[2])[1]))
        st.append(x[1]); st.append(x[2])
    return acc
def core2bat(ax):
    b=bin(ax)[2:]; assert b[:2]=='10', ax
    return int('1'+b[2:],2)
def bat2core(ax):
    b=bin(ax)[2:]
    return int('10'+b[1:],2)
Kbat=('R','nh290d8f32435a'); door=('R','comp.door')
def armK(cax): return slot(core2bat(cax), Kbat)
def armD(bax): return slot(bax, door)
items = [('K', 'compile-scc-in', 2732), ('K', 'member (%compile-scc-fn)', 358182910), ('K','comp', 5590),
         ('K','need-soft', 5466), ('K','hinted', 96116)]
for w,nm,ax in items:
    a=armK(ax); print(w, nm, 'core axis', ax, 'cells', cells(a) if a else None)
for nm,ax in [('callee-need',221180),('callee-sure',4060),('callee-compiled',13791),('made',13814),('sound',13654)]:
    a=armD(ax); print('door', nm, 'battery axis', ax, 'core axis', bat2core(ax), 'cells', cells(a) if a else None)
    cs=calls(a,set()); print('   calls', sorted(cs)[:40])
print('---')
for nm,ax in [('sound-far',5467),('scc-of',96127)]:
    a=armK(ax); print('K', nm, ax, 'cells', cells(a) if a else None); print('   calls', sorted(calls(a,set()))[:30])
