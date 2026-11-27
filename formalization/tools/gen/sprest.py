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
ana = ('R','ana')
sp = slot(44826492927, ana)
print('spRest cells', cells(sp))
# walk the top-level chain of %8 / %7 pushes and print each pushed part's size and first calls
def show(n, depth=0, lim=40):
    n = norm(n)
    k = 0
    while n[0]=='C' and k < lim:
        h = norm(n[1]); t = norm(n[2])
        if h[0]=='A' and h[1] in (7,8) and t[0]=='C':
            b = t[1]; c = t[2]
            cs=set()
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
            cl = calls(b)
            def nm(v):
                try:
                    return bytes.fromhex(hex(v)[2:]).decode()[::-1] if v>255 else v
                except Exception: return v
            print('  '*depth + f'op{h[1]} part cells {cells(b)}  calls {[ (a,b2) for a,b2 in cl if a!="hint"][:8]} hints {[nm(b2) for a,b2 in cl if a=="hint"][:6]}')
            n = norm(c); k += 1
        else:
            print('  '*depth + f'rest cells {cells(n)}'); return
    print('  '*depth + f'rest cells {cells(n)}')
show(sp)
