"""Cut the trap of `+mono-try-call` (door arm `437183`, the trap at axis
`56317` of the arm) into the parts of `lemmas/Compiler/CompRunDirectMono.lean`.

    tools/capped.sh -m 3G python3 tools/gen/monotry.py OUT.lean

The cell branch (`mtcPA`) and the `%both` branch (`mtcBO`, under the hint
`mtcBOh`) are each a chain of `=^` pushes `[7 [0 1] [8 V [7 E [7 F R]]]]`;
writes the value of each push (`<nm>v<i>`), the rest after it (`<nm>r<i>`),
the last part (`<nm>L`), and the three tests of the trap (`mtcT1` ..
`mtcY2`, `mtcT3`), as checked by `mtc_loop_eq`.  Prints the cell count of
each value."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)
from nouns import slot, norm
def full(n):
    n = norm(n)
    if n[0] == 'A': return n
    return ('C', full(n[1]), full(n[2]))
def show(n):
    if n[0]=='A':
        v=n[1]; return '(A %s)' % (hex(v) if v>9999 else str(v))
    return '(C %s %s)' % (show(n[1]), show(n[2]))
def sl(ax,n):
    for b in bin(ax)[3:]:
        n = n[1] if b=='0' else n[2]
    return n
door=('R','comp.door')
F = full(slot(437183, door))
L = sl(56317, F)
def cells(n): return 0 if n[0]=='A' else 1+cells(n[1])+cells(n[2])
def is_push(n):
    try:
        return (sl(2,n)==('A',7) and sl(6,n)==('C',('A',0),('A',1)) and sl(14,n)==('A',8) and sl(62,n)==('A',7)
                and sl(254,n)==('A',7) and sl(126,n)[0]=='C' and sl(252,n)[1]==('A',10) if False else
                sl(2,n)==('A',7) and sl(6,n)==('C',('A',0),('A',1)) and sl(14,n)==('A',8) and sl(62,n)==('A',7) and sl(254,n)==('A',7))
    except Exception:
        return False
out=[]
def chain(name, n):
    k=0; parts=[]
    while is_push(n):
        v = sl(30, n); e = sl(126, n); f = sl(510, n); r = sl(511, n)
        parts.append((v, e, f)); n = r; k += 1
    return parts, n
PAIR = sl(1022, L); BOTH = sl(1023, L)
assert sl(2, BOTH) == ('A', 11)
BB = sl(7, BOTH)
for nm, n in [('mtcPA', PAIR), ('mtcBO', BB)]:
    parts, last = chain(nm, n)
    print(nm, len(parts), [cells(p[0]) for p in parts], cells(last))
    for i,(v,e,f) in enumerate(parts):
        print('  E', show(e), 'F', show(f))
    out.append((nm, parts, last))
# emit lean
lines=[]
def wrap(s, ind='    '):
    res=[]; line='  '
    for tok in s.split(' '):
        if len(line)+len(tok)+1>112: res.append(line.rstrip()); line=ind
        line+=tok+' '
    res.append(line.rstrip()); return '\n'.join(res)
for nm, parts, last in out:
    n=len(parts)
    lines.append(f"/-- The last part of `{nm}`. -/\ndef {nm}L : Noun :=\n" + wrap(show(last)) + "\n")
    for i,(v,e,f) in enumerate(parts):
        lines.append(f"/-- The value of push `{i}` of `{nm}`. -/\ndef {nm}v{i} : Noun :=\n" + wrap(show(v)) + "\n")
    for i in reversed(range(n)):
        v,e,f = parts[i]
        nxt = f"{nm}r{i+1}" if i+1<n else f"{nm}L"
        lines.append(f"def {nm}r{i} : Noun :=\n  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C {nm}v{i} (C (A 7) (C {show(e)} (C (A 7) (C {show(f)} {nxt})))))))\n")
lines.append("/-- The tag and clue of the hint of the `%both` branch. -/\ndef mtcBOh : Noun :=\n" + wrap(show(sl(6, BOTH))) + "\n")
for nm,ax in [('mtcT1',6),('mtcY1',14),('mtcT2',62),('mtcY2',126),('mtcT3',510)]:
    lines.append(f"def {nm} : Noun :=\n" + wrap(show(sl(ax, L))) + "\n")
open(sys.argv[1],'w').write('\n'.join(lines))
