"""The cut of `++  tarjan` (track Q): the arm `2815` of axis `15` of the core
of `+scc-of` (`sccCore`, axis `7` of the library; `sccCore = compK`), 837
cells, cut into its parts by axis, each with its cells and the arms it calls
(`[9 a [0 x]]`, named by the arm files of `lemmas/Pill/Arm`).

    tools/capped.sh -m 3G python3 tools/gen/tarjancut.py tools/gen

Prints the table; the axes are those of `lemmas/Compiler/CompTarjanCut.lean`
(each part a `getD` slot of `tjArm`, its shape checked there by
`kernel_rfl`)."""
import sys, os, re, glob
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
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
# arm names by axis, from the arm files
ROOTD = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'lemmas', 'Pill', 'Arm')
names = {}
for f in glob.glob(ROOTD + '/*.lean'):
    s = open(f).read()
    for m in re.finditer(r'abbrev ([A-Za-z0-9_.]*)\.axis\s*:\s*Nat\s*:=\s*(\d+)', s):
        names.setdefault(int(m.group(2)), []).append(m.group(1))
def calls(x):
    st = [x]; out = []
    while st:
        y = norm(st.pop())
        if y[0] == 'A': continue
        hh = norm(y[1]); tt = norm(y[2])
        if hh == ('A', 9) and tt[0] == 'C':
            a = norm(tt[1]); r = norm(tt[2])
            if a[0] == 'A' and r[0] == 'C' and norm(r[1]) == ('A', 0) and norm(r[2])[0] == 'A':
                out.append((a[1], norm(r[2])[1]))
        st.append(y[1]); st.append(y[2])
    return out
def nm(a):
    return '/'.join(names.get(a, ['?']))
def row(label, ax, n):
    cl = sorted(set(calls(n)))
    cs = ', '.join(f'{nm(a)}({a}@{x})' for a, x in cl if a != 2)
    print(f'{label:12s} {ax:>16} cells {cells(n):4d}  {cs}')
cor = ('R', 'cor'); lib = slot(15, cor); sc = slot(7, lib); tc = slot(15, sc)
arm = slot(2815, tc)

def subs(f, a):
    """the subformulas of the formula f at axis a"""
    f = norm(f)
    if f[0] != 'C': return []
    op = norm(f[1]); r = norm(f[2])
    if op[0] == 'C':
        return [(f[1], 2*a), (f[2], 2*a+1)]
    o = op[1]
    if r[0] != 'C':
        return []
    if o in (2, 5, 7, 8):
        return [(r[1], 4*a+2), (r[2], 4*a+3)]
    if o in (3, 4):
        return [(f[2], 2*a+1)]
    if o == 6:
        cd = norm(r[2])
        return [(r[1], 4*a+2)] + ([(cd[1], 8*a+6), (cd[2], 8*a+7)] if cd[0] == 'C' else [])
    if o == 9:
        return [(r[2], 4*a+3)]
    if o == 10:
        xh = norm(r[1])
        return ([(xh[2], 8*a+5)] if xh[0] == 'C' else []) + [(r[2], 4*a+3)]
    if o == 11:
        h = norm(r[1])
        return ([(h[2], 8*a+5)] if h[0] == 'C' else []) + [(r[2], 4*a+3)]
    if o == 1 and cells(f[2]) > 20:
        return [(f[2], 2*a+1)]
    return []
def opn(f):
    f = norm(f)
    if f[0] != 'C': return 'atom'
    op = norm(f[1])
    if op[0] == 'C': return 'cons'
    return str(op[1])
def walk(f, a, d, th):
    if cells(f) < th: return
    cl = sorted(set(calls(f)))
    cs = ' '.join(f'{nm(x)}({x}@{y})' for x, y in cl if x != 2)
    print('  '*d + f'[{opn(f)}] axis {a} cells {cells(f)}  {cs[:150]}')
    for g, b in subs(f, a):
        walk(g, b, d+1, th)
# the parts: (name, parent, axis in the parent)
ana = slot(15, sc)
PARTS = [
  ('tjArm', 'ana', 2815),       # [8 [1 0] [1 tjBat] 0 1]: the gate, sample bunt 0
  ('tjBat', 'tjArm', 29),       # [7 [0 1] 7 [0 1] 7 tjRun 0 31]: fin of the rep
  ('tjRun', 'tjBat', 126),       # [8 tjRepDoor 9 2 10 [6 tjOGate] 0 2]: ~(rep by g) slammed
  ('tjRepDoor', 'tjRun', 6),    # ~(rep by g): arm 767 of the door by
  ('tjOGate', 'tjRun', 253),    # [7 [0 3] 8 tjSamB [1 tjOBat] 0 1]: the gate of the rep
  ('tjSamB', 'tjOGate', 30),    # its sample's bunt [[v kids] gen]: the molds
  ('tjOBat', 'tjOGate', 125),   # [6 tjHasV [0 13] tjElse]: ?: (~(has by vis.acc) v) acc
  ('tjHasV', 'tjOBat', 6),
  ('tjElse', 'tjOBat', 15),     # [7 [8 [1 tjConn] 9 2 0 1] 0 3]: =< + |-
  ('tjConn', 'tjElse', 53),     # the trap connect
  ('tjEnter', 'tjConn', 126),   # the edit of acc: idx, vis, stk, cur
  ('tjKidsRep', 'tjConn', 2046),  # =^ lowest acc (~(rep in kids) gate)
  ('tjKGate', 'tjKidsRep', 1021), # [7 [0 3] 8 tjKSam [1 tjKBat] 0 1]
  ('tjKSam', 'tjKGate', 30),    # [[bunt-of-vertex index] acc]
  ('tjKBat', 'tjKGate', 125),   # [8 tjKGet 6 test tjKUnvis tjKVis]
  ('tjKGet', 'tjKBat', 6),      # (~(get by vis.acc) kid)
  ('tjKUnvis', 'tjKBat', 62),   # the recursion connect(v kid, kids (~(get ju g) kid), acc acc)
  ('tjKVis', 'tjKBat', 63),     # :_ acc ?. (~(has in cur.acc) kid) lowest (min lowest u.kid-idx)
  ('tjAfter', 'tjConn', 2047),  # :- lowest ?. =(index lowest) acc pop
  ('tjPopBr', 'tjAfter', 510),  # =< acc(fin [done fin.acc]) =| out |-
  ('tjPopBat', 'tjPopBr', 221), # the pop loop
]
OPAQUE = {'tjSamB', 'tjKSam'}
def part_nouns():
    N = {'ana': ana}
    for nm_, par, ax in PARTS:
        N[nm_] = slot(ax, N[par])
    return N
def gen_lean():
    N = part_nouns()
    out = []
    for nm_, par, ax in PARTS:
        out.append(f'/-- axis `{ax}` of `{par}`, {cells(N[nm_])} cells. -/')
        out.append(f'def {nm_} : Noun := (slot? {ax} {par}).getD (A 0)')
    out.append('')
    for nm_, par, ax in PARTS:
        if nm_ in OPAQUE: continue
        kids = [(k, N[k]) for k, p, a in PARTS if p == nm_]
        if not kids and cells(N[nm_]) > 160: continue
        out.append(f'theorem {nm_}_eq : {nm_} = {lean(N[nm_], kids)} := by kernel_rfl')
    return '\n'.join(out)
if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[2] == 'lean':
        print(gen_lean()); sys.exit(0)
    N = part_nouns()
    for nm_, par, ax in PARTS:
        row(nm_, f'{ax}@{par}', N[nm_])
    if len(sys.argv) > 2:
        th = int(sys.argv[2])
        walk(arm, 1, 0, th)
