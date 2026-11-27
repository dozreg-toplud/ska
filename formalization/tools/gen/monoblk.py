"""Cut the `mono` `&` blocks of step `7` of the direct call (`crD7Nm`, read
from `lemmas/Compiler/CompRunDirectKN.lean`) at their `=^` pushes, for
`lemmas/Compiler/CompRunDirectMonoB.lean`.

    python3 tools/gen/monoblk.py OUT.lean

A push is `[7 [0 1] [8 V [7 E [7 F R]]]]`; writes the value of push `i`
(`crNMv<i>`), the rest from push `i` on (`crNMr<i>`) and the last part
(`crNML`), so that `crD7Nm = crNMr0` is a `kernel_rfl` fact."""
import re, sys, os
sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, '..', '..', 'lemmas', 'Compiler', 'CompRunDirectKN.lean')).read()

def lean_def(name):
    m = re.search(r'^def %s : Noun :=\n(.*?)\n\n' % name, src, re.S | re.M)
    return m.group(1)

def parse(text):
    toks = re.findall(r'\(|\)|C|A|0x[0-9a-fA-F]+|\d+|[A-Za-z_][A-Za-z0-9_]*', text)
    pos = [0]
    def go():
        t = toks[pos[0]]; pos[0] += 1
        if t == '(':
            k = toks[pos[0]]; pos[0] += 1
            if k == 'C':
                a = go(); b = go(); n = ('C', a, b)
            elif k == 'A':
                v = toks[pos[0]]; pos[0] += 1; n = ('A', int(v, 0))
            else:
                raise ValueError(k)
            assert toks[pos[0]] == ')'; pos[0] += 1
            return n
        return ('R', t)
    return go()

def sl(ax, n):
    for b in bin(ax)[3:]:
        n = n[1] if b == '0' else n[2]
    return n

def show(n):
    if n[0] == 'A':
        v = n[1]; return '(A %s)' % (hex(v) if v > 9999 else str(v))
    if n[0] == 'R':
        return n[1]
    return '(C %s %s)' % (show(n[1]), show(n[2]))

def cells(n): return 1 + cells(n[1]) + cells(n[2]) if n[0] == 'C' else 0

def is_push(n):
    try:
        return (sl(2, n) == ('A', 7) and sl(6, n) == ('C', ('A', 0), ('A', 1)) and sl(14, n) == ('A', 8)
                and sl(62, n) == ('A', 7) and sl(254, n) == ('A', 7))
    except (IndexError, TypeError):
        return False

def wrap(s, ind='    '):
    res = []; line = '  '
    for tok in s.split(' '):
        if len(line) + len(tok) + 1 > 112: res.append(line.rstrip()); line = ind
        line += tok + ' '
    res.append(line.rstrip()); return '\n'.join(res)

lines = []
for nm, d in [('crNM', 'crD7Nm')]:
    n = parse(lean_def(d)); parts = []
    while is_push(n):
        parts.append((sl(30, n), sl(126, n), sl(510, n))); n = sl(511, n)
    print(nm, len(parts), [cells(p[0]) for p in parts], cells(n))
    lines.append(f"/-- The last part of `{d}`. -/\ndef {nm}L : Noun :=\n" + wrap(show(n)) + "\n")
    for i, (v, e, f) in enumerate(parts):
        lines.append(f"/-- The value of push `{i}` of `{d}`. -/\ndef {nm}v{i} : Noun :=\n" + wrap(show(v)) + "\n")
    for i in reversed(range(len(parts))):
        v, e, f = parts[i]
        nxt = f"{nm}r{i+1}" if i + 1 < len(parts) else f"{nm}L"
        lines.append(f"def {nm}r{i} : Noun :=\n" + wrap(f"C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C {nm}v{i} (C (A 7) (C {show(e)} (C (A 7) (C {show(f)} {nxt})))))))") + "\n")
open(sys.argv[1], 'w').write('\n'.join(lines))
