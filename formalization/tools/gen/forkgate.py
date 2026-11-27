"""Cut the gates `fkGF` and `fkGB` of the trap of `+fork` (as written in
lemmas/Compiler/CompForkGen.lean) into the chains of their pushes.

    tools/capped.sh -m 3G python3 tools/gen/forkgate.py OUTFILE

Each gate is a chain of pushes: `=^` (`[7 [0 1] [8 A [7 E [7 [[0 4] [0 3]]
REST]]]]`), `=.` (`[7 [10 ..] REST]`) and `[7 [0 1] REST]`; the rest after
each push is named `<gate><i>` (`fkGF0` is the whole gate), so that
`fkGF = fkGF0` is a `rfl` fact and a proof can open the chain one push at a
time: a crash at a push leaves the rest a constant, which `simp` does not
open.  Writes the definitions to OUTFILE between `-- BEGIN forkgate` and
`-- END forkgate` and prints the chains."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import parse
OUT = sys.argv[1]
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'lemmas', 'Compiler', 'CompForkGen.lean')
text = open(SRC).read()

def body(name):
    m = re.search(r'^def %s : Noun :=\n  (.*)$' % name, text, re.M)
    return parse(m.group(1))

def sl(ax, n):
    for b in bin(ax)[3:]:
        if n is None or n[0] != 'C':
            return None
        n = n[1] if b == '0' else n[2]
    return n

def isA(n, v):
    return n is not None and n[0] == 'A' and n[1] == v

ID = ('C', ('A', 0), ('A', 1))
SW = ('C', ('C', ('A', 0), ('A', 4)), ('C', ('A', 0), ('A', 3)))

def step(n):
    if isA(sl(2, n), 7) and sl(6, n) == ID and isA(sl(14, n), 8):
        r = sl(31, n)
        if isA(sl(2, r), 7) and isA(sl(14, r), 7) and sl(30, r) == SW:
            return ('=^', sl(31, r))
    if isA(sl(2, n), 7) and sl(6, n) == ID:
        return ('id', sl(7, n))
    if isA(sl(2, n), 7) and isA(sl(12, n), 10):
        return ('=.', sl(7, n))
    return None

def show(n, subs):
    if id(n) in subs:
        return subs[id(n)]
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    if n[0] == 'R':
        return n[1]
    return '(C %s %s)' % (show(n[1], subs), show(n[2], subs))

out = []
for gate in ['fkGF', 'fkGB']:
    n = body(gate)
    parts = [n]
    kinds = []
    while True:
        s = step(parts[-1])
        if s is None:
            break
        kinds.append(s[0])
        parts.append(s[1])
    print('--', gate, len(parts), 'parts:', ' '.join(kinds))
    subs = {}
    defs = []
    for i in range(len(parts) - 1, -1, -1):
        p = parts[i]
        nm = '%s%d' % (gate, i)
        defs.append('def %s : Noun :=\n  %s' % (nm, show(p, subs)))
        subs[id(p)] = nm
    out.extend(defs)
text_out = '\n\n'.join(out) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN forkgate\n') + len('-- BEGIN forkgate\n')
e = src.index('-- END forkgate')
open(OUT, 'w').write(src[:b] + '\n' + text_out + '\n' + src[e:])
print('-- wrote', len(out), 'definitions,', len(text_out), 'characters')
