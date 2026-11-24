"""The pill's nouns as Python tuples, parsed from the generated Lean files of
lemmas/Pill (Nouns/*.lean, Arm/*.lean): ('A', n), ('C', h, t), ('R', name).
`slot`, `show`, `lean` (a noun as a Lean literal), `arms` (the arms of a
battery with their axes), `contains_atom`, `cord`.  Import it from a script
in this directory and run it under tools/capped.sh."""
import re, sys, glob, os
sys.setrecursionlimit(1000000)
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'lemmas', 'Pill')
defs = {}
pat = re.compile(r'^(?:public )?def ([A-Za-z0-9_.]+) : Noun := (.*)$')
for f in glob.glob(ROOT + '/Nouns/*.lean') + glob.glob(ROOT + '/Arm/*.lean'):
    for line in open(f):
        m = pat.match(line)
        if m:
            defs[m.group(1)] = m.group(2)
tokre = re.compile(r'\(|\)|[A-Za-z_][A-Za-z0-9_.]*|0x[0-9a-fA-F]+|[0-9]+')
parsed = {}

def parse(text):
    toks = tokre.findall(text)
    pos = [0]
    def expr():
        t = toks[pos[0]]
        if t == '(':
            pos[0] += 1
            e = expr()
            assert toks[pos[0]] == ')'
            pos[0] += 1
            return e
        if t == 'C':
            pos[0] += 1
            a = expr(); b = expr()
            return ('C', a, b)
        if t == 'A':
            pos[0] += 1
            n = toks[pos[0]]; pos[0] += 1
            return ('A', int(n, 0))
        pos[0] += 1
        return ('R', t)
    return expr()

def get(name):
    if name not in parsed:
        parsed[name] = parse(defs[name])
    return parsed[name]

def norm(n):
    while n[0] == 'R':
        n = get(n[1])
    return n

def slot(ax, n):
    bits = bin(ax)[3:]
    for b in bits:
        n = norm(n)
        if n[0] != 'C':
            return None
        n = n[1] if b == '0' else n[2]
    return n

def show(n, depth=0, maxd=400, names=True):
    if names and n[0] == 'R':
        return n[1]
    n = norm(n)
    if n[0] == 'A':
        v = n[1]
        return hex(v) if v > 9999 else str(v)
    if depth > maxd:
        return '...'
    # right-assoc list printing
    parts = []
    while n[0] == 'C' and len(parts) < 200:
        parts.append(show(n[1], depth + 1, maxd, names))
        n2 = n[2]
        if names and n2[0] == 'R':
            parts.append(n2[1]); return '[' + ' '.join(parts) + ']'
        n = norm(n2)
    parts.append(show(n, depth + 1, maxd, names))
    return '[' + ' '.join(parts) + ']'

def cord(s):
    return int.from_bytes(s.encode(), 'little')

def contains_atom(n, v, seen=None, depth=0):
    stack = [n]
    vis = set()
    while stack:
        x = stack.pop()
        if x[0] == 'R':
            if x[1] in vis: continue
            vis.add(x[1]); stack.append(get(x[1])); continue
        if x[0] == 'A':
            if x[1] == v: return True
            continue
        stack.append(x[1]); stack.append(x[2])
    return False

def arms(bat, ax=1):
    """yield (axis, formula) of arms in a battery"""
    n = norm(bat)
    if n[0] != 'C': return
    h = norm(n[1])
    if h[0] == 'A':
        yield (ax, bat); return
    yield from arms(n[1], 2 * ax)
    yield from arms(n[2], 2 * ax + 1)

def lean(n, sub=None):
    """Lean text; sub maps id-free subterm text to names (by structural equality)"""
    n = norm(n)
    if sub is not None:
        for nm, t in sub:
            if eqn(n, t): return nm
    if n[0] == 'A':
        v = n[1]
        return '(A %s)' % (hex(v) if v > 9999 else str(v))
    return '(C %s %s)' % (lean(n[1], sub), lean(n[2], sub))

def eqn(a, b):
    a = norm(a); b = norm(b)
    if a is b: return True
    if a[0] != b[0]: return False
    if a[0] == 'A': return a[1] == b[1]
    return eqn(a[1], b[1]) and eqn(a[2], b[2])
