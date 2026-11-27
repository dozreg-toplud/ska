#!/usr/bin/env python3
# The 6 soft calls of the corpus: p, q, whether +soft-bond fired, req.  Usage (from formalization/):
#   python3 tools/gen/softcorpus.py lemmas/Ska/SccLoopRealData.lean
import re, sys
sys.setrecursionlimit(100000)
F = sys.argv[1]
txt = open(F).read()
recs = re.split(r'\ndef r\d+ : DoneRec where', txt)[1:]

def parse(t):
    toks = re.findall(r'\[|\]|[0-9]+', t)
    pos = [0]
    def one():
        x = toks[pos[0]]; pos[0] += 1
        if x == '[':
            xs = []
            while toks[pos[0]] != ']':
                xs.append(one())
            pos[0] += 1
            r = xs[-1]
            for y in reversed(xs[:-1]):
                r = (y, r)
            return r
        return int(x)
    return one()

def cord(n):
    s = b''
    while n:
        s += bytes([n & 255]); n >>= 8
    return s.decode('latin1')

def short(n, d=0):
    if isinstance(n, int):
        return str(n) if n < 2**16 else ('%' + cord(n) if all(32 <= c < 127 for c in n.to_bytes((n.bit_length()+7)//8, 'little')) else 'A')
    if d > 6:
        return '..'
    return '[' + short(n[0], d+1) + ' ' + short(n[1], d+1) + ']'

def tag(n):
    return n[0] if isinstance(n, tuple) else None

def kids(n):
    t = n[0]
    if isinstance(t, tuple):
        return [n[0], n[1]]
    b = n[1]
    if t == 0 or t == 1: return []
    if t == 2: return [b[0], b[1][0]]
    if t in (3, 4): return [b]
    if t in (5, 7, 12): return [b[0], b[1]]
    if t == 6: return [b[0], b[1][0], b[1][1]]
    if t == 10: return [b[0][1], b[1]]
    if t == 11:
        p = b[0]
        return ([p[1]] if isinstance(p, tuple) else []) + [b[1][0]]
    if t == cordnum('mean'): return [b[0], b[1][1][0]]
    raise Exception('tag %r' % t)

def cordnum(s):
    return int.from_bytes(s.encode(), 'little')

def calls(n, out, path):
    if isinstance(n[0], int) and n[0] == 2:
        info = n[1][1][1]
        out.append((path, n))
    if isinstance(n[0], int) and n[0] == cordnum('mean'):
        out.append((path, n))
    for i, k in enumerate(kids(n)):
        calls(k, out, path + [i])

def ntag(n):
    t = n[0]
    if isinstance(t, tuple): return 'cons'
    if t == cordnum('mean'): return 'mean'
    return str(t)

def nshape(n, d=0):
    """A nomm as a short tree of tags."""
    t = ntag(n)
    if t == '0': return '[0 %d]' % n[1]
    if t == '1': return '[1 ..]'
    if t == '2':
        info = n[1][1][1]
        if info == 0: inf = 'ind'
        else:
            k = info[1][1]
            inf = 'dir' + ('' if k == 0 else '+key')
        return '[2 %s %s %s]' % (nshape(n[1][0], d+1), nshape(n[1][1][0], d+1), inf)
    if d > 3: return '[%s ..]' % t
    return '[' + t + ' ' + ' '.join(nshape(k, d+1) for k in kids(n)) + ']'

for r in recs:
    def fld(name):
        m = re.search(r'\n  %s := (.*)' % name, r)
        return m.group(1) if m else None
    if fld('nosoft') != 'false':
        continue
    cs = fld('cs'); nomm = parse(fld('nomm').strip('"'))
    soft = re.findall(r'"([^"]*)"', fld('soft'))
    csoft = re.findall(r'"([^"]*)"', fld('csoft') or '[]')
    print('== case', cs, 'b', fld('b'))
    cl = []
    calls(nomm, cl, [])
    for s in soft:
        e = parse(s)
        o = e[0]; sc = e[1]
        kin, (b, (rin, (ned, (sur, (plain, (head, (last, (pro, (out, (aux, req))))))))))= sc
        print(' soft entry at o=%d kin=%s plain=%d head=%d last=%d bond fired=%s req=%s' % (
            o, cord(kin), plain, head, last, o != plain, 'empty' if req == 0 else short(req)))
        print('  ned', short(ned), ' sur', short(sur))
        for path, c in cl:
            if ntag(c) == '2' and c[1][1][1] != 0 and c[1][1][1][1][0] == b:
                print('  call at path', path, ':', nshape(c))
                print('   p =', nshape(c[1][0]))
                print('   q =', nshape(c[1][1][0]))
    for s in csoft:
        e = parse(s)
        req = e[1][1][1][1][1][1][1][1][1][1][1][1]
        print('  after coerce-lazy: req =', short(req))
    print(' member nomm:', nshape(nomm))
    print(' all calls:', [(p, nshape(c)) for p, c in cl])
