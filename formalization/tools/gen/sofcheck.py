"""The models of `+sound-far`, `+need-soft`, `+need-ord-edit` (lemmas/Ska/SofModel.lean)
against the real compiler (README Gaps 19, item (f)).

    python3 tools/gen/sofcheck.py hoon > tools/hoon/sofcheck.hoon
    tools/hoon/runhoon.sh tools/hoon/sofcheck.hoon 600 > tools/hoon/sofcheck.txt
    python3 tools/gen/sofcheck.py lean tools/hoon/sofcheck.txt > lemmas/Ska/SofModelCheck.lean

The cases are drawn from a fixed seed: nomms with cons, `%6`, `%7`, `%10`, `%11`,
`%mean`, direct `%2` into a code table of four bells whose nomms call each other
(recursion past depth 3), needs with `%both`, cells, `%this`, `%none`, socks with
cell capes.  The driver slams each gate on a raw noun (`.*` of the gate core with
the sample replaced), so no library type is used in the test (`fuse-loop`), and
prints `[%sf i r]`, `[%ns i r]`, `[%ne i (jam r)]`."""
import sys, random

T = {'none': 0x656e6f6e, 'this': 0x73696874, 'both': 0x68746f62, 'mean': 0x6e61656d,
     'void': 0x64696f76, 'spot': 0x746f7073, 'memo': 0x6f6d656d, 'slog': 0x676f6c73}
R = random.Random(20261127)

# ---- values: ('pair',a,b) ('both',a,b) ('this',) ('none',)
def need(d):
    if d == 0:
        return R.choice([('none',), ('this',), ('this',)])
    c = R.random()
    if c < 0.15: return ('none',)
    if c < 0.3: return ('this',)
    if c < 0.65: return ('pair', need(d - 1), need(d - 1))
    return ('both', need(d - 1), need(d - 1))

def noun(d):
    if d == 0 or R.random() < 0.4:
        return R.choice([0, 1, 2, 3, 7, 42, 1000])
    return (noun(d - 1), noun(d - 1))

def cape(d):
    if d == 0 or R.random() < 0.5:
        return R.choice(['yes', 'no'])
    return ('cell', cape(d - 1), cape(d - 1))

def sock(d):
    return ('mk', cape(d), noun(d + 1))

BELLS = [(('mk', 'yes', 0), (1, i)) for i in range(4)]

def nomm(d, bells=True):
    if d == 0:
        return R.choice([('n0', R.choice([0, 1, 2, 3, 6, 7])), ('n1', noun(1))])
    ops = ['cons'] * 4 + ['n0', 'n1', 'n3', 'n4', 'n5', 'n12'] + ['n6'] * 2 + ['n7'] * 2 + ['n10'] * 3 + \
          ['n11s', 'n11d', 'mean'] + (['n2b'] * 4 if bells else []) + ['n2']
    o = R.choice(ops)
    s = lambda: nomm(d - 1, bells)
    if o == 'cons': return ('cons', s(), s())
    if o == 'n0': return ('n0', R.choice([0, 1, 2, 3, 6, 7, 14]))
    if o == 'n1': return ('n1', noun(2))
    if o in ('n3', 'n4'): return (o, s())
    if o in ('n5', 'n12', 'n7'): return (o, s(), s())
    if o == 'n6': return ('n6', s(), s(), s())
    if o == 'n10': return ('n10', R.choice([1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 29]), s(), s())
    if o == 'n11s': return ('n11s', R.choice([T['spot'], T['memo']]), s(), noun(1))
    if o == 'n11d': return ('n11d', R.choice([T['slog'], T['spot']]), s(), s(), noun(1))
    if o == 'mean': return ('mean', s(), BELLS[0], s(), noun(1), R.choice([None, 5]))
    if o == 'n2': return ('n2', s(), s(), None)
    return ('n2', s(), s(), (R.choice(BELLS), R.choice([None, None, 3])))

# ---- nouns
def unit(x): return 0 if x is None else (0, x)
def capeN(c):
    if c == 'yes': return 0
    if c == 'no': return 1
    return (capeN(c[1]), capeN(c[2]))
def sockN(s): return T['void'] if s == 'void' else (capeN(s[1]), s[2])
def bellN(b): return (sockN(b[0]), b[1])
def needN(n):
    if n[0] == 'pair': return (needN(n[1]), needN(n[2]))
    if n[0] == 'both': return (T['both'], (needN(n[1]), needN(n[2])))
    return (T[n[0]], 0)
def nommN(m):
    o = m[0]
    if o == 'cons': return (nommN(m[1]), nommN(m[2]))
    if o == 'n0': return (0, m[1])
    if o == 'n1': return (1, m[1])
    if o == 'n2':
        inf = None if m[3] is None else (bellN(m[3][0]), unit(m[3][1]))
        return (2, (nommN(m[1]), (nommN(m[2]), unit(inf))))
    if o == 'n3': return (3, nommN(m[1]))
    if o == 'n4': return (4, nommN(m[1]))
    if o == 'n5': return (5, (nommN(m[1]), nommN(m[2])))
    if o == 'n6': return (6, (nommN(m[1]), (nommN(m[2]), nommN(m[3]))))
    if o == 'n7': return (7, (nommN(m[1]), nommN(m[2])))
    if o == 'n10': return (10, ((m[1], nommN(m[2])), nommN(m[3])))
    if o == 'n11s': return (11, (m[1], (nommN(m[2]), m[3])))
    if o == 'n11d': return (11, ((m[1], nommN(m[2])), (nommN(m[3]), m[4])))
    if o == 'n12': return (12, (nommN(m[1]), nommN(m[2])))
    if o == 'mean': return (T['mean'], (nommN(m[1]), (bellN(m[2]), (nommN(m[3]), (m[4], unit(m[5]))))))
    raise Exception(o)

def hoonA(n):
    s = str(n)
    out = ''
    while len(s) > 3:
        out = '.' + s[-3:] + out; s = s[:-3]
    return s + out
def hoonN(n):
    return hoonA(n) if isinstance(n, int) else '[%s %s]' % (hoonN(n[0]), hoonN(n[1]))

# ---- Lean
def leanN(n):
    return '(A %d)' % n if isinstance(n, int) else '(C %s %s)' % (leanN(n[0]), leanN(n[1]))
def leanCape(c):
    if c == 'yes': return 'Cape.yes'
    if c == 'no': return 'Cape.no'
    return '(Cape.cell %s %s)' % (leanCape(c[1]), leanCape(c[2]))
def leanSock(s): return 'Sock.void' if s == 'void' else '(Sock.mk %s %s)' % (leanCape(s[1]), leanN(s[2]))
def leanBell(b): return '(Bell.mk %s %s)' % (leanSock(b[0]), leanN(b[1]))
def leanNeed(n):
    if n[0] == 'pair': return '(NeedOrd.pair %s %s)' % (leanNeed(n[1]), leanNeed(n[2]))
    if n[0] == 'both': return '(NeedOrd.both %s %s)' % (leanNeed(n[1]), leanNeed(n[2]))
    return 'NeedOrd.' + n[0]
def leanOpt(x, f): return 'Option.none' if x is None else '(some %s)' % f(x)
def leanNomm(m):
    o = m[0]; L = leanNomm
    if o == 'cons': return '(Nomm.cons %s %s)' % (L(m[1]), L(m[2]))
    if o == 'n0': return '(Nomm.n0 %d)' % m[1]
    if o == 'n1': return '(Nomm.n1 %s)' % leanN(m[1])
    if o == 'n2':
        inf = leanOpt(m[3], lambda i: '(%s, %s)' % (leanBell(i[0]), leanOpt(i[1], lambda k: leanN(k))))
        return '(Nomm.n2 %s %s %s)' % (L(m[1]), L(m[2]), inf)
    if o in ('n3', 'n4'): return '(Nomm.%s %s)' % (o, L(m[1]))
    if o in ('n5', 'n7', 'n12'): return '(Nomm.%s %s %s)' % (o, L(m[1]), L(m[2]))
    if o == 'n6': return '(Nomm.n6 %s %s %s)' % (L(m[1]), L(m[2]), L(m[3]))
    if o == 'n10': return '(Nomm.n10 %d %s %s)' % (m[1], L(m[2]), L(m[3]))
    if o == 'n11s': return '(Nomm.n11s %d %s %s)' % (m[1], L(m[2]), leanN(m[3]))
    if o == 'n11d': return '(Nomm.n11d %d %s %s %s)' % (m[1], L(m[2]), L(m[3]), leanN(m[4]))
    if o == 'mean':
        return '(Nomm.mean %s %s %s %s %s)' % (L(m[1]), leanBell(m[2]), L(m[3]), leanN(m[4]),
                                               leanOpt(m[5], lambda k: leanN(k)))
    raise Exception(o)

# ---- the cases
CODE = [(b, nomm(3)) for b in BELLS]
CODE[0] = (BELLS[0], ('cons', ('n2', ('n0', 1), ('n1', 0), (BELLS[0], None)), ('n0', 3)))  # recurses forever
CODE[1] = (BELLS[1], ('n6', ('n0', 2), ('n2', ('n0', 1), ('n1', 0), (BELLS[2], None)), ('cons', ('n0', 2), ('n0', 3))))
SF = []
for i in range(70):
    nm = nomm(R.choice([1, 2, 3, 4]))
    if i < 6:
        nm = ('n2', ('n0', 1), ('n1', 0), (BELLS[i % 4], None))
    SF.append((nm, need(R.choice([1, 2, 3])), R.choice([0, 1, 2, 3, 3, 3, 4])))
NS = []
for i in range(60):
    k = sock(R.choice([0, 1, 2, 3]))
    ned = need(R.choice([1, 2, 3]))
    if i < 3: k = 'void'; ned = R.choice([('none',), ('this',)])
    NS.append((ned, need(R.choice([0, 1, 2, 3])), k))
NE = []
for i in range(60):
    NE.append((R.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 23, 29, 40, 63, 64]), need(R.choice([1, 2, 3, 4]))))

def cue(a):
    bits = bin(a)[2:][::-1] if a else ''
    pos = [0]; refs = {}
    def rd(n):
        v = 0
        for j in range(n): v |= (int(bits[pos[0] + j]) if pos[0] + j < len(bits) else 0) << j
        pos[0] += n; return v
    def mat():
        if bits[pos[0]] == '1': pos[0] += 1; return 0
        z = 0
        while bits[pos[0] + z] == '0': z += 1
        pos[0] += z + 1
        b = rd(z - 1) | (1 << (z - 1)) if z > 1 else 1
        return rd(b)
    def go():
        p = pos[0]
        if bits[pos[0]] == '0':
            pos[0] += 1; v = mat(); refs[p] = v; return v
        pos[0] += 1
        if bits[pos[0]] == '0':
            pos[0] += 1; h = go(); t = go(); refs[p] = (h, t); return (h, t)
        pos[0] += 1; return refs[mat()]
    return go()
def needOf(n):
    if isinstance(n[0], tuple): return ('pair', needOf(n[0]), needOf(n[1]))
    if n[0] == T['both']: return ('both', needOf(n[1][0]), needOf(n[1][1]))
    if n[0] == T['this']: return ('this',)
    assert n[0] == T['none'], n
    return ('none',)

if sys.argv[1] == 'hoon':
    print(':: The models of +sound-far, +need-soft, +need-ord-edit (lemmas/Ska/SofModel.lean) against')
    print(':: the compiler: written by tools/gen/sofcheck.py; each gate slammed on a raw noun.')
    print('=/  sf  sound-far')
    print('=/  ns  need-soft')
    print('=/  ne  need-ord-edit')
    print('=/  cod=(map * *)')
    print('  %-  malt')
    print('  ^-  (list [* *])')
    print('  :~  ' + '\n      '.join('[%s [%s 0 0]]' % (hoonN(bellN(b)), hoonN(nommN(m))) for b, m in CODE))
    print('  ==')
    print('=/  sfc=(list [@ * * @])')
    print('  :~  ' + '\n      '.join('[%d %s %s %d]' % (i, hoonN(nommN(m)), hoonN(needN(n)), d) for i, (m, n, d) in enumerate(SF)))
    print('  ==')
    print('=/  nsc=(list [@ * * *])')
    print('  :~  ' + '\n      '.join('[%d %s %s %s]' % (i, hoonN(needN(n)), hoonN(needN(s)), hoonN(sockN(k))) for i, (n, s, k) in enumerate(NS)))
    print('  ==')
    print('=/  nec=(list [@ @ *])')
    print('  :~  ' + '\n      '.join('[%d %d %s]' % (i, a, hoonN(needN(n))) for i, (a, n) in enumerate(NE)))
    print('  ==')
    print('''=.  sfc
  |-  ?~  sfc  ~
  ~&  [%sf -.i.sfc .*([-.sf [[+<.i.sfc +>-.i.sfc cod +>+.i.sfc] +>.sf]] -.sf)]
  $(sfc t.sfc)
=.  nsc
  |-  ?~  nsc  ~
  ~&  [%ns -.i.nsc .*([-.ns [+.i.nsc +>.ns]] -.ns)]
  $(nsc t.nsc)
=.  nec
  |-  ?~  nec  ~
  ~&  [%ne -.i.nec (jam .*([-.ne [+.i.nec +>.ne]] -.ne))]
  $(nec t.nec)
0''')
elif sys.argv[1] == 'lean':
    import re
    res = {}
    for m in re.finditer(r'\[\s*%(sf|ns|ne)\s+([0-9.]+)\s+([0-9.]+)\s*\]', open(sys.argv[2]).read()):
        key = (m.group(1), int(m.group(2).replace('.', '')))
        val = int(m.group(3).replace('.', ''))
        assert res.get(key, val) == val, key  # the harness evaluates twice
        res[key] = val
    assert len(res) == len(SF) + len(NS) + len(NE), len(res)
    out = ['import lemmas.Ska.SofModel', '', '/-!',
           '# `+sound-far`, `+need-soft`, `+need-ord-edit` against the compiler',
           '',
           'Written by `tools/gen/sofcheck.py` from `tools/hoon/sofcheck.txt`, the output of',
           '`tools/hoon/sofcheck.hoon` on the real compiler (`runhoon.sh`): %d cases of' % len(SF),
           '`+sound-far` on the code table `sfCod` (four bells; `sfCod0` calls itself), %d of' % len(NS),
           '`+need-soft`, %d of `+need-ord-edit`; each `#guard` says the model gives the' % len(NE),
           'product of the compiler\'s arm.', '-/', '',
           'namespace Formalization', 'namespace SkaModel', 'namespace Comp', '', 'open Nock', '',
           '/-- The code table of the cases: four bells and their nomms. -/',
           'def sfCodL : List (Bell × Nomm) := [']
    out.append(',\n'.join('  (%s, %s)' % (leanBell(b), leanNomm(m)) for b, m in CODE) + ']')
    out += ['', 'def sfCod (b : Bell) : Option Nomm := (sfCodL.find? (·.1 == b)).map (·.2)', '']
    nt = {0: 'true', 1: 'false'}
    for i, (m, n, d) in enumerate(SF):
        out.append('#guard soundFar sfCod %d %s %s = some %s' % (d, leanNomm(m), leanNeed(n), nt[res[('sf', i)]]))
    out.append('')
    for i, (n, s, k) in enumerate(NS):
        out.append('#guard needSoft %s %s %s = some %s' % (leanNeed(n), leanNeed(s), leanSock(k), nt[res[('ns', i)]]))
    out.append('')
    for i, (a, n) in enumerate(NE):
        r = cue(res[('ne', i)])
        out.append('#guard needOrdEdit %d %s = some (%s, %s)' % (a, leanNeed(n), leanNeed(needOf(r[0])), leanNeed(needOf(r[1]))))
    out += ['', 'end Comp', 'end SkaModel', 'end Formalization']
    print('\n'.join(out))
    trues = sum(1 for i in range(len(SF)) if res[('sf', i)] == 0)
    sys.stderr.write('sf: %d yes of %d; ns: %d yes of %d\n' % (trues, len(SF),
        sum(1 for i in range(len(NS)) if res[('ns', i)] == 0), len(NS)))
