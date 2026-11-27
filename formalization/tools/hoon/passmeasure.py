#!/usr/bin/env python3
# usage: passmeasure.py OUTDIR [seed]   then, for each driver OUTDIR/ck-*.hoon,
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck-X.hoon 1500 > out-X.txt
#   tools/hoon/passmeasure.py --sum out-X.txt
# The measure of the pass loop of +analyze (lemmas/Ska/PassLoop.lean, README Gaps 16) on the
# real compiler.  The instrumented copy of the library prints:
#   [%pm-run mug first lc pr map-eq in sk changed moved]   at the end of every +run: the class of
#        the change of less-code and of the product (+huge:so both ways: %eq, %eqv (both ways but
#        not equal), %more (the new one knows more), %less, %x (incomparable)), whether the map is
#        unchanged, the class of indi and seek (inclusion of capes by +lack:ca), `changed`, and
#        whether the identity is in .moved
#   [%pm-a mug prod old-map new-map]   a run that changed only the map (open point (a))
#   [%pm-bad tag mug old new]          less-code that did not grow, a product that gained
#   [%pm-new mug index depth]          +analyze of an identity not in the graph (depth: stack)
#   [%pm-pass mug pass members next depth], [%pm-end mug pass changed found]
#   [%pm-cull mug dead-mugs]           +cull dropped members (open point (b) when one is new'd again)
# The drivers: ck-hand (621 swapped/rotated self-calls, mutual recursions, products run as formulas),
# ck-thread (thread-a/b/c, unknown and known subject), ck-rnd0..3 (400 random recursive cores),
# ck-crn0..4 (500 cores whose products are cores called again), ck-zrx0..3 (400 roots calling a member
# on the product of their own recursive call, then another on its product), and passmeasure-lib.hoon
# beside this script (21 library calls with the library as a known subject).  On 2026-11-27 (seed 1,
# 2,269 calls of +ska-callgraph): 6,473 runs after an entry's first, 5,156 passes, 6,838 functions;
# less-code never shrank, 6 times it went from [[& &] |] to [& |] (same nouns); the product never
# gained; 151 runs changed only the map (100 with the product |+~, the map an axis to ~; 51 with a
# known cell: provenance lost under a | of the cape, or spelled out along its cells); no run broke the
# lexicographic order; 21 members culled, none analysed again; at most 62 passes (a chain of new
# functions up to he-threshold), stack depth at most 366 (ream).  Lean: lemmas/Ska/PassMeasure.lean.
import os, re, sys, random
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))

def summarize(path):
    raw = []
    for l in open(path).read().split('\n'):
        if l[:1] in (' ', '\t') and raw:
            raw[-1] += ' ' + l.strip()   # a print wrapped by the pretty printer
        else:
            raw.append(l)
    raw = [re.sub(r'\s+', ' ', l).replace('[ %pm', '[%pm') for l in raw]
    ls = [l.strip() for l in raw if l.startswith('[%pm') or l.startswith('%pm')]
    h = len(ls) // 2
    if h and ls[:h] == ls[h:]:
        ls = ls[:h]  # the harness evaluates the expression twice
    c = {}
    def inc(k, n=1):
        c[k] = c.get(k, 0) + n
    case = None
    culled = {}       # mug -> times culled, in this case
    refound = 0
    maxpass = (0, None)
    maxdepth = 0
    lexbad = []
    last = {}
    for l in ls:
        t = l.strip('[]').split()
        tag = t[0]
        if tag == '%pm-case':
            case = t[1]; culled = {}; inc('cases'); continue
        if tag == '%pm-run':
            mug, first, lc, pr, meq, ind, sk, ch, mov = t[1:10]
            inc('runs')
            if first == '%.y':
                inc('runs first'); continue
            inc('runs later')
            key = 'lc=%s pr=%s map-eq=%s in=%s sk=%s changed=%s' % (lc, pr, meq, ind, sk, ch)
            inc('  ' + key)
            # the lexicographic measure: less-code grows, else the product loses, else (map), indi, seek grow
            ok = None
            if lc == '%more': ok = 'lc'
            elif lc in ('%eq', '%eqv'):
                if pr == '%less': ok = 'pr'
                elif pr in ('%eq', '%eqv'):
                    if meq == '%.n': ok = 'map'
                    elif ind == '%more': ok = 'in'
                    elif ind in ('%eq', '%eqv'):
                        if sk == '%more': ok = 'sk'
                        elif sk in ('%eq', '%eqv'): ok = 'none'
            if ok is None or (ok == 'none' and ch == '%.y') or (ok not in ('none',) and ch == '%.n'):
                if not (ok == 'none' and (lc == '%eqv' or pr == '%eqv' or ind == '%eqv' or sk == '%eqv')):
                    lexbad.append((case, l))
            if ok == 'none' and ch == '%.y':
                inc('changed with every class eq/eqv')
            continue
        if tag == '%pm-new':
            inc('new'); maxdepth = max(maxdepth, int(t[3]))
            if t[1] in culled:
                refound += 1; inc('refound after cull')
            continue
        if tag == '%pm-cull':
            inc('culls')
            for m in t[2:]:
                m = m.strip('~[]')
                if m:
                    culled[m] = culled.get(m, 0) + 1; inc('culled members')
            continue
        if tag == '%pm-pass':
            inc('passes')
            p = int(t[2])
            if p > maxpass[0]: maxpass = (p, case)
            continue
        if tag in ('%pm-end', '%pm-a', '%pm-bad'):
            inc(tag + (' ' + t[1] if tag == '%pm-bad' else ''))
            if tag != '%pm-end':
                print(case, l[:400])
            continue
    for k in sorted(c):
        print(k, c[k])
    print('max pass', maxpass, 'max stack depth at a new function', maxdepth)
    print('runs that break the lexicographic order:', len(lexbad))
    for x in lexbad[:30]:
        print('  ', x[0], x[1][:300])

if sys.argv[1] == '--sum':
    for p in sys.argv[2:]:
        print('==', p)
        summarize(p)
    sys.exit(0)

out = sys.argv[1]
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
os.makedirs(out, exist_ok=True)
src = open(os.path.join(W, 'desk/lib/nock-compilation.hoon')).read().split('\n')

def find(anchor, start=0):
    k = [i for i, l in enumerate(src) if l == anchor and i >= start]
    assert k, anchor
    return k[0]

a0 = find('  ++  analyze')
i = find('    =/  index=@uxsite  next.st', a0)
src[i + 1:i + 1] = ['    ~&  [%pm-new (mug id) index (lent stk.st)]']
i = find('    =/  members=(list identity)  (sweep id (silt (above id stk.st)) st)', a0)
src[i + 1:i + 1] = ['    ~&  [%pm-pass (mug id) pass (lent members) next.st (lent stk.st)]']
i = find('    ?:  &(!changed =(next.st next-before))', a0)
src[i:i] = ['    ~&  [%pm-end (mug id) pass changed !=(next.st next-before)]']
i = find('    =/  dead=(set identity)  (~(dif in members) live)', a0)
src[i + 1:i + 1] = ['    ~?  !=(~ dead)  [%pm-cull (mug id) (turn ~(tap in dead) mug)]']
r0 = find('  ++  run', a0)
i = find('      =.  tick.st  +(tick.st)', r0)
src[i:i] = [
    '      =/  pm-sock',
    '        |=  [o=sock n=sock]',
    '        ^-  @tas',
    '        ?:  =(o n)  %eq',
    '        =/  up=?  (huge:so o n)',
    '        =/  dn=?  (huge:so n o)',
    '        ?:  &(up dn)  %eqv',
    '        ?:  up  %more',
    '        ?:  dn  %less',
    '        %x',
    '      =/  pm-cape',
    '        |=  [o=cape n=cape]',
    '        ^-  @tas',
    '        ?:  =(o n)  %eq',
    '        =/  up=?  =(| (lack:ca o n))',
    '        =/  dn=?  =(| (lack:ca n o))',
    '        ?:  &(up dn)  %eqv',
    '        ?:  up  %more',
    '        ?:  dn  %less',
    '        %x',
    '      =/  pm-small  |=(x=* ?:((lth (met 3 (jam x)) 300) x %big))',
    '      =/  pm-first=?  =(data *datum)',
    '      =/  pm-lc  (pm-sock less-code.data less-code.data-new)',
    '      =/  pm-pr  (pm-sock prod.data prod.data-new)',
    '      ~&  :*  %pm-run  (mug id)  pm-first  pm-lc  pm-pr',
    '              =(map.data map.data-new)  (pm-cape indi.data indi.data-new)',
    '              (pm-cape seek.data seek.data-new)  changed  (~(has in moved.st) id)',
    '          ==',
    '      ~?  ?&  !pm-first  =(less-code.data less-code.data-new)',
    '              =(prod.data prod.data-new)  !=(map.data map.data-new)',
    '          ==',
    '        [%pm-a (mug id) (pm-small prod.data) (pm-small map.data) (pm-small map.data-new)]',
    '      ~?  &(!pm-first !?=(?(%eq %more) pm-lc))',
    '        [%pm-bad %lc (mug id) (pm-small less-code.data) (pm-small less-code.data-new)]',
    '      ~?  &(!pm-first !?=(?(%eq %less) pm-pr))',
    '        [%pm-bad %pr (mug id) (pm-small prod.data) (pm-small prod.data-new)]',
]
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(src))

# ---- the corpus ----------------------------------------------------------------------------
def n2h(x):
    if isinstance(x, int):
        return f'{x:,}'.replace(',', '.')
    return '[' + n2h(x[0]) + ' ' + n2h(x[1]) + ']'

def L(*xs):  # right-nested cell
    if len(xs) == 1:
        return xs[0]
    return (xs[0], L(*xs[1:]))

K = lambda x: L(1, x)
A = lambda a: L(0, a)
def rec(samp, arm=2):     # call the arm with a new sample: [9 arm [10 [6 samp] [0 1]]]
    return L(9, arm, L(10, L(6, samp), A(1)))
def recs(samp, arm=2):    # the same, with the sample at axis 3 of a one-arm core
    return L(9, arm, L(10, L(3, samp), A(1)))
def ite(t, y, n):
    return L(6, t, y, n)

cases = []   # (name, bus-hoon, fol)
def known(name, sub, fol):
    cases.append((name, '&+' + n2h(sub), fol))
def bus(name, b, fol):
    cases.append((name, b, fol))

# the witness of 1813f09 and its variants: sample swapped, rotated, product run as a formula
F = L(6, L(3, A(6)), A(6), L(2, K(0), L(2, L(A(2), A(7), A(6)), A(2))))
known('swaploop', L(F, K(0), K(0)), F)
for perm in [L(A(7), A(6)), L(A(6), A(7)), L(A(7), A(7)), L(A(6), A(6))]:
    for tail in [L(2, K(0), L(2, L(A(2), perm), A(2))), L(2, A(1), L(2, L(A(2), perm), A(2))),
                 L(2, L(2, L(A(2), perm), A(2)), A(1)), L(L(2, L(A(2), perm), A(2)), A(6)),
                 L(7, L(2, L(A(2), perm), A(2)), L(2, A(1), A(0 + 1)))]:
        for base in [A(6), A(7), K(0), A(1)]:
            f = L(6, L(3, A(6)), base, tail)
            for s in [L(K(0), K(0)), L(0, 0), L(K(0), A(1)), L(A(3), A(2)), L(1, 2)]:
                known('swap', L(f, s), f)
            bus('swapu', '[[& |] [%fol ~]]'.replace('%fol', n2h(f)), f)
# three-part samples rotated: [a [b c]] -> [b [c a]], with the product run as a formula
for rot in [L(A(14), A(15), A(6)), L(A(15), A(6), A(14)), L(A(6), A(15), A(14))]:
    for tail in [L(2, K(0), L(2, L(A(2), rot), A(2))), L(2, A(1), L(2, L(A(2), rot), A(2))),
                 L(L(2, L(A(2), rot), A(2)), L(2, L(A(2), rot), A(2)))]:
        for base in [A(6), A(14), K(0)]:
            f = L(6, L(3, A(6)), base, tail)
            for s in [L(K(0), K(0), K(0)), L(K(0), K(1), K(0)), L(0, 0, 0), L(A(2), K(0), A(1))]:
                known('rot', L(f, s), f)
# mutual recursion: a battery of two arms at axes 4 and 5 calling each other, swapping
for x in [L(A(7), A(6)), L(A(6), A(7))]:
    for y in [L(A(7), A(6)), L(A(6), A(7))]:
        fa = L(6, L(3, A(6)), A(6), L(2, K(0), L(9, 5, L(10, L(6, x), A(1)))))
        fb = L(6, L(3, A(7)), A(7), L(2, A(1), L(9, 4, L(10, L(6, y), A(1)))))
        fc = L(6, L(3, A(7)), K(0), L(L(9, 4, L(10, L(6, y), A(1))), L(9, 5, L(10, L(6, x), A(1)))))
        for fbb in [fb, fc]:
            for s in [L(K(0), K(0)), L(0, 0), L(K(0), A(1))]:
                core = L(L(fa, fbb), s)
                known('mut', core, L(9, 4, A(1)))
            bus('mutu', '[[& |] [%c ~]]'.replace('%c', n2h(L(fa, fbb))), L(9, 4, A(1)))

# random recursive cores
rnd = random.Random(seed)
def rexpr(d, arms):
    r = rnd.random()
    if d <= 0 or r < 0.25:
        return rnd.choice([A(rnd.choice([1, 2, 3, 6, 7, 12, 13, 14, 15])), K(rnd.choice([0, 1, L(0, 1), L(0, 6)]))])
    if r < 0.45:
        samp = rnd.choice([L(A(7), A(6)), L(A(6), A(7)), A(6), A(7), L(A(7), L(4, A(6))),
                           L(rexpr(d - 1, arms), rexpr(d - 1, arms)), L(A(13), A(12)), L(A(6), A(6))])
        call = L(9, rnd.choice(arms), L(10, L(6, samp), A(1)))
        k = rnd.random()
        if k < 0.3:
            return L(2, rnd.choice([K(0), A(1), A(6), A(7)]), call)
        if k < 0.45:
            return L(2, call, rnd.choice([A(2), A(4), A(5), A(1)]))
        return call
    if r < 0.6:
        return ite(rnd.choice([L(3, A(6)), L(3, A(7)), L(5, A(6), A(7)), L(5, A(6), K(0)), L(3, A(13))]),
                   rexpr(d - 1, arms), rexpr(d - 1, arms))
    if r < 0.7:
        return L(rexpr(d - 1, arms), rexpr(d - 1, arms))
    if r < 0.78:
        return L(4, rexpr(d - 1, arms))
    if r < 0.86:
        return L(8, rexpr(d - 1, arms), L(7, A(3), rexpr(d - 1, arms)))
    if r < 0.93:
        return L(2, rexpr(d - 1, arms), rexpr(d - 1, arms))
    return L(10, L(rnd.choice([6, 7, 13]), rexpr(d - 1, arms)), A(1))
def rsamp():
    return rnd.choice([L(K(0), K(0)), L(0, 0), L(K(0), A(1)), L(A(3), A(2)), L(1, 2), L(L(0, 1), 0),
                       L(L(1, 0), L(1, 0)), L(0, L(0, 0)), L(K(0), L(K(0), K(0)))])
for k in range(400):
    if rnd.random() < 0.5:
        f = rexpr(rnd.choice([3, 4, 5]), [2])
        core = L(f, rsamp())
        if rnd.random() < 0.7:
            known('rnd1', core, f)
        else:
            bus('rnd1u', '[[& |] [%c ~]]'.replace('%c', n2h(f)), f)
    else:
        fa = rexpr(rnd.choice([3, 4]), [4, 5]); fb = rexpr(rnd.choice([3, 4]), [4, 5])
        bat = L(fa, fb)
        if rnd.random() < 0.7:
            known('rnd2', L(bat, rsamp()), L(9, 4, A(1)))
        else:
            bus('rnd2u', '[[& |] [%c ~]]'.replace('%c', n2h(bat)), L(9, 4, A(1)))

# cores whose products are cores: calls on the products of calls (identities that change across
# passes, so members get culled), the products of calls run as formulas or as subjects
def cexpr(d):
    r = rnd.random()
    if d <= 0 or r < 0.2:
        return rnd.choice([A(1), A(1), A(6), A(7), K(0), L(10, L(6, csamp(0)), A(1)),
                           L(10, L(7, A(6)), A(1)), A(13)])
    if r < 0.4:
        return ccall(d)
    if r < 0.55:
        return L(7, ccall(d - 1), rnd.choice([L(9, rnd.choice([4, 5]), A(1)), ccall(d - 1), A(6),
                                              L(10, L(6, A(13)), A(1)), cexpr(d - 1)]))
    if r < 0.7:
        return ite(rnd.choice([L(3, A(6)), L(3, A(13)), L(5, A(12), A(13)), L(5, A(6), K(0)), L(3, A(7))]),
                   cexpr(d - 1), cexpr(d - 1))
    if r < 0.8:
        return L(2, ccall(d - 1), rnd.choice([A(2), A(4), A(1), K(L(9, 4, A(1))), A(14)]))
    if r < 0.9:
        return L(cexpr(d - 1), cexpr(d - 1))
    return L(8, ccall(d - 1), L(7, A(3), cexpr(d - 1)) if rnd.random() < 0.5 else L(9, 4, A(3)))
def csamp(d):
    return rnd.choice([L(A(7), A(6)), L(A(13), A(12)), A(7), A(6), L(A(6), A(6)), L(K(0), A(6)),
                       L(A(13), A(6)), L(L(A(7), A(6)), K(0))] + ([cexpr(d - 1)] if d > 0 else []))
def ccall(d):
    return L(9, rnd.choice([4, 5]), L(10, L(6, csamp(d)), A(1)))
def csamps():
    return rnd.choice([L(K(0), K(0)), L(0, 0), L(L(0, 0), 0), L(0, L(0, 0)), L(L(1, 0), L(1, 0)),
                       L(K(0), L(K(0), K(0))), L(L(0, 1), L(0, 1))])
for k in range(500):
    bat = L(cexpr(rnd.choice([2, 3, 4])), cexpr(rnd.choice([2, 3, 4])))
    if rnd.random() < 0.75:
        cases.append(('crn', '&+' + n2h(L(bat, csamps())), L(9, 4, A(1))))
    else:
        cases.append(('crnu', '[[& |] [%c ~]]'.replace('%c', n2h(bat)), L(9, 4, A(1))))

# a root R (arm 4) that calls Z (arm 10) on a part of its own recursive call's product, then X
# (arm 11) on Z's product, X calling back R: X's subject comes from an entry that is replaced by a
# fresh one (Z's identity changes as R's product loses knowledge), the way a culled member could be
# called again
def pick(xs):
    return rnd.choice(xs)
SW = [L(A(7), A(6)), L(A(6), A(7)), A(7), L(A(6), K(0)), L(K(0), A(6)), L(A(13), A(12))]
def rcall(arm, samp):
    return L(9, arm, L(10, L(6, samp), A(1)))
for k in range(400):
    rr = rcall(4, pick(SW))
    t = pick([L(7, rr, A(6)), L(7, rr, A(1)), rr, L(7, rr, A(13)), L(L(7, rr, A(6)), A(7))])
    zc = rcall(10, t)
    xc = pick([L(7, zc, L(9, 11, A(1))), L(7, zc, L(9, 4, A(1))), L(2, zc, K(L(9, 11, A(1)))),
               L(7, zc, rcall(11, A(6)))])
    R = ite(pick([L(3, A(6)), L(5, A(6), K(0)), L(3, A(13))]), pick([A(1), A(6), L(10, L(6, K(0)), A(1))]), xc)
    zr = rcall(10, pick([A(7), L(A(7), A(6)), A(6), L(A(13), K(0))]))
    Z = ite(pick([L(3, A(6)), L(5, A(6), K(0)), L(3, A(7))]), pick([A(1), L(10, L(6, A(7)), A(1)), A(6)]),
            pick([L(10, L(6, L(7, zr, A(6))), A(1)), zr, L(7, zr, A(1)), L(L(7, zr, A(6)), A(7))]))
    X = pick([rcall(4, A(13)), rcall(4, A(6)), L(7, rcall(4, L(A(7), A(6))), A(6)), rcall(4, L(A(13), A(12))),
              ite(L(3, A(6)), A(1), rcall(4, A(7)))])
    bat = L(R, L(Z, X))
    sm = pick([L(K(0), K(0)), L(0, 0), L(L(0, 0), 0), L(0, L(0, 0)), L(L(1, 0), L(1, 0)), L(K(0), L(K(0), K(0)))])
    if rnd.random() < 0.7:
        cases.append(('zrx', '&+' + n2h(L(bat, sm)), L(9, 4, A(1))))
    else:
        cases.append(('zrxu', '[[& |] [%c ~]]'.replace('%c', n2h(bat)), L(9, 4, A(1))))

def driver(name, cs):
    t = ['::  the pass-loop measure driver (passmeasure.py)', '=/  cases=(list [nam=@tas bus=sock fol=*])', '  :~']
    for (nm, b, f) in cs:
        t.append(f'      [%{nm} {b} {n2h(f)}]')
    t += ['  ==', '=/  n=@ud  0', '|-  ^-  @', '?~  cases  ~&  %pm-done  0',
          '~&  [%pm-case n nam.i.cases]',
          '=/  f=^  ?>(?=(^ fol.i.cases) fol.i.cases)',
          '=/  res  (ska-callgraph [bus.i.cases f] ~ [~ ~ ~ ~ ~])',
          '~&  [%pm-graph n ~(wyt by -.res)]',
          '$(cases t.cases, n +(n))', '']
    open(os.path.join(out, f'ck-{name}.hoon'), 'w').write('\n'.join(t))

hand = [c for c in cases if not c[0].startswith('rnd')]
rn = [c for c in cases if c[0].startswith('rnd')]
cr = [c for c in cases if c[0].startswith('crn')]
zx = [c for c in cases if c[0].startswith('zrx')]
hand = [c for c in hand if not c[0].startswith('crn') and not c[0].startswith('zrx')]
for j in range(0, len(zx), 100):
    driver(f'zrx{j // 100}', zx[j:j + 100])
driver('hand', hand)
for j in range(0, len(rn), 100):
    driver(f'rnd{j // 100}', rn[j:j + 100])
for j in range(0, len(cr), 100):
    driver(f'crn{j // 100}', cr[j:j + 100])
# the threading formulas, with a subject that knows nothing and with their own subject
th = []
for nm in ['thread-a.hoon', 'thread-b.hoon', 'thread-c.hoon']:
    tx = open(os.path.join(D, nm)).read().split('\n')
    for l in tx:
        m = re.match(r'^      \[(\d+) %\w+ (.*)\]$', l)
        if m:
            th.append(m.group(2))
t = ['::  the pass-loop measure driver over thread-a/b/c (passmeasure.py)',
     '=/  cases=(list [sub=* fol=*])', '  :~'] + [f'      [{x}]' for x in th] + [
     '  ==', '=/  n=@ud  0', '|-  ^-  @', '?~  cases  ~&  %pm-done  0',
     '~&  [%pm-case n %thr]', '=/  f=^  ?>(?=(^ fol.i.cases) fol.i.cases)',
     '=/  r1  (ska-callgraph [[| ~] f] ~ [~ ~ ~ ~ ~])',
     '~&  [%pm-case n %thrk]',
     '=/  r2  (ska-callgraph [&+sub.i.cases f] ~ [~ ~ ~ ~ ~])',
     '$(cases t.cases, n +(n))', '']
open(os.path.join(out, 'ck-thread.hoon'), 'w').write('\n'.join(t))
print(len(hand), 'hand cases,', len(rn), 'random,', len(th), 'threading')
