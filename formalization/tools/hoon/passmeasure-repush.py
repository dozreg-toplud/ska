#!/usr/bin/env python3
# usage: passmeasure-repush.py OUT.hoon (w|m|s|c|r SEED N): drivers for point (b) of README Gaps 16 (re-pushes);
#   run with RUNHOON_LIB=OUTDIR/lib.hoon of passmeasure.py, then passmeasure-repush.py --sum OUT.txt...
#   w: one re-push (two sites), m: k sites push one identity k times, s: one site re-pushes,
#   c: a chain of two restarting callees before the site (one identity pushed 4 times),
#   r: random cores (registers, a shared f, its own product a restarting shift register)
# witness generator for point (b): a re-push of a culled identity
import sys
def n2h(x):
    if isinstance(x, int):
        return f'{x:,}'.replace(',', '.')
    return '[' + n2h(x[0]) + ' ' + n2h(x[1]) + ']'
def L(*xs):
    return xs[0] if len(xs) == 1 else (xs[0], L(*xs[1:]))
K = lambda x: L(1, x)
A = lambda a: L(0, a)
def peg(a, b):
    if b == 1: return a
    return peg(a, b // 2) * 2 + (b % 2)
def tup(xs):  # right-nested tuple of formulas
    return L(*xs) if len(xs) > 1 else xs[0]
def slots(n):  # axes of the n elements of a right-nested n-tuple
    r = []; ax = 1
    for i in range(n - 1):
        r.append(peg(ax, 2)); ax = peg(ax, 3)
    r.append(ax); return r

def witness(np=4, nq=6, a=7, x=L(0, 1), fread=(22, 23), xsel=None, ymode='y', extra=None):
    """R = [6 [3 [0 3]] base step] on core K = [[R ~] sam], sam unknown.
    R's product [P Q]: P an np-tuple [a x .. x], Q an nq-tuple [x .. x]; each run shifts
    both left with an unknown at the end, so P and Q lose their last known slot one per pass.
    Y calls f on [P K]; X calls f on [[a Q.xsel...] K]."""
    base = K(L(tuple_val([a] + [x] * (np - 1)), tuple_val([x] * nq)))
    # in the subject [Pr K] of the step body: Pr = [P Q] at 2, P at 4, Q at 5, sample at 7
    ps = [peg(4, s) for s in slots(np)]
    qs = [peg(5, s) for s in slots(nq)]
    U = A(7)
    hP = tup([A(ps[0])] + [A(s) for s in ps[2:]] + [U])
    hQ = tup([A(s) for s in qs[1:]] + [U])
    f = fbody(fread)
    Y = L(2, L(A(4), A(3)), K(f))
    xs = xsel if xsel is not None else [1, 2, 3]   # which Q slots fill X's P-part after a
    X = L(2, L(tup([K(a)] + [A(qs[i - 1]) for i in xs]), A(3)), K(f))
    calls = L(Y, X) if ymode == 'y' else L(X, Y)
    if extra:
        calls = L(calls, extra)
    # [7 [[calls [0 1]] h'] ]: h' on [[..] [Pr K]], axes under 3
    hP3 = shift3(hP); hQ3 = shift3(hQ)
    step = L(8, L(9, 4, A(1)), L(7, L(calls, A(1)), L(hP3, hQ3)))
    R = L(6, L(3, A(3)), base, step)
    return R, f

def tuple_val(xs):
    return L(*xs) if len(xs) > 1 else xs[0]

def shift3(fm):
    # rewrite every [0 b] in a formula built of conses and [0 b] to [0 peg(3,b)]
    if fm[0] == 0:
        return L(0, peg(3, fm[1]))
    return L(shift3(fm[0]), shift3(fm[1]))

def fbody(reads):
    # f on [P' K]: run the formulas at the axes in .reads (indirect when unknown), then call R
    parts = [L(2, A(1), A(r)) for r in reads] + [L(9, 4, A(3))]
    return tup(parts)

def driver(cases, path):
    t = ['=/  cases=(list [nam=@tas bus=sock fol=*])', '  :~']
    for (nm, b, f) in cases:
        t.append(f'      [%{nm} {b} {n2h(f)}]')
    t += ['  ==', '=/  n=@ud  0', '|-  ^-  @', '?~  cases  ~&  %pm-done  0',
          '~&  [%pm-case n nam.i.cases]',
          '=/  f=^  ?>(?=(^ fol.i.cases) fol.i.cases)',
          '=/  res  (ska-callgraph [bus.i.cases f] ~ [~ ~ ~ ~ ~])',
          '~&  [%pm-graph n ~(wyt by -.res)]',
          '$(cases t.cases, n +(n))', '']
    open(path, 'w').write('\n'.join(t))


def multi(ns, a=7, x=L(0, 1), reads=(22, 23), order=None):
    """registers of n_i x's (n_i >= 3); site i calls f on [[a r_i.1 r_i.2 r_i.3] K]: its subject
    is s = [a x x |] at run n_i only, so s is pushed at each n_i that follows a gap of 2 runs."""
    k = len(ns)
    rs = slots(k) if k > 1 else [1]
    base = K(tuple_val([tuple_val([x] * n) for n in ns]))
    f = fbody(reads)
    sites = []; hs = []
    for i, n in enumerate(ns):
        rax = peg(2, rs[i])                 # register i in [Pr K]
        sl = [peg(rax, s) for s in slots(n)]
        sites.append(L(2, L(tup([K(a), A(sl[0]), A(sl[1]), A(sl[2])]), A(3)), K(f)))
        hs.append(tup([A(s) for s in sl[1:]] + [A(7)]))
    if order: sites = [sites[j] for j in order]
    calls = tup(sites)
    step = L(8, L(9, 4, A(1)), L(7, L(calls, A(1)), shift3(tup(hs))))
    R = L(6, L(3, A(3)), base, step)
    return R, f

def rcase(nm, R):
    return (nm, '[[[& |] |] [[%R 0] 0]]'.replace('%R', n2h(R)), L(9, 4, A(1)))
def single(n=8, a=7, b=9, x=L(0, 1), ylen=3, twice=False):
    f = L(L(2, A(1), A(22)), L(L(2, A(1), A(23)), L(9, 4, A(3))))
    # g on [P' K]: K at 3, sample 7, battery 6 = [R [g f]]: g at 26
    gbase = L(7, L(2, A(1), A(5)), K(tuple_val([b] + [x] * ylen)))
    gs = slots(ylen + 1)                         # G's slots
    sh = tup([A(peg(6, gs[0]))] + [A(peg(6, s)) for s in gs[2:]] + [A(31)])
    gstep = L(8, L(2, A(1), A(26)), L(7, L(L(9, 4, A(7)), A(1)), sh))
    g = L(6, L(3, A(7)), gbase, gstep)
    rb = K(tuple_val([x] * n))
    # body subject [Pr K]: Pr at 2, K at 3
    rs = slots(n)
    y1 = L(2, L(L(K(a), A(peg(2, rs[0]))), A(3)), K(g))
    # after [8 y1 ..]: [G [Pr K]]: G at 2, K at 7
    z = L(2, L(tup([K(a)] + [A(peg(2, s)) for s in gs[1:4]]), A(7)), K(f))
    # after [8 z ..]: [Zp [G [Pr K]]]: Pr at 14, sample at 31
    shP = tup([A(peg(14, s)) for s in rs[1:]] + [A(31)])
    body = L(8, y1, L(8, z, shP))
    R = L(6, L(3, A(3)), rb, L(8, L(9, 4, A(1)), body))
    return R, g, f
def mkf(reads, fself):
    rd = [L(2, A(1), A(r)) for r in reads] + [L(9, 4, A(3))]
    if not fself:
        return L(tup(rd), A(2))
    # f = [6 [3 [0 7]] [0 2] [8 [2 [0 1] [0 SELF]] [[rd'] shift]]] -- f must name itself: keep it in K
    # at axis 5 of K (battery [R f]): self-call [2 [0 1] [0 13]] has formula f known in K
    # inside [F [P' K]]: P' at 6, K at 7, f at 7->(battery 2)->(f 3) = peg(7, 5) = 29
    rd2 = [L(2, A(6), A(peg(6, r // 2 * 0 + 0) if False else peg(3, r))) for r in reads]  # unused
    body = L(tup([L(2, A(peg(3, 1)), A(peg(3, r))) for r in reads] + [L(9, 4, A(7))]),
             L(A(4), L(A(22), L(A(23), A(15)))))   # shift F = [a y1 y2 y3] -> [a y2 y3 U]
    # F's slots in [F [P' K]]: a 4, y1 10, y2 22, y3 23, U = sample at 15
    return L(6, L(3, A(7)), A(2), L(8, L(2, A(1), A(13)), body))
def rnd_case(rnd, idx):
    nreg = rnd.choice([1, 2, 3])
    ns = [rnd.choice([3, 4, 5, 6, 7]) for _ in range(nreg)]
    fself = rnd.random() < 0.7
    reads = rnd.choice([(22, 23), (10, 22, 23), (23,), (22,), (10, 23)])
    f = mkf(reads, fself)
    a = 7; x = L(0, 1)
    base = K(tuple_val([tuple_val([x] * n) for n in ns]))
    rs = slots(nreg) if nreg > 1 else [1]
    # in the body subject [Pr K] (Pr at 2): register i at peg(2, rs[i]); after j sites pushed with
    # [8 ..], the subject is [p_j [.. [p_1 [Pr K]]]]: shift every axis under 3 once per push
    regsl = [[peg(peg(2, rs[i]), s) for s in slots(n)] for i, n in enumerate(ns)]
    hs = [tup([A(s) for s in sl[1:]] + [A(7)]) for sl in regsl]
    nsite = rnd.choice([2, 3, 4, 5])
    prods = []   # axes (in the current subject) of earlier site products' slots
    depth = 0
    def under(ax, d):
        for _ in range(d): ax = peg(3, ax)
        return ax
    sites = []
    for j in range(nsite):
        pool = [under(s, j) for sl in regsl for s in sl]
        # earlier products: site i's product pushed at depth i+1; f's product [[..] P'] or F
        for i in range(j):
            pa = under(2, j - 1 - i)
            if fself:
                pool += [peg(pa, s) for s in (2, 6, 14, 15)]
            else:
                pool += [peg(pa, s) for s in (6, 14, 15)]  # P' = [a x1 x2 x3] at 3 of [[..] P']
        if j > 0 and rnd.random() < 0.6:
            pool = pool[-8:]
        sl3 = [rnd.choice(pool) for _ in range(3)]
        sites.append(L(2, L(tup([K(a)] + [A(s) for s in sl3]), A(under(3, j))), K(f)))
    # nested [8 site [8 site .. h]] with h shifted under the pushes
    h = tup(hs)
    for _ in range(nsite): h = shift3(h)
    body = h
    for j in reversed(range(nsite)):
        body = L(8, sites[j], body)
    step = L(8, L(9, 4, A(1)), body)
    R = L(6, L(3, A(3)), base, step)
    bus = '[[[& &] |] [[%R %F] 0]]'.replace('%R', n2h(R)).replace('%F', n2h(f))
    return ('r%d' % idx, bus, L(9, 4, A(1)))

def gfun(selfax, m, b=9, x=L(0, 1)):
    gbase = L(7, L(2, A(1), A(5)), K(tuple_val([b] + [x] * m)))
    gs = slots(m + 1)
    sh = tup([A(peg(6, gs[0]))] + [A(peg(6, s)) for s in gs[2:]] + [A(31)])
    gstep = L(8, L(2, A(1), A(selfax)), L(7, L(L(9, 4, A(7)), A(1)), sh))
    return L(6, L(3, A(7)), gbase, gstep)
def chain2(n=14, m0=6, a=7, x=L(0, 1)):
    f = L(L(2, A(1), A(22)), L(L(2, A(1), A(23)), L(9, 4, A(3))))
    g0 = gfun(26, m0); g1 = gfun(54, 3)
    rs = slots(n)
    y0 = L(2, L(L(K(a), A(peg(2, rs[0]))), A(3)), K(g0))          # in [Pr K]
    g0s = slots(m0 + 1)
    y1 = L(2, L(L(K(a), A(peg(2, g0s[1]))), A(7)), K(g1))         # in [G0 [Pr K]]
    g1s = slots(4)
    z = L(2, L(tup([K(a)] + [A(peg(2, s)) for s in g1s[1:4]]), A(15)), K(f))  # in [G1 [G0 [Pr K]]]
    shP = tup([A(peg(30, s)) for s in rs[1:]] + [A(63)])          # in [Zp [G1 [G0 [Pr K]]]]
    body = L(8, y0, L(8, y1, L(8, z, shP)))
    R = L(6, L(3, A(3)), K(tuple_val([x] * n)), L(8, L(9, 4, A(1)), body))
    bat = L(R, L(g0, L(g1, f)))
    return ('c%d' % n, '[[[& &] |] [%B 0]]'.replace('%B', n2h(bat)), L(9, 4, A(1)))

def under(ax, d):
    for _ in range(d): ax = peg(3, ax)
    return ax
def chain(d, n, ms, a=7, x=L(0, 1)):
    """a chain of d restarting callees g_0 .. g_{d-1} before one site z of f, in R's step:
    y_0 calls g_0 on [[a Pr.0] K] (Pr: R's product, an n-tuple shift register), y_i calls g_i on
    [[a G_{i-1}.1] K], z calls f on [[a G_{d-1}.1 G_{d-1}.2 G_{d-1}.3] K]; g_i is a restarting
    shift register of ms[i] + 1 slots (gfun), which reads its sample slot, so a change of G_{i-1}.1
    pushes a fresh g_i whose register starts full again.  chain(2, 14, [6, 3]) is chain2()."""
    assert len(ms) == d and ms[-1] >= 3
    f = L(L(2, A(1), A(22)), L(L(2, A(1), A(23)), L(9, 4, A(3))))
    bs = slots(d + 2)                                  # battery [R g_0 .. g_{d-1} f]
    gs = [gfun(peg(6, bs[i + 1]), ms[i]) for i in range(d)]
    rs = slots(n)
    ys = [L(2, L(L(K(a), A(peg(2, rs[0]))), A(3)), K(gs[0]))]       # in [Pr K]
    for i in range(1, d):                                           # in [G_{i-1} [.. [Pr K]]]
        gp = slots(ms[i - 1] + 1)
        ys.append(L(2, L(L(K(a), A(peg(2, gp[1]))), A(under(3, i))), K(gs[i])))
    gl = slots(ms[-1] + 1)
    z = L(2, L(tup([K(a)] + [A(peg(2, s)) for s in gl[1:4]]), A(under(3, d))), K(f))
    shP = tup([A(peg(under(2, d + 1), s)) for s in rs[1:]] + [A(peg(under(3, d + 1), 3))])
    body = shP
    for y in reversed(ys + [z]):
        body = L(8, y, body)
    R = L(6, L(3, A(3)), K(tuple_val([x] * n)), L(8, L(9, 4, A(1)), body))
    bat = tup([R] + gs + [f])
    nm = 'c%d-%d-%s' % (d, n, '-'.join(map(str, ms)))
    return (nm.replace('-', 'x'), '[[[& &] |] [%B 0]]'.replace('%B', n2h(bat)), L(9, 4, A(1)))
def cells(x):
    return 0 if isinstance(x, int) else 1 + cells(x[0]) + cells(x[1])

def summary(paths):
    import importlib.util, os
    pm = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure.py')
    src = open(pm).read().split("if sys.argv[1] in ('--sum'")[0]
    ns = {'__file__': pm}; exec(src, ns)
    tot = {'cases': 0, 're-pushes': 0, 'max pushes of one identity': (0, None), 'max passes': (0, None), 'hist': {}}
    for p in paths:
        res = {}; case = None
        for l in ns['pmlines'](p):
            t = l.strip('[]').split()
            if t[0] == '%pm-case':
                case = t[2]; res[case] = dict(push={}, culled=set(), rep=0, passes=0, done=False)
            elif case is None: continue
            elif t[0] == '%pm-new':
                r = res[case]; r['push'][t[1]] = r['push'].get(t[1], 0) + 1
                if t[1] in r['culled']: r['rep'] += 1
            elif t[0] == '%pm-cull':
                res[case]['culled'] |= {m.strip('~[]') for m in t[2:] if m.strip('~[]')}
            elif t[0] == '%pm-pass': res[case]['passes'] = max(res[case]['passes'], int(t[2]))
            elif t[0] == '%pm-graph': res[case]['done'] = True
        for c, r in res.items():
            mp = max(r['push'].values()) if r['push'] else 0
            tot['cases'] += 1; tot['re-pushes'] += r['rep']; tot['hist'][mp] = tot['hist'].get(mp, 0) + 1
            if not r['done']: print('NOT DONE', p, c, r['passes'])
            if mp > tot['max pushes of one identity'][0]: tot['max pushes of one identity'] = (mp, c)
            if r['passes'] > tot['max passes'][0]: tot['max passes'] = (r['passes'], c)
    print(tot)

if __name__ == '__main__':
    if sys.argv[1] == '--sum':
        summary(sys.argv[2:]); sys.exit(0)
    out, mode = sys.argv[1], sys.argv[2]
    bus = lambda R, bat: '[[[& &] |] [[%R %B] 0]]'.replace('%R', n2h(R)).replace('%B', n2h(bat))
    if mode == 'w':
        R, f = witness(); cs = [rcase('w1', R)]
    elif mode == 'm':
        cs = [rcase(nm, multi(ns)[0]) for nm, ns in
              [('m2', [3, 6]), ('m3', [3, 6, 9]), ('m4', [3, 6, 9, 12]), ('m5', [3, 5, 7, 9, 11])]]
    elif mode == 'c':
        if len(sys.argv) > 3:   # c D N M_0,..,M_{D-1}: a chain of D restarting callees
            d, n = int(sys.argv[3]), int(sys.argv[4])
            cs = [chain(d, n, [int(m) for m in sys.argv[5].split(',')])]
        else:
            cs = [chain2(), chain2(20, 8)]
    elif mode == 's':
        cs = []
        for nm, n in [('s8', 8), ('s12', 12)]:
            R, g, f = single(n); cs.append((nm, bus(R, L(g, f)), L(9, 4, A(1))))
    else:
        import random
        seed, n = int(sys.argv[3]), int(sys.argv[4]); rnd = random.Random(seed)
        cs = [rnd_case(rnd, seed * 1000 + k) for k in range(n)]
    driver(cs, out)
