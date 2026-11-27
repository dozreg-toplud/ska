#!/usr/bin/env python3
# usage: passmeasure-take.py OUT.hoon FAMILY [args]   (track F, README Gaps 16, 2026-11-27)
# Cores designed to make a PERSISTENT member (the root R, constant subject) take a fresh callee identity
# at a site of constant subject forever, by the %rec takeover (the only way left, see Gaps 16): a site
# k_t of R calls f_t on s_t = [[[1 T_t] |] K] (p unknown), which never pushes [s_t f_t] because a
# member of f_t with p = [u |] is on the stack from the first pass (R's register keeps p = [R.0 |] for
# n passes), so k_t resolves by %rec to the NEWEST member of f_t with tag T_t and p partially known.
# A member of f_t on [[[1 T] p] K] reads [1 T] (direct: in less-code) and p as formulas (indirect
# when p is partial: p in indi), calls R back (so it is a member of R's component), calls itself and
# shifts its register REG (m_t equal slots v, one slot unknown more per pass of its life: its AGE).
# Sites j_t of R build p = [X.i Y.j] from the registers of the targets of two k sites: so the
# knowledge of p is one of [v v] (direct, never a takeover), [v |], [| v] (incomparable, both take
# over k_t), | ; a push needs a p that no member on the stack covers.  Two independent ages make
# [v |] and [| v] alternate in principle (one age alone gives the same p after every restart).
#   x N M1 M2 I1 J1 I2 J2 [order]   two formulas f_1, f_2 (tags 5, 6), cross-fed: j_1 builds f_1's
#        p from [A.I1 B.J1], j_2 builds f_2's p from [B.I2 A.J2] (A, B: registers of the k_1, k_2 targets)
#   r N M1 M2 M3 I J                three formulas in a ring: j_t reads the registers of k_t and k_{t+1}
#   s N M I J                       one formula, two tags (both sites share f, so M is common)
#   q N M1 M2 I1 J1 I2 J2           as x, but p's known part is fed through a Nock quine Y
#        ([2 [1 [W 0]] [1 W]] runs to itself, with no provenance), so it survives +patch-prod
#   batch OUTDIR                    writes the designed batch (drivers tk-*.hoon, several cases each)
#   batch2 OUTDIR                   family a, complements (drivers ta-*.hoon): see batch2
#   debuglib LIB.hoon OUT.hoon      LIB (of passmeasure.py) with %pm-sub / %pm-kid: subject heads
#   --sum[-v] OUT.txt...            per case: root passes, %st recurrence, pushes, re-pushes, takeovers,
#        changes of the root's callee set (-v: the set per pass)
import os, sys
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure-repush.py')).read().split("if __name__")[0]
exec(src)

def axis(tree, name):
    """axis of the leaf .name in a subject tree of nested pairs of names"""
    if tree == name: return 1
    if isinstance(tree, tuple):
        a = axis(tree[0], name)
        if a: return peg(2, a)
        b = axis(tree[1], name)
        if b: return peg(3, b)
    return 0

V = L(0, 1)                                   # the slot value of every register: the formula [0 1]
W = L(K(2), L(L(K(1), A(1)), L(K(1), A(2))))  # quine part: .*([W 0], W) = [2 [1 [W 0]] [1 W]]
Y = L(2, K(L(W, 0)), K(W))                    # .*(x, Y) = Y for every x

def farm(m, selfax, rax, quine=False):
    """f on [D K], D = [tag [p c]]: reads tag and p as formulas (not c), calls R back, itself, shifts
    REG.  product [[tag-res p-res] REG]; REG0 = m copies of V (or of the quine Y when quine)"""
    v = Y if quine else V
    reg0 = tuple_val([v] * m)
    t0 = (('tag', ('p', 'c')), ('BAT', 'sam'))
    rd = L(L(2, A(1), A(axis(t0, 'tag'))), L(2, A(1), A(axis(t0, 'p'))))
    base = L(rd, K(reg0))
    t = ('Rp', ('F', t0))          # after the self call and the call of R
    rd2 = L(L(2, A(7), A(axis(t, 'tag'))), L(2, A(7), A(axis(t, 'p'))))
    fx = axis(t, 'F')
    regs = [peg(peg(fx, 3), s) for s in slots(m)]
    sh = tup([A(s) for s in regs[1:]] + [A(axis(t, 'sam'))])
    if quine:   # the known slots are rebuilt by running the quine on itself: [2 [0 r] [0 r]] keeps Y
        sh = tup([L(2, A(s), A(s)) for s in regs[1:]] + [A(axis(t, 'sam'))])
    step = L(8, L(2, A(1), A(peg(6, selfax))),
             L(8, L(2, A(7), A(peg(7, rax))), L(rd2, sh)))
    return L(6, L(3, A(7)), base, step)

def core(n, ms, feeds, order=None, quine=False, tags=None, same=False):
    """R with one k site per formula t (tag tags[t]) and one j site per feed (t, (a, i), (b, j)): j calls
    f_t with p = [reg_a.i reg_b.j], reg_a the register of the k_a target's product."""
    nf = len(ms)
    tags = tags or [5 + t for t in range(nf)]
    bs = slots(nf + 1)                         # battery [R f_1 .. f_nf]
    armK = lambda i: peg(2, bs[i])
    fs = [farm(ms[t], bs[t + 1], armK(0), quine) for t in range(nf)]
    # R on K: [6 [3 [0 3]] [1 RREG0] [8 self [body]]], body subject [Pr K]
    # R's product [c REG]: c a constant that never drains (unknown only in R's first run, whose
    # product is the bunt), so the drained subject [[[1 T] [| c]] K] differs from the first run's
    u = V
    rreg0 = L(7, tuple_val([u] * n))
    tree = (('c', 'Pr'), ('BAT', 'sam'))
    pushes = []
    def kax(tr): return axis(tr, 'BAT') // 2   # K is the parent of BAT
    def call_f(tr, t, pform):
        k = kax(tr)
        subj = L(L(K(L(1, tags[t])), L(pform, A(axis(tr, 'c')))), A(k))
        return L(2, subj, A(peg(k, armK(1 if same else t + 1))))
    prs = slots(n)
    for t in range(nf):
        pr0 = peg(axis(tree, 'Pr'), prs[0])
        pushes.append(call_f(tree, t, L(A(pr0), A(axis(tree, 'sam')))))
        tree = ('k%d' % t, tree)
    js = list(feeds)
    if order: js = [js[i] for i in order]
    def src(tr, x):          # a slot of the register of a k target, or None: the unknown sample
        if x is None: return A(axis(tr, 'sam'))
        a, i = x
        return A(peg(peg(axis(tr, 'k%d' % a), 3), slots(ms[a])[i]))
    for (t, x, y) in js:
        pushes.append(call_f(tree, t, L(src(tree, x), src(tree, y))))
        tree = ('j', tree)
    pa = axis(tree, 'Pr')
    sh = tup([A(peg(pa, s)) for s in prs[1:]] + [A(axis(tree, 'sam'))])
    body = L(K(7), sh)
    for p in reversed(pushes):
        body = L(8, p, body)
    R = L(6, L(3, A(3)), K(rreg0), L(8, L(2, A(1), A(armK(0))), body))
    bat = tup([R] + fs)
    return '[[& |] [%B 0]]'.replace('%B', n2h(bat)), R

def case(nm, n, ms, feeds, **kw):
    bus, R = core(n, ms, feeds, **kw)
    return (nm, bus, R)

def batch2(outdir):
    """family a (complements): two tags; each tag t has j sites [X.i |] and [| X.j] fed by the OTHER
    tag's target register X, so its two pushed members cover each other's subjects at the k site but not
    each other's j subjects: a fresh X pushes the complement of the newest member when that one was culled,
    which takes over k_t and restarts t's register, which feeds the other tag (Gaps 16, design A)"""
    os.makedirs(outdir, exist_ok=True)
    cs = []
    for (m1, m2) in [(3, 3), (3, 4), (4, 3), (4, 5), (5, 4), (3, 5)]:
        for (i1, j1, i2, j2) in [(0, m2 - 1, 0, m1 - 1), (m2 - 2, m2 - 1, m1 - 2, m1 - 1), (0, 1, 0, 1),
                                 (m2 - 1, 0, m1 - 1, 0), (1, m2 - 1, 0, m1 - 1)]:
            fd = [(0, (1, i1), None), (0, None, (1, j1)), (1, (0, i2), None), (1, None, (0, j2))]
            cs.append(case('a%d%d-%d%d%d%d' % (m1, m2, i1, j1, i2, j2), 3, [m1, m2], fd))
    # the j sites of one tag in the other order, and a ring of three tags
    for (m1, m2) in [(3, 3), (4, 5)]:
        fd = [(0, None, (1, m2 - 1)), (0, (1, 0), None), (1, None, (0, m1 - 1)), (1, (0, 0), None)]
        cs.append(case('ab%d%d' % (m1, m2), 3, [m1, m2], fd))
    for m in (3, 4):
        fd = [(0, (1, 0), None), (0, None, (1, m - 1)), (1, (2, 0), None), (1, None, (2, m - 1)),
              (2, (0, 0), None), (2, None, (0, m - 1))]
        cs.append(case('ar%d' % m, 3, [m, m, m], fd))
    paths = []
    for k in range(0, len(cs), 4):
        p = os.path.join(outdir, 'ta-%02d.hoon' % (k // 4))
        driver(cs[k:k + 4], p); paths.append(p)
    print(len(cs), 'cases in', len(paths), 'drivers')

def batch(outdir):
    os.makedirs(outdir, exist_ok=True)
    cs = []
    # x: two formulas cross-fed, lengths and slots varied
    for (n, m1, m2, i1, j1, i2, j2) in [(3, 4, 6, 1, 2, 1, 2), (3, 6, 4, 1, 2, 1, 2), (4, 5, 7, 0, 3, 0, 3),
                                         (2, 3, 5, 0, 2, 0, 2), (5, 4, 4, 1, 2, 2, 1), (3, 7, 3, 2, 1, 0, 2),
                                         (3, 5, 8, 3, 1, 1, 4), (6, 6, 9, 2, 5, 4, 1)]:
        cs.append(case('x%d-%d-%d-%d%d%d%d' % (n, m1, m2, i1, j1, i2, j2), n, [m1, m2],
                       [(0, (0, i1), (1, j1)), (1, (1, i2), (0, j2))]))
    # x with the j sites in the other order
    for (n, m1, m2, i1, j1, i2, j2) in [(3, 4, 6, 1, 2, 1, 2), (4, 5, 7, 0, 3, 0, 3), (3, 5, 8, 3, 1, 1, 4)]:
        cs.append(case('xo%d-%d-%d-%d%d%d%d' % (n, m1, m2, i1, j1, i2, j2), n, [m1, m2],
                       [(0, (0, i1), (1, j1)), (1, (1, i2), (0, j2))], order=[1, 0]))
    # y: each formula fed by its own target and the other one, but [own other] for both
    for (n, m1, m2, i, j) in [(3, 4, 6, 1, 2), (3, 6, 4, 2, 1), (4, 5, 5, 0, 4)]:
        cs.append(case('y%d-%d-%d-%d%d' % (n, m1, m2, i, j), n, [m1, m2],
                       [(0, (0, i), (1, j)), (1, (0, j), (1, i))]))
    # r: a ring of three formulas
    for (n, m1, m2, m3, i, j) in [(3, 4, 5, 6, 1, 2), (3, 6, 5, 4, 2, 1), (4, 3, 5, 7, 0, 2), (3, 5, 7, 9, 3, 1)]:
        cs.append(case('r%d-%d-%d-%d-%d%d' % (n, m1, m2, m3, i, j), n, [m1, m2, m3],
                       [(0, (0, i), (1, j)), (1, (1, i), (2, j)), (2, (2, i), (0, j))]))
    # s: one formula, two tags (f_1 = f_2 as nouns: the same identities' formula)
    for (n, m, i, j) in [(3, 5, 1, 3), (3, 4, 2, 1), (4, 6, 0, 4)]:
        bus, R = core(n, [m, m], [(0, (0, i), (1, j)), (1, (1, i), (0, j))], same=True)
        cs.append(('s%d-%d-%d%d' % (n, m, i, j), bus, R))
    # d: two j sites per formula (both cross-fed), so a target is pushed from two places
    for (n, m1, m2) in [(3, 4, 6), (3, 5, 3), (4, 6, 5)]:
        cs.append(case('d%d-%d-%d' % (n, m1, m2), n, [m1, m2],
                       [(0, (0, 1), (1, 2)), (0, (1, 0), (0, 2)), (1, (1, 1), (0, 2)), (1, (0, 0), (1, 2))]))
    # q: the quine as the register value (known without provenance through +patch-prod)
    for (n, m1, m2, i1, j1, i2, j2) in [(3, 4, 6, 1, 2, 1, 2), (4, 5, 7, 0, 3, 0, 3), (3, 6, 4, 1, 2, 1, 2),
                                         (3, 5, 8, 3, 1, 1, 4)]:
        cs.append(case('q%d-%d-%d-%d%d%d%d' % (n, m1, m2, i1, j1, i2, j2), n, [m1, m2],
                       [(0, (0, i1), (1, j1)), (1, (1, i2), (0, j2))], quine=True))
    # longer seeds (R's register of 8) and a ring on one formula
    for (n, m1, m2, i1, j1, i2, j2) in [(8, 4, 6, 1, 2, 1, 2), (8, 5, 7, 0, 3, 0, 3)]:
        cs.append(case('xl%d-%d-%d-%d%d%d%d' % (n, m1, m2, i1, j1, i2, j2), n, [m1, m2],
                       [(0, (0, i1), (1, j1)), (1, (1, i2), (0, j2))]))
    for (n, m, i, j) in [(3, 5, 1, 3), (4, 6, 2, 4)]:
        bus, R = core(n, [m, m, m], [(0, (0, i), (1, j)), (1, (1, i), (2, j)), (2, (2, i), (0, j))], same=True)
        cs.append(('rs%d-%d-%d%d' % (n, m, i, j), bus, R))
    # three cases per driver, so that one that does not return holds back only two others
    paths = []
    for k in range(0, len(cs), 3):
        p = os.path.join(outdir, 'tk-%02d.hoon' % (k // 3))
        driver(cs[k:k + 3], p); paths.append(p)
    print(len(cs), 'cases in', len(paths), 'drivers')

def summary(paths, verbose=False):
    """per case: passes of the root's loop, whether its %st hash recurs, pushes, re-pushes after a cull,
    %rec takeovers at the root's sites, and the root's callee set per pass (%pm-ent)"""
    g = {}
    exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure-stab.py')).read().split("\nv = '-v'")[0], g)
    rows = []
    for path in paths:
        case = None; cs = []
        for l in g['pmlines'](path):
            t = l.strip('[]').split()
            if t[0] == '%pm-case':
                case = dict(nm=t[2], root=None, passes=0, st=[], push={}, culled=set(), rep=0, rec={}, kids=[],
                            done=False, file=os.path.basename(path)); cs.append(case); continue
            if case is None: continue
            if t[0] == '%pm-new':
                if case['root'] is None: case['root'] = t[1]
                case['push'][t[1]] = case['push'].get(t[1], 0) + 1
                if t[1] in case['culled']: case['rep'] += 1
            elif t[0] == '%pm-cull':
                case['culled'] |= {m.strip('~[]') for m in t[2:] if m.strip('~[]')}
            elif t[0] == '%pm-pass' and t[1] == case['root']:
                case['passes'] = max(case['passes'], int(t[2])); case['st'].append(t[-1])
            elif t[0] == '%pm-rec' and t[1] == case['root']:
                case['rec'].setdefault(t[2], []).append(t[3])
            elif t[0] == '%pm-ent' and t[1] == case['root']:
                r, pas, mem = g['parse_ent'](l)
                for m in mem:
                    if m[0] == case['root']: case['kids'].append((pas, m[3]))
            elif t[0] == '%pm-graph': case['done'] = True
        for c in cs:
            tk = sum(len([1 for a, b in zip(v, v[1:]) if a != b]) for v in c['rec'].values())
            sets = [k for _, k in c['kids']]
            nch = len([1 for a, b in zip(sets, sets[1:]) if a != b])
            rows.append((c['file'], c['nm'], c['passes'], len(c['st']) != len(set(c['st'])),
                         sum(c['push'].values()), max(c['push'].values() or [0]), c['rep'], tk, nch, c['done']))
            if verbose:
                for pas, k in c['kids']: print('   ', c['nm'], 'pass', pas, 'root callees', ' '.join(k))
    print('file case root-passes st-recurs pushes max-push-of-one re-pushes takeovers callee-set-changes returned')
    for r in rows: print(*r)
    print('cases', len(rows), 'returned', sum(r[-1] for r in rows), 'st recurs', sum(r[3] for r in rows),
          'max root passes', max(r[2] for r in rows), 'takeovers', sum(r[7] for r in rows),
          're-pushes', sum(r[6] for r in rows), 'max pushes of one', max(r[5] for r in rows))

if __name__ == '__main__':
    if sys.argv[1] in ('--sum', '--sum-v'):
        summary(sys.argv[2:], sys.argv[1] == '--sum-v'); sys.exit(0)
    if sys.argv[1] == 'batch':
        batch(sys.argv[2]); sys.exit(0)
    if sys.argv[1] == 'debuglib':   # debuglib LIB.hoon OUT.hoon: the library of passmeasure.py plus
        # [%pm-sub mug head] at every push and [%pm-kid caller kid head] at every resolve (the head of
        # the subject sock, %big when its jam is over 400 bytes)
        hd = lambda v: ('?:(?=(%%void more.%s) %%void ?@(cape.more.%s %%atom =/(h (hed:so more.%s) '
                        '?:((gth (met 3 (jam h)) 400) %%big h))))' % (v, v, v))
        t = open(sys.argv[2]).read().split('\n')
        k = [i for i, l in enumerate(t) if l.startswith('    ~&  [%pm-new (mug id) index (lent stk.st)]')]
        assert len(k) == 1
        t[k[0] + 1:k[0] + 1] = ['    ~&  [%%pm-sub (mug id) %s]' % hd('id')]
        k = [i for i, l in enumerate(t) if l.startswith('        =*  resolve  $')]
        assert len(k) == 1
        t[k[0] + 1:k[0] + 1] = ['        ~&  [%%pm-kid (mug id) (mug id-there) %s]' % hd('id-there')]
        open(sys.argv[3], 'w').write('\n'.join(t)); sys.exit(0)
    if sys.argv[1] == 'batch2':
        batch2(sys.argv[2]); sys.exit(0)
    out, fam = sys.argv[1], sys.argv[2]
    a = [int(x) for x in sys.argv[3:]]
    if fam == 'x':
        n, m1, m2, i1, j1, i2, j2 = a[:7]
        cs = [case('x', n, [m1, m2], [(0, (0, i1), (1, j1)), (1, (1, i2), (0, j2))])]
    elif fam == 'q':
        n, m1, m2, i1, j1, i2, j2 = a[:7]
        cs = [case('q', n, [m1, m2], [(0, (0, i1), (1, j1)), (1, (1, i2), (0, j2))], quine=True)]
    elif fam == 'r':
        n, m1, m2, m3, i, j = a
        cs = [case('r', n, [m1, m2, m3], [(0, (0, i), (1, j)), (1, (1, i), (2, j)), (2, (2, i), (0, j))])]
    else:
        n, m, i, j = a
        cs = [case('s', n, [m, m], [(0, (0, i), (1, j)), (1, (1, i), (0, j))], same=True)]
    driver(cs, out)
