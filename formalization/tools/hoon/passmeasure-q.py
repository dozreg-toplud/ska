# random cores for step 2 (non-termination): two shared formulas, f (a self-shifting register that
# reads slots of its subject as formulas) and g (gfun: a restarting register that reads its slot 5),
# sites of either built from R's registers, earlier sites' products and constants, and feedback:
# R's new product takes slots of the sites' products in place of the unknown sample.
import sys, random
src = open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'passmeasure-repush.py')).read().split("if __name__")[0]
exec(src)
def mkf2(reads, selfax):
    rd = [L(2, A(3), A(peg(3, r))) for r in reads] + [L(9, 4, A(7))]
    body = L(tup(rd), L(A(4), L(A(22), L(A(23), A(15)))))
    return L(6, L(3, A(7)), A(2), L(8, L(2, A(1), A(selfax)), body))
def qcase(rnd, idx):
    nreg = rnd.choice([1, 2, 3])
    ns = [rnd.choice([3, 4, 5, 6, 8]) for _ in range(nreg)]
    reads = rnd.choice([(22, 23), (10, 22, 23), (23,), (22,), (10, 23), (10,)])
    f = mkf2(reads, 26); gm = rnd.choice([3, 4, 6]); g = gfun(27, gm)
    x = L(0, 1); a = 7
    base = K(tuple_val([tuple_val([x] * n) for n in ns]))
    rs = slots(nreg) if nreg > 1 else [1]
    regsl = [[peg(peg(2, rs[i]), s) for s in slots(n)] for i, n in enumerate(ns)]
    nsite = rnd.choice([2, 3, 4, 5, 6])
    kinds = []; sites = []
    gsl = slots(gm + 1)
    for j in range(nsite):
        pool = [under(s, j) for sl in regsl for s in sl]
        for i in range(j):
            pa = under(2, j - 1 - i)
            if kinds[i] == 'f': pool += [peg(pa, s) for s in (14, 30, 31, 2)]
            else: pool += [peg(pa, s) for s in gsl[1:]]
        if j > 0 and rnd.random() < 0.6: pool = pool[-8:]
        kd = rnd.choice('ffg'); kinds.append(kd)
        def pick():
            r = rnd.random()
            if r < 0.15: return K(x)
            if r < 0.25: return A(peg(under(3, j), 3))      # the unknown sample
            return A(rnd.choice(pool))
        if kd == 'f':
            sub = tup([K(a), pick(), pick(), pick()]); fm = f
        else:
            sub = L(K(a), pick()); fm = g
        sites.append(L(2, L(sub, A(under(3, j))), K(fm)))
    # R's new product: the registers shifted; with feedback, a register's new last slot is a slot of
    # a site's product instead of the sample
    hs = []
    for sl in regsl:
        last = A(under(peg(3, 3), nsite))
        if rnd.random() < 0.6:
            i = rnd.randrange(nsite); pa = under(2, nsite - 1 - i)
            last = A(peg(pa, rnd.choice((14, 30, 31) if kinds[i] == 'f' else gsl[1:])))
        hs.append(tup([A(under(s, nsite)) for s in sl[1:]] + [last]))
    body = tup(hs)
    for j in reversed(range(nsite)):
        body = L(8, sites[j], body)
    R = L(6, L(3, A(3)), base, L(8, L(9, 4, A(1)), body))
    bat = L(R, L(f, g))
    return ('q%d' % idx, '[[[& &] |] [%B 0]]'.replace('%B', n2h(bat)), L(9, 4, A(1)))
seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rnd = random.Random(seed)
driver([qcase(rnd, seed * 1000 + k) for k in range(n)], out)
