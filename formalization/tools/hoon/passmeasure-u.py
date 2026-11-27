# random self-calls of ONE formula f at many subjects (every call is f: exact match, %rec, %he or a push),
# for the %rec takeover: f on [P K], P = [a y1 y2 y3], K = [f sam]; f reads some slots of P as code
# (direct when known: less-code, else indi), calls itself at subjects built from P, earlier sites'
# products, constants and the sample, and returns [reads [a z1 z2 z3]] with z_i from the same pool.
import sys, random
src = open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'passmeasure-repush.py')).read().split("if __name__")[0]
exec(src)
x = L(0, 1); a = 7
PS = [4, 10, 22, 23]           # slots of P in [P K] at 2: peg(2, slots(4))
def ucase(rnd, idx):
    reads = rnd.sample([10, 22, 23], rnd.choice([1, 2]))
    nsite = rnd.choice([1, 2, 3, 4])
    sites = []
    def pool(j):
        p = [under(s, j) for s in PS[1:]]
        for i in range(j):
            pa = under(2, j - 1 - i)
            p += [peg(pa, s) for s in (14, 30, 31)]
        return p
    def pick(j):
        r = rnd.random()
        if r < 0.2: return K(x)
        if r < 0.45: return A(peg(under(3, j), 3))
        return A(rnd.choice(pool(j)))
    for j in range(nsite):
        sub = tup([K(a), pick(j), pick(j), pick(j)])
        kax = under(3, j)
        sites.append(L(2, L(sub, A(kax)), A(peg(kax, 2))))
    rd = [L(2, A(under(1, 0) if False else under(3, nsite) if False else 1), A(under(peg(2, r // 2 * 0 + r) if False else r, nsite)))
          for r in reads]
    # reads run P.r on the subject after the pushes: P at under(2, nsite)
    rd = [L(2, A(1), A(peg(under(2, nsite), {10: 6, 22: 14, 23: 15}[r]))) for r in reads]
    fin = L(tup(rd), tup([K(a), pick(nsite), pick(nsite), pick(nsite)]))
    body = fin
    for j in reversed(range(nsite)):
        body = L(8, sites[j], body)
    f = L(6, L(3, A(7)), L(K(0), A(2)), body)
    P0 = tup([K(a)] + [K(x) if rnd.random() < 0.7 else A(0) for _ in range(3)])
    # the root: f on [[a x x x] [f |]] (some y unknown in the bus)
    ys = [rnd.random() < 0.75 for _ in range(3)]
    def nc(h, t):
        return h if h == t and h in ('&', '|') else '[%s %s]' % (h, t)
    cap = nc('&', nc('&' if ys[0] else '|', nc('&' if ys[1] else '|', '&' if ys[2] else '|')))
    def nd(c, h, t):
        return '0' if c == '|' else '[%s %s]' % (h, t)
    c3 = nc('&' if ys[1] else '|', '&' if ys[2] else '|')
    d3 = nd(c3, '[0 1]' if ys[1] else '0', '[0 1]' if ys[2] else '0')
    c2 = nc('&' if ys[0] else '|', c3)
    d2 = nd(c2, '[0 1]' if ys[0] else '0', d3)
    dat = '[7 %s]' % d2
    bus = '[[%s [& |]] [%s [%s 0]]]' % (cap, dat, n2h(f))
    return ('u%d' % idx, bus, n2h(f) and f)
seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rnd = random.Random(seed)
driver([ucase(rnd, seed * 1000 + k) for k in range(n)], out)
