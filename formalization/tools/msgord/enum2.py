from msgpy import *
BTT = B(T, T); BIG = B(BTT, BTT)
c = ('c', ('c', 'n', 'n'), ('c', 'n', 'n'))
e = T
for nn in [BTT, BIG, T, BTT, BIG, T]:
    e2 = msg(nn, e, c); print(show(nn), ':', show(e), '->', show(e2)); e = e2
# associativity on shapes up to 2 inner nodes, capes up to 2 inner
S = [s for k in range(3) for s in shapes(k)]
C = [x for k in range(3) for x in capes(k)]
na = 0; ex = None; nt = 0
for cc in C:
    for a in S:
        for b in S:
            ab = msg(a, b, cc)
            for d in S:
                nt += 1
                if msg(ab, d, cc) != msg(a, msg(b, d, cc), cc):
                    na += 1
                    if ex is None or len(str(ex)) > len(str((a, b, d, cc))): ex = (a, b, d, cc)
print('assoc: triples', nt, 'failures', na, 'smallest', [show(x) for x in ex])
a, b, d, cc = ex
print(show(msg(msg(a, b, cc), d, cc)), 'vs', show(msg(a, msg(b, d, cc), cc)))
