import msgpy, random
from msgpy import *
from enum3help import degen
random.seed(1)
S = [s for k in range(4) for s in shapes(k) if not degen(s)]
C = [x for k in range(4) for x in capes(k)]
print(len(S), 'shapes', len(C), 'capes')
def run(split, n):
    msgpy.SPLIT = split; msg.cache_clear(); mnone.cache_clear()
    best = None; f = 0
    for _ in range(n):
        a, b, d = random.choice(S), random.choice(S), random.choice(S); cc = random.choice(C)
        if msg(msg(a, b, cc), d, cc) != msg(a, msg(b, d, cc), cc):
            f += 1; k = len(str((a, b, d, cc)))
            if best is None or k < best[0]: best = (k, a, b, d, cc)
    return f, best
for sp in (6, 10**6):
    f, best = run(sp, 1500000)
    print('split', sp, 'failures', f, 'of 1500000', best and [show(x) for x in best[1:]])
    if best:
        _, a, b, d, cc = best
        print('  (a b) d =', show(msg(msg(a, b, cc), d, cc)), ' a (b d) =', show(msg(a, msg(b, d, cc), cc)))
        print('  ', lean(a), lean(b), lean(d), lean(cc))
