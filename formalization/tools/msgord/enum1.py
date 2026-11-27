import sys, time
from msgpy import *
K = int(sys.argv[1]); KC = int(sys.argv[2])
S = [s for k in range(K + 1) for s in shapes(k)]
C = [c for k in range(KC + 1) for c in capes(k, ('n',))]
print('shapes', len(S), 'capes', len(C), 'pairs', len(S) ** 2)
t = time.time()
bad = {'abs': [], 'comm': [], 'abs2': []}
big = 0; n = 0
for c in C:
    for a in S:
        for b in S:
            n += 1
            m = msg(a, b, c)
            if regs(SPLIT, a, 0) > SPLIT or regs(SPLIT, b, 0) > SPLIT or regs(SPLIT, m, 0) > SPLIT: big += 1
            if msg(a, m, c) != m and len(bad['abs']) < 5: bad['abs'].append((a, b, c, m, msg(a, m, c)))
            if msg(b, a, c) != m and len(bad['comm']) < 5: bad['comm'].append((a, b, c))
            if msg(m, b, c) != m and len(bad['abs2']) < 5: bad['abs2'].append((a, b, c))
print('checked', n, 'triples (a,b,cape);', big, 'with a side or the result over split-max;', time.time() - t, 's')
for k, v in bad.items():
    print(k, len(v))
    for x in v: print('  ', [show(y) for y in x])
