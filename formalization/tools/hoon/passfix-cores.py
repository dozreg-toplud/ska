#!/usr/bin/env python3
# usage: passfix-cores.py all OUT.hoon | grid OUT.hoon | one OUT.hoon n N1 N2 m0 mr l i j [n2]
#        passfix-cores.py --tab OUT.txt...        (track F, README Gaps 16)
# One driver (+ska-callgraph per case, the format of passmeasure-repush.py) with
#   all   the 88 cores of passmeasure-take.py: family X (batch, 32), A (batch2, 34), D (batch3, 22)
#   grid  the search for a smaller takecycle: core3 of passmeasure-take.py with sites k (tag 5,
#         p = [R.0 |]), a chain of N1 relays and one of N2 relays from k's target (relay p = X.l
#         whole), a (tag 5, p = [Z1.i |], Z1 the end of chain 1, or k's target when N1 = 0) and
#         b (tag 5, p = [| Z2.j]); R's register n slots, f_5's m0, the relays' mr
#   grid2 chains (0,2) (0,3) (1,2) (1,3) (0,4) with the slots l, i, j varied, and b on R's register
#   one   one such case (n2 > 0: the sites k, chain 1, a only, with b reading R's own register
#         slot n2-1 instead of chain 2: a variant without the second chain)
# Run the driver with a library of passfix.py instrumented by passmeasure.py and --cap (so a loop
# that does not end stops at the cap and prints %pm-capped), then --tab: per case, the root's passes,
# whether it was capped, the %st period of the root's loop, pushes, re-pushes, takeovers.
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
g = {'__name__': 'passfix_cores', '__file__': os.path.join(D, 'passmeasure-take.py')}
exec(open(os.path.join(D, 'passmeasure-take.py')).read(), g)
got = []
g['driver'] = lambda cs, path: got.extend(cs)

def ecase(n, N1, N2, m0, mr, l, i, j, n2=0):
    w = lambda x: ('w', x); hd = lambda x: ('c', x, None); tl = lambda x: ('c', None, x)
    S = lambda a, k: ('s', a, k)
    st = [(0, hd(('R', 0)))]; r = 1; ends = []
    for Nc in ((N1,) if n2 else (N1, N2)):
        prev = 0
        for _ in range(Nc):
            st.append((r, w(S(prev, l)))); prev = len(st) - 1; r += 1
        ends.append(prev)
    st.append((0, hd(S(ends[0], i))))
    st.append((0, tl(('R', n2 - 1) if n2 else S(ends[1], j))))
    nm = 'e%d-%d%d-%d%d-%d%d%d' % (n, N1, N2, m0, mr, l, i, j) + ('-r%d' % n2 if n2 else '')
    return (nm, *g['core3'](n, [m0] + [mr] * (r - 1), st))

def write(cs, path):
    t = ['=/  cases=(list [nam=@tas bus=sock fol=*])', '  :~']
    for (nm, b, f) in cs:
        t.append(f'      [%{nm} {b} {g["n2h"](f)}]')
    t += ['  ==', '=/  n=@ud  0', '|-  ^-  @', '?~  cases  ~&  %pm-done  0',
          '~&  [%pm-case n nam.i.cases]',
          '=/  f=^  ?>(?=(^ fol.i.cases) fol.i.cases)',
          '=/  res  (ska-callgraph [bus.i.cases f] ~ [~ ~ ~ ~ ~])',
          '~&  [%pm-graph n ~(wyt by -.res)]',
          '$(cases t.cases, n +(n))', '']
    open(path, 'w').write('\n'.join(t))
    print(len(cs), 'cases in', path)

def tab(paths):
    import re
    for path in paths:
        case = None; rows = []
        ls = g['pmlines'](path) if 'pmlines' in g else None
        if ls is None:
            ex = {}
            exec(open(os.path.join(D, 'passmeasure-stab.py')).read().split("\nv = '-v'")[0], ex)
            ls = ex['pmlines'](path)
        for l in ls:
            t = l.strip('[]').split()
            if t[0] == '%pm-case':
                case = dict(nm=t[2], root=None, passes=0, st=[], push={}, culled=set(), rep=0, cap=False,
                            done=False, rec={}); rows.append(case); continue
            if case is None: continue
            if t[0] == '%pm-new':
                if case['root'] is None: case['root'] = t[1]
                case['push'][t[1]] = case['push'].get(t[1], 0) + 1
                if t[1] in case['culled']: case['rep'] += 1
            elif t[0] == '%pm-cull':
                case['culled'] |= {m.strip('~[]') for m in t[2:] if m.strip('~[]')}
            elif t[0] == '%pm-pass' and t[1] == case['root']:
                case['passes'] = max(case['passes'], int(t[2].replace('.', ''))); case['st'].append(t[-1])
            elif t[0] == '%pm-rec' and t[1] == case['root']:
                case['rec'].setdefault(t[2], []).append(t[3])
            elif t[0] == '%pm-capped': case['cap'] = True
            elif t[0] == '%pm-graph': case['done'] = True
        print('case root-passes capped period-from pushes re-pushes takeovers returned')
        for c in rows:
            st = c['st']; per = '-'
            last = {}
            for k, h in enumerate(st):
                if h in last:
                    per = '%d@%d' % (k - last[h], last[h] + 1); break
                last[h] = k
            tk = sum(len([1 for x, y in zip(v, v[1:]) if x != y]) for v in c['rec'].values())
            print(c['nm'], c['passes'], int(c['cap']), per, sum(c['push'].values()), c['rep'], tk, int(c['done']))
        print('cases', len(rows), 'returned', sum(c['done'] for c in rows), 'capped', sum(c['cap'] for c in rows),
              'max passes', max([c['passes'] for c in rows] or [0]))

if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == '--tab':
        tab(a[1:]); sys.exit(0)
    mode, out = a[0], a[1]
    if mode == 'all':
        tmp = out + '.d'
        g['batch'](tmp); g['batch2'](tmp); g['batch3'](tmp)
        write(got, out)
    elif mode == 'grid':
        cs = []
        for n in (2, 3):
            for (N1, N2) in ((0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (2, 4)):
                for m in (2, 3, 4):
                    for s in (0, 1):
                        if s < m: cs.append(ecase(n, N1, N2, m, m, s, s, s))
        write(cs, out)
    elif mode == 'grid2':   # shorter chains with the slots varied, and b on R's own register
        import itertools
        cs = []
        for (N1, N2) in ((0, 2), (0, 3), (1, 2), (1, 3), (0, 4)):
            for (l, i, j) in itertools.product((0, 1), repeat=3):
                cs.append(ecase(2, N1, N2, 3, 3, l, i, j))
        for (N1, N2) in ((1, 2), (0, 3), (1, 3)):
            for (l, i, j) in itertools.product((0, 1, 2), repeat=3):
                cs.append(ecase(2, N1, N2, 4, 4, l, i, j))
        for n in (2, 3, 4):
            for N1 in (1, 2, 3):
                for n2 in range(1, n + 1):
                    cs.append(ecase(n, N1, 0, 3, 3, 0, 0, 0, n2))
        write(cs, out)
    elif mode in ('ablate', 'ablate2'):  # the smallest witness e2-23-33-000 with one part changed or removed
        w = lambda x: ('w', x); hd = lambda x: ('c', x, None); tl = lambda x: ('c', None, x)
        S = lambda a, k: ('s', a, k)
        def sites(N1=2, N2=3, a=True, b=True, kp=None, ap=hd, bp=tl):
            st = [(0, kp or hd(('R', 0)))]; r = 1; ends = []
            for Nc in (N1, N2):
                prev = 0
                for _ in range(Nc):
                    st.append((r, w(S(prev, 0)))); prev = len(st) - 1; r += 1
                ends.append(prev)
            if a: st.append((0, ap(S(ends[0], 0))))
            if b: st.append((0, bp(S(ends[1], 0))))
            return st, r
        cs = []
        def add(nm, m0=3, mr=3, **kw):
            st, r = sites(**kw)
            cs.append((nm, *g['core3'](2, [m0] + [mr] * (r - 1), st)))
        add('full'); add('chains22', N1=2, N2=2); add('chains33', N1=3, N2=3); add('chains13', N1=1, N2=3)
        add('chains12', N1=1, N2=2); add('chains34', N1=3, N2=4); add('noa', a=False); add('nob', b=False)
        add('f5m2', m0=2); add('relm2', mr=2); add('f5m4', m0=4); add('relm4', mr=4)
        add('kwhole', kp=w(('R', 0))); add('awhole', ap=w); add('bwhole', bp=w)
        add('both-head', bp=hd)
        if a[0] == 'ablate2':   # other chain pairs, k's p a cons or whole
            cs = []
            for (N1, N2) in ((1, 1), (2, 1), (2, 0), (3, 0), (3, 1), (3, 2), (2, 2), (1, 0), (0, 0)):
                add('c%d%d' % (N1, N2), N1=N1, N2=N2)
                add('c%d%d-kw' % (N1, N2), N1=N1, N2=N2, kp=w(('R', 0)))
            add('c22-noa', N1=2, N2=2, a=False); add('c22-nob', N1=2, N2=2, b=False)
            add('c22-f5m2', N1=2, N2=2, m0=2); add('c22-relm2', N1=2, N2=2, mr=2)
        write(cs, out)
    elif mode == 'one':
        write([ecase(*[int(x) for x in a[2:]])], out)
