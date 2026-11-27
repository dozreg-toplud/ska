#!/usr/bin/env python3
# usage: passmeasure-tab.py OUT.txt...  per case: root passes, all passes, pushes of the most pushed identity,
#   total pushes, identities, re-pushes after a cull, runs, returned; --take OUT.txt...: per (caller, kid) the
#   sequence of identities it resolved to (%pm-rec, %pm-ex of the library of passmeasure.py), takeovers, returns A..B..A
import sys, os, re
pm = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure.py')
src = open(pm).read().split("if sys.argv[1] in ('--sum'")[0]
ns = {'__file__': pm}; exec(src, ns)
def stats(path):
    res = {}; case = None
    for l in ns['pmlines'](path):
        t = l.strip('[]').split()
        if t[0] == '%pm-case':
            case = t[2]; res[case] = dict(push={}, culled=set(), rep=0, passes={}, done=False, runs=0, pl=0)
        elif case is None: continue
        elif t[0] == '%pm-new':
            r = res[case]; r['push'][t[1]] = r['push'].get(t[1], 0) + 1
            if t[1] in r['culled']: r['rep'] += 1
        elif t[0] == '%pm-cull':
            res[case]['culled'] |= {m.strip('~[]') for m in t[2:] if m.strip('~[]')}
        elif t[0] == '%pm-pass':
            r = res[case]; r['passes'][t[1]] = max(r['passes'].get(t[1], 0), int(t[2])); r['pl'] += 1
        elif t[0] == '%pm-run': res[case]['runs'] += 1
        elif t[0] == '%pm-graph': res[case]['done'] = True
    out = []
    for c, r in res.items():
        mp = max(r['push'].values()) if r['push'] else 0
        out.append((c, max(r['passes'].values()) if r['passes'] else 0, r['pl'], mp, sum(r['push'].values()),
                    len(r['push']), r['rep'], r['runs'], r['done']))
    return out
def takeovers(paths):
    tot = dict(cases=0, rec=0, keys=0, takeovers=0, returns=0, maxchanges=0)
    ex = []
    for p in paths:
        case = None; seq = {}
        def flush():
            for k, v in seq.items():
                c = [v[0]]
                for t in v[1:]:
                    if t != c[-1]: c.append(t)
                tot['keys'] += 1; tot['takeovers'] += len(c) - 1
                tot['maxchanges'] = max(tot['maxchanges'], len(c) - 1)
                if len(set(c)) < len(c): tot['returns'] += 1; ex.append((p.split('/')[-1], case, k, c))
        for l in ns['pmlines'](p):
            t = l.strip('[]').split()
            if t[0] == '%pm-case': flush(); seq = {}; case = t[2]; tot['cases'] += 1
            elif t[0] == '%pm-rec': tot['rec'] += 1; seq.setdefault((t[1], t[2]), []).append(t[3])
            elif t[0] == '%pm-ex': seq.setdefault((t[1], t[2]), []).append(t[2])
        flush()
    print(tot)
    for e in ex[:10]: print(e)

if __name__ == '__main__' and sys.argv[1] == '--take':
    takeovers(sys.argv[2:]); sys.exit(0)
if __name__ == '__main__':
    print('case root-passes all-passes max-push-of-one total-push identities re-push runs done')
    for p in sys.argv[1:]:
        for row in stats(p): print(*row)
