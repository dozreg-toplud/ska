#!/usr/bin/env python3
# usage: passmeasure-branch.py --instrument IN.hoon OUT.hoon
#        passmeasure-branch.py [-v] OUT.txt...                      (track F, README Gaps 16)
# FinBranch on traces: how many distinct identities one identity pushes over one call of
# +ska-callgraph, and what bounds them.  --instrument adds to a library already instrumented by
# passmeasure.py (and passmeasure-quiet.py) one print at the start of every +run:
#   [%pb-beg mug sites fol-mug]   sites: the %2 and %9 nodes of the formula, walked along the
#        formula grammar (the call sites fol-loop can reach; %8, %10, %11 operands included)
# The check pairs %pb-beg with the %pm-run at the end of the same run (runs nest: a run calls
# +analyze of new identities, whose first runs are inside it), so the parent of a %pm-new
# (a push) is the innermost open run, or the root call when no run is open.  Per case (a
# %pm-case line, or a %pm-new at index 0 and depth 0): for every parent, the distinct kids it
# pushed, their distinct formulas, its call sites, and the pushes of kids already pushed by it
# (a re-push after a +cull).  Prints the largest counts and the parents whose distinct kids
# exceed their call sites.
import re, sys, os
D = os.path.dirname(os.path.abspath(__file__))

SITES = [
    '    =/  pb-sites',
    '      |=  f=*',
    '      ^-  @ud',
    '      ?@  f  0',
    '      ?^  -.f  (add $(f -.f) $(f +.f))',
    '      ?@  +.f  0',
    '      =/  o=@  -.f',
    '      =/  a=*  +<.f',
    '      =/  b=*  +>.f',
    '      ?:  |(=(o 0) =(o 1))  0',
    '      ?:  |(=(o 3) =(o 4))  $(f +.f)',
    '      ?:  =(o 2)  +((add $(f a) $(f b)))',
    '      ?:  |(=(o 5) =(o 7) =(o 8) =(o 12))  (add $(f a) $(f b))',
    '      ?:  =(o 6)  ?@(b 0 (add $(f a) (add $(f -.b) $(f +.b))))',
    '      ?:  =(o 9)  +($(f b))',
    '      ?:  |(=(o 10) =(o 11))  ?@(a $(f b) (add $(f +.a) $(f b)))',
    '      0',
    '    ~&  [%pb-beg (mug id) (pb-sites +.id) (mug +.id)]',
]

def instrument(inp, out):
    src = open(inp).read().split('\n')
    k = [i for i, l in enumerate(src) if l == '  ++  run']
    assert k
    a0 = k[0]
    j = [i for i, l in enumerate(src) if l == '    =.  runs.stats.st  +(runs.stats.st)' and i > a0][0]
    src[j + 1:j + 1] = SITES
    open(out, 'w').write('\n'.join(src))

def pmlines(path):
    raw = []
    for l in open(path).read().split('\n'):
        if l[:1] in (' ', '\t') and raw:
            raw[-1] += ' ' + l.strip()
        else:
            raw.append(l)
    raw = [re.sub(r'\s+', ' ', l).replace('[ %p', '[%p') for l in raw]
    return [l.strip() for l in raw if l[:3] in ('[%p', '%pm', '%pb')]

def check(paths, verbose):
    tot = {'cases': 0, 'runs': 0, 'pushes': 0, 'parents': 0}
    maxk = (0, None); maxf = (0, None); maxs = (0, None); over = []; repush = 0; hist = {}
    persite = (0, None); maxpf = (0, None); hpf = {}; overf = []
    for path in paths:
        fam = os.path.basename(path)
        case = None
        def flush():
            nonlocal maxk, maxf, persite, maxpf
            if case is None: return
            for p, (kids, forms, sites) in case['par'].items():
                tot['parents'] += 1
                n = len(kids)
                forms = {case['fol'].get(k, k) for k in kids}
                byf = {}
                for k in kids: byf[case['fol'].get(k, k)] = byf.get(case['fol'].get(k, k), 0) + 1
                mp = max(byf.values()) if byf else 0
                hpf[mp] = hpf.get(mp, 0) + 1
                if mp > maxpf[0]: maxpf = (mp, (case['name'], p, sites, n, len(forms)))
                if sites is not None and n > sites and len(forms) > sites: overf.append((case['name'], p, n, len(forms), sites))
                hist[n] = hist.get(n, 0) + 1
                if n > maxk[0]: maxk = (n, (case['name'], p, sites))
                if len(forms) > maxf[0]: maxf = (len(forms), (case['name'], p, sites))
                if sites is not None and sites > 0 and n > sites:
                    over.append((case['name'], p, n, sites))
                if sites:
                    r = n / sites
                    if r > persite[0]: persite = (r, (case['name'], p, n, sites))
        stack = []
        for l in pmlines(path):
            t = l.strip('[]').split()
            tag = t[0]
            if tag == '%pm-case' or (tag == '%pm-new' and t[2] in ('0', '0x0') and t[3] == '0'):
                flush()
                tot['cases'] += 1
                case = {'name': fam + ':' + ' '.join(t[1:3]), 'par': {}, 'sites': {}, 'fol': {}}
                stack = []
                if tag == '%pm-case': continue
            if case is None:
                tot['cases'] += 1
                case = {'name': fam, 'par': {}, 'sites': {}, 'fol': {}}
            if tag == '%pb-beg':
                tot['runs'] += 1
                stack.append(t[1])
                case['sites'][t[1]] = int(t[2].replace('.', ''))
                case['fol'][t[1]] = t[3]
                continue
            if tag == '%pm-run':
                if stack and stack[-1] == t[1]:
                    stack.pop()
                elif t[1] in stack:
                    while stack and stack[-1] != t[1]: stack.pop()
                    stack.pop()
                continue
            if tag == '%pm-new':
                tot['pushes'] += 1
                par = stack[-1] if stack else '<root>'
                e = case['par'].setdefault(par, [set(), set(), case['sites'].get(par)])
                e[2] = case['sites'].get(par)
                if t[1] in e[0]: repush += 1
                e[0].add(t[1])
                continue
        flush()
    print('cases', tot['cases'], 'runs', tot['runs'], 'pushes', tot['pushes'], 'parents', tot['parents'])
    print('re-pushes of a kid by the same parent:', repush)
    print('largest distinct kids of one parent:', maxk[0], maxk[1])
    print('largest distinct kid formulas of one parent:', maxf[0], maxf[1])
    print('largest kids / sites of one parent:', round(persite[0], 3), persite[1])
    print('parents with more distinct kids than call sites:', len(over))
    for x in over[:20]: print('  ', x)
    print('histogram of distinct kids per parent:', sorted(hist.items()))
    print('largest distinct kids of one parent with one formula:', maxpf[0], maxpf[1])
    print('histogram of that per parent:', sorted(hpf.items()))
    print('parents with more distinct kid formulas than call sites:', len(overf))
    for x in overf[:10]: print('  ', x)

if sys.argv[1] == '--instrument':
    instrument(sys.argv[2], sys.argv[3])
else:
    v = sys.argv[1] == '-v'
    check(sys.argv[2:] if v else sys.argv[1:], v)
