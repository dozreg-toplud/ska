#!/usr/bin/env python3
# usage: passmeasure-stab.py [-v] OUT.txt...
# Track F, 2026-11-27 (README Gaps 16, lemmas/Ska/PassStab.lean): reads the %pm-ent prints of the
# library of passmeasure.py (at the start of every pass of a component: every member with its DFS
# number, how its entry changed since the start of the previous pass of the same loop, %new if it
# was not a member then, and the mugs of its callees) and checks, per pass that goes on (from the
# start of pass p to the start of pass p+1 of the same loop):
#   step 1  (passOn_old): every identity that is a member at both starts keeps or lowers its entry
#           (the classes of passmeasure.py's runclass: a rise is a class None);
#   step 3  the candidates of the measure, over the identities of the case:
#     A     lex by DFS number (the oldest change dominates): some member at the start of p falls or
#           is culled (pushes get DFS numbers above every member at p);
#     B     lex by the DFS number of an identity's FIRST push in the case (a ghost priority that a
#           re-push keeps): the smallest first-push number among the members that fell or were
#           culled is below the smallest among those pushed (or none was pushed);
#     C     not an order: only whether some member at p falls, is culled, or keeps its entry and
#           changes its callee set (what an order on callee resolutions would have to rank);
#     D     lex by DFS number of (entry, +dirty) (StabLt of lemmas/Ska/PassStabM.lean): the first
#           member at p, by DFS number, whose value differs at p+1 falls: its entry fell, it was
#           culled, or its entry is the same and it went from dirty to clean;
#     DB    D by the first-push number, with each pushed identity a rise at its first-push number.
# A pass "goes on" when a later %pm-ent of the same loop follows it.  Needs the dirty flag of the
# print for D and DB (the library of passmeasure.py since 2026-11-27).
import re, sys

def pmlines(path):
    raw = []
    for l in open(path).read().split('\n'):
        if l[:1] in (' ', '\t', ']') and raw:
            raw[-1] += ' ' + l.strip()
        else:
            raw.append(l)
    raw = [re.sub(r'\s+', ' ', l).replace('[ %pm', '[%pm') for l in raw]
    ls = [l.strip() for l in raw if l.startswith('[%pm') or l.startswith('%pm')]
    h = len(ls) // 2
    if h and ls[:h] == ls[h:]:
        ls = ls[:h]   # the harness evaluates the expression twice
    return ls

def runclass(lc, pr, meq, ind, sk):
    if lc == '%more': return 'lc'
    if lc not in ('%eq', '%eqv'): return None
    if pr == '%less': return 'pr'
    if pr not in ('%eq', '%eqv'): return None
    if meq == '%.n': return 'map'
    if ind == '%more': return 'in'
    if ind not in ('%eq', '%eqv'): return None
    if sk == '%more': return 'sk'
    if sk not in ('%eq', '%eqv'): return None
    return 'none'

def num(x):
    x = x.replace('.', '')
    return int(x, 16) if x.startswith('0x') else int(x)

def parse_ent(l):
    # [%pm-ent root pass ~[[mug idx [c c c c c] ~[k ..]] ..]]
    t = l.replace('[', ' [ ').replace(']', ' ] ').split()
    root, pas = t[2], num(t[3])
    body = t[4:]
    mem = []
    i = 0
    # a member: '[' mug idx '[' c*5 ']' '~' ('[' k.. ']')? ']'
    while i < len(body):
        # a member: '[' mug idx dirty? '[' c*5 ']' '~' ('[' k.. ']')? ']'
        if body[i] == '[' and i + 4 < len(body) and (body[i + 3] == '[' or body[i + 4] == '['):
            mug, idx = body[i + 1], num(body[i + 2])
            o = 3 if body[i + 3] == '[' else 4
            dirty = None if o == 3 else body[i + 3] == '%.y'
            cls = tuple(body[i + o + 1:i + o + 6])
            assert body[i + o + 6] == ']' and body[i + o + 7] == '~', l[:200]
            j = i + o + 8
            kids = []
            if body[j] == '[':
                j += 1
                while body[j] != ']':
                    kids.append(body[j]); j += 1
                j += 1
            assert body[j] == ']', l[:200]
            mem.append((mug, idx, cls, tuple(sorted(kids)), dirty))
            i = j + 1
        else:
            i += 1
    return root, pas, mem

def analyse(paths, verbose):
    c = {}
    def inc(k, n=1):
        c[k] = c.get(k, 0) + n
    fails = {'1': [], 'A': [], 'B': [], 'C': [], 'D': [], 'DB': []}
    for path in paths:
        case = None
        first = {}     # mug -> DFS number of its first push in the case
        loops = {}     # root mug -> last (pass, members)
        for l in pmlines(path):
            tag = l.strip('[]').split()[0]
            if tag == '%pm-case':
                case = (path.split('/')[-1], l); first = {}; loops = {}; inc('cases'); continue
            if tag == '%pm-new':
                t = l.strip('[]').split()
                mug, idx = t[1], int(t[2], 16)
                first.setdefault(mug, idx)
                inc('pushes')
                continue
            if tag != '%pm-ent':
                continue
            root, pas, mem = parse_ent(l)
            inc('pass starts')
            prev = loops.get(root)
            loops[root] = (pas, mem)
            if pas == 1 or prev is None or prev[0] != pas - 1:
                continue
            inc('passes that go on')
            pm = {m[0]: m for m in prev[1]}
            cm = {m[0]: m for m in mem}
            fell, culled, pushed, callch = [], [], [], []
            for mug, idx, cls, kids, _ in mem:
                if cls[0] == '%new':
                    pushed.append(mug); continue
                inc('step 1: (identity, pass) pairs')
                k = runclass(*cls)
                if k is None:
                    inc('step 1: rises'); fails['1'].append((case, root, pas, mug, cls))
                elif k != 'none':
                    inc('step 1: falls'); fell.append(mug)
                elif pm[mug][3] != kids:
                    callch.append(mug)
            for mug in pm:
                if mug not in cm:
                    culled.append(mug)
            inc('step 1: culled', len(culled))
            if pushed: inc('passes with a push')
            if pushed and not fell and not culled: inc('passes with a push, no fall, no cull')
            if not pushed and not fell and not culled: inc('passes with no push, no fall, no cull')
            idx = lambda mug: pm[mug][1]
            # A
            if not (fell or culled):
                fails['A'].append((case, root, pas, len(pushed), len(callch)))
            # B
            fc = fell + culled
            if pushed:
                mp = min(first.get(m, 10 ** 9) for m in pushed)
                if not fc or min(first.get(m, 10 ** 9) for m in fc) >= mp:
                    fails['B'].append((case, root, pas, len(pushed),
                                       [(m, first.get(m)) for m in fc][:4], [(m, first.get(m)) for m in pushed][:4]))
            elif not fc:
                fails['B'].append((case, root, pas, 0, [], []))
            # C
            if not (fell or culled or callch):
                fails['C'].append((case, root, pas, len(pushed)))
            # D and DB: the first member at p (by DFS number, by first-push number) whose value
            # (entry, dirty) differs at p+1 must fall: entry fell, culled, or entry the same and
            # dirty went to clean; DB also needs it before every pushed identity's first push
            if mem and mem[0][4] is not None:
                for cand, key in (('D', lambda m: pm[m][1]), ('DB', lambda m: first.get(m, 10 ** 9))):
                    ch = []
                    for mug in pm:
                        if mug not in cm:
                            ch.append((key(mug), 'fall', mug, 'culled')); continue
                        k = runclass(*cm[mug][2])
                        d0, d1 = pm[mug][4], cm[mug][4]
                        if k not in ('none', None):
                            ch.append((key(mug), 'fall', mug, k))
                        elif d0 != d1:
                            ch.append((key(mug), 'fall' if d0 and not d1 else 'rise', mug, 'dirty %s->%s' % (d0, d1)))
                    if cand == 'DB':
                        for mug in pushed:
                            ch.append((first.get(mug, 10 ** 9), 'rise', mug, 'pushed'))
                    ch.sort(key=lambda x: (x[0], x[1] == 'fall'))
                    if not ch or ch[0][1] != 'fall':
                        fails[cand].append((case, root, pas, len(pushed), ch[:3]))
    for k in sorted(c):
        print(k, c[k])
    for k in ['1', 'A', 'B', 'C', 'D', 'DB']:
        print('fails of', 'step 1' if k == '1' else 'candidate ' + k + ':', len(fails[k]))
        for x in fails[k][:(10 ** 6 if verbose else 6)]:
            print('   ', x)

v = '-v' in sys.argv
analyse([p for p in sys.argv[1:] if p != '-v'], v)
