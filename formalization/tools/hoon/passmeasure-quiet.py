#!/usr/bin/env python3
# usage: passmeasure-quiet.py --instrument IN.hoon OUT.hoon
#        passmeasure-quiet.py [-v] OUT.txt...                       (track F, README Gaps 16)
# The measure of the pass loop of +analyze after dab8478 (no +cull between passes; stable also
# needs every member the root reaches to be clean), checked on traces.  --instrument adds to a
# library already instrumented by passmeasure.py (lib.hoon) two prints at every pass start:
#   [%pq-s root pass next g-size g-kept]   g-kept: every identity in g at the previous start of
#        this loop is still in g (the first component, identities not in g, never rises)
#   [%pq-m root pass ~[[member dirty swept callees-mug] ..]]   every member above the root: +dirty,
#        listed by this pass's +sweep (reached), and the mug of its callee set
# and, at the end of +run, [%pq-cal mug old-size new-size] for a run after the first with no
# `changed` whose callee set changed (what a second quiet pass in a row needs)
# The check, per pass loop (root, passes 1, 2, ..), with the %pm-run lines of passmeasure.py:
#   A  g-kept at every start; next and the size of g never fall
#   B  a pass that goes on with a change and no push has no run against the entry measure
#      (runclass of passmeasure.py) and one run that falls
#   C  a QUIET pass (changed no, next the same, and the loop goes on): its runs keep the five
#      fields; whether some member's callee set changed in it; the dirty members at the next start
#      are a subset of those at its start, minus every one reached at its start; their number falls
#   D  the triple (B - next, the entries, the dirty members) falls at every pass that goes on
# and prints the longest run of consecutive quiet passes, and the largest pass counts.
import re, sys, os
D = os.path.dirname(os.path.abspath(__file__))

def instrument(inp, out):
    src = open(inp).read().split('\n')
    def find(anchor, start=0):
        k = [i for i, l in enumerate(src) if l == anchor and i >= start]
        assert k, anchor
        return k[0]
    a0 = find('  ++  analyze')
    i = find('    =/  pass=@  1', a0)
    src[i + 1:i + 1] = ['    =/  pq-g=(set identity)  ~']
    i = find('    =/  next-before=@uxsite  next.st', a0)
    src[i:i] = [
        '    =/  pq-gok=?  (~(all in pq-g) |=(i=identity (~(has by g.st) i)))',
        '    ~&  [%pq-s (mug id) pass next.st ~(wyt by g.st) pq-gok]',
        '    ~&  :*  %pq-m  (mug id)  pass',
        '            %+  turn  (above id stk.st)',
        '            |=  i=identity',
        '            :*  (mug i)  (dirty i st)  ?=(^ (find ~[i] members))',
        '                (mug callees:(git-g g.st i))',
        '            ==',
        '        ==',
        '    =.  pq-g  ~(key by g.st)',
    ]
    # a run after the first that keeps the five fields of `changed` and changes its callee set
    r0 = find('  ++  run', a0)
    i = find('      =.  tick.st  +(tick.st)', r0)
    src[i:i] = [
        '      ~?  &(!pm-first !changed !=(callees.data-new callees.data))',
        '        [%pq-cal (mug id) ~(wyt in callees.data) ~(wyt in callees.data-new)]',
    ]
    open(out, 'w').write('\n'.join(src))

g = {'__name__': 'pmq', '__file__': os.path.join(D, 'passmeasure.py')}
_src = open(os.path.join(D, 'passmeasure.py')).read()
_src = _src[:_src.index("if sys.argv[1] in ('--sum'")]
exec(_src, g)
runclass = g['runclass']

def pmlines(path):
    raw = []
    for l in open(path).read().split('\n'):
        if l[:1] in (' ', '\t') and raw:
            raw[-1] += ' ' + l.strip()
        else:
            raw.append(l)
    raw = [re.sub(r'\s+', ' ', l).replace('[ %pm', '[%pm').replace('[ %pq', '[%pq') for l in raw]
    ls = [l.strip() for l in raw if l[:4] in ('[%pm', '[%pq') or l[:3] in ('%pm', '%pq')]
    h = len(ls) // 2
    if h and ls[:h] == ls[h:]:
        ls = ls[:h]
    return ls

MEM = re.compile(r'\[([\d.]+) (%\.[yn]) (%\.[yn]) ([\d.]+)\]')

def check(paths, verbose):
    c = {}
    def inc(k, n=1): c[k] = c.get(k, 0) + n
    bad = []
    maxq = (0, None)
    maxroot = {}     # family -> (passes, case)
    for path in paths:
        fam = os.path.basename(path)
        case = fam
        loops = {}   # root mug -> state of its current loop
        stack = []   # open passes: [root, pass, runs, pushed]
        for l in pmlines(path):
            t = l.strip('[]').split()
            tag = t[0]
            if tag == '%pm-case':
                case = fam + ':' + ' '.join(t[1:3]); loops = {}; stack = []; continue
            if tag == '%pm-new':
                for p in stack: p[3] = True
                continue
            if tag == '%pm-run':
                if t[2] == '%.y': continue
                if stack: stack[-1][2].append((runclass(t), t[8]))
                continue
            if tag == '%pq-s':
                root, pas, nxt, gs, gok = t[1], int(t[2]), int(t[3].replace('.', ''), 0), int(t[4].replace('.', ''), 0), t[5]
                L = loops.get(root)
                if pas == 1 or L is None or L['pass'] != pas - 1:
                    L = {'pass': pas, 'next': nxt, 'g': gs, 'quiet': 0, 'prev': None, 'starts': []}
                    loops[root] = L
                    inc('loops')
                else:
                    if gok != '%.y':
                        bad.append((case, root, pas, 'A: an identity left g')); inc('bad A g')
                    if nxt < L['next'] or gs < L['g']:
                        bad.append((case, root, pas, 'A: next or g fell')); inc('bad A next')
                L['pass'] = pas; L['next'] = nxt; L['g'] = gs
                stack.append([root, pas, [], False])
                continue
            if tag == '%pq-cal':
                inc('runs with no change and another callee set')
                if stack and stack[-1][0] in loops: inc('  of them inside a pass')
                continue
            if tag == '%pq-m':
                root, pas = t[1], int(t[2])
                ms = {m: (d == '%.y', s == '%.y', cm) for m, d, s, cm in MEM.findall(l)}
                L = loops[root]
                prev = L.get('prev')
                if prev is not None and prev['quiet'] and prev['pass'] == pas - 1:
                    # C: the previous pass was quiet and went on
                    p0 = prev['ms']
                    d0 = {m for m, v in p0.items() if v[0]}
                    r0 = {m for m, v in p0.items() if v[1]}
                    d1 = {m for m, v in ms.items() if v[0]}
                    if set(ms) != set(p0):
                        inc('C: members differ after a quiet pass')
                        bad.append((case, root, pas - 1, 'C: members differ'))
                    if any(p0[m][2] != ms[m][2] for m in p0 if m in ms):
                        inc('C: quiet passes where a callee set changed')
                        if verbose: print('callees changed in quiet pass', case, root, pas - 1)
                    if not d1 <= (d0 - r0):
                        inc('bad C: dirty not within dirty minus reached')
                        bad.append((case, root, pas - 1, 'C: dirty(end) not in dirty(start) - reached(start)', sorted(d1 - (d0 - r0))))
                    if not len(d1) < len(d0):
                        inc('bad C/D: dirty count did not fall')
                        bad.append((case, root, pas - 1, 'D: dirty count %d -> %d' % (len(d0), len(d1))))
                    rd = len(d0 & r0)
                    inc('C: quiet passes checked'); inc('C: reached dirty at a quiet start = %d' % rd)
                    if d1:
                        inc('C: quiet passes leaving unreached dirty members')
                L['prev'] = {'pass': pas, 'ms': ms, 'quiet': False}
                continue
            if tag == '%pm-end':
                root, pas, ch, found = t[1], int(t[2]), t[3], t[4]
                while stack and stack[-1][0] != root:
                    stack.pop(); inc('passes that return (low < index)')
                if not stack: inc('unmatched %pm-end'); continue
                p = stack.pop()
                L = loops[root]
                L['ended'] = (pas, ch, found, p[2], p[3])
                inc('passes')
                continue
            if tag == '%pm-pass':
                # a pass start: settle the previous pass of the same loop, now known to go on
                root, pas = t[1], int(t[2])
                L = loops.get(root)
                if L and pas > 1 and L.get('ended') and L['ended'][0] == pas - 1:
                    epas, ch, found, runs, pushed = L['ended']
                    inc('passes that go on')
                    if found == '%.y':
                        inc('  go on: push'); L['quiet'] = 0
                    elif ch == '%.y':
                        rise = [k for k, _ in runs if k is None]
                        strict = [k for k, _ in runs if k not in (None, 'none')]
                        if rise or not strict:
                            bad.append((case, root, epas, 'B: change without a fall', runs)); inc('bad B')
                        inc('  go on: change'); L['quiet'] = 0
                    else:
                        inc('  go on: QUIET')
                        if any(k != 'none' for k, _ in runs):
                            bad.append((case, root, epas, 'C: quiet pass with a run that moved', runs)); inc('bad C run')
                        L['quiet'] += 1
                        if L['prev'] is not None and L['prev']['pass'] == epas:
                            L['prev']['quiet'] = True
                        if L['quiet'] > maxq[0]: maxq = (L['quiet'], case, root, epas)
                        if L['quiet'] >= 2: inc('C: 2+ quiet passes in a row')
                    L['ended'] = None
                if pas == 1 and L and L.get('ended'):
                    pass
                if pas > maxroot.get(fam, (0,))[0]: maxroot[fam] = (pas, case)
                continue
        for root, L in loops.items():
            pass
    for k in sorted(c): print(k, c[k])
    print('longest run of quiet passes:', maxq)
    print('largest pass number per file:')
    for f in sorted(maxroot): print('  ', f, maxroot[f])
    print('violations:', len(bad))
    for x in bad[:40]: print('  ', x)

if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == '--instrument':
        instrument(a[1], a[2])
    else:
        v = a[0] == '-v'
        check(a[1:] if v else a, v)
