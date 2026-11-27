#!/usr/bin/env python3
# usage: leaptwice.py OUTDIR      then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 1500 > out.txt
#   tools/hoon/leaptwice.py --sum out.txt
# The fuel 3 of the model `sixNextLC` (lemmas/Ska/CompRunLC.lean) on the real compiler.  The model
# runs the case %6 of +run at most three times (+leap, then +kerf, then phase S or F); the Hoon has
# no bound.  They agree when +leap of the rest that +leap returned is ~.  The instrumented copy of
# the library prints, in the case %6 of +run:
#   [%lp2 %ok fb=? n=@]     +leap returned a rest; +leap of that rest is ~ (fb: the rest still has
#                           a fork or a bond, so the second +leap ran its loop; n: parts that leapt)
#   [%lp2-bad n=@ m=@]      +leap of the rest is not ~ (a witness against the fuel 3)
#   [%lp1 fb=?]             a %next goal with forks or bonds, +leap gave ~ (no part leapt)
#   %kerf, %six-f, [%six-s nxt=?]   the other phases
# On 2026-11-27 (726 formulas): %lp2 %ok 708 times (174 with fb), %lp2-bad never, %kerf 242, %six-f 1208 (one copy of the output).
import os, re, sys, random
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))

if sys.argv[1] == '--sum':
    ls = [l.strip() for l in open(sys.argv[2]).read().split('\n')
          if l.startswith('[%') or l in ('%kerf', '%six-f')]
    h = len(ls) // 2
    if ls[:h] == ls[h:]:
        ls = ls[:h]  # the harness evaluates the expression twice: count one copy
    c = {}
    for l in ls:
        k = re.match(r'\[?(%[\w-]+)( %ok fb=(%\.[yn]))?', l)
        key = k.group(1) + (' fb=' + k.group(3) if k.group(3) else '')
        if k.group(1) == '%lp1':
            key += ' ' + l.split()[1]
        c[key] = c.get(key, 0) + 1
    for k in sorted(c):
        print(k, c[k])
    for l in ls:
        if l.startswith('[%lp2-bad') or l.startswith('[%done'):
            print(l)
    sys.exit(0)

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
src = open(os.path.join(W, 'desk/lib/nock-compilation.hoon')).read().split('\n')

def ins(anchor, lines, before=True):
    k = [i for i, l in enumerate(src) if l == anchor]
    assert len(k) == 1, anchor
    i = k[0] if before else k[0] + 1
    src[i:i] = lines

k = src.index('        =^  nex  gen  $(goal gol.u.lep)')
assert src[k - 1] == '      ?^  lep'
src[k - 1:k - 1] = ([
    '      ~?  &(?=(~ lep) ?=(%next -.goal))',
    '        [%lp1 fb=!&(?=(~ fork.laz.goal) ?=(~ bond.laz.goal))]'])
ins('        =^  nex  gen  $(goal gol.u.lep)', [
    '        =/  lp2  (leap laz.gol.u.lep q.nomm r.nomm)',
    '        ~&  ?~  lp2',
    '              [%lp2 %ok fb=!&(?=(~ fork.laz.gol.u.lep) ?=(~ bond.laz.gol.u.lep)) n=(lent bys.u.lep)]',
    '            [%lp2-bad n=(lent bys.u.lep) m=(lent bys.u.lp2)]'])
ins('          =^  [out=@uwoo pro=@uvre]  gen  (kerf goal)', ['          ~&  [%kerf]'])
ins('        =^  r-cond  gen  re', ['        ~&  [%six-f]'])
ins('      =^  [goal-0=^goal goal-1=^goal]  gen', ['      ~&  [%six-s nxt=?=(%next -.goal)]'])
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(src))

def hn(n):
    return f'{n:,}'.replace(',', '.')

def cases(name, base):
    t = open(os.path.join(D, name)).read().split('\n')
    n = next(k for k, l in enumerate(t) if l == '  ==')
    res = []
    for l in t[2:n]:
        m = re.match(r'^      \[(\d+) %\w+ (.*)$', l)
        assert m, l
        res.append(f'      [{hn(base + int(m.group(1)))} {m.group(2)}')
    return res

# a %6 under a %next goal with forks: the %6 in the first part of a %7 whose second part forks,
# with branches that pass parts of the subject (+pass-both)
QR = [('[0 3]', '[0 3]'), ('[[0 6] [0 7]]', '[[0 6] [1 0]]'), ('[[0 6] [0 7]]', '[0 3]'),
      ('[[0 6] [0 7]]', '[[0 6] [0 7]]'), ('[0 1]', '[[0 2] [0 3]]'),
      ('[[0 7] [0 6]]', '[[0 7] [4 [0 6]]]'), ('[0 0]', '[0 3]'), ('[7 [0 3] [0 2]]', '[0 6]'),
      ('[10 [2 [0 6]] [0 1]]', '[0 1]'), ('[[0 6] [[0 14] [0 15]]]', '[[0 6] [0 7]]'),
      ('[6 [0 2] [0 3] [0 3]]', '[0 3]'), ('[[0 6] [2 [0 1] [0 7]]]', '[[0 6] [0 7]]'),
      ('[[0 3] [0 2]]', '[[0 3] [0 2]]'), ('[[0 14] [0 6]]', '[[0 14] [0 6]]')]
OUT = ['[6 [0 1] [0 1] [1 0]]', '[6 [0 6] [[0 3] [0 2]] [1 0]]', '[6 [0 6] [0 2] [0 7]]',
       '[6 [0 6] [4 [0 2]] [0 3]]', '[6 [0 6] [6 [0 2] [0 3] [0 7]] [0 3]]',
       '[7 [6 [0 6] [0 2] [0 3]] [6 [0 1] [0 1] [1 0]]]', '[6 [0 6] [2 [0 2] [0 3]] [0 3]]',
       '[6 [0 6] [[0 2] [0 2]] [[0 3] [0 2]]]', '[6 [0 2] [0 7] [[0 6] [0 7]]]',
       '[6 [0 6] [11 1.953.460.339 [0 2]] [0 3]]', '[11 [1.953.460.339 [1 0]] [6 [0 6] [0 2] [0 3]]]']
X = []
for q, r in QR:
    for o in OUT:
        X.append(f'[0 5] [7 [6 [0 2] {q} {r}] {o}]')
for q, r in QR[:7]:
    for o in OUT[:6]:
        X.append(f'[0 5] [7 [[6 [0 2] {q} {r}] [0 1]] {o}]')            # in the head of a cons
        X.append(f'[0 5] [7 [6 [0 2] [6 [0 3] {q} {r}] {r}] {o}]')      # nested %6
        X.append(f'[0 5] [7 [6 [0 2] {q} {r}] [7 [6 [0 2] {q} {r}] {o}]]')  # two in a row
        X.append(f'[0 5] [[7 [6 [0 2] {q} {r}] {o}] [0 1]]')            # under a cons
        X.append(f'[0 5] [7 [6 [0 2] {q} [6 [0 3] {r} {q}]] {o}]')     # nested in the no branch

# random formulas: %6 and %7 heavy, small axes
rnd = random.Random(20261127)
def rf(d):
    if d == 0:
        return rnd.choice(['[0 1]', '[0 2]', '[0 3]', '[0 6]', '[0 7]', '[1 0]', '[0 0]', '[0 14]'])
    k = rnd.choice([6, 6, 6, 7, 7, 'c', 'c', 4, 0, 2, 10, 11])
    if k == 6: return f'[6 {rf(d - 1)} {rf(d - 1)} {rf(d - 1)}]'
    if k == 7: return f'[7 {rf(d - 1)} {rf(d - 1)}]'
    if k == 'c': return f'[{rf(d - 1)} {rf(d - 1)}]'
    if k == 4: return f'[4 {rf(d - 1)}]'
    if k == 2: return f'[2 {rf(d - 1)} [1 [0 3]]]'
    if k == 10: return f'[10 [{rnd.choice([2, 3, 6])} {rf(d - 1)}] {rf(d - 1)}]'
    if k == 11: return f'[11 1.953.460.339 {rf(d - 1)}]'
    return rf(0)
for _ in range(200):
    X.append(f'[0 5] [7 {rf(3)} {rf(3)}]')

body = cases('thread-a.hoon', 0) + cases('thread-b.hoon', 1000) + cases('thread-c.hoon', 2000)
body += [f'      [{hn(3000 + k)} {c}]' for k, c in enumerate(X)]
drv = ['=/  cases=(list [nam=@ud sub=* fol=*])', '  :~'] + body + [
  '  ==', '=/  n=@ud  0', '|-  ^-  @', '?~  cases  ~&  [%done n]  0', '~&  [%case nam.i.cases]',
  '=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state',
  '  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))',
  '=^  scc=(set bell)  sccs.cache.state', '  (scc-of func calls.long-ska.state sccs.cache.state)',
  '=^  raw=straight  cache.state  (compiled-mono func scc)', '$(cases t.cases, n +(n))', '']
open(os.path.join(out, 'ck.hoon'), 'w').write('\n'.join(drv))
print(len(body), 'cases')
