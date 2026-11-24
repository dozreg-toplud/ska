#!/usr/bin/env python3
# usage: tagkeep.py OUTDIR [a|b|c|x|all]
# The tag invariant of lemmas/Ska/CompTagX.lean and CompTagU.lean on the real compiler.  Writes into OUTDIR an
# instrumented copy of desk/lib/nock-compilation.hoon (lib.hoon) and a driver (ck.hoon) over the
# formulas of thread-a.hoon, thread-b.hoon, thread-c.hoon (162, numbered 0.., 1000.., 2000..), the
# two cases of proxy-dump.hoon and the nestings below (3000..), or only one group of them
# (a, b, c, x: the last is proxy-dump's and the nestings).  Run:
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 900 > out.txt
#   tools/hoon/tagkeep.py --sum out.txt
# Every run of +comp's `run` in %run mode, with region rb and goal gol, prints one line
#   [%tg pre nadd sfx nset nlaz]            when every check below holds, or
#   [%tg-bad a=? s=? n=? c=? ...]           with the failing entries otherwise.
# G(t): rb is a suffix of t, or t is the tag (in tags.gen at the start) of a lazy block of gol
# (its forks and bonds, recursively).  Checked: a, every key the run added to cond has a tag
# satisfying G; s, every entry of tags the run set or changed satisfies G; n, every lazy block of
# the returned next has a tag satisfying G at the end; c, every key of cond at the start keeps its
# tag.  pre: every tag of a lazy block of gol has rb as a suffix (then G is "rb is a suffix").
# nadd: keys added; sfx: those whose tag has rb as a suffix (nadd = sfx whenever pre holds, if
# the checks hold); nset: tag entries set; nlaz: lazy blocks of the next.
import os, re, sys
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))

if sys.argv[1] == '--sum':
    runs = bad = adds = sfx = pre_adds = nopre_out = px = 0
    ls = [l for l in open(sys.argv[2]).read().split('\n') if l.startswith('[%')]
    h = len(ls) // 2
    if ls[:h] == ls[h:]:
        ls = ls[:h]  # the harness evaluates the expression twice: count one copy
    cs = sum(1 for l in ls if l.startswith('[%case'))
    for l in ls:
        m = re.match(r'\[%tg (%\.[yn]) ([\d.]+) ([\d.]+) ([\d.]+) ([\d.]+)\]', l.strip())
        if m:
            runs += 1
            p = m.group(1) == '%.y'
            a, s = int(m.group(2).replace('.', '')), int(m.group(3).replace('.', ''))
            adds += a; sfx += s
            if a: px += 1
            if p: pre_adds += a
            if a > s: nopre_out += 1
        elif l.startswith('[%tg-bad'):
            bad += 1; runs += 1
    print(f'cases={cs} runs={runs} with-proxy={px} keys-added={adds} keys-with-rb-suffix={sfx} '
          f'keys-added-under-pre={pre_adds} runs-with-a-key-outside-rb={nopre_out} bad={bad}')
    sys.exit(0)

out = sys.argv[1]
grp = sys.argv[2] if len(sys.argv) > 2 else 'all'
os.makedirs(out, exist_ok=True)
HELPERS = r'''++  tg-suffix
  |=  [rb=(list @uxid) t=(list @uxid)]
  ^-  ?
  =/  n  (lent t)
  =/  m  (lent rb)
  ?:  (lth n m)  |
  =((slag (sub n m) t) rb)
::
++  tg-blocks
  |=  laz=need-lazy
  ^-  (list @uwoo)
  =/  out=(list @uwoo)  ~
  =.  out
    %+  roll  fork.laz
    |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] acc=_out]
    ^-  (list @uwoo)
    :(weld acc ~[o.y o.n] (tg-blocks laz.y) (tg-blocks laz.n))
  %+  roll  bond.laz
  |=  [[o=@uwoo laz=need-lazy] acc=_out]
  ^-  (list @uwoo)
  :(weld acc ~[o] (tg-blocks laz))
::
++  tg-run
  |=  [g0=line-short gol=goal rb=(list @uxid) nex=next g1=line-short]
  =/  gbl=(list @uwoo)  ?.(?=(%next -.gol) ~ (tg-blocks laz.gol))
  =/  gtags=(set (list @uxid))
    (silt (murn gbl |=(o=@uwoo (~(get by tags.g0) o))))
  =/  pre=?  (levy ~(tap in gtags) |=(t=(list @uxid) (tg-suffix rb t)))
  =/  ok  |=(t=(list @uxid) |((tg-suffix rb t) (~(has in gtags) t)))
  =/  added=(list [k=@uvre v=[def=@uvre tag=(list @uxid)]])
    (skip ~(tap by cond.g1) |=([k=@uvre *] (~(has by cond.g0) k)))
  =/  kept=(list [k=@uvre v=[def=@uvre tag=(list @uxid)]])
    (skim ~(tap by cond.g1) |=([k=@uvre *] (~(has by cond.g0) k)))
  =/  set=(list [o=@uwoo t=(list @uxid)])
    %+  skip  ~(tap by tags.g1)
    |=([o=@uwoo t=(list @uxid)] =((~(get by tags.g0) o) `t))
  =/  nbl=(list @uwoo)  (tg-blocks laz.nex)
  =/  ntag=(list [o=@uwoo t=(unit (list @uxid))])
    (turn nbl |=(o=@uwoo [o (~(get by tags.g1) o)]))
  =/  a-bad  (skip added |=([* v=[* tag=(list @uxid)]] (ok tag.v)))
  =/  s-bad  (skip set |=([* t=(list @uxid)] (ok t)))
  =/  n-bad  (skip ntag |=([* t=(unit (list @uxid))] ?~(t | (ok u.t))))
  =/  c-bad
    %+  skip  kept
    |=  [k=@uvre v=[* tag=(list @uxid)]]
    =(tag.v tag:(~(got by cond.g0) k))
  =/  sfx  (lent (skim added |=([* v=[* tag=(list @uxid)]] (tg-suffix rb tag.v))))
  ?:  &(=(~ a-bad) =(~ s-bad) =(~ n-bad) =(~ c-bad))
    [%tg pre (lent added) sfx (lent set) (lent nbl)]
  :*  %tg-bad  a=?=(~ a-bad)  s=?=(~ s-bad)  n=?=(~ n-bad)  c=?=(~ c-bad)
      rb=rb  gtags=gtags  a-bad=a-bad  s-bad=s-bad  n-bad=n-bad  c-bad=c-bad
  ==
::'''
WRAP = r'''    =/  gen0=_gen  gen
    =;  res=[next _gen]
      ?.  ?=(%run mode.+.res)  res
      ~&  (tg-run gen0 goal region -.res +.res)
      res'''
src = open(os.path.join(W, 'desk/lib/nock-compilation.hoon')).read().split('\n')
i = src.index('++  comp')
assert src[i + 11].strip().startswith('|=  [mono=? =nomm =goal region=(list @uxid)')
assert src[i + 12].strip().startswith('|^  ^-  [next _gen]')
lib = src[:i] + HELPERS.split('\n') + src[i:i + 13] + WRAP.split('\n') + src[i + 13:]
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(lib))

def hn(n):
    return f'{n:,}'.replace(',', '.')

def cases(name, base):
    t = open(os.path.join(D, name)).read().split('\n')
    n = next(k for k, l in enumerate(t) if l == '  ==')
    res = []
    for l in t[2:n]:
        m = re.match(r'^      \[(\d+) (.*)$', l)
        assert m, l
        res.append(f'      [{hn(base + int(m.group(1)))} {m.group(2)}')
    return res

# proxy-dump.hoon's two cases, the smallest formula of README Gaps 12.2 and nestings of it
SMALL = '[7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]]'
X = [
  '[1 0 0 5] [7 [6 [0 2] [1 0] [6 [0 6] [0 7] [0 1]]] [6 [0 2] [0 3] [0 1]]]',
  '[0 5] [7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]',
  f'[0 5] [7 [6 [0 2] {SMALL} [1 0]] [4 [0 1]]]',
  f'[0 5] [[{SMALL}] [0 1]]',
  f'[0 5] [6 [0 1] {SMALL} [1 0]]',
  # inside two %6
  f'[0 5] [7 [6 [0 2] [6 [0 3] {SMALL} [1 1]] [1 0]] [4 [0 1]]]',
  f'[0 5] [7 [6 [0 2] [1 1] [6 [0 3] [1 1] {SMALL}]] [4 [0 1]]]',
  # inside a cons inside a %6
  f'[0 5] [7 [6 [0 2] [{SMALL} [0 1]] [1 0]] [4 [0 1]]]',
  f'[0 5] [7 [6 [0 2] [[0 1] {SMALL}] [1 0]] [0 3]]',
  # a %6 whose test makes a proxy
  f'[0 5] [7 [6 [0 2] [6 {SMALL} [0 1] [1 0]] [1 0]] [4 [0 1]]]',
  f'[0 5] [7 [6 {SMALL} [0 2] [1 0]] [4 [0 1]]]',
  # proxies in both branches, and a proxy run in a branch of the outer fork-free %6 under %done
  f'[0 5] [7 [6 [0 2] {SMALL} {SMALL}] [4 [0 1]]]',
  f'[0 5] [6 [0 2] [7 [4 [0 3]] [6 [0 2] {SMALL} [1 0]]] [1 0]]',
  # a %6 under a goal with forks (the forking branch of the %6 case): proxies of the outer blocks
  '[0 5] [7 [6 [0 2] [7 [4 [0 3]] [0 1]] [1 0]] [6 [0 1] [0 1] [1 0]]]',
  f'[0 5] [7 [6 [0 2] [7 [4 [0 3]] [0 1]] {SMALL}] [6 [0 1] [0 1] [1 0]]]',
  '[0 5] [7 [6 [0 2] [4 [0 3]] [3 [0 2]]] [6 [0 1] [0 1] [5 [0 1] [1 6]]]]',
  f'[0 5] [7 [7 [6 [0 2] {SMALL} [1 0]] [4 [0 1]]] [6 [0 1] [0 1] [1 0]]]',
  f'[0 5] [10 [2 {SMALL}] [6 [0 2] {SMALL} [0 1]]]',
  f'[0 5] [5 {SMALL} [6 [0 2] {SMALL} [1 1]]]',
]
xs = [f'      [{hn(3000 + k)} %x {c}]' for k, c in enumerate(X)]
body = []
if grp in ('a', 'all'): body += cases('thread-a.hoon', 0)
if grp in ('b', 'all'): body += cases('thread-b.hoon', 1000)
if grp in ('c', 'all'): body += cases('thread-c.hoon', 2000)
if grp in ('x', 'all'): body += xs
drv = ['=/  cases=(list [nam=@ud kind=@tas sub=* fol=*])', '  :~'] + body + [
  '  ==', '|-  ^-  @', '?~  cases  0', '~&  [%case nam.i.cases]',
  '=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state',
  '  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))',
  '=^  scc=(set bell)  sccs.cache.state', '  (scc-of func calls.long-ska.state sccs.cache.state)',
  '=^  raw=straight  cache.state  (compiled-mono func scc)', '$(cases t.cases)', '']
open(os.path.join(out, 'ck.hoon'), 'w').write('\n'.join(drv))
