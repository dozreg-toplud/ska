#!/usr/bin/env python3
"""Instrumented COPY of nock-compilation.hoon for the halting of +bake-graph
(track Q, README Gaps 31).  usage: bakehalt_lib.py OUT.hoon [--cap N] [--ties]

Each textual patch asserts its text occurs once.  The copy counts, per run of
+bake-graph: the evaluations (worklist steps), the bells with a bake, the
changes of each bell's bake (the largest), the changes that keep the nouns
(old and new mutually +huge:so: no loss), the changes back to less.c, the
largest queue, and prints at the end
  [%bh-end evals bells maxchg nol tolc grew maxq]
and, with --cap N, stops the worklist after N evaluations with
  [%bh-cap ...] (the bakes left as they are), so a non-ending worklist shows
as a cap.  Every 10.000 evaluations it prints [%bh-evals n].  With --ties it
prints every tie [%bh-tie evals fol less old new] (fol as its +mug) and every
loss back to less.c [%bh-loss-lc evals fol less old].

--fix normfloor  the candidate fix of Gaps 31.7 (the coordinator's, NOT in desk/):
  a bell that is not fixed (jetted, root) and not frozen gets the NORMAL floor
  (norm-sock less.c) where the code takes the raw less.c (no informer, or the
  sites contradict less.c).  The counters then count changes back to the floor.
--plain          only the fix, no instrumentation (for a pill: splitmax/lib/nf.hoon).
--count          prints after each poke of +ska-poke
  [%bh-count new-code baked raw dup] (new variants compiled, variants of the poke,
  variants whose less is not normal (norm-sock),
  new variants with the nouns of an older variant of the same code bell).
"""
import sys

src = '/home/kirill/work/ska-scratch/wt/ska-formalization/desk/lib/nock-compilation.hoon'
out = sys.argv[1]
cap = None
if '--cap' in sys.argv:
    cap = int(sys.argv[sys.argv.index('--cap') + 1])
ties = '--ties' in sys.argv
fix = sys.argv[sys.argv.index('--fix') + 1] if '--fix' in sys.argv else None
assert fix in (None, 'normfloor'), fix
plain = '--plain' in sys.argv
count = '--count' in sys.argv
t = open(src).read()


def rep(a, b):
    global t
    assert t.count(a) == 1, (t.count(a), a)
    t = t.replace(a, b)


if fix == 'normfloor':
    rep("""      ?~  ks  less.c
""", """      ?~  ks  (norm-sock less.c)
""")
    rep("""      ?.  (huge:so less.c both)  less.c
      both
""", """      ?.  (huge:so less.c both)  (norm-sock less.c)
      both
""")

if count:
    rep("""  =^  baked=(map bell [=nomm calls=(set bell) seek=cape])  vars.lon
    (bake-graph root-bell dat jetted vars.lon)
""", """  =/  old-vars  vars.lon
  =^  baked=(map bell [=nomm calls=(set bell) seek=cape])  vars.lon
    (bake-graph root-bell dat jetted vars.lon)
  ~&  :*  %bh-count
          new-code+(lent (skip ~(tap in ~(key by baked)) ~(has by code.lon)))
          baked+~(wyt by baked)
          raw+(lent (skim ~(tap in ~(key by baked)) |=(v=bell !=(less.v (norm-sock less.v)))))
          ^=  dup
          %-  ~(rep by vars.lon)
          |=  [[c=bell vs=(set bell)] n=@ud]
          =/  ol=(set bell)  (~(get ju old-vars) c)
          %-  ~(rep in vs)
          |=  [v=bell n=_n]
          ?:  (~(has in ol) v)  n
          ?.  %-  ~(any in ol)
              |=(w=bell &((huge:so less.w less.v) (huge:so less.v less.w)))
            n
          +(n)
      ==
""")

irep = rep if not plain else (lambda a, b: None)

irep("""          evals=@ud
          grew=@ud                   ::  bakes that would have grown
      ==
""", """          evals=@ud
          grew=@ud                   ::  bakes that would have grown
          chg=(map bell @ud)
          nol=@ud
          tolc=@ud
          maxq=@ud
      ==
""")

capline = ''
if cap is not None:
    cd = f"{cap:,}".replace(',', '.')
    capline = f"""  ?:  (gte evals.st {cd})
    ~&  [%bh-cap evals+evals.st bells+~(wyt by bak.st) maxchg+(roll ~(val by chg.st) max) nol+nol.st tolc+tolc.st q+(lent q)]
    $(q ~)
"""

irep("""  =*  work  $
  ?~  q
""", f"""  =*  work  $
  =.  maxq.st  (max maxq.st (lent q))
  ~?  &(!=(0 evals.st) =(0 (mod evals.st 10.000)))  [%bh-evals evals.st]
{capline}  ?~  q
    ~&  :*  %bh-end  evals+evals.st  bells+~(wyt by bak.st)
            maxchg+(roll ~(val by chg.st) max)  nol+nol.st  tolc+tolc.st
            grew+grew.st  maxq+maxq.st
        ==
""")

tieline = ''
if ties:
    tieline = """    ~?  ?&(?=(^ old) (huge:so bake u.old) (huge:so u.old bake))  [%bh-tie evals+evals.st fol+(mug fol.c) less+less.c old+old new+bake]
    ~?  &(?=(^ old) =(bake FLOOR) !(huge:so u.old bake))  [%bh-loss-lc evals+evals.st fol+(mug fol.c) less+less.c old+old]
"""

irep("""    ?:  =(`bake old)  [changed st]
    [[c changed] st(bak (~(put by bak.st) c bake))]
""", """    ?:  =(`bake old)  [changed st]
""" + tieline + """    =?  nol.st  ?&(?=(^ old) (huge:so bake u.old) (huge:so u.old bake))  +(nol.st)
    =?  tolc.st  &(?=(^ old) =(bake FLOOR))  +(tolc.st)
    =.  chg.st  (~(put by chg.st) c +((~(gut by chg.st) c 0)))
    [[c changed] st(bak (~(put by bak.st) c bake))]
""")


t = t.replace('FLOOR', '(norm-sock less.c)' if fix else 'less.c')
open(out, 'w').write(t)
print('wrote', out)
