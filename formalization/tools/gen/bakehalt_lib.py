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
"""
import sys

src = '/home/kirill/work/ska-scratch/wt/ska-formalization/desk/lib/nock-compilation.hoon'
out = sys.argv[1]
cap = None
if '--cap' in sys.argv:
    cap = int(sys.argv[sys.argv.index('--cap') + 1])
ties = '--ties' in sys.argv
t = open(src).read()


def rep(a, b):
    global t
    assert t.count(a) == 1, (t.count(a), a)
    t = t.replace(a, b)


rep("""          evals=@ud
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

rep("""  =*  work  $
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
    ~?  &(?=(^ old) =(bake less.c) !(huge:so u.old bake))  [%bh-loss-lc evals+evals.st fol+(mug fol.c) less+less.c old+old]
"""

rep("""    ?:  =(`bake old)  [changed st]
    [[c changed] st(bak (~(put by bak.st) c bake))]
""", """    ?:  =(`bake old)  [changed st]
""" + tieline + """    =?  nol.st  ?&(?=(^ old) (huge:so bake u.old) (huge:so u.old bake))  +(nol.st)
    =?  tolc.st  &(?=(^ old) =(bake less.c))  +(tolc.st)
    =.  chg.st  (~(put by chg.st) c +((~(gut by chg.st) c 0)))
    [[c changed] st(bak (~(put by bak.st) c bake))]
""")

open(out, 'w').write(t)
print('wrote', out)
