::  BakeEnds (track Q, README Gaps 31): TIES of +bake-graph on the real
::  compiler, three for one bell in one poke.  Run against the copy of
::  tools/gen/bakehalt_lib.py OUT.hoon --cap 20000 --ties:
::    RUNHOON_LIB=OUT.hoon runhoon.sh bakehalt-tie.hoon 300
::  prints, in poke %p3, [%bh-tie ...] three times for c (fol mug
::  870.705.994), less.c = [[[& &] |] [[[1 0] 1 1] ~]] (not normal), and
::  [%bh-end evals 15 bells 10 maxchg 4 nol 3 tolc 4 grew 0 maxq 3].
::
::  c uses axes 4 and 5 of its subject as code, so its code requirement has
::  the cape [& &] where the normal form has &.  Poke %p1 bakes c at its
::  floor: variant v1 = [norm(less.c) fc].  In %p3:
::  1. x1 is evaluated with its sample known ([5 6]): its %6 joins the
::     literals [H 5] and [H 6] (capes &), +double-int knows nothing, the
::     site is not picked and informs c: c = norm(less.c).
::  2. a1 informs x1 with nothing (a loss): the branches are cells [H ~]
::     with cell capes, the join knows H, the site fits v1 (picked): c loses
::     its only informer and goes back to the raw less.c: TIE 1.
::  3. x2 (fb3 calls it with [5 7]) is first evaluated as x1 in 1: it
::     informs c: norm(less.c) again: TIE 2.
::  4. fb5 informs x2 with nothing, as in 2: raw less.c: TIE 3.
::  Each switch of c is paid by an event of a caller (a loss, a first
::  bake).  Every variant is a bell: after %p3, vars holds both
::  [norm(less.c) fc] and [less.c fc] (the same nouns, compiled twice).
=/  f=*  [1 0]
=/  g=*  [1 1]
=/  hh=*  [f g]
=/  fc=*  [[2 [0 1] [0 4]] [2 [0 1] [0 5]]]
=/  jj=*  [6 [3 [0 2]] [[1 hh] [0 6]] [[1 hh] [0 7]]]
=/  fx1=*  [2 jj [1 fc]]
=/  fx2=*  [7 [0 1] fx1]
=/  fa1=*  [2 [0 1] [1 fx1]]
=/  fb5=*  [2 [0 1] [1 fx2]]
=/  fb4=*  [2 [0 1] [1 fb5]]
=/  fb3=*  [[2 [[0 2] [1 [5 7]]] [1 fx2]] [2 [0 1] [1 fb4]]]
=/  fb2=*  [2 [0 1] [1 fb3]]
=/  fb1=*  [2 [0 1] [1 fb2]]
=/  f1=*  [2 [[1 hh] [0 1]] [1 fc]]
=/  f3=*  [[2 [[0 2] [1 [5 6]]] [1 fx1]] [[2 [0 1] [1 fa1]] [2 [0 1] [1 fb1]]]]
=/  pokes=(list [nam=@tas sut=* fol=*])
  :~  [%p1 [| ~] f1]
      [%p3 [| ~] f3]
  ==
|-  ^-  @
?~  pokes  0
~&  [%bh-case nam.i.pokes]
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [;;(sock sut.i.pokes) ?>(?=(^ fol.i.pokes) fol.i.pokes)] long-ska.state ~(key by jets-hot.state))
$(pokes t.pokes)
