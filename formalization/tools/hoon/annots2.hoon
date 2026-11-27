::  InvBSR step 1 (track Q, README Gaps 27): a droppable formula part that
::  is NOT a literal.  The analysis joins the two branches of a %6 by
::  +double-int with provenance; the bake's +know folds a read of a known
::  part to a literal with no provenance, so the same join in the bake can
::  lose a part the analysis knew.  A call whose subject is that join's
::  product then keeps an unfolded read [0 x] as its formula part, which
::  passes +safe-fol-fol: +inlined drops it.  Cases (real %full pokes):
::  %j1  J = [6 T [0 2] [[0 4] [0 5]]], T reads no code, formula part [0 2]
::  %j2  the same with the formula part [6 [5 [1 0] [1 0]] [0 2] [0 2]]:
::       fails +safe-fol-fol in the analysis, passes it after the bake
::  %j3  J's second branch a call that never returns (void to the analysis)
::  %j4  J's test folds in the bake (it reads the code), first branch kept
::  Printed: every droppable call whose formula part is not a literal, as
::  [bell q sock] (the sock of annots.hoon's walk), the totals, then for
::  each case +eval-top against +mink on subjects that fit the root's code
::  bell, and the inl.cache entry of the root.
::
=/  v=*    [2 [0 1] [1 [0 3]]]
=/  t1=*   [5 [0 3] [1 [8 9]]]
=/  j1=*   [6 t1 [0 2] [[0 4] [0 5]]]
=/  lp=*   [8 [1 [9 2 0 1]] [9 2 0 1]]
=/  j3=*   [6 t1 [0 2] lp]
=/  j4=*   [6 [5 [0 4] [1 v]] [0 2] [[0 4] [0 5]]]
=/  f1=*   [7 j1 [2 [0 1] [0 2]]]
=/  f2=*   [7 j1 [2 [0 1] [6 [5 [1 0] [1 0]] [0 2] [0 2]]]]
=/  f3=*   [7 j3 [2 [0 1] [0 2]]]
=/  f4=*   [7 j4 [2 [0 1] [0 2]]]
=/  cases=(list [nam=@tas sub=* fol=* tst=(list *)])
  :~  [%j1 [[v 7] [8 9]] f1 ~[[[v 7] [8 9]] [[v 0] 0] [[v [1 2]] 5] [[v 7] 8 9]]]
      [%j2 [[v 7] [8 9]] f2 ~[[[v 7] [8 9]] [[v 0] 0] [[v [1 2]] 5]]]
      [%j3 [[v 7] [8 9]] f3 ~[[[v 7] [8 9]] [[v 3] [8 9]]]]
      [%j4 [[v 7] [8 9]] f4 ~[[[v 7] [8 9]] [[v 0] 0] [[v [1 2]] 5]]]
  ==
=/  node
  |=  [s=sock a=@]
  ^-  (unit sock)
  ?@  s  `s
  ?:  =(0 a)  ~
  ?:  =(1 a)  `s
  =/  u  $(a (div a 2))
  ?~  u  ~
  ?@  u.u  `u.u
  =/  t=?  =(0 (mod a 2))
  =/  c  cape.u.u
  =/  d  data.u.u
  ?@  c
    ?:  c
      ?@  d  ~
      `[& ?:(t -.d +.d)]
    ~
  =/  dd=^  ?@(d [0 0] d)
  `[?:(t -.c +.c) ?:(t -.dd +.dd)]
::  q returns on every noun that fits s (q passes +safe-fol-fol)
::
=/  ok
  |=  [q=nomm s=sock]
  ^-  ?
  ?:  ?=(%void s)  &
  ?+  q  |
    [^ *]        &($(q -.q) $(q +.q))
    [%0 *]       ?=(^ (node s p.q))
    [%1 *]       &
    [%11 @ *]    $(q q.q)
    [%11 [@ *] *]  &((safe-nomm q.p.q) $(q q.q))
    [%mean *]    &((safe-nomm p.q) $(q q.q))
  ==
::  the product sock of a nomm on s, knowing no more than the code
::
=/  prod
  |=  [n=nomm s=sock]
  ^-  sock
  ?:  ?=(%void s)  s
  ?-    n
      [^ *]  (knit:so $(n -.n) $(n +.n))
      [%0 *]  ?:(=(0 p.n) |+~ (pull:so s p.n))
      [%1 *]  &+p.n
      [%2 *]
    ?~  info.n  |+~
    =/  k  $(n p.n)
    ?:  ?=(%void k)  k
    =/  hit  (git:mi memo.long-ska.state fol.b.u.info.n k)
    ?~  hit  |+~
    prod.+.u.hit
  ::
      [%3 *]  |+~
      [%4 *]  |+~
      [%5 *]  |+~
      [%6 *]
    =/  a  $(n q.n)
    =/  b  $(n r.n)
    ?:(=(a b) a |+~)
  ::
      [%7 *]  $(n q.n, s $(n p.n))
      [%10 *]  (darn:so $(n q.n) p.p.n $(n q.p.n))
      [%11 *]  $(n q.n)
      [%12 *]  |+~
      [%mean *]  $(n q.n)
  ==
::  the walk: [all direct calls, the ones +inlined may drop q of, those
::  with a q that is not a literal, failures]
::
=/  chk
  |=  [n=nomm s=sock acc=[all=@ sff=@ red=@ bad=(list *)]]
  ^+  acc
  ?-    n
      [^ *]  $(n +.n, acc $(n -.n))
      [%0 *]  acc
      [%1 *]  acc
      [%2 *]
    =.  acc  $(n p.n)
    =.  acc  $(n q.n)
    ?~  info.n  acc
    =.  all.acc  +(all.acc)
    ?.  &(?=(~ k.u.info.n) (safe-fol-fol q.n))  acc
    =.  sff.acc  +(sff.acc)
    =?  red.acc  !?=([%1 *] q.n)  +(red.acc)
    ~?  !?=([%1 *] q.n)  [%nonlit b=b.u.info.n q=q.n s=s]
    ?:  (ok q.n s)  acc
    acc(bad [[q.n s b.u.info.n] bad.acc])
  ::
      [%3 *]  $(n p.n)
      [%4 *]  $(n p.n)
      [%5 *]  $(n q.n, acc $(n p.n))
      [%6 *]  $(n r.n, acc $(n q.n, acc $(n p.n)))
      [%7 *]  $(n q.n, s (prod p.n s), acc $(n p.n))
      [%10 *]  $(n q.n, acc $(n q.p.n))
      [%11 *]
    =?  acc  ?=(^ p.n)  $(n q.p.n)
    $(n q.n)
  ::
      [%12 *]  $(n q.n, acc $(n p.n))
      [%mean *]  $(n q.n, acc $(n p.n))
  ==
=/  all  cases
|-  ^-  @
?^  cases
  =^  p  ..poke  (poke [%full sub.i.cases fol.i.cases])
  ~&  [%case nam.i.cases %full ?=(^ p)]
  $(cases t.cases)
=/  cod=(list [bell code-entry])  ~(tap by code.long-ska.state)
=/  tot=[all=@ sff=@ red=@ bad=(list *)]  [0 0 0 ~]
=/  nb=@  0
=.  tot
  |-
  ?~  cod  tot
  =/  [b=bell e=code-entry]  i.cod
  $(cod t.cod, tot (chk nomm.e less.b tot), nb +(nb))
~&  [%direct all.tot %dropq sff.tot %nonlit red.tot %bad (lent bad.tot)]
~&  [%failures bad.tot]
=/  cases  all
|-  ^-  @
?^  cases
  =/  ts  tst.i.cases
  |-  ^-  @
  ?^  ts
    =/  a=toon  (mook (mink [i.ts fol.i.cases] ~))
    =^  t=tone  ..^poke  (eval-top [i.ts fol.i.cases] ~)
    =^  b=toon  ..^poke  (eval-mook t)
    ~&  [%run nam.i.cases ?:(=(a b) [%same a] [%differ mock=a ska=b])]
    $(ts t.ts)
  ^$(cases t.cases)
=/  il  ~(tap by inl.cache.state)
|-
?~  il  0
~&  [%inl p.i.il q.i.il]
$(il t.il)
