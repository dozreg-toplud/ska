::  InvBS (track F, README Gaps 27, lemmas/Ska/AnnotS.lean): at every
::  direct call [%2 p q info] of the code table whose memo key is ~ and
::  whose formula part q passes +safe-fol-fol (the calls +inlined may drop
::  q of), q returns on every subject that fits the sock at that point.
::  The pokes are those of inldump.hoon (16 by hand with an unknown subject
::  [| ~], 4 real %full) and 8 more whose formula parts read the subject
::  (a read, a cons of reads, static and dynamic hints over a read, an arm
::  of a core a call returns, the witness of M19).  The sock at a point is
::  computed by a walk that knows no more than the code: pull/knit/darn of
::  +so, the memo's product (+git:mi, patched) for a direct call, equal
::  products of both branches of %6, nothing else.  The test of q on a sock
::  s (by the cases of +safe-fol-fol): [%0 a] needs axis a in every noun
::  that fits s (the path to it goes through cells the sock knows are
::  cells), %1 nothing, a cons both parts, a hint its body (the clue of a
::  dynamic one and p of %mean are +safe-nomm: no %0, they return).
::  Printed: the totals (bells, direct calls, calls +inlined may drop q of,
::  those whose q is not a literal, failures), every failure as
::  [q s bell], then the bell and nomm of the witness's root (M19).
::  2026-11-27: 38 bells, 33 direct, 31 tested, 0 not literal, 0 failures;
::  the witness's call is indirect (info ~).
::
=/  xk  |=(k=@ ^-(* ?:(=(0 k) [0 1] [4 $(k (dec k))])))
=/  g1=*   [2 [0 1] [1 [4 0 1]]]
=/  gb=*   [[2 [0 1] [1 [4 0 1]]] (xk 50)]
=/  k40=*  [[2 [0 1] [1 [4 0 1]]] (xk 40)]
=/  h=*    [[2 [0 1] [1 k40]] [0 1]]
=/  g2=*   [2 [0 1] [1 g1]]
=/  r=*    [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  g1c=*  [2 [0 3] [1 [4 0 1]]]
=/  g5=*   [5 [0 1] g1]
=/  g6=*   [8 [1 r] [9 2 [0 1]]]
=/  ma=*   [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*   [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  g7=*   [8 [1 [ma mb]] [9 4 [0 1]]]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  wit=*  [7 [6 [3 0 1] [1 0 0 1 0] [1 5]] [2 [0 1] [0 7]]]
=/  mk=*   [8 [1 g1] [1 k40] [0 1]]
=/  idc=*  [7 [[0 1] [2 [0 1] [1 [4 0 1]]]] [0 2]]
=/  cases=(list [nam=@tas k=? sub=* fol=*])
  :~  [%u1 | 0 [2 [0 1] [1 g1]]]
      [%u2 | 0 [2 [0 1] [1 gb]]]
      [%u3 | 0 [2 [0 1] [1 g2]]]
      [%u4 | 0 [2 [0 1] [1 h]]]
      [%u5 | 0 [8 [1 r] [9 2 [0 1]]]]
      [%u6 | 0 [8 [1 [ma mb]] [9 4 [0 1]]]]
      [%u7 | 0 [2 [0 1] [7 [0 1] [1 g1]]]]
      [%u8 | 0 [11 [1.869.440.365 [1 0]] [2 [0 1] [1 g1]]]]
      [%u9 | 0 [8 [1 g1c] [9 2 [0 1]]]]
      [%ua | 0 [6 [3 0 1] [2 [0 1] [1 g1]] [[2 [0 1] [1 g2]] [0 1]]]]
      [%ub | 0 [[2 [0 1] [1 g1]] [2 [0 1] [1 g1]]]]
      [%uc | 0 [2 [0 1] [11 1.953.460.339 [1 g1]]]]
      [%ud | 0 [2 [0 1] [1 g5]]]
      [%ue | 0 [2 [0 1] [1 g6]]]
      [%uf | 0 [2 [0 1] [1 g7]]]
      [%ug | 0 [4 [2 [0 1] [1 h]]]]
      [%k1 & 7 dec]
      [%k2 & [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%k3 & 5 [2 [0 1] [1 g1]]]
      [%k4 & [g1c 3] [9 2 [0 1]]]
      [%v1 | 0 [8 [1 k40] [2 [0 1] [0 2]]]]
      [%v2 | 0 [8 [1 [4 0 1]] [2 [0 1] [[0 2] [0 2]]]]]
      [%v3 | 0 [8 [1 k40] [2 [0 1] [11 1.953.460.339 [0 2]]]]]
      [%v4 | 0 [8 [1 k40] [2 [0 1] [11 [1.953.460.339 [1 0]] [0 2]]]]]
      [%v5 | 0 [7 [2 [0 1] [1 mk]] [2 [0 3] [0 2]]]]
      [%v6 | 0 [8 [1 [k40 g1]] [2 [0 1] [0 5]]]]
      [%v7 | 0 [8 [1 r] [7 [2 [0 1] [1 idc]] [9 2 [0 1]]]]]
      [%w1 | 0 wit]
  ==
::  the node at axis a, if every noun that fits s has one
::
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
=|  wid=(unit bell)
|-  ^-  @
?^  cases
  ?:  k.i.cases
    =^  p  ..poke  (poke [%full sub.i.cases fol.i.cases])
    ~&  [%case nam.i.cases %full ?=(^ p)]
    $(cases t.cases)
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  ~&  [%case nam.i.cases %unk]
  =?  wid  =(%w1 nam.i.cases)  `func
  $(cases t.cases)
=/  cod=(list [bell code-entry])  ~(tap by code.long-ska.state)
=/  tot=[all=@ sff=@ red=@ bad=(list *)]  [0 0 0 ~]
=/  nb=@  0
|-
?^  cod
  =/  [b=bell e=code-entry]  i.cod
  $(cod t.cod, tot (chk nomm.e less.b tot), nb +(nb))
~&  [%bells nb %direct all.tot %dropq sff.tot %nonlit red.tot %bad (lent bad.tot)]
~&  [%failures bad.tot]
?~  wid  ~&(%no-witness 0)
~&  [%witness-bell u.wid]
~&  [%witness-nomm nomm:(~(got by code.long-ska.state) u.wid)]
0
