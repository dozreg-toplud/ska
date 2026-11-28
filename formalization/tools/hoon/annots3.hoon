::  InvBSR step 1, the executable check of DetK and KC (track Q, README
::  Gaps 27, lemmas/Ska/AnnotSDet.lean, lemmas/Ska/AnnotSCheck.lean) on the
::  ANALYSIS's nomms: the nomm of each datum of memo.long-ska after the
::  pokes of annots.hoon (28), annots2.hoon (4) and hinttab.hoon (16), in
::  one state.  Each nomm is walked from its code requirement less-code
::  (provenance 1) with the analysis's product rules (+fol-loop): %0
::  pull/slot, a cons the constant if both sides are safe and not void and
::  else knit/cons, %6 +double-int, %7 q on p's product, %10 darn/edit,
::  hints the body's, a direct call the memo's product (+git:mi, patched,
::  composed), a call with a void subject or formula void, the rest
::  [| ~].  Tested:
::  (a) at every direct call with no memo key, DetK of the formula part q
::      at the call's subject sock: [%0 a] needs axis a in every noun of
::      the sock (+node of annots.hoon, sockHas of AnnotS.lean); a cons
::      both; a hint its body; %6 each branch DetK or KC; the rest nothing;
::  (b) at every %6 on a subject that is not void, a branch whose product
::      is void satisfies KC (a call under every bake), and so does every
::      nomm whose product is void on a subject that is not void.
::  The walk runs twice: with the memo's products, and with every direct
::  call void (the first pass, where a callee in progress has the bunt
::  entry; only the KC tests are meant there).  Printed: the totals, every
::  failure, every direct call with no memo key whose q is not a literal
::  ([%nonlit q sock]), the void branches of the second walk.
::  2026-11-28: 63 datums, 47 direct calls with no memo key, DetK at all
::  47 (45 pass +safe-fol-fol, 32 not literals); 21 %6, no void branch,
::  no void product (a finished callee's void product is [| ~], +pop);
::  all calls void: 10 void branches, 95 void products, all KC.
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
=/  cases1=(list [nam=@tas k=? sub=* fol=*])
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
=/  cases2=(list [nam=@tas sub=* fol=* tst=(list *)])
  :~  [%j1 [[v 7] [8 9]] f1 ~[[[v 7] [8 9]] [[v 0] 0] [[v [1 2]] 5] [[v 7] 8 9]]]
      [%j2 [[v 7] [8 9]] f2 ~[[[v 7] [8 9]] [[v 0] 0] [[v [1 2]] 5]]]
      [%j3 [[v 7] [8 9]] f3 ~[[[v 7] [8 9]] [[v 3] [8 9]]]]
      [%j4 [[v 7] [8 9]] f4 ~[[[v 7] [8 9]] [[v 0] 0] [[v [1 2]] 5]]]
  ==
=/  hg1=*  =>  ~  !:  |=(a=* ?@(a 0 +($(a +.a))))
=/  hg2=*  =>  ~  !:  |=([a=* b=*] [b a])
=/  hg3=*  =>  ~  !:  |=(a=* ?@(a a $(a -.a)))
=/  hg4=*  =>  ~  !:  |=(a=* =/(b [a a] ?@(a b [+.a b])))
=/  hg5=*  =>  ~  !:  |=(a=* ?:(?=([* *] a) [$(a -.a) $(a +.a)] 7))
=/  hg6=*  =>  ~  !:  |=([a=* b=*] ?@(b a $(a [-.b a], b +.b)))
=/  hfw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  hfm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  hfid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 hfm2]
=/  hdec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  cases3=(list [sut=* fol=*])
  :~  [[[& [| &]] hg1] [9 2 0 1]]
      [[[& [| &]] hg2] [9 2 0 1]]
      [[[& [| &]] hg3] [9 2 0 1]]
      [[[& [| &]] hg4] [9 2 0 1]]
      [[[& [| &]] hg5] [9 2 0 1]]
      [[[& [| &]] hg6] [9 2 0 1]]
      [[& 0] [4 0 1]]
      [[& [0 [hfid [hfw hfm2]]]] [0 0]]
      [[& 5] [0 1]]
      [[& 7] hdec]
      [[& [0 [hfid [hfw hfm2]]]] hfid]
      [[& 9] [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [[& 3] [11 1.886.217.588 [1 0]]]
      [[& 4] [11 [1.886.217.588 1 1] 0 1]]
      [[& [0 [hfid [hfw hfm2]]]] [2 [0 1] 1 hfid]]
      [[& [0 [hfw hfm2]]] [2 [0 1] 0 2]]
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
::  KC: a call under every bake
::
=/  kc
  |=  n=nomm
  ^-  ?
  ?-  n
    [^ *]     |($(n -.n) $(n +.n))
    [%0 *]    |
    [%1 *]    |
    [%2 *]    &
    [%3 *]    $(n p.n)
    [%4 *]    $(n p.n)
    [%5 *]    |($(n p.n) $(n q.n))
    [%6 *]    |($(n p.n) &($(n q.n) $(n r.n)))
    [%7 *]    |($(n p.n) $(n q.n))
    [%10 *]   |($(n q.p.n) $(n q.n))
    [%11 *]   ?@(p.n $(n q.n) |($(n q.p.n) $(n q.n)))
    [%12 *]   |($(n p.n) $(n q.n))
    [%mean *]  |($(n p.n) $(n q.n))
  ==
::  DetK at the sock s
::
=/  detk
  |=  [n=nomm s=sock]
  ^-  ?
  ?-  n
    [^ *]     &($(n -.n) $(n +.n))
    [%0 *]    ?=(^ (node s p.n))
    [%1 *]    &
    [%2 *]    &
    [%3 *]    &
    [%4 *]    &
    [%5 *]    &
    [%6 *]    &(|($(n q.n) (kc q.n)) |($(n r.n) (kc r.n)))
    [%7 *]    &
    [%10 *]   &
    [%11 *]   $(n q.n)
    [%12 *]   &
    [%mean *]  $(n q.n)
  ==
=/  acc0
  *$:(dir=@ud det=@ud dbad=(list *) nlit=@ud sff=@ud six=@ud v6=@ud v6bad=(list *) vd=@ud vdbad=(list *))
::  the pokes
::
|-  ^-  @
?^  cases1
  ?:  k.i.cases1
    =^  p  ..poke  (poke [%full sub.i.cases1 fol.i.cases1])
    $(cases1 t.cases1)
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [[| ~] ?>(?=(^ fol.i.cases1) fol.i.cases1)] long-ska.state ~(key by jets-hot.state))
  $(cases1 t.cases1)
?^  cases2
  =^  p  ..poke  (poke [%full sub.i.cases2 fol.i.cases2])
  $(cases2 t.cases2)
?^  cases3
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [;;(sock sut.i.cases3) ?>(?=(^ fol.i.cases3) fol.i.cases3)] long-ska.state ~(key by jets-hot.state))
  $(cases3 t.cases3)
::  the walk, built after the pokes (its arms read memo.long-ska.state)
::
=/  w
  |_  vm=?
  ++  walk
    |=  [n=nomm sub=sock-anno a=_acc0]
    ^-  [[pro=sock-anno saf=?] _acc0]
    =^  r  a  (step n sub a)
    ?.  &(?=(^ sock.sub) ?=(%void sock.pro.r))  [r a]
    =.  vd.a  +(vd.a)
    ?:  (kc n)  [r a]
    [r a(vdbad [n vdbad.a])]
  ::
  ++  step
    |=  [n=nomm sub=sock-anno a=_acc0]
    ^-  [[pro=sock-anno saf=?] _acc0]
    =/  dunno=sock-anno  [|+~ ~]
    ?-    n
        [^ *]
      =^  l  a  (walk -.n sub a)
      =^  r  a  (walk +.n sub a)
      :_  a
      ?:  &(saf.l saf.r ?=(^ sock.pro.l) ?=(^ sock.pro.r))
        [[&+[data.sock.pro.l data.sock.pro.r] ~] &]
      [[(knit:so sock.pro.l sock.pro.r) (cons:pi src.pro.l src.pro.r)] |]
    ::
        [%0 *]
      ?:  =(0 p.n)  [[dunno |] a]
      ?:  =(1 p.n)  [[sub |] a]
      [[[(pull:so sock.sub p.n) (slot:pi src.sub p.n)] |] a]
    ::
        [%1 *]  [[[&+p.n ~] &] a]
        [%2 *]
      =^  s  a  (walk p.n sub a)
      =^  f  a  (walk q.n sub a)
      ?:  |(?=(%void sock.pro.s) ?=(%void sock.pro.f))  [[[%void ~] |] a]
      ?~  info.n  [[dunno |] a]
      =.  a
        ?^  k.u.info.n  a
        =.  dir.a  +(dir.a)
        =?  sff.a  (safe-fol-fol q.n)  +(sff.a)
        =?  nlit.a  !?=([%1 *] q.n)  +(nlit.a)
        ~?  &(!vm !?=([%1 *] q.n))  [%nonlit q=q.n s=sock.sub sff=(safe-fol-fol q.n)]
        ?:  (detk q.n sock.sub)  a(det +(det.a))
        a(dbad [[q.n sock.sub b.u.info.n] dbad.a])
      ?:  vm  [[[%void ~] |] a]
      =/  hit  (git:mi memo.long-ska.state fol.b.u.info.n sock.pro.s)
      ?~  hit  [[dunno |] a]
      [[[prod.+.u.hit (compose:pi map.+.u.hit src.pro.s)] |] a]
    ::
        [%3 *]  =^(p a (walk p.n sub a) [[dunno |] a])
        [%4 *]  =^(p a (walk p.n sub a) [[dunno |] a])
        [%5 *]
      =^  p  a  (walk p.n sub a)
      =^  q  a  (walk q.n sub a)
      [[dunno |] a]
    ::
        [%6 *]
      =^  p  a  (walk p.n sub a)
      =^  q  a  (walk q.n sub a)
      =^  r  a  (walk r.n sub a)
      =?  a  ?=(^ sock.sub)
        =.  six.a  +(six.a)
        =?  a  ?=(%void sock.pro.q)
          =.  v6.a  +(v6.a)
          ~?  vm  [%void-branch %yes q.n]
          ?:((kc q.n) a a(v6bad [q.n v6bad.a]))
        =?  a  ?=(%void sock.pro.r)
          =.  v6.a  +(v6.a)
          ~?  vm  [%void-branch %no r.n]
          ?:((kc r.n) a a(v6bad [r.n v6bad.a]))
        a
      [[(double-int pro.q pro.r) |] a]
    ::
        [%7 *]
      =^  p  a  (walk p.n sub a)
      =^  q  a  (walk q.n pro.p a)
      [[pro.q |] a]
    ::
        [%10 *]
      =^  d  a  (walk q.p.n sub a)
      =^  r  a  (walk q.n sub a)
      :_  a
      :_  |
      [(darn:so sock.pro.r p.p.n sock.pro.d) (edit:pi src.pro.r p.p.n src.pro.d)]
    ::
        [%11 *]
      ?@  p.n
        =^  q  a  (walk q.n sub a)
        [[pro.q |] a]
      =^  h  a  (walk q.p.n sub a)
      =^  q  a  (walk q.n sub a)
      [[pro.q &(|(=(%spot p.p.n) =(%mean p.p.n)) saf.h saf.q)] a]
    ::
        [%12 *]
      =^  p  a  (walk p.n sub a)
      =^  q  a  (walk q.n sub a)
      [[dunno |] a]
    ::
        [%mean *]
      =^  p  a  (walk p.n sub a)
      =^  q  a  (walk q.n sub a)
      [[pro.q &(saf.p saf.q)] a]
    ==
  --
::  the walk over every datum of the memo
::
=/  ents=(list [id=identity d=datum])
  (zing (turn ~(tap by memo.long-ska.state) |=([* m=(map sock [identity datum])] ~(val by m))))
=/  ne=@ud  (lent ents)
=/  run
  |=  vm=?
  =/  es  ents
  =/  a  acc0
  |-  ^-  _acc0
  ?~  es  a
  =/  r  (~(walk w vm) nomm.d.i.es [less-code.d.i.es 1] a)
  ~?  !=((lent dbad.a) (lent dbad.+.r))
    [%detk-fail-entry fol=fol.id.i.es more=more.id.i.es less=less-code.d.i.es nomm=nomm.d.i.es]
  $(es t.es, a +.r)
=/  a  (run |)
~&  [%entries ne %direct-nokey dir.a %detk det.a %fail (lent dbad.a) %sff sff.a %nonlit nlit.a]
~&  [%six six.a %void-branches v6.a %kc-fail (lent v6bad.a) %void-nodes vd.a %kc-fail (lent vdbad.a)]
~&  [%detk-failures dbad.a]
~&  [%kc6-failures v6bad.a]
~&  [%kcv-failures vdbad.a]
::  every direct call void (the first pass, where a callee in progress has
::  the bunt entry): only the KC tests are meant
::
=.  a  (run &)
~&  [%allvoid %six six.a %void-branches v6.a %kc-fail (lent v6bad.a) %void-nodes vd.a %kc-fail (lent vdbad.a)]
~&  [%allvoid-kc6-failures v6bad.a]
~&  [%allvoid-kcv-failures vdbad.a]
0
