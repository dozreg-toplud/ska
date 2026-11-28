::  optring.hoon (track O, README Gaps 34, 2026-11-28): does the real
::  +optimize commute with ring erasure?  (`OptRing` of lemmas/Glue/PokeOnR.lean)
::  er / ero: a straight (raw / optimized) with %caf %csf %jmf %jsf replaced
::  by %cal %csl %jmp %jsp.  rs m: a ring-free straight with rings put on its
::  call ops uniformly per callee (m=1 every callee, m=2 callees of even mug).
::  Part A (real pairs): the 8 roots of ringdump.hoon on cor, compiled in a
::  fresh state (no rings) and after %fast /mm (rings): every straight of the
::  root (mono, nary) and every nary.cache entry; raw pair equal up to rings,
::  optimized pair equal up to rings.  Part B: ringdump's part B (the cached
::  caller that keeps %jmp after %jets ~ against the fresh compile with %jmf).
::  Part C (generated pairs): every code.long-ska bell after the pokes of
::  annots3.hoon, mono and nary: (a) er(opt (rs 1 s0)) = er(opt s0),
::  (b) the same for rs 2, (c) er(opt s) = er(opt s0) with s0 = er s,
::  (d) equivariance opt (rs m s0) = rso m (opt s0) for m = 1, 2.
::  Part D: the mixed case: a %clq whose two targets end %jmp b and %jmf b.
::
=/  ep
  |=  p=pole
  ^-  pole
  ?+  -.p  p
    %caf  [%cal a.p v.p d.p]
    %csf  [%csl a.p s.p d.p]
  ==
=/  et
  |=  t=termin
  ^-  termin
  ?+  -.t  t
    %jmf  [%jmp a.t v.t]
    %jsf  [%jsp a.t s.t]
  ==
=/  eto
  |=  t=termin-out
  ^-  termin-out
  ?+  -.t  t
    %jmf  [%jmp a.t v.t]
    %jsf  [%jsp a.t s.t]
  ==
=/  er
  |=  s=straight
  ^-  straight
  s(blocks (~(run by blocks.s) |=(b=blob b(body (turn body.b ep), fin (et fin.b)))))
=/  ero
  |=  s=straight-out
  ^-  straight-out
  s(blocks (~(run by blocks.s) |=(b=blob-out b(body (turn body.b ep), fin (eto fin.b)))))
=/  rof
  |=  [m=@ a=bell]
  ^-  (unit ring)
  ?:  =(m 0)  ~
  ?:  =(m 1)  `[/x 2]
  ?:  =(0 (mod (mug a) 2))  `[/y 3]
  ~
=/  rp
  |=  [m=@ p=pole]
  ^-  pole
  ?+  -.p  p
    %cal  =/  n  (rof m a.p)  ?~(n p [%caf a.p v.p d.p u.n])
    %csl  =/  n  (rof m a.p)  ?~(n p [%csf a.p s.p d.p u.n])
  ==
=/  rt
  |=  [m=@ t=termin]
  ^-  termin
  ?+  -.t  t
    %jmp  =/  n  (rof m a.t)  ?~(n t [%jmf a.t v.t u.n])
    %jsp  =/  n  (rof m a.t)  ?~(n t [%jsf a.t s.t u.n])
  ==
=/  rto
  |=  [m=@ t=termin-out]
  ^-  termin-out
  ?+  -.t  t
    %jmp  =/  n  (rof m a.t)  ?~(n t [%jmf a.t v.t u.n])
    %jsp  =/  n  (rof m a.t)  ?~(n t [%jsf a.t s.t u.n])
  ==
=/  rs
  |=  [m=@ s=straight]
  ^-  straight
  s(blocks (~(run by blocks.s) |=(b=blob b(body (turn body.b |=(p=pole (rp m p))), fin (rt m fin.b)))))
=/  rso
  |=  [m=@ s=straight-out]
  ^-  straight-out
  s(blocks (~(run by blocks.s) |=(b=blob-out b(body (turn body.b |=(p=pole (rp m p))), fin (rto m fin.b)))))
=/  hc
  |=  s=straight
  ^-  ?
  %+  lien  ~(val by blocks.s)
  |=  b=blob
  ?|  ?=(?(%jmp %jmf %jsp %jsf) -.fin.b)
      (lien body.b |=(p=pole ?=(?(%cal %caf %csl %csf %cam %csm) -.p)))
  ==
=/  hr
  |=  s=straight
  ^-  ?
  %+  lien  ~(val by blocks.s)
  |=  b=blob
  ?|  ?=(?(%jmf %jsf) -.fin.b)
      (lien body.b |=(p=pole ?=(?(%caf %csf) -.p)))
  ==
=/  hn
  |=  s=straight
  ^-  ?
  %+  lien  ~(val by blocks.s)
  |=(b=blob (lien body.b |=(p=pole ?=(%nok -.p))))
=/  uni
  |=  s=straight
  ^-  ?
  =/  m=(jug bell (unit ring))
    %+  roll  ~(val by blocks.s)
    |=  [b=blob acc=(jug bell (unit ring))]
    =.  acc
      %+  roll  body.b
      |=  [p=pole acc=_acc]
      ?+  -.p  acc
        %cal  (~(put ju acc) a.p ~)
        %caf  (~(put ju acc) a.p `n.p)
        %csl  (~(put ju acc) a.p ~)
        %csf  (~(put ju acc) a.p `n.p)
      ==
    ?+  -.fin.b  acc
      %jmp  (~(put ju acc) a.fin.b ~)
      %jmf  (~(put ju acc) a.fin.b `n.fin.b)
      %jsp  (~(put ju acc) a.fin.b ~)
      %jsf  (~(put ju acc) a.fin.b `n.fin.b)
    ==
  (levy ~(val by m) |=(x=(set (unit ring)) =(1 ~(wyt in x))))
::  the generated-pair check of one raw straight: [a b c d1 d2] as loobeans
=/  check
  |=  s=straight
  ^-  [a=? b=? c=? d1=? d2=?]
  =/  s0  (er s)
  =/  o0  (optimize s0)
  =/  o1  (optimize (rs 1 s0))
  =/  o2  (optimize (rs 2 s0))
  =/  os  (optimize s)
  :*  =((ero o1) (ero o0))
      =((ero o2) (ero o0))
      =((ero os) (ero o0))
      =(o1 (rso 1 o0))
      =(o2 (rso 2 o0))
  ==
=/  ma=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  mb=*  [4 [9 4 [0 1]]]
=/  mc=*  [[9 4 [0 1]] [9 10 [0 1]]]
=/  cor=*  [[ma [mb mc]] [1 2 0]]
=/  na=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  nb=*  [5 [1 0] [9 4 [0 1]]]
=/  cor2=*  [[na nb] [1 0]]
=/  rcases=(list [nam=@tas fol=*])
  :~  [%rt [7 [0 1] [9 4 [0 1]]]]
      [%rn [7 [0 1] [4 [9 4 [0 1]]]]]
      [%rc [7 [0 1] [[9 4 [0 1]] [0 1]]]]
      [%rk [7 [0 1] [[0 1] [9 4 [0 1]]]]]
      [%rp [7 [0 1] [6 [9 4 [0 1]] [1 7] [1 8]]]]
      [%rb [7 [0 1] [6 [3 [0 3]] [9 4 [0 1]] [1 0]]]]
      [%rm [7 [0 1] [9 10 [0 1]]]]
      [%rx [7 [0 1] [9 11 [0 1]]]]
  ==
=/  st0  state
::  the straights of one root in the current state: [key straight] with key
::  [bell mono?]
=/  grab
  |=  [st=_state fol=* cor=*]
  ^-  (list [k=[bell ?] s=straight])
  =.  state  st
  =.  nary.cache.state  ~
  =.  mono.cache.state  ~
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [&+cor ?>(?=(^ fol) fol)] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  =^  nar=straight  cache.state  (compiled-nary func scc)
  :-  [[func &] raw]
  %+  turn  ~(tap by nary.cache.state)
  |=([b=bell s=straight] [[b |] s])
::  Part A
=/  xa=(list [k=[bell ?] s=straight])
  =|  out=(list [k=[bell ?] s=straight])
  =/  cs  rcases
  |-  ^+  out
  ?~  cs  out
  $(cs t.cs, out (weld (grab state fol.i.cs cor) out))
=^  p0  ..poke  (poke [%fast | ~[[/mm [& cor]]]])
=/  ya=(list [k=[bell ?] s=straight])
  =|  out=(list [k=[bell ?] s=straight])
  =/  cs  rcases
  |-  ^+  out
  ?~  cs  out
  $(cs t.cs, out (weld (grab state fol.i.cs cor) out))
=/  xm  (malt xa)
=/  done-a=[n=@ rings=@ uni=@ raw=@ opt=@ miss=@]
  =|  acc=[n=@ rings=@ uni=@ raw=@ opt=@ miss=@]
  =/  l  ya
  |-  ^+  acc
  ?~  l  acc
  =/  x  (~(get by xm) k.i.l)
  ?~  x  $(l t.l, miss.acc +(miss.acc))
  =/  sy  s.i.l
  =/  sx  u.x
  =/  r1  =((er sx) (er sy))
  =/  r2  =((ero (optimize sx)) (ero (optimize sy)))
  =?  rings.acc  (hr sy)  +(rings.acc)
  =?  uni.acc  &((uni sx) (uni sy))  +(uni.acc)
  =?  raw.acc  r1  +(raw.acc)
  =?  opt.acc  r2  +(opt.acc)
  ~?  !r2  [%a-fail k.i.l r1]
  =/  cy  (check sy)
  ~?  !&(a.cy b.cy c.cy d1.cy d2.cy)  [%a-gen-fail k.i.l cy]
  $(l t.l, n.acc +(n.acc))
~&  [%part-a done-a]
::  Part B
=.  state  st0
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [&+cor2 [7 [0 1] [9 4 [0 1]]]] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  b0=straight  cache.state  (compiled-mono func scc)
=^  p1  ..poke  (poke [%fast | ~[[/nn [& cor2]]]])
=^  p2  ..poke  (poke [%jets ~])
=^  b2=straight  cache.state  (compiled-mono func scc)
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=^  b3=straight  cache.state  (compiled-mono func scc)
~&  :*  %part-b  %cached-rings  (hr b2)  %fresh-rings  (hr b3)
        %raw-eq  =(b2 b3)  %raw-ring-eq  =((er b2) (er b3))
        %opt-ring-eq  =((ero (optimize b2)) (ero (optimize b3)))
        %uni  (uni b2)  (uni b3)
    ==
::  Part D: the mixed straight
=/  bb=bell  [[| ~] [0 1]]
=/  mk
  |=  ring2=?
  ^-  straight
  :+  *need-ordered  1
  %-  malt
  ^-  (list [@uwoo blob])
  :~  [`@uwoo`0 [~ ~ [%clq `@uvre`0 [~ `@uwoo`1] [~ `@uwoo`2]]]]
      [`@uwoo`1 [~ ~ [%jmp bb ~[`@uvre`0]]]]
      [`@uwoo`2 [~ ~ ?:(ring2 [%jmf bb ~[`@uvre`0] [/x 2]] [%jmp bb ~[`@uvre`0]])]]
  ==
=/  mix  (mk &)
=/  pla  (mk |)
=/  omix  (optimize mix)
=/  opla  (optimize pla)
~&  [%part-d %mixed-uni (uni mix) %plain-uni (uni pla) %raw-ring-eq =((er mix) (er pla))]
~&  [%part-d %opt-ring-eq =((ero omix) (ero opla))]
~&  [%part-d %omix ~(tap by blocks.omix)]
~&  [%part-d %opla ~(tap by blocks.opla)]
::  Part C: the corpus of annots3.hoon
=.  state  st0
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
::  every code bell, mono and nary, raw
=/  bells=(list bell)  ~(tap in ~(key by code.long-ska.state))
~&  [%part-c %bells (lent bells)]
=/  tot=[n=@ calls=@ nok=@ rings=@ uni=@ a=@ b=@ c=@ d1=@ d2=@]
  =|  acc=[n=@ calls=@ nok=@ rings=@ uni=@ a=@ b=@ c=@ d1=@ d2=@]
  |-  ^+  acc
  ?~  bells  acc
  =/  scc=(set bell)  -:(scc-of i.bells calls.long-ska.state sccs.cache.state)
  =/  sm=straight  -:(compiled-mono i.bells scc)
  =/  sn=straight  -:(compiled-nary i.bells scc)
  =/  two=(list [? straight])  ~[[& sm] [| sn]]
  =.  acc
    |-  ^+  acc
    ?~  two  acc
    =/  s=straight  +.i.two
    ?.  (hc s)  $(two t.two, n.acc +(n.acc))
    =/  r  (check s)
    ~?  !&(a.r b.r c.r d1.r d2.r)  [%c-fail i.bells -.i.two r]
    =.  calls.acc  +(calls.acc)
    =?  nok.acc  (hn s)  +(nok.acc)
    =?  rings.acc  (hr s)  +(rings.acc)
    =?  uni.acc  (uni s)  +(uni.acc)
    =?  a.acc  a.r  +(a.acc)
    =?  b.acc  b.r  +(b.acc)
    =?  c.acc  c.r  +(c.acc)
    =?  d1.acc  d1.r  +(d1.acc)
    =?  d2.acc  d2.r  +(d2.acc)
    $(two t.two, n.acc +(n.acc))
  $(bells t.bells)
~&  [%part-c tot]
0
