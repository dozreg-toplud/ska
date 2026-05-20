::  the idea was to describe SKA as a computation of a fixpoint of a callgraph-
::  transformation function. I screwed up somewhere?
::
/-  *noir
|%
+$  bell  [bus=sock fol=^]
+$  identity  (list @ud)
+$  callgraph  (map identity [=bell more=sock prod=sock less-memo=sock map=spring])
+$  memo  (jar ^ [id=identity =bell prod=sock less-memo=sock map=spring])
+$  source  (lest spring)  ::  no union stuff
+$  spring  *
+$  sock-anno  [=sock src=source]
++  cons-source
  |=  [a=source b=source]
  ^-  source
  [[i.a i.b] t.a]
::
++  dunno
  |=  sub=sock-anno
  ^-  sock-anno
  [|+~ [~[~] t.src.sub]]
::
++  regenerate-memo
  |=  g=callgraph
  ^-  memo
  %-  ~(rep by g)
  |=  [[k=identity [=bell more=sock prod=sock less-memo=sock map=spring]] acc=memo]
  %+  ~(add ja acc)  fol.bell
  [k bell prod less-memo map]
::
++  distribute
  |=  [c=cape s=spring]
  ^-  (unit cape)
  ~+
  ?~  s  `|
  ?:  ?=(%| c)  `|
  ?@  s  `(~(pat ca c) s)
  ?@  c  ~  ::  detect consed-up formulas
  =/  l  $(s -.s, c -.c)
  ?~  l  ~
  =/  r  $(s +.s, c +.c)
  ?~  r  ~
  `(~(uni ca u.l) u.r)
::
++  update-code-usage
  |=  [g=callgraph id=identity =cape src=source fols=(list ^)]
  ^-  (unit callgraph)
  ?:  =(~ i.src)  `g
  =/  comps=(lest spring)
    =/  hed  i.src
    =/  tel  t.src
    |-  ^-  (lest spring)
    ?~  tel  ~[hed]
    =/  comp  (compose-spring:^source hed i.tel)
    [hed $(hed comp, tel t.tel)]
  ::
  |-  ^-  (unit callgraph)
  ?~  need=(distribute cape i.comps)  ~
  =/  need=^cape  u.need
  =/  data=[=bell more=sock prod=sock less-memo=sock map=spring]
    (~(gut by g) id [|+~ -.fols] |+~ |+~ |+~ ~)
  ::
  =.  bus.bell.data  (~(app ca (~(uni ca cape.bus.bell.data) need)) more.data)
  =.  less-memo.data  (~(app ca (~(uni ca cape.less-memo.data) need)) more.data)
  =.  g  (~(put by g) id data)
  ?~  id  `g
  ?~  t.comps  !!
  ?~  fols  !!
  $(id t.id, comps t.comps, fols t.fols)
::
--
::
|=  [bus=sock fol=^]
^-  callgraph
=/  g=callgraph  [[~ [|+~ fol] bus |+~ |+~ ~] ~ ~]
=/  m=memo  (regenerate-memo g)
|-  ^-  callgraph
=*  fixpoint-over-callgraph  $
=;  g1=callgraph
  ?:  =(g g1)  g
  ~&  %fixpoint
  fixpoint-over-callgraph(g g1)
::
=/  worklist=(list identity)  ~[~]
|-  ^-  callgraph
=*  worklist-loop  $
?~  worklist  g
=/  id=identity  i.worklist
=;  [prod=sock-anno g1=callgraph]
  =.  g  g1
  =/  data=[=bell more=sock prod=sock less-memo=sock map=spring]
    (~(gut by g) id [|+~ fol] |+~ |+~ |+~ ~)
  ::
  =.  prod.data  sock.prod
  =.  map.data  i.src.prod
  =.  g  (~(put by g) id data)
  worklist-loop(worklist t.worklist)
^-  [sock-anno g=callgraph]
=/  [bus=sock fol=^ mask=cape]  [more fol.bell cape.bus.bell]:(~(got by g) id)
=/  sub=sock-anno  [bus ~[1]]
=/  n-callees=@  0
=/  list-stack=(list ^)  ~[fol]
|-  ^-  [sock-anno callgraph]
=*  fol-loop  $
?+    fol  [(dunno sub) g]
    [p=^ q=^]
  =^  l=sock-anno  g  fol-loop(fol p.fol)
  =^  r=sock-anno  g  fol-loop(fol q.fol)
  :_  g
  :-  (~(knit so sock.l) sock.r)
  (cons-source src.l src.r)
::
    [%0 p=@]
  :_  g
  ?:  =(0 p.fol)  (dunno sub)
  ?:  =(1 p.fol)  sub
  :-  (~(pull so sock.sub) p.fol)
  [((slot-spring:^source p.fol) i.src.sub) t.src.sub]
::
    [%1 p=*]
  :_  g
  [&+p.fol [~ t.src.sub]]
::
    [%2 p=^ q=^]
  =^  s=sock-anno  g  fol-loop(fol p.fol)
  ~&  sub+sub
  ~&  q.fol
  =^  f=sock-anno  g  fol-loop(fol q.fol)
  ?.  |(=(& cape.sock.f) ?=(@ data.sock.f))
    ::  indirect call
    ::
    ~&  %indi1
    [(dunno sub) g]
  ::
  =/  fol-new  ?@  data.sock.f  ~|  data.sock.f  !!  data.sock.f
  =/  mayb-g  (update-code-usage g id & src.f list-stack)
  ?~  mayb-g
    :: indirect call
    ::
    ~&  %indi2
    ~&  [fol-new src.f]
    [(dunno sub) g]
  =.  g  u.mayb-g
  =/  meme  (~(get ja m) fol-new)
  |-  ^-  [sock-anno callgraph]
  =*  memo-loop  $
  ?^  meme
    ?.  (~(huge so less-memo.i.meme) sock.s)  $(meme t.meme)
    =/  mayb-g  (update-code-usage g id cape.bus.bell.i.meme src.sub list-stack)
    ?~  mayb-g
      :: indirect call
      ::
      ~&  %indi3
      [(dunno sub) g]
    =.  g  u.mayb-g
    =.  m  (regenerate-memo g)
    =?  worklist  !=(mask cape.bus.bell:(~(got by g) id))  [id worklist]
    :_  g
    :-  prod.i.meme
    src.sub(i (compose-spring:^source map.i.meme i.src.sub))
  ::
  =^  id-there=identity  n-callees  [[n-callees id] +(n-callees)]
  =^  res=sock-anno  g
    ~&  %enter
    %=  fol-loop
      n-callees   0
      fol         fol-new
      id          id-there
      sub         s(src [1 src.s])
      list-stack  [fol-new list-stack]
    ==
  ::
  ~&  %done
  =?  worklist  !=(mask cape.bus.bell:(~(got by g) id))  [id worklist]
  :_  g
  ?~  t.src.res  !!
  res(t.src t.t.src.res, i.src (compose-spring:^source i.src.res i.t.src.res))
::
    [%3 p=^]
  =.  g  +:fol-loop(fol p.fol)
  [(dunno sub) g]
::
    [%4 p=^]
  =.  g  +:fol-loop(fol p.fol)
  [(dunno sub) g]
::
    [%5 p=^ q=^]
  =.  g  +:fol-loop(fol p.fol)
  =.  g  +:fol-loop(fol q.fol)
  [(dunno sub) g]
::  pessimization: calls with the subject that comes from a fork are indirect
::
    [%6 p=^ q=^ r=^]
  =.  g  +:fol-loop(fol p.fol)
  =.  g  +:fol-loop(fol q.fol)
  =.  g  +:fol-loop(fol r.fol)
  [(dunno sub) g]
::
    [%7 p=^ q=^]
  =^  p=sock-anno  g  fol-loop(fol p.fol)
  fol-loop(fol q.fol, sub p)
::
    [%8 p=^ q=^]
  fol-loop(fol [%7 [p.fol 0+1] q.fol])
::
    [%9 p=@ q=^]
  fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
::
    [%10 [a=@ don=^] rec=^]
  ?:  =(0 a.fol)  [(dunno sub) g]
  =^  don=sock-anno  g  fol-loop(fol don.fol)
  =^  rec=sock-anno  g  fol-loop(fol rec.fol)
  :_  g
  :-  (~(darn so sock.rec) a.fol sock.don)
  [((edit-spring:^source a.fol) i.src.rec i.src.don) t.src.rec]
==