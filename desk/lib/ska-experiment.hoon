/-  *noir
|%
+$  bell  [bus=sock fol=^]
+$  identity  [more=sock fol=^]
+$  spring  *  ::  no union stuff
+$  callgraph  (map identity [less-code=sock less-memo=sock prod=sock map=spring callees=(set identity)])
+$  sock-anno  [=sock src=spring]
++  git-g
  |=  [i=identity g=callgraph]
  ^+  q.,.-.g
  (~(gut by g) i [|+~ |+~ |+~ ~ ~])
::
++  cons-source
  |=  [a=source b=source]
  ^-  source
  [[i.a i.b] t.a]
::
++  dunno
  ^-  sock-anno
  [|+~ ~]
::
++  distribute
  |=  [c=cape s=spring]
  ^-  cape
  ~+
  ?~  s  |
  ?:  ?=(%| c)  |
  ?@  s  (~(pat ca c) s)
  =/  [p=cape q=cape]  ?@(c [& &] c)
  =/  l  $(s -.s, c p)
  =/  r  $(s +.s, c q)
  (~(uni ca l) r)
::
++  update-code-usage
  |=  [g=callgraph =cape src=spring id=identity]
  ^-  callgraph
  ?:  =(~ src)  g
  =/  need=^cape  (distribute cape src)
  =/  data  (git-g id g)
  =.  less-code.data  (~(app ca (~(uni ca cape.less-code.data) need)) more.id)
  =.  less-memo.data  (~(app ca (~(uni ca cape.less-memo.data) need)) more.id)
  =.  g  (~(put by g) id data)
  g
::
++  add-callee
  |=  [g=callgraph from=identity to=identity]
  ^+  g
  =/  data  (git-g from g)
  =.  g  (~(put by g) from data(callees (~(put in callees.data) to)))
  g
::
--
::
|=  [bus=sock fol=^]
^-  callgraph
=|  g=callgraph
|-  ^-  callgraph
=*  fixpoint-callgraph  $
=;  g1=callgraph
  ?:  =(g1 g)  g
  ~&  %fixpoint
  $(g g1)
=|  worklist=(list identity)
|-  ^-  callgraph
~>  %loop
:: ~&  g
:: ~&  worklist
=*  worklist-loop  $
=;  cont
  ?~  worklist
    =^  w  g  (cont bus fol)
    ?~  w  g
    ~&  %work
    worklist-loop(worklist w)
  =;  [g1=callgraph w=(list identity)]  ~&  %work2  worklist-loop(worklist w, g g1)
  %+  roll  `(list identity)`worklist
  |=  [i=identity acc=[g=_g w=(list identity)]]
  ^+  acc
  =.  g  g.acc
  =^  w1  g  (cont i)
  [g (weld w1 w.acc)]
::
|=  id=identity
^-  [(list identity) callgraph]
=/  bus=sock  more.id
=/  fol  fol.id
=/  dat  (git-g id g)
=/  gen=[w=(list identity) g=callgraph]  [~ g]
=/  sub=sock-anno  [bus 1]
=;  [pro=sock-anno gen1=_gen]
  =.  gen  gen1
  =/  dat  (git-g id g.gen)
  =.  prod.dat  sock.pro
  =.  map.dat   src.pro
  :: ~&  [id=id res=sock.pro]
  =.  g.gen  (~(put by g.gen) id dat)
  gen
::
|-  ^-  [sock-anno gen=_gen]
=*  fol-loop  $
?+    fol  ~|  fol  !!::  [dunno gen]
    [p=^ q=^]
  =^  l=sock-anno  gen  fol-loop(fol p.fol)
  =^  r=sock-anno  gen  fol-loop(fol q.fol)
  :_  gen
  :-  (~(knit so sock.l) sock.r)
  (cons-spring:source src.l src.r)
::
    [%0 p=@]
  :_  gen
  ?:  =(0 p.fol)  dunno
  ?:  =(1 p.fol)  sub
  :-  (~(pull so sock.sub) p.fol)
  ((slot-spring:source p.fol) src.sub)
::
    [%1 p=*]
  :_  gen
  [&+p.fol ~]
::
    [%2 p=^ q=^]
  =^  s=sock-anno  gen  fol-loop(fol p.fol)
  =^  f=sock-anno  gen  fol-loop(fol q.fol)
  ?.  |(=(& cape.sock.f) ?=(^ data.sock.f))
    ::  indirect call
    ::
    ~&  f
    ~&  [sub fol]
    ~&  %indi1
    [dunno gen]
  =/  fol-new  ?@(data.sock.f !! data.sock.f)
  =?  gen  !(~(has in callees.dat) `identity`[sock.s fol-new])
    =.  w.gen  [[sock.s fol-new] w.gen]
    ~&  >>>  callee+[sock.s fol-new]
    =.  g.gen  (add-callee g.gen id [sock.s fol-new])
    gen
  ::
  =.  g.gen  (update-code-usage g.gen & src.f id)
  =/  dat-there  (git-g id g)
  =.  g.gen  (update-code-usage g.gen cape.less-code.dat-there src.s id)
  :_  gen
  :-  prod.dat-there
  (compose-spring:source map.dat src.s)
::
    [%3 p=^]
  =.  gen  +:fol-loop(fol p.fol)
  [dunno gen]
::
    [%4 p=^]
  =.  gen  +:fol-loop(fol p.fol)
  [dunno gen]
::
    [%5 p=^ q=^]
  =.  gen  +:fol-loop(fol p.fol)
  =.  gen  +:fol-loop(fol q.fol)
  [dunno gen]
::  pessimization: calls with the subject that comes from a fork are indirect
::
    [%6 p=^ q=^ r=^]
  =.  gen  +:fol-loop(fol p.fol)
  =.  gen  +:fol-loop(fol q.fol)
  =.  gen  +:fol-loop(fol r.fol)
  [dunno gen]
::
    [%7 p=^ q=^]
  =^  p=sock-anno  gen  fol-loop(fol p.fol)
  fol-loop(fol q.fol, sub p)
::
    [%8 p=^ q=^]
  fol-loop(fol [%7 [p.fol 0+1] q.fol])
::
    [%9 p=@ q=^]
  fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
::
    [%10 [a=@ don=^] rec=^]
  ?:  =(0 a.fol)  [dunno gen]
  =^  don=sock-anno  gen  fol-loop(fol don.fol)
  =^  rec=sock-anno  gen  fol-loop(fol rec.fol)
  :_  gen
  :-  (~(darn so sock.rec) a.fol sock.don)
  ((edit-spring:source a.fol) src.rec src.don)
::
    [%11 p=@ q=^]
  fol-loop(fol q.fol)
::
    [%11 [a=@ h=^] f=^]
  =.  gen  +:fol-loop(fol h.fol)
  fol-loop(fol f.fol)
==



