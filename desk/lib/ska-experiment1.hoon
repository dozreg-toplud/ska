/-  *noir
?>  =(|+~ *sock)
?>  =(| *cape)
|%
+$  bell  [bus=sock fol=^]
+$  identity  [more=sock fol=^]
+$  spring  *  ::  no union stuff
+$  datum
  $:  less-code=sock
      less-memo=sock
      prod=sock
      map=spring
      area=(unit spot)
      callees=(set [seat=(unit spot) =identity])
  ==
::
+$  callgraph  (map identity datum)
+$  sock-anno  [=sock src=spring]
++  git-g
  |=  [i=identity g=callgraph]
  ^-  datum
  (~(gut by g) i *datum)
::
++  dunno
  ^-  sock-anno
  [|+~ ~]
::
++  distribute
  |=  [c=cape s=spring]
  ^-  cape
  ?~  s  |
  ?:  ?=(%| c)  |
  ~+
  ?@  s  (~(pat ca c) s)
  =/  [p=cape q=cape]  ?@(c [& &] c)
  =/  l  $(s -.s, c p)
  =/  r  $(s +.s, c q)
  (~(uni ca l) r)
--
::
|=  [bus=sock fol=^]
^-  callgraph
=/  g=callgraph  (~(put by *callgraph) [bus fol] *datum)
::
|-  ^-  callgraph
=*  fixpoint-callgraph  $
=;  g1=callgraph
  ?:  =(g1 g)  ~&  %done  g
  ~&  %fixpoint
  $(g g1)
::
=*  g-previous  g
=/  funcs=(set identity)
  %-  ~(rep by g)
  |=  [[k=identity [* * * * * callees=(set [* identity])]] acc=(set identity)]
  =/  s=(set identity)  (~(run in callees) |=([* identity] +<+))
  (~(put in (~(uni in acc) s)) k)
::
%-  ~(rep in funcs)
|=  [id=identity g=callgraph]
^-  callgraph
=/  bus=sock  more.id
=;  [pro=sock-anno want=cape callees=(set [(unit spot) identity]) area=(unit spot)]
  =/  less-code  (~(app ca want) bus)
  =/  capture=cape  (prune-spring:source src.pro cape.sock.pro)
  =/  less-memo  (~(app ca (~(uni ca want) capture)) bus)
  (~(put by g) id less-code less-memo sock.pro src.pro area callees)
::
=/  fol  fol.id
=/  sub=sock-anno  [bus 1]
=/  gen  [want=`cape`| callees=`(set [(unit spot) identity])`~ area=`(unit spot)`~]
=/  seat=(unit spot)  ~
|-  ^-  [sock-anno _gen]
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
  ?.  &(=(& cape.sock.f) ?=(^ data.sock.f))
    ::  indirect call
    ::
    ~&  %indi
    [dunno gen]
  =/  fol-new  data.sock.f
  =/  id-there  [sock.s fol-new]
  =.  want.gen  (~(uni ca want.gen) (distribute & src.f))
  =/  dat-there  (git-g id-there g-previous)
  =.  want.gen  (~(uni ca want.gen) (distribute cape.less-code.dat-there src.s))
  =.  callees.gen  (~(put in callees.gen) seat id-there)
  :_  gen
  :-  prod.dat-there
  (compose-spring:source map.dat-there src.s)
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
  ?:  &(=(a.fol %spot) =(1 -.h.fol))
    ?~  pot=((soft spot) +.h.fol)  fol-loop(fol f.fol)
    =?  area.gen  ?=(~ area.gen)  pot
    =.  seat  pot
    fol-loop(fol f.fol)
  =.  gen  +:fol-loop(fol h.fol)
  fol-loop(fol f.fol)
==