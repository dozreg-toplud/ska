/-  *noir
?>  =(|+~ *sock)
?>  =(| *cape)
|%
+$  identity  [more=sock fol=^]
+$  spring  *  ::  no union stuff
+$  datum
  $:  less-code=sock
      less-memo=sock
      prod=sock
      map=spring
      area=(unit spot)
      direct=?
      callees=(set [seat=(unit spot) =identity])
  ==
::
+$  callgraph  (map identity datum)
+$  callers  (jug identity identity)
+$  worklist  (set identity)
+$  memo  (jar ^ [id=identity =datum])
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
::
++  regenerate-callers
  ~%  %regenerate-callers  ..zuse  ~
  |=  g=callgraph
  ^-  callers
  :: ~>  %bout.[0 %regenerate-callers]
  %-  ~(rep by g)
  |=  [[from=identity [* * * * * * callees=(set [* identity])]] acc=callers]
  =>  [from=from callees=callees acc=acc ..regenerate-callers]
  %-  ~(rep in callees)
  |=  [[* to=identity] acc=_acc]
  (~(put ju acc) to from)
::
++  regenerate-memo
  ~%  %regenerate-memo  ..zuse  ~
  |=  g=callgraph
  ^-  memo
  :: ~>  %bout.[0 %regenerate-memo]
  %-  ~(rep by g)
  |=  [[id=identity d=datum] acc=memo]
  ?.  direct.d  acc
  (~(add ja acc) fol.id id d)
--
::
|=  [bus=sock fol=^]
^-  callgraph
=|  g=callgraph
=/  w=worklist  [[bus fol] ~ ~]
::
=<  $
~%  %analysis  ..zuse  ~
|.  ^-  callgraph
=*  fixpoint-callgraph  $
=;  [w-new=worklist w-call=worklist g1=callgraph]
  =.  g  (~(uni by g) g1)
  =.  w-new
    =/  c  (regenerate-callers g)
    %-  ~(rep in w-call)
    |=  [callee=identity acc=_w-new]
    (~(uni in acc) `worklist`(~(get ja c) callee))
  ::
  ?:  =(w-new ~)
    ~&  %done  g
  ~&  [%fixpoint ~(wyt in w-new)]
  $(w w-new)
::
:: ~>  %bout.[0 %iter]
=/  m=memo  (regenerate-memo g)
=*  g-previous  g
%-  ~(rep in w)
|=  [id=identity w-new=worklist w-call=worklist g=callgraph]
^-  [worklist worklist callgraph]
=/  data  (git-g id g-previous)
=/  bus=sock  more.id
=;  [pro=sock-anno want=cape callees=(set [(unit spot) identity]) area=(unit spot) direct=?]
  =/  less-code  (~(app ca want) bus)
  =/  capture=cape  (prune-spring:source src.pro cape.sock.pro)
  =/  less-memo  (~(app ca (~(uni ca want) capture)) bus)
  =/  data-new=datum  [less-code less-memo sock.pro src.pro area direct callees]
  =.  g  (~(put by g) id data-new)
  =.  w-new
    %-  ~(uni in w-new)
    ^-  worklist
    %-  ~(rep in callees)
    |=  [[* id=identity] acc=worklist]
    ?:  (~(has by g-previous) id)  acc
    (~(put in acc) id)
  ::
  =?  w-call  |(!=([less-code prod map]:data-new [less-code prod map]:data))
    (~(put in w-call) id)
  ::
  [w-new w-call g]
::
=/  fol  fol.id
=/  sub=sock-anno  [bus 1]
=/  gen  :*  want=`cape`|
             callees=`(set [(unit spot) identity])`~
             area=`(unit spot)`~
             direct=`?`&
         ==
::
=/  seat=(unit spot)  ~
=<  $
~%  %fol-loop  ..zuse  ~
|.  ^-  [sock-anno _gen]
=*  fol-loop  $
?+    fol  ~|  fol  !!    ::  [dunno gen]
    [p=^ q=^]
  =^  l=sock-anno  gen  fol-loop(fol p.fol)
  =^  r=sock-anno  gen  fol-loop(fol q.fol)
  =<  $
  ~%  %nock-cons  ..fol-loop  ~
  |.
  :_  gen
  :-  (~(knit so sock.l) sock.r)
  (cons-spring:source src.l src.r)
::
    [%0 p=@]
  =<  $
  ~%  %nock-0  ..fol-loop  ~
  |.
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
  =<  $
  ~%  %nock-2  ..fol-loop  ~
  |.
  =*  nock-2  .
  ?.  &(=(& cape.sock.f) ?=(^ data.sock.f))
    ::  indirect call
    ::
    :: ~&  %indi
    :: ~&  seat
    =?  direct.gen  &(?=(@ src.f) !=(~ src.f))  |
    [dunno gen]
  =/  fol-new  data.sock.f
  =/  id-there  [sock.s fol-new]
  =<  $
  ~%  %distribute  nock-2  ~
  |.
  =.  want.gen  (~(uni ca want.gen) (distribute & src.f))
  =/  [id-there=identity dat-there=datum]
    =/  id-exact  [sock.s fol-new]
    ?^  dat=(~(get by g-previous) id-exact)  [id-exact u.dat]
    =/  meme  (~(get ja m) fol-new)
    |-  ^-  [identity datum]
    =*  memo-loop  $
    ?~  meme  [id-exact *datum]
    ?.  (~(huge so less-memo.datum.i.meme) sock.s)  memo-loop(meme t.meme)
    :: ~&  [%memo seat area:(~(got by g-previous) id.i.meme)]
    i.meme
  ::
  =.  want.gen  (~(uni ca want.gen) (distribute cape.less-code.dat-there src.s))
  =.  callees.gen  (~(put in callees.gen) seat id-there)
  =.  direct.gen  &(direct.gen direct.dat-there)
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
  =<  $
  ~%  %nock-10  ..fol-loop  ~
  |.
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