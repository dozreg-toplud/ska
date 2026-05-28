/-  *noir
?>  =(|+~ *sock)
?>  =(| *cape)
|%
+$  identity  [more=sock fol=^]
+$  spring  *  ::  no union stuff
+$  datum
  $:  less-code=sock
      less-memo=sock
      indirect-code-request=cape
      prod=sock
      map=spring
      area=(unit spot)
      callees=(set [seat=(unit spot) =identity])
  ==
::
+$  callgraph  (map identity datum)
+$  jug-id  (jug identity identity)
+$  worklist  (set identity)
+$  memo  (map ^ (map sock [id=identity =datum]))  ::  fol -> less-memo -> entry
++  mi
  |%
  ++  gut
    |=  [m=memo f=^]
    ^-  (map sock [identity datum])
    (~(gut by m) f ~)
  ::
  ++  git
    ~%  %git-mi  ..zuse  ~
    |=  [m=memo f=^ s=sock]
    ^-  (unit [identity datum])
    =/  entries=(list [* id=identity d=datum])  ~(tap by (gut m f))
    |-  ^-  (unit [identity datum])
    ?~  entries  ~
    ?:  ?&  (~(huge so less-memo.d.i.entries) s)
        ::
            =/  c=cape  cape:(~(app ca indirect-code-request.d.i.entries) s)
            ?=(%| c)
        ==
      `[id d]:i.entries
    $(entries t.entries)
  ::
  ++  put
    ~%  %put-mi  ..zuse  ~
    |=  [m=memo id=identity d=datum]
    ^-  memo
    =/  inner  (gut m fol.id)
    =.  inner  (~(put by inner) less-memo.d [id d])
    (~(put by m) fol.id inner)
  --
::
+$  sock-anno  [=sock src=spring]
++  git-g
  |=  [g=callgraph i=identity]
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
:: ++  regenerate-callers
::   ~%  %regenerate-callers  ..zuse  ~
::   |=  g=callgraph
::   ^-  callers
::   :: ~>  %bout.[0 %regenerate-callers]
::   %-  ~(rep by g)
::   |=  [[from=identity [* * * * * * callees=(set [* identity])]] acc=callers]
::   =>  [from=from callees=callees acc=acc ..regenerate-callers]
::   %-  ~(rep in callees)
::   |=  [[* to=identity] acc=_acc]
::   (~(put ju acc) to from)
:: ::
:: ++  regenerate-memo
::   ~%  %regenerate-memo  ..zuse  ~
::   |=  g=callgraph
::   ^-  memo
::   :: ~>  %bout.[0 %regenerate-memo]
::   %-  ~(rep by g)
::   |=  [[id=identity d=datum] acc=memo]
::   (put:mi acc id d)
::
++  trace-g
  ~%  %trace-g  ..zuse  ~
  |=  [r=identity g=callgraph]
  ^-  callgraph
  =|  out=callgraph
  =/  queu=(list identity)  ~[r]
  |-  ^-  callgraph
  ?~  queu  out
  ?~  d=(~(get by g) i.queu)  $(queu t.queu)
  ?:  (~(has by out) i.queu)  $(queu t.queu)
  =.  out  (~(put by out) i.queu u.d)
  $(queu (weld t.queu ~(tap in `(set identity)`(~(run in callees.u.d) tail))))
::
++  trace-c
  ~%  %trace-c  ..zuse  ~
  |=  [r=identity c=jug-id]
  ^-  jug-id
  =|  out=jug-id
  =/  queu=(list identity)  ~[r]
  =|  back=(list identity)
  |-  ^-  jug-id
  ?~  queu
    ?~  back  out
    $(queu back, back ~)
  ?~  v=(~(get by c) i.queu)  $(queu t.queu)
  ?:  (~(has by out) i.queu)  $(queu t.queu)
  =.  out  (~(put by out) i.queu u.v)
  $(queu t.queu, back (weld back `(list identity)`~(tap in u.v)))
--
::
|=  [bus=sock fol=^]
^-  callgraph
=|  g=callgraph
=/  root  [bus fol]
=/  w=worklist  [root ~ ~]
=|  calls=jug-id
=|  called-by=jug-id
::
=<  $
~%  %analysis  ..zuse  ~
|.  ^-  callgraph
=*  fixpoint-callgraph  $
=;  [w-new=worklist w-call=worklist new-calls=jug-id g1=callgraph]
  =.  g  (~(uni by g) g1)
  :: =.  g  (trace-g root g)
  :: =.  new-calls  (trace-c root new-calls)
  =.  called-by
    =<  $
    ~%  %called-by-update  ..zuse  ~
    |.
    =/  all-callers=(list identity)  ~(tap in ~(key by new-calls))
    %+  roll  all-callers
    |=  [caller=identity acc=_called-by]
    =/  old-callees=(set identity)  (~(get ju calls) caller)
    =/  new-callees=(set identity)  (~(get ju new-calls) caller)
    =/  callee-removals=(set identity)  (~(dif in old-callees) new-callees)
    =/  callee-addition=(set identity)  (~(dif in new-callees) old-callees)
    =.  acc
      %-  ~(rep in callee-removals)
      |=  [callee=identity acc=_acc]
      (~(del ju acc) callee caller)
    ::
    %-  ~(rep in callee-addition)
    |=  [callee=identity acc=_acc]
    (~(put ju acc) callee caller)
  ::
  =.  calls  new-calls
  =/  w-new1=worklist
    %-  ~(rep in w-call)
    |=  [callee=identity acc=worklist]
    (~(uni in acc) `worklist`(~(get ja called-by) callee))
  ::
  =/  w-new=worklist  (~(uni in w-new) w-new1)
  ?:  =(w-new ~)
    ~&  %done  g
  ~&  [%fixpoint new+~(wyt in ^w-new) upd+~(wyt in w-new1) uniq+~(wyt in `(set ^)`(~(run in w-new) |=(identity fol)))]
  !.
  fixpoint-callgraph(w w-new)
::
:: ~>  %bout.[0 %iter]
:: =/  m=memo  (regenerate-memo g)
=*  g-previous  g
=<  -
%-  ~(rep in w)
|=  [id=identity [w-new=worklist w-call=worklist calls=_calls g=callgraph] m-new=memo]
^-  [[worklist worklist jug-id callgraph] memo]
=/  data  (git-g g-previous id)
=/  bus=sock  more.id
=;  [memo-hit=? data-new=datum m-new=memo]
  =.  g  (~(put by g) id data-new)
  =.  calls  (~(put by calls) id `(set identity)`(~(run in callees.data-new) tail))
  =?  w-new  !memo-hit
    %-  ~(rep in callees.data-new)
    |=  [[* id=identity] acc=_w-new]
    ?:  (~(has by g-previous) id)  acc
    (~(put in acc) id)
  ::
  =?  w-call  ?&  !memo-hit
                  |(!=([less-code prod map]:data-new [less-code prod map]:data))
              ==
    (~(put in w-call) id)
  ::
  [[w-new w-call calls g] m-new]
::
=/  fol  fol.id
=/  sub=sock-anno  [bus 1]
?^  hit=(git:mi m-new fol bus)  [& +.u.hit m-new]
=;  [pro=sock-anno want=cape indirect-code-request=cape callees=(set [(unit spot) identity]) area=(unit spot)]
  =/  less-code  (~(app ca want) bus)
  =/  capture=cape  (prune-spring:source src.pro cape.sock.pro)
  =/  less-memo  (~(app ca (~(uni ca want) capture)) bus)
  =/  data-new=datum  [less-code less-memo indirect-code-request sock.pro src.pro area callees]
  =.  m-new  (put:mi m-new id data-new)
  :: ~?  !?=(%| indirect-code-request.data-new)  [%m-new-skip area]
  [| data-new m-new]
::
=/  gen  :*  want=`cape`|
             indirect-code-request=`cape`|
             callees=`(set [(unit spot) identity])`~
             area=`(unit spot)`~
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
    =.  indirect-code-request.gen
      (~(uni ca indirect-code-request.gen) (distribute & src.f))
    ::
    [dunno gen]
  =/  fol-new  data.sock.f
  =/  id-there  [sock.s fol-new]
  =<  $
  ~%  %distribute  nock-2  ~
  |.
  =.  want.gen  (~(uni ca want.gen) (distribute & src.f))
  =/  id-there=identity  [sock.s fol-new]
  =/  dat-there=datum  (git-g g-previous id-there)
  =.  want.gen  (~(uni ca want.gen) (distribute cape.less-code.dat-there src.s))
  =/  indi  (distribute indirect-code-request.dat-there src.s)
  =.  indirect-code-request.gen  (~(uni ca indirect-code-request.gen) indi)
  ::
  :: =.  callees.gen  (~(put in callees.gen) seat id-there)
  =.  callees.gen  (~(put in callees.gen) ~ id-there)
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
    =/  pot=(unit spot)  `;;(spot +.h.fol)
    =?  area.gen  ?=(~ area.gen)  pot
    =.  seat  pot
    fol-loop(fol f.fol)
  =.  gen  +:fol-loop(fol h.fol)
  fol-loop(fol f.fol)
::
    [%12 p=^ q=^]
  =.  gen  +:fol-loop(fol p.fol)
  =.  gen  +:fol-loop(fol q.fol)
  [dunno gen]
==