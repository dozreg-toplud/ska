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
      callees=(set [seat=(unit spot) =identity src=spring])
  ==
::
+$  callgraph  (map identity datum)
+$  jug-id  (jug identity identity)
+$  worklist  (set identity)
+$  memo  (map ^ (map sock [id=identity =datum]))  ::  fol -> less-memo -> entry
::
++  recursive-match
  |=  [kid=identity par=identity g=callgraph]
  ^-  (unit datum)
  ?.  =(fol.kid fol.par)  ~
  =/  d=datum  (git-g g par)
  ?:  (~(huge so less-code.d) more.kid)  `d
  ~
::
++  recursive-call
  |=  [id-caller=identity id-kid=identity called-by=jug-id g=callgraph]
  ^-  (unit [id=identity d=datum])
  =|  visited=(set identity)
  =/  callers=(set identity)  [id-caller ~ ~]
  =<  -
  |-  ^-  [(unit [id=identity d=datum]) (set identity)]
  =*  visit-loop  $
  ?:  (~(has in visited) id-kid)  [~ visited]
  =.  visited  (~(put in visited) id-kid)
  ?~  callers  [~ visited]
  ?^  d=(recursive-match id-kid n.callers g)
    [`[n.callers u.d] visited]
  =^  has-l  visited  visit-loop(callers l.callers)
  ?^  has-l  [has-l visited]
  =^  has-r  visited  visit-loop(callers r.callers)
  ?^  has-r  [has-r visited]
  =/  new-callers  (~(get ju called-by) n.callers)
  visit-loop(callers new-callers)
::
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
++  inlineable
  |=  fol=^
  ^-  ?
  =*  l  .
  ?+    fol  |
    [p=^ q=^]  &((l p.fol) (l q.fol))
    [%0 @]  &
    [%1 *]  &
    [%2 *]  |
    [%9 *]  |
  ::
    [%3 p=^]           (l p.fol)
    [%4 p=^]           (l p.fol)
    [%5 p=^ q=^]       &((l p.fol) (l q.fol))
    [%6 p=^ q=^ r=^]   &((l p.fol) (l q.fol) (l r.fol))
    [%7 p=^ q=^]       &((l p.fol) (l q.fol))
    [%8 p=^ q=^]       &((l p.fol) (l q.fol))
    [%10 [@ p=^] q=^]  &((l p.fol) (l q.fol))
    [%11 @ p=^]        (l p.fol)
    [%11 [@ q=^] p=^]  &((l p.fol) (l q.fol))
    [%12 p=^ q=^]      &((l p.fol) (l q.fol))
  ==
::
--
::
|=  [bus=sock fol=^]
^-  (list callgraph)
=|  g=callgraph
=|  history=(list callgraph)
=/  root  [bus fol]
=/  w=worklist  [root ~ ~]
=|  calls=jug-id
=|  called-by=jug-id
::
=<  $
~%  %analysis  ..zuse  ~
|.  ^-  (list callgraph)
=*  fixpoint-callgraph  $
!.
::  one fixpoint iteration gives us new worklists to handle, updated part of the
::  callgraph and updated calls
=;  [w-new=worklist w-call=worklist new-calls=jug-id g1=callgraph]
  =.  g  (~(uni by g) g1)
  =.  called-by
    ::  calculate the diff between new-calls and calls to update called-by
    ::
    =<  $
    ~%  %called-by-update  ..zuse  ~
    |.
    ::  we only add/replace callers to "calls" graph, so grabbing the keys of
    ::  new-calls is enough to get identities of all callers
    ::
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
    ::  worklist of functions whose immediate callees changed
    ::
    %-  ~(rep in w-call)
    |=  [callee=identity acc=worklist]
    (~(uni in acc) `worklist`(~(get ja called-by) callee))
  ::
  ::  total worklist: new functions + functions whose callees changed. Nothing
  ::  else needs to be reanalysed as we'll just get the same result
  ::
  =/  w-new=worklist  (~(uni in w-new) w-new1)
  ?:  =(w-new ~)
    ~&  %done  [g history]
  ~&  [%fixpoint new+~(wyt in ^w-new) upd+~(wyt in w-new1) uniq+~(wyt in `(set ^)`(~(run in w-new) |=(identity fol)))]
  fixpoint-callgraph(w w-new, history [g history])
::
:: ~>  %bout.[0 %iter]
!:
=*  g-previous  g
=<  -
%-  ~(rep in w)
::  note that now "g" is a bunt (empty), but "calls" is inherited from the
::  previous iteration
::
|=  $:  id=identity
        ::  accumulator
        ::
        [[w-new=worklist w-call=worklist calls=_calls g=callgraph] m-new=memo]
    ==
^-  [[worklist worklist jug-id callgraph] memo]
=/  data  (git-g g-previous id)
=/  bus=sock  more.id
=;  [memo-hit=? data-new=datum m-new=memo]
  =.  g  (~(put by g) id data-new)
  =.  calls
    (~(put by calls) id (~(run in callees.data-new) |=([* id=identity *] id)))
  ::
  ::  don't have to put fresh callees in the worklist, they should already be
  ::  there
  ::
  =?  w-new  !memo-hit
    %-  ~(rep in callees.data-new)
    |=  [[* id=identity *] acc=_w-new]
    ?:  (~(has by g-previous) id)  acc
    (~(put in acc) id)
  ::  do have to put ourselves in the callee worklist if our code usage or
  ::  product changed
  ::
  =?  w-call  |(!=([less-code prod map]:data-new [less-code prod map]:data))
    (~(put in w-call) id)
  ::
  [[w-new w-call calls g] m-new]
::
=/  fol  fol.id
=/  sub=sock-anno  [bus 1]
?^  hit=(git:mi m-new fol bus)  [& +.u.hit m-new]
=*  fol-result
  $:  pro=sock-anno
      want=cape
      indirect-code-request=cape
      callees=(set [(unit spot) identity spring])
      area=(unit spot)
  ==
::
=;  ,fol-result
  ::  construct datum & memoize
  ::
  =/  less-code  (~(app ca want) bus)
  =/  capture=cape  (prune-spring:source src.pro cape.sock.pro)
  =/  less-memo  (~(app ca (~(uni ca want) capture)) bus)
  =/  data-new=datum
    [less-code less-memo indirect-code-request sock.pro src.pro area callees]
  ::
  =.  m-new  (put:mi m-new id data-new)
  [| data-new m-new]
::
=|  $=  gen
    $:  want=cape
        indirect-code-request=cape
        callees=(set [(unit spot) identity spring])
        area=(unit spot)
    ==
::
=/  seat=(unit spot)  ~
=<  $
~%  %fol-loop  ..zuse  ~
|.  ^-  [sock-anno _gen]
=*  fol-loop  $
?+    fol  ~|  fol  [dunno gen]
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
  =.  want.gen  (~(uni ca want.gen) (distribute & src.f))
  ?:  (inlineable fol-new)
    fol-loop(fol fol-new, sub s)
  =/  id-there  [sock.s fol-new]
  =<  $
  ~%  %distribute  nock-2  ~
  |.
  =/  [id-there=identity dat-there=datum]
    =/  id-there=identity  [sock.s fol-new]
    ?^  d=(~(get by g-previous) id-there)
      [id-there u.d]
    ?^  par=(recursive-call id id-there called-by g-previous)
      u.par(prod.d |+~, map.d ~)
    [id-there *datum]
  ::
  =.  want.gen  (~(uni ca want.gen) (distribute cape.less-code.dat-there src.s))
  =/  indi  (distribute indirect-code-request.dat-there src.s)
  =.  indirect-code-request.gen  (~(uni ca indirect-code-request.gen) indi)
  ::
  =.  callees.gen  (~(put in callees.gen) seat id-there src.s)
  :: =.  callees.gen  (~(put in callees.gen) [~ id-there src.s])
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