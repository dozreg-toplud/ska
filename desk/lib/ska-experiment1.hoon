/-  *noir
?>  =(|+~ *sock)
?>  =(| *cape)
|%
+$  identity  [more=sock fol=^]
+$  spring  *  ::  no union stuff
+$  datum
  $:  callees=(set [seat=(unit spot) =identity src=spring])
      nomm=nomm-1
      less-code=sock
      less-memo=sock
      indirect-code-request=cape
      [prod=sock map=spring]
      area=(unit spot)
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
  =/  w-back=worklist
    ::  worklist of functions whose immediate callees changed
    ::
    %-  ~(rep in w-call)
    |=  [callee=identity acc=worklist]
    (~(uni in acc) `worklist`(~(get ja called-by) callee))
  ::
  ::  total worklist: new functions + functions whose callees changed. Nothing
  ::  else needs to be reanalysed as we'll just get the same result
  ::
  =/  w-new=worklist  (~(uni in w-new) w-back)
  ?:  =(w-new ~)  [g history]
  =/  new-count   ~(wyt in ^w-new)
  =/  upd-count   ~(wyt in w-back)
  =/  uniq-count  ~(wyt in `(set ^)`(~(run in w-new) |=(identity fol)))
  ~&  [%fixpoint new+new-count upd+upd-count uniq+uniq-count]
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
  $:  [nomm=nomm-1 pro=sock-anno]
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
    [ callees  nomm
      less-code  less-memo
      indirect-code-request
      pro  area
    ]
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
^-  [[nomm=nomm-1 prod=sock-anno] gen=_gen]
=<  $
~%  %fol-loop  ..zuse  ~
|.  ^-  [[nomm=nomm-1 prod=sock-anno] _gen]
=*  fol-loop  $
?+    fol  ~|  fol  [[0+0 dunno] gen]
    [p=^ q=^]
  =^  l  gen  fol-loop(fol p.fol)
  =^  r  gen  fol-loop(fol q.fol)
  =<  $
  ~%  %nock-cons  ..fol-loop  ~
  |.
  :_  gen
  :-  [nomm.l nomm.r]
  :-  (~(knit so sock.prod.l) sock.prod.r)
  (cons-spring:source src.prod.l src.prod.r)
::
    [%0 p=@]
  =<  $
  ~%  %nock-0  ..fol-loop  ~
  |.
  :_  gen
  :-  [%0 p.fol]
  ?:  =(0 p.fol)  dunno
  ?:  =(1 p.fol)  sub
  :-  (~(pull so sock.sub) p.fol)
  ((slot-spring:source p.fol) src.sub)
::
    [%1 p=*]
  :_  gen
  :-  [%1 p.fol]
  [&+p.fol ~]
::
    [%2 p=^ q=^]
  =^  s  gen  fol-loop(fol p.fol)
  =^  f  gen  fol-loop(fol q.fol)
  =<  $
  ~%  %nock-2  ..fol-loop  ~
  |.
  ^-  [[nomm-1 sock-anno] _gen]
  =*  nock-2  .
  ?.  &(=(& cape.sock.prod.f) ?=(^ data.sock.prod.f))
    ::  indirect call
    ::
    :: ~&  %indi
    :: ~&  seat
    =.  indirect-code-request.gen
      (~(uni ca indirect-code-request.gen) (distribute & src.prod.f))
    ::
    [[[%2 nomm.s `nomm.f ~] dunno] gen]
  =/  fol-new  data.sock.prod.f
  =.  want.gen  (~(uni ca want.gen) (distribute & src.prod.f))
  ?:  (inlineable fol-new)
    =^  inline  gen  fol-loop(fol fol-new, sub prod.s)
    :_  gen
    :-  [%7 nomm.s nomm.inline]
    prod.inline
  =<  $
  ~%  %distribute  nock-2  ~
  |.
  ^-  [[nomm-1 sock-anno] _gen]
  =/  [id-there=identity dat-there=datum]
    =/  id-there=identity  [sock.prod.s fol-new]
    ?^  d=(~(get by g-previous) id-there)
      [id-there u.d]
    ?^  par=(recursive-call id id-there called-by g-previous)
      u.par(prod.d |+~, map.d ~)
    [id-there *datum]
  ::
  =.  want.gen
    (~(uni ca want.gen) (distribute cape.less-code.dat-there src.prod.s))
  ::
  =/  indi  (distribute indirect-code-request.dat-there src.prod.s)
  =.  indirect-code-request.gen  (~(uni ca indirect-code-request.gen) indi)
  =.  callees.gen  (~(put in callees.gen) seat id-there src.prod.s)
  :_  gen
  ^-  [nomm-1 sock-anno]
  :-  [%2 nomm.s `nomm.f ~ less-code.dat-there fol-new]  ::  XX remove unit from q, rely on registerization
  :-  prod.dat-there
  (compose-spring:source map.dat-there src.prod.s)
::
    [%3 p=^]
  =^  p  gen  fol-loop(fol p.fol)
  :_  gen
  :-  [%3 nomm.p]
  dunno
::
    [%4 p=^]
  =^  p  gen  fol-loop(fol p.fol)
  :_  gen
  :-  [%4 nomm.p]
  dunno
::
    [%5 p=^ q=^]
  =^  p  gen  fol-loop(fol p.fol)
  =^  q  gen  fol-loop(fol q.fol)
  :_  gen
  :-  [%5 nomm.p nomm.q]
  dunno
::  pessimization: calls with the subject that comes from a fork are indirect
::
    [%6 p=^ q=^ r=^]
  =^  p  gen  fol-loop(fol p.fol)
  =^  q  gen  fol-loop(fol q.fol)
  =^  r  gen  fol-loop(fol r.fol)
  :_  gen
  :-  [%6 nomm.p nomm.q nomm.r]
  dunno
::
    [%7 p=^ q=^]
  =^  p  gen  fol-loop(fol p.fol)
  =^  q  gen  fol-loop(fol q.fol, sub prod.p)
  :_  gen
  :-  [%7 nomm.p nomm.q]
  prod.q
::
    [%8 p=^ q=^]
  fol-loop(fol [%7 [p.fol 0+1] q.fol])
::
    [%9 p=@ q=^]
  fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
::
    [%10 [a=@ don=^] rec=^]
  ?:  =(0 a.fol)  [[0+0 dunno] gen]
  =^  don  gen  fol-loop(fol don.fol)
  =^  rec  gen  fol-loop(fol rec.fol)
  =<  $
  ~%  %nock-10  ..fol-loop  ~
  |.
  :_  gen
  :-  [%10 [a.fol nomm.don] nomm.rec]
  :-  (~(darn so sock.prod.rec) a.fol sock.prod.don)
  ((edit-spring:source a.fol) src.prod.rec src.prod.don)
::
    [%11 p=@ q=^]
  =^  q  gen  fol-loop(fol q.fol)
  :_  gen
  :-  [%11 p.fol nomm.q q.fol]
  prod.q
::
    [%11 [a=@ h=^] f=^]
  =?  .  &(=(a.fol %spot) =(1 -.h.fol))
    =*  dot  .
    =/  pot=(unit spot)  `;;(spot +.h.fol)  ::  XX soft
    =?  area.gen  ?=(~ area.gen)  pot
    =.  seat  pot
    dot
  ::
  =^  h  gen  fol-loop(fol h.fol)
  =^  f  gen  fol-loop(fol f.fol)
  :_  gen
  :-  [%11 [a.fol nomm.h] nomm.f f.fol]
  prod.f
::
    [%12 p=^ q=^]
  =^  p  gen  fol-loop(fol p.fol)
  =^  q  gen  fol-loop(fol q.fol)
  :_  gen
  :-  [%12 nomm.p nomm.q]
  dunno
==