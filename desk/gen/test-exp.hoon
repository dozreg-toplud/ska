/+  ska-experiment1
/+  our-hoot=hoot
::
=,  ska-experiment1
|%
++  condense  ::  lossy
  |=  g=callgraph
  ^-  callgraph
  =/  m=(map identity identity)
    %-  ~(rep by g)
    |=  [[k=identity v=datum] acc=(map identity identity)]
    (~(put by acc) k [less-code.v fol.k])
  ::
  =/  f  |=  [seat=(unit spot) =identity]  [seat (~(got by m) identity)]
  ::
  %-  ~(rep by g)
  |=  [[k=identity v=datum] acc=callgraph]
  (~(put by acc) [less-code.v fol.k] v(callees (~(run in callees.v) f)))
::
++  render-callgraph
  |=  g=callgraph
  ^-  tang
  =/  funcs=(set identity)
    %-  ~(rep by g)
    |=  [[k=identity [* * * * * callees=(set [* identity])]] acc=(set identity)]
    =/  s=(set identity)  (~(run in callees) |=([* identity] +<+))
    (~(put in (~(uni in acc) s)) k)
  ::
  =/  func-to-id=(map identity @ux)
    =<  +
    %-  ~(rep in funcs)
    |=  [id=identity acc=[c=@ux m=(map identity @ux)]]
    %_  acc
      c  +(c.acc)
      m  (~(put by m.acc) id c.acc)
    ==
  ::
  =/  funcs-rendered=(list tank)
    %-  ~(rep by func-to-id)
    |=  [[id=identity num=@ux] acc=(list tank)]
    =/  dat  (~(got by g) id)
    =/  area=tape  ?~  area.dat  "??:??"
      =*  l   p.q.u.area.dat
      =*  r   q.q.u.area.dat
      =/  ud  |=(a=@u (scow %ud a))
      "{<p.u.area.dat>}: <[{(ud p.l)} {(ud q.l)}].[{(ud p.r)} {(ud q.r)}]>"
    ::
    :_  acc
    leaf+"{(scow %ux num)}: [sock={(scow %ux (mug more.id))} fol={(scow %ux (mug fol.id))}] at {area}"
  ::
  =/  calls-rendered=(list tank)
    %-  ~(rep by g)
    |=  [[k=identity [* * * * * callees=(set [* identity])]] acc=(list tank)]
    :_  acc
    =/  callees=tank
      =/  g  |=([* id=identity] `@ux`(~(got by func-to-id) id))
      =/  scox  (cury scot %ux)
      [%rose [", " "" ""] (turn ~(tap in callees) (cork g scox))]
    ::
    [%rose [" -> " "(" ")"] (scot %ux (~(got by func-to-id) k)) callees ~]

  ::
  %-  flop  ^-  (list tank)
  :~  'functions:'
      [%rose [" " "\{" "}"] funcs-rendered]
      ''
      'callgraph:'
      [%rose [" " "\{" "}"] calls-rendered]
  ==
--
::
:-  %say  |=  *  :-  %noun
=/  sub  our-hoot
::
=/  fol
  ;;  ^
  =>  sub  !=
  (~(mint ut [%atom %$ ~]) %noun [%dtls $+1])
::
:: ~&  .*(sub fol)
=/  g  ~>  %bout  (ska-experiment1 &+sub fol)
:: ~:(render-callgraph (condense g))
~(wyt by g)