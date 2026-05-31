/+  ska-experiment1
/+  our-hoot=hoot
/+  our-hoot-zpdt=hoot-zpdt
::
=,  ska-experiment1
|%
++  condense  ::  lossy
  |=  [g=callgraph id=identity]
  ^-  callgraph
  =/  m=(map identity identity)
    %-  ~(rep by g)
    |=  [[k=identity v=datum] acc=(map identity identity)]
    (~(put by acc) k [less-code.v fol.k])
  ::
  =/  q=(list identity)  ~[id]
  =|  new=callgraph
  |-  ^-  callgraph
  ?~  q  new
  =/  id  (~(got by m) i.q)
  ?:  (~(has by new) id)  $(q t.q)
  =/  d=datum  (~(got by g) i.q)
  =/  callees=(list identity)
    (turn ~(tap in callees.d) |=([* id=identity *] id))
  ::
  =/  g  |*  [* id=identity *]  +<(id (~(got by m) id))
  =.  new  (~(put by new) id d(callees (~(run in callees.d) g)))
  $(q (weld t.q callees))
::
++  render-callgraph
  |=  g=callgraph
  ^-  tang
  =/  funcs=(set identity)
    %-  ~(rep by g)
    |=  [[k=identity [* * * * * * callees=(set [* identity *])]] acc=(set identity)]
    =/  s=(set identity)  (~(run in callees) |=([* id=identity *] id))
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
    |=  [[k=identity [* * * * * * callees=(set [seat=(unit spot) identity *])]] acc=(list tank)]
    :_  acc
    =/  callees=tank
      =/  g  |=([* id=identity *] `@ux`(~(got by func-to-id) id))
      =/  scox  (cury scot %ux)
      =/  g
        |=  [seat=(unit spot) id=identity *]
        =/  seat=tape
          ?~  seat  "??:??"
          =*  l   p.q.u.seat
          =*  r   q.q.u.seat
          =/  ud  |=(a=@u (scow %ud a))
          "{<p.u.seat>}: <[{(ud p.l)} {(ud q.l)}].[{(ud p.r)} {(ud q.r)}]>"
        ::
        leaf+"{<(~(got by func-to-id) id)>} at {seat}"
      [%rose [", " "" ""] (turn ~(tap in callees) g)]
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
:-  %say  |=  *
=/  sub  our-hoot
:: =/  sub  ~
::
=/  fol
  ;;  ^
  =>  sub  !=
  (~(mint ut [%atom %$ ~]) %noun [%dtls $+1])
  :: (scow %ud 5)
  :: (mug 42)
  :: (a-co:co 4)
  :: (mul 1 5)
  :: ((x-co:co 0) 4)
  :: |-  ^-  *
  :: [0 $]
  :: =/  t  |.(0)
  :: |-  ^-  ~
  :: ?:  =(3 $:t)  ~
  :: $(t |.(+($:t)))
  
::
:: ~&  .*(sub fol)
=/  memo-call
  =>  ..ride
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  !.  ~>  %memo./user
  (g v) 
::
=/  g  ~>  %bout
  (memo-call ska-experiment1 &+sub fol)
:: tang+(render-callgraph g)
:: noun+~(wyt by (condense g [&+sub fol]))
:-  %noun
`(list cord)`(turn `wall`(zing `(list wall)`(turn (flop (render-callgraph (condense g [&+sub fol]))) (cury wash 0 80))) crip)


