/+  our-hoot=hoot
/+  our-hoot-zpdt=hoot-zpdt
/+  zuse-vendor
/+  nock-compilation1
::
=,  nock-compilation1
|%
++  strongly-normalize-sock
  |=  s=sock
  ^-  sock
  ?@  data.s
    ?^  cape.s  !!
    ?.  cape.s  |+~
    s
  ?@  cape.s
    ?.  cape.s  |+~
    s
  ~+
  =/  l=sock  (hed:so s)
  =/  r=sock  (tel:so s)
  =/  c=cape
    ?:  &(=(cape.l cape.r) ?=(@ cape.l))  cape.l
    [cape.l cape.r]
  ::
  ?:  ?=(%| c)  |+~
  [c data.l data.r]
::
++  count-bells
  |=  g=callgraph
  ^-  @
  =-  ~(wyt in -)
  ^-  (set bell)
  %-  ~(rep by g)
  |=  [[k=identity v=datum] acc=(set bell)]
  (~(put in acc) [(strongly-normalize-sock less-code.v) fol.k])
::
++  condense
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
  =/  id  (~(gut by m) i.q [|+~ fol.i.q])
  ?:  (~(has by new) id)  $(q t.q)
  =/  d=datum  (git-g g i.q)
  =/  callees=(list identity)
    (turn ~(tap in callees.d) |=(callee-entry id))
  ::
  =/  g  |=  callee-entry  +<(id (~(gut by m) id [|+~ fol.id]))
  =.  new  (~(put by new) id d(callees (~(run in callees.d) g)))
  $(q (weld t.q callees))
::
++  render-callgraph
  |=  g=callgraph
  ^-  tang
  =/  funcs=(set identity)
    %-  ~(rep by g)
    |=  [[k=identity v=datum] acc=(set identity)]
    =/  s=(set identity)  (~(run in callees.v) |=(callee-entry id))
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
    leaf+"{(scow %ux num)}: [sock={(scow %ux (mug more.id))} fol={(scow %ux (mug fol.id))}] at {area}; {<indi.dat>}"
  ::
  =/  calls-rendered=(list tank)
    %-  ~(rep by g)
    |=  [[k=identity [callees=(set callee-entry) *]] acc=(list tank)]
    :_  acc
    =/  callees=tank
      =/  scox  (cury scot %ux)
      =/  gate
        |=  callee-entry
        =/  seat=tape
          ?~  seat  "??:??"
          =*  l   p.q.u.seat
          =*  r   q.q.u.seat
          =/  ud  |=(a=@u (scow %ud a))
          "{<p.u.seat>}: <[{(ud p.l)} {(ud q.l)}].[{(ud p.r)} {(ud q.r)}]>"
        ::
        leaf+"{<(~(got by func-to-id) id)>} at {seat}"
      [%rose [", " "" ""] (turn ~(tap in callees) gate)]
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
:: =/  sub  zuse-vendor
:: =/  sub  ~
:: =/  sub  ska-experiment1-hoot
:: =/  sub
::   !:
::   =>  our-hoot
::   :_  .
::   ^-  m=(map @ $-(@ @))
::   %-  malt
::   ^-  (list [@ $-(@ @)])
::   :~  0+|=(@ (dec +<))
::       1+|=(@ (succ +<))
::       2+|=(@ (same +<))
::   ==
::
=/  fol
  ;;  ^
  =>  sub  !=
  :: (~(mint ut [%atom %$ ~]) %noun [%dtls $+1])
  :: (ream '42')
  (ride %noun '42')
  :: !.
  :: =/  t  |.(0)
  :: |-  ^-  ~
  :: ?:  =(3 $:t)  ~
  :: $(t |.(+($:t)))
  ::
  :: (scow %ud 5)
  :: (mug 42)
  :: (a-co:co 4)
  :: (dec 2)
  :: ((x-co:co 0) 4)
  :: |-  ^-  *
  :: [0 $]
  :: $:en:json:html
  :: (.)
  :: =/  m=(map @ $-(@ @))
    :: %-  malt
    :: ^-  (list [@ $-(@ @)])
    :: :~  0+|=(@ (dec +<))
    ::     2+|=(@ (same +<))
    :: ==
    :: ~
  ::
  :: |-  ^-  @
  :: ?~  m  !!
  :: ?:  =(1 p.n.m)  (q.n.m 42)
  :: ?:  =(1 p.n.m)  $(m l.m)
  :: $(m r.m)
::
:: ~&  .*(sub fol)
=/  memo-call
  =>  ..ride  !.
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  ~>  %memo./user
  (g v) 
::
=/  l=(list callgraph)  ~>  %bout
  (ska-callgraph:nock-compilation1 [&+sub fol] ~)
:: noun+(lent g)
:: :-  %noun
:: =;  l=(list wain)
::   %-  zing
::   (join `wain`~['====================='] l)
:: %+  turn  l
:: |=  g=callgraph
:: ~>  %bout
:: noun+(turn l |=(g=callgraph ~(wyt by (condense g [&+sub fol]))))
:: =/  g  -.l
:: (turn `wall`(zing `(list wall)`(turn (flop (render-callgraph (condense g [&+sub fol]))) (cury wash 0 80))) crip)
noun+(count-bells (condense -:l [&+sub fol]))