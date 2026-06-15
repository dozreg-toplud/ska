/+  our-hoot=hoot
/+  our-hoot-zpdt=hoot-zpdt
/+  zuse-vendor
/+  ska-simple=nock-compilation-ska-simplified
::
=,  ska-simple
|%
+$  callee-entry  [id=identity]
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
--
::
:-  %say  |=  *
=/  sub  ~
=/  fol
  ;;  ^
  =>  sub  !=
  !.
  =/  t  |.(0)
  |-  ^-  ~
  ?:  =(3 $:t)  ~
  $(t |.(+($:t)))
::
=/  g=callgraph  ~>  %bout
  (ska-callgraph:ska-simple &+sub fol)
::
noun+(count-bells (condense g [&+sub fol]))