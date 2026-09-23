::  Compile every SCC of the graph after the ride poke and check that every
::  optimized call passes as many arguments as the callee takes.
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  [* [m=@ux ~] ~]
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..ride:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=/  [bell-graph=(jug bell bell) rev=(jug bell bell)]
  (simple-bell-graph-and-reversed graph.final.long-ska)
=/  sccs=(list (set bell))  (tarjan bell-graph)
=/  scc-map=(map bell (set bell))
  =|  out=(map bell (set bell))
  |-  ^+  out
  ?~  sccs  out
  =.  out
    %-  ~(rep in i.sccs)
    |=  [b=bell acc=_out]
    (~(put by acc) b i.sccs)
  ::
  $(sccs t.sccs)
::
=/  jets-hot=(map ring need-ordered)
  %-  malt
  ^-  (list [ring need-ordered])
  =/  unary=need-ordered  [none+~ this+~ none+~]
  =/  binary=need-ordered  [none+~ [this+~ this+~] none+~]
  :~  [/add/one/k135^2 binary]
      [/dec/one/k135^2 unary]
      [/div/one/k135^2 binary]
      [/dvr/one/k135^2 binary]
      [/gte/one/k135^2 binary]
      [/gth/one/k135^2 binary]
      [/lte/one/k135^2 binary]
      [/lth/one/k135^2 binary]
      [/max/one/k135^2 binary]
      [/min/one/k135^2 binary]
      [/mod/one/k135^2 binary]
      [/mul/one/k135^2 binary]
      [/sub/one/k135^2 binary]
      [/bex/two/one/k135^2 unary]
  ==
::
=/  b=bell
  =/  l  (skim ~(tap by code.long-ska) |=([b=bell *] =(m (mug b))))
  ?~  l  ~|(%no-such-bell !!)
  p.i.l
=/  scc=(set bell)  (~(gut by scc-map) b [b ~ ~])
=/  m=(map bell straight)  (compile-scc scc rev [code jets]:long-ska scc-map jets-hot)
=/  s=straight  (~(got by m) b)
=/  calls=(list [from=@ux op=@tas n=@ v=(list @uvre)])
  %-  ~(rep by m)
  |=  [[c=bell t=straight] acc=(list [from=@ux op=@tas n=@ v=(list @uvre)])]
  %-  ~(rep by blocks.t)
  |=  [[* =blob] acc=_acc]
  =.  acc
    ?+  -.fin.blob  acc
      %jmp  ?.(=(a.fin.blob b) acc [[(mug c) %jmp (lent v.fin.blob) v.fin.blob] acc])
      %jmf  ?.(=(a.fin.blob b) acc [[(mug c) %jmf (lent v.fin.blob) v.fin.blob] acc])
    ==
  %+  roll  body.blob
  |=  [op=pole acc=_acc]
  ?+  -.op  acc
    %cal  ?.(=(a.op b) acc [[(mug c) %cal (lent v.op) v.op] acc])
    %caf  ?.(=(a.op b) acc [[(mug c) %caf (lent v.op) v.op] acc])
    %cam  ?.(=(a.op b) acc [[(mug c) %cam (lent v.op) v.op] acc])
  ==
:-  %noun
:*  scc-size+~(wyt in scc)
    need+need.s
    n-args+n-args.s
    less+`@ux`(mug less.b)
    fol+`@ux`(mug fol.b)
    calls+calls
==
