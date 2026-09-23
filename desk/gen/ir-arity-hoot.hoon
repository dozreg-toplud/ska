::  Compile every SCC of the graph after the ride poke and check that every
::  optimized call passes as many arguments as the callee takes.
::
/+  *nock-compilation
/+  hoot
/+  hoot-fol
::
:-  %say  |=  *
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-fol] long-ska)
=/  subject  ..ride:hoot
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
~>  %bout
=/  all=(map bell straight)
  %-  ~(rep by scc-map)
  |=  [[k=* v=(set bell)] acc=(map bell straight)]
  (~(uni by acc) (compile-scc v rev [code jets]:long-ska scc-map jets-hot))
::
=/  bad=(list [caller=@ux callee=@ux got=@ want=@ op=@tas])
  %-  ~(rep by all)
  |=  [[b=bell s=straight] acc=(list [caller=@ux callee=@ux got=@ want=@ op=@tas])]
  %-  ~(rep by blocks.s)
  |=  [[* =blob] acc=_acc]
  =/  check
    |=  [a=bell v=(list @uvre) op=@tas acc=_acc]
    ^+  acc
    ?~  t=(~(get by all) a)  [[(mug b) (mug a) (lent v) 999 op] acc]
    ?:  =((lent v) n-args.u.t)  acc
    [[(mug b) (mug a) (lent v) n-args.u.t op] acc]
  =.  acc
    ?+  -.fin.blob  acc
      %jmp  (check a.fin.blob v.fin.blob %jmp acc)
      %jmf  (check a.fin.blob v.fin.blob %jmf acc)
    ==
  %+  roll  body.blob
  |=  [op=pole acc=_acc]
  ?+  -.op  acc
    %cal  (check a.op v.op %cal acc)
    %caf  (check a.op v.op %caf acc)
    %cam  (check a.op v.op %cam acc)
  ==
:: source area of a function with the callee's formula, if spots are known
::
=/  areas=(map @ux (unit spot))
  %-  ~(rep by graph.final.long-ska)
  |=  [[id=identity d=datum] acc=(map @ux (unit spot))]
  (~(put by acc) (mug fol.id) area.d)
=/  fol-of=(map @ux @ux)
  %-  ~(rep by all)
  |=  [[b=bell *] acc=(map @ux @ux)]
  (~(put by acc) (mug b) (mug fol.b))
:-  %noun
:-  n-bells+~(wyt by all)
%+  turn  bad
|=  m=[caller=@ux callee=@ux got=@ want=@ op=@tas]
:-  m
=/  f  (~(get by fol-of) callee.m)
?~  f  ~
?~  a=(~(get by areas) u.f)  ~
?~  u.a  ~
`[p.q.u.u.a q.q.u.u.a]
