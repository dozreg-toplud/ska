/+  *nock-compilation1
/+  li=line-interpreter
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
::
=/  memo-call
  =>  ..ride  !.
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  ~>  %memo./user
  (g v)
::
:: =/  =long-ska  +:(memo-call ska-poke [&+~ hoot-zpdt-fol] *long-ska)
=/  subject  ..scow:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (scow %ud 5)
::
=|  =long-ska
=^  func=bell  long-ska  (memo-call ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
=/  [bell-graph=(jug bell bell) rev=(jug bell bell)]
  (simple-bell-graph-and-reversed graph.final.long-ska)
::
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
=/  scc-here=(set bell)  (~(gut by scc-map) func [func ~ ~])
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
?:  |
  noun+(run:li |+subject func scc-here rev [code jets]:long-ska scc-map jets-hot)
=/  all-straights=(map bell straight)
  %-  ~(rep by scc-map)
  |=  [[k=* v=(set bell)] acc=(map bell straight)]
  (~(uni by acc) (compile-scc v rev [code jets]:long-ska scc-map jets-hot))
::
:: :-  %tang
:: %-  flop
:-  %noun
%-  to-wain:format  %-  crip
^-  tape
%-  zing
^-  (list tape)
=-  ?:  |  -  :_  -
    =/  pessimistic=straight
      -:(compile-unary func scc-here rev [code jets]:long-ska scc-map ~)
    ::
    =.  pessimistic  (optimize pessimistic)
    "{<`@ux`(mug func)>} pessimistic:\0a{(print-straight:li "  " pessimistic)}\0a"
%+  turn  ~(tap by all-straights)
|=  [k=bell v=straight]
=.  v  (optimize v)
"{<`@ux`(mug k)>}:\0a{(print-straight:li "  " v)}\0a"