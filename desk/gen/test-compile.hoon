/+  *nock-compilation
/+  li=line-interpreter
/+  hoot-zpdt
/+  hoot
::
:-  %say  |=  *
::
=/  subject  ..scow:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (mul 2 5)
::
=/  [func=bell =long-ska]  (ska-poke [&+subject formula] *long-ska)
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
?:  |
  :: =/  args  ~[subject 42]
  :: noun+(run:li &+args func scc-here rev [code jets]:long-ska scc-map ~)
  noun+(run:li |+subject func scc-here rev [code jets]:long-ska scc-map ~)
=/  all-straights=(map bell straight)
  %-  ~(rep by scc-map)
  |=  [[k=* v=(set bell)] acc=(map bell straight)]
  (~(uni by acc) (compile-scc v rev [code jets]:long-ska scc-map ~))
::
:-  %tang
%-  flop
:: :-  %noun
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