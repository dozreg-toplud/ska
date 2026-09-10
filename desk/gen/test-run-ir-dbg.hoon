/+  *nock-compilation
/+  li=line-interpreter
/+  hoot-zpdt
/+  hoot
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
=/  subject  ..ride:hoot
=/  formula=^
  =>  subject
  ;;  ^
  !=
  =/  gat
    |=  [m=* g=$-(* *)]
    |=  n=*
    (g m n)
  ::
  %.  ~
  %+  gat  [?:(=(1 1) 1 0) 1]
  |=  n=*
  %.  n
  %+  gat  [?:(=(1 1) 1 0) 1]
  |=(* +<)
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
noun+(run:li |+subject func scc-here rev [code jets]:long-ska scc-map ~)