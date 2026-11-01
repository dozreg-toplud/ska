::  Deferred %mean traps. A trap with a known battery is pushed as its $ arm
::  and the parts of the trap the arm needs, instead of the trap capturing the
::  whole subject; the known product of a pure arm is pushed instead; an unknown
::  trap is captured as before. For each case: whether the interpreter agrees
::  with Nock, the IR of the gate body and the IR of the arms it pushes.
::
/+  *nock-compilation
/+  li=line-interpreter
/+  hoot-zpdt
::
:-  %say  |=  [* ~ cain=_| sell=_| run=_&]
=/  core  ..scow:hoot-zpdt
::  the gate is at the head of the subject: its body is the function of the
::  gate's battery
::
=/  deferred  =>(core [gat=|=(a=@ ~>(%mean.|.(leaf+(scow %ud a)) (dec a))) .])
=/  constant  =>(core [gat=|=(a=@ ~_(leaf+"foo" (dec a))) .])
::  a battery that depends on data is unknown to the analysis
::
=/  unknown
  =>  core
  :_  .
  ^=  gat
  |=  a=@
  ~>  %mean.?:(=(a 5) |.(leaf+"a") |.(leaf+"b"))
  (dec a)
::  ~| on data: the arm prints a vase, a lot of code to analyze, from a core
::  that has the printer
::
=/  mean-sell  =>(..cain:hoot-zpdt [gat=|=(a=@ ~|([%foo a] (dec a))) .])
::  the same printing as a plain call, to tell its compilation problems from
::  those of deferring it
::
=/  call-sell  =>(..cain:hoot-zpdt [gat=|=(a=@ [(cain !>([%foo a])) (dec a)]) .])
=/  cases=(list [name=tape sub=* fol=^ show=?])
  %+  weld
    ^-  (list [name=tape sub=* fol=^ show=?])
    :~  ["deferred" deferred ;;(^ =>(deferred !=((gat 5)))) &]
        ["deferred, crash" deferred ;;(^ =>(deferred !=((gat 0)))) |]
        ["constant" constant ;;(^ =>(constant !=((gat 5)))) &]
        ["constant, crash" constant ;;(^ =>(constant !=((gat 0)))) |]
        ["unknown" unknown ;;(^ =>(unknown !=((gat 5)))) &]
        ["unknown, crash" unknown ;;(^ =>(unknown !=((gat 0)))) |]
    ==
  %+  weld
    ^-  (list [name=tape sub=* fol=^ show=?])
    ?.  sell  ~
    :~  ["cain call" call-sell ;;(^ =>(call-sell !=((gat 5)))) |]
    ==
  ^-  (list [name=tape sub=* fol=^ show=?])
  ?.  cain  ~
  :~  ["~|" mean-sell ;;(^ =>(mean-sell !=((gat 5)))) &]
      ["~|, crash" mean-sell ;;(^ =>(mean-sell !=((gat 0)))) |]
  ==
::
=/  check
  |=  [name=tape sub=* fol=^ show=?]
  ^-  tape
  =|  lon=long-ska
  =^  [func=bell *]  lon  (ska-poke [&+sub fol] lon)
  =/  [scc=(set bell) sccs=(map bell (set bell))]  (scc-of func calls.lon ~)
  =/  cache=comp-cache  [~ ~ sccs]
  =^  m=(map bell straight)  cache
    (compile-scc scc [code jets calls]:lon ~ cache)
  =.  m  (~(uni by nary.cache) m)
  ::  interpreter vs nock, unless only compiling
  ::
  =/  verdict=tape
    ?.  run  "compiled"
    =/  [rev=(jug bell bell) scc-map=(map bell (set bell))]  (graph-info:li lon)
    =/  expect=(unit *)  (mole |.(.*(sub fol)))
    =/  got=(unit *)  (run:li |+sub func scc rev lon scc-map ~)
    "expect={<expect>} got={<got>} {?:(=(expect got) "OK" "MISMATCH")}"
  ?.  show  "== {name}: {verdict}\0a"
  ::  the gate body and the arms it pushes
  ::
  ?>  ?=([[* *] *] sub)
  =/  bat=*  -<.sub
  =/  bodies=(list bell)  (skim ~(tap in ~(key by m)) |=(b=bell =(fol.b bat)))
  =/  print-bell
    |=  b=bell
    ^-  tape
    =/  s  (optimize (~(got by m) b))
    "{<`@ux`(mug b)>}:\0a{(print-straight:li "  " s)}\0a"
  =/  pushed=(list bell)
    %-  zing
    %+  turn  bodies
    |=  b=bell
    ^-  (list bell)
    =/  s  (optimize (~(got by m) b))
    %-  zing
    %+  turn  ~(val by blocks.s)
    |=  =blob
    ^-  (list bell)
    %+  murn  body.blob
    |=  op=pole
    ^-  (unit bell)
    ?:(?=(%hmp -.op) `a.op ~)
  =/  body-ir=tape  (zing (turn bodies print-bell))
  =/  arms-ir=tape  (zing (turn pushed print-bell))
  ::
  %-  zing
  :~  "== {name}: {verdict}\0a"
      "-- functions: {<~(wyt by m)>}, body\0a"
      body-ir
      "-- pushed arms\0a"
      arms-ir
  ==
::
:-  %tang
%-  flop
%-  to-wain:format
%-  crip
(zing (turn cases check))
