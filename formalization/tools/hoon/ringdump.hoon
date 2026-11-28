::  Track K (README Gaps 19 (g), 2026-11-28): the raw blocks of direct calls
::  to callees WITH A RING (no hot driver), for the model `callLR` / `callDMR`
::  (`lemmas/Ska/CompRingCall.lean`, checks in `CompRingCheck.lean`).
::  The core cor = [[ma [mb mc]] 1 2 0] (three arms, axes 4, 10, 11) is
::  registered by %fast (/mm) before any compile, so every arm gets a ring at
::  the analysis that first sees it.  ma recurs on the tail of its payload
::  (a recursive ring arm); mb is ma under %4; mc is a cons of two arm calls.
::  Part A, per root formula on cor: ska-poke, then the whole-subject version
::  (+compiled-mono) and the n-ary version (+compiled-nary) of the root; the
::  nomm, the top's need, n-args and less, the raw blocks; every nary.cache
::  entry (bell, need, blocks).  Part B, a callee registered AFTER its caller
::  was compiled: cor2 = [[na nb] 1 0], the root [9 4 0 1] compiled with no
::  registration, then %fast /nn, %jets ~ (rings by +ska-cole-settle), and
::  the root from the cache and recompiled.
::
=/  ma=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  mb=*  [4 [9 4 [0 1]]]
=/  mc=*  [[9 4 [0 1]] [9 10 [0 1]]]
=/  cor=*  [[ma [mb mc]] [1 2 0]]
=/  na=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  nb=*  [5 [1 0] [9 4 [0 1]]]
=/  cor2=*  [[na nb] [1 0]]
=/  cases=(list [nam=@tas fol=*])
  :~  [%rt [7 [0 1] [9 4 [0 1]]]]
      [%rn [7 [0 1] [4 [9 4 [0 1]]]]]
      [%rc [7 [0 1] [[9 4 [0 1]] [0 1]]]]
      [%rk [7 [0 1] [[0 1] [9 4 [0 1]]]]]
      [%rp [7 [0 1] [6 [9 4 [0 1]] [1 7] [1 8]]]]
      [%rb [7 [0 1] [6 [3 [0 3]] [9 4 [0 1]] [1 0]]]]
      [%rm [7 [0 1] [9 10 [0 1]]]]
      [%rx [7 [0 1] [9 11 [0 1]]]]
  ==
=/  dump
  |=  [tag=@tas s=straight]
  =/  bl  (sort ~(tap by blocks.s) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
  ~&  [tag %need need.s %nargs n-args.s]
  ~&  [tag %rawneed `*`need.s]
  |-  ^-  @
  ?~  bl  0
  ~&  [tag %raw `*`i.bl]
  $(bl t.bl)
=^  p0  ..poke  (poke [%fast | ~[[/mm [& cor]]]])
~&  [%cole-a ~(tap by call.cole.jets.long-ska.state)]
=/  cs  cases
=/  done-a=@
  |-  ^-  @
  ?~  cs  0
  =.  nary.cache.state  ~
  =.  mono.cache.state  ~
  =/  a=toon  (mook (mink [cor fol.i.cs] ~))
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [&+cor ?>(?=(^ fol.i.cs) fol.i.cs)] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  =^  nar=straight  cache.state  (compiled-nary func scc)
  ~&  [nam.i.cs %mock a %func func]
  ~&  [nam.i.cs %nomm nomm:(~(got by code.long-ska.state) func)]
  ~&  [nam.i.cs %rawnomm `*`nomm:(~(got by code.long-ska.state) func) %rawless `*`less.func]
  ~&  [nam.i.cs %cole ~(tap by call.cole.jets.long-ska.state)]
  ~&  [nam.i.cs %rawinl `*`(~(get by inl.cache.state) func)]
  =/  m  (dump (cat 3 nam.i.cs '-mono') raw)
  =/  n  (dump (cat 3 nam.i.cs '-nary') nar)
  =/  cal  ~(tap by nary.cache.state)
  =/  dd
    |-  ^-  @
    ?~  cal  0
    ?:  =(p.i.cal func)  $(cal t.cal)
    =/  cn  (~(get by code.long-ska.state) p.i.cal)
    ~&  [nam.i.cs %callee p.i.cal ?~(cn ~ `nomm.u.cn)]
    ~&  [nam.i.cs %rawcallee `*`p.i.cal `*`?~(cn ~ `nomm.u.cn)]
    ~&  [nam.i.cs %rawcalleeinl `*`(~(get by inl.cache.state) p.i.cal)]
    =/  k  (dump (cat 3 nam.i.cs '-callee') q.i.cal)
    $(cal t.cal)
  $(cs t.cs)
::  Part B
::
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [&+cor2 [7 [0 1] [9 4 [0 1]]]] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
~&  [%b0 %func func %nomm nomm:(~(got by code.long-ska.state) func)]
~&  [%b0 %rawnomm `*`nomm:(~(got by code.long-ska.state) func) %rawless `*`less.func]
=/  m  (dump %b0-mono raw)
~&  [%b0-cole ~(tap by call.cole.jets.long-ska.state)]
=^  p1  ..poke  (poke [%fast | ~[[/nn [& cor2]]]])
~&  [%b1-cole ~(tap by call.cole.jets.long-ska.state) %pend ~(wyt by pend.jets.long-ska.state)]
~&  [%b1-cached (~(has by mono.cache.state) func) (~(has by nary.cache.state) func)]
=^  p2  ..poke  (poke [%jets ~])
~&  [%b2-prod p2]
~&  [%b2-cole ~(tap by call.cole.jets.long-ska.state) %pend ~(wyt by pend.jets.long-ska.state)]
~&  [%b2-cached (~(has by mono.cache.state) func) (~(has by nary.cache.state) func)]
=^  raw2=straight  cache.state  (compiled-mono func scc)
=/  m2  (dump %b2-mono-cached raw2)
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=^  raw3=straight  cache.state  (compiled-mono func scc)
=/  m3  (dump %b3-mono-fresh raw3)
0
