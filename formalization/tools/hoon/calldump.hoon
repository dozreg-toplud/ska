:: The raw blocks of +comp (before +optimize) for calls, for a subject sock that knows
:: nothing, as proxy-dump.hoon compiles them, with the nomm of the top function and the
:: need and raw blocks of every callee compiled on the way (lemmas/Ska/CompCall.lean).
:: R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]] recurs on the tail of its sample, so
:: +inlined keeps the calls of it (a callee that calls itself is never inlined).  The top
:: function's blocks are those of its whole-subject version (compiled-mono); the callees
:: listed are the n-ary versions, the top function's among them, each with its nomm.
:: %dseq and %dtwo (2026-11-24, twelfth session): two calls in sequence, and two calls in a
:: cons, the second under an increment.
=/  r=*  [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%ind [[4 0 1] 5] [2 [0 3] [0 2]]]
      [%dtail [1 2 3] [8 [1 r] [9 2 [0 1]]]]
      [%dnext [1 2 3] [4 [8 [1 r] [9 2 [0 1]]]]]
      [%dcons [1 2 3] [[8 [1 r] [9 2 [0 1]]] [0 1]]]
      [%dsix [1 2 3] [6 [3 [0 1]] [8 [1 r] [9 2 [0 1]]] [1 0]]]
      [%dpick [1 2 0] [6 [8 [1 r] [9 2 [0 1]]] [1 0] [1 1]]]
      [%drop [1 2 3] [7 [8 [1 r] [9 2 [0 1]]] [1 5]]]
      [%dseq [1 2 3] [7 [8 [1 r] [9 2 [0 1]]] [8 [1 r] [9 2 [0 1]]]]]
      [%dtwo [1 2 3] [[8 [1 r] [9 2 [0 1]]] [4 [8 [1 r] [9 2 [0 1]]]]]]
  ==
|-  ^-  @
?~  cases  0
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
=/  res
  %-  mule  |.
  -:(eval-blob [[[`@`0 `sub.i.cases] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ ~)
=/  bl  (sort ~(tap by blocks.raw) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
~&  :*  nam.i.cases  mock=a
        ?:  ?=(%| -.res)  %interpreter-crashed
        =/  t=tone  p.res
        ?:(?=(%0 -.t) [%0 product.t] ?:(?=(%1 -.t) %1 [%2 (lent trace.t)]))
        n=(lent bl)
    ==
~&  [%nomm nomm:(~(got by code.long-ska.state) func)]
=/  cal  ~(tap by nary.cache.state)
=/  dum
  %+  turn  cal
  |=  [b=bell s=straight]
  =/  cn  (~(get by code.long-ska.state) b)
  ~&  [%callee fol=fol.b need=need.s nomm=?~(cn ~ `nomm.u.cn)]
  =/  cb  (sort ~(tap by blocks.s) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
  %+  turn  cb
  |=  x=[@ blob]
  ~&  [%c x]
  ~
|-
?~  bl  ^$(cases t.cases)
~&  i.bl
$(bl t.bl)
