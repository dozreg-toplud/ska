:: directdump2.hoon: the cases of directdump.hoon and more (lemmas/Ska/CompDirectM.lean,
:: README Gaps 18): %dt a tail call, %dn under %4, %dc in the head of a cons, %dk in the tail of
:: a cons, %dp a call for %pick, and the same with a callee R2 whose need splits two levels deep
:: (%et, %en).  Prints the top's need and argument count and each callee's bell and need.
=/  r=*  [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  r2=*  [6 [3 [0 6]] [9 2 [10 [6 [0 13]] [0 1]]] [0 7]]
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%dt [1 2 3] [8 [1 r] [9 2 [0 1]]]]
      [%dn [1 2 3] [4 [8 [1 r] [9 2 [0 1]]]]]
      [%dc [1 2 3] [[8 [1 r] [9 2 [0 1]]] [0 1]]]
      [%dk [1 2 3] [[0 1] [8 [1 r] [9 2 [0 1]]]]]
      [%dp [1 2 3] [6 [8 [1 r] [9 2 [0 1]]] [1 0] [1 1]]]
      [%et [[1 2] 3] [8 [1 r2] [9 2 [0 1]]]]
      [%en [[1 2] 3] [4 [8 [1 r2] [9 2 [0 1]]]]]
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
~&  [%top need=need.raw nargs=n-args.raw]
=/  cal  ~(tap by nary.cache.state)
=/  dum
  %+  turn  cal
  |=  [b=bell s=straight]
  =/  cn  (~(get by code.long-ska.state) b)
  ~&  [%callee bell=b need=need.s nomm=?~(cn ~ `nomm.u.cn)]
  =/  cb  (sort ~(tap by blocks.s) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
  %+  turn  cb
  |=  x=[@ blob]
  ~&  [%c x]
  ~
|-
?~  bl  ^$(cases t.cases)
~&  i.bl
$(bl t.bl)
