:: The raw blocks of the whole-subject version (+compiled-mono, what %full runs) of direct
:: calls (lemmas/Ska/CompDirect.lean, README Gaps 18), with the nomm, the n-ary need and raw
:: blocks of each callee.  A callee that the analysis can inline becomes [7 p callee-nomm]
:: (a first version of this file called [0 6]: [2 [0 1] [1 [0 6]]] is [7 [0 1] [0 6]]), so the
:: callee is the recursive R of calldump.hoon.  The whole-subject version runs +run with mono &:
:: a direct call takes the subject whole in one register and +mono-try-call tests and splits it
:: (%clq, %hed, %tal) before the optimistic %jmp/%cal, and calls by subject (%jsp/%csl) when a
:: part is missing.  %dt a tail call, %dn a call under %4, %dc a call in the head of a cons.
=/  r=*  [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%dt [1 2 3] [8 [1 r] [9 2 [0 1]]]]
      [%dn [1 2 3] [4 [8 [1 r] [9 2 [0 1]]]]]
      [%dc [1 2 3] [[8 [1 r] [9 2 [0 1]]] [0 1]]]
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
