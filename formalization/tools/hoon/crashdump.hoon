:: The raw blocks (before +optimize) of the whole-subject version and of the n-ary version of
:: [10 [6 0 1] 5 [0 6] 0 1], the smallest formula whose raw blocks fill through +crash-need on a
:: register (the edit of an atom), for a subject sock that knows nothing (lemmas/Ska/CompWhole.lean).
:: Before af5cc39 the crash block was [%cel a] [%imm 0 a] [%imm 0 b], since then [%cel a] [%imm 0 b].
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%ten [1 2] [10 [6 0 1] 5 [0 6] 0 1]]
  ==
|-  ^-  @
?~  cases  0
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
=/  res
  %-  mule  |.
  -:(eval-blob [[[`@`0 `sub.i.cases] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ ~)
~&  :*  nam.i.cases  less=less.func
        ?:  ?=(%| -.res)  %interpreter-crashed
        =/  t=tone  p.res
        ?:(?=(%0 -.t) [%0 product.t] ?:(?=(%1 -.t) %1 [%2 (lent trace.t)]))
    ==
~&  [%nomm nomm:(~(got by code.long-ska.state) func)]
~&  [%mono need=need.raw n-args=n-args.raw]
=/  bl  (sort ~(tap by blocks.raw) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
=/  dum  (turn bl |=(x=[@ blob] ~&([%m x] ~)))
=/  nar=straight  (~(gut by nary.cache.state) func *straight)
~&  [%nary need=need.nar n-args=n-args.nar]
=/  nb  (sort ~(tap by blocks.nar) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
=/  dun  (turn nb |=(x=[@ blob] ~&([%n x] ~)))
$(cases t.cases)
