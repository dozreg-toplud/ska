:: The raw blocks (before +optimize) of the whole-subject version for a subject sock that
:: knows nothing, of formulas whose parts run under goals with lazy entries (bonds behind a
:: call, forks of a %6), with the nomm and the need (lemmas/Ska/CompLazyGoal.lean).
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%bnd [[4 0 1] 5] [[0 1] [2 [0 3] [0 2]]]]
      [%bnh [[4 0 1] 5] [[0 2] [2 [0 3] [0 2]]]]
      [%bnc [[4 0 1] 5] [[4 [0 3]] [2 [0 3] [0 2]]]]
      [%fk1 [1 2] [7 [0 3] [6 [0 1] [0 2] [1 0]]]]
      [%fk2 [1 2] [7 [[0 2] [0 3]] [6 [0 2] [0 3] [1 0]]]]
      [%fk3 [0 2] [7 [6 [0 2] [1 0] [1 1]] [6 [0 1] [1 5] [1 6]]]]
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
