:: The raw blocks (before +optimize) of the whole-subject version for a subject sock that
:: knows nothing, of %7 with indirect calls in its parts in the forms that the analysis
:: gives %7 (README Gaps 12.21, lemmas/Ska/CompSevenF.lean): %7 itself, %8 (the pushed pair a
:: cons whose head calls, or a call in the body), %9 (the arm's call, with a calling core
:: formula), an inlined %2, %7 whose q's need has a bond (%s7f, %s7g), the gate call
:: [8 [9 2 [0 2]] [9 2 [10 [6 [0 7]] [0 2]]]] (%gat), and an [8 b c] outside the fragment (%lim).
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%s7a [[4 0 1] 5] [7 [2 [0 3] [0 2]] [4 [0 1]]]]
      [%s7b [0 1] [7 [[0 1] [0 1]] [2 [0 3] [0 2]]]]
      [%e8a [[4 0 1] 5] [8 [2 [0 3] [0 2]] [4 [0 2]]]]
      [%e8b [[4 0 1] 5] [8 [0 3] [2 [0 2] [0 6]]]]
      [%e9a [[4 0 3] 5] [9 2 [0 1]]]
      [%e9b [[1 [4 0 3] 5] 7] [9 2 [2 [0 3] [0 2]]]]
      [%inl [[4 0 1] 5] [2 [0 1] [1 [2 [0 3] [0 2]]]]]
      [%s7n [[4 0 1] 5] [7 [7 [0 1] [2 [0 3] [0 2]]] [4 [0 1]]]]
      [%s7t [[4 0 1] 5] [[0 1] [7 [0 1] [2 [0 3] [0 2]]]]]
      [%s7f [0 [[4 0 1] 5]] [7 [0 3] [[2 [0 3] [0 2]] [0 1]]]]
      [%s7g [[1 [[4 0 1] 5]] 0] [7 [2 [0 3] [0 2]] [[2 [0 3] [0 2]] [0 1]]]]
      [%gat [[[0 1] 5 0] 7] [8 [9 2 [0 2]] [9 2 [10 [6 [0 7]] [0 2]]]]]
      [%lim [0 [[4 0 1] 5]] [8 [0 3] [[2 [0 2] [0 6]] [0 3]]]]
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
