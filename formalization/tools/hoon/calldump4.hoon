:: The raw blocks (before +optimize) of the whole-subject version for a subject sock that
:: knows nothing, of the cases of the induction over NC (README Gaps 12.22,
:: lemmas/Ska/CompNC.lean): a cons under a goal with entries (%lim, %bc1 with +split's con at
:: the bond block, %bc2 with +copy's move there), the examples of the session (%c8t, %i4, %i3,
:: %h4c), the leaves and %3, %4, %5 as heads under the bond goal (%h1, %h3, %h3c, %h5), %4 under a
:: goal with a bond and a sure part `this d` (%s4t: the bond block reads the goal's d), and %10 at
:: a bond whose need is `this t` (%s10).
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%lim [0 [[4 0 1] 5]] [8 [0 3] [[2 [0 2] [0 6]] [0 3]]]]
      [%bc1 [[[4 0 1] 5] 7] [7 [[0 2] [0 3]] [[2 [0 2] [0 6]] [0 1]]]]
      [%bc2 [[[4 0 1] 5] 7] [7 [[0 1] [0 1]] [[2 [0 2] [0 6]] [[0 2] [0 3]]]]]
      [%c8t [0 [[4 0 1] 5]] [[0 1] [8 [0 3] [2 [0 2] [0 6]]]]]
      [%i4 [[4 0 1] 5] [4 [2 [0 3] [0 2]]]]
      [%i3 [[4 0 1] 5] [3 [2 [0 3] [0 2]]]]
      [%h4c [[4 0 1] 5] [[4 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]]
      [%h1 [[4 0 1] 5] [[1 7] [2 [0 3] [0 2]]]]
      [%h3 [[4 0 1] 5] [[3 [0 2]] [2 [0 3] [0 2]]]]
      [%h3c [[4 0 1] 5] [[3 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]]
      [%h5 [[4 0 1] 5] [[5 [0 2] [0 3]] [2 [0 3] [0 2]]]]
      [%s4t [[[0 1] 5] 6] [7 [4 [0 3]] [[2 [0 1] [0 1]] [0 1]]]]
      [%s10 [[[4 0 1] 5] 7] [7 [10 [2 [0 3]] [0 1]] [[2 [0 2] [0 6]] [0 1]]]]
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
$(cases t.cases)
