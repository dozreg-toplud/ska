:: A jump that passes a register nothing defines, in raw +comp output (found 2026-11-24 by
:: ssacheck.hoon).  The smallest formula seen: [7 [6 [0 1] [0 0] [1 0]] [6 [0 1] [0 2] [1 0]]].
:: The first %6 is compiled through +fork because the second %6 reads its product; +fork-need
:: gives each kid block a fresh register and a hop that passes it; the yes branch [0 0] goes to
:: +bomb, which discards the goal, so nothing writes the kid-0 register (block 0wa passes 0v7).
:: The edge is dead: 0wo sends 0v4 = 0 to the %bom, so the later %brz on 0v4 in 0wi never takes
:: its zero side.  Raw and optimized code agree with +mock on every subject tried; the first
:: +alias folds the %brz and drops the block.  The IR's convention for "no value on this edge"
:: is an argument ~, so this is an unintended emission, not a miscompile.
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%x 1 [7 [6 [0 1] [0 0] [1 0]] [6 [0 1] [0 2] [1 0]]]]
  ==
=/  hasnul
  |=  bs=(list [@ blob])
  ^-  ?
  ?~  bs  |
  =/  f  fin.+.i.bs
  =/  a=(list (unit @))
    ?+  -.f  ~
      %hop  args.t.f
      %brn  (weld args.z.f args.o.f)
      %brz  (weld args.z.f args.o.f)
      %clq  (weld args.z.f args.o.f)
      %eqq  (weld args.z.f args.o.f)
    ==
  ?:  (lien a |=(u=(unit @) ?=(~ u)))  &
  $(bs t.bs)
|-  ^-  @
?~  cases  0
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
=/  r
  %-  mule  |.
  -:(eval-blob [[[`@`0 `sub.i.cases] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ ~)
=/  bl  (sort ~(tap by blocks.raw) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
~&  :*  nam.i.cases  mock=a
        ?:  ?=(%| -.r)  %interpreter-crashed
        =/  t=tone  p.r
        ?:(?=(%0 -.t) [%0 product.t] ?:(?=(%1 -.t) %1 [%2 (lent trace.t)]))
        nul=(hasnul bl)  n=(lent bl)
    ==
|-
?~  bl  ^$(cases t.cases)
~&  i.bl
$(bl t.bl)
