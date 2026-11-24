:: The code of +comp before +optimize (the raw blocks), for a subject sock that knows
:: nothing, as thread-a.hoon compiles it; nul says whether some jump passes ~.
:: %c: the smallest case seen whose join is passed ~ (+sect threading, see lemmas/Ska/ExecPath.lean);
:: %h: a proxy of +collapse-lazy-atom, read by a %mov only.
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%c [1 0 0 5] [7 [6 [0 2] [1 0] [6 [0 6] [0 7] [0 1]]] [6 [0 2] [0 3] [0 1]]]]
      [%h [0 5] [7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]]
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
