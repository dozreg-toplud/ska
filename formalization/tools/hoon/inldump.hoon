::  +inlined against the model `inlinedM` (track G, lemmas/Glue/Inline.lean,
::  LEDGER 2.e): 20 pokes in a row on one state.  %k cases are real %full
::  pokes (known subject); %u cases run the %full branch by hand with an
::  unknown subject [| ~] (+ska-poke, +scc-of, +compiled-mono, as %full does
::  after +validate-ovum), so that the calls are not folded away.  At the end,
::  one jam of [inl cod]: inl = the entries [bell nomm] of inl.cache, cod =
::  per bell of code [bell nomm single self] with single = the SCC of the
::  bell (+scc-of on the final state) has one element, self = the bell is
::  in its own calls.  jets-hot stays ~ (printed), so no callee is hot.
::
=/  xk  |=(k=@ ^-(* ?:(=(0 k) [0 1] [4 $(k (dec k))])))
=/  g1=*   [2 [0 1] [1 [4 0 1]]]
=/  gb=*   [[2 [0 1] [1 [4 0 1]]] (xk 50)]
=/  k40=*  [[2 [0 1] [1 [4 0 1]]] (xk 40)]
=/  h=*    [[2 [0 1] [1 k40]] [0 1]]
=/  g2=*   [2 [0 1] [1 g1]]
=/  r=*    [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  g1c=*  [2 [0 3] [1 [4 0 1]]]
=/  g5=*   [5 [0 1] g1]
=/  g6=*   [8 [1 r] [9 2 [0 1]]]
=/  ma=*   [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*   [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  g7=*   [8 [1 [ma mb]] [9 4 [0 1]]]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  cases=(list [nam=@tas k=? sub=* fol=*])
  :~  [%u1 | 0 [2 [0 1] [1 g1]]]
      [%u2 | 0 [2 [0 1] [1 gb]]]
      [%u3 | 0 [2 [0 1] [1 g2]]]
      [%u4 | 0 [2 [0 1] [1 h]]]
      [%u5 | 0 [8 [1 r] [9 2 [0 1]]]]
      [%u6 | 0 [8 [1 [ma mb]] [9 4 [0 1]]]]
      [%u7 | 0 [2 [0 1] [7 [0 1] [1 g1]]]]
      [%u8 | 0 [11 [1.869.440.365 [1 0]] [2 [0 1] [1 g1]]]]
      [%u9 | 0 [8 [1 g1c] [9 2 [0 1]]]]
      [%ua | 0 [6 [3 0 1] [2 [0 1] [1 g1]] [[2 [0 1] [1 g2]] [0 1]]]]
      [%ub | 0 [[2 [0 1] [1 g1]] [2 [0 1] [1 g1]]]]
      [%uc | 0 [2 [0 1] [11 1.953.460.339 [1 g1]]]]
      [%ud | 0 [2 [0 1] [1 g5]]]
      [%ue | 0 [2 [0 1] [1 g6]]]
      [%uf | 0 [2 [0 1] [1 g7]]]
      [%ug | 0 [4 [2 [0 1] [1 h]]]]
      [%k1 & 7 dec]
      [%k2 & [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%k3 & 5 [2 [0 1] [1 g1]]]
      [%k4 & [g1c 3] [9 2 [0 1]]]
  ==
|-  ^-  @
?^  cases
  ?:  k.i.cases
    =^  p  ..poke  (poke [%full sub.i.cases fol.i.cases])
    ~&  [%case nam.i.cases %full ?=(^ p) %inl ~(wyt by inl.cache.state)]
    $(cases t.cases)
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  ~&  [%case nam.i.cases %unk %inl ~(wyt by inl.cache.state)]
  $(cases t.cases)
=/  inl=(list [bell nomm])  ~(tap by inl.cache.state)
=/  cod=(list [bell nomm ? ?])
  %+  turn  ~(tap by code.long-ska.state)
  |=  [b=bell e=code-entry]
  =/  s=(set bell)  -:(scc-of b calls.long-ska.state sccs.cache.state)
  [b nomm.e =(1 ~(wyt in s)) (~(has in (~(gut by calls.long-ska.state) b ~)) b)]
~&  [%sizes inl=(lent inl) code=(lent cod) hot-empty=?=(~ jets-hot.state)]
~&  [%jam `@ux`(jam [inl cod])]
0
