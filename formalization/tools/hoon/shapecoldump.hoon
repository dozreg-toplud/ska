:: The input and the product of +shape-collapse in the final pass of +compile-scc-in
:: (lemmas/Ska/ShapeCol.lean, README Gaps 9): for each formula and subject sock, the
:: one-bell final pass as `member` runs it (+inlined, then +run in %run mode on
:: [%done ~]), then `laz.nex`, `cape.less`, and +shape-collapse of them.  Printed as
:: raw nouns: `[%sc nam [laz less res]]`, each `(set @)` of the lazy need as the list
:: of its elements in the order of +rep:in (the order +inter1-to-inter2 folds them).
=/  cases=(list [nam=@tas cap=cape dat=* fol=*])
  :~  [%a01 | ~ [6 [0 2] [0 3] [1 0]]]
      [%a02 | ~ [6 [0 2] [0 6] [0 7]]]
      [%a03 | ~ [6 [0 2] [0 6] [0 6]]]
      [%a04 | ~ [6 [0 2] [0 3] [0 3]]]
      [%a05 | ~ [6 [5 [0 2] [0 3]] [0 2] [0 3]]]
      [%a06 | ~ [6 [0 2] [4 [0 6]] [4 [0 7]]]]
      [%a07 | ~ [6 [0 2] [0 1] [0 3]]]
      [%a08 | ~ [6 [0 2] [0 1] [1 0]]]
      [%a09 | ~ [6 [3 [0 2]] [0 4] [0 3]]]
      [%a10 | ~ [6 [0 2] [[0 6] [0 7]] [[0 7] [0 6]]]]
      [%a11 | ~ [6 [0 2] [0 12] [0 13]]]
      [%a12 | ~ [6 [0 2] [0 14] [1 0]]]
      [%n01 | ~ [6 [0 2] [6 [0 6] [0 14] [0 15]] [0 7]]]
      [%n02 | ~ [6 [0 2] [6 [0 6] [0 12] [0 13]] [6 [0 7] [0 14] [0 15]]]]
      [%n03 | ~ [6 [0 2] [6 [0 3] [0 6] [0 7]] [6 [0 3] [0 7] [0 6]]]]
      [%n04 | ~ [6 [0 2] [6 [0 6] [0 1] [0 7]] [0 3]]]
      [%n05 | ~ [6 [6 [0 2] [0 6] [0 7]] [0 12] [0 13]]]
      [%c01 | ~ [[6 [0 2] [0 6] [0 7]] [0 3]]]
      [%c02 | ~ [[0 2] [6 [0 2] [0 6] [0 7]]]]
      [%c03 | ~ [[6 [0 2] [0 6] [0 7]] [6 [0 3] [0 2] [1 0]]]]
      [%c04 | ~ [[6 [0 2] [0 6] [1 0]] [6 [0 2] [1 0] [0 7]]]]
      [%s01 | ~ [7 [0 3] [6 [0 2] [0 6] [0 7]]]]
      [%s02 | ~ [7 [6 [0 2] [0 6] [0 7]] [0 3]]]
      [%s03 | ~ [7 [6 [0 2] [0 6] [0 7]] [4 [0 2]]]]
      [%s04 | ~ [8 [6 [0 2] [1 0] [1 1]] [6 [0 2] [0 6] [0 7]]]]
      [%s05 | ~ [7 [[0 2] [0 3]] [6 [0 2] [0 3] [1 0]]]]
      [%s06 | ~ [7 [6 [0 2] [0 6] [0 7]] [[0 2] [0 3]]]]
      [%m01 | ~ [6 [0 2] [[0 12] [[0 26] [[0 27] [[0 30] [[0 31] [0 28]]]]]] [1 0]]]
      [%m02 | ~ [6 [0 2] [[0 12] [[0 13] [0 14]]] [[0 12] [0 15]]]]
      [%b01 | ~ [6 [0 2] [2 [0 6] [0 7]] [0 3]]]
      [%b02 | ~ [[2 [0 6] [0 7]] [6 [0 2] [0 6] [0 7]]]]
      [%k01 [& |] [0 0] [6 [0 2] [0 6] [0 7]]]
      [%k02 [| [& |]] [0 7 0] [6 [0 2] [0 6] [0 7]]]
      [%k03 [| [| &]] [0 0 0] [6 [0 2] [0 6] [0 14]]]
  ==
|-  ^-  @
?~  cases  0
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[cap.i.cases dat.i.cases] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
=/  lon  [code jets calls]:long-ska.state
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=/  cmp  (comp scc lon jets-hot.state ~ ~ func)
=^  nom=nomm  cache.state  (inlined func lon jets-hot.state cache.state)
=|  gen=line-short
=.  cache.gen  cache.state
=.  mode.gen  %run
=/  nex  -:(~(run cmp gen) | nom [%done ~] ~ ~)
=/  less=cape  cap.i.cases
=/  res  (shape-collapse laz.nex less)
::  the elements of a treap set in the order of +rep:in (node, left, right)
=/  pre
  |=  [t=* acc=*]
  ^-  *
  ?@  t  acc
  ?>  ?=([* * *] t)
  [-.t $(t +<.t, acc $(t +>.t))]
=/  plain
  |=  l=*
  ^-  *
  ?>  ?=([[* *] * *] l)
  =/  fk=*  +<.l
  =/  bd=*  +>.l
  :+  [-<.l (pre ->.l 0)]
    |-  ^-  *
    ?@  fk  0
    ?>  ?=([[[* *] [* *]] *] fk)
    [[[-<-.fk ^$(l -<+.fk)] [->-.fk ^$(l ->+.fk)]] $(fk +.fk)]
  |-  ^-  *
  ?@  bd  0
  ?>  ?=([[* *] *] bd)
  [[-<.bd ^$(l ->.bd)] $(bd +.bd)]
~&  [%sc nam.i.cases `*`[(plain laz.nex) less res]]
~&  [%nomm nam.i.cases nom]
~&  [%res nam.i.cases `*`res `*`less.func scc=~(wyt in scc)]
$(cases t.cases)
