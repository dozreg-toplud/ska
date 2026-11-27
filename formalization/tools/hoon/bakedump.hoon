:: Baking in the final pass of +compile-scc-in (README Gaps 9, MAP of 2026-11-27,
:: lemmas/Ska/BakeNeed.lean, lemmas/Ska/BakeNeedCheck.lean).
:: Part A: for each [cape data formula] of call-free code, the one-bell final pass
:: as `member` runs it on the bell [[cape data] formula]: +inlined of the poke's
:: root (the nomm does not depend on the bake: +know does not fold under bake=~),
:: +run in %run mode on [%done ~], +collapse-shape with the cape, +bake-need of
:: ned-final and the sock, then `finish`: +coerce-lazy, +soft-done, +add-ops of the
:: baked %imm ops, +to-straight.  Printed as raw nouns:
::   [%bk nam [less nomm ord ned-final bak bake-need-ord need-to-ordered:ned.bak straight]]
:: Part B: real %full pokes; for every entry of nary.cache, the same final pass on
:: its own bell (less.b is the bell's), and whether its need is the bake's.
=/  cases=(list [nam=@tas cap=cape dat=* fol=*])
  :~  [%h01 [& |] [[0 1] 0] [[0 2] [4 [0 3]]]]
      [%h02 [& |] [7 0] [[0 2] [0 3]]]
      [%h03 [& |] [7 0] [4 [0 2]]]
      [%h04 [& |] [[1 2] 0] [[0 2] [0 3]]]
      [%h05 [& |] [[1 2] 0] [[0 4] [0 3]]]
      [%h06 [[& |] |] [[[1 2] 0] 0] [[0 4] [0 5] [0 3]]]
      [%t01 [| &] [0 5] [[4 [0 2]] [0 3]]]
      [%t02 [| &] [0 [5 6]] [[0 2] [0 6] [0 7]]]
      [%t03 [| [| &]] [0 0 9] [[0 2] [0 6] [0 7]]]
      [%m01 [| [& |]] [0 7 0] [[0 2] [0 6] [0 7]]]
      [%m02 [[| &] |] [[0 3] 0] [[0 4] [0 5] [0 3]]]
      [%m03 [| [& |]] [0 [1 2] 0] [[0 2] [0 12] [0 13] [0 7]]]
      [%w01 & [1 2] [[0 2] [0 3]]]
      [%w02 & [[1 2] 3] [[0 4] [0 3]]]
      [%w03 & 5 [4 [0 1]]]
      [%b01 [& |] [[1 2] 0] [0 1]]
      [%b02 [& |] [[1 2] 0] [[0 1] [0 2]]]
      [%b03 [& |] [[1 2] 0] [[0 1] [0 4]]]
      [%b04 [| &] [0 7] [[0 1] [0 3] [0 2]]]
      [%b05 [[& |] &] [[1 0] 3] [[0 1] [0 4] [0 5]]]
      [%a01 [& |] [5 0] [[0 4] [0 3]]]
      [%a02 [& |] [5 0] [[0 2] [0 3]]]
      [%s01 [& |] [0 0] [6 [0 2] [0 6] [0 7]]]
      [%s02 [& |] [1 0] [6 [0 2] [0 6] [0 7]]]
      [%s03 [& |] [0 0] [6 [5 [0 2] [1 0]] [0 3] [1 1]]]
      [%s04 [| &] [0 0] [6 [0 3] [0 2] [4 [0 2]]]]
      [%s05 [[& |] |] [[0 0] 0] [6 [0 4] [0 5] [0 3]]]
      [%s06 [& |] [[0 9] 0] [6 [3 [0 2]] [0 5] [0 3]]]
      [%e01 [& |] [7 0] [7 [0 2] [4 [0 1]]]]
      [%e02 [& |] [7 0] [8 [0 2] [[0 2] [0 7]]]]
      [%e03 [| &] [0 8] [10 [2 [0 3]] [0 1]]]
      [%e04 [& |] [[5 6] 0] [3 [0 2]]]
      [%e05 [& |] [[5 6] 0] [[3 [0 2]] [0 5]]]
      [%e06 [& &] [4 5] [5 [0 2] [0 3]]]
  ==
=/  res
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
  =/  less=sock  [cap.i.cases dat.i.cases]
  =^  nex  gen  (~(run cmp gen) | nom [%done ~] ~ ~)
  =/  ord  (shape-collapse laz.nex cap.i.cases)
  =^  [ned-final=need laz=need-lazy o=@uwoo]  gen
    (~(collapse-shape cmp gen) nex cap.i.cases)
  =/  bak=baked  (bake-need ned-final less)
  =/  bno  (bake-need-ord ord less)
  =.  gen  (~(coerce-lazy cmp gen) ned-final o laz cap.i.cases)
  =.  gen  ~(soft-done cmp gen)
  =.  gen  (~(add-ops cmp gen) o (turn imm.bak |=([r=@uvre v=*] [%imm v r])))
  =/  str  (~(to-straight cmp gen) [%next [[ned.bak ~] ~ ~] ~ o])
  ~&  [%bk nam.i.cases `*`[less nom ord ned-final bak bno (need-to-ordered ned.bak) str]]
  ~&  [%lessf nam.i.cases `*`less.func]
  $(cases t.cases)
::  Part B
=/  pokes=(list [nam=@tas sub=* fol=^])
  :~  [%p01 [[4 [0 6]] 5 0] [9 2 [0 1]]]
      [%p02 [[[0 6] [4 [0 6]]] 5 0] [9 2 [0 1]]]
      [%p03 [[[0 6] [0 2]] 5 0] [9 2 [0 1]]]
      [%p04 [[0 2] 5] [[0 2] [2 [0 3] [0 2]]]]
      [%p05 [[[4 [0 6]] [0 7]] 0 9] [[9 2 [10 [6 [1 41]] [0 1]]] [9 2 [10 [6 [1 42]] [0 1]]]]]
      [%p06 [[[0 6] [0 13]] 0 [3 4]] [8 [1 7] [9 2 [10 [6 [0 2]] [0 3]]]]]
      [%p07 [[6 [5 [0 6] [0 7]] [0 6] [9 2 [10 [6 [4 [0 6]]] [0 1]]]] 0 0] [9 2 [10 [7 [1 7]] [10 [6 [1 0]] [0 1]]]]]
      [%p08 [[6 [5 [0 6] [0 14]] [0 15] [9 2 [10 [6 [4 [0 6]]] [0 1]]]] 0 0] [9 2 [10 [7 [1 [5 9]]] [10 [6 [1 0]] [0 1]]]]]
      [%p09 [[6 [5 [0 6] [1 3]] [0 7] [9 2 [10 [6 [4 [0 6]]] [0 1]]]] 0 0] [9 2 [10 [7 [1 [1 2]]] [10 [6 [1 0]] [0 1]]]]]
      [%p10 [[6 [5 [0 6] [0 14]] [[0 15] [0 6]] [9 2 [10 [6 [4 [0 6]]] [0 1]]]] 0 0] [9 2 [10 [7 [1 [4 [6 7]]]] [10 [6 [1 0]] [0 1]]]]]
      [%p11 [[6 [5 [0 6] [0 14]] [0 15] [9 2 [10 [6 [4 [0 6]]] [0 1]]]] 0 0] [9 2 [10 [14 [1 3]] [10 [6 [1 0]] [0 1]]]]]
  ==
|-  ^-  @
?~  pokes  res
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=/  pr  (poke %full sub.i.pokes fol.i.pokes)
=/  st  state:+.pr
=/  lon  [code jets calls]:long-ska.st
=/  ents  ~(tap by nary.cache.st)
=/  out
  |-  ^-  @
  ?~  ents  0
  =/  b=bell  p.i.ents
  ?>  ?=(^ less.b)
  =/  cac  cache.st
  =^  scc=(set bell)  sccs.cac  (scc-of b calls.long-ska.st sccs.cac)
  =/  cmp  (comp scc lon jets-hot.st ~ ~ b)
  =^  nom=nomm  cac  (inlined b lon jets-hot.st cac)
  =|  gen=line-short
  =.  cache.gen  cac
  =.  mode.gen  %run
  =^  nex  gen  (~(run cmp gen) | nom [%done ~] ~ ~)
  =^  [ned-final=need laz=need-lazy o=@uwoo]  gen
    (~(collapse-shape cmp gen) nex cape.less.b)
  =/  bak=baked  (bake-need ned-final less.b)
  ~&  [%nb nam.i.pokes `*`[less.b ned-final bak (need-to-ordered ned.bak) need.q.i.ents] =((need-to-ordered ned.bak) need.q.i.ents) scc=~(wyt in scc)]
  $(ents t.ents)
$(pokes t.pokes)
