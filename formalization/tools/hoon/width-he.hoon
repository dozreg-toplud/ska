::  case 49 of the generated ck-rnd1 driver alone (track F, README Gaps 16): a pass loop of 62 passes whose
::  stack grows by one member every two passes, each pushed at a subject one level deeper (3 to 33); run with
::  the library of passmeasure-git.py; with he-threshold set to 8, 16, 48 in a copy: 14, 30, 94 passes.
::  the pass-loop measure driver (passmeasure.py)
=/  cases=(list [nam=@tas bus=sock fol=*])
  :~
      [%rnd1 &+[[4 [[9 [2 [10 [[6 [[0 7] [4 [0 6]]]] [0 1]]]]] [2 [[9 [2 [10 [[6 [[0 6] [0 7]]] [0 1]]]]] [0 1]]]]] [[1 0] [1 0]]] [4 [[9 [2 [10 [[6 [[0 7] [4 [0 6]]]] [0 1]]]]] [2 [[9 [2 [10 [[6 [[0 6] [0 7]]] [0 1]]]]] [0 1]]]]]]
  ==
=/  n=@ud  0
|-  ^-  @
?~  cases  ~&  %pm-done  0
~&  [%pm-case n nam.i.cases]
=/  f=^  ?>(?=(^ fol.i.cases) fol.i.cases)
=/  res  (ska-callgraph [bus.i.cases f] ~ [~ ~ ~ ~ ~])
~&  [%pm-graph n ~(wyt by -.res)]
$(cases t.cases, n +(n))
