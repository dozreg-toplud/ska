::  The flags [pure total] of every code entry after each of 10 %full pokes
::  (track P, README Gaps 23, P1): per poke, the number of entries and the
::  sorted list of [pure total] over all entries, and per entry of an SCC of
::  more than one bell, the flags with the SCC's size.
::
=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  even=*  [6 [5 [1 0] 0 6] [1 0] 6 [5 [1 1] 0 6] [1 1] 9 2 10 [6 8 [9 2 10 [6 0 14] 0 7] 9 2 0 1] 0 1]
=/  pairs=(list [* *])
  :~  [0 [4 0 1]]
      [[0 [fid [fw fm2]]] [0 0]]
      [5 [0 1]]
      [7 dec]
      [[0 [fid [fw fm2]]] fid]
      [9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [3 [11 1.886.217.588 [1 0]]]
      [4 [11 [1.886.217.588 1 1] 0 1]]
      [[0 [fid [fw fm2]]] [2 [0 1] 1 fid]]
      [[0 [fw fm2]] [2 [0 1] 0 2]]
  ==
=|  n=@ud
|-
?~  pairs  0
=^  p  ..poke  (poke [%full i.pairs])
=/  ent=(list [bell code-entry])  ~(tap by code.long-ska.state)
=/  fl=(list [? ?])  (sort (turn ent |=([* e=code-entry] [pure.e total.e])) aor)
=/  big=(list [@ud ? ?])
  %+  murn  ent
  |=  [b=bell e=code-entry]
  =/  s=(set bell)  -:(scc-of b calls.long-ska.state sccs.cache.state)
  ?:  (lte ~(wyt in s) 1)  ~
  `[~(wyt in s) pure.e total.e]
~&  [%poke n ?=(^ p) %entries (lent ent) %flags fl %multi big]
$(pairs t.pairs, n +(n))
