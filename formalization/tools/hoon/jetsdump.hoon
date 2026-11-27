::  The jets noun and jets-hot after each of 8 %full pokes in a row (track P,
::  README Gaps 23, the invariant Good): before the first poke and after each,
::  whether the five jugs of jets.long-ska and call.cole, back.cole and
::  jets-hot are treaps (+apt:by), the size of call.cole, its pairs (bell
::  -> ring), whether the noun of jets is [r1 r2 r3 r4 pend call back], and
::  whether jets-hot is ~.
::
=/  fk=*
  !=
  =>  ~
  =<  a
  ~%  %k  ~  ~
  |%
  ++  a  42
  --
=/  fc=*
  !=
  =>  ~
  =<  b
  ~%  %c  ~  ~
  |%
  ++  a  42
  ++  b  [a 3]
  --
=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  pairs=(list [* *])
  :~  [0 fk]
      [0 [4 0 1]]
      [0 fc]
      [[0 [fid [fw fm2]]] [0 0]]
      [7 dec]
      [0 fk]
      [3 [11 1.886.217.588 [1 0]]]
      [[0 [fw fm2]] [2 [0 1] 0 2]]
  ==
=/  show
  |=  [n=@ud st=_state]
  =/  j  jets.long-ska.st
  =/  raw=*  j
  ~&  :*  %poke  n
          %apt  ~(apt by root.j)  ~(apt by core.j)  ~(apt by batt.j)  ~(apt by arms.j)
          ~(apt by pend.j)  ~(apt by call.cole.j)  ~(apt by back.cole.j)
          %hot-apt  ~(apt by jets-hot.st)  %hot-nil  =(~ jets-hot.st)
          %shape  ?=([* * * * * * *] raw)
          %call-wyt  ~(wyt by call.cole.j)
          %call  ~(tap by call.cole.j)
      ==
  0
=|  n=@ud
=+  (show 0 state)
|-
?~  pairs  0
=^  p  ..poke  (poke [%full i.pairs])
=+  (show +(n) state)
$(pairs t.pairs, n +(n))
