::  Identical output of a candidate fix of the pass loop (track F, README Gaps 16, passfix.py):
::  the 21 %full pokes of sprestdump.hoon in a row (fresh state), then the 21 library calls of
::  passmeasure-lib.hoon (+ska-callgraph, empty memo), with the core of hoon.hoon as the known subject
::  (not the library: a patched library is another noun).  Prints
::  [%ts n mug-of-product mug-of-state] after each poke and [%tl n mug-of-graph mug-of-regs size]
::  after each call.  Run it with RUNHOON_LIB=LIB (a copy of passfix.py) and compare the lines.
=/  lib  ..ream
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
=/  even=*  [6 [5 [1 0] 0 6] [1 0] 6 [5 [1 1] 0 6] [1 1] 9 2 10 [6 8 [9 2 10 [6 0 14] 0 7] 9 2 0 1] 0 1]
=/  ma=*  [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  mc=*  [6 [3 [0 3]] [8 [9 5 [10 [3 [0 7]] [0 1]]] [9 4 [10 [3 [0 15]] [0 3]]]] [1 2]]
=/  pairs=(list [* *])
  :~  [0 fk]
      [0 [4 0 1]]
      [0 fc]
      [[0 [fid [fw fm2]]] [0 0]]
      [5 [0 1]]
      [7 dec]
      [0 fk]
      [[0 [fid [fw fm2]]] fid]
      [9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [3 [11 1.886.217.588 [1 0]]]
      [4 [11 [1.886.217.588 1 1] 0 1]]
      [[0 [fid [fw fm2]]] [2 [0 1] 1 fid]]
      [[0 [fw fm2]] [2 [0 1] 0 2]]
      [[even [5 0]] [9 2 0 1]]
      [0 [4 0 1]]
      [7 dec]
      [[0 [fid [fw fm2]]] fid]
      [0 fc]
      [[[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [[[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [[[ma mb] [9 8 7 0]] [9 5 [0 1]]]
  ==
=/  n=@ud  0
=^  z=@  ..poke
  |-  ^-  [@ _..poke]
  ?~  pairs  [0 ..poke]
  =/  fol=^  ;;(^ +.i.pairs)
  =^  p  ..poke  (poke [%full -.i.pairs fol])
  ~&  [%ts n (mug p) (mug state)]
  $(pairs t.pairs, n +(n))
=/  fols=(list *)
  =>  lib
  :~  !=((add 2 3))
      !=((mul 12 12))
      !=((roll (gulf 1 10) add))
      !=((sort ~[3 1 2 9 4] lth))
      !=((~(get by (~(put by *(map @ @)) 1 2)) 1))
      !=((cue (jam [1 2 3])))
      !=((scow %ud 12.345))
      !=((need (rush '12+3' ;~(plug dem ;~(pfix lus dem)))))
      !=((flop (turn (gulf 1 5) |=(a=@ (mul a a)))))
      !=((turn (gulf 1 3) |=(a=@ (add a 1))))
      !=((~(put in *(set @)) 7))
      !=((crip (trip 'abc')))
      !=((~(gas by *(map @ @)) ~[[1 2] [3 4]]))
      !=((rash '0x1f' hex))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n), a [a 5]))) (f 40 (add 1 1))))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) [a .*(a a)] $(n (dec n), a [a 5]))) (f (add 20 20) (add 1 1))))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n), a [5 a]))) [(f 40 (add 1 1)) (f 3 4)]))
      !=(=/(f |=([a=* b=*] ?:(=(0 a) b $(a b, b a))) (f 1 2)))
      !=(=/(f |=([a=* b=* c=*] ?@(a .*(b c) $(a b, b c, c a))) (f [1 2] 3 [0 1])))
      !=(~(tap by (~(gas by *(map @ @)) ~[[1 2] [3 4] [5 6]])))
      !=((ream '(add 1 2)'))
  ==
=.  n  0
|-  ^-  @
?~  fols  ~&  %ts-done  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=/  res  (ska-callgraph [&+lib f] ~ [~ ~ ~ ~ ~])
~&  [%tl n (mug -.res) (mug +.res) ~(wyt by -.res)]
$(fols t.fols, n +(n))
