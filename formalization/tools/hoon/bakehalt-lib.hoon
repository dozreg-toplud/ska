::  BakeEnds step 1 (track Q, README Gaps 31): %full pokes (+ska-poke) of library
::  calls in one state, the library as a known subject (the formulas of
::  passmeasure-lib.hoon).  Run against the copy of tools/gen/bakehalt_lib.py:
::  RUNHOON_LIB=OUT.hoon runhoon.sh bakehalt-lib.hoon 3000.  Prints per poke
::  the [%bh-end ..] of the copy and [%bh-poke n variants maxvars] after it.
=/  lib  .
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
=|  n=@ud
|-  ^-  @
?~  fols  ~&  %bh-done  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[& lib] f] long-ska.state ~(key by jets-hot.state))
=/  mv=@ud  (roll (turn ~(val by vars.long-ska.state) |=(s=(set bell) ~(wyt in s))) max)
~&  [%bh-poke n variants+~(wyt by code.long-ska.state) maxvars+mv]
$(fols t.fols, n +(n))
