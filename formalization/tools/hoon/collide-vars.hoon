::  the code bells of H = [2 [0 1] [0 4]] and their variants after each of
::  the two pokes of collide.hoon, and whether the table's entry for each
::  variant of H is the same nomm for both code bells
=/  lib  .
=/  h=^  [2 [0 1] [0 4]]
=/  f1=^  [7 [1 [[[2 [6 [1 0] [[1 [[3 0] 5]] [9 5 0 1]] [1 [[[1 7] 5] 9]]] [1 [2 [0 1] [0 4]]]] [8 [9 4 0 1] [9 5 0 3]]] 0]] [9 4 0 1]]
=/  x=*  =>  lib  !=((dec 40))
=/  f2=^  [7 [[1 [[3 0] 5]] x] [2 [0 1] [1 [2 [0 1] [0 4]]]]]
=/  fols=(list ^)  ~[f1 f2]
=|  lon=long-ska
=/  n=@ud  0
|-  ^-  @
?~  fols  0
=/  r  (mule |.((ska-poke [&+lib i.fols] lon ~)))
?:  ?=(%| -.r)  ~&  [%crash n]  $(fols t.fols, n +(n))
=.  lon  +.p.r
=/  hv=(list [c=bell vs=(list bell)])
  %+  murn  ~(tap by vars.lon)
  |=  [c=bell vs=(set bell)]
  ?.  =(fol.c h)  ~
  `[c ~(tap in vs)]
~&  [%poke n %h-code-bells (lent hv)]
~&  %+  turn  hv
    |=  [c=bell vs=(list bell)]
    :+  less.c
      (turn vs |=(v=bell less.v))
    (turn vs |=(v=bell nomm:(~(got by code.lon) v)))
$(fols t.fols, n +(n))
