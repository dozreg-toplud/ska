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
  ==
=|  lon=long-ska
=/  n=@ud  0
|-  ^-  @
?~  fols  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=/  r  (mule |.((ska-poke [&+lib f] lon ~)))
?:  ?=(%| -.r)  ~&  [%crash n]  $(fols t.fols, n +(n))
=.  lon  +.p.r
=/  all=(list [c=bell v=bell])
  %-  zing
  %+  turn  ~(tap by vars.lon)
  |=  [c=bell vs=(set bell)]
  (turn ~(tap in vs) |=(v=bell [c v]))
=/  bad  (skip all |=([c=bell v=bell] (huge:so less.c less.v)))
=/  baked  (skip all |=([c=bell v=bell] =(less.c less.v)))
~&  [n variants=(lent all) baked=(lent baked) bad=(lent bad)]
~?  ?=(^ bad)  [%bad-fol fol.c.i.bad]
$(fols t.fols, n +(n))
