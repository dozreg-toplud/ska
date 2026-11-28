::  BakeEnds, the normal-floor fix (track Q, README Gaps 31.7): as
::  bakehalt-same.hoon, on the 21 library calls of bakehalt-lib.hoon (the
::  library as the known subject, one state), each run on the library:
::    RUNHOON_LIB=OUT runhoon.sh bakehalt-same-lib.hoon 3000
::  (the library is the copy, another noun per copy: compare the products,
::  the %same/%differ against .* and the product mugs, not the code mugs)
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
?~  fols  ~&  %bh-same-done  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[& lib] f] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
=/  code=straight-out  (optimize raw)
~&  [%bh-poke n variants=~(wyt by code.long-ska.state)]
=/  blob  (~(got by blocks.code) 0w0)
=/  ref  (mule |.(.*(lib f)))
=/  ir  (mule |.(-:(eval-blob [[[`@`0 `lib] ~ ~] ~] blob code ~ ~)))
=/  irp=*  ?:(?=(%| -.ir) %ir-crashed ?:(?=(%0 -.p.ir) [%0 product.p.ir] [-.p.ir ~]))
=/  refp=*  ?:(?=(%| -.ref) [%2 ~] [%0 p.ref])
~&  [%bh-run n 0 ?:(=(irp refp) %same %differ) ?@(irp irp ?:(?=(%0 -.irp) (mug irp) irp))]
$(fols t.fols, n +(n))
