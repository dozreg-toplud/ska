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
      !=((ream '(add 1 2)'))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n), a [a 5]))) (f 40 (add 1 1))))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) [a .*(a a)] $(n (dec n), a [a 5]))) (f (add 20 20) (add 1 1))))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n), a [5 a]))) [(f 40 (add 1 1)) (f 3 4)]))
      [7 [1 [[[2 [6 [5 [1 0] [4 [1 0]]] [9 5 0 1] [1 [1 7]]] [1 [2 [0 1] [0 1]]]] [8 [9 4 0 1] [9 5 0 3]]] 0]] [9 4 0 1]]
      !=(=/(f |=(a=* .*(a a)) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=(a=* [a .*(a a)]) [(f (add 2 3)) (f 5) (f 7)]))
      !=(=/(f |=(a=* [.*(a a) a 7]) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=([a=* b=*] [b .*(a a)]) [(f (add 2 3) 4) (f 5 4) (f 5 (add 1 1))]))
      !=(=/(f |=(a=* ?:(=(a 5) 1 .*(a a))) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=(a=* .*(a a)) [(f (add 2 3)) (f 5) (f [1 2])]))
      !=(=/(g |=(a=* .*(a a)) =/(f |=(a=* [(g a) (g 6)]) [(f (add 2 3)) (f 5)])))
  ==
::  [entries callee-edges missing-callees root-in]
=/  closed
  |=  [g=callgraph root=identity]
  ^-  [@ud @ud @ud ?]
  =/  r=[@ud @ud @ud]
    %-  ~(rep by g)
    |=  [[id=identity d=datum] n=@ud e=@ud m=@ud]
    %-  ~(rep in callees.d)
    |=  [c=callee-entry n=_+(n) e=_e m=_m]
    [n +(e) ?:((~(has by g) id.c) m +(m))]
  [-.r +<.r +>.r (~(has by g) root)]
=|  lon=long-ska
=/  n=@ud  0
=/  tot=[@ud @ud @ud @ud]  [0 0 0 0]
|-  ^-  *
?~  fols  tot
=/  f=^  ?>(?=(^ i.fols) i.fols)
=/  root-identity=identity  [&+lib f]
=/  gr  (mule |.((ska-callgraph root-identity memo.lon [root core batt arms ~]:jets.lon)))
?:  ?=(%| -.gr)  ~&  [%crash-graph n]  $(fols t.fols, n +(n))
=/  c  (closed -.p.gr root-identity)
~&  [n entries=-.c edges=+<.c missing=+>-.c root=+>+.c]
=/  r  (mule |.((ska-poke [&+lib f] lon ~)))
?:  ?=(%| -.r)  ~&  [%crash n]  $(fols t.fols, n +(n))
=.  lon  +.p.r
$(fols t.fols, n +(n), tot [+(-.tot) (add +<.tot -.c) (add +>-.tot +<.c) (add +>+.tot +>-.c)])
