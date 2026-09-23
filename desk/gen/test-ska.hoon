::  Benchmark of call graph analysis alone: the three +ska-poke calls of
::  +test-gen-ir, each timed with %bout, plus graph sizes.
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
=|  =long-ska
=.  long-ska
  ~>  %bout.[0 'poke boot']
  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..scow:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (scow %ud 5)
::
=^  func=bell  long-ska
  ~>  %bout.[0 'poke scow']
  (ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
::
=/  formula=^
  =>  subject
  ;;  ^
  !=
  %.  ~[1]
  |=  l=(list @)
  ^-  (list @)
  ?~  l  ~
  [(dec i.l) $(l t.l)]
::
=^  func=bell  long-ska
  ~>  %bout.[0 'poke dec']
  (ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
:-  %noun
:*  graph+~(wyt by graph.final.long-ska)
    code+~(wyt by code.long-ska)
    memo+(roll (turn ~(val by memo.final.long-ska) |=(m=(map sock *) ~(wyt by m))) add)
==
