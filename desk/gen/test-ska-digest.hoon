::  Digest of the analysis output of the three pokes of +test-gen-ir, for
::  comparing analysis implementations.
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..scow:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (scow %ud 5)
::
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
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
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
=/  g  graph.final.long-ska
:-  %noun
:*  ids+~(wyt by g)
    bells+~(wyt by code.long-ska)
    bell-set+`@ux`(mug (sort (turn ~(tap by code.long-ska) |=([b=bell *] (mug b))) lth))
    code+`@ux`(mug code.long-ska)
    graph-keys+`@ux`(mug (sort (turn ~(tap by g) |=([i=identity *] (mug i))) lth))
    graph+`@ux`(mug g)
    jets+`@ux`(mug [root core batt cole]:jets.long-ska)
    root+`@ux`(mug func)
==
