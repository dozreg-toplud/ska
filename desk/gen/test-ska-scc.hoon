::  SCC structure of the identity-level call graph after the scow poke
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  n-boot  ~(wyt by graph.final.long-ska)
=/  subject  ..scow:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (scow %ud 5)
::
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=/  g  graph.final.long-ska
=/  ig=jug-id
  %-  ~(rep by g)
  |=  [[k=identity v=datum] acc=jug-id]
  =.  acc  (~(put by acc) k (~(run in callees.v) |=(callee-entry id)))
  acc
=/  sccs=(list (set identity))  (tarjan ig)
=/  sizes=(list @)  (sort (turn sccs |=(s=(set identity) ~(wyt in s))) gth)
=/  fols  ~(wyt in `(set ^)`(~(run in ~(key by g)) |=(id=identity fol.id)))
=/  bells  ~(wyt by code.long-ska)
:-  %noun
:*  boot-ids+n-boot
    ids+~(wyt by g)
    fols+fols
    bells+bells
    sccs+(lent sccs)
    big-sccs+(scag 12 sizes)
    in-nontrivial+(roll (skim sizes |=(a=@ (gth a 1))) add)
==
