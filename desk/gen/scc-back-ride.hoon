::  For chosen members of the largest SCC of the ride call graph (by the start
::  line of their area in hoot.hoon), the shortest path within the SCC back to
::  a member whose area starts inside +mint:ut.
::
/+  *nock-compilation
/+  hoot
/+  hoot-fol
::
:-  %say  |=  *
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-fol] long-ska)
=/  subject  ..ride:hoot
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=/  g  graph.final.long-ska
=/  root=identity  [&+subject formula]
=/  ig=jug-id
  %-  ~(rep by g)
  |=  [[k=identity v=datum] acc=jug-id]
  (~(put by acc) k (~(run in callees.v) |=(callee-entry id)))
=/  big=(set identity)
  %+  roll  (tarjan ig)
  |=  [s=(set identity) acc=(set identity)]
  ?:((gth ~(wyt in s) ~(wyt in acc)) s acc)
=/  show-spot
  |=  s=(unit spot)
  ^-  tape
  ?~  s  "?"
  ;:  weld
    (scow %ud p.p.q.u.s)  ":"  (scow %ud q.p.q.u.s)  "-"
    (scow %ud p.q.q.u.s)  ":"  (scow %ud q.q.q.u.s)
  ==
::
=/  line
  |=  id=identity
  ^-  @
  =/  d=datum  (~(got by g) id)
  ?~  area.d  0
  p.p.q.u.area.d
=/  is-mint  |=(id=identity &((gte (line id) 9.974) (lte (line id) 10.132)))
=/  reps=(list @)  ~[9.075 9.827 11.075 10.877 731 8.836 9.235 9.280 9.540 9.782 9.874 11.412 10.322 561 10.403 9.600 9.676 9.549]
:-  %noun
%-  zing
%+  turn  reps
|=  l=@
^-  (list @t)
=/  start=(unit identity)
  (set-first-match big |=(id=identity ?:(=(l (line id)) `id ~)))
?~  start  ~[(crip "{(scow %ud l)}: no member")]
::  BFS within big, parents recorded, stop at the first mint identity
::
=/  q=(list identity)  ~[u.start]
=/  par=(map identity [seat=(unit spot) from=identity])  ~
=/  seen=(set identity)  [u.start ~ ~]
=^  goal=(unit identity)  par
  |-  ^-  [(unit identity) _par]
  ?~  q  [~ par]
  ?:  &(!=(i.q u.start) (is-mint i.q))  [`i.q par]
  =/  cs=(list callee-entry)  ~(tap in callees:(~(got by g) i.q))
  =^  new=(list identity)  par
    %+  roll  cs
    |=  [c=callee-entry acc=(list identity) =_par]
    ?.  &((~(has in big) id.c) !(~(has in seen) id.c) !(~(has by par) id.c))  [acc par]
    [[id.c acc] (~(put by par) id.c [seat.c i.q])]
  =.  seen  (~(gas in seen) new)
  $(q (weld t.q (flop new)))
?~  goal  ~[(crip "{(scow %ud l)}: no path back")]
::  unwind
::
=/  steps=(list @t)  ~
=/  cur  u.goal
|-  ^-  (list @t)
?:  =(cur u.start)  [(crip "from {(show-spot area:(~(got by g) u.start))}") steps]
=/  p  (~(got by par) cur)
%=  $
  cur    from.p
  steps  [(crip " {(show-spot seat.p)} -> {(show-spot area:(~(got by g) cur))}") steps]
==
