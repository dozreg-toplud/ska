::  The largest SCC of the identity-level call graph of the ride poke, on the
::  spotted hoon.hoon (hoot): a DFS walk from its entry point that visits every
::  member once. One line per tree edge: depth, callsite spot, callee area.
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
::  singletons that call themselves, versus trivial components
::
=/  selfs=(set identity)
  %-  ~(rep by ig)
  |=  [[k=identity v=(set identity)] acc=(set identity)]
  ?.((~(has in v) k) acc (~(put in acc) k))
=/  self-single=@
  %+  roll  (tarjan ig)
  |=  [s=(set identity) n=@]
  ?.  =(1 ~(wyt in s))  n
  ?~  s  n
  ?:((~(has in selfs) n.s) +(n) n)
=/  big=(set identity)
  %+  roll  (tarjan ig)
  |=  [s=(set identity) acc=(set identity)]
  ?:((gth ~(wyt in s) ~(wyt in acc)) s acc)
::  entry: the first member reached from the root, breadth first
::
=/  entry=identity
  =/  q=(list identity)  ~[root]
  =|  seen=(set identity)
  |-  ^-  identity
  ?~  q  ~|(%no-entry !!)
  ?:  (~(has in big) i.q)  i.q
  ?:  (~(has in seen) i.q)  $(q t.q)
  =.  seen  (~(put in seen) i.q)
  ?~  d=(~(get by g) i.q)  $(q t.q)
  $(q (weld t.q (turn ~(tap in callees.u.d) |=(callee-entry id))))
::
=/  show-spot
  |=  s=(unit spot)
  ^-  tape
  ?~  s  "?"
  ;:  weld
    (scow %ud p.p.q.u.s)  ":"  (scow %ud q.p.q.u.s)  "-"
    (scow %ud p.q.q.u.s)  ":"  (scow %ud q.q.q.u.s)
  ==
::
=/  area  |=(id=identity (show-spot area:(~(got by g) id)))
=|  seen=(set identity)
=|  out=(list @t)
=/  res=[out=(list @t) seen=(set identity)]
  =/  depth  0
  |-  ^-  [out=(list @t) seen=(set identity)]
  =.  seen  (~(put in seen) entry)
  =/  cs=(list callee-entry)  ~(tap in callees:(~(got by g) entry))
  |-  ^-  [(list @t) (set identity)]
  ?~  cs  [out seen]
  ?.  &((~(has in big) id.i.cs) !(~(has in seen) id.i.cs))  $(cs t.cs)
  =.  out
    :_  out
    %-  crip
    ;:  weld
      (reap depth ' ')  (show-spot seat.i.cs)  " -> "  (area id.i.cs)
    ==
  =/  r  ^$(entry id.i.cs, depth +(depth))
  $(cs t.cs, out out.r, seen seen.r)
::
:-  %noun
:-  (crip "self-calling {(scow %ud ~(wyt in selfs))} self-single {(scow %ud self-single)} entry {(area entry)} of {(scow %ud ~(wyt in big))} visited {(scow %ud ~(wyt in seen.res))}")
(flop out.res)
