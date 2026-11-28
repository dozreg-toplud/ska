::  Track K (README Gaps 19 (g), 2026-11-28): a direct callee with a ring.
::  The core [[ma mb] 1 2 3 4 5 6 0] is registered by %fast (/mm) BEFORE the
::  first %full, so that +ska-cole-update gives its arms rings at that %full.
::  The root [9 4 0 1] calls the arm ma (axis 4) directly; ma and mb call
::  each other.  Then a %jets that makes both rings hot, and the same %full
::  again.  After each poke: the rings of call.cole (formula and ring),
::  whether each ringed bell has a nary.cache entry (compiled), jets-hot,
::  and for a %full the ops of every block of the root's straight-out
::  (%cal/%jmp: no ring, %caf/%csf/%jmf/%jsf: through the ring).
::
=/  ma=*  [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  tmm=sock  [& [[ma mb] [1 2 3 4 5 6 0]]]
=/  cmds=(list $%([%f s=* f=*] [%a r=? p=(list [path sock])] [%j k=@]))
  :~  [%a | ~[[/mm tmm]]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 5 [0 1]]]
      [%j 1]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f [[ma mb] [9 8 7 0]] [9 4 [0 1]]]
  ==
=/  ops
  |=  o=*
  ^-  (list *)
  ::  the tags of the pole ops and of the termin of every blob-out
  ?@  o  ~
  =/  bs=(list [k=* v=*])  ~(tap by ;;((map * *) +>.o))
  %+  turn  bs
  |=  [k=* v=*]
  =/  bo=*  v
  ?@  bo  [k ~]
  :+  k
    ?@  +<.bo  ~
    (turn ;;((list *) +<.bo) |=(p=* ?@(p p -.p)))
  =/  t=*  +>.bo
  ?@(t t -.t)
=|  n=@ud
|-
?~  cmds  0
=/  c  i.cmds
=/  ovo=*
  ?-    -.c
      %f  [%full s.c ;;(^ f.c)]
      %a  [%fast r.c p.c]
      %j
    =/  rs=(list ring)  ~(tap in (silt (turn ~(tap by call.cole.jets.long-ska.state) tail)))
    =/  nd=need-ordered  [%this ~]
    [%jets (turn rs |=(r=ring [r nd]))]
  ==
=^  p  ..poke  (poke ovo)
=/  lon=long-ska  long-ska.state
=/  ca  cache.state
=/  rin=(list [* ring ?])
  %+  turn  ~(tap by call.cole.jets.lon)
  |=  [b=bell r=ring]
  [fol.b r (~(has by nary.ca) b)]
~&  :*  %rc  n  -.c  %cole  rin  %hot  ~(tap in ~(key by jets-hot.state))
        %nary  ~(wyt by nary.ca)
    ==
~&  ?.  ?=([%ir *] p)  [%rc-prod n ?@(p p -.p)]
    =/  q  ;;([%ir func=bell out=* new=*] p)
    [%rc-ops n fol.func.q (ops out.q)]
$(cmds t.cmds, n +(n))
