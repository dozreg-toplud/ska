::  The flags of code against the model of lemmas/Ska/PokeFlags.lean (track P,
::  README Gaps 23, sixth session).  Phase 0: the 32 mixed pokes of
::  invdump2.hoon; phase 1 (after [%r ~], a fresh state): the 21 %full pokes
::  of sprestdump.hoon.  After each poke:
::  [%nb ph i bell nomm]  for each key of code not seen before in the phase,
::                        its index i, bell and nomm (entries never change);
::  [%pk ph n sccs flags] the SCCs of the whole table, callees first
::                        ((flop (tarjan g)), g the calls restricted to keys,
::                        as +ska-poke builds it), each as the indices of its
::                        members in ~(rep in scc) order (preorder), and
::                        [i pure total] for every key.
::  Read by tools/gen/flagscheck.py (lemmas/Ska/PokeFlagsCheck.lean).
::
=/  fk=*
  !=
  =>  ~
  =<  a
  ~%  %k  ~  ~
  |%
  ++  a  42
  --
=/  fc=*
  !=
  =>  ~
  =<  b
  ~%  %c  ~  ~
  |%
  ++  a  42
  ++  b  [a 3]
  --
=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  even=*  [6 [5 [1 0] 0 6] [1 0] 6 [5 [1 1] 0 6] [1 1] 9 2 10 [6 8 [9 2 10 [6 0 14] 0 7] 9 2 0 1] 0 1]
=/  ma=*  [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  mc=*  [6 [3 [0 3]] [8 [9 5 [10 [3 [0 7]] [0 1]]] [9 4 [10 [3 [0 15]] [0 3]]]] [1 2]]
=/  tmm=sock  [& [[ma mb] [1 2 3 4 5 6 0]]]
=/  tmc=sock  [& [[mc mb] [1 2 3 4 5 6 0]]]
=/  cand=(set ring)  (silt `(list ring)`~[[/mm 4] [/mm 5] [/mc 4] [/mc 5]])
=/  cmds=(list $%([%f s=* f=*] [%d k=@ m=?] [%a r=? p=(list [path sock])] [%j k=@]))
  :~  [%f 0 fk]
      [%f 0 [4 0 1]]
      [%f 0 fc]
      [%f [0 [fid [fw fm2]]] [0 0]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%a | ~[[/mm tmm]]]
      [%j 1]
      [%f 7 dec]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%d 0 &]
      [%d 1 |]
      [%f 0 fc]
      [%j 2]
      [%f [0 [fid [fw fm2]]] fid]
      [%f [even [5 0]] [9 2 0 1]]
      [%a & ~[[/mm tmm]]]
      [%d 2 &]
      [%j 1]
      [%f [[ma mb] [9 8 7 0]] [9 5 [0 1]]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f 9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [%j 0]
      [%d 3 |]
      [%f 3 [11 1.886.217.588 [1 0]]]
      [%a | ~[[/mc tmc]]]
      [%j 3]
      [%f [0 [fw fm2]] [2 [0 1] 0 2]]
      [%d 4 &]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%a & ~]
      [%j 1]
      [%f 0 fc]
  ==
=/  cmds1=(list $%([%f s=* f=*] [%d k=@ m=?] [%a r=? p=(list [path sock])] [%j k=@]))
  :~
      [%f 0 fk]
      [%f 0 [4 0 1]]
      [%f 0 fc]
      [%f [0 [fid [fw fm2]]] [0 0]]
      [%f 5 [0 1]]
      [%f 7 dec]
      [%f 0 fk]
      [%f [0 [fid [fw fm2]]] fid]
      [%f 9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [%f 3 [11 1.886.217.588 [1 0]]]
      [%f 4 [11 [1.886.217.588 1 1] 0 1]]
      [%f [0 [fid [fw fm2]]] [2 [0 1] 1 fid]]
      [%f [0 [fw fm2]] [2 [0 1] 0 2]]
      [%f [even [5 0]] [9 2 0 1]]
      [%f 0 [4 0 1]]
      [%f 7 dec]
      [%f [0 [fid [fw fm2]]] fid]
      [%f 0 fc]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f [[ma mb] [9 8 7 0]] [9 5 [0 1]]]
  ==
=/  sccs-of
  |=  lon=long-ska
  ^-  (list (set bell))
  ?:  =(~ code.lon)  ~
  %-  flop
  %-  tarjan
  ^-  (jug bell bell)
  %-  ~(rep by calls.lon)
  |=  [[b=bell cs=(set bell)] acc=(jug bell bell)]
  (~(put by acc) b (silt (skim ~(tap in cs) |=(c=bell (~(has by code.lon) c)))))
=/  run
  |=  [ph=@ud cmds=(list $%([%f s=* f=*] [%d k=@ m=?] [%a r=? p=(list [path sock])] [%j k=@]))]
  ^-  @
  =|  n=@ud
  =|  idx=(map * @ud)
  |-
  ?~  cmds  0
  =/  c  i.cmds
  =/  ovo=*
    ?-    -.c
        %f  [%full s.c ;;(^ f.c)]
        %a  [%fast r.c p.c]
        %d
      =/  ks=(list bell)  ~(tap in ~(key by code.long-ska.state))
      [%dire (snag (mod k.c (lent ks)) ks) m.c]
    ::
        %j
      =/  l=long-ska  +:(ska-cole-settle long-ska.state (~(uni in cand) ~(key by jets-hot.state)))
      =/  rs=(list ring)  ~(tap in (silt (turn ~(tap by call.cole.jets.l) tail)))
      =/  nd=need-ordered  ?:(=(3 k.c) [[%none ~] %this ~] [%this ~])
      =/  rs2=(list ring)
        ?:  =(0 k.c)  ~
        ?:  &(=(2 k.c) ?=(^ rs))  t.rs
        rs
      [%jets (turn rs2 |=(r=ring [r nd]))]
    ==
  =^  p  ..poke  (poke ovo)
  =/  lon=long-ska  long-ska.state
  =/  ents=(list [bell code-entry])  ~(tap by code.lon)
  =.  idx
    |-  ^+  idx
    ?~  ents  idx
    ?:  (~(has by idx) `*`-.i.ents)  $(ents t.ents)
    =/  i=@ud  ~(wyt by idx)
    ~&  [%nb ph i `*`-.i.ents `*`nomm.+.i.ents]
    $(ents t.ents, idx (~(put by idx) `*`-.i.ents i))
  =/  sc=*
    =/  l=(list (set bell))  (sccs-of lon)
    |-  ^-  *
    ?~  l  0
    :_  $(l t.l)
    ^-  (list @ud)
    ::  the members in ~(rep in scc) order: the preorder (node, left, right)
    ::  of the treap
    =/  t=*  i.l
    |-  ^-  (list @ud)
    ?@  t  ~
    [(~(got by idx) -.t) (weld $(t +<.t) $(t +>.t))]
  =/  fs=*
    =/  l  ents
    |-  ^-  *
    ?~  l  0
    [[(~(got by idx) `*`-.i.l) pure.+.i.l total.+.i.l] $(l t.l)]
  ~&  [%pk ph n `*`sc `*`fs]
  $(cmds t.cmds, n +(n))
=+  (run 0 cmds)
(run 1 cmds1)
