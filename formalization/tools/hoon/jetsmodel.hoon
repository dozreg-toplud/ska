::  The clauses of PGood2 (track P, README Gaps 23, sixth session) after each
::  poke of a sequence of 28 pokes mixing %full, %fast, %jets and %dire, so
::  that +ska-cole-settle, +hot-stale and +del-bells really delete.  After
::  each poke, whether
::  %ccall  every callee in calls is a key of code              (Closed)
::  %cinfo  every %2 info bell of an entry's nomm is a key of code (Closed)
::  %smap   sure.cache is a treap                              (IsMap sure)
::  %skey   sure.cache and nary.cache have the same keys
::  %imap   inl.cache is a treap                               (IsMap inl)
::  %ikey   every key of inl.cache is a key of code
::  %ival   every entry of inl.cache is +inlined of its bell on the
::          state with inl.cache emptied (a function of the table)
::  %sccs   SccsGood: every sccs entry S of k is a treap set holding k,
::          and every member k' of S has the entry S
::  %nary   NaryClosed: the keys of nary.cache are whole SCCs of sccs
::  %vars   every variant in vars.lon is a key of code with the fol of
::          its code bell (VarsOK without the formula part)
::  %ckey   code, calls, seek have the same keys
::  %mono   every key of mono.cache is a key of code
::  %flag   the flags of every entry equal the replay of the SCC loop
::          over the WHOLE table from [| |] (as sprestdump.hoon)
::  %scck   every key of sccs.cache is a key of code
::  %gone   a bell of the %drop list has no entry in nary, mono, inl,
::          sure after the poke, and a %jets keeps every nary entry it
::          does not drop
::  %sset  (ninth session) every sccs entry of k is the SCC of k: the keys
::          k2 of code with k reaching k2 and k2 reaching k over calls
::          (the height clause SccsIs of PGood5)
::  %ccoh  (ninth session) ColeCoh: call.cole maps c to r iff c is in the
::          back.cole set of r
::  jetsmodel.hoon (twelfth session, track P): this driver with, after every
::  %f, %jmod: the jets after the poke equal the model jetsOfP of
::  lemmas/Compiler/PokeLinkJetsP.lean: root, core, batt, arms of the regs of
::  +ska-callgraph rerun on the old state, pend by +uni-ju with new-cores,
::  then +cole-put over the keys of the new code that the old code lacks (in
::  the order of +rep:in of that set), with +cole-match on the new seek, the
::  regs' core and arms and the hot rings; %nnew: the poke's list is
::  (flop new.regs).
::
::  %bset, %pset, %jpth, %rmap  (thirteenth session, track P): back.cole
::  and pend are maps whose every value is a set (BackSets, PendSets of
::  PGood7); every key of core.jets is a path; on a %f, the regs that
::  +ska-callgraph returns have four maps and paths as the keys of core.
::
::  %cdom  (eleventh session) ColeDom: every key of call.cole is a key of
::          code, and every member of a back.cole set is a key of code
::  and the sizes of code, inl, sure, nary, mono, sccs, call.cole, pend,
::  jets-hot, and for %jets the length of the %drop list.
::  The commands: [%f sub fol] a %full; [%a reset tems] a %fast;
::  [%j k] a %jets whose hot is built from the rings a dry run of
::  +ska-cole-settle finds (k=0: none, k=1: all with [%this ~], k=2: all
::  but the first, k=3: all with [[%none ~] %this ~]); [%d k mono] a %dire
::  on the k-th bell (mod the size) of ~(tap in ~(key by code)).
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
=/  infos
  |=  n=*
  ^-  (list *)
  ?@  n  ~
  ?^  -.n  (weld $(n -.n) $(n +.n))
  ?+  -.n  ~
    %2     =/  inf=*  +>+.n
           =/  rest=(list *)  (weld $(n +<.n) $(n +>-.n))
           ?@  inf  rest
           [+<.inf rest]
    %3     $(n +<.n)
    %4     $(n +<.n)
    %5     (weld $(n +<.n) $(n +>.n))
    %6     :(weld $(n +<.n) $(n +>-.n) $(n +>+.n))
    %7     (weld $(n +<.n) $(n +>.n))
    %10    (weld $(n +<+.n) $(n +>.n))
    %11    ?@  +<.n  $(n +>.n)
           (weld $(n +<+.n) $(n +>.n))
    %12    (weld $(n +<.n) $(n +>.n))
    %mean  (weld $(n +<.n) $(n +>.n))
  ==
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
=/  replay
  |=  lon=long-ska
  ^-  (map bell code-entry)
  =/  tab=(map bell code-entry)
    (~(run by code.lon) |=(e=code-entry e(pure |, total |)))
  ?:  =(~ tab)  tab
  =/  sccs=(list (set bell))
    %-  flop
    %-  tarjan
    ^-  (jug bell bell)
    %-  ~(rep by calls.lon)
    |=  [[b=bell cs=(set bell)] acc=(jug bell bell)]
    (~(put by acc) b (silt (skim ~(tap in cs) |=(c=bell (~(has by code.lon) c)))))
  |-  ^-  (map bell code-entry)
  ?~  sccs  tab
  =/  loc2=(map bell code-entry)
    %-  ~(rep in i.sccs)
    |=  [b=bell acc=_tab]
    =/  [pure=? total=?]  (eval-finalized b acc)
    (~(jab by acc) b |=(e=code-entry e(pure pure, total total)))
  $(sccs t.sccs, tab loc2)
=|  n=@ud
|-
?~  cmds  0
=/  c  i.cmds
=/  ca0  cache.state
=/  sz0  [~(wyt by nary.ca0) ~(wyt by mono.ca0) ~(wyt by inl.ca0) ~(wyt by sure.ca0) ~(wyt by sccs.ca0)]
=/  cole0  call.cole.jets.long-ska.state
=/  lon0=long-ska  long-ska.state
=/  hot0=(set ring)  ~(key by jets-hot.state)
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
=/  ndrop=@ud  ?:(?=([%drop *] p) (lent p.p) 0)
=/  dl=(list bell)  ?:(?=([%drop *] p) p.p ~)
=/  ok-gone=?
  =/  ca1  cache.state
  ?&  %+  levy  dl
      |=  b=bell
      ?&  !(~(has by nary.ca1) b)  !(~(has by mono.ca1) b)
          !(~(has by inl.ca1) b)  !(~(has by sure.ca1) b)
      ==
    ::  a %jets keeps every entry it does not drop
    ?.  ?=(%j -.c)  &
    %+  levy  ~(tap in ~(key by nary.ca0))
    |=  b=bell
    ?|  ?=(^ (find ~[b] dl))
        (~(has by nary.ca1) b)
    ==
  ==
=/  lon=long-ska  long-ska.state
=/  ks=(set *)  (silt (turn ~(tap in ~(key by code.lon)) |=(b=bell `*`b)))
=/  ok-ccall=?
  %+  levy  ~(tap by calls.lon)
  |=  [b=bell cs=(set bell)]
  (levy ~(tap in cs) |=(c=bell (~(has by code.lon) c)))
=/  ok-cinfo=?
  %+  levy  ~(tap by code.lon)
  |=  [b=bell e=code-entry]
  (levy (infos `*`nomm.e) |=(c=* (~(has in ks) c)))
=/  ca  cache.state
=/  ok-smap=?  ~(apt by sure.ca)
=/  ok-skey=?  =(~(key by sure.ca) ~(key by nary.ca))
=/  ok-imap=?  ~(apt by inl.ca)
=/  ok-ikey=?  (levy ~(tap in ~(key by inl.ca)) |=(b=bell (~(has by code.lon) b)))
=/  ok-ival=?
  %+  levy  ~(tap by inl.ca)
  |=  [b=bell v=nomm]
  =(v -:(inlined b [code jets calls]:lon jets-hot.state ca(inl ~)))
=/  ok-sccs=?
  %+  levy  ~(tap by sccs.ca)
  |=  [k=bell s=(set bell)]
  ?&  ~(apt in s)
      (~(has in s) k)
      (levy ~(tap in s) |=(k2=bell =((~(get by sccs.ca) k2) `s)))
  ==
=/  ok-nary=?
  %+  levy  ~(tap in ~(key by nary.ca))
  |=  k=bell
  ?~  s=(~(get by sccs.ca) k)  |
  (levy ~(tap in u.s) |=(k2=bell (~(has by nary.ca) k2)))
=/  ok-vars=?
  %+  levy  ~(tap by vars.lon)
  |=  [cb=bell vs=(set bell)]
  (levy ~(tap in vs) |=(v=bell &((~(has by code.lon) v) =(fol.v fol.cb))))
=/  ok-ckey=?
  ?&  =(~(key by code.lon) ~(key by calls.lon))
      =(~(key by code.lon) ~(key by seek.lon))
  ==
=/  ok-mono=?  (levy ~(tap in ~(key by mono.ca)) |=(b=bell (~(has by code.lon) b)))
=/  ok-flag=?  =((replay lon) code.lon)
=/  ok-scck=?  (levy ~(tap in ~(key by sccs.ca)) |=(b=bell (~(has by code.lon) b)))
=/  reach
  |=  k=bell
  ^-  (set bell)
  =|  seen=(set bell)
  =/  todo=(list bell)  ~[k]
  |-  ^-  (set bell)
  ?~  todo  seen
  ?:  (~(has in seen) i.todo)  $(todo t.todo)
  =/  nx=(list bell)
    (skim ~(tap in (~(gut by calls.lon) i.todo ~)) |=(c=bell (~(has by code.lon) c)))
  $(seen (~(put in seen) i.todo), todo (weld nx t.todo))
=/  ok-sset=?
  %+  levy  ~(tap by sccs.ca)
  |=  [k=bell s=(set bell)]
  =/  rk=(set bell)  (reach k)
  =/  want=(set bell)
    %-  silt
    %+  skim  ~(tap in ~(key by code.lon))
    |=(k2=bell &((~(has in rk) k2) (~(has in (reach k2)) k)))
  =(s want)
=/  ok-ccoh=?
  ?&  %+  levy  ~(tap by call.cole.jets.lon)
      |=  [c=bell r=ring]
      (~(has in (~(gut by back.cole.jets.lon) r ~)) c)
    ::
      %+  levy  ~(tap by back.cole.jets.lon)
      |=  [r=ring bs=(set bell)]
      (levy ~(tap in bs) |=(c=bell =((~(get by call.cole.jets.lon) c) `r)))
  ==
=/  is-path  |=(p=* ^-(? ?@(p =(0 p) &(?=(@ -.p) $(p +.p)))))
=/  ok-bset=?
  ?&  ~(apt by back.cole.jets.lon)
      (levy ~(tap by back.cole.jets.lon) |=([r=ring bs=(set bell)] ~(apt in bs)))
  ==
=/  ok-pset=?
  ?&  ~(apt by pend.jets.lon)
      (levy ~(tap by pend.jets.lon) |=([p=path ss=(set sock)] ~(apt in ss)))
  ==
=/  ok-jpth=?  (levy ~(tap in ~(key by core.jets.lon)) |=(p=path (is-path p)))
=/  ok-rmap=?
  ?.  ?=(%f -.c)  &
  =/  [g=callgraph =regs]
    (ska-callgraph [[&+s.c ;;(^ f.c)] memo.lon0 [root core batt arms ~]:jets.lon0])
  ?&  ~(apt by root.regs)  ~(apt by core.regs)  ~(apt by batt.regs)  ~(apt by arms.regs)
      (levy ~(tap in ~(key by core.regs)) |=(p=path (is-path p)))
  ==
=/  jm=[ok-jmod=? ok-nnew=?]
  ?.  ?=(%f -.c)  [& &]
  =/  [g=callgraph =regs]
    (ska-callgraph [[&+s.c ;;(^ f.c)] memo.lon0 [root core batt arms ~]:jets.lon0])
  =/  new-cores=(jug path sock)
    (~(gas ju *(jug path sock)) (turn new.regs |=([p=path s=sock *] [p s])))
  =/  nkeys=(set bell)
    (silt (skip ~(tap in ~(key by code.lon)) |=(b=bell (~(has by code.lon0) b))))
  =/  cm
    %-  ~(rep in nkeys)
    |=  [b=bell c=_cole.jets.lon0]
    ?~  r=(cole-match b (~(got by seek.lon) b) core.regs arms.regs hot0)  c
    (cole-put b u.r c)
  =/  model  [root.regs core.regs batt.regs arms.regs ((uni-ju pend.jets.lon0) new-cores) cm]
  :-  =(`*`model `*`jets.lon)
  ?.  ?=([%ir *] p)  |
  =(`*`(flop new.regs) `*`+>+.p)
=/  ok-cdom=?
  ?&  (levy ~(tap in ~(key by call.cole.jets.lon)) |=(c=bell (~(has by code.lon) c)))
      %+  levy  ~(tap by back.cole.jets.lon)
      |=  [r=ring bs=(set bell)]
      (levy ~(tap in bs) |=(c=bell (~(has by code.lon) c)))
  ==
~&  :*  %i  n  -.c  %ccall  ok-ccall  %cinfo  ok-cinfo  %smap  ok-smap  %skey  ok-skey
        %imap  ok-imap  %ikey  ok-ikey  %ival  ok-ival  %sccs  ok-sccs  %nary  ok-nary
        %vars  ok-vars  %ckey  ok-ckey  %mono  ok-mono  %flag  ok-flag  %scck  ok-scck  %gone  ok-gone
        %sset  ok-sset  %ccoh  ok-ccoh  %cdom  ok-cdom  %jmod  ok-jmod.jm  %nnew  ok-nnew.jm
        %bset  ok-bset  %pset  ok-pset  %jpth  ok-jpth  %rmap  ok-rmap
        %before  sz0
        %sizes  ~(wyt by code.lon)  ~(wyt by inl.ca)  ~(wyt by sure.ca)  ~(wyt by nary.ca)
                ~(wyt by mono.ca)  ~(wyt by sccs.ca)
        %cole  ~(wyt by call.cole.jets.lon)  =(cole0 call.cole.jets.lon)
        %pend  ~(wyt by pend.jets.lon)  %hot  ~(wyt by jets-hot.state)  %drop  ndrop
    ==
$(cmds t.cmds, n +(n))
