::  stable.hoon (track A, 2026-11-28): the four compile leaves of CompHyp
::  that had no owner (`stable`, `jetRoot`, `jets`, `fast`), on the real
::  compiler.  The reference compiler of the Lean model is a FRESH compile:
::  +compile-unary / +compile-scc of the bell's SCC on an empty cache, at the
::  state's code, jets and jets-hot.  After each poke of a sequence that
::  Reach admits (%full, %fast, [%jets ~], %dire):
::    %cm %cn  every mono / nary cache entry against the fresh compile at the
::             state the poke left (CacheOK): equal / equal after erasing
::             the ring ops (%jmf %jsf %caf %csf to %jmp %jsp %cal %csl:
::             RingSame plus need and n-args) / different
::    %rm %rn  every bell of the table BEFORE the poke: its fresh compile
::             before against after (the leaf `stable` for %full; for %jets
::             and %fast, whether the reference moves with the jets)
::    %code %ring %scc  old code entries, old rings of call.cole, old SCCs
::             unchanged
::    %clr     whether the poke emptied mono and nary
::  On %e (eval-top, which pokes %full and runs the code): the product of
::  +eval-top against +mink (with +mook), whether the root bell has a ring,
::  and whether the code is the one-block %jsf of the jetted-root branch.
::  Every bell and need that differs is printed in full (%xd).
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
::  ringdump.hoon's core: three arms, ra recurs on the payload's tail
=/  ra=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  rb=*  [4 [9 4 [0 1]]]
=/  rc=*  [[9 4 [0 1]] [9 10 [0 1]]]
=/  rcor=*  [[ra [rb rc]] [1 2 0]]
::  a caller of dec's gate and of even's gate in one formula (shared callees)
=/  both=*  [[8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1] [7 [1 even 5 0] 9 2 0 1]]
=/  tmm=sock  [& [[ma mb] [1 2 3 4 5 6 0]]]
=/  tmc=sock  [& [[mc mb] [1 2 3 4 5 6 0]]]
=/  trc=sock  [& rcor]
=/  cmds=(list $%([%f s=* f=*] [%e s=* f=*] [%d k=@ m=?] [%a r=? p=(list [path sock])] [%j ~]))
  :~  [%f 0 [4 0 1]]
      [%f 7 dec]
      [%f 9 dec]
      [%f [even [5 0]] [9 2 0 1]]
      [%f [even [8 0]] [9 2 0 1]]
      [%f 3 both]
      [%d 0 |]
      [%d 1 &]
      [%f 0 fk]
      [%f 0 fc]
      [%f [0 [fid [fw fm2]]] [0 0]]
      [%f [0 [fid [fw fm2]]] fid]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f [[ma mb] [9 8 7 0]] [9 5 [0 1]]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 5 [0 1]]]
      [%a | ~[[/mm tmm]]]
      [%j ~]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%e [[ma mb] [1 2 3 4 5 6 0]] ma]
      [%e [[ma mb] [1 2 3 4 5 6 0]] mb]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%d 2 |]
      [%d 3 &]
      [%f 11 dec]
      [%f [even [6 0]] [9 2 0 1]]
      [%a | ~[[/rr trc]]]
      [%e rcor [7 [0 1] [9 4 [0 1]]]]
      [%e rcor ra]
      [%f rcor [7 [0 1] [4 [9 4 [0 1]]]]]
      [%f rcor [7 [0 1] [[9 4 [0 1]] [9 10 [0 1]]]]]
      [%j ~]
      [%f rcor [7 [0 1] [9 11 [0 1]]]]
      [%a | ~[[/mc tmc]]]
      [%f [[mc mb] [9 8 7 0]] [9 4 [0 1]]]
      [%j ~]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 5 [0 1]]]
      [%e [[mc mb] [1 2 3 4 5 6 0]] mc]
      [%f 5 both]
      [%f 9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [%f 3 [11 1.886.217.588 [1 0]]]
      [%f [0 [fw fm2]] [2 [0 1] 0 2]]
      [%d 4 |]
      [%a & ~[[/mm tmm]]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f [[ma mb] [4 3 2 1 0]] [9 4 [0 1]]]
      [%e [[ma mb] [4 3 2 1 0]] ma]
      [%j ~]
      [%f 0 fc]
      [%f [even [9 0]] [9 2 0 1]]
      [%f 13 dec]
  ==
=/  erase
  |=  n=*
  ^-  *
  ?@  n  n
  ?:  ?=([%jmf * * *] n)  [%jmp $(n +<.n) $(n +>-.n)]
  ?:  ?=([%jsf * * *] n)  [%jsp $(n +<.n) $(n +>-.n)]
  ?:  ?=([%caf * * * *] n)  [%cal $(n +<.n) $(n +>-.n) $(n +>+<.n)]
  ?:  ?=([%csf * * * *] n)  [%csl $(n +<.n) $(n +>-.n) $(n +>+<.n)]
  [$(n -.n) $(n +.n)]
=/  cmp
  |=  [a=straight b=straight]
  ^-  @tas
  ?:  =(a b)  %eq
  ?:  =((erase `*`a) (erase `*`b))  %ring
  %diff
=/  fresh-mono
  |=  [b=bell lon=long-ska hot=jets-comp]
  ^-  straight
  =/  scc=(set bell)  -:(scc-of b calls.lon ~)
  -<:(compile-unary b scc [code jets calls]:lon hot *comp-cache)
=/  fresh-nary
  |=  [b=bell lon=long-ska hot=jets-comp]
  ^-  straight
  =/  scc=(set bell)  -:(scc-of b calls.lon ~)
  (~(got by -:(compile-scc scc [code jets calls]:lon hot *comp-cache)) b)
=/  fresh-all
  |=  [lon=long-ska hot=jets-comp]
  ^-  (map [bell ?] straight)
  %-  ~(rep in ~(key by code.lon))
  |=  [b=bell acc=(map [bell ?] straight)]
  =.  acc  (~(put by acc) [b &] (fresh-mono b lon hot))
  (~(put by acc) [b |] (fresh-nary b lon hot))
::  tally [eq ring diff] of a list of pairs, printing every pair that differs
=/  tally
  |=  [tag=@tas n=@ud l=(list [k=[bell ?] a=straight b=straight])]
  ^-  [@ud @ud @ud]
  =|  t=[e=@ud r=@ud d=@ud]
  |-  ^+  t
  ?~  l  t
  =/  c=@tas  (cmp a.i.l b.i.l)
  ?:  ?=(%eq c)  $(l t.l, e.t +(e.t))
  ~&  [%xd n tag c k.i.l %need need.a.i.l need.b.i.l %nargs n-args.a.i.l n-args.b.i.l]
  ?:  ?=(%ring c)  $(l t.l, r.t +(r.t))
  $(l t.l, d.t +(d.t))
=|  n=@ud
=|  fr0=(map [bell ?] straight)
|-
?~  cmds  0
=/  c  i.cmds
=/  lon0=long-ska  long-ska.state
=/  ca0  cache.state
=/  hot0  jets-hot.state
=/  ovo=*
  ?-    -.c
      %f  [%full s.c ;;(^ f.c)]
      %e  [%full s.c ;;(^ f.c)]
      %a  [%fast r.c p.c]
      %j  [%jets ~]
      %d
    =/  ks=(list bell)  ~(tap in ~(key by code.long-ska.state))
    [%dire (snag (mod k.c (lent ks)) ks) m.c]
  ==
::  %e: the eval-top run (its own %full poke) against +mink; else the poke
=^  p=prod  ..poke
  ?.  ?=(%e -.c)  (poke ovo)
  =/  a=toon  (mook (mink [s.c f.c] ~))
  =/  st0  state
  =^  ton=tone  ..^poke  (eval-top [s.c f.c] ~)
  =^  b=toon  ..^poke  (eval-mook ton)
  =/  st1  state
  ::  the prod of that %full: the same poke again, from the state before
  =.  state  st0
  =^  q=prod  ..poke  (poke ovo)
  ~&  [%ev n %mink-same =(a b) %state-same =(`*`st1 `*`state)]
  [q ..poke]
=/  lon=long-ska  long-ska.state
=/  ca  cache.state
=/  hot  jets-hot.state
=/  fr1=(map [bell ?] straight)  (fresh-all lon hot)
=/  cm=[@ud @ud @ud]
  %^  tally  %cm  n
  (turn ~(tap by mono.ca) |=([b=bell s=straight] [[b &] s (~(got by fr1) [b &])]))
=/  cn=[@ud @ud @ud]
  %^  tally  %cn  n
  (turn ~(tap by nary.ca) |=([b=bell s=straight] [[b |] s (~(got by fr1) [b |])]))
=/  rr=[@ud @ud @ud]
  %^  tally  %rr  n
  (turn ~(tap by fr0) |=([k=[bell ?] s=straight] [k s (~(got by fr1) k)]))
=/  ok-code=?
  (levy ~(tap by code.lon0) |=([b=bell e=code-entry] =((~(get by code.lon) b) `e)))
=/  ok-ring=?
  %+  levy  ~(tap in ~(key by code.lon0))
  |=(b=bell =((~(get by call.cole.jets.lon0) b) (~(get by call.cole.jets.lon) b)))
=/  ok-scc=?
  %+  levy  ~(tap in ~(key by code.lon0))
  |=(b=bell =(-:(scc-of b calls.lon0 ~) -:(scc-of b calls.lon ~)))
=/  clr=?  &(=(~ mono.ca) =(~ nary.ca) |(!=(~ mono.ca0) !=(~ nary.ca0)))
=/  jr=*
  ?.  ?=([%ir *] p)  ~
  =/  fun=bell  b.p
  =/  rin  (~(get by call.cole.jets.lon) fun)
  =/  vs=(list *)  ~(val by blocks.p.p)
  =/  jsf=?  ?=([[* * %jsf *] ~] vs)
  [%root-ring rin %jsf-block jsf %nblocks ~(wyt by blocks.p.p)]
~&  :*  %i  n  -.c
        %cm  cm  %cn  cn  %rr  rr
        %code  ok-code  %ring  ok-ring  %scc  ok-scc  %clr  clr
        %bells  ~(wyt by code.lon0)  ~(wyt by code.lon)
        %cache  ~(wyt by mono.ca)  ~(wyt by nary.ca)
        %cole  ~(wyt by call.cole.jets.lon0)  ~(wyt by call.cole.jets.lon)
        %pend  ~(wyt by pend.jets.lon)  %hot  ~(wyt by hot)
        %jr  jr
    ==
$(cmds t.cmds, n +(n), fr0 fr1)
