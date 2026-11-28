::  hotempty.hoon (track P, fifteenth session): the pokes of jetsmodel.hoon
::  that Reach admits (every %jets is [%jets ~]) plus extra [%jets ~], %dire
::  and %fast pokes; after each, %hot0: jets-hot is ~; %same: a [%jets ~]
::  with pend empty returns [%drop ~] and the core's state unchanged;
::  %drop0: every [%jets ~] drops nothing; %long: the poke left memo,
::  code, calls, vars, seek alone (other than %full).  (%jatm is a
::  placeholder: mule does not compile here; hotatom.hoon crashes.)
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
  :~  [%j 0]
      [%f 0 fk]
      [%j 0]
      [%f 0 [4 0 1]]
      [%f 0 fc]
      [%f [0 [fid [fw fm2]]] [0 0]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%a | ~[[/mm tmm]]]
      [%j 0]
      [%j 0]
      [%f 7 dec]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%d 0 &]
      [%d 1 |]
      [%f 0 fc]
      [%j 0]
      [%f [0 [fid [fw fm2]]] fid]
      [%f [even [5 0]] [9 2 0 1]]
      [%a & ~[[/mm tmm]]]
      [%d 2 &]
      [%j 0]
      [%f [[ma mb] [9 8 7 0]] [9 5 [0 1]]]
      [%f [[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%f 9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [%j 0]
      [%d 3 |]
      [%f 3 [11 1.886.217.588 [1 0]]]
      [%a | ~[[/mc tmc]]]
      [%d 5 &]
      [%j 0]
      [%f [0 [fw fm2]] [2 [0 1] 0 2]]
      [%d 4 &]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%a & ~]
      [%a | ~[[/mm tmm]]]
      [%d 6 |]
      [%j 0]
      [%j 0]
      [%f 0 fc]
      [%a | ~[[/mc tmc]]]
      [%f [[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [%j 0]
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
::  the models' predictions, from the state before the poke
::
=/  jh0  jets-hot.state
::  %jsmod: settleO, a roll over the code table (not +ska-cole-settle)
::
=/  jpred=_cole.jets.lon0
  ?.  &(?=(%j -.c) !=(~ pend.jets.lon0))  cole.jets.lon0
  %+  roll  ~(tap by code.lon0)
  |=  [[b=bell *] c=_cole.jets.lon0]
  ?:  (~(has by call.c) b)  c
  =/  sek=cape  (~(gut by seek.lon0) b &)
  ?~  r=(cole-match b sek pend.jets.lon0 arms.jets.lon0 ~)  c
  (cole-put b u.r c)
::  %dmod: compileStep: +scc-of, then compiled-mono / compiled-nary on the
::  state with the new sccs, then +optimize
::
=/  dsel=(unit [b=bell m=?])
  ?.  ?=(%d -.c)  ~
  =/  ks=(list bell)  ~(tap in ~(key by code.long-ska.state))
  `[(snag (mod k.c (lent ks)) ks) m.c]
=/  dpred=(unit [out=straight-out ca=_cache.state st=straight])
  ?~  dsel  ~
  =/  sc  (scc-of b.u.dsel calls.long-ska.state sccs.cache.state)
  =.  sccs.cache.state  sccs.sc
  =/  r=[straight _cache.state]
    ?:  m.u.dsel  (compiled-mono b.u.dsel -.sc)
    (compiled-nary b.u.dsel -.sc)
  `[(optimize -.r) +.r -.r]
::  %fmod: the regs rerun, pend by uni-ju / dif-ju (or ~ and the cole
::  rebuilt over all of code on reset), the cache cleared iff call changed
::
=/  fpred=(unit [j=_jets.lon0 ca=_cache.state])
  ?.  ?=(%a -.c)  ~
  =/  j0  jets.lon0
  =/  reg=regs  ?:(r.c *regs [root core batt arms ~]:j0)
  =.  reg
    %+  roll  p.c
    |=  [[pax=path tem=sock] =_reg]
    (register-template pax tem ~ reg)
  =/  pc=[pend=_pend.j0 cole=_cole.j0]
    ?.  r.c  [((uni-ju pend.j0) ((dif-ju core.reg) core.j0)) cole.j0]
    =/  l  ~(tap by code.lon0)
    =/  co=_cole.j0  [~ ~]
    |-  ^-  [_pend.j0 _cole.j0]
    ?~  l  [~ co]
    =/  sek=cape  (~(got by seek.lon0) p.i.l)
    =/  r  (cole-match p.i.l sek core.reg arms.reg hot0)
    $(l t.l, co ?~(r co (cole-put p.i.l u.r co)))
  =/  j1  j0(root root.reg, core core.reg, batt batt.reg, arms arms.reg, pend pend.pc, cole cole.pc)
  =/  cf
    ?:  =(call.cole.j0 call.cole.pc)  cache.state
    cache.state(nary ~, mono ~, inl ~, sure ~)
  `[j1 cf]
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
=/  ok-hot0=?  =(~ jets-hot.state)
=/  ok-same=?
  ?.  &(?=(%j -.c) =(~ pend.jets.lon0))  &
  &(=(p [%drop ~]) =(`*`lon0 `*`long-ska.state) =(`*`ca0 `*`cache.state))
=/  ok-drop0=?  ?.(?=(%j -.c) & =(p [%drop ~]))
=/  ok-long=?
  ?:  ?=(%f -.c)  &
  =(`*`[memo code calls vars seek]:lon0 `*`[memo code calls vars seek]:long-ska.state)
=/  ok-jatm=?  &
=/  lon1=long-ska  long-ska.state
=/  cz  cache.state
=/  jsm=[ok=? cole=? pend=? rest=? cache=? hot=? prod=?]
  ?.  ?=(%j -.c)  [& & & & & & &]
  =/  f1=?  =(`*`jpred `*`cole.jets.lon1)
  =/  f2=?  =(~ pend.jets.lon1)
  =/  f3=?  =(`*`lon0(cole.jets jpred, pend.jets ~) `*`lon1)
  =/  f4=?  =(`*`ca0 `*`cz)
  =/  f5=?  =(~ jets-hot.state)
  =/  f6=?  =(`*`p `*`[%drop ~])
  [&(f1 f2 f3 f4 f5 f6) f1 f2 f3 f4 f5 f6]
=/  dm=[ok=? long=? hot=? cache=? prod=? put=? nput=?]
  ?~  dsel  [& & & & & & &]
  ?~  dpred  [| | | | | | |]
  =/  f1=?  =(`*`lon0 `*`lon1)
  =/  f2=?  =(`*`jh0 `*`jets-hot.state)
  =/  f3=?  =(`*`ca.u.dpred `*`cz)
  =/  f4=?  =(`*`p `*`[%ir b.u.dsel out.u.dpred ~])
  =/  f5=?  ?.(m.u.dsel & =(`*`(~(get by mono.cz) b.u.dsel) `*`[~ st.u.dpred]))
  =/  f6=?  ?:(m.u.dsel & =(`*`(~(get by nary.cz) b.u.dsel) `*`[~ st.u.dpred]))
  [&(f1 f2 f3 f4 f5) f1 f2 f3 f4 f5 f6]
=/  fm=[ok=? jets=? rest=? cache=? sccs=? hot=? prod=?]
  ?~  fpred  [& & & & & & &]
  =/  f1=?  =(`*`j.u.fpred `*`jets.lon1)
  =/  f2=?  =(`*`[memo code calls vars seek]:lon0 `*`[memo code calls vars seek]:lon1)
  =/  f3=?  =(`*`ca.u.fpred `*`cz)
  =/  f4=?  =(`*`sccs.ca0 `*`sccs.cz)
  =/  f5=?  =(`*`jh0 `*`jets-hot.state)
  =/  f6=?  =(`*`p `*`~)
  [&(f1 f2 f3 f4 f5 f6) f1 f2 f3 f4 f5 f6]
~&  :*  %m  n  -.c  %jsmod  ok.jsm  %dmod  ok.dm  %fmod  ok.fm
        %clr  !=(`*`ca0 `*`cz)  %nput  nput.dm
    ==
~?  !ok.jsm  [%jsmod-bad n +.jsm ~(wyt by call.jpred) ~(wyt by call.cole.jets.lon1)]
~?  !ok.dm  [%dmod-bad n +.dm]
~?  !ok.fm
  :*  %fmod-bad  n  +.fm
      ?~  fpred  ~
      :*  (mug root.j.u.fpred)  (mug root.jets.lon1)  (mug core.j.u.fpred)  (mug core.jets.lon1)
          (mug batt.j.u.fpred)  (mug batt.jets.lon1)  (mug arms.j.u.fpred)  (mug arms.jets.lon1)
          (mug pend.j.u.fpred)  (mug pend.jets.lon1)  (mug cole.j.u.fpred)  (mug cole.jets.lon1)
      ==
  ==
~&  :*  %i  n  -.c  %ccall  ok-ccall  %cinfo  ok-cinfo  %smap  ok-smap  %skey  ok-skey
        %imap  ok-imap  %ikey  ok-ikey  %ival  ok-ival  %sccs  ok-sccs  %nary  ok-nary
        %vars  ok-vars  %ckey  ok-ckey  %mono  ok-mono  %flag  ok-flag  %scck  ok-scck  %gone  ok-gone
        %sset  ok-sset  %ccoh  ok-ccoh  %cdom  ok-cdom  %jmod  ok-jmod.jm  %nnew  ok-nnew.jm
        %bset  ok-bset  %pset  ok-pset  %jpth  ok-jpth  %rmap  ok-rmap
        %hot0  ok-hot0  %same  ok-same  %drop0  ok-drop0  %long  ok-long  %jatm  ok-jatm  %pend0  ~(wyt by pend.jets.lon0)
        %before  sz0
        %sizes  ~(wyt by code.lon)  ~(wyt by inl.ca)  ~(wyt by sure.ca)  ~(wyt by nary.ca)
                ~(wyt by mono.ca)  ~(wyt by sccs.ca)
        %cole  ~(wyt by call.cole.jets.lon)  =(cole0 call.cole.jets.lon)
        %pend  ~(wyt by pend.jets.lon)  %hot  ~(wyt by jets-hot.state)  %drop  ndrop
    ==
$(cmds t.cmds, n +(n))
