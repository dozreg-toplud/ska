=/  lib  .
=/  fols=(list *)
  =>  lib
  :~  !=(=/(f |=(a=* .*(a a)) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=(a=* [a .*(a a)]) [(f (add 2 3)) (f 5) (f 7)]))
      !=(=/(f |=(a=* [.*(a a) a 7]) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=([a=* b=*] [b .*(a a)]) [(f (add 2 3) 4) (f 5 4) (f 5 (add 1 1))]))
      !=(=/(f |=(a=* ?:(=(a 5) 1 .*(a a))) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=(a=* .*(a a)) [(f (add 2 3)) (f 5) (f [1 2])]))
      !=(=/(g |=(a=* .*(a a)) =/(f |=(a=* [(g a) (g 6)]) [(f (add 2 3)) (f 5)])))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n), a [a 5]))) (f 40 (add 1 1))))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) [a .*(a a)] $(n (dec n), a [a 5]))) (f (add 20 20) (add 1 1))))
      !=(=/(f |=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n), a [5 a]))) [(f 40 (add 1 1)) (f 3 4)]))
  ==
::  +know of the library with .fold as a sample (the library's reads the
::  flag from bake-mode and folds by default)
::
=/  knowf
  |=  $:  fold=?
          =nomm
          sub=sock
          dat=$-(bell (unit datum))
          res=$-([bell sock] bell)
      ==
  ^-  $:  =^nomm
          sites=(list [b=bell k=sock])
      ==
  =/  gen  [sites=*(list [b=bell k=sock])]
  =/  sub=sock-anno  [sub 1]
  =*  hint-free  ,?(hint-safe %fast %memo)
  =<  =^  out=[nomm=^nomm prod=sock-anno]  gen  $
      [nomm.out sites.gen]
  |.  ^-  [[nomm=^nomm prod=sock-anno] _gen]
  =*  loop  $
  =*  dunno  *sock-anno
  ?-    nomm
      [^ *]
    =^  l  gen  loop(nomm -.nomm)
    =^  r  gen  loop(nomm +.nomm)
    :_  gen
    ?:  &(fold ?=([%1 *] nomm.l) ?=([%1 *] nomm.r))
      =/  x  [p.nomm.l p.nomm.r]
      [[%1 x] [&+x ~]]
    :-  =/  new  [nomm.l nomm.r]
        ?:(=(new nomm) nomm new)
    [(knit:so sock.prod.l sock.prod.r) (cons:pi src.prod.l src.prod.r)]
  ::
      [%0 *]
    ?:  =(0 p.nomm)  [[nomm dunno] gen]
    =/  prod=sock-anno
      ?:  =(1 p.nomm)  sub
      [(pull:so sock.sub p.nomm) (slot:pi src.sub p.nomm)]
    ?.  &(fold ?=(^ sock.prod) (all:ca cape.sock.prod))  [[nomm prod] gen]
    :-  [[%1 data.sock.prod] [sock.prod ~]]
    gen
  ::
      [%1 *]  [[nomm [&+p.nomm ~]] gen]
  ::
      [%2 *]
    =^  s  gen  loop(nomm p.nomm)
    =^  f  gen  loop(nomm q.nomm)
    ?~  info.nomm  [[[%2 nomm.s nomm.f ~] dunno] gen]
    =/  k=sock  sock.prod.s
    =/  v=bell  (res b.u.info.nomm k)
    =.  sites.gen  [[b.u.info.nomm k] sites.gen]
    =/  prod=sock-anno
      ?~  d=(dat b.u.info.nomm)  dunno
      =/  p  (patch-prod [prod map]:u.d k)
      [sock.p (compose:pi src.p src.prod.s)]
    [[[%2 nomm.s nomm.f `[v k.u.info.nomm]] prod] gen]
  ::
      [%3 *]
    =^  [n=^nomm p=sock-anno]  gen  loop(nomm p.nomm)
    ?.  &(fold ?=(^ sock.p) (all:ca cape.sock.p) (safe-nomm n))
      [[[%3 n] dunno] gen]
    =/  pro=@  .?(data.sock.p)
    :-  [[%1 pro] [&+pro ~]]
    gen
  ::
      [%4 *]
    =^  [n=^nomm p=sock-anno]  gen  loop(nomm p.nomm)
    ?.  ?&  fold
            ?=(^ sock.p)
            (all:ca cape.sock.p)
            ?=(@ data.sock.p)
            (safe-nomm n)
        ==
      [[[%4 n] dunno] gen]
    =/  pro=@  +(data.sock.p)
    :-  [[%1 pro] [&+pro ~]]
    gen
  ::
      [%5 *]
    =^  p  gen  loop(nomm p.nomm)
    =^  q  gen  loop(nomm q.nomm)
    ?.  ?&  fold
            ?=(^ sock.prod.p)
            (all:ca cape.sock.prod.p)
            (safe-nomm nomm.p)
            ?=(^ sock.prod.q)
            (all:ca cape.sock.prod.q)
            (safe-nomm nomm.q)
        ==
      [[[%5 nomm.p nomm.q] dunno] gen]
    =/  pro=@  ?:(=(data.sock.prod.p data.sock.prod.q) 0 1)
    :-  [[%1 pro] [&+pro ~]]
    gen
  ::
      [%6 *]
    =^  p  gen  loop(nomm p.nomm)
    ?:  ?&  fold
            ?=(^ sock.prod.p)
            (all:ca cape.sock.prod.p)
            (safe-nomm nomm.p)
            ?=(?(%0 %1) data.sock.prod.p)
        ==
      ?-  data.sock.prod.p
        %0  loop(nomm q.nomm)
        %1  loop(nomm r.nomm)
      ==
    =^  q  gen  loop(nomm q.nomm)
    =^  r  gen  loop(nomm r.nomm)
    [[[%6 nomm.p nomm.q nomm.r] (double-int prod.q prod.r)] gen]
  ::
      [%7 *]
    =^  p  gen  loop(nomm p.nomm)
    =^  q  gen  loop(nomm q.nomm, sub prod.p)
    ?:  &(fold ?=([%1 *] nomm.q) (safe-nomm nomm.p))
      [[nomm.q [&+p.nomm.q ~]] gen]
    [[[%7 nomm.p nomm.q] prod.q] gen]
  ::
      [%10 *]
    =^  don  gen  loop(nomm q.p.nomm)
    =^  rec  gen  loop(nomm q.nomm)
    =/  lit=(unit)
      ?.  &(fold ?=([%1 *] nomm.don) ?=([%1 *] nomm.rec))  ~
      (mole |.(.*([p.nomm.don p.nomm.rec] [%10 [p.p.nomm %0 2] %0 3])))
    ?^  lit  [[[%1 u.lit] [&+u.lit ~]] gen]
    :_  gen
    :-  [%10 [p.p.nomm nomm.don] nomm.rec]
    :-  (darn:so sock.prod.rec p.p.nomm sock.prod.don)
    (edit:pi src.prod.rec p.p.nomm src.prod.don)
  ::
      [%11 *]
    ?@  p.nomm
      =^  q  gen  loop(nomm q.nomm)
      ?:  &(fold ?=(hint-free p.nomm) ?=([%1 *] nomm.q))
        [[nomm.q [&+p.nomm.q ~]] gen]
      [[[%11 p.nomm nomm.q body.nomm] prod.q] gen]
    =^  h  gen  loop(nomm q.p.nomm)
    =^  q  gen  loop(nomm q.nomm)
    ?:  ?&  fold
            ?=(hint-free p.p.nomm)
            (safe-nomm nomm.h)
            ?=([%1 *] nomm.q)
        ==
      [[nomm.q [&+p.nomm.q ~]] gen]
    [[[%11 [p.p.nomm nomm.h] nomm.q body.nomm] prod.q] gen]
  ::
      [%12 *]
    =^  p  gen  loop(nomm p.nomm)
    =^  q  gen  loop(nomm q.nomm)
    [[[%12 nomm.p nomm.q] dunno] gen]
  ::
      [%mean *]
    =^  p  gen  loop(nomm p.nomm)
    =/  k=sock  sock.prod.p
    =/  v=bell  (res b.nomm k)
    =.  sites.gen  [[b.nomm k] sites.gen]
    =^  q  gen  loop(nomm q.nomm)
    [[[%mean nomm.p v nomm.q body.nomm k.nomm] prod.q] gen]
  ==
::  same nouns: each sock's nouns fit the other
::
=/  same  |=([a=sock b=sock] ^-(? &((huge:so a b) (huge:so b a))))
::  two springs equal on the parts that the cape c knows
::
=/  keq
  |=  [c=cape a=spring b=spring]
  ^-  ?
  ?:  =(a b)  &
  ?@  c  !c
  &($(c -.c, a (hed:pi a), b (hed:pi b)) $(c +.c, a (tel:pi a), b (tel:pi b)))
=/  capo  |=(s=sock ^-(cape ?@(s | cape.s)))
::  the maps of the identities of one code bell, patched at the site socks
::  that occur (as prodsites.hoon): equal, or equal where the patched
::  product knows; and, at each callee identity, the product the analysis
::  used for the call (its datum, not patched) against itself patched for
::  its own subject sock and against dat's patched for it
::
=/  check
  |=  [pruned=callgraph lon=long-ska]
  ^-  (list @ud)
  =/  dat
    |=  b=bell
    ^-  (unit datum)
    ?~  m=(~(get by (gut:mi memo.lon fol.b)) less.b)  ~
    `+.u.m
  =/  idc  |=([c=bell k=sock] c)
  =/  groups=(map bell (list [identity datum]))
    %-  ~(rep by pruned)
    |=  [[id=identity d=datum] acc=(map bell (list [identity datum]))]
    =/  b=bell  [less-code.d fol.id]
    (~(put by acc) b [[id d] (~(gut by acc) b ~)])
  ::  [cmp map-neq map-known-neq multi-cmp multi-map-neq]
  =/  cmp
    |=  [b=bell k=sock]
    ^-  [@ud @ud @ud @ud @ud]
    ?~  dd=(dat b)  [0 0 0 0 0]
    =/  pd  (patch-prod [prod map]:u.dd k)
    =/  l=(list [identity datum])  (~(gut by groups) b ~)
    =/  multi=?  (gth (lent l) 1)
    %+  roll  l
    |=  [[id=identity d=datum] n=@ud e=@ud f=@ud m=@ud g=@ud]
    =/  px  (patch-prod [prod map]:d k)
    =/  eq=?  =(src.px src.pd)
    =/  kq=?  (keq (capo sock.pd) src.px src.pd)
    ~?  &(!kq (lth f 3))  [%map-known-fail fol=(mug fol.b) n=(lent l) px=src.px pd=src.pd]
    :*  +(n)
        ?:(eq e +(e))
        ?:(kq f +(f))
        ?:(multi +(m) m)
        ?:(|(!multi eq) g +(g))
    ==
  =/  es=(list [identity datum])  ~(tap by pruned)
  =|  tot=(list @ud)
  =.  tot  (reap 12 0)
  |-  ^-  (list @ud)
  ?~  es  tot
  =/  d=datum  +.i.es
  =/  lr  (mule |.((knowf | nomm.d less-code.d dat idc)))
  ?:  ?=(%| -.lr)  $(es t.es)
  =/  ks=(list [b=bell k=sock])
    %+  weld  sites.p.lr
    %+  turn  ~(tap in callees.d)
    |=  ce=callee-entry
    ^-  [b=bell k=sock]
    =/  dc=datum  (~(got by pruned) id.ce)
    [[less-code.dc fol.id.ce] more.id.ce]
  =/  r
    %+  roll  ks
    |:  [[b=*bell k=*sock] acc=tot]
    =/  x  (cmp b k)
    =/  a  acc
    :~  +((snag 0 a))
        (add (snag 1 a) -.x)
        (add (snag 2 a) +<.x)
        (add (snag 3 a) +>-.x)
        (add (snag 4 a) +>+<.x)
        (add (snag 5 a) +>+>.x)
        (snag 6 a)  (snag 7 a)  (snag 8 a)  (snag 9 a)  (snag 10 a)  (snag 11 a)
    ==
  ::  the callee identities: used product against patched forms
  =/  r2
    %+  roll  ~(tap in callees.d)
    |:  [ce=*callee-entry acc=r]
    =/  dc=datum  (~(got by pruned) id.ce)
    =/  k=sock  more.id.ce
    =/  own  (patch-prod [prod map]:dc k)
    =/  s1=?  (same prod.dc sock.own)
    =/  m1=?  =(src.own map.dc)
    =/  dd  (dat [less-code.dc fol.id.ce])
    =/  s2=?  ?~(dd & (same prod.dc sock:(patch-prod [prod map]:u.dd k)))
    =/  m2=?  ?~(dd & =(src:(patch-prod [prod map]:u.dd k) src.own))
    ~?  &(!s1 (lth (snag 7 acc) 3))  [%own-patch-fail fol=(mug fol.id.ce) prod=prod.dc own=sock.own]
    ~?  &(!s2 (lth (snag 9 acc) 3))  [%used-vs-dat-fail fol=(mug fol.id.ce)]
    =/  a  acc
    :~  (snag 0 a)  (snag 1 a)  (snag 2 a)  (snag 3 a)  (snag 4 a)  (snag 5 a)
        +((snag 6 a))
        ?:(s1 (snag 7 a) +((snag 7 a)))
        ?:(m1 (snag 8 a) +((snag 8 a)))
        ?:(s2 (snag 9 a) +((snag 9 a)))
        ?:(m2 (snag 10 a) +((snag 10 a)))
        (snag 11 a)
    ==
  $(es t.es, tot r2)
=|  lon=long-ska
=/  n=@ud  0
|-  ^-  @
?~  fols  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=/  root-identity=identity  [&+lib f]
=/  gr  (mule |.((ska-callgraph root-identity memo.lon [root core batt arms ~]:jets.lon)))
?:  ?=(%| -.gr)  ~&  [%crash-graph n]  $(fols t.fols, n +(n))
=/  pruned=callgraph  (prune-callgraph -.p.gr root-identity)
=/  r  (mule |.((ska-poke [&+lib f] lon ~)))
?:  ?=(%| -.r)  ~&  [%crash n]  $(fols t.fols, n +(n))
=.  lon  +.p.r
=/  c  (mule |.((check pruned lon)))
?:  ?=(%| -.c)  ~&  [%crash-check n]  $(fols t.fols, n +(n))
=/  v  p.c
~&  :*  n  entries=~(wyt by pruned)  sites=(snag 0 v)  cmp=(snag 1 v)  map-neq=(snag 2 v)
        map-known-neq=(snag 3 v)  multi-cmp=(snag 4 v)  multi-map-neq=(snag 5 v)
        callees=(snag 6 v)  own-patch-notsame=(snag 7 v)  own-map-neq=(snag 8 v)
        used-vs-dat-notsame=(snag 9 v)  used-vs-dat-map-neq=(snag 10 v)
    ==
$(fols t.fols, n +(n))
