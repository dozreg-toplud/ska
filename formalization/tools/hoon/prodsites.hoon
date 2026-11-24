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
::  ProdSame at the site socks that occur.  For every entry of the pruned
::  graph, the sites of +know without folding under its code requirement
::  (k from the walk), and the analysis' site socks of its callees (more of
::  each callee identity): for every identity of the callee's code bell in
::  the pruned graph, its product patched for k against dat's, both ways.
::
=/  check
  |=  [pruned=callgraph lon=long-ska]
  ^-  [@ud @ud @ud @ud @ud @ud]
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
  =/  cmp
    |=  [b=bell k=sock]
    ^-  [@ud @ud @ud]
    ?~  dd=(dat b)  [0 0 1]
    =/  pd=sock  sock:(patch-prod [prod map]:u.dd k)
    =/  l=(list [identity datum])  (~(gut by groups) b ~)
    %+  roll  l
    |=  [[id=identity d=datum] n=@ud f=@ud z=@ud]
    =/  px=sock  sock:(patch-prod [prod map]:d k)
    =/  ok=?  (same px pd)
    ~?  !ok  [%prodsame-fail fol=(mug fol.b) n=(lent l) k=k px=px pd=pd]
    [+(n) ?:(ok f +(f)) z]
  =/  es=(list [identity datum])  ~(tap by pruned)
  =/  nsites=@ud  0
  =/  ncmp=@ud  0
  =/  nfail=@ud  0
  =/  nmiss=@ud  0
  =/  nmulti=@ud  0
  =/  ncrash=@ud  0
  |-  ^-  [@ud @ud @ud @ud @ud @ud]
  ?~  es  [nsites ncmp nfail nmiss nmulti ncrash]
  =/  d=datum  +.i.es
  =/  lr  (mule |.((knowf | nomm.d less-code.d dat idc)))
  ?:  ?=(%| -.lr)  $(es t.es, ncrash +(ncrash))
  =/  ks=(list [b=bell k=sock])
    %+  weld  sites.p.lr
    %+  turn  ~(tap in callees.d)
    |=  ce=callee-entry
    ^-  [b=bell k=sock]
    =/  dc=datum  (~(got by pruned) id.ce)
    [[less-code.dc fol.id.ce] more.id.ce]
  =/  r
    %+  roll  ks
    |=  [[b=bell k=sock] n=@ud c=@ud f=@ud z=@ud m=@ud]
    =/  x  (cmp b k)
    =/  multi=?  (gth (lent (~(gut by groups) b ~)) 1)
    [+(n) (add c -.x) (add f +<.x) (add z +>.x) ?:(multi +(m) m)]
  %=  $
    es  t.es
    nsites  (add nsites -.r)
    ncmp  (add ncmp +<.r)
    nfail  (add nfail +>-.r)
    nmiss  (add nmiss +>+<.r)
    nmulti  (add nmulti +>+>.r)
  ==
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
~&  [n entries=~(wyt by pruned) sites-callees=-.p.c cmp=+<.p.c fail=+>-.p.c nodat=+>+<.p.c multi=+>+>-.p.c nfcrash=+>+>+.p.c]
$(fols t.fols, n +(n))
