::  SitesMeet fails, and so does BakesImply: a bake that is not under its
::  code requirement.  The core C = [[armR armF] 0]; armR runs
::  ?:(0=0 [[[3 0] 5] (armF C)] [[[1 7] 5] 9]) and calls H = [2 [0 1] [0 4]]
::  on the product; armF calls armR, then itself, so it never returns.  The
::  analysis reads armF's product %void (in progress), so the first branch
::  is %void (+knit:so of %void), +double-int keeps the second, and H's
::  code bell requires axis 4 = [1 7].  +know under R's bake folds the test
::  [1 0] to the first branch, where armF's product is the |+~ of +pop, so
::  H's site knows [[[3 0] 5] ~], which shares no noun with H's code
::  requirement (SitesMeet fails), and +uni-sock keeps the fully known side,
::  so H's variant has the bake [[[3 0] 5] ~] (axis 4 = [3 0]).  The second
::  formula tests [5 [1 0] [1 0]] instead.  Prints the checks of
::  voidscc.hoon with the failing SitesMeet sites, then the check of
::  bakeok.hoon with the bad pairs.
::
=/  lib  .
=/  fols=(list *)
  :~  [7 [1 [[[2 [6 [1 0] [[1 [[3 0] 5]] [9 5 0 1]] [1 [[[1 7] 5] 9]]] [1 [2 [0 1] [0 4]]]] [8 [9 4 0 1] [9 5 0 3]]] 0]] [9 4 0 1]]
      [7 [1 [[[2 [6 [5 [1 0] [1 0]] [[1 [[3 0] 5]] [9 5 0 1]] [1 [[[1 7] 5] 9]]] [1 [2 [0 1] [0 4]]]] [8 [9 4 0 1] [9 5 0 3]]] 0]] [9 4 0 1]]
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
=/  no
  |=  c=cape
  ^-  ?
  ?@  c  !c
  &($(c -.c) $(c +.c))
=/  meets
  |=  [ca=cape da=* cb=cape db=*]
  ^-  ?
  ?:  |((no ca) (no cb))  &
  ?:  &(?=(%& ca) ?=(%& cb))  =(da db)
  ?:  |(?=(@ da) ?=(@ db))  |
  =/  ha=cape  ?@(ca ca -.ca)
  =/  ta=cape  ?@(ca ca +.ca)
  =/  hb=cape  ?@(cb cb -.cb)
  =/  tb=cape  ?@(cb cb +.cb)
  ?&  $(ca ha, da -.da, cb hb, db -.db)
      $(ca ta, da +.da, cb tb, db +.db)
  ==
=/  mets  |=([a=sock b=sock] ^-(? ?@(a | ?@(b | (meets cape.a data.a cape.b data.b)))))
=/  hug  |=([a=sock b=sock] ^-(? (huge:so a b)))
::  LessProvidesNF: sites of the run without folding under less.cur that
::  do not provide their callee's code requirement (non-root, root)
::
=/  less-fails
  |=  [roots=(set bell) sites=(list [b=bell k=sock])]
  ^-  [@ud @ud]
  %+  roll  sites
  |=  [[b=bell k=sock] n=@ud r=@ud]
  ?:  (hug less.b k)  [n r]
  ?:  (~(has in roots) b)  [n +(r)]
  [+(n) r]
::  KnowMeetsNF: sites under the bake with no site of the same callee in
::  the run without folding that meets them (non-root, root)
::
=/  meet-fails
  |=  [roots=(set bell) sites=(list [b=bell k=sock]) lsites=(list [b=bell k=sock])]
  ^-  [@ud @ud]
  %+  roll  sites
  |=  [[b=bell k=sock] n=@ud r=@ud]
  =/  ok=?
    %+  lien  lsites
    |=  [b2=bell k2=sock]
    ^-  ?
    &(=(b2 b) (mets k k2))
  ?:  ok  [n r]
  ?:  (~(has in roots) b)  [n +(r)]
  [+(n) r]
::  SitesMeet itself, for comparison
::
=/  sm-fails
  |=  [roots=(set bell) sites=(list [b=bell k=sock])]
  ^-  @ud
  %+  roll  sites
  |=  [[b=bell k=sock] n=@ud]
  ?:  (~(has in roots) b)  n
  ?:  (mets less.b k)  n
  +(n)
=/  check
  |=  [lon=long-ska roots=(set bell)]
  ^-  [@ud @ud @ud @ud @ud @ud @ud @ud @ud @ud]
  =/  dat
    |=  b=bell
    ^-  (unit datum)
    ?~  m=(~(get by (gut:mi memo.lon fol.b)) less.b)  ~
    `+.u.m
  =/  idc  |=([c=bell k=sock] c)
  =/  pairs=(list [c=bell s=sock])
    %+  weld
      ^-  (list [c=bell s=sock])
      %-  zing
      %+  turn  ~(tap by vars.lon)
      |=  [c=bell vs=(set bell)]
      ^-  (list [c=bell s=sock])
      (turn ~(tap in vs) |=(v=bell ^-([c=bell s=sock] [c less.v])))
    ^-  (list [c=bell s=sock])
    %-  zing
    %+  turn  ~(tap by memo.lon)
    |=  [fol=^ m=(map sock [identity datum])]
    ^-  (list [c=bell s=sock])
    (turn ~(tap in ~(key by m)) |=(l=sock ^-([c=bell s=sock] [[l fol] l])))
  =/  npairs=@ud  0
  =/  nstrict=@ud  0
  =/  nsites=@ud  0
  =/  nlsites=@ud  0
  =/  fl=@ud  0
  =/  flr=@ud  0
  =/  fm=@ud  0
  =/  fmr=@ud  0
  =/  fs=@ud  0
  =/  crash=@ud  0
  |-  ^-  [@ud @ud @ud @ud @ud @ud @ud @ud @ud @ud]
  ?~  pairs  [npairs nstrict nsites nlsites fl flr fm fmr fs crash]
  =/  d=(unit datum)  (dat c.i.pairs)
  ?~  d  $(pairs t.pairs)
  =/  sites=(list [b=bell k=sock])  sites:(know nomm.u.d s.i.pairs dat idc)
  =/  lr  (mule |.((knowf | nomm.u.d less.c.i.pairs dat idc)))
  ?:  ?=(%| -.lr)
    ~&  [%nf-crash fol=(mug fol.c.i.pairs)]
    $(pairs t.pairs, crash +(crash))
  =/  lsites=(list [b=bell k=sock])  sites.p.lr
  =/  a  (less-fails roots lsites)
  =/  b  (meet-fails roots sites lsites)
  =/  sm  (sm-fails roots sites)
  ~?  (gth sm 0)  [%sm-sites %s s.i.pairs %sites sites]
  ~?  &(%.n (gth -.a 0))  [%lsites lsites %less less.c.i.pairs %s s.i.pairs]
  ~?  &(%.n (gth -.a 0))  [%nomm nomm.u.d]
  ~?  &(%.n (gth -.a 0))  [%dat-prods (turn lsites |=([b=bell k=sock] [less.b ?~(d=(dat b) ~ `prod.u.d)]))]
  ~?  (gth (add -.a (add -.b sm)) 0)
    [%fail fol=(mug fol.c.i.pairs) strict=!=(s.i.pairs less.c.i.pairs) less=a meet=b sm=sm]
  %=  $
    pairs  t.pairs
    npairs  +(npairs)
    nstrict  ?:(=(s.i.pairs less.c.i.pairs) nstrict +(nstrict))
    nsites  (add nsites (lent sites))
    nlsites  (add nlsites (lent lsites))
    fl  (add fl -.a)
    flr  (add flr +.a)
    fm  (add fm -.b)
    fmr  (add fmr +.b)
    fs  (add fs sm)
  ==
=|  lon=long-ska
=|  roots=(set bell)
=/  n=@ud  0
|-  ^-  @
?~  fols  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=/  r  (mule |.((ska-poke [&+lib f] lon ~)))
?:  ?=(%| -.r)  ~&  [%crash n]  $(fols t.fols, n +(n))
=/  rb=bell  -<.p.r
=.  lon  +.p.r
=.  roots  (~(put in roots) rb)
=/  res  (check lon roots)
~&  [n res]
=/  all=(list [c=bell v=bell])
  %-  zing
  %+  turn  ~(tap by vars.lon)
  |=  [c=bell vs=(set bell)]
  (turn ~(tap in vs) |=(v=bell [c v]))
=/  bad  (skip all |=([c=bell v=bell] (huge:so less.c less.v)))
~&  [%bakeok n variants=(lent all) bad=(lent bad)]
~?  ?=(^ bad)  [%bad bad]
~?  ?=(^ bad)  [%bad-pairs (turn bad |=([c=bell v=bell] [less.c less.v fol.c]))]
$(fols t.fols, n +(n))
