=/  lib  .
=/  fols=(list *)
  =>  lib
  :~  !=((add 2 3))
      !=((mul 12 12))
      !=((roll (gulf 1 10) add))
      !=((sort ~[3 1 2 9 4] lth))
      !=((~(get by (~(put by *(map @ @)) 1 2)) 1))
      !=((cue (jam [1 2 3])))
      !=((scow %ud 12.345))
      !=((need (rush '12+3' ;~(plug dem ;~(pfix lus dem)))))
      !=((flop (turn (gulf 1 5) |=(a=@ (mul a a)))))
      !=((turn (gulf 1 3) |=(a=@ (add a 1))))
      !=((~(put in *(set @)) 7))
      !=((crip (trip 'abc')))
      !=((~(gas by *(map @ @)) ~[[1 2] [3 4]]))
      !=((rash '0x1f' hex))
      !=((ream '(add 1 2)'))
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
=/  mets  |=([a=sock b=sock] ?@(a | ?@(b | (meets cape.a data.a cape.b data.b))))
=/  check
  |=  [lon=long-ska roots=(set bell)]
  ^-  [@ud @ud (list [c=bell s=sock b=bell k=sock])]
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
  =/  nonorm=@ud
    %+  roll  pairs
    |=  [[c=bell s=sock] n=@ud]
    ?:  =(less.c (norm-sock less.c))  n
    +(n)
  ~&  [%non-normal-less nonorm %of (lent pairs)]
  =|  fails=(list [c=bell s=sock b=bell k=sock])
  =/  nsites=@ud  0
  |-  ^-  [@ud @ud (list [c=bell s=sock b=bell k=sock])]
  ?~  pairs  [(lent fails) nsites fails]
  =/  d=(unit datum)  (dat c.i.pairs)
  ?~  d  $(pairs t.pairs)
  =/  sites=(list [b=bell k=sock])  sites:(know nomm.u.d s.i.pairs dat idc)
  =.  nsites  (add nsites (lent sites))
  =.  fails
    |-  ^+  fails
    ?~  sites  fails
    ?:  |((~(has in roots) b.i.sites) (mets less.b.i.sites k.i.sites))  $(sites t.sites)
    $(sites t.sites, fails [[c.i.pairs s.i.pairs b.i.sites k.i.sites] fails])
  $(pairs t.pairs)
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
~&  [n fails=-.res sites=+<.res]
~?  ?=(^ +>.res)  [%fail c=fol.c.i.+>.res callee=b.i.+>.res k=k.i.+>.res]
$(fols t.fols, n +(n))
