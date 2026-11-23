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
=/  hug  |=([a=sock b=sock] ^-(? (huge:so a b)))
=/  isvoid  |=(a=sock ^-(? ?@(a & |)))
=/  less-fails
  |=  [roots=(set bell) sites=(list [b=bell k=sock])]
  ^-  @ud
  %+  roll  sites
  |=  [[b=bell k=sock] n=@ud]
  ?:  (~(has in roots) b)  n
  ?:  (hug less.b k)  n
  +(n)
=/  mono-fails
  |=  [sites=(list [b=bell k=sock]) lsites=(list [b=bell k=sock])]
  ^-  @ud
  %+  roll  sites
  |=  [[b=bell k=sock] n=@ud]
  =/  ok=?
    %+  lien  lsites
    |=  [b2=bell k2=sock]
    ^-  ?
    &(=(b2 b) (hug k2 k))
  ?:  ok  n
  +(n)
=/  void-fails
  |=  sites=(list [b=bell k=sock])
  ^-  @ud
  %+  roll  sites
  |=  [[b=bell k=sock] n=@ud]
  ?:  (isvoid k)  +(n)
  n
=/  check
  |=  [lon=long-ska roots=(set bell)]
  ^-  [@ud @ud @ud @ud @ud @ud]
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
  =/  fl=@ud  0
  =/  fm=@ud  0
  =/  fv=@ud  0
  |-  ^-  [@ud @ud @ud @ud @ud @ud]
  ?~  pairs  [npairs nstrict nsites fl fm fv]
  =/  d=(unit datum)  (dat c.i.pairs)
  ?~  d  $(pairs t.pairs)
  =/  sites=(list [b=bell k=sock])  sites:(know nomm.u.d s.i.pairs dat idc)
  =/  lsites=(list [b=bell k=sock])  sites:(know nomm.u.d less.c.i.pairs dat idc)
  =/  a  (less-fails roots lsites)
  =/  b  (mono-fails sites lsites)
  =/  v  (void-fails sites)
  ~?  (gth (add a (add b v)) 0)  [%fail fol=fol.c.i.pairs less=a mono=b void=v]
  %=  $
    pairs  t.pairs
    npairs  +(npairs)
    nstrict  ?:(=(s.i.pairs less.c.i.pairs) nstrict +(nstrict))
    nsites  (add nsites (lent sites))
    fl  (add fl a)
    fm  (add fm b)
    fv  (add fv v)
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
~&  [n pairs=-.res strict=+<.res sites=+>-.res less-fail=+>+<.res mono-fail=+>+>-.res void-fail=+>+>+.res]
$(fols t.fols, n +(n))
