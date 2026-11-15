|%
++  memo-call
  =>  ..ride  !.
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  ~>  %memo./ska
  (g v)
::
++  build-sys
  |=  [sub=(trap vase) nam=term sys=path]
  ^-  (trap vase)
  ~>  %slog.[0 leaf+"steel: building /sys/{(trip nam)}"]
  =/  src  .^(@t cx+(welp sys /[nam]/hoon))
  (memo-call swat sub (rain /sys/[nam]/hoon src))
::
++  build-lib
  |=  [sub=(trap vase) imp=? bug=? nam=term lib=path]
  ^-  (trap vase)
  ~>  %slog.[0 leaf+"ivory: building /lib/{(trip nam)}"]
  =/  hun=hoon
    %^  mist  bug  /lib/[nam]/hoon
    .^(@t cx+(welp lib /[nam]/hoon))
  ?.  imp  (swat sub hun)
  (swel sub [%ktts nam hun])
::
++  mist
  |=  [bug=? bon=path txt=@]
  ^-  hoon
  =+  vas=vast
  ~|  bon
  %+  scan  (trip txt)
  %-  full
  =/  skip-ford
    %-  star
    ;~  pose  vul
      %+  ifix  [fas (just `@`10)]
      (star ;~(less (just `@`10) next))
    ==
  ::
  %+  ifix  [;~(plug gay skip-ford) gay]
  (stag %tssg (most gap tall:vas(wer bon, bug bug)))
  ::
::  +swel: +swat but with +slop
::
++  swel
  |=  [tap=(trap vase) gen=hoon]
  ^-  (trap vase)
  =/  gun  (~(mint ut p:$:tap) %noun gen)
  =>  [tap=tap gun=gun]
  |.  ~+
  =/  pro  q:$:tap
  [[%cell p.gun p:$:tap] [.*(pro q.gun) pro]]
--
::
:-  %say
|=  [[now=@da eny=@uvJ bec=beak] arg=$@(~ [bug=? ~]) ~]
:-  %noun
::
^-  [%steel p=(list)]
::  the SKA core's own hoon.hoon, not the kernel's: there +mock and +monk
::  are jetted, so that the core's virtualization (road-pure) runs compiled
::  when the core does; the two .* of +mink are under %bare
::
::  The library is built without the spots of its source, unless the
::  argument is & (+steel-pill &): they are for debugging the core, and a
::  core that carries them compiles three times slower
::
=/  bug=?  ?~(arg | bug.arg)
=/  sys=path  /(scot %p p.bec)/ska/(scot %da now)/sys
=/  lib=path  /(scot %p p.bec)/ska/(scot %da now)/lib
=/  trap
  =/  sub  *(trap vase)
  =.  sub  (build-sys sub %hoon sys)
  (build-lib sub | bug %nock-compilation lib)
::
=/  nok  !.
  =>  [=_trap ~]  !=
  q:$:trap
::
[%steel nok trap ~]
