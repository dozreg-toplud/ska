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
  |=  [sub=(trap vase) imp=? nam=term lib=path]
  ^-  (trap vase)
  ~>  %slog.[0 leaf+"ivory: building /lib/{(trip nam)}"]
  =/  hun=hoon
    %+  mist  /lib/[nam]/hoon
    .^(@t cx+(welp lib /[nam]/hoon))
  ?.  imp  (swat sub hun)
  (swel sub [%ktts nam hun])
::
++  mist
  |=  [bon=path txt=@]
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
  (stag %tssg (most gap tall:vas(wer bon, bug &)))
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
|=  [[now=@da eny=@uvJ bec=beak] *]
:-  %noun
::
^-  [%steel p=(list)]
=/  sys=path  /(scot %p p.bec)/base/(scot %da now)/sys
=/  lib=path  /(scot %p p.bec)/ska/(scot %da now)/lib
=/  trap
  =/  sub  *(trap vase)
  =.  sub  (build-sys sub %hoon sys)
  (build-lib sub | %nock-compilation lib)
::
=/  nok  !.
  =>  [=_trap ~]  !=
  q:$:trap
::
[%steel nok trap ~]
