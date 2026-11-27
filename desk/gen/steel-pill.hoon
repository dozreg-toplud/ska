|%
++  memo-call
  =>  ..ride  !.
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  ~>  %memo./ska
  (g v)
::
::  +make: the source of the gate that makes the pill from the two texts.
::  It is compiled against the hoon.hoon that the pill holds and run in it
::
++  make
  ^-  @t
  %-  of-wain:format
  :~  '|=  [sys=@t lib=@t bug=?]'
      '=/  mist'
      '  |=  [bon=path txt=@]'
      '  ^-  hoon'
      '  =+  vas=vast'
      '  ~|  bon'
      '  %+  scan  (trip txt)'
      '  %-  full'
      '  =/  skip-ford'
      '    %-  star'
      '    ;~  pose  vul'
      '      %+  ifix  [fas (just `@`10)]'
      '      (star ;~(less (just `@`10) next))'
      '    =='
      '  %+  ifix  [;~(plug gay skip-ford) gay]'
      '  (stag %tssg (most gap tall:vas(wer bon, bug bug)))'
      '=/  trap'
      '  =/  sub  *(trap vase)'
      '  =.  sub  (swat sub (rain /sys/hoon/hoon sys))'
      '  (swat sub (mist /lib/nock-compilation/hoon lib))'
      '=/  nok  !.'
      '  =>  [=_trap ~]  !='
      '  q:$:trap'
      '[%steel nok trap ~]'
  ==
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
=/  sys=@t  .^(@t cx+/(scot %p p.bec)/ska/(scot %da now)/sys/hoon/hoon)
=/  lib=@t
  .^(@t cx+/(scot %p p.bec)/ska/(scot %da now)/lib/nock-compilation/hoon)
::  the pill is made by the hoon.hoon it holds, not by the kernel's: the
::  kernel builds /sys/hoon, and +make is compiled against that core and
::  run in it.  The trap keeps the core that ran +swat, so with the
::  kernel's own the pill would hold two hoon.hoons, and an edit of
::  /sys/hoon would be paid in every type that the two no longer share
::
~>  %slog.[0 leaf+"steel: building /sys/hoon"]
=/  hon=vase  $:(memo-call swat *(trap vase) (rain /sys/hoon/hoon sys))
~>  %slog.[0 leaf+"steel: building the pill in it"]
;;  [%steel p=(list)]
(slum q:(slap hon (ream make)) [sys lib bug])
