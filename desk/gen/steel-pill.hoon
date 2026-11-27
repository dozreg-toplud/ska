|%
++  memo-call
  =>  ..ride  !.
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  ~>  %memo./ska
  (g v)
::
::  +in-hoon: the source of a gate that builds /sys/hoon from its text,
::  compiles the first of the sources against it, and runs that on the texts
::  and the other sources
::
++  in-hoon
  ^-  @t
  %-  of-wain:format
  :~  '|=  [sys=@t lib=@t bug=? src=(list @t)]'
      '?~  src  !!'
      '=/  hon=vase  $:(swat *(trap vase) (rain /sys/hoon/hoon sys))'
      '(slum q:(slap hon (ream i.src)) [sys lib bug t.src])'
  ==
::  +make: the source of the gate that makes the pill from the two texts
::
++  make
  ^-  @t
  %-  of-wain:format
  :~  '|=  [sys=@t lib=@t bug=? src=(list @t)]'
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
::  the pill is made by the hoon.hoon it holds, and that one by itself: the
::  kernel builds /sys/hoon, that hoon.hoon builds it again (+in-hoon), and
::  +make is compiled by the first against the second and run in it.  The
::  trap keeps the core that ran +swat: made by the kernel's own, the pill
::  held two hoon.hoons, and what the kernel's compiler does showed in it
::
~>  %slog.[0 leaf+"steel: building /sys/hoon"]
=/  hon=vase  $:(memo-call swat *(trap vase) (rain /sys/hoon/hoon sys))
~>  %slog.[0 leaf+"steel: building /sys/hoon by itself, and the pill in it"]
;;  [%steel p=(list)]
(slum q:(slap hon (ream in-hoon)) [sys lib bug ~[make]])
