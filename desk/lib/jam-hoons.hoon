/*  sock            %hoon  /sur/sock/hoon
/*  noir            %hoon  /sur/noir/hoon
/*  gene            %hoon  /sur/gene/hoon
/*  soak            %hoon  /lib/soak/hoon
/*  skan            %hoon  /lib/skan/hoon
/*  line            %hoon  /lib/line/hoon
/*  vere-interface  %hoon  /lib/vere-interface/hoon
::
::  utils
=/  fas-line
  %-  star
  ;~  pose  vul
    %+  ifix  [fas (just `@`10)]
    (star ;~(less (just `@`10) next))
  ==
::
=/  memo-call
  =>  ..ride
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  !.  ~>  %memo./user
  (g v) 
::
|%
::  deferred +slop
::
++  swot
  |=  [a=(trap vase) b=(trap vase)]
  ^-  (trap vase)
  =/  typ  [%cell p:$:a p:$:b]
  |.
  [typ q:$:a q:$:b]
::
++  name
  |=  [tap=(trap vase) nam=term]
  ^-  (trap vase)
  =/  typ  [%face nam p:$:tap]
  |.
  [typ q:$:tap]
::
++  mist
  |=  [bon=path txt=@]
  ^-  hoon
  ~|  bon
  :-  %tssg
  ^-  (list hoon)
  %+  scan  (trip txt)
  %-  full
  (ifix [;~(plug gay fas-line) gay] (most gap tall:(vang | bon)))
::
--
::  assembly
::
|=  sys=path
|^
=;  tap=(trap vase)
  =/  nock  !.
    =>  [tap=tap ~]  !=
    $:tap
  ::
  [nock tap ~]
::
=/  sub=(trap vase)  !.  =>(..vase |.(*vase))
=.  sub  (build-sys sub %hoon)
=.  sub  (build-sys sub %arvo)
=.  sub  (build-sys sub %lull)
=/  zus  (build-sys sub %zuse)
=/  sock-tap=(trap vase)  (swat zus (mist /sur/sock/hoon sock))
::
=/  soak-tap=(trap vase)
  ~&  %soak
  %+  memo-call  swat
  :-  (swot sock-tap zus)
  (mist /lib/soak/hoon soak)
::
=/  noir-tap=(trap vase)
  ~&  %noir
  %+  memo-call  swat
  :-  (swot soak-tap zus)
  (mist /sur/noir/hoon noir)
::
=/  gene-tap=(trap vase)
  ~&  %gene
  %+  memo-call  swat
  :-  (swot noir-tap zus)
  (mist /sur/gene/hoon gene)
::
=/  skan-tap=(trap vase)
  ~&  %skan
  %+  memo-call  swat
  :-  :(swot (name gene-tap %gene) noir-tap zus)
  (mist /lib/skan/hoon skan)
::
=/  line-tap=(trap vase)
  ~&  %line
  %+  memo-call  swat
  :-  :(swot skan-tap (name gene-tap %gene) zus)
  (mist /lib/line/hoon line)
::
=/  vere-tap=(trap vase)
  %+  memo-call  swat
    ~&  %interface
  :-  :(swot (name line-tap %line-dor) (name skan-tap %skan) zus)
  (mist /lib/vere-interface/hoon vere-interface)
::
vere-tap
::
++  build-sys
  |=  [sub=(trap vase) nam=term]
  ^-  (trap vase)
  ~&  "interface: building /sys/{(trip nam)}"
  =/  src  .^(@t cx+(welp sys /[nam]/hoon))
  %-  need
  =>  [sub=sub src=src nam=nam ..ride]  !.
  %-  ~(mole vi |)  |.  =>  +
  ~>  %memo./user
  (swat sub (rain /sys/[nam]/hoon src))
--