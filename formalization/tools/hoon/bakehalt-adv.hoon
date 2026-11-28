::  BakeEnds step 1 (track Q, README Gaps 31): pokes meant to stress the
::  worklist of +bake-graph, in one state (vars from earlier pokes count for
::  +pick).  Run against the copy of tools/gen/bakehalt_lib.py (with --cap):
::  RUNHOON_LIB=OUT.hoon runhoon.sh bakehalt-adv.hoon 900.  Cases:
::  %dl  a walker of a list whose spine is known to depth n and whose heads
::       are not: each re-bake of the walker loses one level (n = 10, 40);
::  %sw  a two-sample gate that swaps its samples, one known deep, one not;
::  %mu  two arms calling each other, each passing a different known part;
::  %fd  a %6 whose test reads a part of the sample the meet loses;
::  %ce  a callee whose callers' knowledge descends (a chain of three gates).
=/  spine
  |=  n=@
  ^-  [c=* d=*]
  ?:  =(0 n)  [& 0]
  =/  r  $(n (dec n))
  [[| c.r] [0 d.r]]
=/  deep
  |=  n=@
  ^-  [c=* d=*]
  ?:  =(0 n)  [| 0]
  =/  r  $(n (dec n))
  [[& c.r] [n d.r]]
=/  deepf
  |=  n=@
  ^-  [c=* d=*]
  ?:  =(0 n)  [| 0]
  =/  r  $(n (dec n))
  [[& c.r] [[1 n] d.r]]
=/  gfl=*  =>  ~  !:  |=(a=* ?@(a 0 [.*(0 -.a) $(a +.a)]))
=/  mf=*
  =>  ~  !:
  =<  ma
  |%
  ++  ma  |=(a=* ?@(a 0 [.*(0 -.a) (mb +.a)]))
  ++  mb  |=(a=* ?@(a 1 [.*(1 -.a) (ma +.a)]))
  --
=/  gdl=*  =>  ~  !:  |=(a=* ?@(a 0 $(a +.a)))
=/  gsw=*  =>  ~  !:  |=([a=* b=*] ?@(a b $(a b, b +.a)))
=/  gfd=*  =>  ~  !:  |=([a=* b=*] ?:(=(a 0) b $(a +.a, b [a b])))
=/  gce=*  =>  ~  !:  |=(a=* =/(f |=(b=* ?@(b 0 $(b +.b))) =/(g |=(c=* ?@(c 1 (f +.c))) ?@(a 2 (g +.a)))))
=/  mu=*
  =>  ~  !:
  =<  ma
  |%
  ++  ma  |=(a=* ?@(a 0 (mb +.a)))
  ++  mb  |=(a=* ?@(a 1 (ma [a a])))
  --
=/  core  |=([g=* c=* d=*] ^-([* *] [[& [c &]] [-.g [d +>.g]]]))
=/  s10  (spine 10)
=/  s40  (spine 40)
=/  d20  (deep 20)
=/  d30  (deep 30)
=/  d40  (deep 40)
=/  f10  (deepf 10)
=/  f40  (deepf 40)
=/  pokes=(list [nam=@tas sut=* fol=*])
  :~  [%fl10 (core gfl c.f10 d.f10) [9 2 0 1]]
      [%fl40 (core gfl c.f40 d.f40) [9 2 0 1]]
      [%fl40k (core gfl & d.f40) [9 2 0 1]]
      [%mf40 (core mf c.f40 d.f40) [9 2 0 1]]
      [%mf40k (core mf & d.f40) [9 2 0 1]]
      [%dl10 (core gdl (spine 10)) [9 2 0 1]]
      [%dl40 (core gdl (spine 40)) [9 2 0 1]]
      [%dd40 (core gdl (deep 40)) [9 2 0 1]]
      [%sw (core gsw [c.d20 |] [d.d20 0]) [9 2 0 1]]
      [%sw2 (core gsw [c.d20 c.d20] [d.d20 d.d20]) [9 2 0 1]]
      [%fd (core gfd [c.d20 |] [d.d20 0]) [9 2 0 1]]
      [%ce (core gce c.d30 d.d30) [9 2 0 1]]
      [%mu (core mu c.d30 d.d30) [9 2 0 1]]
      [%dl40b (core gdl c.s40 d.s40) [9 2 0 1]]
  ==
|-  ^-  @
?~  pokes  0
~&  [%bh-case nam.i.pokes]
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [;;(sock sut.i.pokes) ?>(?=(^ fol.i.pokes) fol.i.pokes)] long-ska.state ~(key by jets-hot.state))
$(pokes t.pokes)
