::  BakeEnds, the normal-floor fix (track Q, README Gaps 31.7): the compiled
::  result of the library on the same subjects, to run with the plain library
::  and with the fixed copy (tools/gen/bakehalt_lib.py OUT --plain [--fix
::  normfloor]) and compare the lines:
::    RUNHOON_LIB=OUT runhoon.sh bakehalt-same.hoon 1200
::  One state: the pokes of bakehalt-tie.hoon (2), hinttab.hoon (16),
::  annots3.hoon (32, then its 16 repeats of hinttab's) and bakehalt-adv.hoon
::  (14).  Per poke: +ska-poke with its sock, the root compiled as +eval-top
::  does (+compiled-mono, +optimize), and per subject that fits the sock the
::  tone of +eval-blob against .* of the formula:
::    [%bh-poke nam variants (mug of the optimized code)]
::    [%bh-run nam k %same|%differ (mug of the IR product, or its tag)]
::  (%mu of the adversarial pokes recurses forever on every subject that fits:
::  poked, not run.)
=/  sam  |=([g=* s=*] ^-(* ?>(?=([* * *] g) [-.g s +>.g])))
=/  samples=(list *)  ~[0 [1 2] [[1 2] 3] [5 [6 7 0]]]
=/  gat  |=(g=* (turn samples |=(s=* (sam g s))))
=/  unk=(list *)  ~[0 5 [1 2] [[1 2] 3] [[1 2] [3 4]]]
::  bakehalt-tie.hoon
::
=/  tf=*  [1 0]
=/  tg=*  [1 1]
=/  thh=*  [tf tg]
=/  tfc=*  [[2 [0 1] [0 4]] [2 [0 1] [0 5]]]
=/  tjj=*  [6 [3 [0 2]] [[1 thh] [0 6]] [[1 thh] [0 7]]]
=/  tfx1=*  [2 tjj [1 tfc]]
=/  tfx2=*  [7 [0 1] tfx1]
=/  tfa1=*  [2 [0 1] [1 tfx1]]
=/  tfb5=*  [2 [0 1] [1 tfx2]]
=/  tfb4=*  [2 [0 1] [1 tfb5]]
=/  tfb3=*  [[2 [[0 2] [1 [5 7]]] [1 tfx2]] [2 [0 1] [1 tfb4]]]
=/  tfb2=*  [2 [0 1] [1 tfb3]]
=/  tfb1=*  [2 [0 1] [1 tfb2]]
=/  tf1=*  [2 [[1 thh] [0 1]] [1 tfc]]
=/  tf3=*  [[2 [[0 2] [1 [5 6]]] [1 tfx1]] [[2 [0 1] [1 tfa1]] [2 [0 1] [1 tfb1]]]]
::  hinttab.hoon
::
=/  hg1=*  =>  ~  !:  |=(a=* ?@(a 0 +($(a +.a))))
=/  hg2=*  =>  ~  !:  |=([a=* b=*] [b a])
=/  hg3=*  =>  ~  !:  |=(a=* ?@(a a $(a -.a)))
=/  hg4=*  =>  ~  !:  |=(a=* =/(b [a a] ?@(a b [+.a b])))
=/  hg5=*  =>  ~  !:  |=(a=* ?:(?=([* *] a) [$(a -.a) $(a +.a)] 7))
=/  hg6=*  =>  ~  !:  |=([a=* b=*] ?@(b a $(a [-.b a], b +.b)))
=/  hfw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  hfm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  hfid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 hfm2]
=/  hdec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  hint=(list [nam=@tas sut=* fol=* tst=(list *)])
  :~  [%hg1 [[& [| &]] hg1] [9 2 0 1] (gat hg1)]
      [%hg2 [[& [| &]] hg2] [9 2 0 1] (gat hg2)]
      [%hg3 [[& [| &]] hg3] [9 2 0 1] (gat hg3)]
      [%hg4 [[& [| &]] hg4] [9 2 0 1] (gat hg4)]
      [%hg5 [[& [| &]] hg5] [9 2 0 1] (gat hg5)]
      [%hg6 [[& [| &]] hg6] [9 2 0 1] (gat hg6)]
      [%hk1 [& 0] [4 0 1] ~[0]]
      [%hk2 [& [0 [hfid [hfw hfm2]]]] [0 0] ~[[0 [hfid [hfw hfm2]]]]]
      [%hk3 [& 5] [0 1] ~[5]]
      [%hk4 [& 7] hdec ~[7]]
      [%hk5 [& [0 [hfid [hfw hfm2]]]] hfid ~[[0 [hfid [hfw hfm2]]]]]
      [%hk6 [& 9] [6 [5 [0 1] 1 0] [1 0] 0 0] ~[9]]
      [%hk7 [& 3] [11 1.886.217.588 [1 0]] ~[3]]
      [%hk8 [& 4] [11 [1.886.217.588 1 1] 0 1] ~[4]]
      [%hk9 [& [0 [hfid [hfw hfm2]]]] [2 [0 1] 1 hfid] ~[[0 [hfid [hfw hfm2]]]]]
      [%hka [& [0 [hfw hfm2]]] [2 [0 1] 0 2] ~[[0 [hfw hfm2]]]]
  ==
::  annots3.hoon
::
=/  xk  |=(k=@ ^-(* ?:(=(0 k) [0 1] [4 $(k (dec k))])))
=/  g1=*   [2 [0 1] [1 [4 0 1]]]
=/  gb=*   [[2 [0 1] [1 [4 0 1]]] (xk 50)]
=/  k40=*  [[2 [0 1] [1 [4 0 1]]] (xk 40)]
=/  h=*    [[2 [0 1] [1 k40]] [0 1]]
=/  g2=*   [2 [0 1] [1 g1]]
=/  r=*    [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  g1c=*  [2 [0 3] [1 [4 0 1]]]
=/  g5=*   [5 [0 1] g1]
=/  g6=*   [8 [1 r] [9 2 [0 1]]]
=/  ma=*   [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*   [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  g7=*   [8 [1 [ma mb]] [9 4 [0 1]]]
=/  adec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  wit=*  [7 [6 [3 0 1] [1 0 0 1 0] [1 5]] [2 [0 1] [0 7]]]
=/  mk=*   [8 [1 g1] [1 k40] [0 1]]
=/  idc=*  [7 [[0 1] [2 [0 1] [1 [4 0 1]]]] [0 2]]
=/  v=*    [2 [0 1] [1 [0 3]]]
=/  t1=*   [5 [0 3] [1 [8 9]]]
=/  j1=*   [6 t1 [0 2] [[0 4] [0 5]]]
=/  lp=*   [8 [1 [9 2 0 1]] [9 2 0 1]]
=/  j3=*   [6 t1 [0 2] lp]
=/  j4=*   [6 [5 [0 4] [1 v]] [0 2] [[0 4] [0 5]]]
=/  f1=*   [7 j1 [2 [0 1] [0 2]]]
=/  f2=*   [7 j1 [2 [0 1] [6 [5 [1 0] [1 0]] [0 2] [0 2]]]]
=/  f3=*   [7 j3 [2 [0 1] [0 2]]]
=/  f4=*   [7 j4 [2 [0 1] [0 2]]]
=/  ann=(list [nam=@tas sut=* fol=* tst=(list *)])
  :~  [%u1 [| ~] [2 [0 1] [1 g1]] unk]
      [%u2 [| ~] [2 [0 1] [1 gb]] unk]
      [%u3 [| ~] [2 [0 1] [1 g2]] unk]
      [%u4 [| ~] [2 [0 1] [1 h]] unk]
      [%u5 [| ~] [8 [1 r] [9 2 [0 1]]] unk]
      [%u6 [| ~] [8 [1 [ma mb]] [9 4 [0 1]]] unk]
      [%u7 [| ~] [2 [0 1] [7 [0 1] [1 g1]]] unk]
      [%u8 [| ~] [11 [1.869.440.365 [1 0]] [2 [0 1] [1 g1]]] unk]
      [%u9 [| ~] [8 [1 g1c] [9 2 [0 1]]] unk]
      [%ua [| ~] [6 [3 0 1] [2 [0 1] [1 g1]] [[2 [0 1] [1 g2]] [0 1]]] unk]
      [%ub [| ~] [[2 [0 1] [1 g1]] [2 [0 1] [1 g1]]] unk]
      [%uc [| ~] [2 [0 1] [11 1.953.460.339 [1 g1]]] unk]
      [%ud [| ~] [2 [0 1] [1 g5]] unk]
      [%ue [| ~] [2 [0 1] [1 g6]] unk]
      [%uf [| ~] [2 [0 1] [1 g7]] unk]
      [%ug [| ~] [4 [2 [0 1] [1 h]]] unk]
      [%k1 [& 7] adec ~[7]]
      [%k2 [& [[ma mb] [1 2 3 4 5 6 0]]] [9 4 [0 1]] ~[[[ma mb] [1 2 3 4 5 6 0]]]]
      [%k3 [& 5] [2 [0 1] [1 g1]] ~[5]]
      [%k4 [& [g1c 3]] [9 2 [0 1]] ~[[g1c 3]]]
      [%v1 [| ~] [8 [1 k40] [2 [0 1] [0 2]]] unk]
      [%v2 [| ~] [8 [1 [4 0 1]] [2 [0 1] [[0 2] [0 2]]]] unk]
      [%v3 [| ~] [8 [1 k40] [2 [0 1] [11 1.953.460.339 [0 2]]]] unk]
      [%v4 [| ~] [8 [1 k40] [2 [0 1] [11 [1.953.460.339 [1 0]] [0 2]]]] unk]
      [%v5 [| ~] [7 [2 [0 1] [1 mk]] [2 [0 3] [0 2]]] unk]
      [%v6 [| ~] [8 [1 [k40 g1]] [2 [0 1] [0 5]]] unk]
      [%v7 [| ~] [8 [1 r] [7 [2 [0 1] [1 idc]] [9 2 [0 1]]]] unk]
      [%w1 [| ~] wit unk]
      [%j1 [& [[v 7] [8 9]]] f1 ~[[[v 7] [8 9]]]]
      [%j2 [& [[v 7] [8 9]]] f2 ~[[[v 7] [8 9]]]]
      [%j3 [& [[v 7] [8 9]]] f3 ~[[[v 7] [8 9]]]]
      [%j4 [& [[v 7] [8 9]]] f4 ~[[[v 7] [8 9]]]]
  ==
::  bakehalt-adv.hoon
::
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
=/  adv=(list [nam=@tas sut=* fol=*])
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
=/  advt=(list [nam=@tas sut=* fol=* tst=(list *)])
  %+  turn  adv
  |=  [nam=@tas sut=* fol=*]
  [nam sut fol ?:(=(%mu nam) ~ ?>(?=(^ sut) ~[+.sut]))]
=/  pokes=(list [nam=@tas sut=* fol=* tst=(list *)])
  ;:  weld
    ^-  (list [nam=@tas sut=* fol=* tst=(list *)])
    :~  [%p1 [| ~] tf1 unk]
        [%p3 [| ~] tf3 unk]
    ==
    hint
    ann
    hint
    advt
  ==
|-  ^-  @
?~  pokes  ~&  %bh-same-done  0
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [;;(sock sut.i.pokes) ?>(?=(^ fol.i.pokes) fol.i.pokes)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
=/  code=straight-out  (optimize raw)
~&  [%bh-poke nam.i.pokes variants=~(wyt by code.long-ska.state) code=(mug code)]
=/  blob  (~(got by blocks.code) 0w0)
=/  ts=(list *)  tst.i.pokes
=|  k=@ud
|-  ^-  @
?~  ts  ^$(pokes t.pokes)
=/  ref  (mule |.(.*(i.ts fol.i.pokes)))
=/  ir  (mule |.(-:(eval-blob [[[`@`0 `i.ts] ~ ~] ~] blob code ~ ~)))
=/  irp=*  ?:(?=(%| -.ir) %ir-crashed ?:(?=(%0 -.p.ir) [%0 product.p.ir] [-.p.ir ~]))
=/  refp=*  ?:(?=(%| -.ref) [%2 ~] [%0 p.ref])
~&  [%bh-run nam.i.pokes k ?:(=(irp refp) %same %differ) ?@(irp irp ?:(?=(%0 -.irp) (mug irp) irp))]
$(ts t.ts, k +(k))
