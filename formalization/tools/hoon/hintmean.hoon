:: hintmean.hoon: %mean hints through +comp (README Gaps 25, lemmas/Compiler/CompRunHintMeanCheck.lean).
:: The style of hintdump.hoon.  For each case (a formula on a subject sock that knows nothing,
:: or a real gate on an unknown sample poked with [9 2 0 1]), for every entry of code.long-ska
:: new in this poke whose nomm holds a %mean hint (the nomm %mean or a dynamic %11 with tag %mean; for a formula
:: case also the root): the nomm, the raw blocks (before +optimize) of the whole-subject version
:: (+compiled-mono, mono &) and of the n-ary version (mono |), the formula of the bell, the
:: subjects run, and the table of the bells the nomm names (two levels): [bell pure nomm (unit need)], the need
:: of its n-ary version when compiled.  One
:: @ux jam of [nomm [need nargs blocks] [need nargs blocks] fol subs tab] per entry, the blocks
:: sorted by label; then per subject +mink's tone and that of the raw whole-subject code under
:: +eval-blob, with no scry gate and with the gate |=(^ ``[%v +<]).
=/  r=*  [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  ss=(list *)  ~[[1 2] [1 [2 3]] [[1 2] 3] [0 1] [[0 1] 0]]
=/  t1=*  [[1 [1 %leaf 120]] [0 1]]
=/  t2=*  [[1 [0 3]] [0 1]]
=/  t3=*  [[1 [4 [1 41]]] [0 1]]
=/  t4=*  [[1 [11 [%slog [1 0 %foo]] [1 7]]] [0 1]]
=/  t5=*  [[1 [0 6]] [[1 5] [0 1]]]
=/  t6=*  [[1 [0 7]] [[1 5] [0 1]]]
=/  t7=*  [[0 2] [0 1]]
=/  t8=*  [1 [[1 %leaf 120] 0]]
=/  t9=*  [[1 [0 0]] [0 1]]
=/  t10=*  [[1 [6 [3 [0 3]] [1 1] [1 2]]] [0 1]]
=/  t11=*  [[1 [8 [1 r] [9 2 [0 1]]]] [0 1]]
=/  b1=*  [4 [0 3]]
=/  b3=*  [6 [3 [0 3]] [1 1] [1 2]]
=/  b4=*  [[0 2] [6 [3 [0 3]] [0 2] [1 0]]]
=/  b5=*  [8 [1 r] [9 2 [0 1]]]
=/  b6=*  [11 [%spot [1 0]] [4 [0 3]]]
=/  mn  |=([t=* b=*] `*`[11 [%mean t] b])
=/  g1=*  =>  ~  !:  |=(a=* ~_([%leaf "foo"] ?@(a +(a) 0)))
=/  g2=*  =>  ~  !:  |=(a=* ~_([%leaf a] ?@(a +(a) 0)))
=/  g3=*  =>  ~  |=(a=* ~_([%leaf "foo"] ?@(a 0 [a a])))
=/  g4=*  =>  ~  !:  |=(a=* ?@(a 0 ~_([%leaf "rec"] +($(a +.a)))))
=/  g5=*  =>  ~  !:  |=(a=* ?@(a 0 ~_([%leaf a] +($(a +.a)))))
=/  cases=(list [nam=@tas sut=* fol=* gat=?])
  :~  [%m01 [| ~] (mn t1 b1) |]
      [%m02 [| ~] (mn t2 b1) |]
      [%m03 [| ~] (mn t3 b1) |]
      [%m04 [| ~] (mn t4 b1) |]
      [%m05 [| ~] (mn t5 b1) |]
      [%m06 [| ~] (mn t6 b1) |]
      [%m07 [| ~] (mn t7 b1) |]
      [%m08 [| ~] (mn t8 b1) |]
      [%m09 [| ~] (mn t9 b1) |]
      [%m10 [| ~] (mn t10 b1) |]
      [%m11 [| ~] (mn t11 b1) |]
      [%m12 [| ~] (mn t1 b3) |]
      [%m13 [| ~] (mn t2 b3) |]
      [%m14 [| ~] (mn t1 b4) |]
      [%m15 [| ~] (mn t2 b4) |]
      [%m16 [| ~] (mn t1 b5) |]
      [%m17 [| ~] (mn t2 b5) |]
      [%m18 [| ~] (mn t1 b6) |]
      [%m19 [| ~] (mn t2 b6) |]
      [%m20 [| ~] [6 [3 [0 2]] (mn t1 b1) [0 3]] |]
      [%m21 [| ~] [6 [3 [0 2]] [0 3] (mn t2 b1)] |]
      [%m22 [| ~] [11 [%spot [1 0]] (mn t1 b1)] |]
      [%m23 [| ~] [11 [%spot [1 0]] (mn t2 b1)] |]
      [%m24 [| ~] [(mn t1 b1) [0 2]] |]
      [%m25 [| ~] [[0 2] (mn t2 b1)] |]
      [%m26 [| ~] [7 (mn t1 [0 3]) [4 [0 2]]] |]
      [%m27 [| ~] [7 (mn t2 [0 3]) [4 [0 2]]] |]
      [%m28 [| ~] [10 [2 (mn t1 b1)] [0 1]] |]
      [%m29 [| ~] (mn t1 (mn t3 b1)) |]
      [%m30 [| ~] [6 (mn t1 [5 [0 2] [0 3]]) [1 0] [1 1]] |]
      [%m31 [| ~] [(mn t1 [6 [3 [0 2]] [4 [0 2]] [1 0]]) [0 3]] |]
      [%g01 [[& [| &]] g1] [9 2 0 1] &]
      [%g02 [[& [| &]] g2] [9 2 0 1] &]
      [%g03 [[& [| &]] g3] [9 2 0 1] &]
      [%g04 [[& [| &]] g4] [9 2 0 1] &]
      [%g05 [[& [| &]] g5] [9 2 0 1] &]
  ==
=/  hasm
  |=  n=*
  ^-  ?
  ?@  n  |
  ?^  -.n  |($(n -.n) $(n +.n))
  ?+  -.n  |
    %2   |($(n +<.n) $(n +>-.n))
    %3   $(n +.n)
    %4   $(n +.n)
    %5   |($(n +<.n) $(n +>.n))
    %6   |($(n +<.n) $(n +>-.n) $(n +>+.n))
    %7   |($(n +<.n) $(n +>.n))
    %10  |($(n +<+.n) $(n +>.n))
    %11  ?@(+<.n $(n +>-.n) |(=(%mean +<-.n) $(n +<+.n) $(n +>-.n)))
    %12  |($(n +<.n) $(n +>.n))
    %mean  &
  ==
=/  bels
  |=  n=*
  ^-  (list *)
  ?@  n  ~
  ?^  -.n  (weld $(n -.n) $(n +.n))
  ?+  -.n  ~
    %2   ;:(weld ?@(+>+.n ~ ~[+>+>-.n]) $(n +<.n) $(n +>-.n))
    %3   $(n +.n)
    %4   $(n +.n)
    %5   (weld $(n +<.n) $(n +>.n))
    %6   ;:(weld $(n +<.n) $(n +>-.n) $(n +>+.n))
    %7   (weld $(n +<.n) $(n +>.n))
    %10  (weld $(n +<+.n) $(n +>.n))
    %11  ?@(+<.n $(n +>-.n) (weld $(n +<+.n) $(n +>-.n)))
    %12  (weld $(n +<.n) $(n +>.n))
    %mean  ;:(weld ~[+>-.n] $(n +<.n) $(n +>+<.n))
  ==
=/  mk  |=([g=* s=*] ?>(?=([* * *] g) `*`[-.g s +>.g]))
=/  gul  |=(a=^ ``[%v a])
|-  ^-  @
?~  cases  0
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=/  old=(set *)  (silt (turn ~(tap by code.long-ska.state) |=([b=bell *] `*`b)))
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [;;(sock sut.i.cases) ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
=/  ent=(list [bell code-entry])  ~(tap by code.long-ska.state)
=/  cm=(map * code-entry)  (malt (turn ent |=([b=bell e=code-entry] [`*`b e])))
=/  sel=(list bell)
  %+  murn  ent
  |=  [b=bell e=code-entry]
  ?:  &(!(~(has in old) `*`b) |((hasm `*`nomm.e) &(!gat.i.cases =(`*`b `*`func))))
    `b
  ~
=/  subs=(list *)
  ?.  gat.i.cases  ss
  =/  g=*  +.sut.i.cases
  (turn ss |=(s=* (mk g s)))
|-
?~  sel  ^$(cases t.cases)
=/  b=bell  i.sel
=^  scc=(set bell)  sccs.cache.state
  (scc-of b calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono b scc)
=^  nar=straight  cache.state  (compiled-nary b scc)
=/  bl  (sort ~(tap by blocks.raw) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
=/  nb  (sort ~(tap by blocks.nar) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
=/  nom=*  nomm:(~(got by code.long-ska.state) b)
=/  b1=(list *)  (bels nom)
=/  b2=(list *)
  %-  zing
  %+  turn  b1
  |=  c=*
  =/  e  (~(get by cm) c)
  ?~  e  ~
  (bels `*`nomm.u.e)
=/  tab=(list *)
  %+  murn  ~(tap in (silt (weld b1 b2)))
  |=  c=*
  =/  e  (~(get by cm) c)
  ?~  e  ~
  =/  n  (~(get by nary.cache.state) ;;(bell c))
  `[c pure.u.e `*`nomm.u.e ?~(n ~ `need.u.n)]
~&  [%case nam.i.cases less=less.b mono=[need.raw n-args.raw (lent bl)] nary=[need.nar n-args.nar (lent nb)]]
~&  [%nomm nam.i.cases nom]
~&  [%jam nam.i.cases `@ux`(jam [nom [need.raw n-args.raw bl] [need.nar n-args.nar nb] fol.b subs tab])]
=/  s  subs
|-
?~  s  ^$(sel t.sel)
=/  a=tone  (mink [i.s fol.b] ~)
=/  bb
  %-  mule  |.
  -:(eval-blob [[[`@`0 `i.s] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ ~)
=/  a2=tone  (mink [i.s fol.b] gul)
=/  b2
  %-  mule  |.
  -:(eval-blob [[[`@`0 `i.s] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ gul)
~&  :*  %run  nam.i.cases  `*`i.s
        mink=`*`a
        ir=?:(?=(%| -.bb) %interpreter-crashed `*`p.bb)
        mink-g=`*`a2
        ir-g=?:(?=(%| -.b2) %interpreter-crashed `*`p.b2)
    ==
$(s t.s)
