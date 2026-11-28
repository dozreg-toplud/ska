::  hintless.hoon (track J, README Gaps 24.24): hintdump3.hoon with the `less` of each bell.
::  Lines 19 on are those of hintdump3.hoon (the `!:` gates sit at the same lines and columns,
::  so their spots, bells and the ~(tap by code) order are the same: names t01..), with one
::  more print per entry: [%less j @ux], the jam of [less nomm] (the battery arm at the read
::  axis of an inlined call is in `less`).  tools/gen/hintless.py --lean OUT OUT2 writes
::  lemmas/Ska/CompHintXData.lean (OUT2 the output of hintmeanless.hoon).
::
::
::
::
::
::
::
::
::
::
::
::
=/  noax
  |=  n=*
  ^-  ?
  ?@  n  &
  ?^  -.n  &($(n -.n) $(n +.n))
  ?+  -.n  &
    %2   &($(n +<.n) $(n +>-.n))
    %3   $(n +.n)
    %4   $(n +.n)
    %5   &($(n +<.n) $(n +>.n))
    %6   &($(n +<.n) $(n +>-.n) $(n +>+.n))
    %7   &($(n +<.n) $(n +>.n))
    %10  &(!=(0 +<-.n) $(n +<+.n) $(n +>.n))
    %11  ?@(+<.n $(n +>-.n) &($(n +<+.n) $(n +>-.n)))
    %12  &($(n +<.n) $(n +>.n))
    %mean  &($(n +<.n) $(n +>+<.n))
  ==
=/  sfx
  |=  n=*
  ^-  ?
  ?@  n  &
  ?^  -.n  &($(n -.n) $(n +.n))
  ?+  -.n  &
    %6   &($(n +>-.n) $(n +>+.n))
    %7   $(n +>.n)
    %10  &(!=(0 +<-.n) $(n +<+.n) $(n +>.n))
    %11  $(n +>-.n)
    %mean  $(n +>+<.n)
  ==
=/  sfb
  |=  n=*
  ^-  (list *)
  ?@  n  ~
  ?^  -.n  (weld $(n -.n) $(n +.n))
  ?+  -.n  ~
    %2   ?@(+>+.n ~ [+>+>-.n ~])
    %6   (weld $(n +>-.n) $(n +>+.n))
    %7   $(n +>.n)
    %10  (weld $(n +<+.n) $(n +>.n))
    %11  $(n +>-.n)
    %mean  $(n +>+<.n)
  ==
=/  alb
  |=  n=*
  ^-  (list *)
  ?@  n  ~
  ?^  -.n  (weld $(n -.n) $(n +.n))
  ?+  -.n  ~
    %2   (weld ?@(+>+.n ~ [+>+>-.n ~]) (weld $(n +<.n) $(n +>-.n)))
    %3   $(n +.n)
    %4   $(n +.n)
    %5   (weld $(n +<.n) $(n +>.n))
    %6   :(weld $(n +<.n) $(n +>-.n) $(n +>+.n))
    %7   (weld $(n +<.n) $(n +>.n))
    %10  (weld $(n +<+.n) $(n +>.n))
    %11  ?@(+<.n $(n +>-.n) (weld $(n +<+.n) $(n +>-.n)))
    %12  (weld $(n +<.n) $(n +>.n))
    %mean  (weld $(n +<.n) $(n +>+<.n))
  ==
=/  dyn=(list @)  ~[%bout %xray %spin %jinx %live %hunk %hand %lose %mean %spot %slog]
=/  kept
  |=  n=*
  ^-  @ud
  ?@  n  0
  ?^  -.n  (add $(n -.n) $(n +.n))
  ?+  -.n  0
    %2   (add $(n +<.n) $(n +>-.n))
    %3   $(n +.n)
    %4   $(n +.n)
    %5   (add $(n +<.n) $(n +>.n))
    %6   :(add $(n +<.n) $(n +>-.n) $(n +>+.n))
    %7   (add $(n +<.n) $(n +>.n))
    %10  (add $(n +<+.n) $(n +>.n))
    %11
      ?@  +<.n
        (add ?:(|(=(%bout +<.n) =(%xray +<.n)) 1 0) $(n +>-.n))
      :(add ?:(?=(^ (find ~[+<-.n] dyn)) 1 0) $(n +<+.n) $(n +>-.n))
    %12  (add $(n +<.n) $(n +>.n))
    %mean  :(add 1 $(n +<.n) $(n +>+<.n))
  ==
=/  inc
  |=  n=*
  ^-  ?
  ?@  n  &
  ?^  -.n  &($(n -.n) $(n +.n))
  ?+  -.n  |
    %0   &
    %1   &
    %2   &(?|(?=(@ +>+.n) ?=(@ +>+>+.n)) $(n +<.n) $(n +>-.n))
    %3   $(n +.n)
    %4   $(n +.n)
    %5   &($(n +<.n) $(n +>.n))
    %6   &($(n +<.n) $(n +>-.n) $(n +>+.n))
    %7   &($(n +<.n) $(n +>.n))
    %10  &(!=(0 +<-.n) $(n +<+.n) $(n +>.n))
    %11  ?@(+<.n $(n +>-.n) &($(n +<+.n) $(n +>-.n)))
  ==
=/  g1=*  =>  ~  !:  |=(a=* ?@(a 0 +($(a +.a))))
=/  g2=*  =>  ~  !:  |=([a=* b=*] [b a])
=/  g3=*  =>  ~  !:  |=(a=* ?@(a a $(a -.a)))
=/  g4=*  =>  ~  !:  |=(a=* =/(b [a a] ?@(a b [+.a b])))
=/  g5=*  =>  ~  !:  |=(a=* ?:(?=([* *] a) [$(a -.a) $(a +.a)] 7))
=/  g6=*  =>  ~  !:  |=([a=* b=*] ?@(b a $(a [-.b a], b +.b)))
=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  pokes=(list [sut=* fol=*])
  :~  [[[& [| &]] g1] [9 2 0 1]]
      [[[& [| &]] g2] [9 2 0 1]]
      [[[& [| &]] g3] [9 2 0 1]]
      [[[& [| &]] g4] [9 2 0 1]]
      [[[& [| &]] g5] [9 2 0 1]]
      [[[& [| &]] g6] [9 2 0 1]]
      [[& 0] [4 0 1]]
      [[& [0 [fid [fw fm2]]]] [0 0]]
      [[& 5] [0 1]]
      [[& 7] dec]
      [[& [0 [fid [fw fm2]]]] fid]
      [[& 9] [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [[& 3] [11 1.886.217.588 [1 0]]]
      [[& 4] [11 [1.886.217.588 1 1] 0 1]]
      [[& [0 [fid [fw fm2]]]] [2 [0 1] 1 fid]]
      [[& [0 [fw fm2]]] [2 [0 1] 0 2]]
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
=|  i=@ud
|-  ^-  @
?~  pokes
  =/  ent=(list [bell code-entry])  ~(tap by code.long-ska.state)
  =/  cm=(map * code-entry)  (malt (turn ent |=([b=bell e=code-entry] [`*`b e])))
  =/  sel=(list [bell code-entry])  ent
  ~&  [%total (lent ent) (lent (skim ent |=([* e=code-entry] (lth 0 (kept `*`nomm.e)))))]
  =|  j=@ud
  |-
  ?~  sel  0
  =/  b=bell  -.i.sel
  =/  e=code-entry  +.i.sel
  =/  nom=*  nomm.e
  =/  b1=(list *)  (bels nom)
  =/  b2=(list *)
    %-  zing
    %+  turn  b1
    |=  c=*
    =/  f  (~(get by cm) c)
    ?~  f  ~
    (bels `*`nomm.u.f)
  =/  tab=(list *)
    %+  murn  ~(tap in (silt (weld b1 b2)))
    |=  c=*
    =/  f  (~(get by cm) c)
    ?~  f  ~
    =/  n  (~(get by nary.cache.state) ;;(bell c))
    `[c pure.u.f `*`nomm.u.f ?~(n ~ `need.u.n)]
  ~&  [%case +(j) less=less.b pure=pure.e total=total.e kept=(kept nom)]
  ~&  [%nomm +(j) nom]
  ~&  [%jam +(j) `@ux`(jam [nom fol.b tab])]
  ~&  [%less +(j) `@ux`(jam [`*`less.b nom])]
  $(sel t.sel, j +(j))
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [;;(sock sut.i.pokes) ?>(?=(^ fol.i.pokes) fol.i.pokes)] long-ska.state ~(key by jets-hot.state))
=/  ent=(list [bell code-entry])  ~(tap by code.long-ska.state)
=/  ks=(set *)  (silt (turn ent |=([b=bell *] `*`b)))
=/  bad=(list [@tas *])
  %-  zing
  %+  turn  ent
  |=  [b=bell e=code-entry]
  =/  n=*  nomm.e
  ;:  weld
    `(list [@tas *])`?:((noax n) ~ ~[[%nax `*`b]])
    `(list [@tas *])`?:((sfx n) ~ ~[[%sfx `*`b]])
    `(list [@tas *])`(murn (sfb n) |=(c=* ?:((~(has in ks) c) ~ `[`@tas`%sfb c])))
    `(list [@tas *])`(murn (alb n) |=(c=* ?:((~(has in ks) c) ~ `[`@tas`%alb c])))
  ==
=/  nk=@ud  (roll (turn ent |=([* e=code-entry] (kept `*`nomm.e))) add)
=/  ni=@ud  (lent (skim ent |=([* e=code-entry] (inc `*`nomm.e))))
=/  nh=@ud  (lent (skim ent |=([* e=code-entry] (lth 0 (kept `*`nomm.e)))))
~&  ?:((lth i 6) [%root i `*`nomm:(~(got by code.long-ska.state) func)] ~)
~&  ?:(=(i 0) [%all (turn ent |=([b=bell e=code-entry] [`*`b `*`nomm.e]))] ~)
~&  [%poke i %entries (lent ent) %kept-hints nk %entries-with-kept nh %in-class ni %bad bad]
$(pokes t.pokes, i +(i))
