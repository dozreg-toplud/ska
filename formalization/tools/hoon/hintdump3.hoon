::  hintdump3.hoon (track J, README Gaps 24): the real `!:` entries for the class tally.
::  The pokes of hinttab.hoon (6 `!:` gates on an unknown sample, then the 10 %full pokes
::  of flagsdump.hoon); after the last poke, for every entry of code.long-ska, in
::  ~(tap by code) order (kept = its number of kept hints: static %bout %xray, a
::  dynamic tag, or %mean): [%case name less pure total kept], [%nomm name nomm] and one @ux jam of
::  [nomm formula table], formula = fol of the bell, table = [bell pure nomm (unit need)]
::  of the bells the nomm names (two levels, as hintmean.hoon builds it); then
::  [%total entries kept-entries].  Below: the text of hinttab.hoon.
::  hinttab.hoon: the table condition of comp_run_hint_tab (README Gaps 25):
::  after each of 16 pokes in a row (6 `!:` gates on an unknown sample, then
::  the 10 %full pokes of flagsdump.hoon), over every entry of code.long-ska:
::  nax  Bake.NoAx0 of the nomm (no %10 at axis 0 anywhere),
::  sfx  SfNoAx0 (none on the product path),
::  sfb  every callee on the product path (sfBells) has an entry,
::  alb  every direct call anywhere, under hints too (hintBells), has an entry,
::  and, as information, the kept hints (static %bout %xray, or a dynamic tag)
::  and whether the nomm is in HintOkC (no %12, %mean, memo key, axis 0).
::  The nomms are walked as raw nouns.
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
