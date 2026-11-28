:: medemink2.hoon (track I, 2026-11-28): +eval-top against +mink on w20 w21 w22 of sccreal.py --extra (the atom of a soft
:: call made by %4 / %5 / %3: +collapse-lazy-atom asks through +crash-need).  Run: tools/hoon/runhoon.sh tools/hoon/medemink2.hoon 300
:: (30 subjects, returning and crashing: all the same, [%done %bad 0]).  Built from the coordinator's medemink-2026-11-28.hoon.
=/  cases=(list [nam=@tas gat=*])
  :~  :-  %w20  =>  ~  |=(s=[i=@ j=* k=*] |-(?:(.=(i.s 9) -.j.s $(i.s .+(i.s), j.s .+(i.s), k.s -.j.s))))
      :-  %w21  =>  ~  |=(s=[i=@ j=* k=*] |-(?:(.=(i.s 9) -.j.s $(i.s .+(i.s), j.s .=(i.s 3), k.s -.j.s))))
      :-  %w22  =>  ~  |=(s=[i=@ j=* k=*] |-(?:(.=(i.s 9) -.j.s $(i.s .+(i.s), j.s .?(k.s), k.s -.j.s))))
  ==
=/  subs=(list [nam=@tas sub=*])
  :~
      [%w20 [0 [9 [1 2] 3]]]
      [%w20 [0 [8 [1 2] 3]]]
      [%w20 [0 [7 [1 2] 3]]]
      [%w20 [0 [9 5 3]]]
      [%w20 [0 [9 [[1 2] 3] [4 5]]]]
      [%w20 [0 [8 [[1 2] 3] [4 5]]]]
      [%w20 [0 [5 [[1 2] [3 4]] [[5 6] 7]]]]
      [%w20 [0 [9 [[1 2] [3 4]] 0]]]
      [%w20 [0 [8 5 3]]]
      [%w20 [0 [2 [1 2] 3]]]
      [%w21 [0 [9 [1 2] 3]]]
      [%w21 [0 [8 [1 2] 3]]]
      [%w21 [0 [7 [1 2] 3]]]
      [%w21 [0 [9 5 3]]]
      [%w21 [0 [9 [[1 2] 3] [4 5]]]]
      [%w21 [0 [8 [[1 2] 3] [4 5]]]]
      [%w21 [0 [5 [[1 2] [3 4]] [[5 6] 7]]]]
      [%w21 [0 [9 [[1 2] [3 4]] 0]]]
      [%w21 [0 [8 5 3]]]
      [%w21 [0 [2 [1 2] 3]]]
      [%w22 [0 [9 [1 2] 3]]]
      [%w22 [0 [8 [1 2] 3]]]
      [%w22 [0 [7 [1 2] 3]]]
      [%w22 [0 [9 5 3]]]
      [%w22 [0 [9 [[1 2] 3] [4 5]]]]
      [%w22 [0 [8 [[1 2] 3] [4 5]]]]
      [%w22 [0 [5 [[1 2] [3 4]] [[5 6] 7]]]]
      [%w22 [0 [9 [[1 2] [3 4]] 0]]]
      [%w22 [0 [8 5 3]]]
      [%w22 [0 [2 [1 2] 3]]]
  ==
=/  bad=@ud  0
|-  ^-  @
?~  subs  ~&([%done %bad bad] bad)
=/  gat=*
  =/  c  cases
  |-  ?~  c  !!  ?:  =(nam.i.c nam.i.subs)  gat.i.c  $(c t.c)
=/  fol=*  [8 [1 gat] [9 2 [10 [6 [0 7]] [0 2]]]]
=/  a=toon  (mook (mink [sub.i.subs fol] ~))
=^  ton=tone  ..^poke  (eval-top [sub.i.subs fol] ~)
=^  b=toon  ..^poke  (eval-mook ton)
~&  ?:  =(a b)  [nam.i.subs %same sub.i.subs ?:(?=(%2 -.a) [%2 (lent p.a)] ?:(?=(%0 -.a) a a))]
    [nam.i.subs %differ mock=a ska=b]
$(subs t.subs, bad ?:(=(a b) bad +(bad)))

