:: hintdump2.hoon: the 39 formulas of hintdump.hoon through the whole pipeline (README Gaps 24):
:: (mook (mink [s f] gul)) against (eval-mook (eval-top [s f] gul)), toons with rendered traces,
:: optimized code (+trim-trace-hints included), on five subjects, with no scry gate and with a gate.
=/  lib  .
=/  r=*  [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  ss=(list *)  ~[[1 2] [1 [2 3]] [[1 2] 3] [0 1] [[0 1] 0]]
=/  cases=(list [nam=@tas fol=*])
  :~  [%s01 [11 %bout [0 3]]]
      [%s02 [11 %spot [0 3]]]
      [%s03 [11 %foo [4 [0 3]]]]
      [%s04 [[11 %bout [0 2]] [0 3]]]
      [%s05 [4 [11 %xray [0 3]]]]
      [%s06 [11 %bout [7 [0 3] [4 [0 1]]]]]
      [%s07 [7 [11 %bout [0 3]] [4 [0 2]]]]
      [%d01 [11 [%spot [1 [1 2] 3]] [0 3]]]
      [%d02 [11 [%spot [0 2]] [4 [0 3]]]]
      [%d03 [11 [%slog [1 0 %foo]] [0 3]]]
      [%d04 [11 [%memo [0 2]] [4 [0 3]]]]
      [%d05 [11 [%foo [0 2]] [4 [0 3]]]]
      [%d06 [11 [%foo [1 7]] [4 [0 3]]]]
      [%d07 [11 [[1 2] [0 2]] [4 [0 3]]]]
      [%d08 [11 [%hunk [0 2]] [4 [0 3]]]]
      [%d09 [11 [%xray [0 2]] [4 [0 3]]]]
      [%d10 [11 [%spot [1 0]] [11 [%spot [1 1]] [4 [0 3]]]]]
      [%d11 [[11 [%spot [1 0]] [4 [0 2]]] [11 [%spot [1 1]] [4 [0 3]]]]]
      [%d12 [7 [11 [%spot [1 0]] [0 3]] [4 [0 2]]]]
      [%d13 [7 [11 [%spot [1 0]] [[0 2] [0 3]]] [4 [0 2]]]]
      [%d14 [7 [0 3] [11 [%spot [0 1]] [4 [0 1]]]]]
      [%d15 [5 [11 [%spot [1 0]] [0 2]] [0 3]]]
      [%d16 [6 [11 [%spot [0 2]] [5 [0 2] [0 3]]] [1 0] [1 1]]]
      [%d17 [6 [3 [0 2]] [11 [%spot [1 0]] [4 [0 2]]] [11 [%spot [1 1]] [4 [0 3]]]]]
      [%d18 [11 [%spot [0 2]] [6 [0 3] [1 1] [1 2]]]]
      [%d19 [4 [11 [%spot [1 0]] [4 [0 3]]]]]
      [%d20 [10 [2 [11 [%spot [1 0]] [4 [0 3]]]] [0 1]]]
      [%d21 [11 [%spot [1 0]] [2 [0 3] [0 2]]]]
      [%d22 [11 [%spot [1 0]] [8 [1 r] [9 2 [0 1]]]]]
      [%d23 [11 [%spot [0 6]] [0 3]]]
      [%m01 [11 [%mean [1 [1 %leaf 120]]] [4 [0 3]]]]
      [%m02 [11 [%mean [[1 [1 %leaf 120]] [0 1]]] [4 [0 3]]]]
      [%m03 [11 [%mean [[1 [0 3]] [0 1]]] [4 [0 3]]]]
      [%m04 [7 [11 [%mean [[1 [1 %leaf 120]] [0 1]]] [0 3]] [4 [0 2]]]]
      [%c01 [12 [1 %ref] [1 %path]]]
      [%c02 [12 [0 2] [0 3]]]
      [%c03 [[12 [1 1] [0 2]] [0 3]]]
      [%c04 [12 [1 0] [11 [%spot [1 0]] [0 3]]]]
      [%c05 [4 [12 [0 2] [0 3]]]]
  ==
=/  runs=(list [nam=@tas fol=* sub=*])
  (zing (turn cases |=([nam=@tas fol=*] (turn ss |=(s=* [nam fol s])))))
=/  gul  |=(a=^ ``[%v a])
=/  bad=@ud  0
=/  n=@ud  0
|-  ^-  @
?~  runs  ~&([%done %runs n %bad bad] bad)
=/  a=toon  (mook (mink [sub fol]:i.runs ~))
=^  ton=tone  ..^poke  (eval-top [sub fol]:i.runs ~)
=^  b=toon  ..^poke  (eval-mook ton)
=/  a2=toon  (mook (mink [sub fol]:i.runs gul))
=^  ton2=tone  ..^poke  (eval-top [sub fol]:i.runs gul)
=^  b2=toon  ..^poke  (eval-mook ton2)
=/  ok  &(=(a b) =(a2 b2))
~?  !ok  [nam.i.runs %differ sub=sub.i.runs mock=a ska=b mock-g=a2 ska-g=b2]
~?  &(ok ?=(%2 -.a) ?=(^ p.a))  [nam.i.runs %same-trace sub=sub.i.runs (lent p.a) a]
$(runs t.runs, n (add 2 n), bad ?:(ok bad +(bad)))
