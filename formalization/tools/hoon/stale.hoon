=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  fr=*
  :*  6  [0 6]  [2 [0 1] 2 [0 1] 0 22]
      8  [2 [10 [6 1 0] 0 1] 0 10]
      8  [2 [0 3] 1 fid]
      8  [2 [0 7] 0 2]
      7  [2 [0 15] 0 2]
      [0 1]  1  42
  ==
=/  s1=*  [[0 [fr [fw fm2]]] [0 0]]
=/  x=*   [[0 [fr [fw fm2]]] [1 1]]
=/  ref=toon  (mook (mink [x fr] ~))
~&  [%mink ?:(?=(%0 -.ref) [%0 =(p.ref [fw 42])] -.ref)]
::  a fresh core, straight on [x fr]
=/  fresh  -:(eval-top [x fr] ~)
~&  [%ska-fresh ?:(?=(%0 -.fresh) [%0 =(product.fresh [fw 42])] -.fresh)]
::  poke 1, then [x fr]
=^  p  ..poke  (poke [%full s1 fid])
~&  [%poke-1 ?=(^ p)]
=/  aft  -:(eval-top [x fr] ~)
~&  [%ska-after-poke-1 ?:(?=(%0 -.aft) [%0 =(product.aft [fw 42])] -.aft)]
0
