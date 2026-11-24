::  variant key collision: poke 1 (bakedrop's witness) leaves the dead
::  variant [s H] of H's code bell at axis 4 = [1 7], s = [[& |] [[[3 0] 5] ~]].
::  poke 2 calls H live at the site sock s, where H's code bell requires
::  axis 4 = [3 0], so its bake is s again: new-code skips [s H], and the
::  call runs the dead variant's code.
=/  lib  .
=/  f1=^  [7 [1 [[[2 [6 [1 0] [[1 [[3 0] 5]] [9 5 0 1]] [1 [[[1 7] 5] 9]]] [1 [2 [0 1] [0 4]]]] [8 [9 4 0 1] [9 5 0 3]]] 0]] [9 4 0 1]]
=/  x=*  =>  lib  !=((dec 40))
=/  f2=^  [7 [[1 [[3 0] 5]] x] [2 [0 1] [1 [2 [0 1] [0 4]]]]]
=/  a=toon  (mook (mink [lib f2] ~))
=^  p1  ..^poke  (poke:..^poke [%full lib f1])
=^  t=tone  ..^poke  (eval-top [lib f2] ~)
=^  b=toon  ..^poke  (eval-mook t)
~&  [%after-witness ?:(=(a b) %same [%differ mock=a ska=b])]
0
