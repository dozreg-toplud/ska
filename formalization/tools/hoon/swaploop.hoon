::  The pass loop of +analyze does not end on this poke (lemmas/Ska/PassLoop.lean).
::  The function [&+[F [1 0] [1 0]] F] calls itself with its sample swapped (the
::  same identity, both halves being [1 0]) and calls that call's product as a
::  formula.  Once the product is |+~ the second call is indirect, and the
::  less-code of the one member alternates between [& [& |]] and [& [| &]]
::  through the swap, so every pass changes the entry.  With the sample not
::  swapped ([[0 2] [0 6] [0 7]]) the poke answers at once.
::
=/  fx=*  [6 [3 0 6] [0 6] [2 [1 0] [2 [[0 2] [0 7] [0 6]] [0 2]]]]
~&  %poke-start
=^  p  ..poke  (poke [%full [fx [1 0] [1 0]] fx])
~&  [%poke-returned ?=(^ p)]
0
