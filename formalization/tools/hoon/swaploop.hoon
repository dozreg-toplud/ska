::  The witness of the pass-loop bug fixed in 1813f09 (lemmas/Ska/PassLoop.lean).
::  The function [&+[F [1 0] [1 0]] F] calls itself with its sample swapped (the
::  same identity, both halves being [1 0]) and calls that call's product as a
::  formula.  Before the fix, once the product was |+~ the second call was
::  indirect, and the less-code of the one member alternated between [& [& |]]
::  and [& [| &]] through the swap, so every pass changed the entry and +poke
::  never answered.  Since 1813f09 less-code is united with the previous run's
::  and the poke returns.
::
=/  fx=*  [6 [3 0 6] [0 6] [2 [1 0] [2 [[0 2] [0 7] [0 6]] [0 2]]]]
~&  %poke-start
=^  p  ..poke  (poke [%full [fx [1 0] [1 0]] fx])
~&  [%poke-returned ?=(^ p)]
0
