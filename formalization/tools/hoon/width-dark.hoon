::  two `done` entries of one formula pass the hit test at one sock (track F, Gaps 16 (c)):
::  F = [2 [0 3] [0 2]] runs the formula at axis 2 of its subject.  e1 = F at [[1 c] 5]: a direct
::  (inlined) call, less-code knows axis 2.  e2 = F at [7 5]: axis 2 an atom, an indirect call,
::  dark, so indi is empty and less-code knows nothing.  At [[1 c] 6] both pass: the answer is
::  the first in tap order: c (e1) or unknown (e2).  The root R calls F at the three socks and
::  itself through a %6 whose test is unknown, so its loop has a second pass.
=/  n=@ud  0
|-  ^-  @
?:  =(n 12)  0
=/  c=@  (add 100 n)
=/  f=^  [2 [0 3] [0 2]]
=/  a=^  :+  [2 [1 [1 c] 5] [1 f]]
             [2 [1 [1 c] 6] [1 f]]
         [2 [1 7 5] [1 f]]
=/  r=^  [6 [0 6] a [2 [0 1] [0 2]]]
~&  [%pm-case n %dark c]
=/  res  (ska-callgraph [[[& |] [r 0]] r] ~ [~ ~ ~ ~ ~])
~&  [%dark-graph n ~(wyt by -.res)]
$(n +(n))
