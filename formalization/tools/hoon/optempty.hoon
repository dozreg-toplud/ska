::  +optimize on a straight with no blocks (track P, README Gaps 23):
::  +bb-topo reads block 0 with +got:by, so the gate crashes.  The link
::  `OptLink` stated for every straight is false of the pill's +optimize.
=/  emp=straight  [[%this ~] 1 ~]
=/  one=straight  [[%this ~] 1 (~(put by *(map @uwoo blob)) `@uwoo`0 [~ ~ [%don `@uvre`0]])]
~&  [%empty-blocks -:(mule |.((optimize emp)))]
~&  [%one-block -:(mule |.((optimize one)))]
0
