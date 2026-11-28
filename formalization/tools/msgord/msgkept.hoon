::  +msg-need-ord-kept (2a5b618) on the real library: run with
::  RUNHOON_LIB=<a worktree at 2a5b618 or later>/desk/lib/nock-compilation.hoon
::  The three steps of the old cycle (msgreal.hoon, msgOrd_cycle) now climb
::  (kept_cycle_stops), the non-canonical entry [[%none ~] [%none ~]] falls to
::  [%none ~] (kept_noncanon), and plain +msg-need-ord regrows %this (msgOrd_falls).
=/  btt=need-ordered  [%both [%this ~] [%this ~]]
=/  big=need-ordered  [%both btt btt]
=/  c=cape  [[| |] [| |]]
~&  [%kept-cycle (msg-need-ord-kept btt [%this ~] c) (msg-need-ord-kept big btt c) (msg-need-ord-kept [%this ~] big c)]
~&  [%kept-noncanon (msg-need-ord-kept [%none ~] [[%none ~] [%none ~]] c)]
~&  [%msg-falls (msg-need-ord btt [%this ~] c)]
~&  [%kept-deep (msg-need-ord-kept [[%this ~] [%this ~]] [[%this ~] [%both [%this ~] [%this ~]]] |)]
0
