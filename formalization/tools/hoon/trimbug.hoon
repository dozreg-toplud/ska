::  the witness against +trim-trace-hints: two nested trace hints whose clue
::  is the same register (the subject, after +alias) have one key, so the
::  inner epilogue closes both and a crash inside the outer hint after it
::  sees no open key; both hints are dropped and the outer frame is lost
::
=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%w-spot 0 [11 [%spot 0 1] [11 [%spot 0 1] 1 5] 0 0]]
      [%w-spot-seven 0 [11 [%spot 0 1] 7 [11 [%spot 0 1] 1 5] 0 0]]
      [%w-mean 0 [11 [%mean 0 1] [11 [%mean 0 1] 1 5] 0 0]]
      [%w-mean-spot 0 [11 [%mean 0 1] [11 [%spot 0 1] 1 5] 0 0]]
      [%w-inc [0 0] [11 [%spot 0 1] [[11 [%spot 0 1] 1 5] 4 0 1]]]
      [%w-inc-atom 7 [11 [%spot 0 1] [[11 [%spot 0 1] 1 5] 4 0 1]]]
      [%w-axis [1 2] [11 [%spot 0 2] [11 [%spot 0 2] 1 5] 0 0]]
      [%w-const 0 [11 [%spot 1 0] [11 [%spot 1 0] 1 5] 0 0]]
  ==
|-  ^-  @
?~  cases  0
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=/  ton=tone  -:(eval-top [sub fol]:i.cases ~)
=/  b=toon  -:(eval-mook ton)
~&  [nam.i.cases ?:(=(a b) %same %differ) mock=a ska=b]
$(cases t.cases)
