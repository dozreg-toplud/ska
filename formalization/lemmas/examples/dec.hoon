:: Based on desk/tests/tests.hoon ++test-dec.
:-  %say  |=  *  :-  %noun
::
=/  dec-core
  !.
  =>  ~
  |.
  %.  3
  |=  n=@
  ^-  @
  ?<  =(0 n)
  =/  c  0
  |-  ^-  @
  ?:  =(+(c) n)  c
  $(c +(c))
::
=/  dec-call  [9 2 0 1]
[dec-core dec-call]
