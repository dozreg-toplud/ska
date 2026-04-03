/+  *test, *skan,  playpen, hoot
::
=/  expect-eq-nock-need
  |=  [sub=* fol=*]
  ^-  tang
  ?~  mol=(mole |.(.*(sub fol)))
    ~[leaf+"bad test"]
  :: (expect-eq !>(mol) !>((run-nomm sub fol)))
  (expect-eq !>(mol) !>((run-nomm-1 sub fol)))
::
|%
++  test-provoke-infinite-loop
  ::  I had an idea that building a growing noun of gates that were called
  ::  (so, a growing noun of code) would provoke an infinite loop in SKA as
  ::  the recursive iterations would not be recognised by the recursive call
  ::  condition
  ::
  ::  XX turns out I am wrong. Why?
  ::
  =/  sub  ..add:hoot
  =/  fol
    =>  sub  !=
    =/  l=*  [mul add]
    =+  .*(-.l [9 2 0 1])
    =+  .*(+.l [9 2 0 1])
    =/  c  0
    =<  even
    |%
    ++  even
      ?:  =(c 100)  ~
      =.  l  [add l]
      =+  .*(-.l [9 2 0 1])
      odd(c +(c))
    ::
    ++  odd
      =.  l  [mul l]
      =+  .*(-.l [9 2 0 1])
      even(c +(c))
    --
  ::
  (expect-eq-nock-need sub fol)
::
++  test-ack
  =/  cor
    =>  ..dec:hoot
    |=  [m=@ n=@]
    ^-  @
    ?:  =(0 m)  +(n)
    ?:  =(0 n)  $(m (dec m), n 1)
    $(m (dec m), n $(n (dec n)))
  ::
  =/  fol
    =>  cor  !=
    (. 3 4)
  ::
  (expect-eq-nock-need cor fol)
::
++  test-abet
  =/  cor
    =>  ..dec:hoot
    =+  c=0
    |%
    ++  this  .
    ++  add
      |=  n=@
      ^+  this
      =-  this.+(c c.-)
      ?~  n  this
      $(c +(c), n (dec n))
    ::
    ++  foo
      =>  (add 42)
      this(c +(c))
    --
  ::
  =/  fol
    =>  cor  !=
    foo
  ::
  (expect-eq-nock-need cor fol)
::
++  test-curr
  =/  sub
    =>  ..add:hoot
    |=  a=@
    |=  b=@
    |=  c=@
    |=  d=@
    :(add a b c d)
  ::
  =/  fol
    =>  sub  !=
    ((((. 1) 2) 3) 4)
  ::
  (expect-eq-nock-need sub fol)
::  XX ~60 seconds to analyze, ~1000 s to run Nomm
::
:: ++  test-ream
::   =/  sub  hoot
::   =/  fol
::     =>  sub  !=
::     (ream '|=(* +<)')
::   ::
::   (expect-eq-nock-need sub fol)
:: ::
:: ++  test-mint
::   =/  sub  hoot
::   =/  fol
::     =>  sub  !=
::     (~(mint ut [%atom %$ ~]) %noun [%dtls $+1])
::   ::
:: (expect-eq-nock-need sub fol)
--