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
++  test-once-dabl
  =/  sub
    =>  ~
    !:
    |.
    =/  once  |=(@ +(+<))
    =/  dabl  =>  +  |=(@ +(+(+<)))
    =/  slam  |=(g=$-(@ @) |=(n=@ (g n)))
    [((slam once) 1) ((slam dabl) 1)]
  ::
  =/  fol  [9 2 0 1]
  (expect-eq-nock-need sub fol)
::
++  test-dec
  =/  sub
    !:
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
  =/  fol  [9 2 0 1]
  (expect-eq-nock-need sub fol)
:: ::
++  test-scow-playpen
  =/  sub  ..scow:playpen
  =/  fol
    =>  sub  !=
    (scow %ud 5)
  ::
  (expect-eq-nock-need sub fol)
::
++  test-scow-hoot
  =/  sub  ..scow:hoot
  =/  fol
    =>  sub  !=
    (scow %ud 5)
  ::
  (expect-eq-nock-need sub fol)
:: ::
++  test-parser
  =/  sub
    =>  ..ride:hoot
    |%
    ++  test  (expr-parse "33+3+4\\\0a/1+1+2")
    ++  expr-parse
      |=  math=tape
      (scan math expr)
      ::
    ++  expr
      %+  knee  *@ud
      |.  ~+
      ;~  pose
        ((slug add) lus ;~(pose dem expr))
        dem
      ==
    --
  ::
  =/  fol
    =>  sub  !=
    test
  ::
  (expect-eq-nock-need sub fol)
::
++  test-muk
  =/  sub  playpen
  =/  fol
    =>  sub  !=
    (muk 0xcafe.babe 1 42)  ::  XX 42 42 42 is a jet mismatch
  ::
  (expect-eq-nock-need sub fol)
::
++  test-y-comb
  =/  sub
    =>  ..add:hoot
    |%
    ++  y
      |*  [m1=mold m2=mold]
      |=  f=$-($-(m1 m2) $-(m1 m2))
      |=  x=m1
      ^-  m2
      ((f .) x)
    ::
    ++  fac-f
      |=  cont=$-(@ @)
      |=  x=@
      ^-  @
      ?:  =(x 0)  1
      (mul x (cont (dec x)))
    --
  ::
  =/  fol
    =>  sub  !=
    (((y @ @) fac-f) 5)
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
::  XX ~60 seconds to analyze, ~1000 s to run Nomm
::
:: ++  test-ream
::   =/  sub  hoot
::   =/  fol
::     =>  sub  !=
::     (ream '|=(* +<)')
::   ::
::   (expect-eq-nock-need sub fol)
::
:: ++  test-mint
::   =/  sub  hoot
::   =/  fol
::     =>  sub  !=
::     (~(mint ut [%atom %$ ~]) %noun [%dtls $+1])
::   ::
:: (expect-eq-nock-need sub fol)
--