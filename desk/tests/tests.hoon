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
::  creates an unreachable loop? (which is fine if it is truly unreachable, 
::  but in that case I wonder what the linearizer will generate...)
::
++  test-tree-functions  
  =/  sub
    =>  hoot
    :_  .
    =-  ~&(-< -)
    ^-  m=(map @ $-(@ @))
    %-  malt
    ^-  (list [@ $-(@ @)])
    :~  0+dec
        1+succ
        2+|=(@ +<)
    ==
  ::
  =/  fol
   =>  sub  !=
   =/  key  0
   =/  sam  42
   |-  ^-  @
   ?~  m  !!
   ?:  =(key p.n.m)  (q.n.m sam)
   ?:  (gor key p.n.m)  $(m l.m)
   $(m r.m)
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