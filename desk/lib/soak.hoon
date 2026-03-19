/-  *sock
:: =/  check-soak
::   :*  reg=~
::       :: norm=~
::   ==
|%
::  operations on $cape
++  ca
  |_  one=cape
  ++  hed  ?@(one one -.one)
  ++  tel  ?@(one one +.one)
  ::  normalization
  ::
  ++  cut
    ^-  cape
    ?@  one  one
    =/  l  cut(one -.one)
    =/  r  cut(one +.one)
    ?:  &(?=(@ l) =(l r))  ~&  %cut-ca-norm  l
    [l r]
  ::  list of known axes
  ::
  ++  yea
    ^-  (list @)
    =/  axe  1
    |-  ^-  (list @)
    ?-  one
      %|  ~
      %&  ~[axe]
      ^  (weld $(one -.one, axe (peg axe 2)) $(one +.one, axe (peg axe 3)))
    ==
  ::    cape intersection
  ::
  ::  intersect two capes
  ++  int
    |=  two=cape
    ^-  cape
    ?:  =(one two)  one  ::  not important
    ?-  one
        %|  %|
        %&  two
        ^
      ?-  two
          %|  %|
          %&  one
          ^
        =/  l   $(one -.one, two -.two)
        =/  r   $(one +.one, two +.two)
        ?:(?&(?=(@ l) =(l r)) l [l r])
      ==
    ==
  ::    apply a cape as a mask to a sock
  ::  
  ::  mask unknown axes in a cape out of a sock
  ++  app
    |=  know=sock
    ^-  sock
    ?:  =(one cape.know)  know  ::  not important
    ?:  |(?=(%| one) ?=(%| cape.know))  lost:so
    ?:  ?=(%& one)  know
    ~+  ::  helps with backtracking?
    %-  ~(knit so $(know ~(hed so know), one -.one))
    $(know ~(tel so know), one +.one)
  ::    union two capes
  ::
  ::  
  ++  uni
    |=  two=cape
    ^-  cape
    ?:  =(one two)  one  ::  load-bearing
    ?-  one
        %&  &
        %|  two
        ^
      ?-  two
          %&  &
          %|  one
          ^ 
        =/  l  $(one -.one, two -.two)
        =/  r  $(one +.one, two +.two)
        ?:(&(?=(@ l) =(l r)) l [l r])
      ==
    ==
  ::    Added axes?
  ::
  ::  big returns true if any subaxis of a masked axis in one
  ::  is unmasked in two. Note that this is not an ordering relation as
  ::  it is not antisymmetric
  ++  big
    |=  two=cape
    ^-  ?
    ?-  one
        %&  |
        %|  ?@(two two ?|($(two -.two) $(two +.two)))
        ^
      ?@  two  ?|($(one -.one) $(one +.one))
      ?|($(one -.one, two -.two) $(one +.one, two +.two))
    ==
  ::    non-null?
  ::
  ::  true if there are any unmasked axes
  ::  XX by virtue of normalization this should be just equivalent to ?=(?(%& ^) one)
  ++  any
    ^-  ?
    :: ?@  one  one
    :: ?|(any(one -.one) any(one +.one))
    ?=(?(%& ^) one)
  ::    push a cape down to an axis
  ::
  ::  this builds a path described by the input axis with one at the
  ::  bottom
  ++  pat
    |=  axe=@
    ?<  =(0 axe)
    ?:  ?=(%| one)  |
    |-  ^-  cape
    ?:  =(1 axe)  one
    ?-  (cap axe)
      %2  [$(axe (mas axe)) |]
      %3  [| $(axe (mas axe))]
    ==
  ::    split a cape
  ::
  ::  assume a cape will be applied to a cell,
  ::  and provide capes for the head and tail of the cell.
  ++  rip
    ^-  [cape cape]
    ?^  one  one
    [one one]
  ::    poke a hole in a cape
  ::
  ::  mask an axis out of a cape, and return a cape
  ::  describing which subaxes were unmasked
  ++  awl
    |=  axe=@
    ?<  =(0 axe)
    |-  ^-  [cape cape]
    ?:  ?=(%| one)  [| |]
    ?:  =(1 axe)  [one |]
    ?-  (cap axe)
        %2
      ?-  one
          %&
        =/  [p=cape t=cape]  $(axe (mas axe))
        [p t &]
      ::
          ^
        =/  [p=cape t=cape]  $(axe (mas axe), one -.one)
        [p t +.one]
      ==
    ::
        %3
      ?-  one
          %&
        =/  [p=cape t=cape]  $(axe (mas axe))
        [p & t]
      ::
          ^
        =/  [p=cape t=cape]  $(axe (mas axe), one +.one)
        [p -.one t]
      ==
    ==
  ::    compose
  ::
  ::  `one` is original need, `two` is need of `one`
  ::
  ++  cmp
    |=  two=cape
    ^-  cape
    !!
  --
::  operations on sock
++  so
  |_  one=sock
  ::  empty sock
  ::
  ++  lost  [| ~]
  ::    valid?
  ++  apt
    |-  ^-  ?
    ?@  cape.one
      &
    ?@  data.one
      |
    ?&  $(cape.one -.cape.one, data.one -.data.one)
        $(cape.one +.cape.one, data.one +.data.one)
    ==
  ::    normalize
  ::  throw away unknown axes in data (setting to ~)
  ++  norm
    |-  ^-  sock
    =-  =>  !@  norm:check-soak  .
            :: ~?  >>>  !=(- one)  %norm-so  .
            ?:  !=(- one)  ~|  [- one]  !!  .
        -
    ?-  cape.one
        %|  lost
        %&  one
        ^
      ?>  ?=(^ data.one)
      =/  l  $(cape.one -.cape.one, data.one -.data.one)
      =/  r  $(cape.one +.cape.one, data.one +.data.one)
      ?:  ?&(=(& cape.l) =(& cape.r))
        [& data.l data.r]
      ?:  ?&(=(| cape.l) =(| cape.r))
        lost
      [[cape.l cape.r] data.l data.r]
    ==
  ::    nesting
  ::
  ::  roughly, 1 < 2
  ::
  ::  every axis known in one is also known in 2, with equal data
  ::
  ++  huge
    !@  check-soak  huge2
    |=  two=sock
    ^-  ?
    =/  a  (huge1 two)
    =/  b  (huge2 two)
    ?>  =(a b)
    a
  ::
  ++  huge1
    |=  two=sock
    ^-  ?
    ?:  =(one two)  &
    ?:  ?=(%| cape.one)  &
    ?:  ?=(%& cape.one)
      ::  either cape.two is not %.y or data.one != data.two
      ::  either way, two does not nest
      ::
      |
    ?:  ?=(%| cape.two)  |
    &($(one hed, two hed(one two)) $(one tel, two tel(one two)))
  ::
  ++  huge2
    |=  two=sock
    ^-  ?
    ?|  =(one two)
        ?@  data.one
          ?.  ?=(@ cape.one)  ~|  badone+one  !!
          ?.  cape.one  &
          ?&(?=(@ cape.two) cape.two =(data.one data.two))
        ?@  data.two
          ?>  ?=(@ cape.two)
          ?<  ?=(%| cape.one)
          |
        =/  [lope=cape rope=cape]
          ?:(?=(^ cape.one) cape.one [cape.one cape.one])
        ::
        =/  [loop=cape roop=cape]
          ?:(?=(^ cape.two) cape.two [cape.two cape.two])
        ::
        ?&  $(one [lope -.data.one], two [loop -.data.two])
            $(one [rope +.data.one], two [roop +.data.two])
        ==
    ==
  ::    axis
  ::
  ++  pull
    |=  axe=@
    ?<  =(0 axe)
    |-  ^-  sock
    ?:  =(1 axe)  one
    ?:  |(?=(%| cape.one) ?=(@ data.one))
      lost
    =+  [now lat]=[(cap axe) (mas axe)]
    ?@  cape.one
      ?-  now
        %2  $(axe lat, data.one -.data.one)
        %3  $(axe lat, data.one +.data.one)
      ==
    ?-  now
      %2  $(axe lat, data.one -.data.one, cape.one -.cape.one)
      %3  $(axe lat, data.one +.data.one, cape.one +.cape.one)
    ==
  ::    axis present?
  ::
  ++  find
    |=  axe=@
    ?<  =(0 axe)
    |-  ^-  ?
    ?:  =(1 axe)  &
    ?:  |(?=(%| cape.one) ?=(@ data.one))
      |
    =+  [now lat]=[(cap axe) (mas axe)]
    ?@  cape.one
      ?-  now
        %2  $(axe lat, data.one -.data.one)
        %3  $(axe lat, data.one +.data.one)
      ==
    ?-  now
      %2  $(axe lat, data.one -.data.one, cape.one -.cape.one)
      %3  $(axe lat, data.one +.data.one, cape.one +.cape.one)
    ==
  ::    pair
  ::
  ::  takes a pair of socks to a sock of a pair.
  ++  knit
    |=  two=sock
    ^-  sock
    =*  l  cape.one
    =*  r  cape.two
    =/  cap  ?:(&(?=(@ l) =(l r)) l [l r])
    ?:  ?=(%| cap)  lost
    [cap data.one data.two]
  ::
  ++  hed
    ^-  sock
    ?:  |(?=(%| cape.one) ?=(@ data.one))
      lost
    ?@  cape.one  [& -.data.one]
    [-.cape.one -.data.one]
  ::
  ++  tel
    ^-  sock
    ?:  |(?=(%| cape.one) ?=(@ data.one))
      lost
    ?@  cape.one  [& +.data.one]
    [+.cape.one +.data.one]
  ::    intersect
  ::
  ::  output is unmasked only where both one and two are unmasked and
  ::  they both agree in data
  ++  purr
    |=  two=sock
    |-  ^-  sock
    ?:  =(one two)  one  ::  helps a bit
    ?:  |(?=(%| cape.one) ?=(%| cape.two))  lost
    ?:  |(?=(^ cape.one) ?=(^ cape.two))
      %-  %~  knit  so
          $(one hed, two hed(one two))
      $(one tel, two tel(one two))
    |-  ^-  sock
    ?:  =(data.one data.two)  one
    ?:  |(?=(@ data.one) ?=(@ data.two))  lost
    %-  %~  knit  so
        $(data.one -.data.one, data.two -.data.two)
    $(data.one +.data.one, data.two +.data.two)
  ::    union
  ::
  ::  take the union of two socks, but crash if they disagree on a known
  ::  axis
  ++  pack
    |=  two=sock
    ^-  sock
    !.
    |-  ^-  sock
    ?:  =(one two)  one
    ?:  ?=(%| cape.one)  two
    ?:  ?=(%| cape.two)  one
    ::  unequal known data
    ::
    ?:  &(?=(%& cape.one) ?=(%& cape.two))  !!
    %-  %~  knit  so
        (pack(one hed) hed(one two)) 
    (pack(one tel) tel(one two))
  ::    edit
  ::
  ::  update mask and data at an axis into a sock
  ++  darn
    !@  check-soak  darn1
    |=  [axe=@ two=sock]
    ^-  sock
    =*  sam  +<
    =/  a  (darn1 sam)
    =/  b  (darn2 sam)
    ?:  =(a b)  a
    |-
    ?:  |(?=(^ cape.a) ?=(^ cape.b))
      (~(knit so $(a ~(hed so a), b ~(hed so b))) $(a ~(tel so a), b ~(tel so b)))
    ?:  |(?=(%| cape.a) ?=(%| cape.b))
      ~|  a
      ~|  b
      !!
    ?:  |(?=(@ data.a) ?=(@ data.b))
      ?:  =(data.a data.b)  lost
      ~|  a
      ~|  b
      !!
    (~(knit so $(a ~(hed so a), b ~(hed so b))) $(a ~(tel so a), b ~(tel so b)))
  ::
  ++  darn1
    |=  [axe=@ two=sock]
    ^-  sock
    ?:  =(1 axe)  two
    ?:  &(?=(%| cape.one) ?=(%| cape.two))  lost
    =|  acc=(list (pair ?(%2 %3) sock))
    |-  ^-  sock
    ?.  |(=(1 axe) &(=(| cape.one) =(| cape.two)))
      ?-  (cap axe)
          %2  $(one hed, acc [[%2 tel] acc], axe (mas axe))
          %3  $(one tel, acc [[%3 hed] acc], axe (mas axe))
      ==
    |-  ^-  sock
    ?~  acc  two
    ?-  p.i.acc
      %2  $(two (~(knit so two) q.i.acc), acc t.acc)
      %3  $(two (~(knit so q.i.acc) two), acc t.acc)
    ==
  ::
  ++  darn2
    |=  [axe=@ two=sock]
    ?<  =(0 axe)
    |-  ^-  sock
    =-  norm(one -)
    ?:  =(1 axe)  two
    =+  [now lat]=[(cap axe) (mas axe)]
    ?^  cape.one
      ?-  now
        %2  =/  n  $(axe lat, one [-.cape -.data]:one)
            [[cape.n +.cape.one] data.n +.data.one]
      ::
        %3  =/  n  $(axe lat, one [+.cape +.data]:one)
            [[-.cape.one cape.n] -.data.one data.n]
      ==
    ?:  &(cape.one ?=(^ data.one))
      ?-  now
        %2  =/  n  $(axe lat, data.one -.data.one)
            :-  ?:(?=(%& cape.n) & [cape.n &])
            [data.n +.data.one]
      ::
        %3  =/  n  $(axe lat, data.one +.data.one)
            :-  ?:(?=(%& cape.n) & [& cape.n])
            [-.data.one data.n]
      ==
    =/  n  $(axe lat)
    ?-  now
      %2  [[cape.n |] data.n ~]
      %3  [[| cape.n] ~ data.n]
    ==
  --
::    apt assertion
::
::  assert a sock is apt:so
++  sap
  |=  know=sock
  ?>  ~(apt so know)
  know
--