::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::    This document is an implementation of the Subject Knowledge Analysis (SKA)
::    pipeline in Hoon, first described by Edward Amsden ~ritpub-sipsyl. It
::    took inspiration from an unfinished implementation by him and Joe Bryan
::    ~master-morzod, which can be found on GitHub in the "sword" repository.
::    It also serves as a documentation and explanation piece: the problem being
::    solved here is unusual and in my opinion quite complicated, and developing
::    the implementation took a lot of experimentation, and it would be a waste
::    not to describe why certain design choices were made, as some of them are
::    crucial for the algorithm to work at reasonable speed.
::
::    Large blocks of comments can be found interspersed in code below.  At the
::    end of this section you will find a table of contents with chapters and
::    the line number.
::
::    But first of all, what kind of problem is being solved here?
::
::    Nock, unlike conventional languages, does not have a notion of a "code
::    object", or a "function", or any other construct that corresponds to known
::    callable code.  Nock 2 formula [2 b c], and Nock 9 by extension as it is
::    just a macro for Nock 2, is equivalent to "eval" in other languages and is
::    reduced like this:
::
::      *[a 2 b c]          *[*[a b] *[a c]]
::
::    That is, we evaluate `c` against the original subject `a`, and reduce the
::    product of that reduction with *[a b] as our new subject.  Nock is
::    expressive enough for *[a c] to be unknowable in the general case without
::    actually running the code. 
::
::    But while it is unknowable in the general case, in practice we can almost
::    always know in advance what formula will be evaluated.  That is because
::    in practice the formula-formula `c` is almost always:
::      - a Nock 0, with the formula being pulled from the known subject (think
::        desugaring of Nock 9),
::      - or a Nock 1, with the formula being a constant/quoted value (think |-
::        loops, where the formula does not come from the subject but is instead
::        quoted into the outer formula).
::
::    This fact allows us to introduce the notion of a *SKA function* object,
::    which is identified by a Nock formula and a masked subject.  The mask
::    includes only the code that could be used by the SKA function, either by
::    itself or transitively by its callees.  A SKA function can use any Nock
::    operations, including raw Nock 2 when *[a c] could not be deduced (an
::    indirect Nock call), but it can also call other SKA functions.
::
::    Once the function call graph is obtained with partial evaluation of the given
::    subject/formula pair, the next step is to discover which parts of the
::    subject are actually used as data by each function.  Without it each
::    function can only be thought of as a function (noun -> noun), which leads
::    to unnecessary busywork when it comes to function calls - the entire
::    subject of a callee would have to be consed up, for it to be deconstructed
::    later by the callee.
::
::    Finally, when the functions and their subject axis usages are known,
::    each function can be compiled to a linear SSA form, allowing further
::    optimizations and eventually efficient execution.
::
::  Table of contents:
::    Call graph construction:  line 595
::    Axis usage analysis:      line X
::    Compilation:              line X
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Compilation flags. Uncomment to enable
::
::  check-soak: test partial noun functions by running two implementations
::  norm:check-soak: check for normalization
::
:: =/  check-soak
::   :*  reg=~
::       :: norm=~
::   ==
::  ska verbosity
::
=/  ska-verb
  :*  ~
      p-bars=&
      f-bars=|
      p-file=|
  ==
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
=*  stub  ~|(%stub !!)
::  Partial noun definitions
::
|%
::  Noun mask. Strongly normalized:
::    [& &] -> &
::    [| |] -> |
::
+$  cape  $~(| $@(? [cape cape]))
::  masked noun. Strongly normalized:
::    "|" leaves of the cape must correspond to 0 leaves in the data
::
::
+$  sock  $~(|+~ [=cape data=*])
::  Provenance of data from the subject of a Nock computation we are in.
::    ~: does not come from the subject.
::    @: comes from that axis of the subject
::    ^: provenance of a cell
::
+$  spring  *
--
::  Partial noun logic.  Self-explanatory for the most part, but take note of
::  equality shortcircuits and ~+ memoization: this is the closest we can get
::  in Nock to pointer equality shortcircuits, which are load-bearing if we
::  consider the degree to which nouns tend to be duplicated in the standard
::  library, with around 4e-12 bits per noun:
::
::    %+  div:rq  (sun:rq (met 0 (jam ..zuse)))
::    %-  sun:rq
::    =/  n=*  ..zuse
::    |-  ^-  @
::    ?@  n  1
::    ~+  .+
::    (add $(n -.n) $(n +.n))
::  
::
|%
::  Operations on capes
::
++  ca
  |%
  ::  head
  ::
  ++  hed  |=(c=cape ?@(c c -.c))
  ::  tail
  ::
  ++  tel  |=(c=cape ?@(c c +.c))
  ::  normalization
  ::
  ++  cut
    |=  c=cape
    ^-  cape
    ?@  c  c
    =/  l  $(c -.c)
    =/  r  $(c +.c)
    ?:  &(?=(@ l) =(l r))  ~&  %cut-ca-norm  l
    [l r]
  ::  list of known axes
  ::
  ++  yea
    |=  c=cape
    ^-  (list @)
    =/  axe  1
    |-  ^-  (list @)
    ?-  c
      %|  ~
      %&  ~[axe]
      ^  (weld $(c -.c, axe (peg axe 2)) $(c +.c, axe (peg axe 3)))
    ==
  ::  intersection
  ::
  ++  int
    |=  [a=cape b=cape]
    ^-  cape
    ?:  =(a b)  a
    ?-  a
        %|  %|
        %&  b
        ^
      ?-  b
          %|  %|
          %&  a
          ^
        =/  l   $(a -.a, b -.b)
        =/  r   $(a +.a, b +.b)
        ?:(?&(?=(@ l) =(l r)) l [l r])
      ==
    ==
  ::  apply mask to a partial noun
  ::
  ++  app
    |=  [c=cape s=sock]
    ^-  sock
    ?:  =(c cape.s)  s
    ?:  |(?=(%| c) ?=(%| cape.s))  *sock
    ?:  ?=(%& c)  s
    ~+
    %+  knit:so  $(s (hed:so s), c -.c)
    $(s (tel:so s), c +.c)
  ::  union
  ::
  ++  uni
    |=  [a=cape b=cape]
    ^-  cape
    ?:  =(a b)  a
    ?-  a
        %&  &
        %|  b
        ^
      ?-  b
          %&  &
          %|  a
          ^ 
        =/  l  $(a -.a, b -.b)
        =/  r  $(a +.a, b +.b)
        ?:(&(?=(@ l) =(l r)) l [l r])
      ==
    ==
  ::  push a cape to an axis
  ::
  ++  pat
    |=  [c=cape a=@]
    ^-  cape
    ?<  =(0 a)
    ?:  ?=(%| c)  |
    |-  ^-  cape
    ?:  =(1 a)  c
    ?-  (cap a)
      %2  [$(a (mas a)) |]
      %3  [| $(a (mas a))]
    ==
  --
::  Operations on socks
::
++  so
  |%
  ::  normalized?
  ::
  ++  apt
    |=  sock
    ^-  ?
    ?@  cape  &
    ?@  data  |
    ?&  $(cape -.cape, data -.data)
        $(cape +.cape, data +.data)
    ==
  ::  normalize
  ::
  ++  norm
    |=  s=sock
    ^-  sock
    =-  =>  !@  norm:check-soak  .
            ?:  !=(- s)  ~|  [- s]  !!  .
        -
    ?-  cape.s
        %|  *sock
        %&  s
        ^
      ?>  ?=(^ data.s)
      =/  l  $(cape.s -.cape.s, data.s -.data.s)
      =/  r  $(cape.s +.cape.s, data.s +.data.s)
      ?:  ?&(=(& cape.l) =(& cape.r))
        [& data.l data.r]
      ?:  ?&(=(| cape.l) =(| cape.r))
        *sock
      [[cape.l cape.r] data.l data.r]
    ==
  ::  Does b nest under a? i.e. is everything that is known by a also known
  ::  by b?
  ::
  ++  huge
    !@  check-soak  huge2
    |=  [a=sock b=sock]
    ^-  ?
    =/  x  (huge1 a b)
    =/  y  (huge2 a b)
    ?>  =(x y)
    x
  ::
  ++  huge1
    |=  [one=sock two=sock]
    ^-  ?
    ?:  =(one two)  &
    ?:  ?=(%| cape.one)  &
    ?:  ?=(%& cape.one)
      ::  either cape.two is not %.y or data.one != data.two
      ::  either way, two does not nest
      ::
      |
    ?:  ?=(%| cape.two)  |
    &($(one (hed one), two (hed two)) $(one (tel one), two (tel two)))
  ::
  ++  huge2
    |=  [one=sock two=sock]
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
    ::  axis of a partial noun, never fails
    ::
    ++  pull
      |=  [s=sock axe=@]
      ^-  sock
      ?<  =(0 axe)
      |-  ^-  sock
      ?:  =(1 axe)  s
      ?:  |(?=(%| cape.s) ?=(@ data.s))
        *sock
      =+  [now lat]=[(cap axe) (mas axe)]
      ?@  cape.s
        ?-  now
          %2  $(axe lat, data.s -.data.s)
          %3  $(axe lat, data.s +.data.s)
        ==
      ?-  now
        %2  $(axe lat, data.s -.data.s, cape.s -.cape.s)
        %3  $(axe lat, data.s +.data.s, cape.s +.cape.s)
      ==
    ::  axis present?
    ::
    ++  find
      |=  [s=sock axe=@]
      ^-  ?
      ?<  =(0 axe)
      |-  ^-  ?
      ?:  =(1 axe)  &
      ?:  |(?=(%| cape.s) ?=(@ data.s))
      |
    =+  [now lat]=[(cap axe) (mas axe)]
    ?@  cape.s
      ?-  now
        %2  $(axe lat, data.s -.data.s)
        %3  $(axe lat, data.s +.data.s)
      ==
    ?-  now
      %2  $(axe lat, data.s -.data.s, cape.s -.cape.s)
      %3  $(axe lat, data.s +.data.s, cape.s +.cape.s)
    ==
  ::  cons
  ::
  ++  knit
    |=  [one=sock two=sock]
    ^-  sock
    =*  l  cape.one
    =*  r  cape.two
    =/  cap  ?:(&(?=(@ l) =(l r)) l [l r])
    ?:  ?=(%| cap)  *sock
    [cap data.one data.two]
  ::  head
  ::
  ++  hed
    |=  s=sock
    ^-  sock
    ?:  |(?=(%| cape.s) ?=(@ data.s))
      *sock
    ?@  cape.s  [& -.data.s]
    [-.cape.s -.data.s]
  ::  tail
  ::
  ++  tel
    |=  s=sock
    ^-  sock
    ?:  |(?=(%| cape.s) ?=(@ data.s))
      *sock
    ?@  cape.s  [& +.data.s]
    [+.cape.s +.data.s]
  ::  intersect - output is unmasked only where both one and two are unmasked
  ::  and they both agree in data
  ::
  ++  purr
    |=  [one=sock two=sock]
    ^-  sock
    ?:  =(one two)  one
    ?:  |(?=(%| cape.one) ?=(%| cape.two))  *sock
    ?:  |(?=(^ cape.one) ?=(^ cape.two))
      %+  knit  $(one (hed one), two (hed two))
      $(one (tel one), two (tel two))
    |-  ^-  sock
    ?:  =(data.one data.two)  one
    ?:  |(?=(@ data.one) ?=(@ data.two))  *sock
    %+  knit  $(data.one -.data.one, data.two -.data.two)
    $(data.one +.data.one, data.two +.data.two)
  ::  union - take the union of two socks, crashing if they disagree on a known
  ::  axis
  ::
  ++  pack
    |=  [one=sock two=sock]
    ^-  sock
    ?:  =(one two)  one
    ?:  ?=(%| cape.one)  two
    ?:  ?=(%| cape.two)  one
    ::  unequal known data
    ::
    ?:  &(?=(%& cape.one) ?=(%& cape.two))  !!
    ~+
    %+  knit
      $(one (hed one), two (hed two))
    $(one (tel one), two (tel two))
  ::  edit
  ::
  ++  darn
    !@  check-soak  darn1
    |=  [one=sock axe=@ two=sock]
    ^-  sock
    =*  sam  +<
    =/  a  (darn1 sam)
    =/  b  (darn2 sam)
    ?:  =(a b)  a
    |-
    ?:  |(?=(^ cape.a) ?=(^ cape.b))
      (knit $(a (hed a), b (hed b)) $(a (tel a), b (tel b)))
    ?:  |(?=(%| cape.a) ?=(%| cape.b))
      ~|  a
      ~|  b
      !!
    ?:  |(?=(@ data.a) ?=(@ data.b))
      ?:  =(data.a data.b)  *sock
      ~|  a
      ~|  b
      !!
    (knit $(a (hed a), b (hed b)) $(a (tel a), b (tel b)))
  ::
  ++  darn1
    |=  [one=sock axe=@ two=sock]
    ^-  sock
    ?:  =(1 axe)  two
    ?:  &(?=(%| cape.one) ?=(%| cape.two))  *sock
    =|  acc=(list (pair ?(%2 %3) sock))
    |-  ^-  sock
    ?.  |(=(1 axe) &(=(| cape.one) =(| cape.two)))
      ?-  (cap axe)
          %2  $(one (hed one), acc [[%2 (tel one)] acc], axe (mas axe))
          %3  $(one (tel one), acc [[%3 (hed one)] acc], axe (mas axe))
      ==
    |-  ^-  sock
    ?~  acc  two
    ?-  p.i.acc
      %2  $(two (knit two q.i.acc), acc t.acc)
      %3  $(two (knit q.i.acc two), acc t.acc)
    ==
  ::
  ++  darn2
    |=  [one=sock axe=@ two=sock]
    ?<  =(0 axe)
    |-  ^-  sock
    =-  (norm -)
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
::  Operations on provenance
::
++  pi
  |%
  ++  cons
    |=  [a=spring b=spring]
    ^-  spring
    ?:  &(?=(~ a) ?=(~ b))  ~
    [a b]
  ::
  ++  hed
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 2)
    -.pin
  ::
  ++  tel
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 3)
    +.pin
  ::
  ++  prune
    |=  [pin=spring cap=cape]
    ^-  cape
    ?:  ?=(%| cap)  |
    ?~  pin  |
    ~+
    ?@  pin  (pat:ca cap pin)
    =/  [p=cape q=cape]  ?@(cap [& &] cap)
    =/  l  $(pin -.pin, cap p)
    =/  r  $(pin +.pin, cap q)
    (uni:ca l r)
  ::
  ++  slot
    |=  [pin=spring ax=@]
    ^-  spring
    ?:  =(ax 1)  pin
    ?~  pin  ~
    ?@  pin  (peg pin ax)
    ?-  (cap ax)
      %2  $(pin -.pin, ax (mas ax))
      %3  $(pin +.pin, ax (mas ax))
    ==
  ::
  ++  compose
    |=  [a=spring b=spring]
    ^-  spring
    ?~  b  ~
    |-  ^-  spring
    ?~  a  ~
    ~+
    ?@  a  (slot b a)
    (cons $(a -.a) $(a +.a))
  ::
  ++  edit
    |=  [rec=spring ax=@ don=spring]
    ^-  spring
    ?:  =(ax 1)  don
    ?:  &(?=(~ rec) ?=(~ don))  ~
    =|  tack=(list [c=?(%2 %3) p=spring])
    |-  ^-  spring
    ?.  =(1 ax)
      ?-  (cap ax)
        %2  $(ax (mas ax), rec (hed rec), tack [2+(tel rec) tack])
        %3  $(ax (mas ax), rec (tel rec), tack [3+(hed rec) tack])
      ==
    |-  ^-  spring
    ?~  tack  don
    ?-  c.i.tack
      %2  $(don (cons don p.i.tack), tack t.tack)
      %3  $(don (cons p.i.tack don), tack t.tack)
    ==
  --
::  distribute noun usage along provenance
::
++  distribute
  |=  [c=cape s=spring]
  ^-  cape
  ?~  s  |
  ?:  ?=(%| c)  |
  ~+
  ?@  s  (pat:ca c s)
  =/  [p=cape q=cape]  ?@(c [& &] c)
  =/  l  $(s -.s, c p)
  =/  r  $(s +.s, c q)
  (uni:ca l r)
::  doubly intersect a sock and a provenance
::
++  double-int
  |=  [a=[=sock src=spring] b=[=sock src=spring]]
  ^-  [=sock src=spring]
  ?:  =(a b)  a
  ?:  |(?=(%| cape.sock.a) ?=(%| cape.sock.b))
    [*sock *spring]
  ?.  |(?=(^ cape.sock.a) ?=(^ cape.sock.b) ?=(^ src.a) ?=(^ src.b))
    [*sock *spring]
  ~+
  =/  h
    %=  $
      sock.a  (hed:so sock.a)
      sock.b  (hed:so sock.b)
      src.a   (hed:pi src.a)
      src.b   (hed:pi src.b)
    ==
  ::
  =/  t
    %=  $
      sock.a  (tel:so sock.a)
      sock.b  (tel:so sock.b)
      src.a   (tel:pi src.a)
      src.b   (tel:pi src.b)
    ==
  ::
  [(knit:so sock.h sock.t) (cons:pi src.h src.t)]
--
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Call graph construction
::
::    With partial noun logic defined, we can move to the description of call
::    graph construction. The overall goal is, given a pair of a subject and a
::    formula, to construct:
::      - a code subject mask, which describes code requirements of the SKA
::        function,
::      - a call graph, with that SKA function being the root.
::      - a code + data subject mask, which would be used to cache the analysis
::        result. Data mask is necessary due to potential subject capture by the
::        function.
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
?>  =(|+~ *sock)
?>  =(| *cape)
?>  =(~ *spring)
|%
+$  identity  [more=sock fol=^]  ::  max subject
+$  bell      [bus=sock fol=^]   ::  minimized subject
+$  nomm
  $^  [nomm nomm]
  $%  [%1 p=*]
      [%2 p=nomm q=nomm info=(unit bell)]
      [%3 p=nomm]
      [%4 p=nomm]
      [%5 p=nomm q=nomm]
      [%6 p=nomm q=nomm r=nomm]
      [%7 p=nomm q=nomm]
      [%10 p=[p=@ q=nomm] q=nomm]
      [%11 p=$@(@ [p=@ q=nomm]) q=nomm body=*]
      [%12 p=nomm q=nomm]
      [%0 p=@]
  ==
+$  spring  *  ::  no union stuff
+$  datum
  $:  callees=(set [seat=(unit spot) =identity src=spring])
      =nomm
      less-code=sock
      less-memo=sock
      indirect-code-request=cape
      [prod=sock map=spring]
      area=(unit spot)
  ==
::
+$  callgraph  (map identity datum)
+$  jug-id  (jug identity identity)
+$  worklist  (set identity)
+$  memo  (map ^ (map sock [id=identity =datum]))  ::  fol -> less-memo -> entry
::
++  recursive-match
  |=  [kid=identity par=identity g=callgraph]
  ^-  (unit datum)
  ?.  =(fol.kid fol.par)  ~
  =/  d=datum  (git-g g par)
  ?:  (huge:so less-code.d more.kid)  `d
  ~
::
++  recursive-call
  ~%  %recursive-call  ..zuse  ~
  |=  [id-caller=identity id-kid=identity called-by=jug-id g=callgraph]
  ^-  (unit [id=identity d=datum])
  =|  visited=(set identity)
  =/  callers=(set identity)  [id-caller ~ ~]
  =<  -
  |-  ^-  [(unit [id=identity d=datum]) (set identity)]
  =*  visit-loop  $
  ?:  (~(has in visited) id-kid)  [~ visited]
  =.  visited  (~(put in visited) id-kid)
  ?~  callers  [~ visited]
  ?^  d=(recursive-match id-kid n.callers g)
    [`[n.callers u.d] visited]
  =^  has-l  visited  visit-loop(callers l.callers)
  ?^  has-l  [has-l visited]
  =^  has-r  visited  visit-loop(callers r.callers)
  ?^  has-r  [has-r visited]
  =/  new-callers  (~(get ju called-by) n.callers)
  visit-loop(callers new-callers)
::
++  mi
  |%
  ++  gut
    |=  [m=memo f=^]
    ^-  (map sock [identity datum])
    (~(gut by m) f ~)
  ::
  ++  git
    ~%  %git-mi  ..zuse  ~
    |=  [m=memo f=^ s=sock]
    ^-  (unit [identity datum])
    =/  entries=(list [* id=identity d=datum])  ~(tap by (gut m f))
    |-  ^-  (unit [identity datum])
    ?~  entries  ~
    ?:  ?&  (huge:so less-memo.d.i.entries s)
        ::
            =/  c=cape  cape:(app:ca indirect-code-request.d.i.entries s)
            ?=(%| c)
        ==
      `[id d]:i.entries
    $(entries t.entries)
  ::
  ++  put
    ~%  %put-mi  ..zuse  ~
    |=  [m=memo id=identity d=datum]
    ^-  memo
    =/  inner  (gut m fol.id)
    =.  inner  (~(put by inner) less-memo.d [id d])
    (~(put by m) fol.id inner)
  --
::
+$  sock-anno  [=sock src=spring]
++  git-g
  |=  [g=callgraph i=identity]
  ^-  datum
  (~(gut by g) i *datum)
::
++  dunno
  ^-  sock-anno
  [|+~ ~]
::
++  inlineable
  ~%  %inlineable  ..zuse  ~
  |=  fol=^
  ^-  ?
  =*  l  .
  ?+    fol  |
    [p=^ q=^]  &((l p.fol) (l q.fol))
    [%0 @]  &
    [%1 *]  &
    [%2 *]  |
    [%9 *]  |
  ::
    [%3 p=^]           (l p.fol)
    [%4 p=^]           (l p.fol)
    [%5 p=^ q=^]       &((l p.fol) (l q.fol))
    [%6 p=^ q=^ r=^]   &((l p.fol) (l q.fol) (l r.fol))
    [%7 p=^ q=^]       &((l p.fol) (l q.fol))
    [%8 p=^ q=^]       &((l p.fol) (l q.fol))
    [%10 [@ p=^] q=^]  &((l p.fol) (l q.fol))
    [%11 @ p=^]        (l p.fol)
    [%11 [@ q=^] p=^]  &((l p.fol) (l q.fol))
    [%12 p=^ q=^]      &((l p.fol) (l q.fol))
  ==
::
--
|%
++  ska
  |=  [bus=sock fol=^]
  ^-  (list callgraph)
  =|  g=callgraph
  =|  history=(list callgraph)
  =/  root  [bus fol]
  =/  w=worklist  [root ~ ~]
  =|  calls=jug-id
  =|  called-by=jug-id
  ::
  =<  $
  ~%  %analysis  ..zuse  ~
  |.  ^-  (list callgraph)
  =*  fixpoint-callgraph  $
  ::  one fixpoint iteration gives us new worklists to handle, updated part of
  ::  the callgraph and updated calls
  ::
  =;  [w-new=worklist w-call=worklist new-calls=jug-id g1=callgraph]
    =.  g  (~(uni by g) g1)
    =.  called-by
      ::  calculate the diff between new-calls and calls to update called-by
      ::
      =<  $
      ~%  %called-by-update  ..zuse  ~
      |.
      ::  we only add/replace callers to "calls" graph, so grabbing the keys of
      ::  new-calls is enough to get identities of all callers
      ::
      =/  all-callers=(list identity)  ~(tap in ~(key by new-calls))
      %+  roll  all-callers
      |=  [caller=identity acc=_called-by]
      =/  old-callees=(set identity)  (~(get ju calls) caller)
      =/  new-callees=(set identity)  (~(get ju new-calls) caller)
      =/  callee-removals=(set identity)  (~(dif in old-callees) new-callees)
      =/  callee-addition=(set identity)  (~(dif in new-callees) old-callees)
      =.  acc
        %-  ~(rep in callee-removals)
        |=  [callee=identity acc=_acc]
        (~(del ju acc) callee caller)
      ::
      %-  ~(rep in callee-addition)
      |=  [callee=identity acc=_acc]
      (~(put ju acc) callee caller)
    ::
    =.  calls  new-calls
    =/  w-back=worklist
      ::  worklist of functions whose immediate callees changed
      ::
      %-  ~(rep in w-call)
      |=  [callee=identity acc=worklist]
      (~(uni in acc) `worklist`(~(get ja called-by) callee))
    ::
    ::  total worklist: new functions + functions whose callees changed. Nothing
    ::  else needs to be reanalysed as we'll just get the same result
    ::
    =/  w-new=worklist  (~(uni in w-new) w-back)
    ?:  =(w-new ~)  [g history]
    =/  new-count   ~(wyt in ^w-new)
    =/  upd-count   ~(wyt in w-back)
    =/  uniq-count  ~(wyt in `(set ^)`(~(run in w-new) |=(id=identity fol.id)))
    ~&  [%fixpoint new+new-count upd+upd-count uniq+uniq-count]
    fixpoint-callgraph(w w-new, history [g history])
  ::
  :: ~>  %bout.[0 %iter]
  =*  g-previous  g
  =<  -
  %-  ~(rep in w)
  ::  note that now "g" is a bunt (empty), but "calls" is inherited from the
  ::  previous iteration
  ::
  |=  $:  id=identity
          ::  accumulator
          ::
          [[w-new=worklist w-call=worklist calls=_calls g=callgraph] m-new=memo]
      ==
  ^-  [[worklist worklist jug-id callgraph] memo]
  =/  data  (git-g g-previous id)
  =/  bus=sock  more.id
  =;  [memo-hit=? data-new=datum m-new=memo]
    =.  g  (~(put by g) id data-new)
    =.  calls
      (~(put by calls) id (~(run in callees.data-new) |=([* id=identity *] id)))
    ::
    ::  don't have to put fresh callees in the worklist, they should already be
    ::  there
    ::
    =?  w-new  !memo-hit
      %-  ~(rep in callees.data-new)
      |=  [[* id=identity *] acc=_w-new]
      ?:  (~(has by g-previous) id)  acc
      (~(put in acc) id)
    ::  do have to put ourselves in the callee worklist if our code usage or
    ::  product changed
    ::
    =?  w-call  |(!=([less-code prod map]:data-new [less-code prod map]:data))
      (~(put in w-call) id)
    ::
    [[w-new w-call calls g] m-new]
  ::
  =/  fol  fol.id
  =/  sub=sock-anno  [bus 1]
  ?^  hit=(git:mi m-new fol bus)  [& +.u.hit m-new]
  =*  fol-result
    $:  [=nomm pro=sock-anno]
        want=cape
        indirect-code-request=cape
        callees=(set [(unit spot) identity spring])
        area=(unit spot)
    ==
  ::
  =;  ,fol-result
    ::  construct datum & memoize
    ::
    =/  less-code  (app:ca want bus)
    =/  capture=cape  (prune:pi src.pro cape.sock.pro)
    =/  less-memo  (app:ca (uni:ca want capture) bus)
    =/  data-new=datum
      [ callees  nomm
        less-code  less-memo
        indirect-code-request
        pro  area
      ]
    ::
    =.  m-new  (put:mi m-new id data-new)
    [| data-new m-new]
  ::
  =|  $=  gen
      $:  want=cape
          indirect-code-request=cape
          callees=(set [(unit spot) identity spring])
          area=(unit spot)
      ==
  ::
  =/  seat=(unit spot)  ~
  ^-  [[=nomm prod=sock-anno] gen=_gen]
  =<  $
  ~%  %fol-loop  ..zuse  ~
  |.  ^-  [[=nomm prod=sock-anno] _gen]
  =*  fol-loop  $
  ?+    fol  ~|  fol  [[0+0 dunno] gen]
      [p=^ q=^]
    =^  l  gen  fol-loop(fol p.fol)
    =^  r  gen  fol-loop(fol q.fol)
    =<  $
    ~%  %nock-cons  ..fol-loop  ~
    |.
    :_  gen
    :-  [nomm.l nomm.r]
    :-  (knit:so sock.prod.l sock.prod.r)
    (cons:pi src.prod.l src.prod.r)
  ::
      [%0 p=@]
    =<  $
    ~%  %nock-0  ..fol-loop  ~
    |.
    :_  gen
    :-  [%0 p.fol]
    ?:  =(0 p.fol)  dunno
    ?:  =(1 p.fol)  sub
    :-  (pull:so sock.sub p.fol)
    (slot:pi src.sub p.fol)
  ::
      [%1 p=*]
    :_  gen
    :-  [%1 p.fol]
    [&+p.fol ~]
  ::
      [%2 p=^ q=^]
    =^  s  gen  fol-loop(fol p.fol)
    =^  f  gen  fol-loop(fol q.fol)
    ^-  [[nomm sock-anno] _gen]
    =*  nock-2  .
    ?.  &(=(& cape.sock.prod.f) ?=(^ data.sock.prod.f))
      ::  indirect call
      ::
      :: ~&  %indi
      :: ~&  seat
      =.  indirect-code-request.gen
        (uni:ca indirect-code-request.gen (distribute & src.prod.f))
      ::
      [[[%2 nomm.s nomm.f ~] dunno] gen]
    =/  fol-new  data.sock.prod.f
    =.  want.gen  (uni:ca want.gen (distribute & src.prod.f))
    ?:  (inlineable fol-new)
      =^  inline  gen  fol-loop(fol fol-new, sub prod.s)
      :_  gen
      :-  [%7 nomm.s nomm.inline]
      prod.inline
    =<  $
    ~%  %nock-2-direct-non-inlined  ..zuse  ~
    |.
    ^-  [[nomm sock-anno] _gen]
    =/  [id-there=identity dat-there=datum]
      =/  id-there=identity  [sock.prod.s fol-new]
      ?^  d=(~(get by g-previous) id-there)
        [id-there u.d]
      ?^  par=(recursive-call id id-there called-by g-previous)
        u.par(prod.d |+~, map.d ~)
      [id-there *datum]
    ::
    =.  want.gen
      (uni:ca want.gen (distribute cape.less-code.dat-there src.prod.s))
    ::
    =/  indi  (distribute indirect-code-request.dat-there src.prod.s)
    =.  indirect-code-request.gen  (uni:ca indirect-code-request.gen indi)
    =.  callees.gen  (~(put in callees.gen) seat id-there src.prod.s)
    :_  gen
    ^-  [nomm sock-anno]
    :-  [%2 nomm.s nomm.f ~ less-code.dat-there fol-new]
    :-  prod.dat-there
    (compose:pi map.dat-there src.prod.s)
  ::
      [%3 p=^]
    =^  p  gen  fol-loop(fol p.fol)
    :_  gen
    :-  [%3 nomm.p]
    dunno
  ::
      [%4 p=^]
    =^  p  gen  fol-loop(fol p.fol)
    :_  gen
    :-  [%4 nomm.p]
    dunno
  ::
      [%5 p=^ q=^]
    =^  p  gen  fol-loop(fol p.fol)
    =^  q  gen  fol-loop(fol q.fol)
    :_  gen
    :-  [%5 nomm.p nomm.q]
    dunno
  ::
      [%6 p=^ q=^ r=^]
    =^  p  gen  fol-loop(fol p.fol)
    =^  q  gen  fol-loop(fol q.fol)
    =^  r  gen  fol-loop(fol r.fol)
    :_  gen
    :-  [%6 nomm.p nomm.q nomm.r]
    (double-int prod.q prod.r)
  ::
      [%7 p=^ q=^]
    =^  p  gen  fol-loop(fol p.fol)
    =^  q  gen  fol-loop(fol q.fol, sub prod.p)
    :_  gen
    :-  [%7 nomm.p nomm.q]
    prod.q
  ::
      [%8 p=^ q=^]
    fol-loop(fol [%7 [p.fol 0+1] q.fol])
  ::
      [%9 p=@ q=^]
    fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
  ::
      [%10 [a=@ don=^] rec=^]
    ?:  =(0 a.fol)  [[0+0 dunno] gen]
    =^  don  gen  fol-loop(fol don.fol)
    =^  rec  gen  fol-loop(fol rec.fol)
    =<  $
    ~%  %nock-10  ..fol-loop  ~
    |.
    :_  gen
    :-  [%10 [a.fol nomm.don] nomm.rec]
    :-  (darn:so sock.prod.rec a.fol sock.prod.don)
    (edit:pi src.prod.rec a.fol src.prod.don)
  ::
      [%11 p=@ q=^]
    =^  q  gen  fol-loop(fol q.fol)
    :_  gen
    :-  [%11 p.fol nomm.q q.fol]
    prod.q
  ::
      [%11 [a=@ h=^] f=^]
    =?  .  &(=(a.fol %spot) =(1 -.h.fol))
      =*  dot  .
      =<  $
      ~%  %nock-11-soft  ..zuse  ~
      |.
      =/  pot=(unit spot)  `;;(spot +.h.fol)  ::  XX soft
      =?  area.gen  ?=(~ area.gen)  pot
      =.  seat  pot
      dot
    ::
    =^  h  gen  fol-loop(fol h.fol)
    =^  f  gen  fol-loop(fol f.fol)
    :_  gen
    :-  [%11 [a.fol nomm.h] nomm.f f.fol]
    prod.f
  ::
      [%12 p=^ q=^]
    =^  p  gen  fol-loop(fol p.fol)
    =^  q  gen  fol-loop(fol q.fol)
    :_  gen
    :-  [%12 nomm.p nomm.q]
    dunno
  ==
--