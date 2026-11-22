::  hoon.hoon is the only dependency
::
=>  ..ride
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::    This file is an implementation of the Subject Knowledge Analysis (SKA)
::    pipeline in Hoon, first described by Edward Amsden (~ritpub-sipsyl).  It
::    took inspiration from an unfinished implementation by him and Joe Bryan
::    (~master-morzod), which can be found on GitHub in the "sword" repository.
::    It also serves as a documentation and explanation piece: the problem being
::    solved here is unusual and, in my opinion, quite complicated.  Developing
::    the implementation took a lot of experimentation, and it would be a waste
::    not to describe why certain design choices were made, as some of them are
::    crucial for the algorithm to work at a reasonable speed.
::
::    Large blocks of comments can be found interspersed in the code below.  At
::    the end of this section you will find a table of contents with the
::    chapters and their line numbers.
::
::    But first of all, what kind of problem is being solved here?
::
::    Nock, unlike conventional languages, does not have a notion of a "code
::    object", a "function", or any other construct that corresponds to known
::    callable code.  The Nock 2 formula [2 b c] (and Nock 9 by extension, as it
::    is just a macro for Nock 2) is equivalent to "eval" in other languages and
::    is reduced like this:
::
::      *[a 2 b c]          *[*[a b] *[a c]]
::
::    That is, we evaluate `c` against the original subject `a`, and reduce the
::    product of that reduction with *[a b] as our new subject.  Nock is
::    expressive enough for *[a c] to be unknowable in the general case without
::    actually running the code.
::
::    But while it is unknowable in the general case, in practice we can almost
::    always know in advance which formula will be evaluated.  That is because
::    in practice the formula-formula `c` is almost always:
::      - a Nock 0, with the formula being pulled from the known subject (think
::        of the desugaring of Nock 9),
::      - or a Nock 1, with the formula being a constant/quoted value (think of
::        |- loops, where the formula does not come from the subject but is
::        instead quoted into the outer formula).
::
::    This fact allows us to introduce the notion of a *SKA function* object,
::    which is identified by a Nock formula and a masked subject.  The mask
::    includes only the code that could be used by the SKA function, either
::    directly or transitively through its callees.  A SKA function can use any
::    Nock operation, including raw Nock 2 when *[a c] cannot be deduced (an
::    indirect Nock call), but it can also call other SKA functions.
::
::    Once the call graph is known, each function can be compiled to a linear
::    SSA form, allowing further optimizations and eventually efficient
::    execution.  The compilation also performs data flow analysis, discovering
::    which axes of the input subject are used by a function, which allows us to
::    get rid of the core consing/deconsing busywork that usually happens with
::    gate slamming.  Since we need to know the subject split of the callee
::    functions to compile a SKA function, we have to perform linearization in a
::    fixed point loop for callees that are in the same SCC as the caller.
::
::  Table of contents:
::    Call graph construction:  line 541
::    Compilation:              line 2112
::    IR optimization passes:   line 5560
::    Interactive core:         line 6555
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
::
::  ska verbosity
::
:: =/  ska-verb  ~
::
::  Baking (+bake-graph):
::    `bake`: the constants a function's callers know from their code are part
::            of its bell;
::    `fold`: only the function's own reads of its code fold to constants, every
::            function is its own one variant;
::     `off`: no baking
::
=/  bake-mode  bake=~
::  Homeomorphic embedding (+recursive-call) is not checked until `he-threshold`
::  functions with the same formula are on the stack. Tuned by running Hoon
::  compiler, which needed `he-threshold` of at least 9 to analyze complex molds
::  through
::
=/  he-threshold  32
::
::  compiler verbosity
::
:: =/  comp-verb  ~
::
=/  print-ska
  |=  [pri=@ print=(trap tank)]
  !@  ska-verb  same
  %*($ slog pri pri, a ~[$:print])
::
=/  print-comp
  |=  [pri=@ print=(trap tank)]
  !@  comp-verb  same
  %*($ slog pri pri, a ~[$:print])
::
=/  road-pure
  |*  =(trap *)
  ^+  $:trap
  =/  res  (~(mule vi |) trap)
  ?-  -.res
    %&  p.res
    %|  (mean p.res)
  ==
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
=*  stub  ~|(%stub !!)
!@  bake-mode  !!
::  Partial noun definitions
::
|%
::  Noun mask. Normalization: [| |] -> |
::  [& &] is not normalized: this signals that a noun was consed during
::  a computation, preventing us from using it in a direct call. This (among
::  other denormalizations) makes the set of formulas finite, allowing the
::  analysis to converge.
::
+$  cape  $~(| $@(? [cape cape]))
::  masked noun. Normalization:  "|" leaves of the cape must correspond to 0
::  leaves in the data
::
::  %void is the top element of sock lattice, it corresponds to the empty set
::  of nouns like |+~ corresponds to a set of all nouns and &+* corresponds to a
::  singleton set. During analysis a function is assumed to return %void in the
::  beginning. It is an identity element when it comes to intersection. During
::  finalization it is turned into an unknown element for now, although this
::  info could be retained: a function that returns %void in a fixed point does
::  not return so calls to it could always be tail calls?
::
+$  sock  $~(|+~ $@(%void [=cape data=*]))
::  Provenance of data from the subject of a Nock computation we are in.
::    ~: does not come from the subject.
::    @: comes from that axis of the subject
::    ^: provenance of a cell
::
+$  spring  $~(~ *)
--
::  Partial noun logic.  Self-explanatory for the most part, but take note of
::  equality shortcircuits and ~+ memoization: this is the closest we can get
::  in Nock to pointer equality shortcircuits, which are load-bearing if we
::  consider the degree to which nouns tend to be duplicated in the standard
::  library, with around 4e-12 bits per noun:
::
::    %+  div:rs  (sun:rs (met 0 (jam ..zuse)))
::    %-  sun:rs
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
  ~%  %ca  ..ride  ~
  |%
  ::  all is known
  ::
  ++  all
    ~/  %all
    |=  c=cape
    ^-  ?
    ?@  c  c
    ~+
    &($(c -.c) $(c +.c))
  ::
  ++  hed  ~/  %hed  |=(c=cape ?@(c c -.c))
  ++  tel  ~/  %tel  |=(c=cape ?@(c c +.c))
  ++  con
    ~/  %con
    |=  [h=cape t=cape]
    ^-  cape
    =*  cons  +<
    ?:  &(?=(%| h) ?=(%| t))  |
    cons
  ::  list of known axes
  ::
  ++  yea
    ~/  %yea
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
    ~/  %int
    |=  [a=cape b=cape]
    ^-  cape
    ?:  =(a b)  a
    ?-  a
        %|  |
        %&  b
        ^
      ?-  b
          %|  |
          %&  a
          ^   (con $(a -.a, b -.b) $(a +.a, b +.b))
      ==
    ==
  ::  apply mask to a partial noun
  ::
  ++  app
    ~/  %app
    |=  [c=cape s=sock]
    ^-  sock
    ?@  s  s
    ?:  =(c cape.s)  s
    ?:  |(?=(%| c) ?=(%| cape.s))  *sock
    ?:  ?=(%& c)  s
    ~+
    %+  knit:so  $(s (hed:so s), c -.c)
    $(s (tel:so s), c +.c)
  ::  union
  ::
  ++  uni
    ~/  %uni
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
          ^   ~+((con $(a -.a, b -.b) $(a +.a, b +.b)))
      ==
    ==
  ::  push a cape to an axis
  ::
  ++  pat
    ~/  %pat
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
  ::  subtract b from a
  ::
  ++  dif
    |=  [a=cape b=cape]
    ^-  cape
    ?:  =(a b)    |
    ?:  ?=(%& b)  |
    ?:  ?=(%| b)  a
    ?:  ?=(%| a)  |
    ?:  ?=(%& a)  ~|  [%misunderstanding a+a b+b]  !!
    (con:ca $(a -.a, b -.b) $(a +.a, b +.b))
  ::  +lack: the parts of a that b does not know
  ::
  ++  lack
    |=  [a=cape b=cape]
    ^-  cape
    ?:  ?=(%| a)  |
    ?:  ?=(%& b)  |
    ?:  ?=(%| b)  a
    ?:  =(a b)    |
    =/  [p=cape q=cape]  ?@(a [a a] a)
    (con $(a p, b -.b) $(a q, b +.b))
  ::  slot
  ::
  ++  lot
    |=  [c=cape axe=@]
    ^-  cape
    ?<  =(0 axe)
    ?:  =(1 axe)  c
    ?@  c  c
    ?-  (cap axe)
      %2  $(c -.c, axe (mas axe))
      %3  $(c +.c, axe (mas axe))
    ==
  --
::  Operations on socks
::
++  so
  ~%  %so  ..ride  ~
  |%
  ::  Does b nest under a? i.e. is everything that is known by a also known
  ::  by b?
  ::
  ++  huge
    ~/  %huge
    |=  [one=sock two=sock]
    ^-  ?
    ?:  =(one two)  &
    ?@  two  &
    ?@  one  |
    ?@  data.one
      ?.  ?=(@ cape.one)  ~|  badone+one  !!
      ?.  cape.one  &
      ?&(?=(%& cape.two) =(data.one data.two))
    ?@  data.two
      ?>  ?=(@ cape.two)
      ?<  ?=(%| cape.one)
      |
    ~+
    =/  [lope=cape rope=cape]
      ?:(?=(^ cape.one) cape.one [cape.one cape.one])
    ::
    =/  [loop=cape roop=cape]
      ?:(?=(^ cape.two) cape.two [cape.two cape.two])
    ::
    ?&  $(one [lope -.data.one], two [loop -.data.two])
        $(one [rope +.data.one], two [roop +.data.two])
    ==
  ::  Do two socks agree wherever both know?
  ::
  ++  jibe
    |=  [one=sock two=sock]
    ^-  ?
    ?:  |(?=(%void one) ?=(%void two))  |
    ?:  =(one two)  &
    ?:  |(?=(%| cape.one) ?=(%| cape.two))  &
    ?:  &(?=(%& cape.one) ?=(%& cape.two))  =(data.one data.two)
    ?.  &(?=(^ data.one) ?=(^ data.two))  |
    ~+
    =/  [lope=cape rope=cape]
      ?:(?=(^ cape.one) cape.one [cape.one cape.one])
    ::
    =/  [loop=cape roop=cape]
      ?:(?=(^ cape.two) cape.two [cape.two cape.two])
    ::
    ?&  $(one [lope -.data.one], two [loop -.data.two])
        $(one [rope +.data.one], two [roop +.data.two])
    ==
  ::  axis of a partial noun, never fails
  ::
  ++  pull
    ~/  %pull
    |=  [s=sock axe=@]
    ^-  sock
    ?<  =(0 axe)
    ?@  s  s
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
  ::  cons
  ::
  ++  knit
    ~/  %knit
    |=  [one=sock two=sock]
    ^-  sock
    ?:  |(?=(%void one) ?=(%void two))  %void
    =*  l  cape.one
    =*  r  cape.two
    =/  cap  (con:ca l r)
    ?:  ?=(%| cap)  *sock
    [cap data.one data.two]
  ::  head
  ::
  ++  hed
    ~/  %hed
    |=  s=sock
    ^-  sock
    ?@  s  s
    ?:  |(?=(%| cape.s) ?=(@ data.s))
      *sock
    ?@  cape.s  [& -.data.s]
    [-.cape.s -.data.s]
  ::  tail
  ::
  ++  tel
    ~/  %tel
    |=  s=sock
    ^-  sock
    ?@  s  s
    ?:  |(?=(%| cape.s) ?=(@ data.s))
      *sock
    ?@  cape.s  [& +.data.s]
    [+.cape.s +.data.s]
  ::  intersect - output is unmasked only where both one and two are unmasked
  ::  and they both agree in data
  ::
  ++  purr
    ~/  %purr
    |=  [one=sock two=sock]
    ^-  sock
    ?:  =(one two)  one
    ?@  one  two
    ?@  two  one
    ?:  |(?=(%| cape.one) ?=(%| cape.two))  *sock
    ~+
    ?:  |(?=(^ cape.one) ?=(^ cape.two))
      %+  knit  $(one (hed one), two (hed two))
      $(one (tel one), two (tel two))
    |-  ^-  sock
    ?:  =(data.one data.two)  one
    ?:  |(?=(@ data.one) ?=(@ data.two))  *sock
    ~+
    %+  knit  $(data.one -.data.one, data.two -.data.two)
    $(data.one +.data.one, data.two +.data.two)
  ::  edit
  ::
  ++  darn
    ~/  %darn
    |=  [one=sock axe=@ two=sock]
    ^-  sock
    ?:  =(1 axe)  two
    ?:  |(=(%void one) =(%void two))  %void
    ?:  &(?=([%| *] one) ?=([%| *] two))  *sock
    =|  acc=(list (pair ?(%2 %3) sock))
    |-  ^-  sock
    ?.  |(=(1 axe) &(?=([%| *] one) ?=([%| *] two)))
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
  ::    Structure
  ::
  ::  A cape [| |] over data [0 0] is a cell of which nothing else is known.
  ::  The call graph analysis never makes one (+knit loses it, which keeps
  ::  the subjects of its functions few); baking does (+know), from what the
  ::  callers of a function build: a part of a subject that every caller
  ::  conses is a cell for the callee, and a fetch from it cannot crash.
  ::
  ::  cons, a cell also when nothing of its parts is known
  ::
  ++  cons
    ~/  %cons
    |=  [one=sock two=sock]
    ^-  sock
    ?:  |(?=(%void one) ?=(%void two))  %void
    [[cape.one cape.two] data.one data.two]
  ::  is the noun known to be a cell?
  ::
  ++  cell
    |=  s=sock
    ^-  ?
    ?@  s  |
    ?^  cape.s  &
    &(cape.s ?=(^ data.s))
  ::  +purr that keeps a cell where both are cells
  ::
  ++  meet
    ~/  %meet
    |=  [one=sock two=sock]
    ^-  sock
    ?:  =(one two)  one
    ?@  one  two
    ?@  two  one
    ?.  &((cell one) (cell two))  *sock
    ~+
    (cons $(one (hed one), two (hed two)) $(one (tel one), two (tel two)))
  ::  +darn that keeps the cells on the way to the axis: an edit that did
  ::  not crash went through them
  ::
  ++  mend
    ~/  %mend
    |=  [one=sock axe=@ two=sock]
    ^-  sock
    ?:  =(1 axe)  two
    ?:  |(=(%void one) =(%void two))  %void
    =|  acc=(list (pair ?(%2 %3) sock))
    |-  ^-  sock
    ?.  =(1 axe)
      ?-  (cap axe)
          %2  $(one (hed one), acc [[%2 (tel one)] acc], axe (mas axe))
          %3  $(one (tel one), acc [[%3 (hed one)] acc], axe (mas axe))
      ==
    |-  ^-  sock
    ?~  acc  two
    ?-  p.i.acc
      %2  $(two (cons two q.i.acc), acc t.acc)
      %3  $(two (cons q.i.acc two), acc t.acc)
    ==
  --
::  Operations on provenance
::
++  pi
  ~%  %pi  ..ride  ~
  |%
  ++  cons
    ~/  %cons
    |=  [a=spring b=spring]
    ^-  spring
    ?:  &(?=(~ a) ?=(~ b))  ~
    [a b]
  ::
  ++  hed
    ~/  %hed
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 2)
    -.pin
  ::
  ++  tel
    ~/  %tel
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 3)
    +.pin
  ::
  ++  prune
    ~/  %prune
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
    ~/  %slot
    |=  [pin=spring ax=@]
    ^-  spring
    ?:  =(ax 1)  pin
    ?~  pin  ~
    ?@  pin  (peg pin ax)
    ?-  (cap ax)
      %2  $(pin -.pin, ax (mas ax))
      %3  $(pin +.pin, ax (mas ax))
    ==
  ::  a is provenance from b, b is provenance from x.
  ::  what is the provenance of a from x?
  ::
  ++  compose
    ~/  %compose
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
    ~/  %edit
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
  ~%  %distribute  ..ride  ~
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
  ~%  %double-int  ..ride  ~
  |=  [a=[=sock src=spring] b=[=sock src=spring]]
  ^-  [=sock src=spring]
  ?:  =(a b)  a
  ?@  sock.a  b
  ?@  sock.b  a
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
::  +double-int that keeps a cell where both are cells: by the sock, or by
::  the provenance, which is a cell for what was consed
::
++  double-meet
  ~%  %double-meet  ..ride  ~
  |=  [a=[=sock src=spring] b=[=sock src=spring]]
  ^-  [=sock src=spring]
  ?:  =(a b)  a
  ?@  sock.a  b
  ?@  sock.b  a
  ?.  ?&  |((cell:so sock.a) ?=(^ src.a))
          |((cell:so sock.b) ?=(^ src.b))
      ==
    (double-int a b)
  ::  two constants are not walked for what they share, as in +double-int:
  ::  they are cells, and that is all
  ::
  ?.  |(?=(^ cape.sock.a) ?=(^ cape.sock.b) ?=(^ src.a) ?=(^ src.b))
    [[[| |] ~ ~] ~]
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
  [(cons:so sock.h sock.t) (cons:pi src.h src.t)]
--
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Call graph construction
::
::    With partial noun logic defined, we can move on to the description of call
::    graph construction.  The overall goal is, given a pair of a subject and a
::    formula, to construct:
::      - a code subject mask, which describes the code requirements of the SKA
::        function,
::      - a call graph, with that SKA function as the root,
::      - the product of the function with the provenance of its parts in the
::        subject, so that the analysis result can be cached by the code mask
::        alone and patched for another subject (+patch-prod).
::
::    The implementation below works by finding a fixed point of a function F
::    that maps a set of SKA function calls onto itself by, formally, partially
::    evaluating each callsite in the set, using the information from the
::    previous set for Nock 2 handling.  This appears to be the same thing as
::    "chaotic iteration over a lattice" in the literature.
::
::    The algorithm assumes that the set of SKA function calls forms a complete
::    lattice, and the fixed point is found via Kleene iteration, starting from
::    the least element of the lattice that contains the root call.
::
::    An earlier version iterated breadth-first over the whole call graph with
::    back-propagation of changes, which reanalyzed every function once per
::    level of discovery and per level of propagation (7 times on average for
::    +scow, 20 for +ride).  The current version (+ska-callgraph) explores the
::    graph depth-first, analyzing a newly found callee before its caller
::    proceeds, so that a function outside of a cycle is analyzed once, with
::    its callees final; the iteration only happens over strongly connected
::    components, which are found on the fly with Tarjan's algorithm.
::
::    Proving that F is monotonic for some ordering of the lattice, in which
::    [[[&+sub fol] *datum] ~ ~] is the least element that contains [&+sub fol],
::    is left as an exercise for the reader.  The hardest part, in my opinion,
::    is taking recursive calls into account.  The rest is trivial: socks for a
::    given noun form a complete lattice with huge:so as the partial ordering,
::    and we only ever grow products and code requirements.  The only place
::    where the code requirement shrinks is when going from a recursive call to
::    a new non-recursive call.  However, a non-recursive call can never become
::    recursive again, and since the set of all transitive callers of a function
::    is finite, this shrinkage can only happen a finite amount of times, so
::    eventually the iteration will converge on a fixed point.
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Partial noun datatypes bunt to their bottom elements
::
?>  =(|+~ *sock)
?>  =(| *cape)
?>  =(~ *spring)
|%
+$  identity  [more=sock fol=^]     ::  max subject
+$  bell      [less=sock fol=^]     ::  minimized subject
+$  info-2    [b=bell k=(unit *)]   ::  callee, maybe memoization key
+$  nomm
  $~  [%0 0]
  $^  [nomm nomm]
  $%  [%0 p=@]
      [%1 p=*]
      [%2 p=nomm q=nomm info=(unit info-2)]
      [%3 p=nomm]
      [%4 p=nomm]
      [%5 p=nomm q=nomm]
      [%6 p=nomm q=nomm r=nomm]
      [%7 p=nomm q=nomm]
      [%10 p=[p=_`@`1 q=nomm] q=nomm]  ::  p.p != 0
      ::  body: original hinted formula
      ::
      [%11 p=$@(@ [p=@ q=nomm]) q=nomm body=*]
      [%12 p=nomm q=nomm]
      ::  ~>  %mean.|.(...), known battery
      ::  p: formula for the trap
      ::  b: bell for the trap
      ::  q: hinted formula
      ::  k: product of the arm, if known
      ::
      [%mean p=nomm b=bell q=nomm body=* k=(unit *)]
  ==
::  seat: callsite location
::  id:   identity of the callee
::
+$  callee-entry  [seat=(unit spot) id=identity]
::  A callgraph entry:
::    callees: immediate callees
::    nomm: SKA code of that function, with direct %2's annotated
::    less-code: subject requirement for a call: subject with only the parts
::               that are used as code transitively
::    indi: parts of the subject that were transitively used as code but which
::          didn't have data to make a direct call
::    seek: parts of the subject where an indirect call sought its formula,
::          transitively, known or not: what the function may run of its
::          subject that the analysis did not find (+cole-match)
::    prod/map: product of the function, with the provenance of its parts in
::              the subject of the function (+patch-prod carries it over to
::              another subject that provides less-code)
::    area: (approximate) location of the function's body
::
::  Bunts to an entry of a function in progress that was not analyzed yet:
::  it requires nothing and its product is void.
::
+$  datum
  $:  callees=(set callee-entry)
      =nomm
      less-code=sock
      indi=cape
      seek=cape
      [prod=$~(%void sock) map=spring]
      area=(unit spot)
  ==
::
+$  callgraph  (map identity datum)
::  A graph of functions
::
+$  jug-id  (jug identity identity)
+$  worklist  (set identity)
::  %fast registrations: root cores by noun, core templates by path, battery
::  -> paths of the registered cores with it, battery node (arm formula or a
::  subtree of arms) -> paths of the registered cores with it (index for
::  +cole-match), and the registrations made since the analysis began,
::  latest first, with the clues of their hints, for vere to register the
::  cores too
::
+$  regs
  $:  root=(jug * path)
      core=(jug path sock)
      batt=(jug ^ path)
      arms=(jug ^ path)
      new=(list [pax=path tem=sock clue=*])
  ==
::  Analysis state, see +ska-callgraph
::
+$  ska-state
  $:  g=callgraph             ::  functions found so far, in progress or done
      done=memo               ::  memoization of finished functions
      order=(map identity @uxsite)  ::  DFS numbers of the functions in progress
      stk=(list identity)     ::  functions in progress, latest first
      next=@uxsite            ::  next DFS number
      moved=(set identity)    ::  functions whose product changed already
      tick=@ud                ::  counts the runs
  ::
      $=  ticks               ::  of the functions in progress: the tick of
      %+  map  identity       ::  the last run and of the last change
      [ran=@ud chg=@ud]       ::  of the entry
  ::
      =regs                   ::  %fast registrations so far
  ::
      $=  stats               ::  statistics for debugging
      $:  runs=@ud            ::    number of function analyses
          passes=@ud          ::    number of passes over components
          late-runs=@ud       ::    analyses in the second and later passes
          misses=@ud          ::    child registrations without a parent
          culled=@ud          ::    members dropped from components
  ==  ==
::  memoization map
::  formula -> less-code -> entry
::
+$  memo  (map ^ (map sock [id=identity =datum]))
+$  sock-anno  [=sock src=spring]
+$  ring  [=path axe=@]
+$  code-entry  [=nomm pure=? total=?]
::  Persistent SKA state
::
+$  long-ska
  $+  long-ska
  $:
  ::::  cold state
    ::
    $=  jets
    $:  root=(jug * path)     ::  root registrations
        core=(jug path sock)  ::  core registrations
        batt=(jug ^ path)     ::  core battery -> set of possible paths
        arms=(jug ^ path)     ::  battery node -> set of possible paths
        pend=(jug path sock)  ::  core registrations old bells wait for
    ::
        $=  cole              ::  bell <--> ring bidirectional mapping
        $:  call=(map bell ring)
            back=(jug ring bell)
    ==  ==
  ::::  finalized functions, for the analysis to pick up instead of
  ::::  analyzing them again (+analyze): by formula and code requirement
  ::::  (+mi), as +memo-final-entry stores them
    ::
    =memo
  ::::  saved entries:
    ::
    code=(map bell code-entry)          ::  direct bell mapping
    calls=(map bell (set bell))         ::  bell call graph
    vars=(jug bell bell)                ::  code bell -> its baked variants
    held=(map bell cape)                ::  compiled bell -> what every site
                                        ::  holds of its subject (+heft)
    seek=(map bell cape)                ::  compiled bell -> .seek of its
                                        ::  function (+cole-match)
  ==
--
::
|%
::  Check if "big" homeomorphically embeds "smol".
::
++  he-sock
  ~%  %he-sock  ..ride  ~
  |=  [big=sock smol=sock]
  ^-  ?
  =*  h-e  .
  ?:  =(big smol)  &
  ?:  |(?=(%void big) ?=(%void smol))  |
  ::  embedding never shrinks the cape
  ::
  ?:  (lth (cape-size cape.big) (cape-size cape.smol))  |
  ?:  &(?=(@ cape.big) ?=(@ cape.smol))  |
  =/  couple=?
    ::  smol and big are cells and smol is distributed in head and tail of big
    ::
    ?.  &(?=(^ cape.big) ?=(^ cape.smol))  |
    ~+
    ?&  (h-e (hed:so big) (hed:so smol))
        (h-e (tel:so big) (tel:so smol))
    ==
  ::
  ?:  couple  &
  ?@  cape.big  |
  ::  big is a cell and smol is either in head or tail
  ::
  ~+
  ?|  (h-e (hed:so big) smol)
      (h-e (tel:so big) smol)
  ==
::
++  cape-size
  |=  c=cape
  ^-  @
  ?@  c  1
  ~+((add $(c -.c) $(c +.c)))
::  Most specific generalization of two socks. Disagreeing parts are replaced
::  with an unknown element |+~. Note that this has different behavior and
::  intent compared to +msg-ca.
::
++  msg-sock
  |=  [a=sock b=sock]
  ^-  sock
  =*  msg  .
  ?:  =(a b)  a
  ?:  ?=(%void a)  b
  ?:  ?=(%void b)  a
  ?:  |(?=(@ cape.a) ?=(@ cape.b))  |+~
  ~+
  %+  knit:so  (msg [-.cape -.data]:a [-.cape -.data]:b)
  (msg [+.cape +.data]:a [+.cape +.data]:b)
::  Check if a call to "id-kid" is a recursive call to one of the functions
::  in progress, i.e. its transitive callers (the analysis stack, latest
::  caller first): a function with the same formula whose code requirement is
::  satisfied by id-kid's subject, unless id-kid's subject knows more than
::  that function's own subject where it failed to get code for a direct call
::  (.indi): a separate analysis of id-kid could make such a call direct.
::  Also check if id-kid's subject homeomorphically embeds the subject of one
::  of them, masking out the accumulating part with +msg-sock. This is done to
::  stop infinite chains of dynamically generated functions. Produces the
::  identity to call instead: %rec, a function in progress (the caller
::  patches its product for id-kid's subject, +patch-prod), or %he, a
::  generalized identity.
::
::  The embedding is checked only once .he-threshold functions with the
::  formula of id-kid are in progress: a shorter chain of functions with one
::  formula is analyzed in full. This keeps termination: an infinite chain
::  has infinitely many functions with one formula (the callable formulas
::  are finitely many), so past the threshold HE applies to it as before.
::
::  Chains before HE firing are theoretically finite but could be V A S T (see
::  TREE(3) to get the sense of scale); however in testing I could not construct
::  an example where a chain of functions would grow faster than linearly with
::  the size of the formula and the subject: the products would get masked down
::  with either the simple recursion pessimization (we erase the product of
::  recursive calls), or with +double-int as we intersect nouns on both their
::  values and provenances.
::
++  recursive-call
  ~%  %recursive-call  ..ride  ~
  |=  [id-kid=identity stk=(list identity) g=callgraph]
  ^-  (unit [?(%rec %he) identity])
  ::  functions in progress with the formula of id-kid
  ::
  =/  same=@
    %+  roll  stk
    |=  [id=identity acc=@]
    ?.  =(fol.id-kid fol.id)  acc
    +(acc)
  ::
  =/  he-on=?  (gte same he-threshold)
  |-  ^-  (unit [?(%rec %he) identity])
  ?~  stk  ~
  ?.  =(fol.id-kid fol.i.stk)  $(stk t.stk)
  =/  d=datum  (git-g g i.stk)
  ?:  ?&  (huge:so less-code.d more.id-kid)
          (huge:so (app:ca indi.d more.id-kid) (app:ca indi.d more.i.stk))
      ==
    `[%rec i.stk]
  ?:  &(he-on (he-sock more.id-kid more.i.stk))
    `[%he [(msg-sock more.id-kid more.i.stk) fol.id-kid]]
  $(stk t.stk)
::  Patch the product of the memoized computation with the new subject
::
++  patch-prod
  ~%  %patch-prod  ..ride  ~
  |=  [pro=[=sock src=spring] new=sock]
  ^-  [=sock src=spring]
  ?:  =(~ src.pro)  pro
  ?:  ?=(%void sock.pro)  pro
  ?@  src.pro  [(pull:so new src.pro) src.pro]
  ~+
  %+  knit-anno
    $(pro [(hed:so sock.pro) (hed:pi src.pro)])
  $(pro [(tel:so sock.pro) (tel:pi src.pro)])
::
++  knit-anno
  |=  [h=[=sock src=spring] t=[=sock src=spring]]
  ^-  [=sock src=spring]
  [(knit:so sock.h sock.t) (cons:pi src.h src.t)]
::  MSG of $sock-anno
::
++  msg-anno
  ~%  %msg-anno  ..ride  ~
  |=  [a=[=sock src=spring] b=[=sock src=spring]]
  ^-  [=sock src=spring]
  ?:  =(a b)  a
  ?:  ?=(%void sock.a)  b
  ?:  ?=(%void sock.b)  a
  ?:  |(?=(@ cape.sock.a) ?=(@ cape.sock.b))  [*sock *spring]
  ~+
  %+  knit-anno
    $(a [(hed:so sock.a) (hed:pi src.a)], b [(hed:so sock.b) (hed:pi src.b)])
  $(a [(tel:so sock.a) (tel:pi src.a)], b [(tel:so sock.b) (tel:pi src.b)])
::  Memoization core
::
++  mi
  |%
  ++  gut
    |=  [m=memo f=^]
    ^-  (map sock [identity datum])
    (~(gut by m) f ~)
  ::
  ++  git
    ~%  %git-mi  ..ride  ~
    |=  [m=memo f=^ s=sock]
    ^-  (unit [identity datum])
    =/  entries=(list [* id=identity d=datum])  ~(tap by (gut m f))
    |-  ^-  (unit [identity datum])
    ?~  entries  ~
    ::  a hit: the subject provides the code that the function used, and
    ::  knows no more than the function's own subject where it failed to get
    ::  code for a direct call (same rule as the merge in +recursive-call)
    ::
    ?:  ?&  (huge:so less-code.d.i.entries s)
        ::
            %+  huge:so  (app:ca indi.d.i.entries s)
            (app:ca indi.d.i.entries more.id.i.entries)
        ==
      =/  p  (patch-prod [prod map]:d.i.entries s)
      `[id.i.entries d.i.entries(prod sock.p, map src.p)]
    $(entries t.entries)
  ::
  ++  put
    ~%  %put-mi  ..ride  ~
    |=  [m=memo id=identity d=datum]
    ^-  memo
    =/  inner  (gut m fol.id)
    =.  inner  (~(put by inner) less-code.d [id d])
    (~(put by m) fol.id inner)
  --
::
++  git-g
  |=  [g=callgraph i=identity]
  ^-  datum
  (~(gut by g) i *datum)
::
++  inlineable
  ~%  %inlineable  ..ride  ~
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
::  Hints that don't affect whether a Nock formula could be skipped
::
+$  hint-safe  ?(%hunk %hand %lose %mean %spot)
::  check that the formula does not crash and has no important side-effect,
::  returning constant product and nomm
::
++  safe
  |=  fol=^
  ^-  (unit [=nomm prod=*])
  =*  g  .
  ?+    fol  ~
      [p=^ q=^]
    ?~  p=(g p.fol)  ~
    ?~  q=(g q.fol)  ~
    `[[nomm.u.p nomm.u.q] [prod.u.p prod.u.q]]
  ::
      [%1 p=*]
    `[fol p.fol]
  ::
      [%11 a=@ p=^]
    ?.  ?=(hint-safe a.fol)  ~
    ?~  p=(g p.fol)  ~
    `[[%11 a.fol nomm.u.p p.fol] prod.u.p]
  ::
      [%11 [a=@ h=^] p=^]
    ?.  ?=(hint-safe a.fol)  ~
    ?~  h=(g h.fol)  ~
    ?~  p=(g p.fol)  ~
    `[[%11 [a.fol nomm.u.h] nomm.u.p p.fol] prod.u.p]
  ==
::  same, but for nomm, and no product
::
++  safe-nomm
  |=  =nomm
  ^-  ?
  =*  g  .
  ?+    nomm  |
      [p=^ q=^]  &((g p.nomm) (g q.nomm))
      [%1 *]     &
  ::
      [%11 @ *]
    &(?=(?(hint-safe %memo) p.nomm) (g q.nomm))
  ::
      [%11 [@ *] *]
    &(?=(?(hint-safe %memo) p.p.nomm) (g q.p.nomm) (g q.nomm))
  ::
      [%mean *]
    &((g p.nomm) (g q.nomm))
  ==
::  Is the product of the formula always in a single register?
::
++  whole
  |=  =nomm
  ^-  ?
  =*  g  .
  ?+  nomm  |
    [%1 @]    &
    [%2 *]    &
    [%3 *]    &
    [%4 *]    &
    [%5 *]    &
    [%12 *]   &
    [%6 *]    &((g q.nomm) (g r.nomm))
    [%7 *]    (g q.nomm)
    [%11 *]   (g q.nomm)
    [%mean *]  (g q.nomm)
  ==
::  check if the formula for a formula in Nomm %2 can be safely dropped
::
++  safe-fol-fol
  |=  =nomm
  ^-  ?
  =*  g  .
  ?+    nomm  |
      ::  Nomm 0 is safe for fol-fol, since all executable code is required to
      ::  be present in the subject
      ::
      [%0 @]  &
  ::
      [p=^ q=^]  &((g p.nomm) (g q.nomm))
      [%1 *]     &
  ::  
      [%11 @ *]
    &(?=(?(hint-safe %memo) p.nomm) (g q.nomm))
  ::
      [%11 [@ *] *]
    &(?=(?(hint-safe %memo) p.p.nomm) (safe-nomm q.p.nomm) (g q.nomm))
  ::
      [%mean *]
    &((safe-nomm p.nomm) (g q.nomm))
  ==
::  treat %fast hint formula
::  returns ~ on failure, [~ ~] on root registration, [~ ~ @] on child
::  registration
::
++  fast-parent
  |=  fol=^
  ^-  (unit (unit @))
  ?+  fol  ~
    [%1 %0]            `~
    [%0 p=@]           ``p.fol
    [%11 @ p=^]        $(fol p.fol)
    [%11 [@ f=^] p=^]  ?~((safe f.fol) ~ $(fol p.fol))
  ==
::
++  uni-ju
  |*  a=(jug)
  |*  b=_a
  ^+  a
  ?:  =(~ b)  a
  %-  ~(rep by b)
  |=  [[p=_?>(?=(^ b) p.n.b) q=_?>(?=(^ b) q.n.b)] =_a]
  (~(put by a) p (~(uni in (~(get ju a) p)) q))
::
++  dif-ju
  |*  a=(jug)
  |*  b=_a
  ^+  a
  =/  c=_a  (~(dif by a) b)
  =/  i=_a  (~(int by b) a)
  ?:  =(~ i)  c
  %-  ~(rep by i)
  |=  [[p=_?>(?=(^ i) p.n.i) q=_?>(?=(^ i) q.n.i)] =_c]
  =/  r=_q  (~(get ju b) p)
  =/  s=_q  (~(dif in q) r)
  ?:  =(~ s)  c
  (~(put by c) p s)
::
++  int-ju
  |*  a=(jug)
  |*  b=_a
  ^+  a
  ?:  =(~ a)  ~
  %-  ~(rep by a)
  |=  [[k=_?>(?=(^ a) p.n.a) v=_?>(?=(^ a) q.n.a)] acc=_`_a`~]
  =/  s  (~(int in v) (~(get ju b) k))
  ?:  =(~ s)  acc
  (~(put by acc) k s)
::  Register the core with a %fast hint: the clue and the product of the hinted
::  formula as seen by the analysis at that point. The analysis walks the code
::  in execution order, so a parent core is registered before its children.
::  Produces whether a child registration missed its parent.
::
++  register-fast
  ~%  %register-fast  ..ride  ~
  |=  [clue=sock prod=sock reg=regs]
  ^-  [miss=? =regs]
  =/  gen  [miss=| reg]
  ^+  gen
  ::  unreachable registration
  ::
  ?:  |(?=(%void clue) ?=(%void prod))  gen
  ?.  (all:ca cape.clue)
    %-  (print-ska 3 |.(%fast-lost-clue))
    gen
  =/  clue=*  data.clue
  ?.  ?=([name=$@(@tas [@tas @]) dad=^ *] clue)
    %-  (print-ska 3 |.(%fast-bad-clue))
    gen
  =/  label=term
    ?@  name.clue  name.clue
    (cat 3 -.name.clue (scot %ud +.name.clue))
  ::
  ?.  ((sane %tas) label)
    %-  (print-ska 3 |.(>fast-insane-label+label<))
    gen
  ?~  parent=(fast-parent dad.clue)
    %-  (print-ska 3 |.(>fast-bad-clue-parent+label<))
    gen
  ?~  u.parent
    ::  root registration
    ::
    ?.  (all:ca cape.prod)
      %-  (print-ska 3 |.(%fast-lost-root))
      gen
    ?.  ?=([^ *] data.prod)
      %-  (print-ska 3 |.(>fast-atom-root+label<))
      gen
    [miss.gen (register-template ~[label] prod clue +.gen)]
  ::  child core registration
  ::
  =/  axis=@  u.u.parent
  ?.  =(3 (cap axis))
    %-  (print-ska 3 |.(>fast-weird-axis+[label axis]<))
    gen
  =/  batt  (pull:so prod 2)
  ?.  &(?=(^ batt) (all:ca cape.batt))
    %-  (print-ska 3 |.(>fast-lost-batt+label<))
    gen
  ?.  ?=(^ data.batt)
    %-  (print-ska 3 |.(>fast-atom-batt+[label data.batt]<))
    gen
  =/  fore  (pull:so prod axis)
  ?>  ?=(^ fore)
  =/  past=(list path)
    %~  tap  in
    %-  %~  uni  in
        ::  root registrations: check the noun before the cape, which can
        ::  be big
        ::
        ?.  (~(has by root.gen) data.fore)  ~
        ?.  (all:ca cape.fore)  ~
        (~(get ju root.gen) data.fore)
    ::  parent core registrations
    ::
    =/  batt-fore  (pull:so fore 2)
    ?.  ?=(^ batt-fore)  ~
    ?.  &((all:ca cape.batt-fore) ?=(^ data.batt-fore))  ~
    (~(get ju batt.gen) data.batt-fore)
  ::
  |-  ^+  gen
  =*  past-loop  $
  ?~  past
    %-  (print-ska 2 |.(>missed-parent+label<))
    gen(miss &)
  =/  pax=path  [label i.past]
  =/  socks  ~(tap in (~(get ju core.gen) i.past))
  |-  ^+  gen
  =*  sock-loop  $
  ?~  socks
    %-  (print-ska 2 |.(>missed-path+label<))
    past-loop(past t.past)
  ?.  (huge:so i.socks fore)  sock-loop(socks t.socks)
  =/  template=sock
    ::  put the parent into [formula *] sock
    ::
    (darn:so [[& |] data.batt ~] axis i.socks)
  ::
  %-  (print-ska 1 |.(>[%matched pax]<))
  [miss.gen (register-template pax template clue +.gen)]
::  Register a template at a path: for a root registration the whole core,
::  else the battery with the parent's template at the parent axis and
::  nothing else known, as +register-fast builds it.  Vere builds the same
::  for the cores u3n registers and feeds them through the %fast ovum, and
::  registers the ones made here from the clues %ir carries back.
::
++  register-template
  |=  [pax=path tem=sock clue=* reg=regs]
  ^-  regs
  ?>  ?=(^ tem)
  =.  tem
    ::  Normalize the sock for better matches. Denormalization is needed during
    ::  the analysis, not in between
    ::
    =>  [s=tem ..sock]
    |-  ^+  s
    ?:  ?=(%| cape.s)  |+~
    ?:  ?=(%& cape.s)  s
    ~+
    =/  l  $(s [-.cape.s -.data.s])
    =/  r  $(s [+.cape.s +.data.s])
    ?:  &(?=(%| cape.l) ?=(%| cape.r))  |+~
    :_  [data.l data.r]
    ?:  &(?=(@ cape.l) =(cape.l cape.r))  cape.l
    [cape.l cape.r]
  ::
  ?:  (~(has ju core.reg) pax tem)  reg
  =/  batt=sock  (hed:so tem)
  ?>  &(?=(^ batt) (all:ca cape.batt) ?=(^ data.batt))
  =.  new.reg   [[pax tem clue] new.reg]
  =.  core.reg  (~(put ju core.reg) pax tem)
  =.  arms.reg  (index-arms data.batt pax arms.reg)
  ?.  ?=([* ~] pax)
    reg(batt (~(put ju batt.reg) data.batt pax))
  ?>  (all:ca cape.tem)
  reg(root (~(put ju root.reg) data.tem pax))
::  Put the battery `batt` and its subformulas (if present) into `arms`
::
++  index-arms
  |=  [batt=^ pax=path arms=(jug ^ path)]
  ^+  arms
  ?:  (~(has ju arms) batt pax)  arms
  |-  ^+  arms
  =.  arms  (~(put ju arms) batt pax)
  ?.  ?=([^ *] batt)  arms
  =.  arms  $(batt -.batt)
  ?.  ?=(^ +.batt)  arms
  $(batt +.batt)
::  The functions the root reaches. Assumes finalized (fixed point): every
::  callee of a function in the graph is in the graph, a function found
::  memoized having none (+memo-final-entry).
::
++  prune-callgraph
  ~%  %prune-callgraph  ..ride  ~
  |=  [g=callgraph root=identity]
  ^+  g
  =|  out=callgraph
  =/  q=(list identity)  ~[root]
  |-  ^+  out
  ?~  q  out
  ?:  (~(has by out) i.q)  $(q t.q)
  =/  d=datum  ~|(%ska-prune-missing-callee (~(got by g) i.q))
  %=  $
      q  (weld t.q (turn ~(tap in callees.d) |=(callee-entry id)))
    out  (~(put by out) i.q d)
  ==
::  A finished function as the persistent memo keeps it, for +git to find
::  and the analysis to use in place of its own: without its callees, which
::  are final too and memoized with it, and with the subject of its identity
::  masked down to .indi, all that +git reads of it. The rest of the state
::  keeps the function's bell and nomm (.code) and the bells it calls
::  (.calls); nothing keeps the whole subject it was found with.
::
++  memo-final-entry
  |=  [id=identity d=datum]
  ^-  [identity datum]
  [[(app:ca indi.d more.id) fol.id] d(callees ~)]
::  Match a bell against registered cores: look for its formula in the battery
::  of a core template that its subject fits. Produces the ring of the arm.
::
::  The template has all the code the driver may run, and the bell has all
::  the code its function was found to run, so a bell that nests in the
::  template is one the driver is right for.  Not when the function made an
::  indirect call whose formula it sought in a part the template knows
::  (.seek of its datum): what runs there was not found, and the driver is
::  right only for what the template has there, so a core with another
::  context, +add's battery over ~, would take the driver.  A formula sought
::  in the sample, the comparator of +sort, the formula of +mink, is no
::  such call.
::
::  A bell that knows more than the template, the code of a gate in its
::  sample, is a function of fewer subjects, and the arm's driver is right for
::  it as it is for the function that knows what both do.  It gets the ring
::  only if the ring has a driver (.hot): with none the ring would change
::  nothing but keep the function from being baked, and a driver that takes
::  such a function must be worth more than the code specialized on the gate
::  (the sort by a jetted comparator, +hmac by any hash), or punt.
::
++  cole-match
  ~%  %cole-match  ..ride  ~
  |=  [b=bell seek=cape core=(jug path sock) arms=(jug ^ path) hot=(set ring)]
  ^-  (unit ring)
  ~+
  ::  only the paths of cores whose battery contains the formula can match
  ::
  =/  cands=(set path)  (~(get ju arms) fol.b)
  ?:  =(~ cands)  ~
  |-  ^-  (unit ring)
  =*  path-loop  $
  ?~  core  ~
  =;  matching-axe-any=(unit @)
    ?^  matching-axe-any  `[p.n.core u.matching-axe-any]
    =/  l  path-loop(core l.core)
    ?^  l  l
    path-loop(core r.core)
  ::
  ?.  (~(has in cands) p.n.core)  ~
  =/  templates=(set sock)  q.n.core
  |-  ^-  (unit @)
  =*  template-loop  $
  ?~  templates  ~
  =;  matching-axe=(unit @)
    ?^  matching-axe  matching-axe
    =/  l  template-loop(templates l.templates)
    ?^  l  l
    template-loop(templates r.templates)
  ::
  =/  template=sock  n.templates
  ?:  ?&  ?=(^ template)
          !=(~ (yea:ca (int:ca seek cape.template)))
      ==
    ::  the function has an indirect call with code provenance from a
    ::  place where template is known: don't match it
    ::
    ~
  =/  nest=?  (huge:so less.b template)
  ?.  |(nest (jibe:so less.b template))  ~
  =/  template-fol=sock  (hed:so template)
  =/  axis=@  2
  =;  axe=(unit @)
    ?:  |(nest ?=(~ axe))  axe
    ::  bell doesn't nest under the table and got an axis:
    ::  potential higher-order jet, check the hot state
    ::
    ?:((~(has in hot) [p.n.core u.axe]) axe ~)
  ::
  |-  ^-  (unit @)
  =*  fol-loop  $
  ?.  &(?=(^ template-fol) (all:ca cape.template-fol))  ~
  ?:  =(data.template-fol fol.b)  `axis
  ?.  ?=([^ *] data.template-fol)  ~
  =/  h  fol-loop(template-fol (hed:so template-fol), axis (peg axis 2))
  ?^  h  h
  fol-loop(template-fol (tel:so template-fol), axis (peg axis 3))
::  We just analyzed a callgraph and called some new functions: match the new
::  bells against all cores. A bell seen before keeps what it has until
::  +ska-cole-settle: the ring of a callee goes into the need of its callers,
::  whose programs may be running, so functions compile the same for as long as
::  the process lasts.
::
++  ska-cole-update
  ~%  %ska-cole-update  ..ride  ~
  |=  [lon=long-ska new-bells=(set bell) hot=(set ring)]
  ^-  long-ska
  =*  cole  cole.jets.lon
  =.  cole
    %-  ~(rep in new-bells)
    |=  [b=bell c=_cole]
    =/  sek=cape
      ~|  %ska-seek
      (~(got by seek.lon) b)
    ::
    ?~  r=(cole-match b sek core.jets.lon arms.jets.lon hot)  c
    (cole-put b u.r c)
  ::
  lon
::  With no compiled code running: match the bells without a ring against the
::  cores registered since this was done last. Produces those that got a ring.
::
++  ska-cole-settle
  ~%  %ska-cole-settle  ..ride  ~
  |=  [lon=long-ska hot=(set ring)]
  ^-  [(set bell) long-ska]
  ?:  =(~ pend.jets.lon)  [~ lon]
  =/  [rung=(set bell) cole=_cole.jets.lon]
    %-  ~(rep by code.lon)
    |=  [[b=bell *] rung=(set bell) c=_cole.jets.lon]
    ?:  (~(has by call.c) b)  [rung c]
    =/  sek=cape  (~(gut by seek.lon) b &)
    ?~  r=(cole-match b sek pend.jets.lon arms.jets.lon hot)  [rung c]
    [(~(put in rung) b) (cole-put b u.r c)]
  ::
  [rung lon(cole.jets cole, pend.jets ~)]
::
++  cole-put
  |=  [b=bell r=ring c=[call=(map bell ring) back=(jug ring bell)]]
  ^+  c
  [(~(put by call.c) b r) (~(put ju back.c) r b)]
::
++  ska-cole-restore
  |=  [lon=long-ska hot=(set ring)]
  ^-  long-ska
  =.  cole.jets.lon  [~ ~]
  =.  pend.jets.lon  ~
  (ska-cole-update lon ~(key by code.lon) hot)
::  Baking: the constants a function's callers know from their code become
::  part of its bell
::
::    A bell [less fol] names the subject a function is compiled for: the
::    analysis makes .less the parts of the subject used as code
::    (+less-code), so everything else the function reads is an argument,
::    even a constant that every caller computes from its own code: the
::    character a parser closure was built with, the sample of a door, a
::    core passed along whole.  Parsing combinators make functions of a
::    hundred arguments this way, most of them known to their one caller.
::
::    Baking widens .less with the data the callers know of the callee's
::    subject from their own bells: +know evaluates a caller's nomm as
::    socks under its bell, as the analysis does under the full subject,
::    and reports the subject at each call site; the meet (+purr:so) of
::    the sites, with the callee's code, is the callee's bake, and
::    +bake-graph iterates this down the graph to a greatest fixed point.
::    Reads of the baked parts fold to constants and branches on them to
::    the branch taken, and the leaves of the compiled shape inside the
::    baked parts are immediates of the prologue (+bake-need), so the
::    baked parts are not arguments.
::
::    The root is baked no further than its code: vere calls it with any
::    subject that provides the code, and a bell per subject would compile
::    the function once per datum.  So what gets baked is what is derivable
::    from code: literals, the products of calls on them, batteries; the
::    data of the root subject (a kernel's payload) stays an argument.
::
::    A code bell gets variants, one per knowledge its callers turned out
::    to have (.vars): a call site reuses a variant whose bell it
::    satisfies, else the poke makes one variant for the sites that fit
::    none.  A variant is a bell like any other: compiled once, called
::    directly, matched against the jets.
::
::  The union of two socks of one noun: known where either knows
::
::  The normal form of a sock: a cape is & where all is known, | where
::  nothing is.  The analysis keeps [& &] apart from & (a noun consed on
::  the way is not code); what a bell knows of data needs no such mark,
::  and one noun for one knowledge makes a change of a bake a loss
::
++  norm-sock
  ~%  %norm-sock  ..ride  ~
  |=  s=sock
  ^-  sock
  ?@  s  s
  ?:  ?=(%| cape.s)  |+~
  ?:  ?=(%& cape.s)  s
  ~+
  =/  l=sock  $(s [-.cape.s -.data.s])
  =/  r=sock  $(s [+.cape.s +.data.s])
  ?>  &(?=(^ l) ?=(^ r))
  ::  [| |] stays: a cell of unknown parts
  ::
  :_  [data.l data.r]
  ?:  &(?=(%& cape.l) ?=(%& cape.r))  &
  [cape.l cape.r]
::
++  uni-sock
  ~%  %uni-sock  ..ride  ~
  |=  [a=sock b=sock]
  ^-  sock
  ?:  =(a b)  a
  ?:  ?=(%void a)  b
  ?:  ?=(%void b)  a
  ?:  (all:ca cape.a)  a
  ?:  (all:ca cape.b)  b
  ?:  ?=(%| cape.a)  b
  ?:  ?=(%| cape.b)  a
  ~+
  (cons:so $(a (hed:so a), b (hed:so b)) $(a (tel:so a), b (tel:so b)))
::    What a caller holds
::
::  A cape of the parts of a noun that the code that made it holds
::  separately, in registers of their own: a cell where the noun was
::  assembled, by a cons or an edit; | where it is held whole (a product
::  of a call, a part of a subject that its callers hold whole) or is an
::  atom; & for a constant cell, which comes either way for nothing.  The
::  parts of a subject that every call site assembles (+held-graph) cost
::  its callers a move each, where the noun whole would cost them a cons:
::  the function takes them apart (+msg-need-ord), where the bell knows the
::  cell too (+cons:so): that it is a cell rests on the bell, as for any
::  part the bell knows, and only the cost on this.
::
++  slot-held
  |=  [c=cape axe=@]
  ^-  cape
  ?:  =(1 axe)  c
  ?@  c  c
  ?-  (cap axe)
    %2  $(c -.c, axe (mas axe))
    %3  $(c +.c, axe (mas axe))
  ==
::  what both hold; a constant holds what the other does
::
++  meet-held
  |=  [a=cape b=cape]
  ^-  cape
  ?:  ?=(%& a)  b
  ?:  ?=(%& b)  a
  ?:  |(?=(%| a) ?=(%| b))  |
  [$(a -.a, b -.b) $(a +.a, b +.b)]
::  what is held, as far as the bell of the function knows cells: only
::  there does it count (+msg-need-ord), and that makes it finite, where a
::  noun that a loop conses onto (a list) is held to any depth
::
++  trim-held
  |=  [h=cape les=cape]
  ^-  cape
  ?@  h  h
  ?@  les  les
  [$(h -.h, les -.les) $(h +.h, les +.les)]
::
++  edit-held
  |=  [rec=cape axe=@ don=cape]
  ^-  cape
  ?:  =(1 axe)  don
  =/  [h=cape t=cape]  ?@(rec [rec rec] rec)
  ?-  (cap axe)
    %2  [$(rec h, axe (mas axe)) t]
    %3  [h $(rec t, axe (mas axe))]
  ==
::  +heft: what a formula holds of its product, given what is held of its
::  subject
::
++  heft
  ~%  %heft  ..ride  ~
  |=  [=nomm sub=cape]
  ^-  cape
  ?:  ?=([%0 *] nomm)
    ?:(=(0 p.nomm) & (slot-held sub p.nomm))
  ?:  ?=([%1 *] nomm)  .?(p.nomm)
  ~+
  ?+  nomm  |
    [^ *]      [$(nomm -.nomm) $(nomm +.nomm)]
    [%6 *]     (meet-held $(nomm q.nomm) $(nomm r.nomm))
    [%7 *]     $(nomm q.nomm, sub $(nomm p.nomm))
    [%10 *]    (edit-held $(nomm q.nomm) p.p.nomm $(nomm q.p.nomm))
    [%11 *]    $(nomm q.nomm)
    [%mean *]  $(nomm q.nomm)
  ==
::  the direct calls of a function's code, each with what the function
::  holds of the callee's subject at the call
::
++  heft-sites
  ~%  %heft-sites  ..ride  ~
  |=  [=nomm own=cape]
  ^-  (list [b=bell h=cape])
  =|  out=(list [b=bell h=cape])
  =/  hub=cape  own
  |-  ^+  out
  ?-    nomm
      [^ *]    $(nomm +.nomm, out $(nomm -.nomm))
      [%0 *]   out
      [%1 *]   out
      [%3 *]   $(nomm p.nomm)
      [%4 *]   $(nomm p.nomm)
      [%5 *]   $(nomm q.nomm, out $(nomm p.nomm))
      [%6 *]   $(nomm r.nomm, out $(nomm q.nomm, out $(nomm p.nomm)))
      [%7 *]   $(nomm q.nomm, hub (heft p.nomm hub), out $(nomm p.nomm))
      [%10 *]  $(nomm q.nomm, out $(nomm q.p.nomm))
      [%12 *]  $(nomm q.nomm, out $(nomm p.nomm))
  ::
      [%2 *]
    =.  out  $(nomm p.nomm)
    =.  out  $(nomm q.nomm)
    ?~  info.nomm  out
    ::  a memoized call fetches the parts of its callee's subject with a
    ::  crash, not with a try: its callee takes nothing apart on the word
    ::  of its callers
    ::
    ?^  k.u.info.nomm  [[b.u.info.nomm |] out]
    [[b.u.info.nomm (heft p.nomm hub)] out]
  ::
      [%11 *]
    ?@  p.nomm  $(nomm q.nomm)
    $(nomm q.nomm, out $(nomm q.p.nomm))
  ::
      [%mean *]
    =.  out  $(nomm p.nomm)
    =.  out  [[b.nomm (heft p.nomm hub)] out]
    $(nomm q.nomm)
  ==
::  +held-graph: for the variants of a poke (+bake-graph), what every call
::  site holds of each one's subject.  From the root down: a function
::  enters with what its first site holds and loses what a later site, or
::  a site whose function came to hold less, does not.
::
++  held-graph
  ~%  %held-graph  ..ride  ~
  |=  [root=bell baked=(map bell [=nomm calls=(set bell) seek=cape])]
  ^-  (map bell cape)
  =/  hel=(map bell cape)  [[root |] ~ ~]
  =/  q=(list bell)  ~[root]
  |-  ^+  hel
  ?~  q  hel
  ?~  ent=(~(get by baked) i.q)  $(q t.q)
  =/  sites=(list [b=bell h=cape])
    (heft-sites nomm.u.ent (~(gut by hel) i.q |))
  ::
  =^  changed=(list bell)  hel
    %+  roll  sites
    |=  [[b=bell h=cape] changed=(list bell) hel=_hel]
    ?:  =(b root)  [changed hel]
    =/  old=(unit cape)  (~(get by hel) b)
    =/  new=cape
      (trim-held ?~(old h (meet-held h u.old)) ?@(less.b | cape.less.b))
    ::
    ?:  =(`new old)  [changed hel]
    [[b changed] (~(put by hel) b new)]
  ::
  $(q (weld t.q changed))
::  Evaluate a function's nomm as socks under a subject (what its bell
::  knows), folding reads of known parts to constants and branches on them
::  to the branch taken.  Produces the folded nomm, with the callee of each
::  call site replaced by what .res says, the parts of the subject the
::  folds assumed (.used), and the sites: callee code bell, the sock of its
::  subject and the provenance of that from ours.  .dat gives a callee code
::  bell's datum, for the product of a call.
::
::  A fold drops the computation of the folded value, so it is only done
::  when that computation is safe (+safe-nomm: a literal, a cons, a trace
::  hint on one), which it is after its own reads folded.
::
++  know
  ~%  %know  ..ride  ~
  |=  $:  =nomm
          sub=sock
          dat=$-(bell (unit datum))
          res=$-([bell sock] bell)
      ==
  ^-  $:  =^nomm
          sites=(list [b=bell k=sock])
      ==
  =/  gen  [sites=*(list [b=bell k=sock])]
  ::  provenance is tracked to reproduce +double-int results only, it is
  ::  discarded afterwards
  ::
  =/  sub=sock-anno  [sub 1]
  =/  fold=?  !@(off:bake-mode & |)
  ::  hints a literal can drop: traces, which only a crash shows, inert
  ::  %memo, and %fast, which the analysis registered already
  ::
  =*  hint-free  ,?(hint-safe %fast %memo)
  =<  =^  out=[nomm=^nomm prod=sock-anno]  gen  $
      [nomm.out sites.gen]
  ::
  |.  ^-  [[nomm=^nomm prod=sock-anno] _gen]
  =*  loop  $
  =*  dunno  *sock-anno
  ?-    nomm
      [^ *]
    =^  l  gen  loop(nomm -.nomm)
    =^  r  gen  loop(nomm +.nomm)
    :_  gen
    ?:  &(fold ?=([%1 *] nomm.l) ?=([%1 *] nomm.r))
      =/  x  [p.nomm.l p.nomm.r]
      [[%1 x] [&+x ~]]
    :-  =/  new  [nomm.l nomm.r]
        ?:(=(new nomm) nomm new)
    [(cons:so sock.prod.l sock.prod.r) (cons:pi src.prod.l src.prod.r)]
  ::
      [%0 *]
    ?:  =(0 p.nomm)  [[nomm dunno] gen]
    =/  prod=sock-anno
      ?:  =(1 p.nomm)  sub
      [(pull:so sock.sub p.nomm) (slot:pi src.sub p.nomm)]
    ::
    ?.  &(fold ?=(^ sock.prod) (all:ca cape.sock.prod))  [[nomm prod] gen]
    ::  a read of a known part: a literal, assuming that part
    ::
    :-  [[%1 data.sock.prod] [sock.prod ~]]
    gen
  ::
      [%1 *]  [[nomm [&+p.nomm ~]] gen]
  ::
      [%2 *]
    =^  s  gen  loop(nomm p.nomm)
    =^  f  gen  loop(nomm q.nomm)
    ?~  info.nomm  [[[%2 nomm.s nomm.f ~] dunno] gen]
    =/  k=sock  sock.prod.s
    =/  v=bell  (res b.u.info.nomm k)
    =.  sites.gen  [[b.u.info.nomm k] sites.gen]
    =/  prod=sock-anno
      ?~  d=(dat b.u.info.nomm)  dunno
      =/  p  (patch-prod [prod map]:u.d k)
      [sock.p (compose:pi src.p src.prod.s)]
    [[[%2 nomm.s nomm.f `[v k.u.info.nomm]] prod] gen]
  ::
      [%3 *]
    =^  [n=^nomm p=sock-anno]  gen  loop(nomm p.nomm)
    ?.  &(fold ?=(^ sock.p) (all:ca cape.sock.p) (safe-nomm n))
      [[[%3 n] dunno] gen]
    =/  pro=@  .?(data.sock.p)
    :-  [[%1 pro] [&+pro ~]]
    gen
  ::
      [%4 *]
    =^  [n=^nomm p=sock-anno]  gen  loop(nomm p.nomm)
    ?.  ?&  fold
            ?=(^ sock.p)
            (all:ca cape.sock.p)
            ?=(@ data.sock.p)
            (safe-nomm n)
        ==
      [[[%4 n] dunno] gen]
    =/  pro=@  +(data.sock.p)
    :-  [[%1 pro] [&+pro ~]]
    gen
  ::
      [%5 *]
    =^  p  gen  loop(nomm p.nomm)
    =^  q  gen  loop(nomm q.nomm)
    ?.  ?&  fold
            ?=(^ sock.prod.p)
            (all:ca cape.sock.prod.p)
            (safe-nomm nomm.p)
            ?=(^ sock.prod.q)
            (all:ca cape.sock.prod.q)
            (safe-nomm nomm.q)
        ==
      [[[%5 nomm.p nomm.q] dunno] gen]
    =/  pro=@  ?:(=(data.sock.prod.p data.sock.prod.q) 0 1)
    :-  [[%1 pro] [&+pro ~]]
    gen
  ::
      [%6 *]
    =^  p  gen  loop(nomm p.nomm)
    ?:  ?&  fold
            ?=(^ sock.prod.p)
            (all:ca cape.sock.prod.p)
            (safe-nomm nomm.p)
            ?=(?(%0 %1) data.sock.prod.p)
        ==
      ::  a known condition: the branch taken, assuming the parts of the
      ::  subject the condition came from
      ::
      ?-  data.sock.prod.p
        %0  loop(nomm q.nomm)
        %1  loop(nomm r.nomm)
      ==
    =^  q  gen  loop(nomm q.nomm)
    =^  r  gen  loop(nomm r.nomm)
    [[[%6 nomm.p nomm.q nomm.r] (double-meet prod.q prod.r)] gen]
  ::
      [%7 *]
    =^  p  gen  loop(nomm p.nomm)
    =^  q  gen  loop(nomm q.nomm, sub prod.p)
    ?:  &(fold ?=([%1 *] nomm.q) (safe-nomm nomm.p))
      [[nomm.q [&+p.nomm.q ~]] gen]
    [[[%7 nomm.p nomm.q] prod.q] gen]
  ::
      [%10 *]
    =^  don  gen  loop(nomm q.p.nomm)
    =^  rec  gen  loop(nomm q.nomm)
    =/  lit=(unit)
      ?.  &(fold ?=([%1 *] nomm.don) ?=([%1 *] nomm.rec))  ~
      (mole |.(.*([p.nomm.don p.nomm.rec] [%10 [p.p.nomm %0 2] %0 3])))
    ::
    ?^  lit  [[[%1 u.lit] [&+u.lit ~]] gen]
    :_  gen
    :-  [%10 [p.p.nomm nomm.don] nomm.rec]
    :-  (mend:so sock.prod.rec p.p.nomm sock.prod.don)
    (edit:pi src.prod.rec p.p.nomm src.prod.don)
  ::
      [%11 *]
    ?@  p.nomm
      =^  q  gen  loop(nomm q.nomm)
      ?:  &(fold ?=(hint-free p.nomm) ?=([%1 *] nomm.q))
        [[nomm.q [&+p.nomm.q ~]] gen]
      [[[%11 p.nomm nomm.q body.nomm] prod.q] gen]
    =^  h  gen  loop(nomm q.p.nomm)
    =^  q  gen  loop(nomm q.nomm)
    ?:  ?&  fold
            ?=(hint-free p.p.nomm)
            (safe-nomm nomm.h)
            ?=([%1 *] nomm.q)
        ==
      [[nomm.q [&+p.nomm.q ~]] gen]
    [[[%11 [p.p.nomm nomm.h] nomm.q body.nomm] prod.q] gen]
  ::
      [%12 *]
    =^  p  gen  loop(nomm p.nomm)
    =^  q  gen  loop(nomm q.nomm)
    [[[%12 nomm.p nomm.q] dunno] gen]
  ::
      [%mean *]
    =^  p  gen  loop(nomm p.nomm)
    =/  k=sock  sock.prod.p
    =/  v=bell  (res b.nomm k)
    =.  sites.gen  [[b.nomm k] sites.gen]
    =^  q  gen  loop(nomm q.nomm)
    [[[%mean nomm.p v nomm.q body.nomm k.nomm] prod.q] gen]
  ==
::  Bake the functions of a poke, from the root down: the variants to
::  compile, as the folded nomm, the variants it calls and the .seek of
::  its function, and the code bell -> variants index with them.  The
::  root's variant is itself.
::
::  A worklist approaches the greatest fixed point from above: a function
::  enters with what its first evaluated caller knows, is evaluated under
::  that, and loses what later callers, or its own recursion, do not know,
::  each loss re-evaluating it and its callees.  A bake only shrinks, so
::  this settles: it is the intersection (+purr:so) of what the sites
::  know, in normal form, and a caller that knows less has the sites it
::  had, each knowing less, and maybe more of them.  Except at a join of
::  branches that no longer fold, which may keep more: there a bake that
::  would grow is intersected with the old one.
::
++  bake-graph
  ~%  %bake-graph  ..ride  ~
  |=  $:  root=bell
          dat=$-(bell (unit datum))
          jetted=$-(bell ?)
          vars=(jug bell bell)
      ==
  ^-  [(map bell [=nomm calls=(set bell) seek=cape]) (jug bell bell)]
  =*  site  ,[b=bell k=sock]
  ::  an existing variant of a code bell fit for a subject: the one that
  ::  knows the most.
  ::
  ::  The subject of a site mostly provides the callee's code: the caller's
  ::  bell has what the callee's code requirement comes from in the
  ::  caller's subject (the analysis put it there), and +know computes the
  ::  rest again.  Sometimes a callsite may provide less than `less.c` in know,
  ::  like when branches get folded and turn into %1 constant, which makes their
  ::  double-int empty because the latter is limited on capes. Allowing
  ::  +double-int to decend into data would slow it down a lot.
  ::
  =/  pick
    |=  [c=bell k=sock]
    ^-  (unit bell)
    ?.  (huge:so less.c k)  ~
    %-  ~(rep in (~(get ju vars) c))
    |=  [v=bell best=(unit bell)]
    ?.  (huge:so less.v k)  best
    ?~  best  `v
    ?:  (huge:so less.u.best less.v)  `v
    best
  ::
  =/  idc  |=([c=bell k=sock] c)
  =/  frozen=?  !@(bake:bake-mode & |)
  =|  $=  st
      $:  bak=(map bell sock)        ::  code bell -> its bake, the variant
          fix=(set bell)             ::  bakes fixed at the code bell
          out=(map bell (set bell))  ::  callees whose variant it awaits
          inn=(map bell (map bell (list sock)))  ::  callee -> caller -> known
          evals=@ud
          grew=@ud                   ::  bakes that would have grown
      ==
  ::
  =.  bak.st  (~(put by bak.st) root less.root)
  =.  fix.st  (~(put in fix.st) root)
  =/  q=(list bell)  ~[root]
  =/  qs=(set bell)  [root ~ ~]
  |-  ^-  [(map bell [=nomm calls=(set bell) seek=cape]) (jug bell bell)]
  =*  work  $
  ?~  q
    %-  %+  print-ska  0
        |.  %-  sell  !>
        :*  %bake
            variants+~(wyt by bak.st)
            bake+(lent (skim ~(tap by bak.st) |=([c=bell s=sock] !=(s less.c))))
            evals+evals.st
            grew+grew.st
            fixed+(dec ~(wyt in fix.st))
        ==
    =/  res
      |=  [c=bell k=sock]
      ^-  bell
      ?^  v=(pick c k)  u.v
      [(~(got by bak.st) c) fol.c]
    ::
    %-  ~(rep by bak.st)
    |=  $:  [t=bell s=sock]
            out=(map bell [=nomm calls=(set bell) seek=cape])
            =_vars
        ==
    =/  d=datum  (need (dat t))
    =/  [=nomm sites=(list site)]  (know nomm.d s dat res)
    =/  v=bell  [s fol.t]
    :-  (~(put by out) v [nomm (silt (turn sites |=(site (res b k)))) seek.d])
    (~(put ju vars) t v)
  ::
  =/  cur=bell  i.q
  =/  rest=(list bell)  t.q
  =.  qs  (~(del in qs) cur)
  ::  evaluate .cur under its bake
  ::
  =/  sites=(list site)
    sites:(know nomm:(need (dat cur)) (~(got by bak.st) cur) dat idc)
  ::
  =.  evals.st  +(evals.st)
  ::  its sites: what each callee waiting for a variant of this poke learns
  ::  from .cur
  ::
  =/  new=(map bell (list sock))
    %+  roll  sites
    |=  [s=site new=(map bell (list sock))]
    ?^  (pick b.s k.s)  new
    (~(put by new) b.s [k.s (~(gut by new) b.s ~)])
  ::
  =/  new-bells=(set bell)  ~(key by new)
  =/  prev=(set bell)  (~(gut by out.st) cur ~)
  =.  out.st  (~(put by out.st) cur new-bells)
  ::  the bakes to recompute: the callees .cur informs.  A bake is the
  ::  code and what all the callers know
  ::
  =/  touched=(set bell)  (~(uni in prev) new-bells)
  =^  changed=(list bell)  st
    %+  roll  ~(tap in touched)
    |=  [c=bell changed=(list bell) =_st]
    =/  m=(map bell (list sock))  (~(gut by inn.st) c ~)
    =.  m
      ?~  ks=(~(get by new) c)  (~(del by m) cur)
      (~(put by m) cur u.ks)
    ::
    =.  inn.st  (~(put by inn.st) c m)
    ?:  =(c root)  [changed st]
    ::  a jetted arm is called through its ring and runs its program only
    ::  when the jet punts: nothing to bake, and a variant would have to
    ::  match the template again
    ::
    =?  fix.st  (jetted c)  (~(put in fix.st) c)
    =/  bake=sock
      ?:  |(frozen (~(has in fix.st) c))  less.c
      =/  ks=(list sock)  (zing ~(val by m))
      ?~  ks  less.c
      =/  meet=sock  (roll t.ks |=([k=sock acc=_i.ks] (meet:so k acc)))
      (norm-sock (uni-sock less.c meet))
    ::
    =/  old=(unit sock)  (~(get by bak.st) c)
    ::  +know is not monotone due to %6 branch folding or lack thereof and
    ::  +double-int not intersecting beyond capes for speed
    ::
    =^  bake=sock  grew.st
      ?~  old  [bake grew.st]
      ?:  (huge:so bake u.old)  [bake grew.st]
      [(norm-sock (purr:so bake u.old)) +(grew.st)]
    ?:  =(`bake old)  [changed st]
    [[c changed] st(bak (~(put by bak.st) c bake))]
  ::
  =/  fresh=(list bell)  (skip changed ~(has in qs))
  %=  work
    q   (weld rest fresh)
    qs  (~(gas in qs) fresh)
  ==
::
++  ska-poke
  |=  [[bus=sock fol=^] lon=long-ska hot=(set ring)]
  ^-  [[bell (list [pax=path tem=sock clue=*])] long-ska]
  %-  road-pure  |.
  =/  root-identity=identity  [bus fol]
  =/  [g=callgraph =regs]
    %-  ska-callgraph
    [root-identity memo.lon [root core batt arms ~]:jets.lon]
  ::
  =/  pruned=callgraph  (prune-callgraph g root-identity)
  =/  root-datum=datum  (~(got by pruned) root-identity)
  ::  memoize the finished functions, and index their datums by code bell
  ::
  =^  dats=(map bell datum)  memo.lon
    =<  $  ~%  %poke-just-code  ..ride  ~  |.
    %-  ~(rep by pruned)
    |=  [[id=identity d=datum] dats=(map bell datum) =_memo.lon]
    :-  (~(put by dats) [less-code.d fol.id] d)
    =/  entry  (memo-final-entry id d)
    (put:mi memo -.entry +.entry)
  ::  a code bell's datum: from this poke, or memoized by an earlier one
  ::
  =/  dat
    |=  b=bell
    ^-  (unit datum)
    ?^  d=(~(get by dats) b)  d
    ?^  m=(~(get by (gut:mi memo.lon fol.b)) less.b)  `+.u.m
    ~
  ::  the variants to compile, with their folded code and their callees
  ::
  =/  root-bell=bell  [less-code.root-datum fol]
  ::  jetted arms, by the registrations so far, this poke's included
  ::
  =/  jetted
    |=  c=bell
    ^-  ?
    ?|  (~(has by call.cole.jets.lon) c)
        ?=(^ (cole-match c ?~(d=(dat c) & seek.u.d) core.regs arms.regs hot))
    ==
  ::
  =^  baked=(map bell [=nomm calls=(set bell) seek=cape])  vars.lon
    (bake-graph root-bell dat jetted vars.lon)
  ::
  =/  helds=(map bell cape)  (held-graph root-bell baked)
  ::  a variant seen before keeps its entry and its programs
  ::
  =/  new-code=(map bell [=nomm calls=(set bell) seek=cape])
    %-  ~(rep by baked)
    |=  $:  [b=bell v=[=nomm calls=(set bell) seek=cape]]
            acc=(map bell [=nomm calls=(set bell) seek=cape])
        ==
    ?:((~(has by code.lon) b) acc (~(put by acc) b v))
  ::  callees first (+tarjan takes its vertex type from the graph's root
  ::  node, so not on an empty graph: a root seen before has no new variant)
  ::
  =/  sccs=(list (set bell))
    ?:  =(~ new-code)  ~
    %-  flop
    =<  $  ~%  %poke-tarjan  ..ride  ~  |.
    %-  tarjan
    ^-  (jug bell bell)
    %-  ~(rep by new-code)
    |=  [[b=bell v=[=nomm calls=(set bell) seek=cape]] acc=(jug bell bell)]
    %+  ~(put by acc)  b
    %-  silt
    (skim ~(tap in calls.v) |=(c=bell (~(has by new-code) c)))
  ::
  =.  lon
    =<  $  ~%  %poke-scc-loop  ..ride  ~  |.
    |-  ^-  long-ska
    =*  scc-loop  $
    ?~  sccs  lon
    =/  scc  i.sccs
    =/  loc1=(map bell code-entry)
      %-  ~(rep in scc)
      |=  [b=bell acc=_code.lon]
      (~(put by acc) b [nomm:(~(got by new-code) b) | |])
    ::  Previously there was a fixed point loop that could mark potentially
    ::  diverging computations as pure/total. While it is correct from the POV
    ::  of +mink correctness, it would make stacktraces obtained in a non-
    ::  deterministic way (e.g. ^C interrupt) less verbose. Ultimately both ways
    ::  are fine when it comes to strict Nock correctness. If you want to go
    ::  back to the previous behavior, set entry's flags above to [& &] and turn
    ::  on the fixed point loop below.
    ::  Otherwise the fixed point loop is not necessary: we start of with the
    ::  worst assumption, calls within SCC will keep that assumption, and going
    ::  over SCCs in reversed topo order makes sure that non-recursive callees
    ::  are checked before the callers.
    ::
    :: |-  ^-  long-ska
    :: =*  fixpoint-loop  $
    =;  loc2=(map bell code-entry)
      :: ?.  =(loc1 loc2)  fixpoint-loop(loc1 loc2)
      =.  code.lon  loc2
      scc-loop(sccs t.sccs)
    ::
    %-  ~(rep in scc)
    |=  [b=bell acc=_loc1]
    ^+  acc
    =/  [pure=? total=?]  (eval-finalized b acc)
    (~(jab by acc) b |=(=code-entry code-entry(pure pure, total total)))
  ::
  =/  new-cores=(jug path sock)
    (~(gas ju *(jug path sock)) (turn new.regs |=([p=path s=sock *] [p s])))
  ::
  =.  jets.lon
    %=  jets.lon
      root  root.regs
      core  core.regs
      batt  batt.regs
      arms  arms.regs
      pend  ((uni-ju pend.jets.lon) new-cores)
    ==
  ::
  =.  seek.lon
    %-  ~(rep by new-code)
    |=  [[b=bell v=[=nomm calls=(set bell) seek=cape]] acc=_seek.lon]
    (~(put by acc) b seek.v)
  ::
  =.  held.lon
    %-  ~(rep by new-code)
    |=  [[b=bell *] acc=_held.lon]
    =/  h=cape  (~(gut by helds) b |)
    ?:  ?=(@ h)  acc
    (~(put by acc) b h)
  ::
  =.  calls.lon
    %-  ~(rep by new-code)
    |=  [[b=bell v=[=nomm calls=(set bell) seek=cape]] acc=_calls.lon]
    (~(put by acc) b calls.v)
  ::
  :-  [root-bell (flop new.regs)]
  (ska-cole-update lon ~(key by new-code) hot)
::  produces data about a function
::  pure: no crashes + no hints excepts %fast (call to it could be omitted)
::  total: no crashes (stacktrace boundaries around them could be omitted)
::  by this point socks are never %void
::
++  eval-finalized
  ::  %memo and %fast: handled by analysis, noops in computations
  ::
  =*  hint-pure  ,?(hint-safe %fast %memo)
  ~%  %eval-finalized  ..ride  ~
  |=  [b=bell code=(map bell code-entry)]
  ^-  [pure=? total=?]
  =/  sub=sock  less.b
  =/  =nomm  nomm:(~(got by code) b)
  =<  +
  |^  ^-  [s=sock pure=? total=?]
  =*  nomm-loop  $
  ?-    nomm
      [p=^ q=*]
    =/  p  nomm-loop(nomm p.nomm)
    =/  q  nomm-loop(nomm q.nomm)
    :-  (knit:so s.p s.q)
    [&(pure.p pure.q) &(total.p total.q)]
  ::
      [%0 *]
    ?:  =(0 p.nomm)  [|+~ | |]
    :-  (pull:so sub p.nomm)
    [. .]:(have sub p.nomm)
  ::
      [%1 *]  [&+p.nomm & &]
  ::
      [%2 *]
    :-  |+~
    :-
      ?&  pure:nomm-loop(nomm p.nomm)
          pure:nomm-loop(nomm q.nomm)
          &(?=(^ info.nomm) pure:(~(got by code) b.u.info.nomm))
      ==
    ?&  total:nomm-loop(nomm p.nomm)
        total:nomm-loop(nomm q.nomm)
        &(?=(^ info.nomm) total:(~(got by code) b.u.info.nomm))
    ==
  ::
      [%3 *]  [|+~ [pure total]:nomm-loop(nomm p.nomm)]
      [%4 *]  [|+~ | |]
      [%5 *]  :+  |+~
                &(pure:nomm-loop(nomm p.nomm) pure:nomm-loop(nomm q.nomm))
              &(total:nomm-loop(nomm p.nomm) total:nomm-loop(nomm q.nomm))
  ::
      [%6 *]
    =/  y  nomm-loop(nomm q.nomm)
    =/  n  nomm-loop(nomm r.nomm)
    [(purr:so s.y s.n) | |]
  ::
      [%7 *]
    =/  p  nomm-loop(nomm p.nomm)
    =/  q  nomm-loop(sub s.p, nomm q.nomm)
    [s.q &(pure.p pure.q) &(total.p total.q)]
  ::
      [%10 *]
    =/  don  nomm-loop(nomm q.p.nomm)
    =/  rec  nomm-loop(nomm q.nomm)
    =/  got=?  (have s.rec p.p.nomm)
    :+  (darn:so s.rec p.p.nomm s.don)
      ?&  pure.rec
          pure.don
          got
      ==
    ?&  total.rec
        total.don
        got
    ==
  ::
      [%11 *]
    ?@  p.nomm
      =/  q  nomm-loop(nomm q.nomm)
      [s.q | total.q]
    =/  tok  nomm-loop(nomm q.p.nomm)
    =/  fol  nomm-loop(nomm q.nomm)
    :+  s.fol
      &(?=(hint-pure p.p.nomm) pure.tok pure.fol)
    &(total.tok total.fol)
  ::
      [%mean *]
    =/  tok  nomm-loop(nomm p.nomm)
    =/  fol  nomm-loop(nomm q.nomm)
    [s.fol &(pure.tok pure.fol) &(total.tok total.fol)]
  ::
      [%12 *]  [|+~ | |]
  ==
  ::
  ++  have
    |=  [=sock axe=@]
    ^-  ?
    ?<  =(0 axe)
    |-  ^-  ?
    ?:  =(1 axe)  &
    ?:  ?=([%| *] sock)  |
    ?-  (cap axe)
      %2  $(sock (hed:so sock), axe (mas axe))
      %3  $(sock (tel:so sock), axe (mas axe))
    ==
  --
::
++  simple-bell-graph-and-reversed
  ~%  %simple-bell-graph  ..ride  ~
  |=  g=callgraph
  ^-  [(jug bell bell) (jug bell bell)]
  %-  ~(rep by g)
  |=  [[k=identity v=datum] acc=(jug bell bell) acc-r=(jug bell bell)]
  =/  caller-bell=bell  [less-code.v fol.k]
  =?  acc  !(~(has by acc) caller-bell)  (~(put by acc) caller-bell ~)
  %-  ~(rep in callees.v)
  |=  [callee=callee-entry =_acc =_acc-r]
  ?~  callee-datum=(~(get by g) id.callee)  [acc acc-r]
  =/  callee-bell=bell  [less-code.u.callee-datum fol.id.callee]
  :-  (~(put ju acc) caller-bell callee-bell)
  (~(put ju acc-r) callee-bell caller-bell)
::  callee -> callers, of a bell graph like .calls of $long-ska
::
++  reverse-bell-graph
  |=  g=(jug bell bell)
  ^-  (jug bell bell)
  %-  ~(rep by g)
  |=  [[m=bell cs=(set bell)] acc=(jug bell bell)]
  (~(rep in cs) |=([c=bell acc=_acc] (~(put ju acc) c m)))
::  callers first
::
++  tarjan
  |*  g=(jug * *)
  =*  vertex  _p.n.-.g
  ^-  (list (set vertex))
  =*  gen
    $:  idx=@                     ::  index generator
        vis=(map vertex @)        ::  numbered vertices
        stk=(list vertex)         ::  stack of tr. callers, partially ordered
        cur=(set vertex)          ::  above a set
        fin=(list (set vertex))   ::  finalized SCCs
    ==
  ::
  =<  fin  ^-  gen
  %-  ~(rep by g)
  |=  [[v=vertex kids=(set vertex)] acc=gen]
  ?:  (~(has by vis.acc) v)  acc
  =<  +
  |-  ^-  [@ gen]
  =*  connect  $
  =/  index=@  idx.acc
  =.  acc
    %_  acc
      idx  +(idx.acc)
      vis  (~(put by vis.acc) v index)
      stk  [v stk.acc]
      cur  (~(put in cur.acc) v)
    ==
  ::  lowest strongly-connected vertex, including itself
  ::
  =^  lowest=@  acc
    %-  ~(rep in kids)
    |=  [kid=vertex lowest=_index =_acc]
    ?^  kid-idx=(~(get by vis.acc) kid)
      :_  acc
      ?.  (~(has in cur.acc) kid)  lowest
      (min lowest u.kid-idx)
    =^  lowest-kid=@  acc  connect(v kid, kids (~(get ju g) kid), acc acc)
    [(min lowest lowest-kid) acc]
  ::
  :-  lowest
  ?.  =(index lowest)  acc
  =<  acc(fin [done fin.acc])
  ^-  [done=(set vertex) =_acc]
  =|  out=(set vertex)
  |-  ^+  [out acc]
  =*  pop-loop  $
  =^  pop=vertex  stk.acc  ?~(stk.acc !! stk.acc)
  =.  cur.acc  (~(del in cur.acc) pop)
  =.  out  (~(put in out) pop)
  ?:  =(v pop)  [out acc]
  pop-loop
::  Most specific generalization of two capes. Disagreeing parts are replaced
::  with & to capture/demand more. Note that this has different behavior and
::  intent compared to +msg-sock
::
++  msg-ca
  |=  [a=cape b=cape]
  ^-  cape
  =*  msg  .
  ?:  =(a b)  a
  ?:  |(?=(@ a) ?=(@ b))  &
  [(msg -.a -.b) (msg +.a +.b)]
::
++  soft-spot
  |=  n=*
  ^-  (unit spot)
  ?@  n  ~
  =/  tel  +.n
  =/  hed  -.n
  ?.  ?=(pint tel)  ~
  =;  pax=(unit path)
    ?~  pax  ~
    `[u.pax tel]
  ::
  |-  ^-  (unit path)
  ?~  hed  `~
  ?.  ?=([@ta *] hed)  ~
  =/  rest=(unit path)  $(hed +.hed)
  ?~  rest  ~
  `[-.hed u.rest]
::  The graph is explored depth-first: a direct call to a function that is not
::  in the graph yet analyzes that function right away, before the caller
::  proceeds, so a function that is not on a cycle is analyzed exactly once,
::  with its callees final. Cycles are found with Tarjan's SCC algorithm on the
::  fly: a function stays on the stack (.stk) while a function below it on the
::  stack is reachable from it, and when the root of a strongly connected
::  component finishes, the component is reanalyzed in passes until no member
::  changes. A pass may discover new functions, which join the component if
::  they call back into it.
::
::  Functions popped off the stack are final and get memoized in .done, so
::  that a later call to the same formula with a subject that provides what a
::  finished function used resolves to that function instead of a new one.
::
++  ska-callgraph
  ~%  %ska-callgraph  ..ride  ~
  !.
  |=  [[bus=sock fol=^] memo-final=memo reg=regs]
  ^-  [callgraph regs]
  =|  st=ska-state
  =.  regs.st  reg
  =<  =/  res  (analyze [bus fol] st)
      %-  %+  print-ska  0
          |.  %-  sell  !>
          :*  %ska-callgraph
              functions+~(wyt by g.st.res)
              runs+runs.stats.st.res
              passes+passes.stats.st.res
              late-runs+late-runs.stats.st.res
              fast-misses+misses.stats.st.res
              culled+culled.stats.st.res
          ==
      [g.st.res regs.st.res]
  |%
  ::  Analyze a function that is not in the graph yet, and the functions it
  ::  calls. Produces the lowest DFS number of a function in progress reachable
  ::  from it (Tarjan's lowlink), or .next if none.
  ::
  ++  analyze
    ~%  %ska-analyze  ..ride  ~
    |=  [id=identity st=ska-state]
    ^-  [low=@uxsite st=ska-state]
    ::  analyzed in a previous poke: the memoized function is final and has
    ::  no callees, they are final and memoized too (+memo-final-entry)
    ::
    ?^  hit=(git:mi memo-final fol.id more.id)
      =/  d=datum  +.u.hit
      :-  next.st
      st(g (~(put by g.st) id d), done (put:mi done.st id d))
    =/  index=@uxsite  next.st
    =.  st
      %=  st
        next   +(index)
        order  (~(put by order.st) id index)
        stk    [id stk.st]
        g      (~(put by g.st) id *datum)
      ==
    ::
    =^  [low=@uxsite back=? changed=?]  st  (run id index st)
    ?.  =(low index)  [low st]
    ::  .id is the root of a strongly connected component: everything above it
    ::  on the stack. If it is trivial, it is final.
    ::
    ?.  |(back !?=([* ~] (above id stk.st)))
      [next.st (pop id st)]
    ::  Reanalyze the component until it is stable. A pass sweeps the members
    ::  callees first (+sweep), so that a change reaches the callers within
    ::  the pass except across back edges. A pass may find a call to a
    ::  function below .id on the stack: then .id was not the root after all,
    ::  and the component stays on the stack for the real root to iterate.
    ::
    ::  A member is re-run only if the entry of one of its callees changed
    ::  since the member last ran (+dirty): the data a run reads are the
    ::  entries of its callees, so a member whose callees did not change would
    ::  produce the same entry again. This covers the first pass (a member
    ::  that saw a callee in progress, with an empty entry, is dirty once the
    ::  callee has run) and the members of a component that was found stable
    ::  before its real root was known.
    ::
    =/  pass=@  1
    |-  ^-  [@ ska-state]
    =*  pass-loop  $
    =/  members=(list identity)  (sweep id (silt (above id stk.st)) st)
    =.  passes.stats.st  +(passes.stats.st)
    ::  every function analyzed afresh takes a DFS number, so a change of
    ::  .next tells whether this pass found one
    ::
    =/  next-before=@uxsite  next.st
    =^  [low=@uxsite changed=?]  st
      |-  ^-  [[@ ?] ska-state]
      =*  member-loop  $
      ?~  members  [[index |] st]
      ?.  (dirty i.members st)  member-loop(members t.members)
      =?  late-runs.stats.st  (gth pass 1)  +(late-runs.stats.st)
      =^  [low-m=@uxsite back-m=? changed-m=?]  st
        (run i.members (~(got by order.st) i.members) st)
      ::
      ?:  (lth low-m index)  [[low-m changed-m] st]
      =^  [low-t=@uxsite changed-t=?]  st
        member-loop(members t.members)
      ::
      [[(min low-m low-t) |(changed-m changed-t)] st]
    ::
    ?.  =(low index)  [low st]
    ::  members that .id does not reach anymore are dropped
    ::
    =.  st  (cull id st)
    ::  stable: no member was dirty, or no entry changed and no function was
    ::  found (a new function was seen in progress, as an empty entry, by the
    ::  members that called it, which are dirty now)
    ::
    ?:  &(!changed =(next.st next-before))
      [next.st (pop id st)]
    pass-loop(pass +(pass))
  ::  did the entry of a callee of .m change since .m last ran? A run reads
  ::  the entries of its callees as they are at the time, except its own: a
  ::  recursive call to .m itself reads the entry from before the run, which
  ::  the run then replaces, so a change in the run itself (the same tick)
  ::  counts too.
  ::
  ++  dirty
    |=  [m=identity st=ska-state]
    ^-  ?
    =/  ran=@ud  ran:(~(gut by ticks.st) m [ran=0 chg=0])
    %-  ~(any in callees:(git-g g.st m))
    |=  callee-entry
    (gte chg:(~(gut by ticks.st) id [ran=0 chg=0]) ran)
  ::  the members (.was) of the component of .id that .id reaches, callees
  ::  before callers: the post-order of a depth-first search from .id over
  ::  the current callees
  ::
  ++  sweep
    |=  [id=identity was=(set identity) st=ska-state]
    ^-  (list identity)
    =/  kids
      |=  i=identity
      ^-  (list identity)
      (turn ~(tap in callees:(git-g g.st i)) |=(callee-entry id))
    =/  seen=(set identity)  [id ~ ~]
    =/  stack=(list [i=identity kids=(list identity)])  [id (kids id)]~
    =|  out=(list identity)
    |-  ^-  (list identity)
    ?~  stack  (flop out)
    ?~  kids.i.stack  $(stack t.stack, out [i.i.stack out])
    =/  k=identity  i.kids.i.stack
    =/  rest=(list [i=identity kids=(list identity)])
      [[i.i.stack t.kids.i.stack] t.stack]
    ?:  |((~(has in seen) k) !(~(has in was) k))  $(stack rest)
    $(stack [[k (kids k)] rest], seen (~(put in seen) k))
  ::  functions on the stack above and including .id, latest first
  ::
  ++  above
    |=  [id=identity stk=(list identity)]
    ^-  (list identity)
    ?~  stk  ~|(%ska-stack !!)
    ?:  =(id i.stk)  [id ~]
    [i.stk $(stk t.stk)]
  ::  Forget the members of the component of .id that are not reachable from
  ::  .id anymore: a later pass can stop calling a function that an earlier
  ::  one found, e.g. when a call becomes indirect or gets another subject.
  ::  Such a function can still call members, so its entry is not final and
  ::  must not be left in the graph, where it would pass for a finished one.
  ::  Nothing else refers to it: every function above .id on the stack was
  ::  found after .id, by a member. If it is called again, it is analyzed
  ::  afresh.
  ::
  ++  cull
    |=  [id=identity st=ska-state]
    ^-  ska-state
    =/  members=(set identity)  (silt (above id stk.st))
    =/  live=(set identity)
      =/  q=(list identity)  ~[id]
      =|  live=(set identity)
      |-  ^+  live
      ?~  q  live
      ?:  |((~(has in live) i.q) !(~(has in members) i.q))  $(q t.q)
      %=  $
        live  (~(put in live) i.q)
        q     %+  weld  t.q
              (turn ~(tap in callees:(git-g g.st i.q)) |=(callee-entry id))
      ==
    ::
    =/  dead=(set identity)  (~(dif in members) live)
    ?:  =(~ dead)  st
    =.  culled.stats.st  (add culled.stats.st ~(wyt in dead))
    =.  stk.st  (skip stk.st ~(has in dead))
    =.  moved.st  (~(dif in moved.st) dead)
    %-  ~(rep in dead)
    |=  [i=identity =_st]
    %=  st
      order  (~(del by order.st) i)
      ticks  (~(del by ticks.st) i)
      g      (~(del by g.st) i)
    ==
  ::  pop a finished component off the stack, memoizing its members
  ::
  ++  pop
    |=  [id=identity st=ska-state]
    ^-  ska-state
    =^  top=identity  stk.st
      ?~  stk.st  ~|(%ska-stack !!)
      stk.st
    ::
    =.  order.st  (~(del by order.st) top)
    =.  ticks.st  (~(del by ticks.st) top)
    ::  a finished function: a void product becomes unknown
    ::
    =/  d=datum   (git-g g.st top)
    =?  prod.d  ?=(%void prod.d)  |+~
    =.  g.st      (~(put by g.st) top d)
    =.  done.st   (put:mi done.st top d)
    ?:  =(top id)  st
    $
  ::  One analysis pass over the formula of .id, updating its entry in the
  ::  graph. Produces its lowlink, whether it called its transitive caller,
  ::  and whether the entry changed in a way that could affect its immediate
  ::  callers.
  ::
  ++  run
    ~%  %ska-callgraph-iteration  ..ride  ~
    |=  [id=identity index=@uxsite st=ska-state]
    ^-  [[low=@uxsite back=? changed=?] ska-state]
    =.  runs.stats.st  +(runs.stats.st)
    =/  data=datum  (git-g g.st id)
    =/  bus=sock  more.id
    =/  fol  fol.id
    =/  sub=sock-anno  [bus 1]
    =*  fol-result
      $:  [=nomm pro=sock-anno *]
          want=cape
          indi=cape
          seek=cape
          callees=(set callee-entry)
          area=(unit spot)
          low=@uxsite
          back=?
          st=ska-state
      ==
    ::
    =;  ,fol-result
      ::  construct datum
      ::
      =/  less-code  (app:ca want bus)
      ::  indi is intersected with the inverse of subject knowledge to track
      ::  only the parts that we actually do not know, not the parts where there
      ::  is an atom where formula look up expected a cell or a denormalized
      ::  cell which %2 couldn't use for a direct call. These parts of the
      ::  subject cannot be known better, and indi is used to reanalyze if the
      ::  new subject actually knows more and could turn indirect calls of a
      ::  memoized entry into direct ones.
      ::
      =/  dark=cape  ?@(bus | cape.bus)
      =.  indi  (lack:ca indi dark)
      =/  data-new=datum  [callees nomm less-code indi seek pro area]
      ::  If we got two different non-void products we will compute their MSG to
      ::  converge faster, otherwise we intersect the products to preserve more
      ::  knowledge
      ::
      =/  pm=[=sock src=spring]
        ?:  (~(has in moved.st) id)
          (msg-anno [prod map]:data-new [prod map]:data)
        (double-int [prod map]:data-new [prod map]:data)
      ::
      =.  prod.data-new  sock.pm
      =.  map.data-new  src.pm
      =?  moved.st  &(!?=(%void prod.data) !=(pm [prod map]:data))
        (~(put in moved.st) id)
      ::
      =?  indi.data-new
          ?&  =([less-code prod map]:data-new [less-code prod map]:data)
              !=(indi.data-new indi.data)
          ==
        ::  if new datum only differs in indi.data-new when it comes to data
        ::  that could affect the immediate callers, turn disagreeing parts into
        ::  %.y so that we converge
        ::
        (lack:ca (msg-ca indi.data-new indi.data) dark)
      ::
      =?  seek.data-new
          ?&  .=  [less-code prod map indi]:data-new
                  [less-code prod map indi]:data
              !=(seek.data-new seek.data)
          ==
        ::  likewise for .seek, which only takes rings away
        ::
        (msg-ca seek.data-new seek.data)
      ::
      =/  changed=?
        ?!  .=  [less-code prod map indi seek]:data-new
                [less-code prod map indi seek]:data
      ::
      =.  tick.st  +(tick.st)
      =.  ticks.st
        %+  ~(put by ticks.st)  id
        :-  tick.st
        ?:  changed  tick.st
        chg:(~(gut by ticks.st) id [ran=0 chg=0])
      ::
      :-  [low back changed]
      st(g (~(put by g.st) id data-new))
    ::
    =/  gen
      ^-  $:  want=cape
              indi=cape
              seek=cape
              callees=(set callee-entry)
              area=(unit spot)
              low=@uxsite
              back=?
              st=ska-state
          ==
      [| | | ~ ~ index | st]
    ::
    =/  seat=(unit spot)  ~
    =/  memo-key=(unit *)  ~
    =/  bare-call=?  |
    =/  defer=?  |
    ::  saf: the formula is safe: it does not crash and has no important side
    ::  effect, i.e. it is a constant, a cons of safe formulas or a %spot/%mean
    ::  hint on one. Its product is a constant with cape exactly & and no
    ::  provenance, as if it were a Nock 1: a workaround for our cape cons
    ::  denormalization breaking code like !:([%9 2 %0 1]).
    ::
    ^-  [[=nomm prod=sock-anno saf=?] gen=_gen]
    =<  $
    ~%  %fol-loop  ..ride  ~
    |.  ^-  [[=nomm prod=sock-anno saf=?] _gen]
    =*  fol-loop  $
    =*  dunno  *sock-anno
    ?+    fol  [[0+0 dunno |] gen]
        [p=^ q=^]
      =^  l  gen  fol-loop(fol p.fol)
      =^  r  gen  fol-loop(fol q.fol)
      :_  gen
      :-  [nomm.l nomm.r]
      ?:  &(saf.l saf.r ?=(^ sock.prod.l) ?=(^ sock.prod.r))
        [[&+[data.sock.prod.l data.sock.prod.r] ~] &]
      :_  |
      :-  (knit:so sock.prod.l sock.prod.r)
      (cons:pi src.prod.l src.prod.r)
    ::
        [%0 p=@]
      :_  gen
      :-  [%0 p.fol]
      :_  |
      ?:  =(0 p.fol)  dunno
      ?:  =(1 p.fol)  sub
      :-  (pull:so sock.sub p.fol)
      (slot:pi src.sub p.fol)
    ::
        [%1 p=*]
      [[[%1 p.fol] [&+p.fol ~] &] gen]
    ::
        [%2 p=^ q=^]
      ::  memo-key might have been set by %11 %memo which redirected us here.
      ::  but there is no reason to unset it when we decend into children: if it
      ::  was set, then the child expressions will be [%0 1] and [%1 fol],
      ::  neither of which are affected by memo-key
      ::  
      =^  s  gen  fol-loop(fol p.fol)
      =^  f  gen  fol-loop(fol q.fol)
      ^-  [[nomm sock-anno ?] _gen]
      ::  a void subject or formula: no execution reaches this call
      ::
      ?:  |(?=(%void sock.prod.s) ?=(%void sock.prod.f))
        [[[%2 nomm.s nomm.f ~] [%void ~] |] gen]
      ::  Here we check that the mask is precisely %& instead of cheking with
      ::  +all:ca to prevent analyzing through Nock evals with consed up
      ::  formulas. This makes the set of all callable nouns finite,
      ::  guaranteeing termination of the algo when paired with homeomorphic
      ::  embedding check in recursive calls
      ::
      ?.  &(=(& cape.sock.prod.f) ?=(^ data.sock.prod.f) !bare-call)
        ::  indirect call
        ::
        =.  indi.gen  (uni:ca indi.gen (distribute & src.prod.f))
        =.  seek.gen  (uni:ca seek.gen (distribute & src.prod.f))
        [[[%2 nomm.s nomm.f ~] dunno |] gen]
      =/  fol-new=^  data.sock.prod.f
      ::  Inline leaf formulas. Allows to analyze through formulas whose
      ::  products are gates, also speeds up analysis. Should be safe to comment
      ::  out the condition and the first branch - useful during debugging to
      ::  rule out stuff.
      ::
      ?:  &(?=(~ memo-key) !defer (inlineable fol-new))
        =.  want.gen  (uni:ca want.gen (distribute & src.prod.f))
        =^  inline  gen  fol-loop(fol fol-new, sub prod.s)
        :_  gen
        :-  [%7 nomm.s nomm.inline]
        [prod.inline |]
      =<  $
      ~%  %nock-2-direct-non-inlined  ..ride  ~
      |.
      ^-  [[nomm sock-anno ?] _gen]
      =^  [id-there=identity dat-there=datum]  gen
        =/  id-there=identity  [sock.prod.s fol-new]
        |-  ^-  [[identity datum] _gen]
        =*  resolve  $
        ?^  d=(~(get by g.st.gen) id-there)
          ::  Exact identity match. If in `order`: recursive call to a function
          ::  in progress
          ::
          ?~  ord=(~(get by order.st.gen) id-there)  [[id-there u.d] gen]
          :-  [id-there u.d]
          gen(low (min low.gen u.ord), back &)
        ::  finalized memo hit
        ::
        ?^  m=(git:mi done.st.gen fol-new sock.prod.s)
          [u.m gen]
        ::  a recursive call to a function in progress with a different
        ::  subject: its code requirement is satisfied, and its product is
        ::  used where the subjects agree. Or a call in a chain of growing
        ::  subjects, generalized
        ::
        ?^  par=(recursive-call id-there stk.st.gen g.st.gen)
          ?-    -.u.par
              %he  resolve(id-there +.u.par)
              %rec
            =/  d=datum  (git-g g.st.gen +.u.par)
            =/  m  (patch-prod [prod map]:d sock.prod.s)
            :-  [+.u.par d(prod sock.m, map src.m)]
            gen(low (min low.gen (~(got by order.st.gen) +.u.par)), back &)
          ==
        ::  a new function: analyze it now
        ::
        =^  low-there=@uxsite  st.gen  (analyze id-there st.gen)
        =.  low.gen  (min low.gen low-there)
        [[id-there (git-g g.st.gen id-there)] gen]
      ::  a code requirement is never void
      ::
      ?>  ?=(^ less-code.dat-there)
      ::  Direct call: record immediate code usage (we just got the formula) +
      ::  transitive code usage by the callee
      ::
      =.  want.gen
        ;:  uni:ca
          want.gen
          (distribute & src.prod.f)
          (distribute cape.less-code.dat-there src.prod.s)
        ==
      ::  Also propagate transitive attempts to get code for indirect calls
      ::
      =.  indi.gen  (uni:ca indi.gen (distribute indi.dat-there src.prod.s))
      =.  seek.gen  (uni:ca seek.gen (distribute seek.dat-there src.prod.s))
      =.  callees.gen  (~(put in callees.gen) seat id-there)
      :_  gen
      ^-  [nomm sock-anno ?]
      :-  [%2 nomm.s nomm.f `[[less-code.dat-there fol-new] memo-key]]
      :_  |
      :-  prod.dat-there
      (compose:pi map.dat-there src.prod.s)
    ::
        [%3 p=^]
      =^  p  gen  fol-loop(fol p.fol)
      [[[%3 nomm.p] dunno |] gen]
    ::
        [%4 p=^]
      =^  p  gen  fol-loop(fol p.fol)
      [[[%4 nomm.p] dunno |] gen]
    ::
        [%5 p=^ q=^]
      =^  p  gen  fol-loop(fol p.fol)
      =^  q  gen  fol-loop(fol q.fol)
      [[[%5 nomm.p nomm.q] dunno |] gen]
    ::
        [%6 p=^ q=^ r=^]
      =^  p  gen  fol-loop(fol p.fol)
      =^  q  gen  fol-loop(fol q.fol)
      =^  r  gen  fol-loop(fol r.fol)
      :_  gen
      :-  [%6 nomm.p nomm.q nomm.r]
      [(double-int prod.q prod.r) |]
    ::
        [%7 p=^ q=^]
      =^  p  gen  fol-loop(fol p.fol)
      =^  q  gen  fol-loop(fol q.fol, sub prod.p)
      [[[%7 nomm.p nomm.q] prod.q |] gen]
    ::
        [%8 p=^ q=^]
      fol-loop(fol [%7 [p.fol 0+1] q.fol])
    ::
        [%9 p=@ q=^]
      fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
    ::
        [%10 [a=@ don=^] rec=^]
      ?:  =(0 a.fol)  [[0+0 dunno |] gen]
      =^  don  gen  fol-loop(fol don.fol)
      =^  rec  gen  fol-loop(fol rec.fol)
      :_  gen
      :-  [%10 [a.fol nomm.don] nomm.rec]
      :_  |
      :-  (darn:so sock.prod.rec a.fol sock.prod.don)
      (edit:pi src.prod.rec a.fol src.prod.don)
    ::
        [%11 p=@ q=^]
      ?:  ?=(%bare p.fol)
        ::  %bare keeps a formula out of compiled nock: it is not analyzed,
        ::  and is run by an indirect call as it is written, with the hint,
        ::  which tells the runtime to give it to the plain interpreter.
        ::  The boundary of code that is compiled only under hints of its
        ::  own: an agent run by gall, say.
        ::
        fol-loop(fol [%2 [%0 1] 1 fol], bare-call &)
      =^  q  gen  fol-loop(fol q.fol)
      :_  gen
      :-  [%11 p.fol nomm.q q.fol]
      [prod.q |]
    ::
        [%11 [a=@ h=^] f=^]
      =?  .  &(=(a.fol %spot) =(1 -.h.fol))
        =*  dot  .
        =<  $
        ~%  %nock-11-soft  ..ride  ~
        |.
        =/  pot=(unit spot)  (soft-spot +.h.fol)
        ?~  pot  dot
        =?  area.gen  ?=(~ area.gen)  pot
        =.  seat  pot
        dot
      ::
      =^  h  gen  fol-loop(fol h.fol)
      ::  valid %memo generates a new call to an uninlineable function to be
      ::  memoized
      ::
      ?:  &(?=(%memo a.fol) saf.h ?=(^ sock.prod.h))
        ::  saf.h implies fully known sock.prod.h
        ::
        fol-loop(fol [%2 [%0 1] 1 f.fol], memo-key `data.sock.prod.h)
      =^  arm=(unit [b=bell k=(unit *)])  gen
        ?.  &(?=(%mean a.fol) !saf.h ?=(^ sock.prod.h))  [~ gen]
        =/  bat=sock  (pull:so sock.prod.h 2)
        ?.  &(?=(^ bat) =(& cape.bat) ?=(^ data.bat))  [~ gen]
        =^  call  gen  fol-loop(fol [%2 [%0 1] %0 2], sub prod.h, defer &)
        ?>  ?=([%2 * * ^] nomm.call)
        :_  gen
        :+  ~  b.u.info.nomm.call
        ?.  ?=(^ sock.prod.call)  ~
        ?.  (all:ca cape.sock.prod.call)  ~
        `data.sock.prod.call
      ::
      =^  f  gen  fol-loop(fol f.fol)
      ::  %fast: register the core in execution order
      ::
      =?  gen  ?=(%fast a.fol)
        =^  miss=?  regs.st.gen
          (register-fast sock.prod.h sock.prod.f regs.st.gen)
        ::
        ?.  miss  gen
        gen(misses.stats.st +(misses.stats.st.gen))
      ::
      =/  saf=?  &(?=(?(%spot %mean) a.fol) saf.h saf.f)
      :_  gen
      :_  [prod.f saf]
      ?^  arm  [%mean nomm.h b.u.arm nomm.f f.fol k.u.arm]
      [%11 [a.fol nomm.h] nomm.f f.fol]
    ::
        [%12 p=^ q=^]
      =^  p  gen  fol-loop(fol p.fol)
      =^  q  gen  fol-loop(fol q.fol)
      [[[%12 nomm.p nomm.q] dunno |] gen]
    ==
  --
--
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Compilation
::
::    Previous iterations of the SKA pipeline design included a data-flow
::    analysis step between call graph construction and compilation.  The
::    motivation for that was to reduce the work performed to compile a given
::    function, since the data-flow analysis requires a fixed point iteration
::    over a given SCC.  Once the data-flow analysis was complete, the
::    compilation itself could be done lazily, per function.  In the current
::    approach the compilation and the data-flow analysis are performed
::    together, to avoid having to keep these two steps in sync, which reduces
::    the complexity of the algorithm.  Maybe there is a way to add the
::    intermediate step without too much headache, but one would have to take
::    into account register allocation and code emission for branches and hints,
::    which would have to be synced with the subject shape prescribed by that
::    intermediate step.
::
::    Here we compile a SKA function with a destination-driven code generation
::    (DDCG) approach, except that for Nock 6 forks and some hints we produce a
::    lazy destination, which is collapsed when we satisfy it: either with a
::    Nock 1 literal, with a Nock 2/12 product, or with the input subject, once
::    the goal has bubbled up all the way to the root Nock formula of the SKA
::    function.
::
::    The motivation for the lazy destination approach here is the same as the
::    motivation for the poisoned register semantics and, later, %cel assertions
::    in the `sword` implementation: preventing crash relocation.  For the
::    compiler output to be at least correct, +mink semantics have to be
::    preserved, and +mink materializes the stack trace as a product of the
::    computation.  This means that if a function is called with a subject that
::    does not fit its argument shape, we can't just crash in the caller or
::    somewhere in the callee: we have to match the stack trace that we would
::    have had if we ran +mink unjetted.  In the general case of %mean hints
::    with traps that capture the subject inside of the callee, this means
::    entering the callee and crashing in the right place.
::
::    Furthermore, for better UX it makes sense to prevent crash relocation for
::    other hints used in debugging as well.  If I put a ~& before a crash site,
::    I would like to see the printout, even though it would be formally correct
::    to relocate the crash before the hint, as %slog hints are not recognized
::    by +mink.
::
::    This implementation achieves crash correctness by carrying basic block
::    labels together with the data requirements, represented by the $need type,
::    inside of a recursive data structure, $need-lazy.  Whenever the lazy need
::    is collapsed, the splitting code is emitted into the relevant labels.
::
::    Collapsing needs to a single atom (Nock 3/4/5, via +collapse-lazy-atom) or
::    to an arbitrary noun (Nock 2/12, via +kern and friends) is easy.  Doing
::    the same for the top-level subject is a lot harder, since we also want to
::    find the shape of the argument subject without pessimizing it too much.
::    This is why we accumulate the needs of branches lazily: collapsing them
::    properly requires knowing what data gets accessed by the code before and
::    after the fork.  Furthermore, branch collapsing is order sensitive, so we
::    do it in a fixed point loop, retrying shape collapses while accumulating
::    knowledge about the axes available outside of the branches.
::
::    Compiling a pessimized version of a function, with the entire subject as a
::    single argument, requires compiling the function normally, then compiling
::    that function in pessimized mode, where code is emitted before each
::    callsite to try to split the input subject for the callee and call the
::    optimized version; the pessimized version of the callee is called if any
::    of the checks fail.  That way optimized functions only ever call optimized
::    functions, and pessimized functions try to enter optimized functions.
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Compilation flags. Uncomment to enable.
::
::  Compute the input shapes of the compilation fixed point with +run-shape
::  instead of +run with code emission dropped
::
=/  dedicated-shape-pass  ~
::  Debug: check that both agree on the final pass
::
:: =/  shape-check  ~
::  Debug: check the whole-tree shape collapse against the nested one
::
:: =/  collapse-check  ~
::
::
|%
+$  hint-static  ?(%bout %xray)
+$  hint-dynamic  ?(%bout %xray %spin %jinx %live hint-dynamic-stop)
+$  hint-dynamic-stop  ?(%hunk %hand %lose %mean %spot %slog)
::  Data requirement of a computation. %both means both the root noun and some
::  of its descendants.
::  Normalizations:         [[%none ~] [%none ~]] --> [%none ~]
::                  [%both x [%none ~] [%none ~]] --> [%this x]
::
::  %lax: the noun whole or in parts, whichever its maker has: whole in .r
::  with .g 0, or .g 1 and the needs .h and .t met.  Nothing is consed and
::  nothing is fetched to meet it; the registers that the other form would
::  have filled hold 0.  It is the need that the lazy blocks past a fork have
::  of the fork's product (+lerf): a branch that conses the product hands on
::  the parts, a branch that has it in a register hands on the register, and
::  the block that reads it tells by .g.  On entry .g is a constant: the
::  parts where every call site holds them (+heft), the noun otherwise.
::
+$  need
  $~  [%none ~]
  $^  [p=need q=need]
  $%  [%both r=@uvre h=need t=need]
      [%this r=@uvre]
      [%none ~]
      [%lax g=@uvre r=@uvre h=need t=need]
  ==
::  Same as $need but no registers allocated, pure shape.
::
+$  need-ordered
  $~  [%none ~]
  $^  [p=need-ordered q=need-ordered]
  $%  [%both h=need-ordered t=need-ordered]
      [%this ~]
      [%none ~]
      [%lax h=need-ordered t=need-ordered]
  ==
::  Shape of a product returned in parts (+rets-scc):
::    ~:   a noun in one register
::    %c:  a pair whose halves are returned apart
::    %m:  an atom or a pair: a tag register, then the halves.  The tag is
::         the atom itself, or any cell when the product is a pair, so that
::         a test of the product (for a cell, for an atom) is a test of the
::         tag; the registers of the halves of an atom hold 0
::    %k:  an atom known to the caller: no register
::
+$  rets
  $@  ~
  $%  [%c p=rets q=rets]
      [%m p=rets q=rets]
      [%k n=@]
  ==
::  What +rets-scc knows of the structure of a product:
::    %top: nothing yet: a crash, a callee not analyzed yet
::    %one: a noun
::    %a:   an atom
::    %k:   a constant
::    %c:   a pair made by the function or returned in parts by a callee
::    %n:   a pair that exists already: a noun the function fetched into
::    %m:   an atom on some paths, a pair made on others
::
+$  form
  $~  %one
  $@  ?(%top %one %a)
  $%  [%k n=*]
      [%c h=form t=form]
      [%n h=form t=form]
      [%m h=form t=form]
  ==
::  Lazy data requirement, with needs of Nock 6 forks and Nock 11 crash relo-
::  cation boundaries.
::
::  sure: data requirement of this logical code block (this level of branchness,
::        crash relocation boundaries) + shape requirement with no registers.
::        The latter comes from Nock 0/10's with discarded products
::
::  fork: branches
::  bond: crash relocation boundaries due to hints
::
::            |
::            | sure
::            |
::           / \
::          /   \
::  y.fork |     | n.fork
::          \   /
::           \ /
::            |
::           ---  bond
::            |
::           --- 
::            |
::            | also sure
::            |
::
::
::  Registers read in lazy blocks. Code emitted into a lazy block (a spliced
::  %brn on a materialized conditional, moves and deconsing of a computed
::  product via +kern) does not read the register `def` directly but a proxy
::  register which is the key. `tag` is the region of the lazy block: the list
::  of merging Nock 6's (each given a fresh @uxid) whose branches contain it.
::  In +sect an entry made during the compilation of a branch is either inside
::  the branch (the definition dominates the uses, nothing to do) or past the
::  join block. Then `def` becomes an input parameter for the merging block on
::  one side, a new target register is allocated that becomes the input
::  parameter in the merging block, and on the other side a dummy register is
::  used as an input with a placeholder value. The proxy register now points to
::  the new target in the merging block. At the function entry the proxies are
::  guaranteed to be dominated by their respective defined registers, so
::  +rewrite-cond rewrites the proxies with their definitions directly.
::
+$  cond  (map @uvre [def=@uvre tag=(list @uxid)])
+$  sure  [ned=need lok=(set @)]
::
+$  need-lazy
  $+  need-lazy
  $;  |-
  $:  =sure
      fork=(list [y=[o=@uwoo laz=$] n=[o=@uwoo laz=$]])
      bond=(list [o=@uwoo laz=$])
  ==
::
::  there - target basic block
::  args  - arguments for that basic block
::  BBs with arguments: control flow merges (instead of phi nodes)
::  everywhere else args are empty, and there are assertions for that littered
::  around when we use there.jmp alone.
::
::  An empty argument supplies nothing: the parameter is never read on that
::  edge. Used by +sect to keep SSA form when only one branch defines a value.
::
+$  lazy-fork  [y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]]
+$  lazy-bond  [o=@uwoo laz=need-lazy]
::
+$  jmp  [args=(list (unit @uvre)) there=@uwoo]
::  goal of a computation.
::  %done: return the product of the computation, tail position. Used for TCO.
::  %pick: the product is used as a conditional in Nock 6: if 0 go to z, if 1
::         go to 1, else crash
::  %next: the most common goal. Put the product into registers in laz, then go
::  to `then`
::
+$  goal
  $%  [%pick z=jmp o=jmp]
      [%done ~]
      [%next laz=need-lazy then=jmp]
  ==
::
++  lazy-from-need
  |=  ned=need
  ^-  need-lazy
  [[ned ~] ~ ~]
::
++  lazy-from-reg
  |=  r=@uvre
  ^-  need-lazy
  [[this+r ~] ~ ~]
::  Compiler takes a goal and a Nomm formula and produces a $next for it.
::
+$  next  $>(%next goal)
::  $next but no lazy stuff
::
+$  next-resolved  [%next [[ned=need ~] ~ ~] [~ then=@uwoo]]
::  basic block: arguments if merge block, list of ops, lastly control flow ter-
::  minating op.
::
+$  blob  [par=(list @uvre) body=(list pole) fin=termin]
::  Linearized SKA-function: desired shape of its subject, number of registers
::  in that shape and the basic blocks, with the entry block having an index 0.
::
+$  straight  [need=need-ordered n-args=@ud blocks=(map @uwoo blob)]
::  Baked shape: the arguments of a function less the parts its bell knows,
::  which are immediates loaded in the prologue (+bake-need)
::
+$  baked  [ned=need imm=(list [r=@uvre v=*])]
::  Inner state for the linearizer
::
::  The compiler computes the subject shape and emits code in one traversal,
::  but the compilation fixed point only reads the shape, and code emission is
::  the more expensive half.  So every operation that touches the emitted IR
::  (.blocks, .tags, .cond) does nothing in %drop mode, used for the fixed
::  point iterations whose code is never used.  Register and block identifiers
::  are allocated eagerly either way, since needs and lazy blocks carry them.
::
+$  line-short
  $:  re-gen=@uvre
      bo-gen=_`@uwoo`1               ::  0 is reserved for the entry point
      id-gen=@uxid                   ::  branch region identifiers
      mode=?(%drop %run)
      blocks=(map @uwoo blob)
      tags=(map @uwoo (list @uxid))  ::  region of lazy need blocks
      =cond
      cache=comp-cache               ::  compiled callees, their SCCs
      soft=(map @uwoo soft-call)     ::  blocks where a callee's need is met
      sofs=(set @uxid)               ::  the same for shapes
      tst=(set @uvre)                ::  registers that are only tested (+tst-read)
      mine=rets                      ::  the shape the function returns in
  ==
::  A direct call whose callee takes parts that the subject formula does
::  not make by a cons.  The need of the callee is bound at blocks before
::  the call, where this function takes a noun apart for it (+soft-emit).
::  A part that the callee reads first thing (.sur, +sure-of) is fetched
::  with a crash: the callee would crash on it the same way.  Any other
::  part is the callee's to read, under a hint or on a branch or later: it
::  is tried, and a noun that is not a cell goes to the subject version of
::  the callee, whole, which crashes where the plain interpreter does, or
::  does not.
::
::  kin: a call, a tail call, or the push of a deferred %mean, whose arm
::  reads nothing unless the trace is rendered: all its parts are tried,
::  and where one is not there the trap is pushed whole
::
::  b, rin: the callee, its ring; ned: its need, with the registers of the
::  call; plain: the block of the call.  Three blocks run before it: head,
::  with the fetches that crash; that of the bond, with the moves and
::  conses that make the callee's arguments, and what a fork splices into
::  it (+insert-hop); last, with the tries.  pros, out: the registers of
::  the product and the block that follows, of a call that is no tail call
::  (out: the block past the push); ret: the shape the callee returns its
::  product in, which the subject version returns as one noun: it is taken
::  apart for the same registers (+conv); aux: the block of the epilogue
::  of a %mean, and its hint; req: the nouns to take apart, with the need
::  of each
::
+$  soft-call
  $:  kin=?(%call %tail %mean)
      b=bell
      rin=(unit ring)
      ned=need
      sur=need-ordered
      plain=@uwoo
      head=@uwoo
      last=@uwoo
      pros=(list @uvre)
      ret=rets
      out=@uwoo
      aux=*
      req=(list [src=@uvre ned=need])
  ==
::
+$  jets-comp-info  [need=need-ordered]
+$  jets-comp  (map ring jets-comp-info)
::  what compiling derives from the state: the functions compiled, dropped
::  when the jets change, and the SCCs found, which hold for good (+scc-of)
::
+$  comp-cache
  $:  nary=(map bell straight)      ::  functions of the parts they use
      mono=(map bell straight)      ::  functions of their whole subject
      sccs=(map bell (set bell))    ::  strongly connected components
      rets=(map bell rets)          ::  shapes of the products of .nary
      inl=(map bell nomm)           ::  code with the small callees inlined
      sure=(map bell need-ordered)  ::  what each reads first thing (+sure-of)
  ==
::  Non-control-flow ops
::
+$  pole
  $%  [%imm n=* d=@uvre]                          ::  n -> d
      [%mov s=@uvre d=@uvre]                      ::  s -> d
      [%inc s=@uvre d=@uvre]                      ::  +(s) -> d or crash
      [%con h=@uvre t=@uvre d=@uvre]              ::  [h t] -> d
      [%hed s=@uvre d=@uvre]                      ::  -.s -> d, does not crash
      [%tal s=@uvre d=@uvre]                      ::  +.s -> d, does not crash
      [%cel p=@uvre]                              ::  ?>  ?=(^ p)
      [%lob p=@uvre]                              ::  ?>  ?=(? p)
      [%equ l=@uvre r=@uvre]                      ::  =(l r) for the sideeffect
      [%hsp n=hint-static f=*]                    ::  prologue of a static hint
      [%hse n=hint-static f=*]                    ::  epilogue of a static hint
      [%hdp n=hint-dynamic p=@uvre f=*]           ::  prologue of a dynamic hint
      [%hde n=hint-dynamic p=@uvre f=*]           ::  epilogue of a dynamic hint
      [%hmp a=bell v=(list @uvre) f=*]            ::  push deferred %mean: a(v)
      [%hme a=bell v=(list @uvre) f=*]            ::  pop it
      [%hcp n=* f=*]                              ::  push %mean of product n
      [%hce n=* f=*]                              ::  pop it
      [%spy e=@uvre p=@uvre d=@uvre]              ::  .^(e p) -> d
      [%nok u=@uvre f=@uvre d=@uvre]              ::  .*(u f) -> d
      [%cal a=bell v=(list @uvre) d=@uvre]        ::  a(v) -> d
      [%caf a=bell v=(list @uvre) d=@uvre n=ring] ::  %cal but maybe jetted
      [%cam a=bell v=(list @uvre) d=@uvre k=*]    ::  %cal but memoized
      [%csl a=bell s=@uvre d=@uvre]               ::  %cal but sub is in one reg
      [%csf a=bell s=@uvre d=@uvre n=ring]        ::  %caf but sub is in one reg
      [%csm a=bell s=@uvre d=@uvre k=*]           ::  %cam but sub is in one reg
      [%rtl i=@ud d=@uvre]                        ::  part i of a call's product
  ==
::  Tags of the ops that cannot crash
::
+$  pole-not-crashing
  ?(%imm %mov %con %hed %tal %hsp %hse %hdp %hde %hmp %hme %hcp %hce %equ)
::  Control-flow ops
::
+$  termin
  $%  [%clq s=@uvre z=jmp o=jmp]            ::  ?^  s
      [%eqq l=@uvre r=@uvre z=jmp o=jmp]    ::  ?:  =(l r)
      [%brn s=@uvre z=jmp o=jmp]            ::  ?:  s  (crashes on non-loobean)
      [%brz s=@uvre z=jmp o=jmp]            ::  ?:  =(0 s), never crashes
      [%hop t=jmp]                          ::  unconditional block jump
      [%jmp a=bell v=(list @uvre)]          ::  %cal but in tail position
      [%jmf a=bell v=(list @uvre) n=ring]   ::  %caf but in tail position
      [%jsp a=bell s=@uvre]                 ::  %jmp but sub is in one reg
      [%jsf a=bell s=@uvre n=ring]          ::  %jmf but sub is in one reg
      [%don s=@uvre]                        ::  return s
      [%dox v=(lest @uvre) n=rets]          ::  return a product n in parts v
      [%bom o=(unit @uwoo)]                 ::  boom! crash. would've gone to o
  ==
::  get assignment register of the op if exists and does not crash
::  XX pure/safe function calls
::
++  get-reg-safe-assignment
  |=  op=pole
  ^-  (unit @uvre)
  =>  op
  ?-  -
    %imm  `d
    %mov  `d
    %inc  ~
    %con  `d
    %hed  `d
    %tal  `d
    %cel  ~
    %lob  ~
    %equ  ~
    %hsp  ~
    %hse  ~
    %hdp  ~
    %hde  ~
    %hmp  ~
    %hme  ~
    %hcp  ~
    %hce  ~
    %spy  ~
    %nok  ~
    %cal  ~
    %caf  ~
    %cam  ~
    %csl  ~
    %csf  ~
    %csm  ~
    %rtl  ~
  ==
++  get-regs
  |=  op=$%(pole termin)
  ^-  (list @uvre)
  ?-  -.op
    %imm  ~[d]:op
    %mov  ~[s d]:op
    %inc  ~[s d]:op
    %con  ~[h t d]:op
    %hed  ~[s d]:op
    %tal  ~[s d]:op
    %cel  ~[p]:op
    %lob  ~[p]:op
    %equ  ~[l r]:op
    %hsp  ~
    %hse  ~
    %hdp  ~[p]:op
    %hde  ~[p]:op
    %hmp  v.op
    %hme  v.op
    %hcp  ~
    %hce  ~
    %spy  ~[e p d]:op
    %nok  ~[u f d]:op
    %cal  [d v]:op
    %caf  [d v]:op
    %cam  [d v]:op
    %csl  ~[s d]:op
    %csf  ~[s d]:op
    %csm  ~[s d]:op
    %rtl  ~[d]:op
    %clq  [s.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %eqq  [l.op r.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %brn  [s.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %brz  [s.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %hop  (jmp-regs t.op)
    %jmp  v:op
    %jmf  v:op
    %jsp  ~[s]:op
    %jsf  ~[s]:op
    %don  ~[s]:op
    %dox  v:op
    %bom  ~
  ==
::
++  jmp-regs
  |=  j=jmp
  ^-  (list @uvre)
  (murn args.j same)
::
++  get-jmps
  |=  op=termin
  ^-  (list jmp)
  =>  op
  ?-  -
    %clq  ~[z o]
    %eqq  ~[z o]
    %brn  ~[z o]
    %brz  ~[z o]
    %hop  ~[t]
    %jmp  ~
    %jmf  ~
    %jsp  ~
    %jsf  ~
    %don  ~
    %dox  ~
    %bom  ~
  ==
::  Rename every register of a block, definitions included
::
++  map-regs
  |=  ren=$-(@uvre @uvre)
  ~%  %map-regs  ..ride  ~
  |=  b=blob
  ^-  blob
  =/  ren-jmp  |=(j=jmp j(args (turn args.j (lift ren))))
  :+  (turn par.b ren)
    %+  turn  body.b
    |=  op=pole
    ^-  pole
    ?-  -.op
      %imm  op(d (ren d.op))
      %mov  op(s (ren s.op), d (ren d.op))
      %inc  op(s (ren s.op), d (ren d.op))
      %con  op(h (ren h.op), t (ren t.op), d (ren d.op))
      %hed  op(s (ren s.op), d (ren d.op))
      %tal  op(s (ren s.op), d (ren d.op))
      %cel  op(p (ren p.op))
      %lob  op(p (ren p.op))
      %equ  op(l (ren l.op), r (ren r.op))
      %hsp  op
      %hse  op
      %hdp  op(p (ren p.op))
      %hde  op(p (ren p.op))
      %hmp  op(v (turn v.op ren))
      %hme  op(v (turn v.op ren))
      %hcp  op
      %hce  op
      %spy  op(e (ren e.op), p (ren p.op), d (ren d.op))
      %nok  op(u (ren u.op), f (ren f.op), d (ren d.op))
      %cal  op(v (turn v.op ren), d (ren d.op))
      %caf  op(v (turn v.op ren), d (ren d.op))
      %cam  op(v (turn v.op ren), d (ren d.op))
      %csl  op(s (ren s.op), d (ren d.op))
      %csf  op(s (ren s.op), d (ren d.op))
      %csm  op(s (ren s.op), d (ren d.op))
      %rtl  op(d (ren d.op))
    ==
  =/  fin  fin.b
  ?-  -.fin
    %clq  fin(s (ren s.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %eqq
      fin(l (ren l.fin), r (ren r.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %brn  fin(s (ren s.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %brz  fin(s (ren s.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %hop  fin(t (ren-jmp t.fin))
    %jmp  fin(v (turn v.fin ren))
    %jmf  fin(v (turn v.fin ren))
    %jsp  fin(s (ren s.fin))
    %jsf  fin(s (ren s.fin))
    %don  fin(s (ren s.fin))
    %dox  fin(v [(ren i.v.fin) (turn t.v.fin ren)])
    %bom  fin
  ==
--
::  Check that $next-resolved nests under $next
::
=+  `next`*next-resolved
=>  +
::
|%
::  Compiles `func` with the root subject as a sole argument, plus its SCC
::  including itself as N-ary functions
::
::  The SCC of a bell: found before, or by Tarjan over the functions it
::  reaches whose SCCs are not found yet.
::
++  scc-of
  ~%  %scc-of  ..ride  ~
  |=  [b=bell calls=(map bell (set bell)) sccs=(map bell (set bell))]
  ^-  [(set bell) sccs=(map bell (set bell))]
  ?^  s=(~(get by sccs) b)  [u.s sccs]
  =/  sub=(jug bell bell)
    =|  sub=(jug bell bell)
    =/  q=(list bell)  ~[b]
    |-  ^+  sub
    ?~  q  sub
    ?:  (~(has by sub) i.q)  $(q t.q)
    =/  cs=(set bell)
      %-  ~(rep in (~(gut by calls) i.q ~))
      |=  [c=bell acc=(set bell)]
      ?:((~(has by sccs) c) acc (~(put in acc) c))
    ::
    $(q (weld ~(tap in cs) t.q), sub (~(put by sub) i.q cs))
  ::
  =.  sccs
    %+  roll  (tarjan sub)
    |=  [s=(set bell) acc=_sccs]
    (~(rep in s) |=([m=bell acc=_acc] (~(put by acc) m s)))
  ::
  [(~(got by sccs) b) sccs]
::  Inlining.  A direct call of a function that is small, not recursive,
::  not memoized and without a driver is replaced by the function's code,
::  run on the subject the call made for it: [%2 p q info] becomes [%7 p n].
::  The needs of that code then reach the caller's registers and its product
::  goes where the caller wants it, where a call moves both through the
::  callee's interface.  The formula of the call is dropped, so it must be
::  safe to drop.  The code of a function, inlined into, is found once.
::
++  inline-max  48   ::  nodes of the code of a function that is inlined
::
++  nomm-size
  |=  =nomm
  ^-  @ud
  =|  n=@ud
  |-  ^-  @ud
  ?:  (gth n inline-max)  n
  =.  n  +(n)
  ?-    nomm
      [^ *]      $(nomm +.nomm, n $(nomm -.nomm))
      [%0 *]     n
      [%1 *]     n
      [%2 *]     $(nomm q.nomm, n $(nomm p.nomm))
      [%3 *]     $(nomm p.nomm)
      [%4 *]     $(nomm p.nomm)
      [%5 *]     $(nomm q.nomm, n $(nomm p.nomm))
      [%6 *]     $(nomm r.nomm, n $(nomm q.nomm, n $(nomm p.nomm)))
      [%7 *]     $(nomm q.nomm, n $(nomm p.nomm))
      [%10 *]    $(nomm q.nomm, n $(nomm q.p.nomm))
      [%11 *]    ?@  p.nomm  $(nomm q.nomm)
                 $(nomm q.nomm, n $(nomm q.p.nomm))
      [%12 *]    $(nomm q.nomm, n $(nomm p.nomm))
      [%mean *]  $(nomm q.nomm, n $(nomm p.nomm))
  ==
::  the functions a piece of code calls directly
::
++  nomm-callees
  |=  =nomm
  ^-  (set bell)
  =|  out=(set bell)
  |-  ^-  (set bell)
  ?-    nomm
      [^ *]      $(nomm +.nomm, out $(nomm -.nomm))
      [%0 *]     out
      [%1 *]     out
  ::
      [%2 *]
    =?  out  ?=(^ info.nomm)  (~(put in out) b.u.info.nomm)
    $(nomm q.nomm, out $(nomm p.nomm))
  ::
      [%3 *]     $(nomm p.nomm)
      [%4 *]     $(nomm p.nomm)
      [%5 *]     $(nomm q.nomm, out $(nomm p.nomm))
      [%6 *]     $(nomm r.nomm, out $(nomm q.nomm, out $(nomm p.nomm)))
      [%7 *]     $(nomm q.nomm, out $(nomm p.nomm))
      [%10 *]    $(nomm q.nomm, out $(nomm q.p.nomm))
      [%11 *]    ?@  p.nomm  $(nomm q.nomm)
                 $(nomm q.nomm, out $(nomm q.p.nomm))
      [%12 *]    $(nomm q.nomm, out $(nomm p.nomm))
      [%mean *]  $(nomm q.nomm, out $(nomm p.nomm))
  ==
::
++  inlined
  ~%  %inlined  ..ride  ~
  |=  $:  b=bell
          long-ska=_[=_code =_jets =_calls =_held]:*long-ska
          jets-hot=jets-comp
          cache=comp-cache
      ==
  ^-  [nomm comp-cache]
  =*  inlined-loop  $
  ?^  n=(~(get by inl.cache) b)  [u.n cache]
  =/  hot
    |=  c=bell
    ^-  ?
    ?=(^ (biff (~(get by call.cole.jets.long-ska) c) ~(get by jets-hot)))
  ::
  =-  [new cache(inl (~(put by inl.cache) b new))]
  ^-  [new=nomm =_cache]
  =/  =nomm  nomm:(~(got by code.long-ska) b)
  ?:  inline-off  [nomm cache]
  |-  ^-  [^nomm comp-cache]
  ?-    nomm
      [^ *]
    =^  a  cache  $(nomm -.nomm)
    =^  d  cache  $(nomm +.nomm)
    [[a d] cache]
  ::
      [%0 *]  [nomm cache]
      [%1 *]  [nomm cache]
  ::
      [%2 *]
    =^  p  cache  $(nomm p.nomm)
    =^  q  cache  $(nomm q.nomm)
    =/  keep=^nomm  [%2 p q info.nomm]
    ?~  info.nomm  [keep cache]
    =/  c=bell  b.u.info.nomm
    ?.  &(?=(~ k.u.info.nomm) (safe-fol-fol q.nomm) !(hot c))
      [keep cache]
    =^  s=(set bell)  sccs.cache  (scc-of c calls.long-ska sccs.cache)
    ?.  ?=([* ~ ~] s)  [keep cache]
    ?:  (~(has in (~(gut by calls.long-ska) c ~)) c)  [keep cache]
    =^  m=^nomm  cache  inlined-loop(b c, cache cache)
    ?:  (gth (nomm-size m) inline-max)  [keep cache]
    [[%7 p m] cache]
  ::
      [%3 *]
    =^  p  cache  $(nomm p.nomm)
    [[%3 p] cache]
  ::
      [%4 *]
    =^  p  cache  $(nomm p.nomm)
    [[%4 p] cache]
  ::
      [%5 *]
    =^  p  cache  $(nomm p.nomm)
    =^  q  cache  $(nomm q.nomm)
    [[%5 p q] cache]
  ::
      [%6 *]
    =^  p  cache  $(nomm p.nomm)
    =^  q  cache  $(nomm q.nomm)
    =^  r  cache  $(nomm r.nomm)
    [[%6 p q r] cache]
  ::
      [%7 *]
    =^  p  cache  $(nomm p.nomm)
    =^  q  cache  $(nomm q.nomm)
    [[%7 p q] cache]
  ::
      [%10 *]
    =^  v  cache  $(nomm q.p.nomm)
    =^  q  cache  $(nomm q.nomm)
    [[%10 [p.p.nomm v] q] cache]
  ::
      [%11 *]
    ?@  p.nomm
      =^  q  cache  $(nomm q.nomm)
      [[%11 p.nomm q body.nomm] cache]
    =^  v  cache  $(nomm q.p.nomm)
    =^  q  cache  $(nomm q.nomm)
    [[%11 [p.p.nomm v] q body.nomm] cache]
  ::
      [%12 *]
    =^  p  cache  $(nomm p.nomm)
    =^  q  cache  $(nomm q.nomm)
    [[%12 p q] cache]
  ::
      [%mean *]
    =^  p  cache  $(nomm p.nomm)
    =^  q  cache  $(nomm q.nomm)
    [[%mean p b.nomm q body.nomm k.nomm] cache]
  ==
::  Products in parts.  A function whose product is a pair on every path
::  that returns, and a pair it makes itself on one of them at least (a
::  cons, an edit, the product of a callee that returns in parts), returns
::  the halves of the pair in registers instead of the cell, and so on into
::  the halves: the cell is made only where a caller wants it whole.  The
::  shape is found here, per SCC, before the functions are compiled against
::  it: the meet of the forms of the returning paths, a fixed point from
::  %top for the members.
::
::  On a path that does not make the pair, the product must still be known
::  to be one, to be split without a check that could fail: a constant, or
::  a noun the function has fetched into before (%n).  A pair that no path
::  makes is returned whole: splitting it would only make the callers that
::  want it cons it again (measured on +ream of hoon.hoon: a fifth more
::  cells allocated).
::
::  A form that claims less than it could costs speed only, since a call
::  site receives the shape of its callee, not the form of the call.
::
::  Sums (.rets-sums, off: measured, they do not pay in the interpreter).
::  A product that is an atom on some returning paths and a made pair on
::  others is returned as a tag register and the halves (%m).  The tag is
::  the atom itself, or any cell when the product is a pair, so a test of
::  the product, for a cell or against an atom, is the same test of the
::  tag: the caller gives the tag to a register that is only tested
::  (.tst in the compiler's state), checks it for a cell where it fetches
::  from the product, and conses the pair, on the cell side of a branch
::  on the tag, only where the product is wanted whole.  The callee fills
::  the registers where the returned formula shows its form (a cons, a
::  constant) and tells any other noun apart when it has it (+fill,
::  +unpack).  An atom that every path agrees on takes no register (%k).
::
::  A function with a driver returns one noun, as the driver does.  So does a
::  memoized call (the interpreter conses for it), and a function of its
::  whole subject (the .mono ones).
::
++  rets-max    6   ::  registers of a product, at most (the interpreter: 8)
++  rets-sums   |   ::  an atom on some paths and a made pair on others: %m
++  rets-opaque  |  ::  a noun on some paths and a made pair on others: %m
++  form-depth  4   ::  depth of the forms followed
++  rets-known  &   ::  nouns the function fetched into are pairs too
++  inline-off  |   ::  debug: no inlining
::
++  form-pair
  |=  [made=? h=form t=form]
  ^-  form
  ?:(made [%c h t] [%n h t])
::
++  form-atom
  |=  f=form
  ^-  ?
  |(?=(%a f) &(?=([%k *] f) ?=(@ n.f)))
::  the halves of a form, where it is a pair
::
++  form-half
  |=  f=form
  ^-  (unit [p=form q=form])
  ?@  f  ~
  ?-  -.f
    %c  `[h.f t.f]
    %n  `[h.f t.f]
    %m  `[h.f t.f]
    %k  ?@(n.f ~ `[[%k -.n.f] [%k +.n.f]])
  ==
::
++  form-meet
  |=  [a=form b=form d=@ud]
  ^-  form
  ?:  ?=(%top a)  b
  ?:  ?=(%top b)  a
  ?:  =(a b)  a
  =/  aa=?  (form-atom a)
  =/  ab=?  (form-atom b)
  ?:  &(aa ab)  %a
  ::  an atom on one side: a sum, if the other side makes a pair
  ::
  ?:  |(aa ab)
    =/  c=form  ?:(aa b a)
    ?.  rets-sums  %one
    ?:  ?=([%c *] c)  [%m h.c t.c]
    ?:  ?=([%m *] c)  c
    %one
  ::  a noun on one side: a sum, to be told apart when it is returned
  ::
  ?:  |(?=(%one a) ?=(%one b))
    =/  c=form  ?:(?=(%one a) b a)
    ?.  &(rets-sums rets-opaque !=(0 d))  %one
    ?.  ?=([?(%c %m) *] c)  %one
    :+  %m
      $(a %one, b h.c, d (dec d))
    $(a %one, b t.c, d (dec d))
  ?:  =(0 d)  %one
  =/  ha  (form-half a)
  =/  hb  (form-half b)
  ?~  ha  %one
  ?~  hb  %one
  =/  h=form  $(a p.u.ha, b p.u.hb, d (dec d))
  =/  t=form  $(a q.u.ha, b q.u.hb, d (dec d))
  ?:  |(?=([%m *] a) ?=([%m *] b))  [%m h t]
  ::  made on one path at least: worth returning in parts
  ::
  (form-pair |(?=([%c *] a) ?=([%c *] b)) h t)
::
++  form-slot
  |=  [axe=@ f=form]
  ^-  form
  ?:  =(1 axe)  f
  ?:  ?=(%a f)  %top
  ?@  f  f
  =/  h  (form-half f)
  ?~  h  %top
  ?-  (cap axe)
    %2  $(axe (mas axe), f p.u.h)
    %3  $(axe (mas axe), f q.u.h)
  ==
::
++  form-edit
  |=  [axe=@ don=form rec=form]
  ^-  form
  ?:  =(1 axe)  don
  ?:  ?=(?(%top %a) rec)  %top
  =/  h=(unit [p=form q=form])
    ?:  ?=(%one rec)  `[%one %one]
    (form-half rec)
  ?~  h  %top
  ?-  (cap axe)
    %2  [%c $(axe (mas axe), rec p.u.h) q.u.h]
    %3  [%c p.u.h $(axe (mas axe), rec q.u.h)]
  ==
::
++  form-cap
  |=  [f=form d=@ud]
  ^-  form
  ?@  f  f
  ?:  ?=(%k -.f)  f
  ?:  =(0 d)  %one
  =/  h=form  $(f h.f, d (dec d))
  =/  t=form  $(f t.f, d (dec d))
  ?:  ?=(%m -.f)  [%m h t]
  (form-pair ?=(%c -.f) h t)
::  the shape a form is returned in: a pair or a sum that was made, a
::  constant atom below one
::
++  form-rets
  |=  f=form
  ^-  rets
  =/  top=?  &
  |-  ^-  rets
  ?@  f  ~
  ?-  -.f
    %n  ~
    %k  ?:(|(top !rets-sums ?=(^ n.f)) ~ [%k n.f])
    %c  [%c $(f h.f, top |) $(f t.f, top |)]
    %m  [%m $(f h.f, top |) $(f t.f, top |)]
  ==
::
++  rets-form
  |=  r=rets
  ^-  form
  ?~  r  %one
  ?-  -.r
    %k  [%k n.r]
    %c  [%c $(r p.r) $(r q.r)]
    %m  [%m $(r p.r) $(r q.r)]
  ==
::  registers of a shape
::
++  rets-size
  |=  r=rets
  ^-  @ud
  ?~  r  1
  ?-  -.r
    %k  0
    %c  (add $(r p.r) $(r q.r))
    %m  +((add $(r p.r) $(r q.r)))
  ==
::  a shape cut down to .n registers at most
::
++  rets-trim
  |=  [r=rets n=@ud]
  ^-  rets
  ?~  r  ~
  ?-    -.r
      %k  r
      %c
    ?:  (lth n 2)  ~
    =/  h=rets  $(r p.r, n (dec n))
    [%c h $(r q.r, n (sub n (rets-size h)))]
  ::
      %m
    ?:  (lth n 3)  ~
    =/  h=rets  $(r p.r, n (sub n 2))
    [%m h $(r q.r, n (sub n +((rets-size h))))]
  ==
::  what a fetch of .axe tells of the noun fetched from: it has cells down
::  to the axis; .cel: the noun at the axis is a cell too
::
++  form-know
  |=  [axe=@ f=form cel=?]
  ^-  form
  ?:  ?=(%top f)  %top
  ?:  ?=(%a f)  ?:(|(cel !=(1 axe)) %top %a)
  ?:  ?=([%k *] f)  f
  ?:  =(1 axe)
    ?.  cel  f
    ?:  ?=(%one f)  [%n %one %one]
    ?:  ?=([%m *] f)  [%c h.f t.f]
    f
  =/  h=[made=? p=form q=form]
    ?:  ?=(%one f)  [| %one %one]
    [?=(?(%c %m) -.f) h.f t.f]
  ?-  (cap axe)
    %2  (form-pair made.h $(axe (mas axe), f p.h) q.h)
    %3  (form-pair made.h p.h $(axe (mas axe), f q.h))
  ==
::  what a test told of the noun at .axe, which was fetched before
::
++  form-jab
  |=  [axe=@ f=form fun=$-(form form)]
  ^-  form
  ?:  =(1 axe)  (fun f)
  ?@  f  f
  ?:  ?=(%k -.f)  f
  =/  made=?  ?=(?(%c %m) -.f)
  ?-  (cap axe)
    %2  (form-pair made $(axe (mas axe), f h.f) t.f)
    %3  (form-pair made h.f $(axe (mas axe), f t.f))
  ==
::  What a test tells each branch of the part of the subject it tested: a
::  cell or an atom, or the atom it was found equal to.  The atom and the
::  equality matter to sums only
::
++  form-test
  |=  [=nomm sub=form]
  ^-  [yes=form nay=form]
  ?.  rets-known  [sub sub]
  ?:  &(?=([%3 %0 @] nomm) !=(0 p.p.nomm))
    :-  (form-know p.p.nomm sub &)
    ?.  rets-sums  sub
    (form-jab p.p.nomm sub |=(f=form ?:(?=(?(%one [%m *]) f) %a f)))
  ?.  rets-sums  [sub sub]
  =/  eq=(unit [axe=@ n=@])
    ?:  ?=([%5 [%1 @] %0 @] nomm)  `[p.q.nomm p.p.nomm]
    ?:  ?=([%5 [%0 @] %1 @] nomm)  `[p.p.nomm p.q.nomm]
    ~
  ?~  eq  [sub sub]
  ?:  =(0 axe.u.eq)  [sub sub]
  :_  sub
  (form-jab axe.u.eq sub |=(f=form `form`[%k n.u.eq]))
::  form of the product of a formula on a subject of the form .sub; .loc
::  has the forms of the SCC so far, .ext the shapes of the functions
::  outside.  The form of the subject is refined along the way by what the
::  formula fetches from it (.rets-known): a noun that was fetched into is
::  a cell where it is returned later.
::
++  form-of
  ~%  %form-of  ..ride  ~
  |=  $:  =nomm
          sub=form
          scc=(set bell)
          loc=(map bell form)
          ext=(map bell rets)
      ==
  ^-  form
  =<  pro
  |-  ^-  [pro=form sub=form]
  ?-    nomm
      [^ *]
    =/  a  $(nomm -.nomm)
    =/  b  $(nomm +.nomm, sub sub.a)
    [[%c pro.a pro.b] sub.b]
  ::
      [%0 *]
    ?:  =(0 p.nomm)  [%top %top]
    =?  sub  rets-known  (form-know p.nomm sub |)
    [(form-slot p.nomm sub) sub]
  ::
      [%1 *]  [[%k p.nomm] sub]
  ::
      [%2 *]
    =/  a  $(nomm p.nomm)
    =/  b  $(nomm q.nomm, sub sub.a)
    :_  sub.b
    ?~  info.nomm  %one
    ?^  k.u.info.nomm  %one
    ?:  (~(has in scc) b.u.info.nomm)  (~(gut by loc) b.u.info.nomm %top)
    (rets-form (~(gut by ext) b.u.info.nomm ~))
  ::
      [%3 *]  [%a sub:$(nomm p.nomm)]
      [%4 *]  [%a sub:$(nomm p.nomm)]
  ::
      [%5 *]
    =/  a  $(nomm p.nomm)
    [%a sub:$(nomm q.nomm, sub sub.a)]
  ::
      [%6 *]
    =/  c  $(nomm p.nomm)
    =/  [yes=form nay=form]  (form-test p.nomm sub.c)
    =/  y  $(nomm q.nomm, sub yes)
    =/  n  $(nomm r.nomm, sub nay)
    ?:  ?=(%top pro.y)  n
    ?:  ?=(%top pro.n)  y
    ::  past the branches the subject is known as it was before them: what
    ::  both branches fetched is not looked for, a meet of two forms of the
    ::  subject at every branch being most of the cost of this pass on the
    ::  large arms of the compiler
    ::
    [(form-meet pro.y pro.n form-depth) sub.c]
  ::
      [%7 *]
    =/  a  $(nomm p.nomm)
    [pro:$(nomm q.nomm, sub pro.a) sub.a]
  ::
      [%10 *]
    =/  a  $(nomm q.p.nomm)
    =/  b  $(nomm q.nomm, sub sub.a)
    [(form-edit p.p.nomm pro.a pro.b) sub.b]
  ::
      [%11 *]
    ?@  p.nomm  $(nomm q.nomm)
    =/  a  $(nomm q.p.nomm)
    $(nomm q.nomm, sub sub.a)
  ::
      [%12 *]
    =/  a  $(nomm p.nomm)
    [%one sub:$(nomm q.nomm, sub sub.a)]
  ::
      [%mean *]
    =/  a  $(nomm p.nomm)
    $(nomm q.nomm, sub sub.a)
  ==
::  the shapes of the products of an SCC, into the cache; of its callees
::  first
::
++  rets-scc
  ~%  %rets-scc  ..ride  ~
  |=  $:  scc=(set bell)
          long-ska=_[=_code =_jets =_calls =_held]:*long-ska
          jets-hot=jets-comp
          cache=comp-cache
      ==
  ^-  comp-cache
  =*  rets-loop  $
  =/  mem=(list bell)  ~(tap in scc)
  ?:  (levy mem ~(has by rets.cache))  cache
  =.  cache
    %+  roll  mem
    |=  [m=bell cache=_cache]
    =^  n=nomm  cache  (inlined m long-ska jets-hot cache)
    ::  the callees of the code as it was, too: the function of the whole
    ::  subject calls them (+compile-unary)
    ::
    %-  %~  rep  in
        %-  ~(uni in (nomm-callees n))
        (nomm-callees nomm:(~(got by code.long-ska) m))
    |=  [c=bell cache=_cache]
    ?:  |((~(has in scc) c) (~(has by rets.cache) c))  cache
    =^  s=(set bell)  sccs.cache  (scc-of c calls.long-ska sccs.cache)
    rets-loop(scc s, cache cache)
  ::
  =/  hot
    |=  b=bell
    ^-  ?
    ?=(^ (biff (~(get by call.cole.jets.long-ska) b) ~(get by jets-hot)))
  ::
  =/  loc=(map bell form)
    %-  ~(gas by *(map bell form))
    (murn mem |=(b=bell ?:((hot b) `[b %one] ~)))
  ::
  =/  fuel=@ud  32
  |-  ^-  comp-cache
  =/  res=[any=? loc=(map bell form)]
    %+  roll  mem
    |=  [m=bell any=_`?`| loc=_loc]
    ?:  (hot m)  [any loc]
    =/  f=form
      %+  form-cap
        %:  form-of
          (~(got by inl.cache) m)
          %one
          scc
          loc
          rets.cache
        ==
      form-depth
    ?:  =(f (~(gut by loc) m %top))  [any loc]
    [& (~(put by loc) m f)]
  ::
  ?:  &(any.res !=(0 fuel))  $(loc loc.res, fuel (dec fuel))
  =?  loc.res  any.res  ~
  %=    cache
      rets
    %-  ~(gas by rets.cache)
    %+  turn  mem
    |=  b=bell
    =/  r=rets
      (rets-trim (form-rets (~(gut by loc.res) b %top)) rets-max)
    [b ?:(=(0 (rets-size r)) ~ r)]
  ==
::
++  compile-unary
  ~%  %compile-unary  ..ride  ~
  |=  $:  func=bell
          scc=(set bell)
          long-ska=_[=_code =_jets =_calls =_held]:*long-ska
          jets-hot=jets-comp
          cache=comp-cache
      ==
  ^-  [[straight (map bell straight)] cache=comp-cache]
  =/  args  +<
  %-  road-pure  |.
  ::  Compile normally
  ::
  =^  n-ary-map=(map bell straight)  cache  (compile-scc-in +.args)
  =/  comp  (comp scc long-ska jets-hot n-ary-map ~ func)
  ::  Compile the pessimized version
  ::
  =|  gen=line-short
  =.  cache.gen  cache
  ::  nothing is inlined into the function of the whole subject: a %mean
  ::  trap is deferred in the n-ary functions only (+run), and a callee
  ::  inlined here would push its traps whole
  ::
  =^  nex=next  gen
    (~(run comp gen) & nomm:(~(got by code.long-ska) func) [%done ~] ~ ~)
  ::  Collapse the subject need to a single noun, finalize
  ::
  =^  [o=@uwoo sub=@uvre]  gen  (~(kerf comp gen) nex)
  :_  cache.gen
  :-  (~(to-straight comp gen) [%next [[this+sub ~] ~ ~] ~ o])
  n-ary-map
::
++  compile-scc
  ~%  %compile-scc  ..ride  ~
  |=  $:  scc=(set bell)
          long-ska=_[=_code =_jets =_calls =_held]:*long-ska
          jets-hot=jets-comp
          cache=comp-cache
      ==
  ^-  [(map bell straight) cache=comp-cache]
  =*  args  +<
  (road-pure |.((compile-scc-in args)))
::  The compilation proper, called directly for callees so that the whole
::  recursion shares the entry's road
::
++  compile-scc-in
  ~%  %compile-scc-in  ..ride  ~
  |=  $:  scc=(set bell)
          long-ska=_[=_code =_jets =_calls =_held]:*long-ska
          jets-hot=jets-comp
          cache=comp-cache
      ==
  ^-  [(map bell straight) cache=comp-cache]
  ?:  (levy ~(tap in scc) ~(has by nary.cache))
    :_  cache
    %-  ~(gas by *(map bell straight))
    (turn ~(tap in scc) |=(b=bell [b (~(got by nary.cache) b)]))
  =.  cache  (rets-scc scc long-ska jets-hot cache)
  ::  Only the subject shapes in .map-local are read by the loop, so the rest
  ::  of the straight is a placeholder until the fixed point is reached, when
  ::  the whole SCC is compiled once more with .done set, this time for real
  ::
  =|  map-local=(map bell straight)
  ::  the callees of each member in the SCC
  ::
  =/  kids=(jug bell bell)
    %-  ~(rep in scc)
    |=  [m=bell acc=(jug bell bell)]
    (~(put by acc) m (~(int in (~(gut by calls.long-ska) m ~)) scc))
  ::  A function alone in its SCC that does not call itself needs no fixed
  ::  point: the final pass computes its subject shape by itself
  ::
  =/  done=?  &(?=([* ~ ~] scc) !(~(has ju kids) n.scc n.scc))
  ::  Compile one member against the shapes in .map-local, and against
  ::  what the members read first thing (.sure.cache); produces whether its
  ::  shape changed, or what it reads first thing (not used in the final
  ::  pass)
  ::
  =/  member
    ~%  %compile-scc-fn  ..ride  ~
    |=  $:  b=bell
            mode=scc-mode
            map-local=(map bell straight)
            top=(map bell need-ordered)
            cache=comp-cache
        ==
    ^-  [? (map bell straight) comp-cache]
    =/  done=?  ?=(%done mode)
    ?>  ?=(^ less.b)
    =/  lor=lore  [cape.less.b (~(gut by held.long-ska) b |)]
    =/  comp  (comp scc long-ska jets-hot map-local top b)
    =^  =nomm  cache  (inlined b long-ska jets-hot cache)
    ::  Until the fixed point only the input shape is needed: from the
    ::  shape-only traversal, or from the full compilation with code emission
    ::  dropped.  The final pass compiles for real, emitting code right away.
    ::
    =|  gen=line-short
    =.  cache.gen  cache
    =.  mine.gen   (~(got by rets.cache) b)
    ::  Baking: the leaves of the shape inside what the bell knows of the
    ::  subject are immediates loaded in the prologue, not arguments: .bak
    ::  has the shape of the arguments and the registers to load, .ned-final
    ::  the one the body's registers follow
    ::
    ::  .sur: what the function reads first thing (+sure-of)
    ::
    =*  res  $:  need-new=need-ordered
                 laz=need-lazy
                 ned-final=need
                 bak=baked
                 o=@uwoo
                 sur=need-ordered
             ==
    ::
    =^  ,res  gen
      !@  dedicated-shape-pass
        =.  mode.gen  ?:(done %run %drop)
        =^  nex  gen  (~(run comp gen) | nomm [%done ~] ~ ~)
        =^  [ned-final=need laz=need-lazy o=@uwoo]  gen
          (~(collapse-shape comp gen) nex lor)
        =/  bak=baked  (bake-need ned-final less.b)
        =/  sur
          (sure-of [(need-to-ordered ned.sure.laz) lok.sure.laz] cape.less.b)
        ::
        [[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]
      ?.  done
        =^  l=laze  gen  (~(run-shape comp gen) nomm [%done ~] ~)
        =/  shape
          %+  bake-need-ord
            ?:  ?=(%must mode)  (laze-collapse l lor)
            (laze-may l lor)
          less.b
        :_  gen
        [shape *need-lazy *need *baked `@uwoo`0 (sure-of sure.l cape.less.b)]
      =.  mode.gen  %run
      =^  nex  gen  (~(run comp gen) | nomm [%done ~] ~ ~)
      =^  [ned-final=need laz=need-lazy o=@uwoo]  gen
        (~(collapse-shape comp gen) nex lor)
      =/  bak=baked  (bake-need ned-final less.b)
      =/  sur
        (sure-of [(need-to-ordered ned.sure.laz) lok.sure.laz] cape.less.b)
      ::
      [[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]
    =.  cache  cache.gen
    =/  was=(unit need-ordered)  (~(get by sure.cache) b)
    ::  what is read first thing only gets less from one compile to the
    ::  next (+int-need-ord): a part of it is read first thing too.  The
    ::  final pass compiles against what the sweeps found
    ::
    =/  sur=need-ordered
      ?~  was  sur
      ?:  done  u.was
      (int-need-ord u.was sur)
    =.  sure.cache  (~(put by sure.cache) b sur)
    =/  moved=?  !=(sur (fall was [%none ~]))
    ::  Debug assert of +run-shape correctenss
    ::
    =>  =*  dot  .
        !@  shape-check  dot
        ?.  done  dot
        =/  l=laze  -:(~(run-shape comp gen) nomm [%done ~] ~)
        =/  shape  (bake-need-ord (laze-collapse l lor) less.b)
        ~|  [%shape-mismatch b shape need-new]
        ?>  =(shape need-new)
        dot
    ::
    ::  Finalization: emit the subject deconsing code, coerce the subject to
    ::  the pessimized shape if there is one, and renumber the registers
    ::
    =/  finish
      ~%  %compile-scc-finish  ..ride  ~
      |=  pessimized=(unit need-ordered)
      ^-  straight
      ::  argument count and the blocks are bunted unless fixed point of the
      ::  subject shape was achieved
      ::
      ?.  done  [?~(pessimized need-new u.pessimized) 0 ~]
      =.  gen  (~(coerce-lazy comp gen) ned-final o laz cape.less.b)
      =.  gen  ~(soft-done comp gen)
      ::  the baked registers are loaded before the deconsing code
      ::
      =.  gen
        (~(add-ops comp gen) o (turn imm.bak |=([r=@uvre v=*] [%imm v r])))
      =/  res=next-resolved  [%next [[ned.bak ~] ~ ~] ~ o]
      ?~  pessimized  (~(to-straight comp gen) res)
      =^  coerced=next-resolved  gen
        (~(coerce-soft comp gen) u.pessimized res)
      (~(to-straight comp gen) coerced)
    ::  The shape changed when it is new and needs something, or when the MSG
    ::  with the previous one (taken to avoid divergence) differs from it
    ::
    ::  A first shape is a change for the callers that were compiled with
    ::  another: nothing, or what the member may read (+callee-need)
    ::
    ?~  s-previous=(~(get by map-local) b)
      :+  ?|  moved
              !?=([%none ~] need-new)
              !?=([%none ~] (~(gut by top) b [%none ~]))
          ==
        (~(put by map-local) b (finish ~))
      cache
    =/  need-pessimized  (msg-need-ord need-new need.u.s-previous lor)
    ::  Debug assert: the final pass finds the shape of the sweeps
    ::
    =>  =*  dot  .
        !@  shape-check  dot
        ?.  done  dot
        ~|  [%shape-moved b need-pessimized need.u.s-previous]
        ?>  =(need-pessimized need.u.s-previous)
        dot
    ::
    :+  |(moved !=(need-pessimized need.u.s-previous))
      %+  ~(put by map-local)  b
      ?:  =(need-pessimized need-new)  (finish ~)
      (finish `need-pessimized)
    cache
  ::  The final pass: every member compiled for real
  ::
  ::  It compiles each member as its last sweep did, against the same
  ::  shapes and the same .sure.cache: what the sweeps found the members to
  ::  read first thing is kept, so that a member compiled before a callee
  ::  in the SCC and one compiled after it take the same of it.
  ::
  =/  final
    |=  [map-local=(map bell straight) cache=comp-cache]
    ^-  [(map bell straight) comp-cache]
    =;  [m=(map bell straight) c=comp-cache]
      [m c(nary (~(uni by nary.c) m))]
    %+  roll  ~(tap in scc)
    |=  [b=bell m=_map-local c=_cache]
    =/  r  (member b %done m ~ c)
    [+<.r +>.r]
  ?:  done  (final map-local cache)
  ::  Fixed point, with the schedule of the call graph analysis: sweeps over
  ::  the members in DFS postorder (callees before their callers, but for the
  ::  back edges), so that a shape reaches its callers in the same sweep
  ::  instead of one call per round.  A member is compiled again only when a
  ::  callee in the SCC changed its shape at or after the member's last
  ::  compile ("at": a self-call read the shape from before the compile).  The
  ::  loop ends with a sweep that finds nothing to do.
  ::
  ::  What a member reads first thing (+sure-of) is found by the same
  ::  sweeps, and a change of it is a change for the callers: whether a
  ::  call tries decides, at a fork, whether the product goes into one
  ::  register (+lazy-soft-ok:comp), which the shape shows.  A shape only
  ::  loses parts from sweep to sweep, and so does what is read first
  ::  thing: a member keeps of it what its compiles agree on.
  ::
  =/  order=(list bell)
    =|  [vis=(set bell) out=(list bell)]
    =|  stk=(list [b=bell kids=(list bell)])
    =/  roots=(list bell)  ~(tap in scc)
    |-  ^+  out
    ?~  stk
      ?~  roots  (flop out)
      ?:  (~(has in vis) i.roots)  $(roots t.roots)
      %=  $
        roots  t.roots
        vis    (~(put in vis) i.roots)
        stk    [[i.roots ~(tap in (~(get ju kids) i.roots))] ~]
      ==
    ?~  kids.i.stk
      $(stk t.stk, out [b.i.stk out])
    =/  k=bell  i.kids.i.stk
    =/  stk1=(list [b=bell kids=(list bell)])  [[b.i.stk t.kids.i.stk] t.stk]
    ?:  (~(has in vis) k)  $(stk stk1)
    %=  $
      vis  (~(put in vis) k)
      stk  [[k ~(tap in (~(get ju kids) k))] stk1]
    ==
  ::  A callee in the SCC that has no shape yet is not taken to read
  ::  nothing, as it once was: a member compiled before its callee then took
  ::  what its other branch read for conditional and the noun above it
  ::  whole, its callers kept that noun whole for it, and a loop that
  ::  changed one field of the noun consed it back every turn: the first
  ::  guess held itself up.  Such a callee is taken to read on every path
  ::  what it may read on any (.top): one sweep before the loop unites, for
  ::  each member, the needs of both branches of its forks (+laze-may), with
  ::  those of the callees the sweep has been to.  The loop then makes whole
  ::  what a member reads on some paths only, as before.
  ::
  ::  A part that is taken to be read and is not there costs a try and the
  ::  subject version of the callee (\$soft-call), not a crash.
  ::
  ::  .tick counts member compiles; .ran is the tick of a member's last
  ::  compile, .chg the tick of its last shape change
  ::
  ::  Two sweeps.  The first has nothing for a callee across a back edge;
  ::  the second reads every callee from what the first found, so a member
  ::  gets what one more turn of its cycle reads.  A third would add what
  ::  only a third turn reads: the next level of a noun that the cycle
  ::  walks, and a walk has no last level.
  ::
  =^  top=(map bell need-ordered)  cache
    !@  dedicated-shape-pass  [~ cache]
    =/  sweep
      |=  [top=(map bell need-ordered) cache=comp-cache]
      ^-  [(map bell need-ordered) comp-cache]
      %+  roll  order
      |=  [b=bell top=_top c=_cache]
      =/  r  (member b %may ~ top c)
      =/  new=need-ordered  need:(~(got by +<.r) b)
      :_  +>.r
      %+  ~(put by top)  b
      ?~  old=(~(get by top) b)  new
      (uni-need-ord u.old new)
    ::
    =^  one=(map bell need-ordered)  cache  (sweep ~ cache)
    (sweep one cache)
  ::
  =/  st=[any=? tick=@ud ran=(map bell @ud) chg=(map bell @ud)]  [| 0 ~ ~]
  =/  counter=@ud  0
  |-  ^+  [map-local cache]
  =*  sweep-loop  $
  =/  res
    %+  roll  order
    |=  [b=bell st=_st m=_map-local c=_cache]
    =/  dirty=?
      ?~  r=(~(get by ran.st) b)  &
      %-  ~(any in (~(get ju kids) b))
      |=(k=bell (gte (~(gut by chg.st) k 0) u.r))
    ?.  dirty  [st m c]
    =/  t=@ud  +(tick.st)
    =/  r  (member b %must m top c)
    :_  [+<.r +>.r]
    :^  &  t
      (~(put by ran.st) b t)
    ?:(-.r (~(put by chg.st) b t) chg.st)
  ?.  any.st.res  (final map-local cache)
  %-  (print-comp 0 |.(leaf+"[fixpoint-compilation {(scow %ud counter)}]"))
  %=  sweep-loop
    st         st.res(any |)
    map-local  m.res
    cache      c.res
    counter    +(counter)
  ==
::  Baking of a shape: the leaves of a need inside what the bell knows of
::  the subject are not arguments but immediates: the need without them,
::  and the registers to load with their values, in the prologue.  A known
::  part is baked whole only when it has the structure the need asks of
::  it; where it does not, the caller's fetch crashes, as it should.
::
++  bake-need
  ~%  %bake-need  ..ride  ~
  |=  [ned=need know=sock]
  ^-  baked
  =|  imm=(list [r=@uvre v=*])
  ::  .k: what the bell knows of the part of the subject .ned is the need
  ::  of, taken down with the walk (+pull:so composes): pulling it from
  ::  the root at each node was most of a hoon-parser compile
  ::
  =/  k=sock  know
  |-  ^-  [need _imm]
  =*  loop  $
  ?:  ?&  ?=(^ k)
          (all:ca cape.k)
          (need-fits ned data.k)
      ==
    :-  [%none ~]
    =/  j=sock  k
    |-  ^+  imm
    =*  all  $
    ?-  -.ned
        %lax   ~|(%lax-in-a-shape !!)
        %none  imm
        %this  [[r.ned data:(known-sock j)] imm]
        ^      all(ned q.ned, j (tel:so j), imm all(ned p.ned, j (hed:so j)))
        %both
      =.  imm  [[r.ned data:(known-sock j)] imm]
      all(ned t.ned, j (tel:so j), imm all(ned h.ned, j (hed:so j)))
    ==
  ?-    -.ned
      %lax   ~|(%lax-in-a-shape !!)
      %none  [ned imm]
      %this  [ned imm]
      ^
    =^  l  imm  loop(ned p.ned, k (hed:so k))
    =^  r  imm  loop(ned q.ned, k (tel:so k))
    [(cons-need l r) imm]
  ::
      %both
    =^  h  imm  loop(ned h.ned, k (hed:so k))
    =^  t  imm  loop(ned t.ned, k (tel:so k))
    =/  x  (cons-need h t)
    ?^  -.x  [[%both r.ned x] imm]
    [[%this r.ned] imm]
  ==
::  does a known noun have the structure a need or a shape asks of it?
::
++  need-fits
  |=  [ned=$@(~ *) som=*]
  ^-  ?
  ?.  ?=([?(%none %this %both) *] ned)
    ?@  som  |
    ?>  ?=(^ ned)
    &($(ned -.ned, som -.som) $(ned +.ned, som +.som))
  ?.  ?=(%both -.ned)  &
  ?@  som  |
  ?>  ?=([%both * *] ned)
  =/  rest  +.ned
  ::  a need carries a register before the halves, a shape doesn't
  ::
  =/  halves  ?@(-.rest +.rest rest)
  ?>  ?=(^ halves)
  &($(ned -.halves, som -.som) $(ned +.halves, som +.som))
::  a known part of a sock
::
++  known-sock
  |=  k=sock
  ^-  [cape=cape data=*]
  ?>  ?=(^ k)
  k
::  +bake-need for a shape
::
++  bake-need-ord
  ~%  %bake-need-ord  ..ride  ~
  |=  [ned=need-ordered know=sock]
  ^-  need-ordered
  =/  k=sock  know
  |-  ^-  need-ordered
  ?:  &(?=(^ k) (all:ca cape.k) (need-fits ned data.k))  [%none ~]
  ?-    -.ned
      %lax   ~|(%lax-in-a-shape !!)
      %none  ned
      %this  ned
      ^      (cons-need $(ned p.ned, k (hed:so k)) $(ned q.ned, k (tel:so k)))
      %both
    =/  x  (cons-need $(ned h.ned, k (hed:so k)) $(ned t.ned, k (tel:so k)))
    ?^  -.x  [%both x]
    [%this ~]
  ==
::
++  need-normalize
  ~%  %need-normalize  ..ride  ~
  |=  ned=need
  ^-  need
  =*  this  .
  ?-    -.ned
      %lax   ~|(%lax-in-a-shape !!)
      %none  ned
      %this  ned
  ::
      ^
    =/  l  (this -.ned)
    =/  r  (this +.ned)
    (cons-need l r)
  ::
      %both
    =/  l  (this h.ned)
    =/  r  (this t.ned)
    =/  x  (cons-need l r)
    ?^  -.x  [%both r.ned x]
    [%this r.ned]
  ==
::
++  comp
  |=  $:  scc=(set bell)
          long-ska=_[=_code =_jets =_calls =_held]:*long-ska
          jets-hot=jets-comp
          map-local=(map bell straight)
          top=(map bell need-ordered)
          b=bell
      ==
  |_  gen=line-short
  ++  run
    ~%  %comp-run  ..ride  ~
    |=  [mono=? =nomm =goal region=(list @uxid) sup=(unit nomm)]
    |^  ^-  [next _gen]
    ?:  &(?=(%done -.goal) !(rets-plain mine) !(done-through mono nomm))
      done-sum
    ?-    nomm
        [^ *]
      =>  =*  dot  .
          ?.  ?=(%done -.goal)  dot
          =^  nex  gen  done-next
          dot(goal nex)
      ::
      ?-    -.goal
          %pick
        ::  Autocons product is used as a conditional: it will crash and we
        ::  don't care about the particular values of the consed formulas,
        ::  though we still need to compile them for crash correctness
        ::
        =^  o  gen  (emit ~ ~ [%bom ~])
        =^  nex-2  gen  $(nomm +.nomm, goal [%next *need-lazy ~ o])
        =^  nex-2  gen  (past nex-2 -.nomm region)
        =^  nex-1  gen  $(nomm -.nomm, goal [%next *need-lazy then.nex-2])
        ::  Here and later +copy is used to combine together two needs for one
        ::  subject
        ::
        (copy nex-1 laz.nex-2)
      ::
          %next
        =^  [hed=need-lazy tel=need-lazy o=@uwoo]  gen  (split goal)
        ::  the tail runs before the code that follows: what that code
        ::  takes apart of the head's product is taken apart past the tail
        ::  (+past)
        ::
        =^  nex-h=next  gen  (past [%next hed ~ o] +.nomm region)
        =^  nex-2  gen  $(nomm +.nomm, goal [%next tel then.nex-h])
        =^  nex-2  gen  (past nex-2 -.nomm region)
        =^  nex-1  gen  $(nomm -.nomm, goal [%next laz.nex-h then.nex-2])
        (copy nex-1 laz.nex-2)
      ==
    ::
        [%0 *]
      ?:  =(0 p.nomm)  (bomb ?:(?=(%next -.goal) `there.then.goal ~))
      =^  nex  gen  simple-next
      ?:  =(1 p.nomm)  [nex gen]
      [[%next (from p.nomm laz.nex) then.nex] gen]
    ::
        [%1 *]
      ?-    -.goal
          %done
        ?:  =(~ mine)
          =^  r  gen  re
          =^  o  gen  (emit ~ ~[imm+[p.nomm r]] don+r)
          [[%next *need-lazy ~ o] gen]
        =^  nex  gen  done-next
        =^  o  gen  (mede then.nex p.nomm laz.nex)
        [[%next *need-lazy ~ o] gen]
      ::
          %pick
        ?+  p.nomm  (bomb ~)
          %0  [[%next *need-lazy z.goal] gen]
          %1  [[%next *need-lazy o.goal] gen]
        ==
      ::
          %next
        =^  o  gen  (mede then.goal p.nomm laz.goal)
        [[%next *need-lazy ~ o] gen]
      ==
    ::
        [%2 *]
      ?~  info.nomm
        ::  indirect call
        ::
        =^  nex  gen  simple-next
        ::  Here and later +kerf and friends are used to collapse a need for
        ::  a noun into a single registers, i.e. to emit deconsing code that
        ::  splits the product of whatever computation (here it's indirect %2)
        ::  into the registers for a following computation.
        ::
        ::  Indirect %2 is never TCO'd
        ::
        =^  [out=@uwoo pro=@uvre]  gen  (kerf nex)
        =^  r-sub  gen  re
        =^  r-fol  gen  re
        =^  o      gen  (emit ~ [%nok r-sub r-fol pro]~ %hop ~ out)
        ::
        =^  nex-fol  gen
          $(nomm q.nomm, goal [%next (lazy-from-need this+r-fol) ~ o])
        ::
        =^  nex-fol  gen  (past nex-fol p.nomm region)
        =^  nex-sub  gen
          $(nomm p.nomm, goal [%next (lazy-from-need this+r-sub) then.nex-fol])
        ::
        (copy nex-sub laz.nex-fol)
      =*  b-callee  b.u.info.nomm
      =*  key       k.u.info.nomm
      =/  callee-pure=?  pure:(~(got by code.long-ska) b-callee)
      ?:  &(callee-pure ?=(%next -.goal) (none-equivalent laz.goal))
        ::  The product is not used and the function is pure: drop
        ::
        =^  nex-fol=next  gen
          ?:  (safe-fol-fol q.nomm)  [[%next *need-lazy then.goal] gen]
          $(nomm q.nomm, goal [%next *need-lazy then.goal])
        ::
        =^  nex-fol  gen  (past nex-fol p.nomm region)
        =^  nex-sub  gen  $(nomm p.nomm, goal [%next *need-lazy then.nex-fol])
        (copy nex-sub laz.nex-fol)
      =*  call-cole  call.cole.jets.long-ska
      =/  rin=(unit ring)  (~(get by call-cole) b-callee)
      ::  register-less need of the callee: jet or SCC-local best guess or recur
      ::  if calling persistently memoized function: call with the entire
      ::  subject
      ::
      =^  b-ned=need-ordered  gen
        ::  persistent memoization: always %csm
        ::
        ?:  ?=([~ ^] key)  [this+~ gen]
        (callee-need b-callee)
      ::  allocate registers
      ::
      =^  sub-ned=need  gen  (need-ord-alloc-regs b-ned)
      =/  sub-v=(list @uvre)  (flatten-need sub-ned)
      ::  a noun might be taken apart for the callee: its need is bound at
      ::  the call if a part is not read first thing, or if a hint or a call
      ::  runs between the argument and the call ($soft-call).  A jet is
      ::  taken to read nothing first: a core that lacks an argument goes
      ::  whole to its driver, which bails or punts in its own way
      ::
      =/  b-sur=need-ordered
        ?^  (biff rin ~(get by jets-hot))  [%none ~]
        (callee-sure b-callee)
      ::
      =/  sof=?
        ?&  ?=(~ key)
            !(sound (made p.nomm sup) b-ned)
            ?|  (need-soft b-ned b-sur less.b-callee)
                (hinted p.nomm code.long-ska)
                (hinted q.nomm code.long-ska)
            ==
        ==
      ::  the shape the callee returns its product in
      ::
      =/  ret=rets  (callee-rets b-callee key)
      =^  call-blocks=$@(@uwoo [opt=@uwoo pes=[sub=@uvre o=@uwoo]])  gen
        =/  call-op
          |=  [pes=(unit @uvre) pro=@uvre]
          ^-  pole
          ?^  key
            ?~  pes
              ?@  u.key  [%cam b-callee sub-v pro u.key]
              [%csm b-callee -.sub-v pro u.key]
            [%csm b-callee u.pes pro u.key]
          ?~  rin
            ?~  pes  [%cal b-callee sub-v pro]
            [%csl b-callee u.pes pro]
          ?~  pes  [%caf b-callee sub-v pro u.rin]
          [%csf b-callee u.pes pro u.rin]
        ::
        =/  jump-op
          |=  pes=(unit @uvre)
          ^-  termin
          ?~  rin
            ?~  pes  [%jmp b-callee sub-v]
            [%jsp b-callee u.pes]
          ?~  pes  [%jmf b-callee sub-v u.rin]
          [%jsf b-callee u.pes u.rin]
        ::  the parts of the product after the first, into their registers
        ::
        =/  rtls
          |=  regs=(list @uvre)
          ^-  (list pole)
          =/  i=@ud  1
          |-  ^-  (list pole)
          ?~  regs  ~
          [[%rtl i i.regs] $(regs t.regs, i +(i))]
        ::  Memoized calls are never TCO'd, nor is a call whose product comes
        ::  in other parts than this function's
        ::
        ?:  &(?=(~ key) ?=(%done -.goal) =(ret mine))
          ?.  mono
            =^  o  gen  (emit ~ ~ (jump-op ~))
            =?  gen  sof
              (soft-new o %tail b-callee rin sub-ned b-sur ~ ret *@uwoo ~)
            [o gen]
          =^  sub-pes  gen  re
          =^  opt  gen  (emit ~ ~ (jump-op ~))
          =^  pes  gen  (emit ~ ~ (jump-op `sub-pes))
          [[opt sub-pes pes] gen]
        =^  nex  gen  simple-next
        ?.  mono
          =^  [regs=(list @uvre) out=@uwoo]  gen  (spread nex ret)
          ?>  ?=(^ regs)
          =^  o  gen
            (emit ~ [(call-op ~ i.regs) (rtls t.regs)] %hop ~ out)
          ::
          =?  gen  sof
            (soft-new o %call b-callee rin sub-ned b-sur regs ret out ~)
          [o gen]
        =^  [out=@uwoo pro=@uvre]  gen  (kerf nex)
        =^  merged   gen  re
        =^  sub-pes  gen  re
        =^  merge    gen  (emit ~[merged] [%mov merged pro]~ %hop ~ out)
        =^  pro-pes  gen  re
        ::  a function of its whole subject takes the product whole
        ::
        =^  regs=(list @uvre)  gen  (rets-regs ret)
        ?>  ?=(^ regs)
        =^  y  gen  oo
        =^  [ob=@uwoo pro-opt=@uvre]  gen  (whole-of ret regs y)
        =.  gen  (emir y ~ ~ %hop ~[`pro-opt] merge)
        =^  opt      gen
          (emit ~ [(call-op ~ i.regs) (rtls t.regs)] %hop ~ ob)
        ::
        =^  pes      gen
          (emit ~ ~[(call-op `sub-pes pro-pes)] %hop ~[`pro-pes] merge)
        ::
        [[opt sub-pes pes] gen]
      ::  call-blocks end definition
      ::
      =^  [sub-ned=need call-block=@uwoo]  gen
        ?@  call-blocks  [[sub-ned call-blocks] gen]
        =^  o=@uwoo  gen  (mono-try-call sub-ned call-blocks)
        [[this+sub.pes.call-blocks o] gen]
      ::
      ::  the need of the callee: bound at a block of the call when a noun
      ::  might be taken apart for it ($soft-call)
      ::
      =^  nex-arg=next  gen
        =/  nex-arg=next  [%next (lazy-from-need sub-ned) ~ call-block]
        ?.  (~(has by soft.gen) call-block)  [nex-arg gen]
        (soft-bond nex-arg region)
      ::
      =^  nex-fol=next  gen
        ?:  (safe-fol-fol q.nomm)  [[%next *need-lazy then.nex-arg] gen]
        $(nomm q.nomm, goal [%next *need-lazy then.nex-arg])
      ::
      =^  nex-fol  gen  (past nex-fol p.nomm region)
      =^  nex-sub  gen
        $(nomm p.nomm, goal [%next laz.nex-arg then.nex-fol])
      ::
      (copy nex-sub laz.nex-fol)
    ::
        [%3 *]
      ?:  &(?=(%next -.goal) (none-equivalent laz.goal))
        ::  Don't care about the product
        ::
        $(nomm p.nomm)
      =>  =*  dot  .
          ?-    -.goal
              %pick  dot
          ::
              %done
            ?>  =(~ mine)
            =^  r-0  gen  re
            =^  r-1  gen  re
            =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
            =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
            dot(goal `$>(%pick ^goal)`[%pick ~^o-0 ~^o-1])
          ::
              %next
            =^  a=(unit [r=@uvre o=@uwoo])  gen  (collapse-lazy-atom goal)
            ?~  a  !!
            =^  [z=@uwoo o=@uwoo]  gen  (forl r.u.a o.u.a)
            dot(goal `$>(%pick ^goal)`[%pick ~^z ~^o])
          ==
      ::
      =^  r  gen  re
      =?  tst.gen  rets-sums  (~(put in tst.gen) r)
      =^  o  gen  (emit ~ ~ clq+[r [z o]:goal])
      $(nomm p.nomm, goal [%next (lazy-from-need this+r) ~ o])
    ::
        [%4 *]
      ?-    -.goal
          %done
        ?>  =(~ mine)
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o    gen  (emit ~ [%inc arg pro]~ %don pro)
        $(nomm p.nomm, goal [%next (lazy-from-reg arg) ~ o])
      ::
          %pick
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o    gen  (emit ~ [%inc arg pro]~ %brn pro [z o]:goal)
        $(nomm p.nomm, goal [%next (lazy-from-reg arg) ~ o])
      ::
          %next
        =^  a=(unit [r=@uvre o=@uwoo])  gen  (collapse-lazy-atom goal)
        =^  [pro=@uvre then=@uwoo]  gen
          ?^  a  [u.a gen]
          =^  r  gen  re
          ?>  =(~ args.then.goal)
          [[r there.then.goal] gen]
        ::
        =^  arg  gen  re
        =^  o    gen  (emit ~ [%inc arg pro]~ %hop ~ then)
        $(nomm p.nomm, goal [%next (lazy-from-reg arg) ~ o])
      ==
    ::
        [%5 *]
      =^  r-p  gen  re
      =^  r-q  gen  re
      =^  o=@uwoo  gen
        ?-    -.goal
            %pick  (emit ~ ~ eqq+[r-p r-q [z o]:goal])
        ::
            %done
          ?>  =(~ mine)
          =^  r-0  gen  re
          =^  r-1  gen  re
          =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
          =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
          (emit ~ ~ eqq+[r-p r-q ~^o-0 ~^o-1])
        ::
            %next
          =^  a=(unit [r=@uvre o=@uwoo])  gen  (collapse-lazy-atom goal)
          ?~  a
            ::  Compare for the sideeffect only
            ::
            ?>  =(~ args.then.goal)
            (emit ~ [%equ r-p r-q]~ %hop ~ there.then.goal)
          =^  [z=@uwoo o=@uwoo]  gen  (forl r.u.a o.u.a)
          (emit ~ ~ eqq+[r-p r-q ~^z ~^o])
        ==
      ::  a noun compared with an atom is only tested
      ::
      =?  tst.gen  &(rets-sums ?=([%1 @] p.nomm))  (~(put in tst.gen) r-q)
      =?  tst.gen  &(rets-sums ?=([%1 @] q.nomm))  (~(put in tst.gen) r-p)
      =^  nex-q  gen
        $(nomm q.nomm, goal [%next (lazy-from-need this+r-q) ~ o])
      ::
      =^  nex-q  gen  (past nex-q p.nomm region)
      =^  nex-p  gen
        $(nomm p.nomm, goal [%next (lazy-from-need this+r-p) then.nex-q])
      ::
      (copy nex-p laz.nex-q)
    ::
        [%6 *]
      ::  What follows needs of the product lazily, in blocks of its own:
      ::  those blocks read it from one need, which each branch meets with
      ::  what it has (+lerf).  The fork is then compiled for a sure need.
      ::
      ?:  ?&  ?=(%next -.goal)
              !(none-equivalent laz.goal(sure *sure))
          ==
        =^  ler=(unit next)  gen  (lerf goal q.nomm r.nomm mono)
        ?^  ler  $(goal u.ler)
        =^  [out=@uwoo pro=@uvre]  gen  (kerf goal)
        $(goal [%next (lazy-from-need this+pro) ~ out])
      ::  No lazy needs captured, simpler compilation
      ::
      =^  [goal-0=^goal goal-1=^goal]  gen
        ?.  ?=(%next -.goal)  [[goal goal] gen]
        =^  o-0  gen  oo
        =^  o-1  gen  oo
        =^  [sur-0=sure sur-1=sure]  gen
          (fork-sure sure.laz.goal there.then.goal o-0 o-1)
        ::
        :_  gen
        [[%next [sur-0 ~ ~] ~ o-0] [%next [sur-1 ~ ~] ~ o-1]]
      ::
      =^  region-branch=(list @uxid)  gen
        ?.  ?=(%next -.goal-0)  [region gen]
        =^  region-id  gen  id
        [[region-id region] gen]
      ::
      =/  cond-before  cond.gen
      =^  nex-1  gen  $(nomm r.nomm, goal goal-1, region region-branch)
      =/  cond-between  cond.gen
      =^  nex-0  gen  $(nomm q.nomm, goal goal-0, region region-branch)
      =^  [lazy=need-lazy yes=@uwoo nuh=@uwoo]  gen
        ?:  ?=(%next -.goal)
          ?>  ?=(%next -.goal-0)
          ?>  ?=(%next -.goal-1)
          %-  sect
          :*  nex-0  nex-1  there.then.goal-0  there.then.goal-1
              region-branch  cond-before  cond-between
          ==
        =^  yes  gen  (emit ~ ~ %hop then.nex-0)
        =^  nuh  gen  (emit ~ ~ %hop then.nex-1)
        =.  gen  (set-tag yes region)
        =.  gen  (set-tag nuh region)
        :_  gen
        ?>  =(~ args.then.nex-0)
        ?>  =(~ args.then.nex-1)
        :_  [yes nuh]
        [*sure [[yes laz.nex-0] [nuh laz.nex-1]]~ ~]
      ::
      =.  lazy  (past-fork lazy p.nomm)
      =^  nex-cond  gen  $(nomm p.nomm, goal [%pick ~^yes ~^nuh])
      (copy nex-cond lazy)
    ::
        [%7 *]
      =^  nex  gen  $(nomm q.nomm, sup `p.nomm)
      $(nomm p.nomm, goal nex)
    ::
        [%10 *]
      =^  next  gen  simple-next
      =^  [don=need-lazy rec=need-lazy o=@uwoo]  gen  (into next p.p.nomm)
      ::  as the tail of a cons does to the head
      ::
      =^  nex-d  gen  (past [%next don ~ o] q.nomm region)
      =^  nex-rec  gen  $(nomm q.nomm, goal [%next rec then.nex-d])
      =^  nex-rec  gen  (past nex-rec q.p.nomm region)
      =^  nex-don  gen  $(nomm q.p.nomm, goal [%next laz.nex-d then.nex-rec])
      (copy nex-don laz.nex-rec)
    ::
        [%11 *]
      ?@  p.nomm
        ?.  ?=(hint-static p.nomm)  $(nomm q.nomm)
        ::  A hint with an effect bounds the needs both ways, as one that
        ::  keeps a trace frame does: no noun is taken apart before the
        ::  effect for what the plain interpreter reads after it
        ::
        =^  nex    gen  simple-next
        =^  nex=next  gen  (past-if nex q.nomm region)
        =^  epil    gen  (emit ~ ~[hse+[p.nomm body.nomm]] %hop then.nex)
        =^  nex-fol  gen  $(nomm q.nomm, goal nex(then [~ epil]))
        =^  nex-fol=next  gen  (lazy-bound nex-fol region)
        =^  prol    gen  (emit ~ ~[hsp+[p.nomm body.nomm]] %hop then.nex-fol)
        [[%next laz.nex-fol ~ prol] gen]
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  nex-fol  gen  $(nomm q.nomm)
        ?:  (safe-nomm q.p.nomm)  [nex-fol gen]
        =^  nex-fol  gen  (past nex-fol q.p.nomm region)
        =^  nex-toke  gen
          $(nomm q.p.nomm, goal [%next *need-lazy then.nex-fol])
        ::
        (copy nex-toke laz.nex-fol)
      =^  nex      gen  simple-next
      =^  nex=next  gen  (past-if nex q.nomm region)
      =^  toke     gen  re
      =^  epil     gen  (emit ~ ~[hde+[p.p.nomm toke body.nomm]] %hop then.nex)
      =^  nex-fol1  gen  $(nomm q.nomm, goal nex(then [~ epil]))
      =^  nex-fol2=next  gen  (lazy-bound nex-fol1 region)
      =^  prol  gen
        (emit ~ ~[hdp+[p.p.nomm toke body.nomm]] %hop then.nex-fol2)
      ::
      =^  nex-toke  gen
        $(nomm q.p.nomm, goal [%next (lazy-from-reg toke) ~ prol])
      ::
      (copy nex-toke laz.nex-fol2)
    ::
        [%mean *]
      ::  A known product of a pure arm is pushed as a constant: no call
      ::
      =/  konst=(unit *)  (mean-konst b.nomm k.nomm)
      ::  The subject will already be a single noun and we don't bother with
      ::  mono version of the mean bell: just push the trap as is
      ::
      ?:  &(mono ?=(~ konst))  $(nomm [%11 [%mean p.nomm] q.nomm body.nomm])
      ::  The trap's function will be pushed on the stack w/ its arguments
      ::
      =^  b-ned=need-ordered  gen
        ?^  konst  [[%none ~] gen]
        (callee-need b.nomm)
      ::
      =^  sub-ned=need  gen  (need-ord-alloc-regs b-ned)
      =/  sub-v=(list @uvre)  (flatten-need sub-ned)
      =/  [prol-op=pole epil-op=pole]
        ?^  konst  [[%hcp u.konst body.nomm] [%hce u.konst body.nomm]]
        [[%hmp b.nomm sub-v body.nomm] [%hme b.nomm sub-v body.nomm]]
      ::
      =^  nex   gen  simple-next
      =^  nex=next  gen  (past-if nex q.nomm region)
      =^  epil  gen  (emit ~ ~[epil-op] %hop then.nex)
      =^  nex-fol1  gen  $(nomm q.nomm, goal nex(then [~ epil]))
      =^  nex-fol2=next  gen  (lazy-bound nex-fol1 region)
      =^  prol  gen  (emit ~ ~[prol-op] %hop then.nex-fol2)
      ::  The arm reads its parts only if the trace is rendered: none is
      ::  fetched here with a crash ($soft-call)
      ::
      =^  nex-arg=next  gen
        =/  nex-arg=next  [%next (lazy-from-need sub-ned) ~ prol]
        ?:  (sound p.nomm b-ned)  [nex-arg gen]
        =.  gen
          %:  soft-new
            prol  %mean  b.nomm  ~  sub-ned  [%none ~]  ~  ~
            there.then.nex-fol2  [epil body.nomm]
          ==
        (soft-bond nex-arg region)
      ::
      =^  nex-trap  gen  $(nomm p.nomm, goal nex-arg)
      (copy nex-trap laz.nex-fol2)
    ::
        [%12 *]
      =^  nex  gen  simple-next
      =^  [out=@uwoo pro=@uvre]  gen  (kerf nex)
      =^  r-path     gen  re
      =^  r-ref      gen  re
      =^  o-spy      gen  (emit ~ [%spy r-ref r-path pro]~ %hop ~ out)
      =^  nex-path  gen
        $(nomm q.nomm, goal [%next (lazy-from-reg r-path) ~ o-spy])
      ::
      =^  nex-path  gen  (past nex-path p.nomm region)
      =^  nex-ref   gen
        $(nomm p.nomm, goal [%next (lazy-from-reg r-ref) then.nex-path])
      ::
      (copy nex-ref laz.nex-path)
    ==
    ::
    ++  simple-next
      ^-  [next _gen]
      ?-    -.goal
          %next  [goal gen]
          %done  done-next
      ::
          %pick
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ [%brn r [z o]:goal])
        [[%next [[this+r ~] ~ ~] ~ o] gen]
      ==
    ::  the shape this function returns its product in
    ::
    ++  mine  (rets-mine mono)
    ::  The goal of a product that is returned: in one register, or in parts
    ::
    ++  done-next
      ^-  [next _gen]
      =/  ret=rets  mine
      ?~  ret
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ [%don r])
        [[%next [[this+r ~] ~ ~] ~ o] gen]
      =^  ned=need  gen  (rets-need ret)
      =/  v=(list @uvre)  (flatten-need ned)
      ?>  ?=(^ v)
      =^  o  gen  (emit ~ ~ [%dox v ret])
      [[%next [[ned ~] ~ ~] ~ o] gen]
    ::  A product returned by a shape with sums: its registers are filled
    ::  by the formula, as far as its form shows
    ::
    ++  done-sum
      ^-  [next _gen]
      =/  ret=rets  mine
      =^  v=(list @uvre)  gen  (rets-regs ret)
      ?>  ?=(^ v)
      =^  o  gen  (emit ~ ~ [%dox v ret])
      (fill nomm ret v [~ o])
    ::  Code for .nom, its product into the registers .v by the shape .ret,
    ::  then to .then.  A cons fills the halves, of a sum too, under any
    ::  cell as the tag; a constant atom is the tag of its sum; any other
    ::  formula is asked for the pairs of the shape and its sums whole,
    ::  which are told apart when it is done (+unpack)
    ::
    ++  fill
      |=  [nom=^nomm ret=rets v=(list @uvre) then=jmp]
      ^-  [next _gen]
      ?~  ret
        ?>  ?=(^ v)
        ^$(nomm nom, goal [%next (lazy-from-reg i.v) then])
      ?:  ?=(%k -.ret)
        ^$(nomm nom, goal [%next *need-lazy then])
      ?:  ?=([%7 *] nom)
        =^  nex  gen  $(nom q.nom)
        ^$(nomm p.nom, goal nex)
      =/  [vp=(list @uvre) vq=(list @uvre)]
        =/  w=(list @uvre)  ?:(?=(%m -.ret) (slag 1 v) v)
        =/  n=@ud  (rets-size p.ret)
        [(scag n w) (slag n w)]
      ::  the tag of a pair: any cell
      ::
      =/  tag
        |=  then=jmp
        ^-  [jmp _gen]
        ?.  ?=(%m -.ret)  [then gen]
        ?>  ?=(^ v)
        =^  o  gen  (emit ~ [%imm [0 0] i.v]~ %hop then)
        [[~ o] gen]
      ::
      ?:  ?=([^ *] nom)
        =^  then  gen  (tag then)
        =^  nex-2  gen  $(nom +.nom, ret q.ret, v vq, then then)
        =^  nex-1  gen  $(nom -.nom, ret p.ret, v vp, then then.nex-2)
        (copy nex-1 laz.nex-2)
      ?:  ?=([%1 *] nom)
        ?@  p.nom
          ?:  ?=(%c -.ret)  (bomb ~)
          ?>  ?=(^ v)
          =^  o  gen
            %^  emit  ~
              [[%imm p.nom i.v] (turn t.v |=(x=@uvre `pole`[%imm 0 x]))]
            [%hop then]
          [[%next *need-lazy ~ o] gen]
        =^  then  gen  (tag then)
        =^  nex-2  gen  $(nom [%1 +.p.nom], ret q.ret, v vq, then then)
        $(nom [%1 -.p.nom], ret p.ret, v vp, then then.nex-2)
      =^  [ned=need o=@uwoo]  gen  (unpack ret v then)
      ^$(nomm nom, goal [%next (lazy-from-need ned) ~ o])
    --
  ::
  ++  rets-mine
    |=  mono=?
    ^-  rets
    ?:(mono ~ mine.gen)
  ::  A memoized call produces one noun
  ::
  ++  callee-rets
    |=  [b-callee=bell key=(unit *)]
    ^-  rets
    ?^  key  ~
    ~|  %rets-missing-callee
    (~(got by rets.cache.gen) b-callee)
  ++  rets-plain
    |=  ret=rets
    ^-  ?
    ?~  ret  &
    ?-  -.ret
      %k  &
      %m  |
      %c  &($(ret p.ret) $(ret q.ret))
    ==
  ::  registers for the parts of a product of a plain shape, as a need
  ::
  ++  rets-need
    |=  ret=rets
    ^-  [need _gen]
    ?~  ret  =^(r gen re [this+r gen])
    ?-    -.ret
        %k  [[%none ~] gen]
        %m  !!
        %c
      =^  h  gen  $(ret p.ret)
      =^  t  gen  $(ret q.ret)
      ?:  &(?=(%none -.h) ?=(%none -.t))  [[%none ~] gen]
      [[h t] gen]
    ==
  ::
  ++  rets-ord
    |=  ret=rets
    ^-  need-ordered
    ?~  ret  [%this ~]
    ?-    -.ret
        %k  [%none ~]
        %m  !!
        %c
      =/  h  $(ret p.ret)
      =/  t  $(ret q.ret)
      ?:  &(?=(%none -.h) ?=(%none -.t))  [%none ~]
      [h t]
    ==
  ::  the need of a noun that +unpack takes apart by the shape .ret: a sum
  ::  is asked for whole
  ::
  ++  unpack-ord
    |=  ret=rets
    ^-  need-ordered
    ?~  ret  [%this ~]
    ?-    -.ret
        %k  [%none ~]
        %m  [%this ~]
        %c
      =/  h  $(ret p.ret)
      =/  t  $(ret q.ret)
      ?:  &(?=(%none -.h) ?=(%none -.t))  [%none ~]
      [h t]
    ==
  ::  fresh registers for a shape, in the order of its registers
  ::
  ++  rets-regs
    |=  ret=rets
    ^-  [(list @uvre) _gen]
    =/  n=@ud  (rets-size ret)
    =|  out=(list @uvre)
    |-  ^-  [(list @uvre) _gen]
    ?:  =(0 n)  [(flop out) gen]
    =^  r  gen  re
    $(n (dec n), out [r out])
  ::  a product returned by the shape of this function without ending here:
  ::  the formula passes the goal on (+run)
  ::
  ++  done-through
    |=  [mono=? =nomm]
    ^-  ?
    ?+    nomm  |
        [%6 *]  &
        [%7 *]  &
    ::
        [%2 *]
      ?~  info.nomm  |
      &(?=(~ k.u.info.nomm) =((callee-rets u.info.nomm) (rets-mine mono)))
    ::
        [%11 *]
      ?@  p.nomm  !?=(hint-static p.nomm)
      !?=(hint-dynamic p.p.nomm)
    ==
  ::  Receive a product in parts: the lazy need of the product, split along
  ::  the shape of the callee, each part collapsed to one register.
  ::  Produces the registers of the parts and the block to go to.
  ::
  ::  A sum arrives as a tag and the halves.  Where the product is only
  ::  tested, the tag stands in for it; where its halves are fetched, the
  ::  tag is checked to be a cell, as the product would be; where it is
  ::  wanted whole, it is consed on the pair side of a branch on the tag
  ::  (+split-need-tag).
  ::
  ++  spread
    |=  [nex=next ret=rets]
    ^-  [[(list @uvre) @uwoo] _gen]
    ?~  ret
      =^  [o=@uwoo r=@uvre]  gen  (kerf nex)
      [[~[r] o] gen]
    ?-    -.ret
        %k
      =^  o=@uwoo  gen  (mede then.nex n.ret laz.nex)
      [[~ o] gen]
    ::
        %c
      =^  [hed=need-lazy tel=need-lazy o=@uwoo]  gen  (split nex)
      =^  [rt=(list @uvre) ot=@uwoo]  gen  $(nex [%next tel ~ o], ret q.ret)
      =^  [rh=(list @uvre) oh=@uwoo]  gen  $(nex [%next hed ~ ot], ret p.ret)
      [[(weld rh rt) oh] gen]
    ::
        %m
      =^  tag  gen  re
      =^  [hed=need-lazy tel=need-lazy o=@uwoo]  gen  (split-tag nex tag)
      =^  [rt=(list @uvre) ot=@uwoo]  gen  $(nex [%next tel ~ o], ret q.ret)
      =^  [rh=(list @uvre) oh=@uwoo]  gen  $(nex [%next hed ~ ot], ret p.ret)
      [[[tag (weld rh rt)] oh] gen]
    ==
  ::  Blocks that cons the parts .v of a product of the shape .ret, then go
  ::  to .then.  Produces the first block and the register of the product
  ::
  ++  whole-of
    |=  [ret=rets v=(list @uvre) then=@uwoo]
    ^-  [[@uwoo @uvre] _gen]
    ?~  ret
      ?>  ?=(^ v)
      [[then i.v] gen]
    ?-    -.ret
        %k
      =^  d  gen  re
      =^  o  gen  (emit ~ [%imm n.ret d]~ %hop ~ then)
      [[o d] gen]
    ::
        %c
      =/  n=@ud  (rets-size p.ret)
      =^  d  gen  re
      =^  x  gen  oo
      =^  [oq=@uwoo dq=@uvre]  gen  $(ret q.ret, v (slag n v), then x)
      =^  [op=@uwoo dp=@uvre]  gen  $(ret p.ret, v (scag n v), then oq)
      =.  gen  (emir x ~ [%con dp dq d]~ %hop ~ then)
      [[op d] gen]
    ::
        %m
      ?>  ?=(^ v)
      =/  n=@ud  (rets-size p.ret)
      =^  d  gen  re
      =^  j  gen  (emit ~[d] ~ %hop ~ then)
      =^  a  gen  (emit ~ ~ %hop ~[`i.v] j)
      =^  dk  gen  re
      =^  x  gen  oo
      =^  [oq=@uwoo dq=@uvre]  gen  $(ret q.ret, v (slag n t.v), then x)
      =^  [op=@uwoo dp=@uvre]  gen  $(ret p.ret, v (scag n t.v), then oq)
      =.  gen  (emir x ~ [%con dp dq dk]~ %hop ~[`dk] j)
      =^  o  gen  (emit ~ ~ [%clq i.v [~ op] [~ a]])
      [[o d] gen]
    ==
  ::  Blocks that take the noun in .r apart into the registers .v by the
  ::  shape .ret, then go to .then.  A sum is told apart here: a cell goes
  ::  to its halves under any cell as the tag, an atom is its own tag
  ::
  ++  conv
    |=  [r=@uvre ret=rets v=(list @uvre) then=@uwoo cold=?]
    ^-  [@uwoo _gen]
    ?~  ret
      ?>  ?=(^ v)
      (emit-as cold ~ [%mov r i.v]~ %hop ~ then)
    ?-    -.ret
        %k  [then gen]
        %c
      =/  n=@ud  (rets-size p.ret)
      =^  h  gen  re
      =^  t  gen  re
      =^  oq  gen  $(r t, ret q.ret, v (slag n v))
      =^  op  gen  $(r h, ret p.ret, v (scag n v), then oq)
      (emit-as cold ~ ~[[%cel r] [%hed r h] [%tal r t]] %hop ~ op)
    ::
        %m
      ?>  ?=(^ v)
      ::  the join takes the registers of the shape as parameters
      ::
      =^  j  gen  (emit-as cold v ~ %hop ~ then)
      =^  z  gen  re
      =^  a  gen
        %:  emit-as  cold  ~  [%imm 0 z]~
          [%hop [`r (turn t.v |=(* `(unit @uvre)``z))] j]
        ==
      ::
      =^  w=(list @uvre)  gen  (rets-regs ret)
      ?>  ?=(^ w)
      =^  e  gen
        %:  emit-as  cold  ~  ~
          [%hop (turn `(list @uvre)`w |=(x=@uvre `(unit @uvre)``x)) j]
        ==
      ::
      =/  n=@ud  (rets-size p.ret)
      =^  h  gen  re
      =^  t  gen  re
      =^  oq  gen  $(r t, ret q.ret, v (slag n t.w), then e)
      =^  op  gen  $(r h, ret p.ret, v (scag n t.w), then oq)
      =^  k  gen
        (emit-as cold ~ ~[[%imm [0 0] i.w] [%hed r h] [%tal r t]] %hop ~ op)
      ::
      (emit-as cold ~ ~ [%clq r [~ k] [~ a]])
    ==
  ::  The need of a noun whose parts go into the registers .v by the shape
  ::  .ret, and the block that takes its sums apart (+conv) and goes to
  ::  .then: the pairs of the shape are asked for by the need
  ::
  ++  unpack
    |=  [ret=rets v=(list @uvre) then=jmp]
    ^-  [[need @uwoo] _gen]
    =^  end=@uwoo  gen  (emit ~ ~ %hop then)
    |-  ^-  [[need @uwoo] _gen]
    ?~  ret
      ?>  ?=(^ v)
      [[this+i.v end] gen]
    ?-    -.ret
        %k  [[[%none ~] end] gen]
        %c
      =/  n=@ud  (rets-size p.ret)
      =^  [nq=need oq=@uwoo]  gen  $(ret q.ret, v (slag n v))
      =^  [np=need op=@uwoo]  gen  $(ret p.ret, v (scag n v), end oq)
      ?:  &(?=(%none -.np) ?=(%none -.nq))  [[[%none ~] op] gen]
      [[[np nq] op] gen]
    ::
        %m
      =^  r  gen  re
      =^  o  gen  (conv r ret v end |)
      [[this+r o] gen]
    ==
  ::  Registers that are read as nouns are not test registers.  A register
  ::  made for a test (Nock 3, Nock 5 with an atom) is in .tst as long as
  ::  nothing but tests, cell checks and moves into such registers reads it:
  ::  a sum received in parts gives such a register its tag (+spread)
  ::
  ++  tst-read
    |=  [ops=(list pole) fin=(unit termin)]
    ^+  gen
    ?:  =(~ tst.gen)  gen
    =/  del
      |=  [rs=(list @uvre) tst=(set @uvre)]
      ^-  (set @uvre)
      ?~  rs  tst
      $(rs t.rs, tst (~(del in tst) i.rs))
    ::
    =.  tst.gen
      %+  roll  ops
      |=  [op=pole tst=_tst.gen]
      ?+  -.op  (del (get-regs op) tst)
        %cel  tst
        %equ  tst
        %mov  ?:((~(has in tst) d.op) tst (~(del in tst) s.op))
      ==
    ?~  fin  gen
    =.  tst.gen
      ?+  -.u.fin  (del (get-regs u.fin) tst.gen)
        %clq  (del (weld (jmp-regs z.u.fin) (jmp-regs o.u.fin)) tst.gen)
        %eqq  (del (weld (jmp-regs z.u.fin) (jmp-regs o.u.fin)) tst.gen)
        %brn  (del (weld (jmp-regs z.u.fin) (jmp-regs o.u.fin)) tst.gen)
        %brz  (del (weld (jmp-regs z.u.fin) (jmp-regs o.u.fin)) tst.gen)
      ==
    gen
  ::
  ++  re  `[@uvre _gen]`[re-gen.gen gen(re-gen +(re-gen.gen))]
  ++  oo  `[@uwoo _gen]`[bo-gen.gen gen(bo-gen +(bo-gen.gen))]
  ++  id  `[@uxid _gen]`[id-gen.gen gen(id-gen +(id-gen.gen))]
  ::  Nothing is emitted in %drop mode, see $line-short
  ::
  ++  dropping  ?=(%drop mode.gen)
  ::
  ++  set-tag
    |=  [o=@uwoo region=(list @uxid)]
    ^+  gen
    ?:  dropping  gen
    gen(tags (~(put by tags.gen) o region))
  ::  The kids of a lazy block are in its region
  ::
  ++  copy-tag
    |=  [from=@uwoo to=(list @uwoo)]
    ^+  gen
    ?:  dropping  gen
    =/  region  (~(got by tags.gen) from)
    gen(tags (~(gas by tags.gen) (turn to |=(o=@uwoo [o region]))))
  ::
  ::  Shape-only compilation: the traversal of +run reduced to what decides
  ::  the lazy need of the subject.  No code, no registers, no blocks.
  ::
  ++  run-shape
    ~%  %comp-run-shape  ..ride  ~
    |=  [=nomm goal=goal-shape sup=(unit nomm)]
    ^-  [laze _gen]
    =/  none=laze  *laze
    =/  this=laze  [[this+~ ~] ~ ~]
    ::  what +simple-next does to the goal
    ::
    ::  what +fill does to a product returned by a shape with sums
    ::
    =/  fill
      |=  [nom=^nomm ret=rets]
      ^-  [laze _gen]
      ?~  ret  ^$(nomm nom, goal [%next this])
      ?:  ?=(%k -.ret)  ^$(nomm nom, goal [%next none])
      ?:  ?=([%7 *] nom)
        =^  l  gen  $(nom q.nom)
        ^$(nomm p.nom, goal [%next l])
      ?:  ?=([^ *] nom)
        =^  l-2  gen  $(nom +.nom, ret q.ret)
        =^  l-1  gen  $(nom -.nom, ret p.ret)
        [(laze-copy l-1 l-2) gen]
      ?:  ?=([%1 *] nom)  [none gen]
      ^$(nomm nom, goal [%next [[(unpack-ord ret) ~] ~ ~]])
    ::
    ?:  ?&  ?=(%done -.goal)
            !(rets-plain (rets-mine |))
            !(done-through | nomm)
        ==
      (fill nomm (rets-mine |))
    =/  done=laze
      ?.  (rets-plain (rets-mine |))  this
      [[(rets-ord (rets-mine |)) ~] ~ ~]
    =/  simple=$>(%next goal-shape)
      ?-  -.goal
        %next  goal
        %done  [%next done]
        %pick  [%next this]
      ==
    ?-    nomm
        [^ *]
      ?-    -.goal
          %done  $(goal [%next done])
      ::
          %pick
        =^  l-2  gen  $(nomm +.nomm, goal [%next none])
        =^  l-2  gen  (laze-past l-2 -.nomm)
        =^  l-1  gen  $(nomm -.nomm, goal [%next none])
        [(laze-copy l-1 l-2) gen]
      ::
          %next
        =/  [hed=laze tel=laze]  (laze-split laz.goal)
        =^  hed  gen  (laze-past hed +.nomm)
        =^  l-2  gen  $(nomm +.nomm, goal [%next tel])
        =^  l-2  gen  (laze-past l-2 -.nomm)
        =^  l-1  gen  $(nomm -.nomm, goal [%next hed])
        [(laze-copy l-1 l-2) gen]
      ==
    ::
        [%0 *]
      ?:  =(0 p.nomm)  [none gen]
      ?:  =(1 p.nomm)  [laz.simple gen]
      [(laze-from p.nomm laz.simple) gen]
    ::
        [%1 *]  [none gen]
    ::
        [%2 *]
      ?~  info.nomm
        =^  l-fol  gen  $(nomm q.nomm, goal [%next this])
        =^  l-fol  gen  (laze-past l-fol p.nomm)
        =^  l-sub  gen  $(nomm p.nomm, goal [%next this])
        [(laze-copy l-sub l-fol) gen]
      =*  b-callee  b.u.info.nomm
      =/  callee-pure=?  pure:(~(got by code.long-ska) b-callee)
      =/  drop=?
        &(callee-pure ?=(%next -.goal) (laze-none-equivalent laz.goal))
      ::
      =^  l-fol=laze  gen
        ?:  (safe-fol-fol q.nomm)  [none gen]
        $(nomm q.nomm, goal [%next none])
      ::
      =^  l-fol  gen  (laze-past l-fol p.nomm)
      =^  l-sub  gen
        ?:  drop  $(nomm p.nomm, goal [%next none])
        =^  ned=need-ordered  gen
          ?:  ?=([~ ^] k.u.info.nomm)  [this+~ gen]
          (callee-need b-callee)
        ::  as +run does ($soft-call)
        ::
        =/  sur=need-ordered
          =/  rin=(unit ring)  (~(get by call.cole.jets.long-ska) b-callee)
          ?^  (biff rin ~(get by jets-hot))  [%none ~]
          (callee-sure b-callee)
        ::
        ?.  ?&  ?=(~ k.u.info.nomm)
                !(sound (made p.nomm sup) ned)
                ?|  (need-soft ned sur less.b-callee)
                    (hinted p.nomm code.long-ska)
                    (hinted q.nomm code.long-ska)
                ==
            ==
          $(nomm p.nomm, goal [%next [[ned ~] ~ ~]])
        =^  i  gen  id
        =.  sofs.gen  (~(put in sofs.gen) i)
        $(nomm p.nomm, goal [%next [*sure-ordered ~ [i [[ned ~] ~ ~]]~]])
      ::
      [(laze-copy l-sub l-fol) gen]
    ::
        [%3 *]
      ?:  &(?=(%next -.goal) (laze-none-equivalent laz.goal))  $(nomm p.nomm)
      $(nomm p.nomm, goal [%next this])
    ::
        [%4 *]  $(nomm p.nomm, goal [%next this])
    ::
        [%5 *]
      =^  l-q  gen  $(nomm q.nomm, goal [%next this])
      =^  l-q  gen  (laze-past l-q p.nomm)
      =^  l-p  gen  $(nomm p.nomm, goal [%next this])
      [(laze-copy l-p l-q) gen]
    ::
        [%6 *]
      ::  as +run does (+lerf)
      ::
      ?:  ?&  ?=(%next -.goal)
              !(laze-none-equivalent laz.goal(sure *sure-ordered))
          ==
        ?^  ler=(laze-lerf laz.goal q.nomm r.nomm)
          $(goal [%next u.ler])
        $(goal [%next this])
      =/  goal-branch=goal-shape
        ?.  ?=(%next -.goal)  goal
        [%next [sure.laz.goal ~ ~]]
      =^  l-1  gen  $(nomm r.nomm, goal goal-branch)
      =^  l-0  gen  $(nomm q.nomm, goal goal-branch)
      =^  lazy  gen  (laze-sect l-0 l-1)
      =.  lazy  (laze-past-fork lazy p.nomm)
      =^  l-cond  gen  $(nomm p.nomm, goal [%pick ~])
      [(laze-copy l-cond lazy) gen]
    ::
        [%7 *]
      =^  l  gen  $(nomm q.nomm, sup `p.nomm)
      $(nomm p.nomm, goal [%next l])
    ::
        [%10 *]
      ?>  ?=(%next -.simple)
      =/  [don=laze rec=laze]  (laze-into p.p.nomm laz.simple)
      =^  don  gen  (laze-past don q.nomm)
      =^  l-rec  gen  $(nomm q.nomm, goal [%next rec])
      =^  l-rec  gen  (laze-past l-rec q.p.nomm)
      =^  l-don  gen  $(nomm q.p.nomm, goal [%next don])
      [(laze-copy l-don l-rec) gen]
    ::
        [%11 *]
      ?@  p.nomm
        ?.  ?=(hint-static p.nomm)  $(nomm q.nomm)
        =^  gol=laze  gen  (laze-past-if laz.simple q.nomm)
        =^  l-fol=laze  gen  $(nomm q.nomm, goal [%next gol])
        =^  i  gen  id
        [[*sure-ordered ~ [i l-fol]~] gen]
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  l-fol  gen  $(nomm q.nomm)
        ?:  (safe-nomm q.p.nomm)  [l-fol gen]
        =^  l-fol  gen  (laze-past l-fol q.p.nomm)
        =^  l-toke  gen  $(nomm q.p.nomm, goal [%next none])
        [(laze-copy l-toke l-fol) gen]
      =^  gol=laze  gen  (laze-past-if laz.simple q.nomm)
      =^  l-fol=laze  gen  $(nomm q.nomm, goal [%next gol])
      =^  l-fol=laze  gen
        =^  i  gen  id
        [[*sure-ordered ~ [i l-fol]~] gen]
      =^  l-toke  gen  $(nomm q.p.nomm, goal [%next this])
      [(laze-copy l-toke l-fol) gen]
    ::
        [%mean *]
      =^  gol=laze  gen  (laze-past-if laz.simple q.nomm)
      =^  l-fol=laze  gen  $(nomm q.nomm, goal [%next gol])
      =^  i  gen  id
      =/  l-fol=laze  [*sure-ordered ~ [i l-fol]~]
      =^  ned=need-ordered  gen
        ?^  (mean-konst b.nomm k.nomm)  [[%none ~] gen]
        (callee-need b.nomm)
      ::  as +run does ($soft-call)
      ::
      =^  l-arg=laze  gen
        ?:  (sound p.nomm ned)  [[[ned ~] ~ ~] gen]
        =^  i  gen  id
        =.  sofs.gen  (~(put in sofs.gen) i)
        [[*sure-ordered ~ [i [[ned ~] ~ ~]]~] gen]
      ::
      =^  l-trap  gen  $(nomm p.nomm, goal [%next l-arg])
      [(laze-copy l-trap l-fol) gen]
    ::
        [%12 *]
      =^  l-q  gen  $(nomm q.nomm, goal [%next this])
      =^  l-q  gen  (laze-past l-q p.nomm)
      =^  l-p  gen  $(nomm p.nomm, goal [%next this])
      [(laze-copy l-p l-q) gen]
    ==
  ::  register-less need of the callee: jet or SCC-local best guess or recur
  ::
  ::  what a callee reads first thing (+sure-of), as far as it is known
  ::
  ++  callee-sure
    |=  b-callee=bell
    ^-  need-ordered
    (~(gut by sure.cache.gen) b-callee [%none ~])
  ::
  ++  callee-need
    |=  b-callee=bell
    ^-  [need-ordered _gen]
    =/  rin=(unit ring)  (~(get by call.cole.jets.long-ska) b-callee)
    ?^  j=(biff rin ~(get by jets-hot))  [need.u.j gen]
    ?.  (~(has in scc) b-callee)  (callee-compiled b-callee)
    ::  a member of the SCC that has no shape yet is taken to read what it
    ::  may read (.top)
    ::
    :_  gen
    ?^  s=(~(get by map-local) b-callee)  need.u.s
    (~(gut by top) b-callee [%none ~])
  ::  need of a callee outside the SCC, compiled for it: from the compiled
  ::  functions in .gen, which compiling it extends
  ::
  ++  callee-compiled
    |=  b-callee=bell
    ^-  [need-ordered _gen]
    ?^  s=(~(get by nary.cache.gen) b-callee)  [need.u.s gen]
    =^  new-scc=(set bell)  sccs.cache.gen
      (scc-of b-callee calls.long-ska sccs.cache.gen)
    =^  m=(map bell straight)  cache.gen
      (compile-scc-in new-scc long-ska jets-hot cache.gen)
    [need:(~(got by m) b-callee) gen]
  ::
  ::  The constant to push for a deferred %mean instead of its arm: the arm's
  ::  product, when it is known and the call could be omitted
  ::
  ++  mean-konst
    |=  [b=bell k=(unit *)]
    ^-  (unit *)
    ?~  k  ~
    ?.  pure:(~(got by code.long-ska) b)  ~
    k
  ::
  ::  +split and +into give both halves a copy of every fork and bond entry
  ::  of the need they split, and a half keeps an entry even when it needs
  ::  nothing there.  Under a hinted push (=+  a=X  rest, with X in a %spot)
  ::  the head half of rest's entries ends up inside X's bond while the tail
  ::  half stays on top, where +copy-lazy cannot merge them back, so every
  ::  hinted push doubled the entries of the code after it.  Parsers built
  ::  of nested ;~ under !: got lazy needs of hundreds of thousands of
  ::  entries for a few hundred Nock nodes, and the compile time with them.
  ::
  ::  An entry that needs nothing gets no code (nothing to collapse into its
  ::  block, only an empty %brz when a fork forks it) and adds nothing to
  ::  the shape (MSG and union with none are none), so the halves drop such
  ::  entries.  Their kids are pruned first, so emptiness is a check of one
  ::  level.
  ::
  ++  lazy-empty
    |=  l=need-lazy
    ^-  ?
    ?&  ?=([%none ~] ned.sure.l)
        ?=(?(~ [%1 ~ ~]) lok.sure.l)
        ?=(~ fork.l)
        ?=(~ bond.l)
    ==
  ::
  ++  lazy-prune
    |=  l=need-lazy
    ^-  need-lazy
    :+  sure.l
      %+  skip  fork.l
      |=(e=lazy-fork &((lazy-empty laz.y.e) (lazy-empty laz.n.e)))
    (skip bond.l |=(e=lazy-bond (lazy-empty laz.e)))
  ::  +lazy-empty for shapes
  ::
  ++  laze-empty
    |=  l=laze
    ^-  ?
    ?&  ?=([%none ~] ned.sure.l)
        ?=(?(~ [%1 ~ ~]) lok.sure.l)
        ?=(~ fork.l)
        ?=(~ bond.l)
    ==
  ::  +lazy-prune for shapes
  ::
  ++  laze-prune
    |=  l=laze
    ^-  laze
    :+  sure.l
      %+  skip  fork.l
      |=(e=laze-fork &((laze-empty laz.y.e) (laze-empty laz.n.e)))
    (skip bond.l |=(e=laze-bond (laze-empty laz.e)))
  ::
  ++  laze-none-equivalent
    |=  laz=laze
    ^-  ?
    =*  none  .
    ?&  ?=([%none ~] ned.sure.laz)
        ?=(?(~ [%1 ~ ~]) lok.sure.laz)
        (levy fork.laz |=([[* a=laze] * b=laze] &((none a) (none b))))
        (levy bond.laz |=([* n=laze] (none n)))
    ==
  ++  laze-must
    |=  ned=need-ordered
    ^-  need-ordered
    ?-  -.ned
      %both  ned
      %this  ned
      ^      [%both ned]
      %none  [%this ~]
      %lax   [%this ~]
    ==
  ::  +split for shapes
  ::
  ++  laze-split
    ~%  %comp-laze-split  ..ride  ~
    |=  laz=laze
    ^-  [laze laze]
    =/  [lok-h=(set @) lok-t=(set @)]
      %-  ~(rep in lok.sure.laz)
      |=  [axe=@ lok-h=(set @) lok-t=(set @)]
      ?<  =(0 axe)
      ?:  ?=(?(%1 %2 %3) axe)  [lok-h lok-t]
      ?-  (cap axe)
        %2  [(~(put in lok-h) (mas axe)) lok-t]
        %3  [lok-h (~(put in lok-t) (mas axe))]
      ==
    ::
    =/  [ned-h=need-ordered ned-t=need-ordered]
      =/  ned  ned.sure.laz
      ?-  -.ned
        ^      [-.ned +.ned]
        %none  [ned ned]
        %this  [ned ned]
        %both  [(laze-must h.ned) (laze-must t.ned)]
        %lax   [h.ned t.ned]
      ==
    ::
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))
      [[[ned-h lok-h] ~ ~] [[ned-t lok-t] ~ ~]]
    =/  forks=(list [laze-fork laze-fork])
      %+  turn  fork.laz
      |=  [y=[o=@uxid laz=laze] n=[o=@uxid laz=laze]]
      =/  [y-h=laze y-t=laze]  (laze-split laz.y)
      =/  [n-h=laze n-t=laze]  (laze-split laz.n)
      [[[o.y y-h] [o.n n-h]] [[o.y y-t] [o.n n-t]]]
    ::
    =/  bonds=(list [laze-bond laze-bond])
      %+  turn  bond.laz
      |=  [o=@uxid laz=laze]
      =/  [h=laze t=laze]  (laze-split laz)
      [[o h] [o t]]
    ::
    :-  (laze-prune [ned-h lok-h] (turn forks head) (turn bonds head))
    (laze-prune [ned-t lok-t] (turn forks tail) (turn bonds tail))
  ::  +into for shapes
  ::
  ++  laze-into
    ~%  %comp-laze-into  ..ride  ~
    |=  [axe=@ laz=laze]
    ^-  [laze laze]
    ?<  =(0 axe)
    =/  [lok-don=(set @) lok-rec=(set @)]
      =;  [lok-don=(set @) lok-rec=(set @)]
        :-  lok-don
        ?:  =(1 axe)  lok-rec
        (~(put in lok-rec) axe)
      %-  ~(rep in lok.sure.laz)
      |=  [axe-lok=@ lok-don=(set @) lok-rec=(set @)]
      ?~  rest=(gep axe axe-lok)
        [lok-don (~(put in lok-rec) axe-lok)]
      ?:  =(1 u.rest)  [lok-don lok-rec]
      [(~(put in lok-don) u.rest) lok-rec]
    ::
    =/  [ned-don=need-ordered ned-rec=need-ordered]
      =/  ned  ned.sure.laz
      ?:  =(1 axe)  [ned none+~]
      =|  tack=(list [h=? n=need-ordered])
      |-  ^-  [need-ordered need-ordered]
      ?:  =(1 axe)
        :-  ned
        %+  roll  tack
        |:  [*[h=? n=need-ordered] acc=`need-ordered`[%none ~]]
        ^-  need-ordered
        ?:  h  (cons-need acc n)
        (cons-need n acc)
      =/  [h=? lat=@]  [?=(%2 (cap axe)) (mas axe)]
      ?-    -.ned
          %none  $(tack [[h ned] tack], axe lat)
          %this  $(tack [[h ned] tack], axe lat)
      ::
          ^
        =+  [new old]=?:(h ned [+.ned -.ned])
        $(tack [[h old] tack], ned new, axe lat)
      ::
          %both
        =/  l  (laze-must h.ned)
        =/  r  (laze-must t.ned)
        =+  [new old]=?:(h [l r] [r l])
        $(tack [[h old] tack], ned new, axe lat)
      ::
          %lax
        $(ned [h.ned t.ned])
      ==
    ::
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))
      [[[ned-don lok-don] ~ ~] [[ned-rec lok-rec] ~ ~]]
    =/  forks=(list [laze-fork laze-fork])
      %+  turn  fork.laz
      |=  [y=[o=@uxid laz=laze] n=[o=@uxid laz=laze]]
      =/  [y-don=laze y-rec=laze]  (laze-into axe laz.y)
      =/  [n-don=laze n-rec=laze]  (laze-into axe laz.n)
      [[[o.y y-don] [o.n n-don]] [[o.y y-rec] [o.n n-rec]]]
    ::
    =/  bonds=(list [laze-bond laze-bond])
      %+  turn  bond.laz
      |=  [o=@uxid laz=laze]
      =/  [don=laze rec=laze]  (laze-into axe laz)
      [[o don] [o rec]]
    ::
    :-  (laze-prune [ned-don lok-don] (turn forks head) (turn bonds head))
    (laze-prune [ned-rec lok-rec] (turn forks tail) (turn bonds tail))
  ::  +from for shapes
  ::
  ++  laze-from
    ~%  %comp-laze-from  ..ride  ~
    |=  [axe=@ laz=laze]
    ^-  laze
    ?<  =(0 axe)
    =/  sur=sure-ordered
      ?:  ?=(%none -.ned.sure.laz)
        :-  [%none ~]
        ?<  =(1 axe)
        ?:  =(~ lok.sure.laz)  [axe ~ ~]
        (~(run in lok.sure.laz) |=(x=@ (peg axe x)))
      :_  (~(run in lok.sure.laz) |=(x=@ (peg axe x)))
      =/  ned  ned.sure.laz
      |-  ^-  need-ordered
      ?:  =(1 axe)  ned
      ?-  (cap axe)
        %2  [$(axe (mas axe)) none+~]
        %3  [none+~ $(axe (mas axe))]
      ==
    ::
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [sur ~ ~]
    :+  sur
      %+  turn  fork.laz
      |=  [y=[o=@uxid laz=laze] n=[o=@uxid laz=laze]]
      [y(laz (laze-from axe laz.y)) n(laz (laze-from axe laz.n))]
    %+  turn  bond.laz
    |=  [o=@uxid laz=laze]
    [o (laze-from axe laz)]
  ++  laze-copy
    ~%  %comp-laze-copy  ..ride  ~
    |=  [first=laze second=laze]
    ^-  laze
    :+  :-  (uni-need-ord ned.sure.first ned.sure.second)
        (~(uni in lok.sure.first) lok.sure.second)
      ?:  =(~ fork.second)  fork.first
      ?:  =(~ fork.first)  fork.second
      =/  index=(map @uxid laze-fork)
        (malt (turn fork.second |=(e=laze-fork [o.y.e e])))
      =/  merged=(list laze-fork)
        %+  turn  fork.first
        |=  e=laze-fork
        ?~  m=(~(get by index) o.y.e)  e
        ?>  =(o.n.e o.n.u.m)
        :-  [o.y.e (laze-copy laz.y.e laz.y.u.m)]
        [o.n.e (laze-copy laz.n.e laz.n.u.m)]
      =/  seen=(set @uxid)  (silt (turn fork.first |=(e=laze-fork o.y.e)))
      (weld merged (skip fork.second |=(e=laze-fork (~(has in seen) o.y.e))))
    ?:  =(~ bond.second)  bond.first
    ?:  =(~ bond.first)  bond.second
    =/  index=(map @uxid laze-bond)
      (malt (turn bond.second |=(e=laze-bond [o.e e])))
    =/  merged=(list laze-bond)
      %+  turn  bond.first
      |=  e=laze-bond
      ?~  m=(~(get by index) o.e)  e
      [o.e (laze-copy laz.e laz.u.m)]
    =/  seen=(set @uxid)  (silt (turn bond.first |=(e=laze-bond o.e)))
    (weld merged (skip bond.second |=(e=laze-bond (~(has in seen) o.e))))
  ++  laze-sect
    |=  [l-0=laze l-1=laze]
    ^-  [laze _gen]
    =^  o-0  gen  id
    =^  o-1  gen  id
    [[*sure-ordered [[o-0 l-0] [o-1 l-1]]~ ~] gen]
  ++  lay-of
    |=  [=nomm sub=lay mono=?]
    ^-  lay
    ?-    nomm
        [^ *]      [$(nomm -.nomm) $(nomm +.nomm)]
        [%0 *]     ?:(=(0 p.nomm) %x (lay-slot sub p.nomm))
        [%1 *]     %w
        [%3 *]     %w
        [%4 *]     %w
        [%5 *]     %w
        [%12 *]    %w
        [%6 *]     (lay-join $(nomm q.nomm) $(nomm r.nomm))
        [%7 *]     $(nomm q.nomm, sub $(nomm p.nomm))
        [%10 *]    (lay-edit $(nomm q.nomm) p.p.nomm $(nomm q.p.nomm))
        [%11 *]    $(nomm q.nomm)
        [%mean *]  $(nomm q.nomm)
    ::
        [%2 *]
      ?:  |(mono ?=(~ info.nomm))  %w
      =/  ret=rets  (callee-rets u.info.nomm)
      |-  ^-  lay
      ?~  ret  %w
      ?-  -.ret
        %k  %w
        %m  %p
        %c  [$(ret p.ret) $(ret q.ret)]
      ==
    ==
  ::  +lerf: the blocks of a lazy need of the product of a fork read it
  ::  from one need of it, which the fork is then compiled for with the
  ::  sure need: no block gets a copy per branch (forks in a row doubled
  ::  them each time), and the product is not consed for them (+kerf).  The
  ::  need asks each branch for what it has (+lax-ord): a part that one
  ::  branch makes of parts and the other has in a register comes as
  ::  either, with a flag, and the block that reads it tests the flag
  ::  (+meet).  ~ if the block of a soft call would have to take a noun
  ::  apart: then the product goes into one register, as before.
  ::
  ++  lerf
    |=  [nex=next q=nomm r=nomm mono=?]
    ^-  [(unit next) _gen]
    =/  laz=need-lazy  laz.nex(sure *sure)
    =/  lo=need-ordered
      (lax-ord (lazy-want laz) (lay-of q %p mono) (lay-of r %p mono))
    ::
    ?.  (lazy-soft-ok laz lo)  [~ gen]
    =^  l=need  gen  (need-ord-alloc-regs lo)
    =^  o=@uwoo  gen  (emit ~ ~ %hop then.nex)
    =.  gen
      ?:  dropping  gen
      %^  walk-lazy  o  laz
      |=  [o-laz=@uwoo sur=sure gen-init=_gen]
      ^+  gen
      =.  gen  gen-init
      =^  [t=need lop=(list pole)]  gen  (sure-require-look sur)
      ?:  ?=(%none -.t)  gen
      =.  gen  (add-ops o-laz lop)
      (meet o-laz l t)
    ::
    =^  [ned=need ops=(list pole)]  gen
      (copy-need-make-ops ned.sure.laz.nex l)
    ::
    =.  gen  (add-ops o ops)
    [`[%next [[ned lok.sure.laz.nex] ~ ~] ~ o] gen]
  ::  the block of a soft call takes nothing apart to meet its need from
  ::  .lo: all it does there is tried (+soft-emit), and a noun that may come
  ::  either way can't be
  ::
  ++  lazy-soft-ok
    |=  [laz=need-lazy lo=need-ordered]
    ^-  ?
    ?&  %+  levy  bond.laz
        |=  e=lazy-bond
        ?&  ?|  !(~(has by soft.gen) o.e)
                %+  movable  lo
                (look-ord (need-to-ordered ned.sure.laz.e) lok.sure.laz.e)
            ==
            ^$(laz laz.e)
        ==
    ::
        %+  levy  fork.laz
        |=  e=lazy-fork
        &(^$(laz laz.y.e) ^$(laz laz.n.e))
    ==
  ::  +lerf for shapes
  ::
  ++  laze-lerf
    |=  [laz=laze q=nomm r=nomm]
    ^-  (unit laze)
    =/  rest=laze  laz(sure *sure-ordered)
    =/  lo=need-ordered
      (lax-ord (laze-want rest) (lay-of q %p |) (lay-of r %p |))
    ::
    ?.  (laze-soft-ok rest lo)  ~
    `[[(uni-need-ord ned.sure.laz lo) lok.sure.laz] ~ ~]
  ::
  ++  laze-soft-ok
    |=  [laz=laze lo=need-ordered]
    ^-  ?
    ?&  %+  levy  bond.laz
        |=  e=laze-bond
        ?&  ?|  !(~(has in sofs.gen) o.e)
                (movable lo (look-ord sure.laz.e))
            ==
            ^$(laz laz.e)
        ==
    ::
        %+  levy  fork.laz
        |=  e=laze-fork
        &(^$(laz laz.y.e) ^$(laz laz.n.e))
    ==
  ::  +meet: in the lazy block .o, the need .t met from the registers of
  ::  .l, a need of the same noun that was met where the noun was made.
  ::  A %lax part is told apart by its flag: where it came whole it is
  ::  taken apart here, as the block would have taken it apart; where a
  ::  noun is wanted whole and came in parts it is consed here.  The
  ::  registers of .l are read by proxy, see \$cond.
  ::
  ++  meet
    |=  [o=@uwoo l=need t=need]
    ^+  gen
    ?:  ?=(%none -.t)  gen
    ?:  (movable (need-to-ordered l) (need-to-ordered t))
      =^  ops  gen  (meet-moves o l t)
      (add-ops o ops)
    ?-    -.l
        %none  ~|(%meet-none !!)
        %both  ~|(%meet-both !!)
        %lax   (meet-lax o l t)
        %this
      =^  src  gen  (proxy r.l o)
      =^  ops  gen  (kern-need src t)
      (add-ops o ops)
    ::
        ^
      ?-    -.t
          %this  (whole-into o l r.t)
          ^
        =.  gen  $(l p.l, t p.t)
        $(l q.l, t q.t)
      ::
          %both
        =.  gen  (whole-into o l r.t)
        =.  gen  $(l p.l, t h.t)
        $(l q.l, t t.t)
      ::
          %lax
        =.  gen  (add-ops o (lax-parts t))
        =.  gen  $(l p.l, t h.t)
        $(l q.l, t t.t)
      ==
    ==
  ::  the moves of a need that is +movable
  ::
  ++  meet-moves
    |=  [o=@uwoo l=need t=need]
    ^-  [(list pole) _gen]
    ?-    -.t
        %none  [~ gen]
        %both  ~|(%meet-moves !!)
        %this
      ?>  ?=(%this -.l)
      =^  s  gen  (proxy r.l o)
      [[%mov s r.t]~ gen]
    ::
        ^
      ?>  ?=(^ -.l)
      =^  a  gen  $(l p.l, t p.t)
      =^  b  gen  $(l q.l, t q.t)
      [(weld a b) gen]
    ::
        %lax
      ?+    -.l  ~|(%meet-moves !!)
          %this
        =^  s  gen  (proxy r.l o)
        [(lax-whole s t) gen]
      ::
          ^
        =^  a  gen  $(l p.l, t h.t)
        =^  b  gen  $(l q.l, t t.t)
        [(weld (lax-parts t) (weld a b)) gen]
      ::
          %lax
        =^  g  gen  (proxy g.l o)
        =^  s  gen  (proxy r.l o)
        =^  a  gen  $(l h.l, t h.t)
        =^  b  gen  $(l t.l, t t.t)
        [[[%mov g g.t] [%mov s r.t] (weld a b)] gen]
      ==
    ==
  ::  the noun of the need .l, whole, into the register .d in block .o:
  ::  consed where it came in parts
  ::
  ++  whole-into
    |=  [o=@uwoo l=need d=@uvre]
    ^+  gen
    ?-    -.l
        %none  ~|(%whole-none !!)
        %both  ~|(%whole-both !!)
        %lax   (meet-lax o l [%this d])
        %this
      =^  s  gen  (proxy r.l o)
      (add-ops o [%mov s d]~)
    ::
        ^
      =^  h  gen  re
      =^  t  gen  re
      =.  gen  (add-ops o [%con h t d]~)
      =.  gen  $(l p.l, d h)
      $(l q.l, d t)
    ==
  ::  a %lax need .l by its flag, before what block .o holds now: two
  ::  blocks, one meets .t from the noun, the other from the parts, and a
  ::  join that gives the registers of .t (as +fork-need gives those of a
  ::  need to the branches of a fork)
  ::
  ++  meet-lax
    |=  [o=@uwoo l=need t=need]
    ^+  gen
    ?>  ?=(%lax -.l)
    =^  o-0  gen  oo
    =^  o-1  gen  oo
    =^  o-in  gen  oo
    =.  gen  (copy-tag o ~[o-0 o-1])
    =^  [t-0=need t-1=need]  gen  (fork-need t o-in o-0 o-1)
    =^  p  gen  (proxy g.l o)
    =^  o-if=@uwoo  gen  (emit ~ ~ [%brz p ~^o-0 ~^o-1])
    =.  gen  (insert-hop o o-if o-in)
    =.  gen  (meet o-0 [%this r.l] t-0)
    (meet o-1 [h.l t.l] t-1)
  ::
  ++  kerf
    ~%  %comp-kerf  ..ride  ~
    |=  =next
    ^-  [[@uwoo @uvre] _gen]
    =^  o  gen  (emit ~ ~ %hop then.next)
    =^  r=@uvre  gen  (kern o laz.next)
    [[o r] gen]
  ::
  ++  walk-lazy
    ~%  %comp-walk-lazy  ..ride  ~
    |=  [o=@uwoo laz=need-lazy f=$-([@uwoo sure _gen] _gen)]
    ^+  gen
    =*  walk  $
    !.
    =.  gen  (f o sure.laz gen)
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  gen
    =.  gen
      %+  roll  fork.laz
      |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen=_gen]
      =.  gen  walk(gen gen, laz laz.y, o o.y)
      walk(gen gen, laz laz.n, o o.n)
    ::
    %+  roll  bond.laz
    |=  [[o=@uwoo laz=need-lazy] gen=_gen]
    walk(gen gen, laz laz, o o)
  ::
  ++  kern
    ~%  %comp-kern  ..ride  ~
    |=  [o=@uwoo laz=need-lazy]
    ^-  [@uvre _gen]
    =^  r  gen  re
    ?:  dropping  [r gen]
    :-  r
    %^  walk-lazy  o  laz
    |=  [o-laz=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  [ned=need lop=(list pole)]  gen  (sure-require-look sur)
    ?:  ?=(%none -.ned)  gen
    =.  gen  (add-ops o-laz lop)
    =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
    ?:  (~(has by soft.gen) o-laz)  (soft-ask o-laz src ned)
    =^  ops  gen  (kern-need src ned)
    (add-ops o-laz ops)
  ::  Register to read `r` through in the lazy block `o`. Recorded in cond.gen
  ::  so that +sect can thread `r` through join blocks.
  ::
  ++  proxy
    ~%  %comp-proxy  ..ride  ~
    |=  [r=@uvre o=@uwoo]
    ^-  [@uvre _gen]
    =^  p  gen  re
    ?:  dropping  [p gen]
    [p gen(cond (~(put by cond.gen) p [r (~(got by tags.gen) o)]))]
  ::
  ++  kern-r-need
    ~%  %comp-kern-r-need  ..ride  ~
    |=  [o=@uwoo ned=need]
    ^-  [@uvre _gen]
    =^  r  gen  re
    =^  ops=(list pole)  gen  (kern-need r ned)
    =.  gen  (add-ops o ops)
    [r gen]
  ::
  ++  kern-need
    ~%  %comp-kern-need  ..ride  ~
    |=  [r=@uvre ned=need]
    ^-  [(list pole) _gen]
    =|  ops=(list pole)
    :: =;  [ops=(list pole) gen=_gen]
      :: ~?  (lien ops |=(op=pole ?=(%cel -.op)))  [ops ned]
      :: [ops gen]
    ::
    |-  ^-  [(list pole) _gen]
    ?-    -.ned
        %none  [ops gen]
        %this  ?<  =(r r.ned)  [[[%mov r r.ned] ops] gen]
        %lax   ?<  =(r r.ned)  [(weld (lax-whole r ned) ops) gen]
    ::
        ^
      =^  r-ned  gen  re
      $(ned [%both r-ned ned])
    ::
        %both
      =^  r-t    gen  re
      =^  ops-1  gen  $(ned t.ned, r r-t)
      =?  ops-1  !=(ops-1 ops)
        [[%tal r.ned r-t] ops-1]
      ::
      =.  ops  ops-1
      =^  r-h    gen  re
      =^  ops-1  gen  $(ned h.ned, r r-h)
      =?  ops-1  !=(ops-1 ops)
        [[%hed r.ned r-h] ops-1]
      ::
      =.  ops  ops-1
      =.  ops  [[%cel r.ned] ops]
      ?<  =(r r.ned)
      [[[%mov r r.ned] ops] gen]
    ==
  ::
  ::  +past-if: a hint that stops crash relocation (%spot, %mean, ..) ends
  ::  where its formula has made its product.  What follows the hint needs
  ::  parts of that product; if the formula met that need itself, a product
  ::  that is not a cell where a part is wanted would crash inside the hint,
  ::  and the trace would hold a frame that the plain interpreter has
  ::  already left.  So the sure need is met in a block of its own past the
  ::  hint's epilogue, as the needs of the lazy blocks of the goal already
  ::  are.  Unless meeting it cannot crash (+sound): then it is left to the
  ::  formula, and conses, branches and calls hand their parts on directly.
  ::
  ++  past-if
    |=  [nex=next nom=nomm region=(list @uxid)]
    ^-  [next _gen]
    ?:  ?&  ?=(?(~ [%1 ~ ~]) lok.sure.laz.nex)
            (sound nom (need-to-ordered ned.sure.laz.nex))
        ==
      [nex gen]
    =^  o  gen  (emit ~ ~ %hop then.nex)
    =.  gen  (set-tag o region)
    :_  gen
    [%next [*sure fork.laz.nex [[o [sure.laz.nex ~ ~]] bond.laz.nex]] ~ o]
  ::  +past-if for shapes
  ::
  ++  laze-past-if
    |=  [laz=laze nom=nomm]
    ^-  [laze _gen]
    ?:  ?&  ?=(?(~ [%1 ~ ~]) lok.sure.laz)
            (sound nom ned.sure.laz)
        ==
      [laz gen]
    =^  i  gen  id
    [[*sure-ordered fork.laz [[i [sure.laz ~ ~]] bond.laz]] gen]
  ::  +sound: no noun of unknown shape is taken apart to meet the need .ned
  ::  of the product of .nom: where parts are wanted the product is made of
  ::  parts, by a cons or by a call that returns them apart, in every branch
  ::
  ++  sound
    |=  [nom=nomm ned=need-ordered]
    ^-  ?
    (sound-far nom ned code.long-ska rets.cache.gen 3)
  ::  +made: the formula that makes the product of .nom, for +sound: a
  ::  formula that hands its subject on was given the subject by .sup, the
  ::  head of the composition it is the tail of
  ::
  ++  made
    |=  [nom=nomm sup=(unit nomm)]
    ^-  nomm
    ?:  &(?=([%0 %1] nom) ?=(^ sup))  u.sup
    nom
  ::
  ::  +soft-new: a direct call whose callee's need is met softly, by the
  ::  block of the call; +soft-bond moves it to the block of the bond
  ::
  ++  soft-new
    |=  $:  o=@uwoo
            kin=?(%call %tail %mean)
            b=bell
            rin=(unit ring)
            ned=need
            sur=need-ordered
            pros=(list @uvre)
            ret=rets
            out=@uwoo
            aux=*
        ==
    ^+  gen
    %=    gen
        soft
      (~(put by soft.gen) o [kin b rin ned sur o o o pros ret out aux ~])
    ==
  ::  +soft-bond: the need of the callee is bound at a block before the
  ::  call: all that takes a noun apart for the callee goes there
  ::
  ++  soft-bond
    |=  [nex=next region=(list @uxid)]
    ^-  [next _gen]
    =/  call=@uwoo  there.then.nex
    =^  l  gen  (emit ~ ~ %hop then.nex)
    =^  o  gen  (emit ~ ~ %hop ~ l)
    =^  h  gen  (emit ~ ~ %hop ~ o)
    =.  gen  (set-tag o region)
    =/  s=soft-call  (~(got by soft.gen) call)
    =.  soft.gen  (~(put by (~(del by soft.gen) call)) o s(head h, last l))
    :_  gen
    [%next [*sure ~ [o [sure.laz.nex ~ ~]]~] ~ h]
  ::  +soft-ask: the noun in .src is to be taken apart in the block .o of a
  ::  soft call, to meet .ned
  ::
  ++  soft-ask
    |=  [o=@uwoo src=@uvre ned=need]
    ^+  gen
    ?:  dropping  gen
    gen(soft (~(jab by soft.gen) o |=(s=soft-call s(req [[src ned] req.s]))))
  ++  soft-done
    ^+  gen
    ?:  dropping  gen
    =/  lis=(list [o=@uwoo s=soft-call])  ~(tap by soft.gen)
    |-  ^+  gen
    ?~  lis  gen
    $(lis t.lis, gen (soft-emit i.lis))
  ::  +soft-emit: the blocks of a soft call.  A noun that is taken apart
  ::  for the callee is a part of the callee's subject, as the caller has
  ::  it, or is above such parts (+soft-cut).  Above them the fetch is this
  ::  function's own, and crashes here.  The parts are tried: if one is not
  ::  a cell where the callee takes it apart, the callee's subject is made
  ::  of what there is (+soft-cons) and given to its subject version.
  ::
  ::  The tries come last, right before the call, and a try that fails
  ::  goes straight to the subject version: all that the bond's block makes
  ::  is there to make the subject of.  Unless the block, or what a fork
  ::  spliced into it, reads a register that a try defines (a part that is
  ::  passed twice): then the tries come first, a try that fails sets a
  ::  flag and gives its registers a 0 that nothing reads (+soft-try), and
  ::  the flag is tested before the call.
  ::
  ::  A fork does not take a noun apart in a branch for the need of a soft
  ::  call (+lazy-soft-ok).
  ::
  ++  soft-emit
    |=  [o=@uwoo s=soft-call]
    ^+  gen
    ?~  req.s  gen
    =/  axs=(map @uvre @)  (soft-axes ned.s)
    =^  cut=[ops=(list pole) tops=(list [q=@ r=@uvre ned=need])]  gen
      =|  acc=[ops=(list pole) tops=(list [q=@ r=@uvre ned=need])]
      =/  req=(list [src=@uvre ned=need])  req.s
      |-  ^-  [[ops=(list pole) tops=(list [q=@ r=@uvre ned=need])] _gen]
      ?~  req  [acc gen]
      =^  c  gen  (soft-cut src.i.req ned.i.req axs sur.s less.b.s)
      $(req t.req, acc [(weld ops.c ops.acc) (weld tops.c tops.acc)])
    ::  the fetches that are this function's, and the moves of the parts
    ::  that the callee takes whole, and of the wholes of those it takes
    ::  apart too
    ::
    =/  ops=(list pole)
      %+  weld  ops.cut
      %+  murn  tops.cut
      |=  [q=@ r=@uvre ned=need]
      ^-  (unit pole)
      =/  d=(unit @uvre)
        ?:  ?=(%this -.ned)  `r.ned
        ?:  ?=(%both -.ned)  `r.ned
        ~
      ?~  d  ~
      ?:  =(r u.d)  ~
      `[%mov r u.d]
    ::  what is tried: the parts under each noun
    ::
    =/  tries=(list [q=@ r=@uvre ned=need])
      %+  murn  tops.cut
      |=  [q=@ r=@uvre ned=need]
      ^-  (unit [q=@ r=@uvre ned=need])
      ?:  ?=(?(%none %this %lax) -.ned)  ~
      ?:  ?=(%both -.ned)  `[q r h.ned t.ned]
      `[q r ned]
    ::
    =/  hed=blob  (~(got by blocks.gen) head.s)
    ?>  ?=([~ ~ %hop ~ *] hed)
    ?~  tries  (emir head.s ~ ops fin.hed)
    =/  lat=blob  (~(got by blocks.gen) last.s)
    ?>  ?=([~ ~ %hop ~ *] lat)
    ::  the tries first, each going on to the next, the last to the block
    ::  of the bond; the flag is 0 until one fails, and is tested last.
    ::  Produces the flag
    ::
    =/  flag
      |=  fail=@uwoo
      ^-  [@uvre _gen]
      =^  f0  gen  re
      =^  [first=@uwoo f=@uvre]  gen
        =/  tops=(list [q=@ r=@uvre ned=need])  tries
        =/  nxt=@uwoo  there.t.fin.hed
        ::  the flags are made front to back, the blocks back to front
        ::
        =^  fla=(list @uvre)  gen
          =/  n=@ud  (lent tops)
          |-  ^-  [(list @uvre) _gen]
          ?:  =(0 n)  [~ gen]
          =^  r  gen  re
          =^  rest  gen  $(n (dec n))
          [[r rest] gen]
        ::
        =/  tops  (flop tops)
        =/  fla   (flop fla)
        |-  ^-  [[@uwoo @uvre] _gen]
        ?~  tops  [[nxt f0] gen]
        ?>  ?=(^ fla)
        =/  pre=@uvre  ?~(t.fla f0 i.t.fla)
        =^  n  gen  (soft-try r.i.tops ned.i.tops pre i.fla nxt)
        =^  [fir=@uwoo *]  gen  $(tops t.tops, fla t.fla, nxt n)
        [[fir i.fla] gen]
      ::
      =.  gen  (emir head.s ~ (snoc ops [%imm 0 f0]) %hop ~ first)
      [f (emir last.s ~ ~ %brz f t.fin.lat ~^fail)]
    ::  the subject of the callee, in .rub
    ::
    =/  tom=(map @ @uvre)
      (malt (turn tops.cut |=([q=@ r=@uvre ned=need] [q r])))
    ::
    =^  [kon=(list pole) rub=@uvre]  gen  (soft-cons ned.s tom less.b.s)
    ::  A trap whose arm lacks a part is pushed as the plain interpreter
    ::  pushes it: the trap itself, which is the subject of its arm, for
    ::  the renderer to run.  The epilogue of that frame is another: it
    ::  takes its pick by the flag.
    ::
    ?:  ?=(%mean kin.s)
      =/  [epil=@uwoo body=*]  ;;([@uwoo *] aux.s)
      =^  rum  gen  re
      =^  join=@uwoo  gen  (emit ~[rum] ~ %hop ~ out.s)
      =^  fail=@uwoo  gen
        %^  emit-cold  ~
          (snoc kon `pole`[%hdp %mean rub body])
        [%hop ~[`rub] join]
      ::
      =/  pla=blob  (~(got by blocks.gen) plain.s)
      ?>  ?=([~ * %hop ~ *] pla)
      =.  gen  (emir plain.s ~ body.pla %hop ~[~] join)
      =^  f=@uvre  gen  (flag(gen gen) fail)
      =/  epi=blob  (~(got by blocks.gen) epil)
      ?>  ?=([~ * %hop *] epi)
      =^  epa=@uwoo  gen  (emit epi)
      =^  epb=@uwoo  gen
        (emit-cold ~ `(list pole)`[%hde %mean rum body]~ fin.epi)
      ::
      (emir epil ~ ~ %brz f ~^epa ~^epb)
    ::  the call of the subject version
    ::
    =^  pes=@uwoo  gen
      ?:  ?=(%tail kin.s)  (soft-back ~ b.s rin.s rub)
      ::  The product goes on in the parts the callee returns it in, on
      ::  both ways: the subject version returns one noun, which is taken
      ::  apart for them (+conv)
      ::
      =^  opt=(list @uvre)  gen  (rets-regs ret.s)
      =^  mer=(list @uvre)  gen  (rets-regs ret.s)
      ?>  ?=(^ opt)
      =/  movs=(list pole)
        =/  [a=(list @uvre) b=(list @uvre)]  [mer pros.s]
        |-  ^-  (list pole)
        ?~  a  ~
        ?>  ?=(^ b)
        [[%mov i.a i.b] $(a t.a, b t.b)]
      ::
      =^  merge  gen  (emit mer movs %hop ~ out.s)
      =/  sub-v=(list @uvre)  (flatten-need ned.s)
      =.  gen
        %^  emir  plain.s  ~
        :_  [%hop (turn opt some) merge]
        ^-  (list pole)
        :-  ?~(rin.s [%cal b.s sub-v i.opt] [%caf b.s sub-v i.opt u.rin.s])
        =/  i=@ud  1
        =/  regs=(list @uvre)  t.opt
        |-  ^-  (list pole)
        ?~  regs  ~
        [[%rtl i i.regs] $(regs t.regs, i +(i))]
      ::
      =^  pro-pes  gen  re
      =^  pv=(list @uvre)  gen  (rets-regs ret.s)
      =^  end=@uwoo  gen  (emit-cold ~ ~ %hop (turn pv some) merge)
      =^  oc=@uwoo  gen  (conv pro-pes ret.s pv end &)
      %^  emit-cold  ~
        ^-  (list pole)
        :_  ~
        ?~(rin.s [%csl b.s rub pro-pes] [%csf b.s rub pro-pes u.rin.s])
      [%hop ~ oc]
    ::
    =^  fail=@uwoo  gen  (emit-cold ~ kon %hop ~ pes)
    ::  the registers that the tries define
    ::
    =/  def=(set @uvre)
      %-  silt
      ^-  (list @uvre)
      %-  zing
      (turn tries |=([q=@ r=@uvre ned=need] (flatten-need ned)))
    ::
    ?.  (soft-free o last.s def)  +:(flag(gen gen) fail)
    ::  the tries last
    ::
    =^  first=@uwoo  gen
      =/  tops=(list [q=@ r=@uvre ned=need])  tries
      =/  nxt=@uwoo  there.t.fin.lat
      |-  ^-  [@uwoo _gen]
      ?~  tops  [nxt gen]
      =^  n  gen  (mono-try-call ned.i.tops nxt [r.i.tops fail])
      $(tops t.tops, nxt n)
    ::
    =.  gen  (emir head.s ~ ops fin.hed)
    (emir last.s ~ ~ %hop ~ first)
  ::  +emit-cold: +emit for a block that runs when a try has failed: the
  ::  runtime lays the blocks with this bit in their label last, out of the
  ::  way of the code that falls through
  ::
  ++  emit-cold
    |=  =blob
    ^-  [@uwoo _gen]
    =^  o  gen  oo
    =/  c=@uwoo  (con (bex 30) o)
    [c (emir c blob)]
  ::
  ++  emit-as
    |=  [cold=? =blob]
    ^-  [@uwoo _gen]
    ?:(cold (emit-cold blob) (emit blob))
  ::  +soft-back: a block that does .kon and then runs the subject version
  ::  of .b on the subject in .rub, in place of the rest of this function.
  ::  The subject version returns one noun.  Where this function returns
  ::  its product in parts, it is called, and its product is taken apart
  ::  for them (+conv): the pairs that the shape has are there, the product
  ::  being that of this function
  ::
  ++  soft-back
    |=  [kon=(list pole) b=bell rin=(unit ring) rub=@uvre]
    ^-  [@uwoo _gen]
    =/  ret=rets  mine.gen
    ?~  ret
      (emit-cold ~ kon ?~(rin [%jsp b rub] [%jsf b rub u.rin]))
    =^  w  gen  re
    =^  v=(list @uvre)  gen  (rets-regs ret)
    ?>  ?=(^ v)
    =^  end=@uwoo  gen  (emit-cold ~ ~ [%dox v ret])
    =^  o=@uwoo  gen  (conv w ret v end &)
    %^  emit-cold  ~
      (snoc kon `pole`?~(rin [%csl b rub w] [%csf b rub w u.rin]))
    [%hop ~ o]
  ::  +soft-free: no block from .o on, before .las, reads a register in
  ::  .def: the block of a bond and what a fork spliced into it
  ::
  ++  soft-free
    |=  [o=@uwoo las=@uwoo def=(set @uvre)]
    ^-  ?
    =|  seen=(set @uwoo)
    =/  todo=(list @uwoo)  ~[o]
    |-  ^-  ?
    ?~  todo  &
    ?:  |(=(las i.todo) (~(has in seen) i.todo))  $(todo t.todo)
    =/  =blob  (~(got by blocks.gen) i.todo)
    ?:  (lien body.blob |=(op=pole (lien (get-regs op) ~(has in def))))  |
    =/  nex=(list @uwoo)
      ?+  -.fin.blob  ~
        %hop  ~[there.t.fin.blob]
        %clq  ~[there.z.fin.blob there.o.fin.blob]
        %eqq  ~[there.z.fin.blob there.o.fin.blob]
        %brn  ~[there.z.fin.blob there.o.fin.blob]
        %brz  ~[there.z.fin.blob there.o.fin.blob]
      ==
    ::  a block that ends otherwise is none of the bond's
    ::
    ?:  ?=(~ nex)  |
    $(todo (weld nex t.todo), seen (~(put in seen) i.todo))
  ::  +soft-try: the noun in .src is taken apart to meet .ned if it has the
  ::  cells; if it has not, the registers of .ned get 0, which nothing
  ::  reads, and the flag .f is 1; else .f is the flag .pre of the tries
  ::  before.  Goes on to .nxt
  ::
  ++  soft-try
    |=  [src=@uvre ned=need pre=@uvre f=@uvre nxt=@uwoo]
    ^-  [@uwoo _gen]
    =/  out=(list @uvre)  (flatten-need ned)
    =^  merge=@uwoo  gen  (emit (snoc out f) ~ %hop ~ nxt)
    ::  fresh registers on the way that has the cells
    ::
    =^  tem=need  gen  (need-ord-alloc-regs (need-to-ordered ned))
    =^  good=@uwoo  gen
      %^  emit  ~  ~
      [%hop (snoc (turn (flatten-need tem) some) `pre) merge]
    ::
    =^  zero  gen  re
    =^  one   gen  re
    =^  bad=@uwoo  gen
      %^  emit  ~
        `(list pole)`~[[%imm 0 zero] [%imm 1 one]]
      [%hop (snoc (turn out |=(* `(unit @uvre)``zero)) `one) merge]
    ::
    (mono-try-call tem good [src bad])
  ::  +soft-axes: where the registers of a callee's need are in its subject
  ::
  ++  soft-axes
    |=  ned=need
    ^-  (map @uvre @)
    =|  m=(map @uvre @)
    =/  axe=@  1
    |-  ^+  m
    ?-    -.ned
        %lax   ~|(%lax-in-a-shape !!)
        %none  m
        %this  (~(put by m) r.ned axe)
        ^      $(ned +.ned, axe (peg axe 3), m $(ned -.ned, axe (peg axe 2)))
        %both
      =.  m  (~(put by m) r.ned axe)
      $(ned t.ned, axe (peg axe 3), m $(ned h.ned, axe (peg axe 2)))
    ==
  ::  +soft-axis: the place in the callee's subject of the noun that .ned
  ::  is the need of: %any for no need, %no when it is not one place (the
  ::  noun is above parts of the callee's subject, or a register of the
  ::  need is none of the callee's: a fetch of the subject formula's own)
  ::
  ++  soft-axis
    |=  [ned=need axs=(map @uvre @)]
    ^-  $@(?(%any %no) [%at q=@])
    ?-    -.ned
        %lax   ~|(%lax-in-a-shape !!)
        %none  %any
        %this
      ?~  a=(~(get by axs) r.ned)  %no
      [%at u.a]
    ::
        ^
      (soft-pair $(ned -.ned) $(ned +.ned))
    ::
        %both
      =/  b  (soft-pair $(ned h.ned) $(ned t.ned))
      ::  a register that is none of the callee's holds a noun to cons
      ::  (+must): its place is that of its parts
      ::
      ?~  a=(~(get by axs) r.ned)
        ?:(?=(%any b) %no b)
      ?:  ?=(%any b)  [%at u.a]
      ?:  ?=(%no b)  %no
      ?.(=(q.b u.a) %no b)
    ==
  ::
  ++  soft-pair
    |=  $:  h=$@(?(%any %no) [%at q=@])
            t=$@(?(%any %no) [%at q=@])
        ==
    ^-  $@(?(%any %no) [%at q=@])
    ?:  |(?=(%no h) ?=(%no t))  %no
    ::  the parent of a head at 2q and of a tail at 2q+1 is q
    ::
    =/  qh=(unit @)
      ?@  h  ~
      ?.  &((gth q.h 1) =(0 (end 0 q.h)))  [~ 0]
      `(rsh 0 q.h)
    =/  qt=(unit @)
      ?@  t  ~
      ?.  &((gth q.t 1) =(1 (end 0 q.t)))  [~ 0]
      `(rsh 0 q.t)
    ?~  qh
      ?~  qt  %any
      ?:(=(0 u.qt) %no [%at u.qt])
    ?:  =(0 u.qh)  %no
    ?~  qt  [%at u.qh]
    ?.(=(u.qh u.qt) %no [%at u.qh])
  ::  +soft-cut: the noun in .src, to be taken apart to meet .ned: the
  ::  fetches that crash on a noun that is not a cell (.ops): this
  ::  function's own, above the callee's subject, and those of what the
  ::  callee reads first thing; and the other parts of the callee's
  ::  subject (.tops: place, register, need), which are tried
  ::
  ++  soft-cut
    |=  $:  src=@uvre
            ned=need
            axs=(map @uvre @)
            sur=need-ordered
            k=sock
        ==
    ^-  [[ops=(list pole) tops=(list [q=@ r=@uvre ned=need])] _gen]
    =/  q  (soft-axis ned axs)
    ?:  ?=(%any q)  [[~ ~] gen]
    ::  a part of the callee's subject: handed on whole, or taken apart
    ::  with a try, unless the callee reads it first thing (+sure-at): then
    ::  the fetch crashes as the callee would
    ::
    ?:  ?&  ?=(^ q)
            ?|  ?=(?(%none %this %lax) -.ned)
                !(sure-at q.q sur k)
            ==
        ==
      [[~ [q.q src ned]~] gen]
    ?-    -.ned
        %lax   ~|(%lax-in-a-shape !!)
        %none  [[~ ~] gen]
        %this
      ?<  =(src r.ned)
      [[[%mov src r.ned]~ ~] gen]
    ::
        ^
      =^  r-h  gen  re
      =^  r-t  gen  re
      =^  h  gen  $(src r-h, ned -.ned)
      =^  t  gen  $(src r-t, ned +.ned)
      :_  gen
      :_  (weld tops.h tops.t)
      ^-  (list pole)
      :-  [%cel src]
      %+  weld
        ?:  &(?=(~ ops.h) ?=(~ tops.h))  ~
        `(list pole)`[[%hed src r-h] ops.h]
      ?:  &(?=(~ ops.t) ?=(~ tops.t))  ~
      `(list pole)`[[%tal src r-t] ops.t]
    ::
        %both
      ?<  =(src r.ned)
      =^  r-h  gen  re
      =^  r-t  gen  re
      =^  h  gen  $(src r-h, ned h.ned)
      =^  t  gen  $(src r-t, ned t.ned)
      :_  gen
      :_  (weld tops.h tops.t)
      ^-  (list pole)
      :+  [%mov src r.ned]
        [%cel src]
      %+  weld
        ?:  &(?=(~ ops.h) ?=(~ tops.h))  ~
        `(list pole)`[[%hed src r-h] ops.h]
      ?:  &(?=(~ ops.t) ?=(~ tops.t))  ~
      `(list pole)`[[%tal src r-t] ops.t]
    ==
  ::  +soft-cons: the subject of a callee as a noun, from the registers of
  ::  its need .ned: the nouns in .tops where they are (a noun that was
  ::  tried is whole in its source), and what the callee's bell knows (.k)
  ::  where the need has nothing: where the bell knows nothing either, the
  ::  callee reads nothing
  ::
  ++  soft-cons
    |=  [ned=need tops=(map @ @uvre) k=sock]
    ^-  [[(list pole) @uvre] _gen]
    =/  axe=@  1
    |-  ^-  [[(list pole) @uvre] _gen]
    ?^  t=(~(get by tops) axe)  [[~ u.t] gen]
    ?:  ?=(%this -.ned)  [[~ r.ned] gen]
    ?:  ?=(%both -.ned)  [[~ r.ned] gen]
    ::  nothing of the callee's below: the noun of its bell, which has
    ::  what the bell knows, and elsewhere what nothing reads
    ::
    ?:  ?=(%none -.ned)
      =^  r  gen  re
      [[[%imm +.k r]~ r] gen]
    ?:  ?=(%lax -.ned)  ~|(%lax-in-a-shape !!)
    =/  [h=need t=need]  ned
    =^  [oh=(list pole) rh=@uvre]  gen
      $(ned h, k (hed:so k), axe (peg axe 2))
    ::
    =^  [ot=(list pole) rt=@uvre]  gen
      $(ned t, k (tel:so k), axe (peg axe 3))
    ::
    =^  r  gen  re
    [[:(weld oh ot `(list pole)`[%con rh rt r]~) r] gen]
  ::  +past: the need of what runs after .nom is bound past it, when .nom
  ::  has a hint that keeps a trace frame or a call that may crash
  ::  (+hinted): where this function takes a noun apart for the code that
  ::  follows, it does so past .nom, and not before a crash that the plain
  ::  interpreter comes to first, with other frames.  The shape the
  ::  function is entered with is the same: a bond is part of it.  The
  ::  bonds of the need are where they belong already.
  ::
  ++  past
    |=  [nex=next nom=nomm region=(list @uxid)]
    ^-  [next _gen]
    ?:  ?&  ?=([%none ~] ned.sure.laz.nex)
            ?=(?(~ [%1 ~ ~]) lok.sure.laz.nex)
            ?=(~ fork.laz.nex)
        ==
      [nex gen]
    ?.  (hinted nom code.long-ska)  [nex gen]
    =^  o  gen  (emit ~ ~ %hop then.nex)
    =.  gen  (set-tag o region)
    :_  gen
    [%next [*sure ~ [[o [sure.laz.nex fork.laz.nex ~]] bond.laz.nex]] ~ o]
  ::  +past for shapes
  ::
  ++  laze-past
    |=  [laz=laze nom=nomm]
    ^-  [laze _gen]
    ?:  ?&  ?=([%none ~] ned.sure.laz)
            ?=(?(~ [%1 ~ ~]) lok.sure.laz)
            ?=(~ fork.laz)
        ==
      [laz gen]
    ?.  (hinted nom code.long-ska)  [laz gen]
    =^  i  gen  id
    [[*sure-ordered ~ [[i [sure.laz fork.laz ~]] bond.laz]] gen]
  ::  +past-fork: +past for the need of the branches of a fork (+sect), when
  ::  the test .nom has such a hint: each branch is bound where it begins
  ::
  ++  past-fork
    |=  [laz=need-lazy nom=nomm]
    ^-  need-lazy
    ?.  (hinted nom code.long-ska)  laz
    :+  sure.laz
      %+  turn  fork.laz
      |=  e=lazy-fork
      ^-  lazy-fork
      :-  [o.y.e [*sure ~ [o.y.e laz.y.e]~]]
      [o.n.e [*sure ~ [o.n.e laz.n.e]~]]
    bond.laz
  ::
  ++  laze-past-fork
    |=  [laz=laze nom=nomm]
    ^-  laze
    ?.  (hinted nom code.long-ska)  laz
    :+  sure.laz
      %+  turn  fork.laz
      |=  e=laze-fork
      ^-  laze-fork
      :-  [o.y.e [*sure-ordered ~ [o.y.e laz.y.e]~]]
      [o.n.e [*sure-ordered ~ [o.n.e laz.n.e]~]]
    bond.laz
  ::
  ++  lazy-bound
    ~%  %comp-lazy-bound  ..ride  ~
    |=  [nex=next region=(list @uxid)]
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %hop then.nex)
    =.  gen  (set-tag o region)
    :_  gen
    ?>  =(~ args.then.nex)
    [%next [*sure ~ [o laz.nex]~] ~ o]
  ::
  ++  sect
    ~%  %comp-sect  ..ride  ~
    |=  $:  nex-0=next
            nex-1=next
            o-0-end=@uwoo
            o-1-end=@uwoo
            region-branch=(list @uxid)
            cond-before=cond   ::  cond.gen before the branches were compiled
            cond-between=cond  ::  cond.gen after the no branch was compiled
        ==
    ^-  [[need-lazy @uwoo @uwoo] _gen]
    ?>  ?=(^ region-branch)
    =^  o-0-beg  gen  (emit ~ ~ %hop then.nex-0)
    =^  o-1-beg  gen  (emit ~ ~ %hop then.nex-1)
    =.  gen  (set-tag o-0-beg region-branch)
    =.  gen  (set-tag o-1-beg region-branch)
    ::  Thread the registers read past the join through the join block, see
    ::  $cond
    ::
    =.  gen
      ?:  dropping  gen
      =/  made-0  (~(dif by cond.gen) cond-between)
      =/  made-1  (~(dif by cond-between) cond-before)
      =/  o-target=@uwoo
        =/  blob-0-end  (~(got by blocks.gen) o-0-end)
        =/  blob-1-end  (~(got by blocks.gen) o-1-end)
        ?>  ?=(%hop -.fin.blob-0-end)
        ?>  ?=(%hop -.fin.blob-1-end)
        ?>  =(there.t.fin.blob-0-end there.t.fin.blob-1-end)
        there.t.fin.blob-0-end
      ::
      =/  inside-branch
        |=(tag=(list @uxid) (lien tag |=(id=@uxid =(id i.region-branch))))
      ::
      =|  tars=(map @uvre @uvre)  ::  definition -> join parameter
      =/  args=[yes=(list (unit @uvre)) nuh=(list (unit @uvre)) tar=(list @uvre)]
        =/  yes-end=blob  (~(got by blocks.gen) o-0-end)
        ?>  ?=(%hop -.fin.yes-end)
        =/  nuh-end=blob  (~(got by blocks.gen) o-1-end)
        ?>  ?=(%hop -.fin.nuh-end)
        :+  args.t.fin.yes-end
          args.t.fin.nuh-end
        par:(~(got by blocks.gen) o-target)
      ::
      =>
        =*  dot  .
        ^+  dot
        %-  ~(rep by made-0)
        |=  [[k=@uvre v=[def=@uvre tag=(list @uxid)]] dot-init=_dot]
        =.  dot  dot-init
        ?:  (inside-branch tag.v)  dot
        ?^  tar=(~(get by tars) def.v)
          dot(cond.gen (~(put by cond.gen) k [u.tar tag.v]))
        =^  tar-new  gen  re
        =.  tars  (~(put by tars) def.v tar-new)
        =.  yes.args  [`def.v yes.args]
        =.  nuh.args  [~ nuh.args]
        =.  tar.args  [tar-new tar.args]
        =.  cond.gen  (~(put by cond.gen) k [tar-new tag.v])
        dot
      ::
      =>
        =*  dot  .
        ^+  dot
        %-  ~(rep by made-1)
        |=  [[k=@uvre v=[def=@uvre tag=(list @uxid)]] dot-init=_dot]
        =.  dot  dot-init
        ?:  (inside-branch tag.v)  dot
        ?^  tar=(~(get by tars) def.v)
          dot(cond.gen (~(put by cond.gen) k [u.tar tag.v]))
        =^  tar-new  gen  re
        =.  tars  (~(put by tars) def.v tar-new)
        =.  nuh.args  [`def.v nuh.args]
        =.  yes.args  [~ yes.args]
        =.  tar.args  [tar-new tar.args]
        =.  cond.gen  (~(put by cond.gen) k [tar-new tag.v])
        dot
      ::
      =.  blocks.gen  (~(jab by blocks.gen) o-target |=(blob +<(par tar.args)))
      =/  lens-hop
        |=  args=(list (unit @uvre))
        |=  b=blob
        ?>  ?=(%hop -.fin.b)
        b(args.t.fin args)
      ::
      =.  blocks.gen  (~(jab by blocks.gen) o-0-end (lens-hop yes.args))
      =.  blocks.gen  (~(jab by blocks.gen) o-1-end (lens-hop nuh.args))
      gen
    ::
    :_  gen
    ?>  =(~ args.then.nex-0)
    ?>  =(~ args.then.nex-1)
    :_  [o-0-beg o-1-beg]
    [*sure [[o-0-beg laz.nex-0] [o-1-beg laz.nex-1]]~ ~]
  ::
  ++  mede
    ~%  %comp-mede  ..ride  ~
    |=  [then=jmp som=* laz=need-lazy]
    ^-  [@uwoo _gen]
    =^  o=@uwoo  gen  (emit ~ ~ %hop then)
    ?:  dropping  [o gen]
    :-  o
    %^  walk-lazy  o  laz
    |=  [o=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  [ned=need lop=(list pole)]  gen  (sure-require-look sur)
    =.  gen  (add-ops o lop)
    |-  ^+  gen
    ?-    -.ned
        %none  gen
        %this  (add-ops o [%imm som r.ned]~)
        %lax   (add-ops o [[%imm som r.ned] t:(lax-whole r.ned ned)])
    ::
        ^
      ?@  som  (crash-need o [%& %imm som] ned)
      =.  gen  $(som -.som, ned -.ned)
      $(som +.som, ned +.ned)
    ::
        %both
      ?:  ?=(@ som)  (crash-need o [%& %imm som] ned)
      =.  gen  (add-ops o [%imm som r.ned]~)
      =.  gen  $(som -.som, ned h.ned)  ::  XX no +kern here, is OK?
      $(som +.som, ned t.ned)
    ==
  ::
  ::  ~: nothing needed
  ::  [~ @uvre @uwoo]: something is needed (an atom or whatever + crash)
  ::
  ++  collapse-lazy-atom
    ~%  %comp-collapse-lazy-atom  ..ride  ~
    |=  nex=next
    ^-  [(unit [@uvre @uwoo]) _gen]
    ?>  =(~ args.then.nex)
    ?:  (none-equivalent laz.nex)  [~ gen]
    =^  [ned-sure=need lop=(list pole)]  gen
      (sure-require-look sure.laz.nex)
    ::
    =.  gen  (add-ops there.then.nex lop)
    =^  r=@uvre  .
      =*  dot  .
      ?-    -.ned-sure
          %this
        [r.ned-sure dot]
      ::
          %lax
        =.  gen  (add-ops there.then.nex t:(lax-whole r.ned-sure ned-sure))
        [r.ned-sure dot]
      ::
          %none
        =^  r  gen  re
        [r dot]
      ::
          ^
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %bom ~)
        =.  there.then.nex  o
        [r dot]
      ::
          %both
        =^  o  gen  (emit ~ ~ %bom ~)
        =.  there.then.nex  o
        [r.ned-sure dot]
      ==
    ::
    :-  `[r there.then.nex]
    ?:  dropping  gen
    ::  add moves wherever lazy needs need one noun, crashes wherever lazy
    ::  needs need more than an atom
    ::
    =/  o  there.then.nex
    %^  walk-lazy  o  laz.nex(ned.sure this+r)
    |=  [o-laz=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  [ned-sure=need lop=(list pole)]  gen  (sure-require-look sur)
    =.  gen  (add-ops o-laz lop)
    ?:  ?=(%none -.ned-sure)  gen
    ?:  ?=(%this -.ned-sure)
      ?:  =(r r.ned-sure)  gen
      =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
      (add-ops o-laz [%mov src r.ned-sure]~)
    ?:  ?=(%lax -.ned-sure)
      ?:  =(r r.ned-sure)  gen
      =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
      (add-ops o-laz (lax-whole src ned-sure))
    =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
    (crash-need o-laz [%| src] ned-sure)
  ::  A need for the parts of an atom, in block .o: the fetch crashes there.
  ::  The block is not made a crash as a whole: it keeps its place in the
  ::  control flow, since a fork may still splice into it (+insert-hop), and
  ::  the registers of the need are defined, with values nothing reads.
  ::  The atom is an immediate or in a register
  ::
  ++  crash-need
    |=  [o=@uwoo atom=(each [%imm n=@] @uvre) ned=need]
    ^+  gen
    =/  fill=(list pole)
      (turn (flatten-need ned) |=(x=@uvre `pole`[%imm 0 x]))
    ?-    -.atom
        %|
      ?:  (~(has by soft.gen) o)  (soft-ask o p.atom ned)
      (add-ops o [[%cel p.atom] fill])
    ::
        %&
      =^  r  gen  re
      ?:  (~(has by soft.gen) o)
        (soft-ask(gen (add-ops o [%imm n.p.atom r]~)) o r ned)
      (add-ops o [[%imm n.p.atom r] [%cel r] fill])
    ==
  ::
  ++  flatten-need
    ~%  %comp-flatten-need  ..ride  ~
    |=  ned=need
    ^-  (list @uvre)
    =*  flat  .
    ?-  -.ned
      %none  ~
      %this  ~[r.ned]
      ^      (weld (flat -.ned) (flat +.ned))
      %both  [r.ned (weld (flat h.ned) (flat t.ned))]
      %lax   [g.ned r.ned (weld (flat h.ned) (flat t.ned))]
    ==
  ::  %lax needs (see \$need).  +lax-whole: the ops that meet one with the
  ::  noun in .src: the registers of its parts get 0, which nothing reads.
  ::  +lax-parts: the ops for one that is met by its parts
  ::
  ++  lax-whole
    |=  [src=@uvre ned=need]
    ^-  (lest pole)
    ?>  ?=(%lax -.ned)
    :+  [%mov src r.ned]
      [%imm 0 g.ned]
    %+  turn  (weld (flatten-need h.ned) (flatten-need t.ned))
    |=(x=@uvre `pole`[%imm 0 x])
  ::
  ++  lax-parts
    |=  ned=need
    ^-  (list pole)
    ?>  ?=(%lax -.ned)
    ~[[%imm 1 g.ned] [%imm 0 r.ned]]
  ::  fork CFG
  ::
  ::  Produces a pair of needs, emitting code into given o-0/1 provided by the
  ::  caller
  ::
  ++  fork-sure
    ~%  %comp-fork-sure  ..ride  ~
    |=  [sur=sure o=@uwoo o-0=@uwoo o-1=@uwoo]
    ^-  [[sure sure] _gen] 
    =^  [ned-0=need ned-1=need]  gen  (fork-need ned.sur o o-0 o-1)
    [[[ned-0 lok.sur] [ned-1 lok.sur]] gen]
  ::
  ++  fork-need
    ~%  %comp-fork-need  ..ride  ~
    |=  [ned=need o=@uwoo o-0=@uwoo o-1=@uwoo]
    ^-  [[need need] _gen]
    =;  [[ned-0=need ned-1=need] gen1=_gen]
      =.  gen  gen1
      :-  [ned-0 ned-1]
      =/  args-0  (turn (flatten-need ned-0) some)
      =/  args-1  (turn (flatten-need ned-1) some)
      =^  barg  gen  (emit (flatten-need ned) ~ %hop ~ o)
      =.  gen  (emir o-0 ~ ~ %hop args-0 barg)
      (emir o-1 ~ ~ %hop args-1 barg)
    ::
    |-  ^-  [[need need] _gen]
    ?-    -.ned
        %none  [[[%none ~] [%none ~]] gen]
    ::
        %this
      =^  r-0  gen  re
      =^  r-1  gen  re
      :_  gen
      [[%this r-0] [%this r-1]]
    ::
        ^
      =^  [hed-0=need hed-1=need]  gen  $(ned -.ned)
      =^  [tel-0=need tel-1=need]  gen  $(ned +.ned)
      :_  gen
      ::  no need to normalize, shapes are preserved
      ::
      [[hed-0 tel-0] [hed-1 tel-1]]
    ::
        %both
      =^  r-0  gen  re
      =^  r-1  gen  re
      =^  [hed-0=need hed-1=need]  gen  $(ned h.ned)
      =^  [tel-0=need tel-1=need]  gen  $(ned t.ned)
      :_  gen
      [[%both r-0 hed-0 tel-0] [%both r-1 hed-1 tel-1]]
    ::
        %lax
      =^  g-0  gen  re
      =^  g-1  gen  re
      =^  r-0  gen  re
      =^  r-1  gen  re
      =^  [hed-0=need hed-1=need]  gen  $(ned h.ned)
      =^  [tel-0=need tel-1=need]  gen  $(ned t.ned)
      :_  gen
      [[%lax g-0 r-0 hed-0 tel-0] [%lax g-1 r-1 hed-1 tel-1]]
    ==
  ::  o2 is empty
  ::  a -> b  ==>  a -> o' ... o'' -> b
  ::
  ::  o' and o'' are assumed to be linked somehow. Right now they are linked
  ::  with a control flow fork and join.
  ::
  ::  It also moves code from a to o''! That way the fork between o' and o''
  ::  precedes the code that uses the product of the fork.
  ::
  ++  insert-hop
    ~%  %comp-insert-hop  ..ride  ~
    |=  [a=@uwoo o1=@uwoo o2=@uwoo]
    ^+  gen
    ?:  dropping  gen
    =/  blob-from=blob  (~(got by blocks.gen) a)
    ?>  ?=(%hop -.fin.blob-from)
    ?>  =(~ par.blob-from)
    :: ?>  =(~ args.t.fin.blob-from)
    =/  a-to-b=jmp  t.fin.blob-from
    =.  gen  (emir o2 ~ body.blob-from fin.blob-from)
    gen(blocks (~(put by blocks.gen) a blob-from(body ~, t.fin [~ o1])))
  ::  fork CFG for loobean-producing opcodes
  ::
  ++  forl
    ~%  %comp-forl  ..ride  ~
    |=  [r=@uvre o=@uwoo]
    ^-  [[@uwoo @uwoo] _gen]
    =^  r-0   gen  re
    =^  r-1   gen  re
    =^  barg  gen  (emit ~[r] ~ %hop ~ o)
    =^  if-0  gen  (emit ~ [%imm `*`0 r-0]~ %hop ~[`r-0] barg)
    =^  if-1  gen  (emit ~ [%imm `*`1 r-1]~ %hop ~[`r-1] barg)
    [[if-0 if-1] gen]
  ::
  ++  emit
    ~%  %comp-emit  ..ride  ~
    |=  =blob
    ^-  [@uwoo _gen]
    =^  o  gen  oo
    [o (emir o blob)]
  ::
  ++  from-sure
    ~%  %comp-from-sure  ..ride  ~
    |=  [axe=@ sur=sure]
    ^-  sure
    ?<  =(0 axe)
    ?:  ?=(%none -.ned.sur)
      :-  [%none ~]
      ?<  =(1 axe)
      ?:  =(~ lok.sur)  [axe ~ ~]
      (~(run in lok.sur) |=(x=@ (peg axe x)))
    :_  (~(run in lok.sur) |=(x=@ (peg axe x)))
    |-  ^-  need
    ?:  =(1 axe)  ned.sur
    ?-  (cap axe)
      %2  [$(axe (mas axe)) none+~]
      %3  [none+~ $(axe (mas axe))]
    ==
  ::
  ++  from
    ~%  %comp-from  ..ride  ~
    |=  [axe=@ laz=need-lazy]
    ^-  need-lazy
    =*  from-buc  $
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [(from-sure axe sure.laz) ~ ~]
    :+  (from-sure axe sure.laz)
      %+  turn  fork.laz
      |=  [y=[@uwoo laz=need-lazy] n=[@uwoo laz=need-lazy]]
      [y(laz from-buc(laz laz.y)) n(laz from-buc(laz laz.n))]
    %+  turn  bond.laz
    |=  [o=@uwoo laz=need-lazy]
    [o from-buc(laz laz)]
  ++  copy
    ~%  %comp-copy  ..ride  ~
    |=  [first=next second=need-lazy]
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %hop then.first)
    =^  laz=need-lazy  gen  (copy-lazy o laz.first second)
    [[%next laz ~ o] gen]
  ::
  ++  copy-lazy
    ~%  %comp-copy-lazy  ..ride  ~
    |=  [o=@uwoo first=need-lazy second=need-lazy]
    ^-  [need-lazy _gen]
    =*  copy-lazy  $
    =^  [ned=need ops=(list pole)]  gen
      (copy-need-make-ops ned.sure.first ned.sure.second)
    ::
    =.  gen  (add-ops o ops)
    ::  Fork and bond entries of the two needs that name the same lazy block
    ::  come from the two children of one node (+split/+into share the block
    ::  labels between the halves) and describe two needs of the same subject
    ::  in the same block, so they are merged the same way as the sure needs,
    ::  with the moves emitted into that lazy block.  Without this each
    ::  autocons leaf would contribute its own copy of the whole fork list.
    ::
    =^  fork=(list lazy-fork)  gen
      ?:  =(~ fork.second)  [fork.first gen]
      ?:  =(~ fork.first)  [fork.second gen]
      =/  index=(map @uwoo lazy-fork)
        (malt (turn fork.second |=(e=lazy-fork [o.y.e e])))
      ::
      =^  merged=(list lazy-fork)  gen
        %^  spin  fork.first  gen
        |=  [e=lazy-fork gen-acc=_gen]
        ^-  [lazy-fork _gen]
        =.  gen  gen-acc
        ?~  m=(~(get by index) o.y.e)  [e gen]
        ?>  =(o.n.e o.n.u.m)
        =^  laz-y  gen  copy-lazy(o o.y.e, first laz.y.e, second laz.y.u.m)
        =^  laz-n  gen  copy-lazy(o o.n.e, first laz.n.e, second laz.n.u.m)
        [[[o.y.e laz-y] [o.n.e laz-n]] gen]
      ::
      =/  seen=(set @uwoo)  (silt (turn fork.first |=(e=lazy-fork o.y.e)))
      :_  gen
      (weld merged (skip fork.second |=(e=lazy-fork (~(has in seen) o.y.e))))
    ::
    =^  bond=(list lazy-bond)  gen
      ?:  =(~ bond.second)  [bond.first gen]
      ?:  =(~ bond.first)  [bond.second gen]
      =/  index=(map @uwoo lazy-bond)
        (malt (turn bond.second |=(e=lazy-bond [o.e e])))
      =^  merged=(list lazy-bond)  gen
        %^  spin  bond.first  gen
        |=  [e=lazy-bond gen-acc=_gen]
        ^-  [lazy-bond _gen]
        =.  gen  gen-acc
        ?~  m=(~(get by index) o.e)  [e gen]
        =^  laz  gen  copy-lazy(o o.e, first laz.e, second laz.u.m)
        [[o.e laz] gen]
      ::
      =/  seen=(set @uwoo)  (silt (turn bond.first |=(e=lazy-bond o.e)))
      :_  gen
      (weld merged (skip bond.second |=(e=lazy-bond (~(has in seen) o.e))))
    ::
    :_  gen
    [[ned (~(uni in lok.sure.first) lok.sure.second)] fork bond]
  ::  +split-* and +into-* for autoconses and Nock 10 follow the same pattern:
  ::  they split a lazy need into two, emitting consing code into the BBs of the
  ::  children lazy needs. The split needs share the BB label, which should be
  ::  fine since they produce disjoint parts of a noun
  ::
  ++  into-sure
    ~%  %comp-into-sure  ..ride  ~
    |=  [axe=@ sur=sure o=@uwoo]
    ^-  [[sure sure] _gen]
    =;  [lok-don=(set @) lok-rec=(set @)]
      =^  [ned-don=need ned-rec=need]  gen  (into-need axe ned.sur o)
      [[[ned-don lok-don] [ned-rec lok-rec]] gen]
    ::
    =;  [lok-don=(set @) lok-rec=(set @)]
      :-  lok-don
      ?:  =(1 axe)  lok-rec
      (~(put in lok-rec) axe)
    ::
    %-  ~(rep in lok.sur)
    |=  [axe-lok=@ lok-don=(set @) lok-rec=(set @)]
    ?<  =(0 axe)
    ?~  rest=(gep axe axe-lok)
      [lok-don (~(put in lok-rec) axe-lok)]
    ?:  =(1 u.rest)  [lok-don lok-rec]
    [(~(put in lok-don) u.rest) lok-rec]
  ::
  ++  into-need
    ~%  %comp-into-need  ..ride  ~
    |=  [axe=@ ned=need o=@uwoo]
    ^-  [[need need] _gen]
    ?<  =(0 axe)
    ?:  =(1 axe)  [[ned none+~] gen]
    =|  tack=(list [h=? n=need])
    =|  ops=(list pole)
    |-  ^-  [[need need] _gen]
    ?:  =(1 axe)
      =.  gen  (add-ops o ops)
      =;  big=need  [[ned big] gen]
      %+  roll  tack
      |:  [*[h=? n=need] acc=`need`[%none ~]]
      ^-  need
      ?:  h  (cons-need acc n)
      (cons-need n acc)
    =/  [h=? lat=@]  [?=(%2 (cap axe)) (mas axe)]
    ?-    -.ned
        %none  $(tack [[h ned] tack], axe lat)  ::  XX we don't have to descend here
    ::
        %this
      =^  l  gen  re
      =^  r  gen  re
      =/  =pole  [%con l r r.ned]
      =+  [new old]=?:(h [l r] [r l])
      $(tack [[h %this old] tack], ned [%this new], ops [pole ops], axe lat)
    ::
        ^
      =+  [new old]=?:(h ned [q.ned p.ned])
      $(tack [[h old] tack], ned new, axe lat)
    ::
        %both
      =^  l  gen  (must-at o h.ned)
      =^  r  gen  (must-at o t.ned)
      =/  =pole  [%con p.l p.r r.ned]
      =+  [new old]=?:(h [q.l q.r] [q.r q.l])
      $(tack [[h old] tack], ned new, ops [pole ops], axe lat)
    ::  an edit makes the noun of parts
    ::
        %lax
      $(ned [h.ned t.ned], ops (weld (lax-parts ned) ops))
    ==
  ::
  ++  into
    ~%  %comp-into  ..ride  ~
    |=  [nex=next axe=@]
    ^-  [[need-lazy need-lazy @uwoo] _gen]
    =^  o=@uwoo  gen  (emit ~ ~ %hop then.nex)
    =;  [[ned-don=need-lazy ned-rec=need-lazy] gen=_gen]
      [[ned-don ned-rec o] gen]
    ::
    =/  laz=need-lazy  laz.nex
    |-  ^-  [[need-lazy need-lazy] _gen]
    =*  split-loop  $
    =^  [sure-don=sure sure-rec=sure]  gen  (into-sure axe sure.laz o)
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [[[sure-don ~ ~] [sure-rec ~ ~]] gen]
    =*  fork  ,(list [[@uwoo need-lazy] [@uwoo need-lazy]])
    =^  [fork-don=fork fork-rec=fork]  gen
      %^  spin-split  fork.laz  gen
      |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen-acc=_gen]
      =*  i  ,[[@uwoo need-lazy] [@uwoo need-lazy]]
      ^-  [[i i] _gen]
      =.  gen  gen-acc
      =^  [laz-y-don=need-lazy laz-y-rec=need-lazy]  gen
        split-loop(laz laz.y, o o.y)
      ::
      =^  [laz-n-don=need-lazy laz-n-rec=need-lazy]  gen
        split-loop(laz laz.n, o o.n)
      ::
      :_  gen
      :-  [[o.y laz-y-don] [o.n laz-n-don]]
      [[o.y laz-y-rec] [o.n laz-n-rec]]
    ::
    =*  bond  ,(list [o=@uwoo laz=need-lazy])
    =^  [bond-don=bond bond-rec=bond]  gen
      %^  spin-split  bond.laz  gen
      |=  [[o-bond=@uwoo laz-bond=need-lazy] gen-acc=_gen]
      ^-  [[[@uwoo need-lazy] [@uwoo need-lazy]] _gen]
      =.  gen  gen-acc
      =^  [laz-don=need-lazy laz-rec=need-lazy]  gen
        split-loop(laz laz-bond, o o-bond)
      ::
      [[[o-bond laz-don] [o-bond laz-rec]] gen]
    ::
    :_  gen
    :-  (lazy-prune sure-don fork-don bond-don)
    (lazy-prune sure-rec fork-rec bond-rec)
  ::
  ++  split-sure
    ~%  %comp-split-sure  ..ride  ~
    |=  [sur=sure o=@uwoo]
    ^-  [[sure sure] _gen]
    =;  [lok-h=(set @) lok-t=(set @)]
      =^  [ned-h=need ned-t=need]  gen  (split-need ned.sur o)
      [[[ned-h lok-h] [ned-t lok-t]] gen]
    ::
    %-  ~(rep in lok.sur)
    |=  [axe=@ lok-h=(set @) lok-t=(set @)]
    ?<  =(0 axe)
    ?:  ?=(?(%1 %2 %3) axe)  [lok-h lok-t]
    ?-  (cap axe)
      %2  [(~(put in lok-h) (mas axe)) lok-t]
      %3  [lok-h (~(put in lok-t) (mas axe))]
    ==
  ::
  ++  split-need
    ~%  %comp-split-need  ..ride  ~
    |=  [ned=need o=@uwoo]
    ^-  [[need need] _gen]
    ?-    -.ned
        ^      [[p.ned q.ned] gen]
        %none  [[ned ned] gen]
    ::
        %this
      =^  h  gen  re
      =^  t  gen  re
      =.     gen  (add-ops o [%con h t r.ned]~)
      [[this+h this+t] gen]
    ::
        %both
      =^  hed  gen  (must-at o h.ned)
      =^  tel  gen  (must-at o t.ned)
      =.       gen  (add-ops o [%con p.hed p.tel r.ned]~)
      [[q.hed q.tel] gen]
    ::
        %lax
      =.  gen  (add-ops o (lax-parts ned))
      [[h.ned t.ned] gen]
    ==
  ::
  ++  must
    ~%  %comp-must  ..ride  ~
    |=  ned=need
    ^-  [(pair @uvre $>(?(%both %this) need)) _gen]
    ?-  -.ned
      %both  [[r.ned ned] gen]
      %this  [[r.ned ned] gen]
      ^      =^(r gen re [[r %both r ned] gen])
      %none  =^(r gen re [[r %this r] gen])
      %lax   ~|(%must-lax !!)
    ==
  ::  +must in block .o, which gets the ops for a %lax need: it is met with
  ::  the noun whole
  ::
  ++  must-at
    |=  [o=@uwoo ned=need]
    ^-  [(pair @uvre $>(?(%both %this) need)) _gen]
    ?.  ?=(%lax -.ned)  (must ned)
    =^  w  gen  re
    =.  gen  (add-ops o (lax-whole w ned))
    [[w %this w] gen]
  ::
  ++  split
    ~%  %comp-split  ..ride  ~
    |=  nex=next
    ^-  [[need-lazy need-lazy @uwoo] _gen]
    (split-in nex ~)
  ::  +split for a product that is an atom or a pair and comes as a tag and
  ::  its halves (+spread)
  ::
  ++  split-tag
    |=  [nex=next tag=@uvre]
    ^-  [[need-lazy need-lazy @uwoo] _gen]
    (split-in nex `tag)
  ::  the tag of a sum as read in block .o: lazy blocks read it by proxy
  ::
  ++  tag-in
    |=  [o=@uwoo tag=@uvre top=?]
    ^-  [@uvre _gen]
    ?:  top  [tag gen]
    (proxy tag o)
  ::  In block .o, before what it holds now: .r is the pair of .h and .t if
  ::  .src is a cell, else .src.  The ops of the block read .r (they were
  ::  added before, so they run after), so they move to a block past the
  ::  join; .o stays a hop that takes the ops added from now on, which
  ::  make .h and .t, and +insert-hop may still splice into it
  ::
  ++  join-after
    |=  [o=@uwoo src=@uvre h=@uvre t=@uvre r=@uvre]
    ^+  gen
    ?:  dropping  gen
    =/  bob=blob  (~(got by blocks.gen) o)
    =^  rest  gen  (emit ~ body.bob fin.bob)
    =^  j  gen  (emit ~[r] ~ %hop ~ rest)
    =^  rk  gen  re
    =^  k  gen  (emit ~ [%con h t rk]~ %hop ~[`rk] j)
    =^  a  gen  (emit ~ ~ %hop ~[`src] j)
    =^  x  gen  (emit ~ ~ [%clq src [~ k] [~ a]])
    =.  gen  (emir o par.bob ~ [%hop ~ x])
    ?.  (~(has by tags.gen) o)  gen
    (copy-tag o ~[rest j k a x])
  ::
  ++  split-sure-tag
    |=  [sur=sure o=@uwoo tag=@uvre top=?]
    ^-  [[sure sure] _gen]
    ::  .deep: something is fetched from the noun, so it must be a cell
    ::
    =/  [lok-h=(set @) lok-t=(set @) deep=?]
      %-  ~(rep in lok.sur)
      |=  [axe=@ lok-h=(set @) lok-t=(set @) deep=_`?`|]
      ?<  =(0 axe)
      ?:  =(1 axe)  [lok-h lok-t deep]
      ?:  ?=(?(%2 %3) axe)  [lok-h lok-t &]
      ?-  (cap axe)
        %2  [(~(put in lok-h) (mas axe)) lok-t &]
        %3  [lok-h (~(put in lok-t) (mas axe)) &]
      ==
    =^  [ned-h=need ned-t=need]  gen  (split-need-tag ned.sur o tag top deep)
    [[[ned-h lok-h] [ned-t lok-t]] gen]
  ::
  ++  split-need-tag
    |=  [ned=need o=@uwoo tag=@uvre top=? cel=?]
    ^-  [[need need] _gen]
    ?-    -.ned
        ^
      =^  src  gen  (tag-in o tag top)
      =.  gen  (add-ops o [%cel src]~)
      [[p.ned q.ned] gen]
    ::
        %none
      ?.  cel  [[ned ned] gen]
      =^  src  gen  (tag-in o tag top)
      =.  gen  (add-ops o [%cel src]~)
      [[ned ned] gen]
    ::
        %this
      =^  src  gen  (tag-in o tag top)
      ?:  (~(has in tst.gen) r.ned)
        =.  gen
          %+  add-ops  o
          ?:(cel ~[[%cel src] [%mov src r.ned]] [%mov src r.ned]~)
        [[[%none ~] [%none ~]] gen]
      =^  h  gen  re
      =^  t  gen  re
      =.  gen  (join-after o src h t r.ned)
      =?  gen  cel  (add-ops o [%cel src]~)
      [[this+h this+t] gen]
    ::
        %lax
      =^  w  gen  re
      =.  gen  (add-ops o (lax-whole w ned))
      $(ned [%this w])
    ::
        %both
      =^  src  gen  (tag-in o tag top)
      ?:  (~(has in tst.gen) r.ned)
        =.  gen  (add-ops o ~[[%cel src] [%mov src r.ned]])
        [[h.ned t.ned] gen]
      =^  hed  gen  (must-at o h.ned)
      =^  tel  gen  (must-at o t.ned)
      =.  gen  (add-ops o ~[[%cel src] [%con p.hed p.tel r.ned]])
      [[q.hed q.tel] gen]
    ==
  ::
  ++  split-in
    |=  [nex=next tag=(unit @uvre)]
    ^-  [[need-lazy need-lazy @uwoo] _gen]
    ::  emit an empty basic block
    ::
    =^  o=@uwoo  gen  (emit ~ ~ %hop then.nex)
    =;  [[ned-h=need-lazy ned-t=need-lazy] gen=_gen]
      [[ned-h ned-t o] gen]
    =/  top=@uwoo  o
    =/  laz=need-lazy  laz.nex
    |-  ^-  [[need-lazy need-lazy] _gen]
    =*  split-loop  $
    =^  [sure-h=sure sure-t=sure]  gen
      ?~  tag  (split-sure sure.laz o)
      (split-sure-tag sure.laz o u.tag =(o top))
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [[[sure-h ~ ~] [sure-t ~ ~]] gen]
    =*  fork  ,(list [[@uwoo need-lazy] [@uwoo need-lazy]])
    =^  [fork-h=fork fork-t=fork]  gen
      %^  spin-split  fork.laz  gen
      |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen-acc=_gen]
      ::  (pair of pairs of [@uwoo need-lazy])
      ::
      ^-  [_[. .]:[. .]:*[@uwoo need-lazy] _gen]
      =.  gen  gen-acc
      =^  [laz-y-h=need-lazy laz-y-t=need-lazy]  gen
        split-loop(laz laz.y, o o.y)
      ::
      =^  [laz-n-h=need-lazy laz-n-t=need-lazy]  gen
        split-loop(laz laz.n, o o.n)
      ::
      :_  gen
      :-  [[o.y laz-y-h] [o.n laz-n-h]]
      [[o.y laz-y-t] [o.n laz-n-t]]
    ::
    =*  bond  ,(list [o=@uwoo laz=need-lazy])
    =^  [bond-h=bond bond-t=bond]  gen
      %^  spin-split  bond.laz  gen
      |=  [[o-bond=@uwoo laz-bond=need-lazy] gen-acc=_gen]
      ^-  [_[. .]:*[@uwoo need-lazy] _gen]
      =.  gen  gen-acc
      =^  [laz-h=need-lazy laz-t=need-lazy]  gen
        split-loop(laz laz-bond, o o-bond)
      ::
      [[[o-bond laz-h] [o-bond laz-t]] gen]
    ::
    :_  gen
    :-  (lazy-prune sure-h fork-h bond-h)
    (lazy-prune sure-t fork-t bond-t)
  ::
  ++  add-ops
    ~%  %comp-add-ops  ..ride  ~
    |=  [o=@uwoo ops=(list pole)]
    ^+  gen
    ?:  dropping  gen
    =.  gen  (tst-read ops ~)
    =/  =blob  (~(got by blocks.gen) o)
    =.  body.blob  (weld ops body.blob)
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  emir
    ~%  %comp-emir  ..ride  ~
    |=  [o=@uwoo =blob]
    ^+  gen
    ?:  dropping  gen
    =.  gen  (tst-read body.blob `fin.blob)
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  bomb
    ~%  %comp-bomb  ..ride  ~
    |=  miss=(unit @uwoo)
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %bom miss)
    [[%next *need-lazy ~ o] gen]
  ::
  ++  copy-need-make-ops
    ~%  %comp-copy-need-make-ops  ..ride  ~
    |=  [first=need second=need]
    ^-  [[need (list pole)] _gen]
    ::  One need for two of the same noun: the registers of the need that
    ::  asks for more are the ones to fill, and those of the other are
    ::  moved to from them
    ::
    =/  l=need  first
    =/  r=need  second
    =|  ops=(list pole)
    |-  ^-  [[need (list pole)] _gen]
    ?:  ?=(%none -.l)  [[r ops] gen]
    ?:  ?=(%none -.r)  [[l ops] gen]
    ::  %lax gives way to a need that is sure: it is met with the noun where
    ::  that is wanted, with the parts where the noun is taken apart
    ::
    ?:  ?=(%lax -.r)
      ?.  ?=(%lax -.l)  $(l r, r l)
      =.  ops  [[%mov g.l g.r] [%mov r.l r.r] ops]
      =^  h=[n=need o=(list pole)]  gen  $(l h.l, r h.r)
      =^  t=[n=need o=(list pole)]  gen  $(l t.l, r t.r, ops o.h)
      [[[%lax g.l r.l n.h n.t] o.t] gen]
    ?:  ?=(%lax -.l)
      ?:  ?=(%this -.r)  [[r (weld (lax-whole r.r l) ops)] gen]
      ?:  ?=(%both -.r)  [[r (weld (lax-whole r.r l) ops)] gen]
      =.  ops  (weld (lax-parts l) ops)
      =^  h=[n=need o=(list pole)]  gen  $(l h.l, r p.r)
      =^  t=[n=need o=(list pole)]  gen  $(l t.l, r q.r, ops o.h)
      [[[n.h n.t] o.t] gen]
    ?:  ?=(%this -.l)
      ?:  ?=(%this -.r)
        [[l [[%mov r.l r.r] ops]] gen]
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x r] gen]))
      [[rr [[%mov r.rr r.l] ops]] gen]
    ?:  ?=(%this -.r)
      =^  ll=$>(%both need)  gen
        ?@(-.l [l gen] =^(x gen re [[%both x l] gen]))
      [[ll [[%mov r.ll r.r] ops]] gen]
    ?:  ?=(%both -.l)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x r] gen]))
      =.  ops  [[%mov r.rr r.l] ops]
      =^  h=[n=need o=(list pole)]  gen  $(l h.l, r h.rr)
      =^  t=[n=need o=(list pole)]  gen  $(l t.l, r t.rr, ops o.h)
      [[[%both r.rr n.h n.t] o.t] gen]
    ?^  -.r
      =^  h=[n=need o=(list pole)]  gen  $(l p.l, r p.r)
      =^  t=[n=need o=(list pole)]  gen  $(l q.l, r q.r, ops o.h)
      [[(cons-need n.h n.t) o.t] gen]
    ::  first computation does not have a cell check for r.r,
    ::  so r.r will need to be checked upstream
    ::
    =^  h=[n=need o=(list pole)]  gen  $(l p.l, r h.r)
    =^  t=[n=need o=(list pole)]  gen  $(l q.l, r t.r, ops o.h)
    [[[%both r.r n.h n.t] o.t] gen]
  ++  coerce-soft
    ~%  %comp-coerce-soft  ..ride  ~
    |=  [need-pessimized=need-ordered nex=next-resolved]
    ^-  [next-resolved _gen]
    =|  req=(list [r=@uvre ned=need])
    =^  [ned=need req=_req]  gen
      |-  ^-  [[need _req] _gen]
      ?-    -.need-pessimized
          %lax   ~|(%lax-in-a-shape !!)
          %none
        ?>  ?=(%none -.ned.nex)
        [[[%none ~] req] gen]
      ::
          %this
        ?:  ?=(%this -.ned.nex)  [[ned.nex req] gen]
        =^  r  gen  re
        :_  gen
        :-  [%this r]
        ?:(?=(%none -.ned.nex) req [[r ned.nex] req])
      ::
          ^
        =/  [h=need t=need]
          ?:  ?=(%none -.ned.nex)  [ned.nex ned.nex]
          ?@  -.ned.nex  !!
          ned.nex
        ::
        =^  [hed=need req=_req]  gen
          $(need-pessimized -.need-pessimized, ned.nex h, req req)
        ::
        =^  [tel=need req=_req]  gen
          $(need-pessimized +.need-pessimized, ned.nex t, req req)
        ::
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[[hed tel] req] gen]
      ::
          %both
        =^  [r=@uvre h=need t=need]  gen
          ?-  -.ned.nex
            %lax   ~|(%lax-in-a-shape !!)
            %none  =^(r gen re [[r ned.nex ned.nex] gen])
            %this  [[r.ned.nex [. .]:[%none ~]] gen]
            ^      =^(r gen re [[r ned.nex] gen])
            %both  [[r.ned.nex h.ned.nex t.ned.nex] gen]
          ==
        ::
        =^  [hed=need req=_req]  gen
          $(need-pessimized h.need-pessimized, ned.nex h, req req)
        ::
        =^  [tel=need req=_req]  gen
          $(need-pessimized t.need-pessimized, ned.nex t, req req)
        ::
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[[%both r hed tel] req] gen]
      ==
    ::
    ?:  |(?=(~ req) dropping)  [[%next [[ned ~] ~ ~] [~ then.nex]] gen]
    =/  rin=(unit ring)  (~(get by call.cole.jets.long-ska) b)
    =^  [kon=(list pole) rub=@uvre]  gen  (soft-cons ned ~ less.b)
    =^  fail=@uwoo  gen  (soft-back kon b rin rub)
    =^  first=@uwoo  gen
      =/  req=(list [r=@uvre ned=need])  req
      =/  nxt=@uwoo  then.nex
      |-  ^-  [@uwoo _gen]
      ?~  req  [nxt gen]
      =^  n  gen  (mono-try-call ned.i.req nxt [r.i.req fail])
      $(req t.req, nxt n)
    ::
    [[%next [[ned ~] ~ ~] [~ first]] gen]
  ::
  ++  need-ord-alloc-regs
    ~%  %comp-need-ord-alloc-regs  ..ride  ~
    |=  ord=need-ordered
    ^-  [need _gen]
    ?-    -.ord
        %none  [[%none ~] gen]
    ::
        %this
      =^  r  gen  re
      [[%this r] gen]
    ::
        ^
      =^  hed  gen  $(ord -.ord)
      =^  tel  gen  $(ord +.ord)
      ?<  &(?=(%none -.hed) ?=(%none -.tel))
      [[hed tel] gen]
    ::
        %both
      =^  r  gen  re
      =^  hed  gen  $(ord h.ord)
      =^  tel  gen  $(ord t.ord)
      ?<  &(?=(%none -.hed) ?=(%none -.tel))
      [[%both r hed tel] gen]
    ::
        %lax
      =^  g  gen  re
      =^  r  gen  re
      =^  hed  gen  $(ord h.ord)
      =^  tel  gen  $(ord t.ord)
      [[%lax g r hed tel] gen]
    ==
  ::  With the top level need finally known, emit noun splitting code into
  ::  appropriate BBs
  ::
  ++  coerce-lazy
    ~%  %comp-coerce-lazy  ..ride  ~
    |=  [ned=need o=@uwoo laz=need-lazy less=cape]
    ^+  gen
    =*  coerce-lazy  .
    =.  gen
      =^  [ned-target=need lop=(list pole)]  gen
        %-  sure-require-look
        %=    sure.laz
            lok
          %-  ~(rep in lok.sure.laz)
          |=  [axe=@ acc=(set @)]
          ?:  (axe-in-less-cape axe less)  acc
          ?:  (axe-in-need axe ned)  acc
          (~(put in acc) axe)
        ==
      ::
      =.  gen  (add-ops o lop)
      |-  ^+  gen
      =*  sure-loop  $
      ?-    -.ned
          %lax   ~|(%lax-in-a-shape !!)
          %none
        ?>  ?=(%none -.ned-target)
        gen
      ::
          %this
        ?:  (~(has by soft.gen) o)  (soft-ask o r.ned ned-target)
        =^  ops  gen  (kern-need r.ned ned-target)
        (add-ops o ops)
      ::
          ^
        ?:  ?=(%none -.ned-target)  gen
        ::  the parts are what there is
        ::
        ?:  ?=(%lax -.ned-target)
          =.  gen  (add-ops o (lax-parts ned-target))
          =.  gen  sure-loop(ned -.ned, ned-target h.ned-target)
          sure-loop(ned +.ned, ned-target t.ned-target)
        ?@  -.ned-target  !!
        =.  gen  sure-loop(ned -.ned, ned-target -.ned-target)
        sure-loop(ned +.ned, ned-target +.ned-target)
      ::
          %both
        ?-    -.ned-target
            %none  gen
            %this
          ?<  =(r.ned r.ned-target)
          (add-ops o [%mov r.ned r.ned-target]~)
        ::
            %lax
          (add-ops o (lax-whole r.ned ned-target))
        ::
            ^
          =.  gen  sure-loop(ned h.ned, ned-target -.ned-target)
          sure-loop(ned t.ned, ned-target +.ned-target)
        ::
            %both
          ?<  =(r.ned r.ned-target)
          =.  gen  (add-ops o [%mov r.ned r.ned-target]~)
          =.  gen  sure-loop(ned h.ned, ned-target h.ned-target)
          sure-loop(ned t.ned, ned-target t.ned-target)
        ==
      ==
    ::
    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  gen
    =.  gen
      %+  roll  bond.laz
      |=  [[o=@uwoo laz=need-lazy] gen-acc=_gen]
      =.  gen  gen-acc
      (coerce-lazy ned o laz less)
    ::
    %+  roll  fork.laz
    |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen-acc=_gen]
    =.  gen  gen-acc
    =.  gen  (coerce-lazy ned o.y laz.y less)
    (coerce-lazy ned o.n laz.n less)
  ++  collapse-shape
    ~%  %comp-collapse-shape  ..ride  ~
    |=  [nex=next less=lore]
    ^-  [[need need-lazy @uwoo] _gen]
    ?>  =(~ args.then.nex)
    =^  ned-final=need  gen  (need-ord-alloc-regs (shape-collapse laz.nex less))
    [[ned-final laz.nex there.then.nex] gen]
  ::
  ::  Renumber the registers so that the input registers are 0-N, set the
  ::  starting block index to 0w0
  ::
  ++  to-straight
    ~%  %comp-to-straight  ..ride  ~
    |=  nex=next-resolved
    ^-  straight
    =/  blocks=(map @uwoo blob)  blocks.gen
    ::  Proxy registers (see $cond) are dominated by their definitions at this
    ::  point, so they are replaced by their definitions while renumbering
    ::
    =/  unproxy  |=(r=@uvre ?~(e=(~(get by cond.gen) r) r def.u.e))
    =/  proxies=?  !=(~ cond.gen)
    ::  +collapse-shape allocates the input registers last, one after the
    ::  other, in the order +rewrite-input numbers them.  When they are such
    ::  a run [r0, r0+n), the inputs go to 0..n-1, the registers before them
    ::  move up by n and those after them stay: a pure renaming, no map and
    ::  no compaction (the compiler uses most registers it allocates).  A
    ::  coerced subject is not such a run and is renumbered through the map.
    ::
    =/  ins=(list @uvre)  (flatten-need ned.nex)
    =/  r0=@uvre  ?~(ins 0v0 i.ins)
    =/  n-in=@ud  (lent ins)
    =/  run=?
      =/  i=@ud  0
      |-  ^-  ?
      ?~  ins  &
      ?.  =(i.ins (add r0 i))  |
      $(ins t.ins, i +(i))
    =/  ren
      |=  r=@uvre
      ^-  @uvre
      ?:  (lth r r0)  `@uvre``@`(add r n-in)
      ?:  (lth r (add r0 n-in))  `@uvre``@`(sub r r0)
      r
    =/  start=blob  (~(got by blocks) then.nex)
    =.  blocks  (~(del by blocks) then.nex)
    =.  blocks  (~(put by blocks) `@`0 start)
    =|  gen=[re-gen=@uvre m=(map @uvre @uvre)]
    |^  ^-  straight
    =^  input=need-ordered  gen  (rewrite-input ned.nex)
    ?:  &(run !proxies)
      ::  a pure renaming: the parameters and the body of each kept block
      ::  through +map-regs, its terminator by +chase-fin
      ::
      =/  rename  (map-regs ren)
      :+  input  (count-args input)
      %-  ~(rep by blocks)
      |=  [[k=@uwoo b=blob] new=(map @uwoo blob)]
      ?:  &(!=(0w0 k) (bypassable & b))  new
      =/  b1=blob  (rename b(fin [%bom ~]))
      (~(put by new) k b1(fin (chase-fin fin.b)))
    :+  input  (count-args input)
    =<  new
    ^-  [new=(map @uwoo blob) *]
    %-  ~(rep by blocks)
    |=  [[k=@uwoo b=blob] new=(map @uwoo blob) gen-acc=_gen]
    =.  gen  gen-acc
    ::  Empty blocks that every jump bypasses are dropped, see +chase
    ::
    ?:  &(!=(0w0 k) (bypassable & b))  [new gen]
    =;  [b1=blob gen1=_gen]
      :_  gen1
      (~(put by new) k b1)
    ::
    =^  par1   gen  (rewrite-par par.b)
    =^  body1  gen  (rewrite-body body.b)
    =^  fin1   gen  (rewrite-fin fin.b)
    :_  gen
    [par1 body1 fin1]
    ::  Most blocks the compiler emits are empty hops: +copy, +split, +into,
    ::  +kerf, +mede and friends each make one.  A jump to such a block may go
    ::  to the block's target directly, unless the jump is a branch and the
    ::  hop passes arguments: then the edge could be critical and there would
    ::  be no block to move the arguments in.  Same rules as
    ::  +remove-empty-middle, but here, before the IR gets to the optimizer,
    ::  so that the passes work on a CFG that is many times smaller.
    ::
    ++  bypassable
      |=  [branch=? b=blob]
      ^-  ?
      ?&  ?=(~ par.b)
          ?=(~ body.b)
          ?=(%hop -.fin.b)
          |(!branch ?=(~ args.t.fin.b))
      ==
    ::
    ++  chase
      |=  [branch=? j=jmp]
      ^-  jmp
      |-  ^-  jmp
      =/  b=blob  (~(got by blocks) there.j)
      ?.  ?=(%hop -.fin.b)  j
      ?.  (bypassable branch b)  j
      ?>  ?=(~ args.j)
      $(j t.fin.b)
    ::
    ::  the terminator: jumps chased past the bypassed blocks, then renamed
    ::
    ++  chase-fin
      |=  fin=termin
      ^-  termin
      =/  rj  |=(j=jmp j(args (turn args.j (lift ren))))
      ?-  -.fin
        %clq  fin(s (ren s.fin), z (rj (chase & z.fin)), o (rj (chase & o.fin)))
        %eqq
          %=  fin
            l  (ren l.fin)
            r  (ren r.fin)
            z  (rj (chase & z.fin))
            o  (rj (chase & o.fin))
          ==
        %brn  fin(s (ren s.fin), z (rj (chase & z.fin)), o (rj (chase & o.fin)))
        %brz  fin(s (ren s.fin), z (rj (chase & z.fin)), o (rj (chase & o.fin)))
        %hop  fin(t (rj (chase | t.fin)))
        %jmp  fin(v (turn v.fin ren))
        %jmf  fin(v (turn v.fin ren))
        %jsp  fin(s (ren s.fin))
        %jsf  fin(s (ren s.fin))
        %don  fin(s (ren s.fin))
        %dox  fin(v [(ren i.v.fin) (turn t.v.fin ren)])
        %bom  ?~(o.fin fin fin(o `there:(chase & [~ u.o.fin])))
      ==
    ::
    ++  rer
      |=  r=@uvre
      ^-  [@uvre _gen]
      =?  r  proxies  (unproxy r)
      ?:  run  [(ren r) gen]
      ?^  r1=(~(get by m.gen) r)  [u.r1 gen]
      =^  r1  re-gen.gen  [re-gen.gen +(re-gen.gen)]
      =.  m.gen  (~(put by m.gen) r r1)
      [r1 gen]
    ::
    ++  rewrite-input
      |=  ned=need
      ^-  [need-ordered _gen]
      ?>  =(0 re-gen.gen)
      |-  ^-  [need-ordered _gen]
      ?-    -.ned
          %none
        [[%none ~] gen]
      ::
          %lax  ~|(%lax-in-a-shape !!)
          %this
        =.  gen  +:(rer r.ned)
        [[%this ~] gen]
      ::
          ^
        =^  l  gen  $(ned -.ned)
        =^  r  gen  $(ned +.ned)
        [[l r] gen]
      ::
          %both
        =.  gen  +:(rer r.ned)
        =^  h  gen  $(ned h.ned)
        =^  t  gen  $(ned t.ned)
        [[%both h t] gen]
      ==
    ::
    ++  rewrite-par
      |=  par=(list @uvre)
      ^-  [(list @uvre) _gen]
      ?:  =(~ par)  [~ gen]
      %^  spin  par  gen
      |=  [r=@uvre =_gen]
      (rer(gen gen) r)
    ::
    ++  rewrite-body
      |=  bod=(list pole)
      ^-  [(list pole) _gen]
      ?:  =(~ bod)  [~ gen]
      %^  spin  bod  gen
      |=  [op=pole =_gen]
      (rewrite-op(gen gen) op)
    ::
    ++  rewrite-op
      |=  op=pole
      ^-  [pole _gen]
      ?-    -.op
          %imm
        =^  d1  gen  (rer d.op)
        [op(d d1) gen]
      ::
          %mov
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %inc
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %con
        =^  h1  gen  (rer h.op)
        =^  t1  gen  (rer t.op)
        =^  d1  gen  (rer d.op)
        [op(h h1, t t1, d d1) gen]
      ::
          %hed
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %tal
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %cel
        =^  p1  gen  (rer p.op)
        [op(p p1) gen]
      ::
          %lob
        =^  p1  gen  (rer p.op)
        [op(p p1) gen]
      ::
          %equ
        =^  l1  gen  (rer l.op)
        =^  r1  gen  (rer r.op)
        [op(l l1, r r1) gen]
      ::
          %hsp  [op gen]
          %hse  [op gen]
      ::
          %hdp
        =^  p1  gen  (rer p.op)
        [op(p p1) gen]
      ::
          %hde
        =^  p1  gen  (rer p.op)
        [op(p p1) gen]
      ::
          %hmp
        =^  v1  gen  (rewrite-par v.op)
        [op(v v1) gen]
      ::
          %hme
        =^  v1  gen  (rewrite-par v.op)
        [op(v v1) gen]
      ::
          %hcp  [op gen]
          %hce  [op gen]
      ::
          %spy
        =^  e1  gen  (rer e.op)
        =^  p1  gen  (rer p.op)
        =^  d1  gen  (rer d.op)
        [op(e e1, p p1, d d1) gen]
      ::
          %nok
        =^  u1  gen  (rer u.op)
        =^  f1  gen  (rer f.op)
        =^  d1  gen  (rer d.op)
        [op(u u1, f f1, d d1) gen]
      ::
          %cal
        =^  v1  gen  (rewrite-par v.op)
        =^  d1  gen  (rer d.op)
        [op(v v1, d d1) gen]
      ::
          %caf
        =^  v1  gen  (rewrite-par v.op)
        =^  d1  gen  (rer d.op)
        [op(v v1, d d1) gen]
      ::
          %cam
        =^  v1  gen  (rewrite-par v.op)
        =^  d1  gen  (rer d.op)
        [op(v v1, d d1) gen]
      ::
          %csl
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %csf
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %csm
        =^  s1  gen  (rer s.op)
        =^  d1  gen  (rer d.op)
        [op(s s1, d d1) gen]
      ::
          %rtl
        =^  d1  gen  (rer d.op)
        [op(d d1) gen]
      ==
    ::
    ++  rewrite-fin
      |=  fin=termin
      ^-  [termin _gen]
      ?-    -.fin
          %clq
        =^  s1  gen  (rer s.fin)
        =^  z1  gen  (rewrite-jump z.fin)
        =^  o1  gen  (rewrite-jump o.fin)
        [fin(s s1, z z1, o o1) gen]
      ::
          %eqq
        =^  l1  gen  (rer l.fin)
        =^  r1  gen  (rer r.fin)
        =^  z1  gen  (rewrite-jump z.fin)
        =^  o1  gen  (rewrite-jump o.fin)
        [fin(l l1, r r1, z z1, o o1) gen]
      ::
          %brn
        =^  s1  gen  (rer s.fin)
        =^  z1  gen  (rewrite-jump z.fin)
        =^  o1  gen  (rewrite-jump o.fin)
        [fin(s s1, z z1, o o1) gen]
      ::
          %brz
        =^  s1  gen  (rer s.fin)
        =^  z1  gen  (rewrite-jump z.fin)
        =^  o1  gen  (rewrite-jump o.fin)
        [fin(s s1, z z1, o o1) gen]
      ::
          %hop
        =^  t1  gen  (rewrite-hop t.fin)
        [fin(t t1) gen]
      ::
          %jmp
        =^  v1  gen  (rewrite-par v.fin)
        [fin(v v1) gen]
      ::
          %jmf
        =^  v1  gen  (rewrite-par v.fin)
        [fin(v v1) gen]
      ::
          %jsp
        =^  s1  gen  (rer s.fin)
        [fin(s s1) gen]
      ::
          %jsf
        =^  s1  gen  (rer s.fin)
        [fin(s s1) gen]
      ::
          %don
        =^  s1  gen  (rer s.fin)
        [fin(s s1) gen]
      ::
          %dox
        =^  v1  gen  (rewrite-par v.fin)
        ?>  ?=(^ v1)
        [fin(v v1) gen]
      ::
          %bom
        ?~  o.fin  [fin gen]
        [fin(o `there:(chase & [~ u.o.fin])) gen]
      ==
    ::  branch edge
    ::
    ++  rewrite-jump
      |=  j=jmp
      ^-  [jmp _gen]
      (rewrite-args (chase & j))
    ::  hop edge
    ::
    ++  rewrite-hop
      |=  j=jmp
      ^-  [jmp _gen]
      (rewrite-args (chase | j))
    ::
    ++  rewrite-args
      |=  j=jmp
      ^-  [jmp _gen]
      ?:  =(~ args.j)  [j gen]
      =^  args1  gen
        %^  spin  args.j  gen
        |=  [a=(unit @uvre) gen-init=_gen]
        ^-  [(unit @uvre) _gen]
        =.  gen  gen-init
        ?~  a  [~ gen]
        =^  r  gen  (rer u.a)
        [`r gen]
      ::
      [j(args args1) gen]
    --
  ::  XX sloppy codegen, always both head and tail
  ::
  ++  mono-try-call
    ~%  %comp-mono-try-call  ..ride  ~
    |=  [ned=need opt=@uwoo pes=[sub=@uvre o=@uwoo]]
    ^-  [@uwoo _gen]
    =/  r=@uvre  sub.pes
    =/  fail=@uwoo  o.pes
    =/  o=@uwoo  opt
    |-  ^-  [@uwoo _gen]
    ?-    -.ned
        %none
      [o gen]
    ::
        %lax   ~|(%lax-in-a-shape !!)
        %this
      ?<  =(r r.ned)
      (emit ~ [%mov r r.ned]~ %hop ~ o)
    ::
        ^
      =^  r-t  gen  re
      =^  r-h  gen  re
      =^  o-t=@uwoo  gen  $(ned +.ned, r r-t)
      =^  o-h=@uwoo  gen  $(ned -.ned, o o-t, r r-h)
      =^  o-split  gen  (emit ~ ~[[%hed r r-h] [%tal r r-t]] %hop ~ o-h)
      (emit ~ ~ [%clq r ~^o-split ~^fail])
    ::
        %both
      =^  r-t  gen  re
      =^  r-h  gen  re
      =^  o-t=@uwoo  gen  $(ned t.ned, r r-t)
      =^  o-h=@uwoo  gen  $(ned h.ned, o o-t, r r-h)
      =^  o-split  gen
        ?<  =(r r.ned)
        (emit ~ ~[[%hed r r-h] [%tal r r-t] [%mov r r.ned]] %hop ~ o-h)
      ::
      (emit ~ ~ [%clq r ~^o-split ~^fail])
    ==
  ::
  ++  sure-require-look
    ~%  %comp-sure-require-look  ..ride  ~
    |=  sur=sure
    ^-  [[need (list pole)] _gen]
    ::  .lop: the ops for the %lax needs that a look goes into: such a noun
    ::  is fetched into, so it is taken whole, and its %lax need is met from
    ::  that
    ::
    %-  ~(rep in lok.sur)
    |=  [axe=@ [ned=_ned.sur lop=(list pole)] gen-init=_gen]
    =.  gen  gen-init
    ?:  =(1 axe)  [[ned lop] gen]
    ?<  =(0 axe)
    |-  ^-  [[need (list pole)] _gen]
    ?:  =(1 axe)
      ?.  ?=(%none -.ned)  [[ned lop] gen]
      =^  r  gen  re
      [[[%this r] lop] gen]
    ?:  ?=(%lax -.ned)
      =^  w  gen  re
      $(ned [%this w], lop (weld (lax-whole w ned) lop))
    =/  [here=(unit @uvre) h=need t=need]
      ?-  -.ned
        %none  [~ [. .]:[%none ~]]
        %this  [`r.ned [. .]:[%none ~]]
        ^      [~ ned]
        %both  [`r.ned [h t]:ned]
      ==
    ::
    =^  kid=[n=need l=(list pole)]  gen
      ?-  (cap axe)
        %2  $(ned h, axe (mas axe))
        %3  $(ned t, axe (mas axe))
      ==
    ::
    =.  lop  l.kid
    =/  [h-required=need t-required=need]
      ?-  (cap axe)
        %2  [n.kid t]
        %3  [h n.kid]
      ==
    ::
    =/  x  (cons-need h-required t-required)
    ?~  here  [[x lop] gen]
    ?@  -.x  [[[%this u.here] lop] gen]
    [[[%both u.here x] lop] gen]
  ::
  --
::
++  count-args
  |=  args=need-ordered
  ^-  @ud
  ?-  -.args
    %none  0
    %this  1
    ^      (add $(args -.args) $(args +.args))
    %both  +((add $(args h.args) $(args t.args)))
    %lax   ~|(%lax-in-a-shape !!)
  ==
::
::  a cape that knows no noun: cells of unknown parts at most (+cons:so)
::
++  bare-cape
  |=  c=cape
  ^-  ?
  ?@  c  !c
  &($(c -.c) $(c +.c))
::
++  hed-lore  |=(l=lore `lore`[(hed:ca les.l) (hed:ca hel.l)])
++  tel-lore  |=(l=lore `lore`[(tel:ca les.l) (tel:ca hel.l)])
::
++  msg-need-ord
  ~%  %msg-need-ord  ..ride  ~
  |=  [a=need-ordered b=need-ordered less=lore]
  ^-  need-ordered
  =*  msg  .
  ?:  =(a b)  a
  ~+
  ::  %lax asks for nothing by itself: two of them meet part by part, and
  ::  one gives way to what the other branch needs for sure
  ::
  ?:  |(?=(%lax -.a) ?=(%lax -.b))
    ?:  ?=(%lax -.a)
      ?:  ?=(%lax -.b)
        [%lax (msg h.a h.b (hed-lore less)) (msg t.a t.b (tel-lore less))]
      (uni-need-ord (msg none+~ b less) a)
    (uni-need-ord (msg none+~ a less) b)
  ::  none are cells
  ::
  ?:  ?&  |(?=(%this -.a) ?=(%none -.a))
          |(?=(%this -.b) ?=(%none -.b))
      ==
    this+~
  ::  one is maybe atom, can't refine with `less`
  ::
  ?:  ?&  ?=(@ les.less)
          ?|  ?=(%this -.a)
              ?=(%none -.a)
              ?=(%this -.b)
              ?=(%none -.b)
      ==  ==
    this+~
  ::  one is still this/none: `less` is a cell
  ::
  ?:  ?|  ?=(%this -.a)
          ?=(%none -.a)
          ?=(%this -.b)
          ?=(%none -.b)
      ==
    =/  [single=need-ordered double=need-ordered]
      ?:  |(?=(%this -.a) ?=(%none -.a))  [a b]
      [b a]
    ::
    =/  h-double
      ?:  ?=(%both -.double)  h.double
      ?>  ?=(^ -.double)
      -.double
    ::
    =/  t-double
      ?:  ?=(%both -.double)  t.double
      ?>  ?=(^ -.double)
      +.double
    ::
    ::  a noun that only its callers' conses make a cell (the bell knows
    ::  no part of it), used whole on the other path: whole, as one that is
    ::  not known to be a cell.  With its parts too (%both) a loop that
    ::  changed one part would cons the noun anew every turn
    ::
    ?:  &(?=(%this -.single) (bare-cape les.less))  this+~
    =/  l  (msg none+~ h-double (hed-lore less))
    =/  r  (msg none+~ t-double (tel-lore less))
    =/  res=need-ordered
      ?:  |(?=(%this -.single) ?=(%both -.double))  [%both l r]
      %-  cons-need  ::  XX
      [l r]
    ::  Only one branch takes the noun apart.  Where every call site holds
    ::  its parts (+heft), passing them costs a move each and the noun whole
    ::  would cost every caller a cons: it is split.  Where the callers hold
    ::  it whole, a split would be paid on entry by every path, in fetches
    ::  and moves for parts that path never reads (the rule trees of the
    ::  parsers): it is passed whole, as structs are by reference, and the
    ::  branch that reads it splits its one register.
    ::
    ?:  |(?=(^ hel.less) ?=(%none -.res))  res
    this+~
  ::
  ?:  ?=(%both -.a)
    ?:  ?=(%both -.b)
      [%both (msg h.a h.b (hed-lore less)) (msg t.a t.b (tel-lore less))]
    [%both (msg h.a p.b (hed-lore less)) (msg t.a q.b (tel-lore less))]
  ?:  ?=(%both -.b)
    [%both (msg p.a h.b (hed-lore less)) (msg q.a t.b (tel-lore less))]
  %-  cons-need  ::  XX
  [(msg p.a p.b (hed-lore less)) (msg q.a q.b (tel-lore less))]
::
++  need-to-ordered
  ~%  %need-to-ordered  ..ride  ~
  |=  ned=need
  ^-  need-ordered
  ~+
  =*  this  .
  ?-  -.ned
    %none  [%none ~]
    %this  [%this ~]
    ^      [(this -.ned) (this +.ned)]
    %both  [%both (this h.ned) (this t.ned)]
    %lax   [%lax (this h.ned) (this t.ned)]
  ==
::
++  cons-need
  |*  [a=?([%none ~] ^) b=?([%none ~] ^)]
  ?:  &(?=(%none -.a) ?=(%none -.b))  [%none ~]
  [a b]
::
++  uni-need-ord
  ~%  %uni-need-ord  ..ride  ~
  |=  [a=need-ordered b=need-ordered]
  ^-  need-ordered
  ?:  =(a b)  a
  ?:  ?=(%none -.a)  b
  ?:  ?=(%none -.b)  a
  ::  %lax gives way to a need that is sure: the noun whole where it is
  ::  wanted whole, the parts, with what the %lax wants of them, where it is
  ::  taken apart (as +copy-need-make-ops does with the registers)
  ::
  ?:  ?=(%lax -.b)
    ?:  ?=(%lax -.a)
      ~+
      [%lax $(a h.a, b h.b) $(a t.a, b t.b)]
    $(a b, b a)
  ?:  ?=(%lax -.a)
    ?:  ?=(?(%this %both) -.b)  b
    ?>  ?=(^ -.b)
    ~+
    (cons-need $(a h.a, b -.b) $(a t.a, b +.b))
  ?:  ?=(%this -.a)
    ?:  ?=(%both -.b)  b
    ?>  ?=(^ -.b)
    [%both b]
  ?:  ?=(%this -.b)
    ?:  ?=(%both -.a)  a
    ?>  ?=(^ -.a)
    [%both a]
  ?:  &(?=(^ -.a) ?=(^ -.b))
    ~+
    (cons-need $(a -.a, b -.b) $(a +.a, b +.b))
  ?>  |(?=(%both -.a) ?=(%both -.b))
  =/  [h-a=need-ordered t-a=need-ordered]
    ?:  ?=(%both -.a)  [h t]:a
    ?>  ?=(^ -.a)
    a
  ::
  =/  [h-b=need-ordered t-b=need-ordered]
    ?:  ?=(%both -.b)  [h t]:b
    ?>  ?=(^ -.b)
    b
  ::
  =/  x=need-ordered
    ~+
    (cons-need $(a h-a, b h-b) $(a t-a, b t-b))
  ::
  ?:  |(?=(%none -.x) ?=(%this -.x))  [%this ~]
  :-  %both
  ?:  ?=(^ -.x)  x
  [h t]:x
::  Given a final need-lazy, produce the shape of the input subject.
::
::  Some facts first, then the descripion of the algorithm:
::
::  Fork collapsing is order-sensitive. If one fork used +2 in both branches,
::  and the other used +2 only in one branch, the desired result should contain
::  +2. But if we finalized the second fork first and simply unified the results
::  of all forks collapsed so far, we would have either lost +2 or kept both the
::  root noun and +2 in %both. So we have to have a fixed point loop to refine
::  the final shape iteratively.
::
::  For the fixed point loop to converge the shape needs to grow monotonically.
::  However, if we captured the root noun once, like in the example above, we
::  want to be able to subtract it once we learn that the root is not needed.
::  For this reason we will keep track of two shapes:
::    orig: this is the shape that we want to return. It contains sure.laz on
::          the current level of the lazy tree, plus all the collapsed stuff
::    fix: the shape we accumulate in the fixed point loop. It contains all the
::         axes that were available to us, including in the prior iterations.
::
+$  sure-ordered  [ned=need-ordered lok=(set @)]
::  $need-lazy without registers or blocks: what +run-shape computes.  Fork and
::  bond entries carry identifiers so that +laze-copy can merge them.
::
+$  laze
  $+  laze
  $;  |-
  $:  sure=sure-ordered
      fork=(list [y=[o=@uxid laz=$] n=[o=@uxid laz=$]])
      bond=(list [o=@uxid laz=$])
  ==
::  What a pass over a member of an SCC computes: what it may read
::  (%may), its shape (%must), its code (%done)
::
+$  scc-mode  ?(%may %must %done)
::  What the shape collapse knows of a subject: the cape of its bell, and
::  what every call site holds of it (+heft)
::
+$  lore  [les=cape hel=cape]
::  How a formula holds its product (+lay-of:comp): %w, whole in one
::  register; a cell, where it makes it of parts; %p, as its subject holds
::  the part that it hands on; %x, it has none (a crash)
::
+$  lay  $@(?(%w %p %x) [h=lay t=lay])
::
++  lay-hed  |=(a=lay `lay`?@(a a h.a))
++  lay-tel  |=(a=lay `lay`?@(a a t.a))
++  lay-slot
  |=  [a=lay axe=@]
  ^-  lay
  ?:  =(1 axe)  a
  ?@  a  a
  ?-  (cap axe)
    %2  $(a h.a, axe (mas axe))
    %3  $(a t.a, axe (mas axe))
  ==
::
++  lay-edit
  |=  [rec=lay axe=@ don=lay]
  ^-  lay
  ?:  =(1 axe)  don
  ?:  ?=(%x rec)  %x
  ?-  (cap axe)
    %2  [$(rec (lay-hed rec), axe (mas axe)) (lay-tel rec)]
    %3  [(lay-hed rec) $(rec (lay-tel rec), axe (mas axe))]
  ==
::  the product of a fork: of parts where both branches make it of parts,
::  whole where both have it whole
::
++  lay-join
  |=  [a=lay b=lay]
  ^-  lay
  ?:  ?=(%x a)  b
  ?:  ?=(%x b)  a
  ?:  &(?=(^ a) ?=(^ b))  [$(a h.a, b h.b) $(a t.a, b t.b)]
  ?:  &(?=(%w a) ?=(%w b))  %w
  %p
::  +look-ord: a shape with the looks of its block: a noun that is looked
::  into is fetched into
::
++  look-ord
  |=  sur=sure-ordered
  ^-  need-ordered
  %-  ~(rep in lok.sur)
  |=  [axe=@ new=_ned.sur]
  ?:  =(1 axe)  new
  |-  ^-  need-ordered
  ?:  =(1 axe)
    ?.  ?=(%none -.new)  new
    [%this ~]
  =/  [h=need-ordered t=need-ordered]
    ?-  -.new
      ?(%none %this %lax)  [. .]:[%none ~]
      ^                    new
      %both                [h t]:new
    ==
  ::
  =/  [h-new=need-ordered t-new=need-ordered]
    ?-  (cap axe)
      %2  [$(axe (mas axe), new h) t]
      %3  [h $(axe (mas axe), new t)]
    ==
  ::
  =/  x  (cons-need h-new t-new)
  ?:  ?=(?(%none ^) -.new)  x
  ?@  -.x  [%this ~]
  [%both x]
::  +laze-want: what the blocks of a lazy need may want of the noun: their
::  needs united, with their looks
::
++  laze-want
  |=  laz=laze
  ^-  need-ordered
  =/  acc=need-ordered  (look-ord sure.laz)
  =.  acc
    %+  roll  fork.laz
    |=  [e=laze-fork acc=_acc]
    (uni-need-ord (uni-need-ord acc ^$(laz laz.y.e)) ^$(laz laz.n.e))
  ::
  %+  roll  bond.laz
  |=  [e=laze-bond acc=_acc]
  (uni-need-ord acc ^$(laz laz.e))
::  the same for a need with registers
::
++  lazy-want
  |=  laz=need-lazy
  ^-  need-ordered
  =/  acc=need-ordered
    (look-ord (need-to-ordered ned.sure.laz) lok.sure.laz)
  ::
  =.  acc
    %+  roll  fork.laz
    |=  [e=lazy-fork acc=_acc]
    (uni-need-ord (uni-need-ord acc ^$(laz laz.y.e)) ^$(laz laz.n.e))
  ::
  %+  roll  bond.laz
  |=  [e=lazy-bond acc=_acc]
  (uni-need-ord acc ^$(laz laz.e))
::  +lax-ord: the need that the lazy blocks past a fork have of its product
::  (+lerf:comp), from what they may want of it (.s) and how the branches
::  hold it.  A part that both branches have whole is asked for whole; one
::  that both make of parts, in parts; any other is %lax, whichever each
::  branch has.  Where a block wants a noun whole that a branch makes of
::  parts, the parts are asked for, and the block conses them if it runs.
::
++  lax-ord
  ~%  %lax-ord  ..ride  ~
  |=  [s=need-ordered a=lay b=lay]
  ^-  need-ordered
  ?:  ?=(%none -.s)  s
  =?  a  ?=(%x a)  b
  =?  b  ?=(%x b)  a
  ?:  ?=(%x a)  [%this ~]
  ?:  &(?=(%w a) ?=(%w b))  [%this ~]
  =/  whole=?  ?=(?(%this %both) -.s)
  =/  sh=need-ordered
    ?.  whole  (hed-need-ord s)
    (uni-need-ord (hed-need-ord s) [%this ~])
  ::
  =/  st=need-ordered
    ?.  whole  (tel-need-ord s)
    (uni-need-ord (tel-need-ord s) [%this ~])
  ::
  ?:  &(?=(^ a) ?=(^ b))
    =/  x  (cons-need $(s sh, a h.a, b h.b) $(s st, a t.a, b t.b))
    ?:(?=(%none -.x) [%this ~] x)
  ?:  &(?=(%this -.s) ?=(@ a) ?=(@ b))  [%this ~]
  :+  %lax
    $(s sh, a (lay-hed a), b (lay-hed b))
  $(s st, a (lay-tel a), b (lay-tel b))
::  +movable: a need .t of a noun is met from a need .l of it that was
::  met before by moves alone: nothing is fetched, nothing is consed
::
++  movable
  |=  [l=need-ordered t=need-ordered]
  ^-  ?
  ?-    -.t
      %none  &
      %this  ?=(%this -.l)
      %both  |
      ^      &(?=(^ -.l) $(l -.l, t -.t) $(l +.l, t +.t))
      %lax
    ?+  -.l  |
      %this  &
      ^      &($(l -.l, t h.t) $(l +.l, t t.t))
      %lax   &($(l h.l, t h.t) $(l t.l, t t.t))
    ==
  ==
+$  laze-fork  [y=[o=@uxid laz=laze] n=[o=@uxid laz=laze]]
+$  laze-bond  [o=@uxid laz=laze]
+$  goal-shape  $%([%pick ~] [%done ~] [%next laz=laze])
+$  need-inter1
  $+  need-inter1
  $;  |-
  $:  sure=sure-ordered
      fork=(list [y=$ n=$])
  ==
::
+$  need-inter2
  $+  need-inter2
  $;  |-
  $:  sure=need-ordered
      fork=(list [y=$ n=$])
  ==
::  Ignore bounds by unifying sure with bonds
::
++  lazy-to-inter1
  ~%  %lazy-to-inter1  ..ride  ~
  |=  laz=need-lazy
  ^-  need-inter1
  =*  lazy-to-inter  .
  ?:  &(?=(~ fork.laz) ?=(~ bond.laz))
    [[(need-to-ordered ned.sure.laz) lok.sure.laz] ~]
  %+  roll  bond.laz
  =/  ned-sure-new  (need-to-ordered ned.sure.laz)
  =/  fork-new=(list [need-inter1 need-inter1])
    %+  turn  fork.laz
    |=  [[* laz-y=need-lazy] * laz-n=need-lazy]
    [(lazy-to-inter laz-y) (lazy-to-inter laz-n)]
  ::
  =/  sure-new=sure-ordered  [ned-sure-new lok.sure.laz]
  |=  [[* i=need-lazy] sur=_sure-new fork=_fork-new]
  ^+  [sur fork]
  =/  i  (lazy-to-inter i)
  :_  (weld fork.i fork)
  :-  (uni-need-ord ned.sure.i ned.sur)
  (~(uni in lok.sur) lok.sure.i)
::
++  axe-in-less-cape
  |=  [axe=@ less=cape]
  ^-  ?
  ?<  =(0 axe)
  |-  ^-  ?
  ?:  =(1 axe)  &
  ?@  less  |
  ?-  (cap axe)
    %2  $(axe (mas axe), less -.less)
    %3  $(axe (mas axe), less +.less)
  ==
::
++  axe-in-need
  |=  [axe=@ ned=need]
  ^-  ?
  ?<  =(0 axe)
  |-  ^-  ?
  ?:  =(1 axe)  &
  ?-  -.ned
    %lax   ~|(%lax-in-a-shape !!)
    ?(%none %this)  |
    ^               $(axe (mas axe), ned ?-((cap axe) %2 -.ned, %3 +.ned))
    %both           $(axe (mas axe), ned ?-((cap axe) %2 h.ned, %3 t.ned))
  ==
::
++  inter1-to-inter2
  ~%  %inter1-to-inter2  ..ride  ~
  |=  [intr=need-inter1 less=cape]
  ^-  need-inter2
  =*  this-buc  $
  :-  %-  look-ord
      :-  ned.sure.intr
      %-  silt
      (skip ~(tap in lok.sure.intr) |=(axe=@ (axe-in-less-cape axe less)))
  %+  turn  fork.intr
  |=  [y=need-inter1 n=need-inter1]
  [this-buc(intr y) this-buc(intr n)]
::
++  laze-to-inter1
  ~%  %laze-to-inter1  ..ride  ~
  |=  laz=laze
  ^-  need-inter1
  =*  laze-to-inter  .
  ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [sure.laz ~]
  %+  roll  bond.laz
  =/  fork-new=(list [need-inter1 need-inter1])
    %+  turn  fork.laz
    |=  [[* laz-y=laze] * laz-n=laze]
    [(laze-to-inter laz-y) (laze-to-inter laz-n)]
  ::
  |=  [[* i=laze] sur=_sure.laz fork=_fork-new]
  ^+  [sur fork]
  =/  i  (laze-to-inter i)
  :_  (weld fork.i fork)
  :-  (uni-need-ord ned.sure.i ned.sur)
  (~(uni in lok.sur) lok.sure.i)
::
::  +sure-of: the shape of what a function reads first thing: on every
::  path, before any hint that keeps a trace frame or has an effect, and
::  before any call that may crash.  It is the sure need of the function's
::  lazy need: a need under a hint is in a bond, on a branch in a fork, and
::  a need of code that runs after such a hint or call is bound past it
::  (+past:comp).  If a part of this shape is not there, the function
::  crashes on it with the trace stack it was entered with and before any
::  effect of its own: so does a fetch of the part by its caller, at the
::  call.
::
++  sure-of
  |=  [sur=sure-ordered less=cape]
  ^-  need-ordered
  (lax-strip sure:(inter1-to-inter2 [sur ~] less))
::  a shape without its %lax parts: they are no reads
::
++  lax-strip
  |=  ned=need-ordered
  ^-  need-ordered
  ?-    -.ned
      %none  ned
      %this  ned
      %lax   [%none ~]
      ^      (cons-need $(ned -.ned) $(ned +.ned))
      %both
    =/  x  (cons-need $(ned h.ned) $(ned t.ned))
    ?^  -.x  [%both x]
    [%this ~]
  ==
::  A shape with its %lax parts decided: the parts where every call site
::  holds them and the bell knows the cell, the noun otherwise
::
++  lax-resolve
  ~%  %lax-resolve  ..ride  ~
  |=  [ned=need-ordered less=lore]
  ^-  need-ordered
  ?-    -.ned
      %none  ned
      %this  ned
      ^
    %+  cons-need
      $(ned -.ned, less (hed-lore less))
    $(ned +.ned, less (tel-lore less))
  ::
      %both
    =/  x
      %+  cons-need
        $(ned h.ned, less (hed-lore less))
      $(ned t.ned, less (tel-lore less))
    ?^  -.x  [%both x]
    [%this ~]
  ::
      %lax
    ?.  &(?=(^ les.less) ?=(^ hel.less))  [%this ~]
    =/  x
      %+  cons-need
        $(ned h.ned, less (hed-lore less))
      $(ned t.ned, less (tel-lore less))
    ?:  ?=(%none -.x)  [%this ~]
    x
  ==
::  +cell-sure: the noun that .sur is the sure need of (+sure-of) is a cell:
::  a part of it is read first thing, or the bell knows the cell (.k)
::
++  cell-sure
  |=  [sur=need-ordered k=sock]
  ^-  ?
  ?|  ?=(%both -.sur)
      ?=(^ -.sur)
      ?=(^ -.k)
      &(?=(%& -.k) ?=(^ +.k))
  ==
::  +sure-at: +cell-sure of the noun at .axe
::
++  sure-at
  |=  [axe=@ sur=need-ordered k=sock]
  ^-  ?
  ?:  =(1 axe)  (cell-sure sur k)
  ?-  (cap axe)
    %2  $(axe (mas axe), sur (hed-need-ord sur), k (hed:so k))
    %3  $(axe (mas axe), sur (tel-need-ord sur), k (tel:so k))
  ==
::  +need-soft: the need .ned of a callee has a part that the callee does
::  not read first thing (.sur): a cell of it that is not sure
::
++  need-soft
  |=  [ned=need-ordered sur=need-ordered k=sock]
  ^-  ?
  ?:  ?=(?(%none %this %lax) -.ned)  |
  ?.  (cell-sure sur k)  &
  =/  [h=need-ordered t=need-ordered]
    ?:(?=(%both -.ned) [h.ned t.ned] [p.ned q.ned])
  ?|  $(ned h, sur (hed-need-ord sur), k (hed:so k))
      $(ned t, sur (tel-need-ord sur), k (tel:so k))
  ==
::  +sound-far: +sound:comp, which sees through .dep direct calls: the
::  product of a call is that of the callee's formula
::
++  sound-far
  ~%  %sound-far  ..ride  ~
  |=  $:  nom=nomm
          ned=need-ordered
          cod=_code:*long-ska
          ret=(map bell rets)
          dep=@ud
      ==
  ^-  ?
  ?:  ?=(?(%none %this %lax) -.ned)  &
  ~+
  =/  [h=need-ordered t=need-ordered]
    ?:(?=(%both -.ned) [h.ned t.ned] [p.ned q.ned])
  ?+    nom  |
      [^ *]      &($(nom -.nom, ned h) $(nom +.nom, ned t))
      [%0 *]     =(0 p.nom)
      [%6 *]     &($(nom q.nom) $(nom r.nom))
      [%7 *]     $(nom q.nom)
      [%11 *]    $(nom q.nom)
      [%mean *]  $(nom q.nom)
  ::
  ::  a callee that returns the parts apart hands them on without a
  ::  noun to take apart, and its product, where it comes whole (to a
  ::  function of its whole subject, from the subject version), is a pair
  ::  wherever the shape has one
  ::
      [%2 *]
    ?~  info.nom  |
    ?:  ?&  ?=(~ k.u.info.nom)
            (sound-rets (~(gut by ret) b.u.info.nom ~) ned)
        ==
      &
    ?:  =(0 dep)  |
    $(nom nomm:(~(got by cod) b.u.info.nom), dep (dec dep))
  ::  what is put in makes the part at the axis, the noun it is put into
  ::  the rest: the edit takes that noun apart down to the axis itself
  ::
      [%10 *]
    =/  e  (need-ord-edit p.p.nom ned)
    &($(nom q.p.nom, ned don.e) $(nom q.nom, ned rec.e))
  ==
::  +sound for a product returned by a shape
::
++  sound-rets
  |=  [ret=rets ned=need-ordered]
  ^-  ?
  ?:  ?=(?(%none %this %lax) -.ned)  &
  ?.  ?=([%c *] ret)  |
  =/  [h=need-ordered t=need-ordered]
    ?:(?=(%both -.ned) [h.ned t.ned] [p.ned q.ned])
  &($(ret p.ret, ned h) $(ret q.ret, ned t))
::  +need-ord-edit: the need .ned of an edited noun, as the need of what
::  was put at .axe and the need of the noun it was put into, where the
::  part at .axe needs nothing
::
++  need-ord-edit
  |=  [axe=@ ned=need-ordered]
  ^-  [don=need-ordered rec=need-ordered]
  ?:  =(1 axe)  [ned [%none ~]]
  ?:  ?=(?(%none %this %lax) -.ned)  [[%none ~] [%none ~]]
  =/  [h=need-ordered t=need-ordered]
    ?:(?=(%both -.ned) [h.ned t.ned] [p.ned q.ned])
  ?-    (cap axe)
      %2
    =/  r  $(axe (mas axe), ned h)
    [don.r (cons-need rec.r t)]
  ::
      %3
    =/  r  $(axe (mas axe), ned t)
    [don.r (cons-need h rec.r)]
  ==
::  +hinted: the formula has a hint that keeps a trace frame or has an
::  effect, or a call that may crash: the callee may have such hints, and a
::  jet reports a crash with frames of its own
::
++  hinted
  ~%  %hinted  ..ride  ~
  |=  [=nomm cod=_code:*long-ska]
  ^-  ?
  ?-  nomm
    [%0 *]     |
    [%1 *]     |
    [%3 *]     $(nomm p.nomm)
    [%4 *]     $(nomm p.nomm)
    [%mean *]  &
    [%12 *]    &
  ::
      ?([^ *] [%2 *] [%5 *] [%6 *] [%7 *] [%10 *] [%11 *])
    ~+
    ?-  nomm
      [^ *]    |($(nomm -.nomm) $(nomm +.nomm))
      [%5 *]   |($(nomm p.nomm) $(nomm q.nomm))
      [%6 *]   |($(nomm p.nomm) $(nomm q.nomm) $(nomm r.nomm))
      [%7 *]   |($(nomm p.nomm) $(nomm q.nomm))
      [%10 *]  |($(nomm q.p.nomm) $(nomm q.nomm))
    ::
        [%2 *]
      ?~  info.nomm  &
      ?|  !pure:(~(got by cod) b.u.info.nomm)
          $(nomm p.nomm)
          $(nomm q.nomm)
      ==
    ::
        [%11 *]
      ?@  p.nomm  |(?=(hint-static p.nomm) $(nomm q.nomm))
      ?|  ?=(hint-dynamic p.p.nomm)
          $(nomm q.p.nomm)
          $(nomm q.nomm)
      ==
    ==
  ==
::
::  +laze-may: the shape of all that some path reads of the subject: the
::  needs of both branches of every fork united, where +laze-collapse takes
::  their MSG
::
++  laze-may
  ~%  %laze-may  ..ride  ~
  |=  [laz=laze less=lore]
  ^-  need-ordered
  =/  intr=need-inter2  (inter1-to-inter2 (laze-to-inter1 laz) les.less)
  %-  lax-resolve
  :_  less
  |-  ^-  need-ordered
  %+  roll  fork.intr
  |=  [[y=need-inter2 n=need-inter2] acc=_sure.intr]
  (uni-need-ord (uni-need-ord acc ^$(intr y)) ^$(intr n))
::
++  laze-collapse
  ~%  %laze-collapse  ..ride  ~
  |=  [laz=laze less=lore]
  ^-  need-ordered
  %-  lax-resolve
  :_  less
  (inter2-collapse (inter1-to-inter2 (laze-to-inter1 laz) les.less) less)
::
++  shape-collapse
  ~%  %shape-collapse  ..ride  ~
  |=  [laz=need-lazy less=lore]
  ^-  need-ordered
  %-  lax-resolve
  :_  less
  (inter2-collapse (inter1-to-inter2 (lazy-to-inter1 laz) les.less) less)
::
++  inter2-collapse
  ~%  %inter2-collapse  ..ride  ~
  |=  [intr=need-inter2 less=lore]
  ^-  need-ordered
  ::  The fixed point of the available shapes is computed over the whole fork
  ::  tree per round: push each parent's shape down, then pull the MSG of the
  ::  branches of every fork up, so that a round is linear in the tree size.
  ::  Starting from the sure shapes, this converges to the same least fixed
  ::  point as the nested per-fork loop of +inter2-collapse-nested, which
  ::  re-collapsed every subtree once per level above it.
  ::
  =/  fix=need-inter2  intr
  =.  fix
    |-  ^-  need-inter2
    =/  new  (inter2-fix-round fix less)
    ?:  =(new fix)  new
    $(fix new)
  ::
  =/  res  (inter2-orig intr fix less)
  !@  collapse-check  res
  ~|  %inter2-collapse-mismatch
  ?>  =(res (inter2-collapse-nested intr less))
  res
::  One round of the fixed point: the parent's shape comes in as .p
::
++  inter2-fix-round
  ~%  %inter2-fix-round  ..ride  ~
  |=  [prev=need-inter2 less=lore]
  ^-  need-inter2
  =/  parent=need-ordered  none+~
  |-  ^-  need-inter2
  =*  round  $
  =.  parent  (uni-need-ord parent sure.prev)
  =/  kids=(list [y=need-inter2 n=need-inter2])
    %+  turn  fork.prev
    |=  [y=need-inter2 n=need-inter2]
    [round(prev y) round(prev n)]
  ::
  :_  kids
  %+  roll  kids
  |=  [[y=need-inter2 n=need-inter2] =_parent]
  (uni-need-ord parent (msg-need-ord sure.y sure.n less))
::  The returned shape, given the fixed point of the available shapes
::
++  inter2-orig
  ~%  %inter2-orig  ..ride  ~
  |=  [intr=need-inter2 fix=need-inter2 less=lore]
  ^-  need-ordered
  =*  orig  .
  =/  acc=need-ordered  sure.intr
  =/  forks  fork.intr
  =/  fixes  fork.fix
  |-  ^-  need-ordered
  ?~  forks  acc
  ?>  ?=(^ fixes)
  =/  o-y  (orig y.i.forks y.i.fixes less)
  =/  o-n  (orig n.i.forks n.i.fixes less)
  =/  msg-special  (msg-need-ord-fix-aware o-y o-n sure.fix less)
  $(acc (uni-need-ord acc msg-special), forks t.forks, fixes t.fixes)
::
++  inter2-collapse-nested
  ~%  %inter2-collapse-nested  ..ride  ~
  |=  [intr=need-inter2 less=lore]
  ^-  need-ordered
  =/  sures=[orig=need-ordered fix=need-ordered]  [. .]:sure.intr
  =<  orig
  |-  ^+  sures
  =*  sures-loop  $
  =;  sures1=_sures
    ?:  =(fix.sures1 fix.sures)  sures1
    $(fix.sures fix.sures1)
  ::  We propagate fix.sures deeper for correct MSG computations. We don't
  ::  do the same for orig.sures to avoid adding extra information we would like
  ::  to drop.
  ::
  %+  roll  fork.intr
  |=  [[intr-y=need-inter2 intr-n=need-inter2] =_sures]
  =/  sures-y=_sures
    %=  sures-loop
      orig.sures  sure.intr-y
      fix.sures   (uni-need-ord fix.sures sure.intr-y)
      intr        intr-y
    ==
  ::
  =/  sures-n=_sures
    %=  sures-loop
      orig.sures  sure.intr-n
      fix.sures   (uni-need-ord fix.sures sure.intr-n)
      intr        intr-n
    ==
  ::
  =.  fix.sures
    (uni-need-ord fix.sures (msg-need-ord fix.sures-y fix.sures-n less))
  ::
  ::  We compute simple MSG of fix.sures-y/n as they contain the totality of 
  ::  the shape info. We compute special MSG of orig.sures-y/n that takes
  ::  fix.sures into account without adding it to orig.sures-y/n
  ::
  =/  msg-special
    (msg-need-ord-fix-aware orig.sures-y orig.sures-n fix.sures less)
  ::
  sures(orig (uni-need-ord orig.sures msg-special))
::
::  what two shapes both take apart: for what is read first thing
::  (+sure-of), where only the cells count
::
++  int-need-ord
  ~%  %int-need-ord  ..ride  ~
  |=  [a=need-ordered b=need-ordered]
  ^-  need-ordered
  ?:  =(a b)  a
  ?:  |(?=(%none -.a) ?=(%none -.b))  [%none ~]
  ?:  |(?=(%lax -.a) ?=(%lax -.b))  [%none ~]
  ?:  |(?=(%this -.a) ?=(%this -.b))  [%this ~]
  ~+
  =/  x=need-ordered
    %+  cons-need
      $(a (hed-need-ord a), b (hed-need-ord b))
    $(a (tel-need-ord a), b (tel-need-ord b))
  ?.  &(?=(%both -.a) ?=(%both -.b))  x
  ?^  -.x  [%both x]
  [%this ~]
::
++  hed-need-ord
  |=  a=need-ordered
  ^-  need-ordered
  ?-  -.a
    %none  [%none ~]
    %this  [%none ~]
    %both  h.a
    ^      -.a
    %lax   h.a
  ==
::
++  tel-need-ord
  |=  a=need-ordered
  ^-  need-ordered
  ?-  -.a
    %none  [%none ~]
    %this  [%none ~]
    %both  t.a
    ^      +.a
    %lax   t.a
  ==
::
::  MSG of `a` and `b` while knowing that axes in `fix` exist
::
++  msg-need-ord-fix-aware
  ~%  %msg-need-ord-fix-aware  ..ride  ~
  |=  [a=need-ordered b=need-ordered fix=need-ordered less=lore]
  ^-  need-ordered
  ~+
  =*  msg  .
  ?:  =(a b)  a
  ?:  |(?=(%lax -.a) ?=(%lax -.b))
    ?:  ?=(%lax -.a)
      ?:  ?=(%lax -.b)
        :+  %lax
          (msg h.a h.b (hed-need-ord fix) (hed-lore less))
        (msg t.a t.b (tel-need-ord fix) (tel-lore less))
      (uni-need-ord (msg none+~ b fix less) a)
    (uni-need-ord (msg none+~ a fix less) b)
  ?:  |(?=(%this -.fix) ?=(%none -.fix) ?=(%lax -.fix))
    (msg-need-ord a b less)
  ?:  &(?=(%none -.a) =(b fix))  b
  ?:  &(?=(%none -.b) =(a fix))  a
  =/  need-here=?  |(?=(%this -.a) ?=(%this -.b) ?=(%both -.a) ?=(%both -.b))
  =/  x
    %+  cons-need
      (msg (hed-need-ord a) (hed-need-ord b) (hed-need-ord fix) (hed-lore less))
    (msg (tel-need-ord a) (tel-need-ord b) (tel-need-ord fix) (tel-lore less))
  ::
  ?-  -.x
    %none  ?:(need-here [%this ~] [%none ~])
    ^      ?:(need-here [%both x] x)
  ==
::
++  spin-split
  |*  [a=(list) b=* c=_|=(^ [*^ +<+])]
  =>  .(c `$-([_?>(?=(^ a) i.a) _b] [_-:(c) _b])`c)
  =/  acc=[p=(list _-<:(c)) q=(list _->:(c))]  [~ ~]
  |-  ^-  (pair _acc _b)
  ?~  a  [[(flop p.acc) (flop q.acc)] b]
  =^  res  b  (c i.a b)
  $(acc [[-.res p.acc] [+.res q.acc]], a t.a)
::  if axis b is in axis a, return [~ c] such that (peg a c) == b
::  else return ~
::
++  gep
  |=  [a=@ b=@]
  ^-  (unit @)
  ?<  =(0 a)
  ?<  =(0 b)
  ?:  =(a b)  `1
  ?:  (lth b a)  ~
  :: |-  ^-  (unit @)
  :: ?:  =(a 1)  `b
  :: ?.  =((cap a) (cap b))  ~
  :: $(a (mas a), b (mas b))
  ::
  =/  dif-wid  (sub (met 0 b) (met 0 a))
  =/  top-b  (rsh [0 dif-wid] b)
  ?.  =(top-b a)  ~
  =/  x  (bex dif-wid)
  =/  low-b  (dis b (dec x))
  `(con low-b x)
::
::
++  none-equivalent
  ~%  %none-equivalent  ..ride  ~
  |=  laz=need-lazy
  ^-  ?
  =*  none  .
  ?&  ?=([%none ~] ned.sure.laz)
      ?=(?(~ [%1 ~ ~]) lok.sure.laz)
      (levy fork.laz |=([[* a=need-lazy] * b=need-lazy] &((none a) (none b))))
      (levy bond.laz |=([* n=need-lazy] (none n)))
  ==
--
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  IR optimization passes
::
::    The code emitted by the compilation step is correct but rather bloated.
::    Deconsing code gets emitted into every BB that needs something from the
::    subject, a lot of branches are produced that do not do anything useful,
::    etc.  Each of the optimization passes below addresses a gripe I had with
::    the shape of the produced control flow graph.
::
::    The biggest pass is +alias: it partially executes the code in BBs, getting
::    rid of unnecessary %mov's, as these are just an artifact of DDCG: we know
::    which registers correspond to the same noun once we have compiled the
::    whole function.  It also keeps track of information about the values in
::    registers, eliminating branches when the shape or the value of a given
::    register is known.
::
::    Other passes remove dead code, trim stack trace hints, etc.  All of them
::    are applied in sequence in a fixed point loop, which is a recurring theme,
::    for better or for worse.  Doing so introduces unnecessary iterations over
::    the CFG, so at some point these passes should be merged into one, with the
::    one-pass-at-a-time version kept around for parity checks in debug mode.
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
|%
::  BBs in topological order
::
++  bb-topo
  ~%  %bb-topo  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  (list @uwoo)
  =|  saw=(set @uwoo)
  =|  out=(list @)
  =/  o=@uwoo  `@`0
  =<  -
  |-  ^-  [(list @uwoo) (set @uwoo)]
  =*  dfs-buc  $
  =.  saw  (~(put in saw) o)
  =<  [[o out] saw]
  ^-  [o=@uwoo out=(list @uwoo) saw=(set @uwoo)]
  :-  o
  %+  roll  (get-jmps fin:(~(got by blocks) o))
  |=  [[* o1=@uwoo] =_out =_saw]
  ?:  (~(has in saw) o1)  [out saw]
  dfs-buc(o o1, out out, saw saw)
::
++  rev-cfg
  ~%  %rev-cfg  ..ride  ~
  |=  [blocks=(map @uwoo blob) topo-set=(set @uwoo)]
  ^-  (jar @uwoo @uwoo)
  %-  ~(rep by blocks)
  |=  [[o=@uwoo v=blob] acc=(jar @uwoo @uwoo)]
  ?.  (~(has in topo-set) o)  acc
  %+  roll  (get-jmps fin.v)
  |=  [[* o1=@uwoo] =_acc]
  (~(add ja acc) o1 o)
::  For each vertex find the immediate dominator, if exists.
::  That is, for each BB find either the predecessor if it is not
::  the merge block, or the corresponing branching ancestor
::
++  get-idom
  ~%  %get-idom  ..ride  ~
  |=  [blocks=(map @uwoo blob) topo=(list @uwoo) rev=(jar @uwoo @uwoo)]
  ^-  (map @uwoo @uwoo)
  =|  idom=(map @uwoo @uwoo)
  =|  depf=(map @uwoo @)
  |^  ^+  idom
  ?~  topo  idom
  =/  pre  (~(get ja rev) i.topo)
  ?~  pre
    =.  depf  (~(put by depf) i.topo 1)
    $(topo t.topo)
  =/  dom  (roll t.pre |=([i=@uwoo acc=_i.pre] (nca i acc)))
  ~|  dom
  =.  depf  (~(put by depf) i.topo +((~(got by depf) dom)))
  =.  idom  (~(put by idom) i.topo dom)
  $(topo t.topo)
  ::  nearest common ancestor
  ::
  ++  nca
    |=  [a=@uwoo b=@uwoo]
    ^-  @uwoo
    ?:  =(a b)  a
    =/  [[deeper=@uwoo dep-deeper=@] [shallow=@uwoo dep-shallow=@]]
      ~|  [=_a =_b =_rev]
      =/  dep-a  (~(got by depf) a)
      =/  dep-b  (~(got by depf) b)
      ?:  (lth dep-a dep-b)  [[b dep-b] a dep-a]
      [[a dep-a] b dep-b]
    ::
    |-  ^-  @uwoo
    ?:  =(deeper shallow)  deeper
    =/  nex  (~(got by idom) deeper)
    =/  dep-nex  (~(got by depf) nex)
    ?:  (lth dep-shallow dep-nex)
      $(deeper nex, dep-deeper dep-nex)
    %=  $
      shallow      nex
      dep-shallow  dep-nex
      deeper       shallow
      dep-deeper   dep-shallow
    ==
  --
::  For each vertex find the immediate postdominator, if exists.
::  That is, for each BB find either the immediate successor if it does not
::  branch, or the successor where the branches merge.
::
++  get-ipdom
  ~%  %get-ipdom  ..ride  ~
  |=  [blocks=(map @uwoo blob) rev-topo=(list @uwoo)]
  ^-  (map @uwoo @uwoo)
  =|  ipdom=(map @uwoo @uwoo)
  =|  depth=(map @uwoo @)
  |^  ^+  ipdom
  ?~  rev-topo  ipdom
  =/  nex=(^pole jmp)  (get-jmps fin:(~(got by blocks) i.rev-topo))
  ?+    nex  ~|(%impossible !!)
      ~
    =.  depth  (~(put by depth) i.rev-topo 1)
    $(rev-topo t.rev-topo)
  ::
      [a=* ~]
    =.  depth  (~(put by depth) i.rev-topo +((~(got by depth) there.a.nex)))
    =.  ipdom  (~(put by ipdom) i.rev-topo there.a.nex)
    $(rev-topo t.rev-topo)
  ::
      [a=* b=* ~]
    =/  [z=@uwoo o=@uwoo]  [there.a.nex there.b.nex]
    ?~  x=(ncs z o)
      =.  depth  (~(put by depth) i.rev-topo 1)
      $(rev-topo t.rev-topo)
    =.  depth  (~(put by depth) i.rev-topo +((~(got by depth) u.x)))
    =.  ipdom  (~(put by ipdom) i.rev-topo u.x)
    $(rev-topo t.rev-topo)
  ==
  ::  nearest common successor
  ::
  ++  ncs
    |=  [a=@uwoo b=@uwoo]
    ^-  (unit @uwoo)
    ?:  =(a b)  `a
    =/  [[deeper=@uwoo dep-deeper=@] [shallow=@uwoo dep-shallow=@]]
      =/  dep-a  (~(got by depth) a)
      =/  dep-b  (~(got by depth) b)
      ?:  (lth dep-a dep-b)  [[b dep-b] a dep-a]
      [[a dep-a] b dep-b]
    ::
    |-  ^-  (unit @uwoo)
    ?:  =(deeper shallow)  `deeper
    ?~  nex=(~(get by ipdom) deeper)  ~
    =/  dep-nex  (~(got by depth) u.nex)
    ?:  (lth dep-shallow dep-nex)
      $(deeper u.nex, dep-deeper dep-nex)
    %=  $
      shallow      u.nex
      dep-shallow  dep-nex
      deeper       shallow
      dep-deeper   dep-shallow
    ==
  --
::
+$  info-reg
  $:  is-cell=$~(| ?)
      is-loob=$~(| ?)
      hed-of=(set @uvre)
      tel-of=(set @uvre)
      has-hed=(unit @uvre)
      has-tel=(unit @uvre)
      dec-of=(unit @uvre)
      has-imm=(unit *)
  ==
::  Removes %mov's and other unnecessary instructions by symbolicly executing
::  IR, keeping track of noun aliasing and cellness. Also removes branches
::  if the noun is known to be a cell in %clq, or if the register is compared
::  to itself in %eqq, or if the noun is known in %brn
::
++  alias
  ~%  %alias  ..ride  ~
  |=  $:  n-args=@ud
          blocks=(map @uwoo blob)
          rev=(jar @uwoo @uwoo)
          topo=(list @uwoo)
      ==
  ^-  [folded=? (map @uwoo blob)]
  =|  $=  gen
      $:  new=(map @uwoo blob)
          old=(map @uvre @uvre)  ::  eliminated register -> its alias
          info=(map @uwoo (map @uvre info-reg))
          imms=(map @uwoo (jug * @uvre))
          info-local=(map @uvre info-reg)
          imms-local=(jug * @uvre)
          rev=(jug @uwoo @uwoo)
          folded=_|   ::  a branch or a block was eliminated
      ==
  ::
  =.  rev.gen  (~(run by rev) (bake silt (list @uwoo)))
  |^  ^-  [? (map @uwoo blob)]
  ?~  topo  [folded.gen new.gen]
  =*  o  i.topo
  =/  pre=(list @uwoo)  ~(tap in (~(get ju rev.gen) o))
  ?:  &(=(~ pre) !=(0w0 o))
    ::  this block became unreachable: delete its descendants from reversed CFG
    ::
    =.  folded.gen  &
    =.  rev.gen
      %+  roll  (get-jmps fin:(~(got by blocks) o))
      |=  [j=jmp acc=_rev.gen]
      (~(del ju acc) there.j o)
    ::
    $(topo t.topo)
  =^  info=(map @uvre info-reg)  gen
    ?~  pre
      ::  entry block: initialize input registers
      ::
      =|  info=(map @uvre info-reg)
      =/  r=@uvre  0v0
      |-  ^+  [info gen]
      ?:  =(r n-args)  [info gen]
      =.  info  (~(put by info) r *info-reg)
      $(r `@uvre`+(r))
    :_  gen
    =/  info=(map @uvre info-reg)
      %+  roll  t.pre
      |=  [o1=@uwoo acc=_(~(got by info.gen) i.pre)]
      (join-info acc (~(got by info.gen) o1))
    ::  if previous block only %brn/%clq - refine info-local
    ::
    ^+  info
    ?^  t.pre  info
    =/  pre-b  (~(got by new.gen) i.pre)
    ?:  ?=(%brn -.fin.pre-b)
      =/  pre-z=@uwoo  there.z.fin.pre-b
      =/  pre-o=@uwoo  there.o.fin.pre-b
      ?:  &(=(pre-z o) !=(pre-o o))
        =/  lens  |=(info-reg +<(has-imm `&))
        (~(jab by info) s.fin.pre-b lens)
      ?:  &(=(pre-o o) !=(pre-z o))
        =/  lens  |=(info-reg +<(has-imm `|))
        (~(jab by info) s.fin.pre-b lens)
      ~|  %brn-successor-lost
      ?>  =(pre-z pre-o)
      ?>  =(pre-z o)
      =/  lens  |=(info-reg +<(is-loob &))
      (~(jab by info) s.fin.pre-b lens)
    ?:  ?=(%brz -.fin.pre-b)
      =/  pre-z=@uwoo  there.z.fin.pre-b
      =/  pre-o=@uwoo  there.o.fin.pre-b
      ?:  &(=(pre-z o) !=(pre-o o))
        =/  lens  |=(info-reg +<(has-imm `&))
        (~(jab by info) s.fin.pre-b lens)
      ?:  &(=(pre-o o) !=(pre-z o) is-loob:(~(got by info) s.fin.pre-b))
        =/  lens  |=(info-reg +<(has-imm `|))
        (~(jab by info) s.fin.pre-b lens)
      info
    ?:  ?=(%clq -.fin.pre-b)
      =/  pre-z=@uwoo  there.z.fin.pre-b
      =/  pre-o=@uwoo  there.o.fin.pre-b
      ?:  &(=(pre-z o) !=(pre-o o))
        =/  lens  |=(info-reg +<(is-cell &))
        (~(jab by info) s.fin.pre-b lens)
      ~|  %clq-successor-lost
      ?>  =(pre-o o)
      info
    info
  ::
  =/  imms=(jug * @uvre)
    ?~  pre  ~
    %+  roll  t.pre
    |=  [o1=@uwoo acc=_(~(got by imms.gen) i.pre)]
    (join-imms acc (~(got by imms.gen) o1))
  ::
  =.  info-local.gen  info
  =.  imms-local.gen  imms
  =/  bob  (~(got by blocks) o)
  ::  parameters get the joined info of the arguments passed to them
  ::
  =^  par-new=(list @uvre)  gen
    =/  edges=(list [p=@uwoo args=(list (unit @uvre))])
      %-  zing
      %+  turn  pre
      |=  p=@uwoo
      %+  murn  (get-jmps fin:(~(got by new.gen) p))
      |=  j=jmp
      ?.  =(there.j o)  ~
      `[p args.j]
    ::
    =|  out=(list @uvre)
    |-  ^-  [(list @uvre) _gen]
    ?~  par.bob  [(flop out) gen]
    =/  new  i.par.bob
    =/  ins=(list (unit info-reg))
      %+  turn  edges
      |=  [p=@uwoo args=(list (unit @uvre))]
      ?>  ?=(^ args)
      ?~  i.args  ~
      `(~(got by (~(got by info.gen) p)) u.i.args)
    ::
    =.  info-local.gen  (~(put by info-local.gen) new (param-info ins))
    =.  out  [new out]
    %=    $
        par.bob  t.par.bob
    ::
        edges
      %+  turn  edges
      |=  [p=@uwoo args=(list (unit @uvre))]
      [p ?>(?=(^ args) t.args)]
    ==
  ::
  =^  body-new=(list pole)  gen
    =-  [(flop -<) ->]
    ^-  [(list pole) _gen]
    %+  roll  body.bob
    |=  [op=pole body-new=(list pole) gen-init=_gen]
    ^+  [body-new gen]
    =.  gen  gen-init
    ?-    -.op
        %imm
      ?^  res=(~(get ju imms-local.gen) n.op)
        =.  old.gen  (~(put by old.gen) d.op n.res)
        [body-new gen]
      =/  new=@uvre  d.op
      =|  info=info-reg
      =.  info-local.gen  (~(put by info-local.gen) new info(has-imm `n.op))
      =.  imms-local.gen  (~(put ju imms-local.gen) n.op new)
      ::
      [[[%imm n.op new] body-new] gen]
    ::
        %mov
      =.  old.gen  (~(put by old.gen) d.op (rn s.op))
      [body-new gen]
    ::
        %inc
      =/  arg  (rn s.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?^  dec-of.arg-info
        =.  old.gen  (~(put by old.gen) d.op u.dec-of.arg-info)
        [body-new gen]
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(dec-of `new)))
      ::
      [[[%inc arg new] body-new] gen]
    ::
        %con
      =/  h  (rn h.op)
      =/  t  (rn t.op)
      =/  h-info  (~(got by info-local.gen) h)
      =/  t-info  (~(got by info-local.gen) t)
      ?^  intersect=(~(int in hed-of.h-info) tel-of.t-info)
        =.  old.gen  (~(put by old.gen) d.op n.intersect)
        [body-new gen]
      =/  new  d.op
      =|  info=info-reg
      =.  info-local.gen
        (~(put by info-local.gen) new info(has-hed `h, has-tel `t, is-cell &))
      ::
      =.  info-local.gen
        =/  lens  |=(info-reg +<(hed-of (~(put in hed-of) new)))
        (~(jab by info-local.gen) h lens)
      ::
      =.  info-local.gen
        =/  lens  |=(info-reg +<(tel-of (~(put in tel-of) new)))
        (~(jab by info-local.gen) t lens)
      ::
      [[[%con h t new] body-new] gen]
    ::
        %hed
      =/  arg  (rn s.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?^  has-hed.arg-info
        =.  old.gen  (~(put by old.gen) d.op u.has-hed.arg-info)
        [body-new gen]
      =/  new  d.op
      =|  info=info-reg
      =.  info-local.gen  (~(put by info-local.gen) new info(hed-of [arg ~ ~]))
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(has-hed `new)))
      ::
      [[[%hed arg new] body-new] gen]
    ::
        %tal
      =/  arg  (rn s.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?^  has-tel.arg-info
        =.  old.gen  (~(put by old.gen) d.op u.has-tel.arg-info)
        [body-new gen]
      =/  new  d.op
      =|  info=info-reg
      =.  info-local.gen  (~(put by info-local.gen) new info(tel-of [arg ~ ~]))
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(has-tel `new)))
      ::
      [[[%tal arg new] body-new] gen]
    ::
        %cel
      =/  arg  (rn p.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?:  is-cell.arg-info
        [body-new gen]
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(is-cell &)))
      ::
      [[[%cel arg] body-new] gen]
    ::
        %lob
      =/  arg  (rn p.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?:  |(is-loob.arg-info ?=([~ ?] has-imm.arg-info))
        [body-new gen]
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(is-loob &)))
      ::
      [[[%lob arg] body-new] gen]
    ::
        %equ
      =/  l  (rn l.op)
      =/  r  (rn r.op)
      ?:  =(l r)  [body-new gen]
      [[[%equ l r] body-new] gen]
    ::
        %hsp
      [[op body-new] gen]
    ::
        %hse
      [[op body-new] gen]
    ::
        %hdp
      =/  arg  (rn p.op)
      [[[%hdp n.op arg f.op] body-new] gen]
    ::
        %hde
      =/  arg  (rn p.op)
      [[[%hde n.op arg f.op] body-new] gen]
    ::
        %hmp
      [[[%hmp a.op (turn v.op rn) f.op] body-new] gen]
    ::
        %hme
      [[[%hme a.op (turn v.op rn) f.op] body-new] gen]
    ::
        %hcp
      [[op body-new] gen]
    ::
        %hce
      [[op body-new] gen]
    ::
        %spy
      =/  e  (rn e.op)
      =/  p  (rn p.op)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%spy e p new] body-new] gen]
    ::
        %nok
      =/  u  (rn u.op)
      =/  f  (rn f.op)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%nok u f new] body-new] gen]
    ::
        %cal
      =/  v  (turn v.op rn)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%cal a.op v new] body-new] gen]
    ::
        %caf
      =/  v  (turn v.op rn)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%caf a.op v new n.op] body-new] gen]
    ::
        %cam
      =/  v  (turn v.op rn)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%cam a.op v new k.op] body-new] gen]
    ::
        %csl
      =/  s  (rn s.op)
      ~|  d.op
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%csl a.op s new] body-new] gen]
    ::
        %csf
      =/  s  (rn s.op)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%csf a.op s new n.op] body-new] gen]
    ::
        %csm
      =/  s  (rn s.op)
      =/  new  d.op
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      [[[%csm a.op s new k.op] body-new] gen]
    ::
        %rtl
      =.  info-local.gen  (~(put by info-local.gen) d.op *info-reg)
      [[op body-new] gen]
    ==
  ::
  =^  fin-new=termin  gen
    ?-    -.fin.bob
        %clq
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (rn s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      ?:  |(is-cell.info-cond ?=([~ ^] has-imm.info-cond))
        :-  [%hop ~ there.z.fin.bob]
      =.  folded.gen  &
        =.  folded.gen  &
        ::  if the branching instruction points to a block twice then we can't
        ::  delete the edge from the reversed graph since it still points to it
        ::  after the branch elimination
        ::
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.o.fin.bob o))
      ?:  |(is-loob.info-cond ?=([~ @] has-imm.info-cond))
        :-  [%hop ~ there.o.fin.bob]
        =.  folded.gen  &
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.z.fin.bob o))
      [fin.bob(s cond-new) gen]
    ::
        %eqq
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  l-new  (rn l.fin.bob)
      =/  r-new  (rn r.fin.bob)
      ?.  =(l-new r-new)  [fin.bob(l l-new, r r-new) gen]
      :-  [%hop ~ there.z.fin.bob]
      =.  folded.gen  &
      ?:  =(there.o.fin.bob there.z.fin.bob)  gen
      gen(rev (~(del ju rev.gen) there.o.fin.bob o))
    ::
        %brn
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (rn s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      ?~  has-imm.info-cond
        ?.  is-loob.info-cond  [fin.bob(s cond-new) gen]
        [[%brz cond-new z.fin.bob o.fin.bob] gen(folded &)]
      ?-    u.has-imm.info-cond
          %&
        :-  [%hop ~ there.z.fin.bob]
        =.  folded.gen  &
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.o.fin.bob o))
      ::
          %|
        :-  [%hop ~ there.o.fin.bob]
        =.  folded.gen  &
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.z.fin.bob o))
      ::
          * 
        :-  [%bom ~]
        =.  rev.gen  (~(del ju rev.gen) there.o.fin.bob o)
        =.  rev.gen  (~(del ju rev.gen) there.z.fin.bob o)
        gen
      ==
    ::
        %brz
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (rn s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      =/  zero=(unit ?)
        ?^  has-imm.info-cond  `=(0 u.has-imm.info-cond)
        ?:(is-cell.info-cond `| ~)
      ?~  zero  [fin.bob(s cond-new) gen]
      =/  [go=@uwoo cut=@uwoo]
        ?:(u.zero [there.z there.o]:fin.bob [there.o there.z]:fin.bob)
      :-  [%hop ~ go]
      =.  folded.gen  &
      ?:  =(go cut)  gen
      gen(rev (~(del ju rev.gen) cut o))
    ::
        %hop
      [fin.bob(args.t (turn args.t.fin.bob (lift rn))) gen]
    ::
        %jmp
      [fin.bob(v (turn v.fin.bob rn)) gen]
    ::
        %jmf
      [fin.bob(v (turn v.fin.bob rn)) gen]
    ::
        %jsp
      [fin.bob(s (rn s.fin.bob)) gen]
    ::
        %jsf
      [fin.bob(s (rn s.fin.bob)) gen]
    ::
        %don
      [fin.bob(s (rn s.fin.bob)) gen]
    ::
        %dox
      [fin.bob(v [(rn i.v.fin.bob) (turn t.v.fin.bob rn)]) gen]
    ::
        %bom
      [fin.bob gen]
    ==
  ::
  =.  new.gen  (~(put by new.gen) o [par-new body-new fin-new])
  =.  info.gen  (~(put by info.gen) o info-local.gen)
  =.  imms.gen  (~(put by imms.gen) o imms-local.gen)
  $(topo t.topo)
  ::
  ::  Registers keep their numbers, only eliminated ones are renamed
  ::
  ++  rn  |=(r=@uvre ^-(@uvre (~(gut by old.gen) r r)))
  ::  Intersection of two info maps, joining the facts.  The maps of two
  ::  predecessors share most of their structure, since both grew from the
  ::  map of the branching block, so this is +int:by with a shortcut for
  ::  identical subtrees instead of a walk over the whole map.
  ::
  ++  join-info
    |=  [a=(map @uvre info-reg) b=(map @uvre info-reg)]
    ^-  (map @uvre info-reg)
    |-  ^-  (map @uvre info-reg)
    ?~  b  ~
    ?~  a  ~
    ?:  =(a b)  a
    ?:  (mor p.n.a p.n.b)
      ?:  =(p.n.b p.n.a)
        %=  b
          n  [p.n.b (join-reg q.n.a q.n.b)]
          l  $(a l.a, b l.b)
          r  $(a r.a, b r.b)
        ==
      ?:  (gor p.n.b p.n.a)
        (~(uni by $(a l.a, r.b ~)) $(b r.b))
      (~(uni by $(a r.a, l.b ~)) $(b l.b))
    ?:  (gor p.n.a p.n.b)
      (~(uni by $(b l.b, r.a ~)) $(a r.a))
    (~(uni by $(b r.b, l.a ~)) $(a l.a))
  ::
  ::  Intersection of two immediates maps with the register sets intersected,
  ::  structural like +join-info
  ::
  ++  join-imms
    |=  [a=(jug * @uvre) b=(jug * @uvre)]
    ^-  (jug * @uvre)
    |-  ^-  (jug * @uvre)
    ?~  b  ~
    ?~  a  ~
    ?:  =(a b)  a
    ?:  (mor p.n.a p.n.b)
      ?:  =(p.n.b p.n.a)
        =/  v  (~(int in q.n.a) q.n.b)
        =/  l  $(a l.a, b l.b)
        =/  r  $(a r.a, b r.b)
        ?:  =(~ v)  (~(uni by l) r)
        [[p.n.b v] l r]
      ?:  (gor p.n.b p.n.a)
        (~(uni by $(a l.a, r.b ~)) $(b r.b))
      (~(uni by $(a r.a, l.b ~)) $(b l.b))
    ?:  (gor p.n.a p.n.b)
      (~(uni by $(b l.b, r.a ~)) $(a r.a))
    (~(uni by $(b r.b, l.a ~)) $(a l.a))
  ::
  ++  join-reg
    |=  [a=info-reg b=info-reg]
    ^-  info-reg
    :*  &(is-cell.a is-cell.b)
        ?&  |(is-loob.a ?=([~ ?] has-imm.a))
            |(is-loob.b ?=([~ ?] has-imm.b))
        ==
        (~(int in hed-of.a) hed-of.b)
        (~(int in tel-of.a) tel-of.b)
        ?:(=(has-hed.a has-hed.b) has-hed.a ~)
        ?:(=(has-tel.a has-tel.b) has-tel.a ~)
        ?:(=(dec-of.a dec-of.b) dec-of.a ~)
        ?:(=(has-imm.a has-imm.b) has-imm.a ~)
    ==
  ::  Info of a parameter from the arguments passed on each edge. An edge that
  ::  passes nothing is skipped; then facts naming other registers are dropped,
  ::  since those registers may be defined on the skipped edge only.
  ::
  ++  param-info
    |=  ins=(list (unit info-reg))
    ^-  info-reg
    =/  have=(list info-reg)  (murn ins same)
    ?~  have  *info-reg
    =/  joined  (roll t.have |:([a=*info-reg b=i.have] (join-reg a b)))
    ?:  =((lent have) (lent ins))  joined
    joined(hed-of ~, tel-of ~, has-hed ~, has-tel ~, dec-of ~)
  --
::  If blocks are each others ipdom and idom respectively, we can merge them
::  into one. This requires the predecessor block to have %hop as the final
::  instruction
::
++  remove-hops
  ~%  %remove-hops  ..ride  ~
  |=  $:  blocks=(map @uwoo blob)
          rev=(jar @uwoo @uwoo)
          topo=(list @uwoo)
      ==
  ^-  [changed=? (map @uwoo blob)]
  =*  gen  ,[new=(map @uwoo blob) saw=(set @uwoo)]
  =;  =gen  [!=(~ saw.gen) new.gen]
  ^-  gen
  %+  roll  topo
  |=  [o=@uwoo =gen]
  ^+  gen
  ?:  (~(has in saw.gen) o)  gen
  =/  o-new=@uwoo  o
  =/  b-new=blob  (~(got by blocks) o)
  ::  bodies of the blocks merged into it so far, latest first
  ::
  =|  segs=(list (list pole))
  |-  ^+  gen
  =*  done
    %=    gen
        new
      %+  ~(put by new.gen)  o-new
      b-new(body (zing [body.b-new (flop segs)]))
    ==
  ::
  ?.  ?=(%hop -.fin.b-new)  done
  =/  o1=@uwoo  there.t.fin.b-new
  =/  pre-o1=(list @uwoo)  (~(get ja rev) o1)
  ?<  =(~ pre-o1)
  ?.  =(pre-o1 ~[o])  done
  =.  saw.gen  (~(put in saw.gen) o1)
  =/  b1  (~(got by blocks) o1)
  =/  seg=(list pole)
    =/  args-a  args.t.fin.b-new
    =/  args-b  par.b1
    =/  ops=(list pole)  body.b1
    |-  ^-  (list pole)
    ?~  args-a
      ?^  args-b  !!
      ops
    ?~  args-b  !!
    %=  $
      args-a  t.args-a
      args-b  t.args-b
      ::  an argument that passes nothing leaves its parameter without a
      ::  definition here, where the block that held it is gone, while the
      ::  joins further on still pass the parameter along (+sect): it is
      ::  made 0, as the interpreter makes it on such an edge
      ::
      ops     ?~  i.args-a  [[%imm 0 i.args-b] ops]
              [[%mov u.i.args-a i.args-b] ops]
    ==
  ::
  $(o o1, segs [seg segs], fin.b-new fin.b1)
::  If a non-crashing op assigns to a register which is never used, we can
::  omit the op.
::  XX non-crashing direct calls
::
++  remove-dead-code
  ~%  %remove-dead-code  ..ride  ~
  |=  [blocks=(map @uwoo blob) rev-topo=(list @uwoo)]
  ^+  blocks
  =|  new=(map @uwoo blob)
  =|  saw=(set @uvre)
  |-  ^+  new
  ?~  rev-topo  new
  =/  b  (~(got by blocks) i.rev-topo)
  =;  [new-body=(list pole) saw1=(set @uvre)]
    =.  new  (~(put by new) i.rev-topo b(body new-body))
    $(rev-topo t.rev-topo, saw saw1)
  ::
  =/  old-body=(list pole)  (flop body.b)
  ::  register in the BB arguments (par.b) are only used, never assigned to.
  ::  so we don't have to save them
  ::
  =.  saw  (~(gas in saw) (get-regs fin.b))
  =|  new-body=(list pole)
  |-  ^+  [new-body saw]
  ?~  old-body  [new-body saw]
  =/  dest=(unit @uvre)  (get-reg-safe-assignment i.old-body)
  ?:  &(?=(^ dest) !(~(has in saw) u.dest))  $(old-body t.old-body)
  %=  $
    old-body  t.old-body
    new-body  [i.old-body new-body]
    saw       (~(gas in saw) (get-regs i.old-body))
  ==
::
++  trim-trace-hints
  ~%  %trim-trace-hints  ..ride  ~
  |=  [blocks=(map @uwoo blob) topo=(list @uwoo) rev=(jar @uwoo @uwoo)]
  ^+  blocks
  ::  a trace hint: %spot/%mean with its clue register, a deferred %mean
  ::  with the arm and its arguments, or a constant %mean. The hinted formula
  ::  tells nested hints with the same arguments or constant apart: the
  ::  outer one contains the inner one
  ::
  =*  key
    ^:  $%  [%clue hint=?(%spot %mean) reg=@uvre]
            [%defer a=bell v=(list @uvre) f=*]
            [%konst n=* f=*]
        ==
  ::  the key of a trace hint op, and whether it opens the hint
  ::
  =/  trace
    |=  op=pole
    ^-  (unit [open=? =key])
    ?+  op  ~
      [%hdp ?(%spot %mean) *]  `[& %clue n.op p.op]
      [%hde ?(%spot %mean) *]  `[| %clue n.op p.op]
      [%hmp *]                 `[& %defer a.op v.op f.op]
      [%hme *]                 `[| %defer a.op v.op f.op]
      [%hcp *]                 `[& %konst n.op f.op]
      [%hce *]                 `[| %konst n.op f.op]
    ==
  ::  Walk in topological order carrying the hints that are open: prologue
  ::  passed, epilogue not reached yet. A hint open at an op that could crash,
  ::  or at a terminator that could crash or leave the function, is unsafe to
  ::  drop since the stack trace would change.
  ::
  =/  unsafe=(set key)
    =|  [unsafe=(set key) out=(map @uwoo (set key))]
    |-  ^-  (set key)
    ?~  topo  unsafe
    =/  b  (~(got by blocks) i.topo)
    =/  open=(set key)
      %+  roll  (~(get ja rev) i.topo)
      |=  [p=@uwoo acc=(set key)]
      (~(uni in acc) (~(get ju out) p))
    ::
    =/  body  body.b
    |-  ^-  (set key)
    ?^  body
      =/  op  i.body
      ?^  hint=(trace op)
        ?:  open.u.hint  $(body t.body, open (~(put in open) key.u.hint))
        $(body t.body, open (~(del in open) key.u.hint))
      ?:  ?=(pole-not-crashing -.op)  $(body t.body)
      $(body t.body, unsafe (~(uni in unsafe) open))
    =?  unsafe  !?=(?(%clq %eqq %brz %hop) -.fin.b)  (~(uni in unsafe) open)
    ^$(topo t.topo, out (~(put by out) i.topo open))
  ::
  ::  An epilogue that no prologue has the key of stays: that of a trap
  ::  pushed whole where a part of its arm is not there, which ends the
  ::  frame of a prologue with another register (+soft-emit:comp)
  ::
  =/  opened=(set key)
    %-  ~(rep by blocks)
    |=  [[* b=blob] acc=(set key)]
    %+  roll  body.b
    |=  [op=pole acc=_acc]
    ?~  hint=(trace op)  acc
    ?.  open.u.hint  acc
    (~(put in acc) key.u.hint)
  ::
  %-  ~(run by blocks)
  |=  b=blob
  %_    b
      body
    %+  skip  body.b
    |=  op=pole
    ?~  hint=(trace op)  |
    ?&  !(~(has in unsafe) key.u.hint)
        (~(has in opened) key.u.hint)
    ==
  ==
::
++  remove-useless-branching
  ~%  %remove-useless-branching  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  [changed=? (map @uwoo blob)]
  %-  ~(rep by blocks)
  |=  [[o=@uwoo b=blob] changed=_| new=(map @uwoo blob)]
  =;  [epilogue=(list pole) new-fin=termin]
    :-  |(changed !=(new-fin fin.b))
    (~(put by new) o b(body (weld body.b epilogue), fin new-fin))
  ::
  ?+    -.fin.b  `fin.b
      %clq
    :-  ~
    ?>  =(~ args.z.fin.b)
    ?>  =(~ args.o.fin.b)
    =/  nex-z=blob  (~(got by blocks) there.z.fin.b)
    =/  nex-o=blob  (~(got by blocks) there.o.fin.b)
    ?.  =(nex-z nex-o)  fin.b
    [%hop ~ there.z.fin.b]
  ::
      %eqq
    ?>  =(~ args.z.fin.b)
    ?>  =(~ args.o.fin.b)
    =/  nex-z=blob  (~(got by blocks) there.z.fin.b)
    =/  nex-o=blob  (~(got by blocks) there.o.fin.b)
    ?.  =(nex-z nex-o)  `fin.b
    :-  [%equ l.fin.b r.fin.b]~
    [%hop ~ there.z.fin.b]
  ::
      %brz
    :-  ~
    ?>  =(~ args.z.fin.b)
    ?>  =(~ args.o.fin.b)
    =/  nex-z=blob  (~(got by blocks) there.z.fin.b)
    =/  nex-o=blob  (~(got by blocks) there.o.fin.b)
    ?.  =(nex-z nex-o)  fin.b
    [%hop ~ there.z.fin.b]
  ::
      %brn
    ?>  =(~ args.z.fin.b)
    ?>  =(~ args.o.fin.b)
    =/  nex-z=blob  (~(got by blocks) there.z.fin.b)
    =/  nex-o=blob  (~(got by blocks) there.o.fin.b)
    ?.  =(nex-z nex-o)  `fin.b
    :-  [%lob s.fin.b]~
    [%hop ~ there.z.fin.b]
  ==
::
++  remove-empty-middle
  ~%  %remove-empty-middle  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  [changed=? (map @uwoo blob)]
  ::  Readers are only consulted for empty blocks with parameters, see
  ::  +rewrite-hop, so they are computed only when there is such a block
  ::
  =/  readers=(jug @uvre @uwoo)
    ?.  %-  ~(any by blocks)
        |=(b=blob &(?=(^ par.b) ?=(~ body.b) ?=(%hop -.fin.b)))
      ~
    %-  ~(rep by blocks)
    |=  [[o=@uwoo b=blob] acc=(jug @uvre @uwoo)]
    =/  put  |=([r=@uvre acc=(jug @uvre @uwoo)] (~(put ju acc) r o))
    =.  acc  (roll (get-regs fin.b) put(acc acc))
    %+  roll  body.b
    |=  [op=pole acc=_acc]
    (roll (get-regs op) put(acc acc))
  ::
  |^  ^-  [? (map @uwoo blob)]
  %-  ~(rep by blocks)
  |=  [[o=@uwoo b=blob] changed=_| new=(map @uwoo blob)]
  =;  new-fin=termin
    :-  |(changed !=(new-fin fin.b))
    (~(put by new) o b(fin new-fin))
  ?+    -.fin.b  fin.b
      %clq  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
      %eqq  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
      %brn  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
      %brz  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
      %hop  fin.b(t (rewrite-hop t.fin.b))
  ==
  ::  Bypass an empty block on a branch edge. Only when nothing is passed
  ::  along: the edge could be critical and arguments on it would have no
  ::  block to be moved in.
  ::
  ++  rewrite-jump
    |=  j=jmp
    ^-  jmp
    ?.  =(~ args.j)  j
    =/  nex  (~(got by blocks) there.j)
    ?>  =(~ par.nex)
    ?.  =(~ body.nex)        j
    ?.  ?=(%hop -.fin.nex)   j
    ?.  =(~ args.t.fin.nex)  j
    $(j t.fin.nex)
  ::  Bypass an empty block on a hop edge. A hop is its block's only exit, so
  ::  the edge is never critical and can carry arguments: the parameters of
  ::  the bypassed block are substituted by what the hop passes to them. The
  ::  parameters must not be read anywhere else, they lose their definition.
  ::
  ++  rewrite-hop
    |=  j=jmp
    ^-  jmp
    =/  nex  (~(got by blocks) there.j)
    ?.  =(~ body.nex)        j
    ?.  ?=(%hop -.fin.nex)   j
    ?.  %+  levy  par.nex
        |=(p=@uvre =(~ (~(del in (~(get ju readers) p)) there.j)))
      j
    =/  sub=(map @uvre (unit @uvre))
      =|  sub=(map @uvre (unit @uvre))
      =/  par   par.nex
      =/  args  args.j
      |-  ^+  sub
      ?~  par  ?>(?=(~ args) sub)
      ?>  ?=(^ args)
      $(par t.par, args t.args, sub (~(put by sub) i.par i.args))
    ::
    =/  pass  |=(a=(unit @uvre) ?~(a ~ (~(gut by sub) u.a a)))
    $(there.j there.t.fin.nex, args.j (turn args.t.fin.nex pass))
  --
::
::  The optimized IR has one more branch: %lti, the step of a binary
::  search among the constants a register is compared with
::
+$  termin-out
  $%  termin
      [%lti n=@ s=@uvre z=jmp o=jmp]    ::  ?:  (lth s n), s a direct atom
  ==
+$  blob-out  [par=(list @uvre) body=(list pole) fin=termin-out]
+$  straight-out
  [need=need-ordered n-args=@ud blocks=(map @uwoo blob-out)]
::  A ?- over a head-tagged union compiles to a chain of tests of the head
::  of one register .s against constants, each test in blocks of its own:
::
::    P:  [%clq s Y N]
::    Y:  [%hed s d]  [%imm c r]  [%eqq d r hit N]
::    N:  the next test, or what follows the last
::
::  which is a linear search: +open:ap has eighty cases.  A chain of four
::  tests or more, of direct atoms, becomes a binary search: the cell test
::  and the head once, %lti by the sorted constants, and one %eqq against
::  the constant found.  The first of equal constants wins, as in the
::  chain; the blocks of the chain are those of the tree.
::
::  A ?- or a ?+ over atoms (a tag already fetched, a character) compiles
::  to a chain of plain tests of one register .d, each ending a block:
::
::    P:  ..  [%imm c r]  [%eqq d r hit N]
::    N:  [%imm c' r']  [%eqq d r' hit' N']
::
::  and becomes a binary search the same way.  %lti takes any noun: a cell
::  or an indirect atom is above every direct atom, and the %eqq at the
::  leaf then misses.
::
++  switch-chains
  ~%  %switch-chains  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  (map @uwoo blob-out)
  =/  topo=(list @uwoo)  (bb-topo blocks)
  =/  rev=(jar @uwoo @uwoo)  (rev-cfg blocks (sy topo))
  ::  how many times each register is mentioned
  ::
  =/  uses=(map @uvre @ud)
    =/  put
      |=  [r=@uvre acc=(map @uvre @ud)]
      (~(put by acc) r +((~(gut by acc) r 0)))
    %-  ~(rep by blocks)
    |=  [[o=@uwoo b=blob] acc=(map @uvre @ud)]
    =.  acc  (roll par.b put(acc acc))
    =.  acc  (roll (get-regs fin.b) put(acc acc))
    %+  roll  body.b
    |=  [op=pole acc=_acc]
    (roll (get-regs op) put(acc acc))
  ::  the test that the block .p ends with, if it does: of the head .d of
  ::  .s against the constant .c in .r, to .hit or .miss, in the block .y
  ::
  =*  test  ,[s=@uvre c=@ hit=@uwoo miss=@uwoo y=@uwoo d=@uvre r=@uvre]
  =/  test-of
    |=  p=@uwoo
    ^-  (unit test)
    =/  b=blob  (~(got by blocks) p)
    ?.  ?=([%clq * [~ *] [~ *]] fin.b)  ~
    =/  y=@uwoo  there.z.fin.b
    =/  n=@uwoo  there.o.fin.b
    ?.  =(~[p] (~(get ja rev) y))  ~
    =/  yb=blob  (~(got by blocks) y)
    ?.  ?=(~ par.yb)  ~
    ?.  ?=([%eqq * * [~ *] [~ *]] fin.yb)  ~
    ?.  =(n there.o.fin.yb)  ~
    =/  bod=(list pole)  body.yb
    ?.  ?=([* * ~] bod)  ~
    =/  h=(unit [s=@uvre d=@uvre])
      ?:  ?=([%hed *] i.bod)    `[s d]:i.bod
      ?:  ?=([%hed *] i.t.bod)  `[s d]:i.t.bod
      ~
    =/  m=(unit [n=* d=@uvre])
      ?:  ?=([%imm *] i.bod)    `[n d]:i.bod
      ?:  ?=([%imm *] i.t.bod)  `[n d]:i.t.bod
      ~
    ?~  h  ~
    ?~  m  ~
    ?.  =(s.u.h s.fin.b)  ~
    =/  c=*  n.u.m
    ?.  ?=(@ c)  ~
    ?.  (lth c (bex 31))  ~
    ?.  ?|  =([l r]:fin.yb [d.u.h d.u.m])
            =([l r]:fin.yb [d.u.m d.u.h])
        ==
      ~
    ?.  ?&  =(2 (~(gut by uses) d.u.h 0))
            =(2 (~(gut by uses) d.u.m 0))
        ==
      ~
    `[s.fin.b c there.z.fin.yb n y d.u.h d.u.m]
  ::  the tests chained from the one of .p: the miss of each is a block
  ::  with nothing but the next test, of the same register, reached from
  ::  that test only
  ::
  =/  chain-of
    |=  p=@uwoo
    ^-  (list test)
    =/  t=(unit test)  (test-of p)
    ?~  t  ~
    :-  u.t
    =/  nb=blob  (~(got by blocks) miss.u.t)
    ?.  &(?=(~ par.nb) ?=(~ body.nb))  ~
    =/  rev-miss  (~(get ja rev) miss.u.t)
    ?.  |(=(rev-miss ~[p y.u.t]) =(rev-miss ~[y.u.t p]))  ~
    =/  t2=(unit test)  (test-of miss.u.t)
    ?~  t2  ~
    ?.  =(s.u.t2 s.u.t)  ~
    $(p miss.u.t)
  ::
  ::  the plain test that the block .p ends with, if it does: of the
  ::  register .d against the constant .c, put in .r by the block, to .hit
  ::  or .miss
  ::
  =*  plain  ,[d=@uvre c=@ hit=@uwoo miss=@uwoo r=@uvre]
  =/  plain-of
    |=  p=@uwoo
    ^-  (unit plain)
    =/  b=blob  (~(got by blocks) p)
    ?.  ?=([%eqq * * [~ *] [~ *]] fin.b)  ~
    =/  m=(unit [n=* d=@uvre])
      =/  bod=(list pole)  body.b
      |-  ^-  (unit [n=* d=@uvre])
      ?~  bod  ~
      ?:  ?&  ?=([%imm *] i.bod)
              |(=(d.i.bod l.fin.b) =(d.i.bod r.fin.b))
          ==
        `[n d]:i.bod
      $(bod t.bod)
    ?~  m  ~
    =/  c=*  n.u.m
    ?.  ?=(@ c)  ~
    ?.  (lth c (bex 31))  ~
    ?:  =(l.fin.b r.fin.b)  ~
    ?.  =(2 (~(gut by uses) d.u.m 0))  ~
    =/  d=@uvre  ?:(=(d.u.m l.fin.b) r.fin.b l.fin.b)
    `[d c there.z.fin.b there.o.fin.b d.u.m]
  ::  the plain tests chained from the one of .p, with their blocks: the
  ::  miss of each is a block with nothing but the constant and the test of
  ::  the next, of the same register, reached from that test only
  ::
  =/  plains-of
    |=  p=@uwoo
    ^-  (list [p=@uwoo t=plain])
    =/  t=(unit plain)  (plain-of p)
    ?~  t  ~
    :-  [p u.t]
    =/  nb=blob  (~(got by blocks) miss.u.t)
    ?.  ?=(~ par.nb)  ~
    ?.  ?=([[%imm *] ~] body.nb)  ~
    ?.  =(~[p] (~(get ja rev) miss.u.t))  ~
    =/  t2=(unit plain)  (plain-of miss.u.t)
    ?~  t2  ~
    ?.  =(d.u.t2 d.u.t)  ~
    $(p miss.u.t)
  ::  the cases of a chain, the first of each constant, by the constants
  ::
  =*  case  ,[c=@ hit=@uwoo r=@uvre]
  =/  cases
    |=  ces=(list case)
    ^-  (list case)
    =|  [saw=(set @) acc=(list case)]
    |-  ^+  acc
    ?~  ces  (sort acc |=([a=[c=@ *] b=[c=@ *]] (lth c.a c.b)))
    ?:  (~(has in saw) c.i.ces)  $(ces t.ces)
    $(ces t.ces, saw (~(put in saw) c.i.ces), acc [i.ces acc])
  ::  the tree of a binary search over the cases .cas of the register .d,
  ::  .mis where no case leads: the body and the end of its root; the other
  ::  nodes are put in .out under the labels .ids
  ::
  =/  tree
    |=  $:  cas=(list case)
            d=@uvre
            mis=@uwoo
            ids=(list @uwoo)
            out=(map @uwoo blob-out)
        ==
    ^-  $:  body=(list pole)
            fin=termin-out
            ids=(list @uwoo)
            out=(map @uwoo blob-out)
        ==
    ?>  ?=(^ cas)
    ?:  ?=(~ t.cas)
      :*  ~[[%imm c.i.cas r.i.cas]]
          [%eqq d r.i.cas [~ hit.i.cas] [~ mis]]
          ids
          out
      ==
    =/  all=(list case)  cas
    =/  haf=@ud  (div (lent all) 2)
    =/  hi=(list case)  (slag haf all)
    ?>  ?=(^ hi)
    ?>  ?=([* * *] ids)
    =/  [l-id=@uwoo r-id=@uwoo]  [i.ids i.t.ids]
    =/  l  $(cas (scag haf all), ids t.t.ids)
    =.  out.l  (~(put by out.l) l-id [~ body.l fin.l])
    =/  r  $(cas hi, ids ids.l, out out.l)
    =.  out.r  (~(put by out.r) r-id [~ body.r fin.r])
    [~ [%lti c.i.hi d [~ l-id] [~ r-id]] ids.r out.r]
  ::
  =/  out=(map @uwoo blob-out)  blocks
  =|  done=(set @uwoo)
  ::  the first label that no block has
  ::
  =/  nex=@uwoo
    %+  roll  ~(tap in ~(key by blocks))
    |=([o=@uwoo m=@uwoo] ?:((gte o m) `@uwoo`+(o) m))
  |-  ^-  (map @uwoo blob-out)
  ?~  topo  out
  ?:  (~(has in done) i.topo)  $(topo t.topo)
  =/  cs=(list test)  (chain-of i.topo)
  ?:  (gte (lent cs) 4)
    ?>  ?=(^ cs)
    =/  s=@uvre  s.i.cs
    =/  d=@uvre  d.i.cs
    =/  top=@uwoo  y.i.cs
    =/  mis=@uwoo  miss:(rear `(list test)`cs)
    ::  the blocks of the chain but its first two: those of the tree
    ::
    =/  ids=(list @uwoo)
      %+  weld  (turn t.cs |=(t=test y.t))
      (turn (snip `(list test)`cs) |=(t=test miss.t))
    =.  done  (~(gas in done) ids)
    =.  out  (roll ids |=([o=@uwoo acc=_out] (~(del by acc) o)))
    =/  cas=(list case)
      (cases (turn `(list test)`cs |=(t=test [c hit r]:t)))
    =/  node  (tree cas d mis ids out)
    =.  out  out.node
    =.  out  (~(put by out) top [~ [[%hed s d] body.node] fin.node])
    =/  b=blob  (~(got by blocks) i.topo)
    =.  out  (~(put by out) i.topo b(fin [%clq s [~ top] [~ mis]]))
    $(topo t.topo)
  ::  a chain of plain tests: the root of the tree ends the first block,
  ::  the other nodes take the blocks of the chain and new ones
  ::
  =/  ps=(list [p=@uwoo t=plain])  (plains-of i.topo)
  ?:  (lth (lent ps) 4)  $(topo t.topo)
  ?>  ?=(^ ps)
  =/  d=@uvre  d.t.i.ps
  =/  mis=@uwoo  miss.t:(rear `(list [p=@uwoo t=plain])`ps)
  =/  old=(list @uwoo)  (turn t.ps |=([p=@uwoo *] p))
  =.  done  (~(gas in done) old)
  =.  out  (roll old |=([o=@uwoo acc=_out] (~(del by acc) o)))
  =/  cas=(list case)
    (cases (turn `(list [p=@uwoo t=plain])`ps |=([* t=plain] [c hit r]:t)))
  ::  a tree of k leaves has 2k-1 nodes, and the root has a block
  ::
  =/  ned=@ud  (sub (mul 2 (lent cas)) 2)
  =^  ids=(list @uwoo)  nex
    =/  ids=(list @uwoo)  (scag ned old)
    |-  ^-  [(list @uwoo) @uwoo]
    ?:  (gte (lent ids) ned)  [ids nex]
    $(ids [nex ids], nex `@uwoo`+(nex))
  =/  node  (tree cas d mis ids out)
  =.  out  out.node
  =/  b=blob  (~(got by blocks) i.topo)
  =/  bod=(list pole)
    %+  skip  body.b
    |=(op=pole &(?=([%imm *] op) =(d.op r.t.i.ps)))
  =.  out  (~(put by out) i.topo [par.b (weld bod body.node) fin.node])
  $(topo t.topo)
::
++  optimize
  ~%  %optimize  ..ride  ~
  |=  s=straight
  ^-  straight-out
  =.  s
    |-  ^-  straight
    =^  changed=?  s  (optimize-once s)
    ?.  changed  s
    $(s s)
  ::
  s(blocks (switch-chains blocks.s))
::  One round of all the optimization passes.  Every pass says whether it
::  changed anything, so that the fixed point is known without another round.
::  +remove-hops and +alias only ever delete blocks and edges, so the reverse
::  postorder computed up front stays valid once filtered.
::
++  optimize-once
  ~%  %optimize-once  ..ride  ~
  |=  s=straight
  ^-  [again=? straight]
  ::  Structural cleanup first, to a fixed point: it is cheap and it lets
  ::  +alias see merged blocks right away instead of a round later
  ::
  =/  topo  (bb-topo blocks.s)
  =/  rev  (rev-cfg blocks.s (sy topo))
  =^  [topo=(list @uwoo) rev=(jar @uwoo @uwoo)]  blocks.s
    |-  ^-  [[(list @uwoo) (jar @uwoo @uwoo)] (map @uwoo blob)]
    =^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)
    =^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)
    =^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)
    ?.  |(c-hops c-branch c-middle)  [[topo rev] blocks.s]
    =.  topo  (bb-topo blocks.s)
    =.  rev  (rev-cfg blocks.s (sy topo))
    $
  ::
  =^  f-alias=?  blocks.s  (alias n-args.s blocks.s rev topo)
  =.  topo  (skim topo ~(has by blocks.s))
  =.  rev  (rev-cfg blocks.s (sy topo))
  ::  Trimming hints can leave their token registers dead, so dead code goes
  ::  after it
  ::
  =.  blocks.s  (trim-trace-hints blocks.s topo rev)
  =.  blocks.s  (remove-dead-code blocks.s (flop topo))
  ::  Another round is needed only if +alias folded a branch or dropped a
  ::  block, or if the structure can be cleaned up further after the op
  ::  eliminations.  Op eliminations alone never make +alias more precise.
  ::
  =^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)
  =^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)
  =^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)
  [|(f-alias c-hops c-branch c-middle) s]
--
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Arvo-shaped core for stateful interaction with SKA code
::
::    Persistent memoization is used in some places instead of explicit state,
::    perhaps more out of laziness than for a good reason. Because of that SKA
::    core needs to be evaluated with scrying disabled for persistent memoiza-
::    tion to work.
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
|%
+$  ovum
  $%  [%full sub=* fol=^]
      [%jets p=(list (pair ring jets-comp-info))]
      [%dire b=bell mono=?]
      [%fast reset=? p=(list [pax=path =sock])]
  ==
::  %ir carries the registrations the analysis made, parents first, with
::  the clues of their hints, for vere to keep and to register the cores.
::  %drop: the functions whose compiled forms a change of the jets invalidated
::
+$  prod
  $@  ~
  $%  [%ir b=bell p=straight-out new=(list [pax=path tem=sock clue=*])]
      [%drop p=(list bell)]
  ==
::  The state of a core of any version, for +load
::
+$  state-0  [%0 =long-ska jets-hot=jets-comp cache=comp-cache]
+$  state-any  $%(state-0)
::
++  validate-ovum
  |=  n=*
  ^-  ovum
  =;  out  =+(=(n out) out)
  ?@  n  !!
  ?+    -.n  !!
      ?(%full %jets %fast)  ;;(ovum n)
      %dire
    ?.  ?=([%dire b=* mono=?] n)  !!
    n(b (validate-bell b.n))
  ==
::
++  validate-bell
  |=  n=*
  ^-  bell
  =;  out  =+(=(n out) out)
  ?>  ?=([[cape=* data=*] fol=^] n)
  [[(validate-cape cape.n) data.n] fol.n]
::
++  validate-cape
  |=  n=*
  ^-  cape
  =;  out  =+(=(n out) out)
  =*  val  .
  ?@  n
    ?>  ?=(? n)
    n
  ~+
  [(val -.n) (val +.n)]
::  The rings whose drivers differ between two hot states
::
++  hot-diff
  |=  [a=jets-comp b=jets-comp]
  ^-  (set ring)
  %-  ~(rep by (~(uni by a) b))
  |=  [[r=ring *] acc=(set ring)]
  ?:  =((~(get by a) r) (~(get by b) r))  acc
  (~(put in acc) r)
::  The functions whose compiled forms changes of the jets invalidated, as the
::  need of a callee goes into the need of its caller: those with rings whose
::  drivers differ, those that got a ring with a driver, and their transitive
::  callers
::
++  hot-stale
  |=  [rings=(set ring) rung=(set bell) hot=jets-comp lon=long-ska]
  ^-  (set bell)
  =/  rev=(jug bell bell)  (reverse-bell-graph calls.lon)
  =/  driven=(set bell)
    %-  ~(rep in rung)
    |=  [b=bell acc=(set bell)]
    ?.  (~(has by hot) (~(got by call.cole.jets.lon) b))  acc
    (~(put in acc) b)
  ::
  =/  q=(list bell)
    %-  ~(rep in rings)
    |=  [r=ring acc=_~(tap in driven)]
    (weld ~(tap in (~(get ju back.cole.jets.lon) r)) acc)
  ::
  =|  out=(set bell)
  |-  ^+  out
  ?~  q  out
  ?:  (~(has in out) i.q)  $(q t.q)
  $(q (weld ~(tap in (~(get ju rev) i.q)) t.q), out (~(put in out) i.q))
::
++  del-bells
  |=  [m=(map bell straight) s=(set bell)]
  ^+  m
  (~(rep in s) |=([b=bell =_m] (~(del by m) b)))
--
::
=|  state=state-0
|%
++  version  -.state
::  a function compiled as one of its whole subject, from the cache or made
::  and cached, with its SCC
::
++  compiled-mono
  |=  [b=bell scc=(set bell)]
  ^-  [straight _cache.state]
  ?^  s=(~(get by mono.cache.state) b)  [u.s cache.state]
  =^  [=straight n-ary=(map bell straight)]  cache.state
    %-  compile-unary
    [b scc [code jets calls held]:long-ska.state jets-hot.state cache.state]
  ::
  [straight cache.state(mono (~(put by mono.cache.state) b straight))]
::  a function compiled as one of the parts of its subject it uses, from the
::  cache or made and cached with its SCC
::
++  compiled-nary
  |=  [b=bell scc=(set bell)]
  ^-  [straight _cache.state]
  ?^  s=(~(get by nary.cache.state) b)  [u.s cache.state]
  =^  m=(map bell straight)  cache.state
    %-  compile-scc
    [scc [code jets calls held]:long-ska.state jets-hot.state cache.state]
  ::
  [(~(got by m) b) cache.state]
--
::
|%
::  This core with the state of an installed core of any version, at the same
::  axis of all of them. Functions compiled by another version don't hold
::
++  load      ::  +4
  |=  old=[* * state=state-any *]
  ^+  ..load
  ?-  -.state.old
    %0
      %=  ..load
        state
          %=  state.old
            nary.cache  ~
            mono.cache  ~
            rets.cache  ~
            inl.cache   ~
            sure.cache  ~
          ==
      ==
  ==
::
++  peek      ::  +22
  |=  pax=path
  ^-  (unit (pair @tas *))
  ?+  pax  ~
    [%ver ~]  `[%ud `@ud`version]
  ==
::
++  poke      ::  +23
  |=  ovo=*
  ^-  [prod _..poke]
  =/  ovo
    ~_  'ska: malformed ovum'
    (validate-ovum ovo)
  ::
  ?-    -.ovo
      %jets
    =/  hot=jets-comp  (malt p.ovo)
    ?:  &(=(hot jets-hot.state) =(~ pend.jets.long-ska.state))
      [[%drop ~] ..poke]
    =^  rung=(set bell)  long-ska.state
      (ska-cole-settle long-ska.state ~(key by hot))
    =/  stale=(set bell)
      (hot-stale (hot-diff jets-hot.state hot) rung hot long-ska.state)
    ::
    :-  [%drop ~(tap in stale)]
    %=  ..poke
      jets-hot.state    hot
      nary.cache.state  (del-bells nary.cache.state stale)
      mono.cache.state  (del-bells mono.cache.state stale)
      rets.cache.state
        (~(rep in stale) |=([b=bell m=_rets.cache.state] (~(del by m) b)))
      inl.cache.state
        (~(rep in stale) |=([b=bell m=_inl.cache.state] (~(del by m) b)))
    ::
      sure.cache.state
        (~(rep in stale) |=([b=bell m=_sure.cache.state] (~(del by m) b)))
    ==
  ::
      %fast
    =/  old=(jug path sock)  core.jets.long-ska.state
    =/  reg=regs
      ?:  reset.ovo  *regs
      [root core batt arms ~]:jets.long-ska.state
    ::  no clue: vere registered these itself
    ::
    =.  reg
      %+  roll  p.ovo
      |=  [[pax=path tem=sock] =_reg]
      (register-template pax tem ~ reg)
    ::
    =.  jets.long-ska.state
      %=  jets.long-ska.state
        root  root.reg
        core  core.reg
        batt  batt.reg
        arms  arms.reg
      ==
    ::
    =/  cole  call.cole.jets.long-ska.state
    =.  long-ska.state
      ?:  reset.ovo
        (ska-cole-restore long-ska.state ~(key by jets-hot.state))
      %=  long-ska.state
        pend.jets  ((uni-ju pend.jets.long-ska.state) ((dif-ju core.reg) old))
      ==
    ::  compiled functions call through the rings: none holds if those
    ::  changed
    ::
    =?  nary.cache.state  !=(cole call.cole.jets.long-ska.state)  ~
    =?  mono.cache.state  !=(cole call.cole.jets.long-ska.state)  ~
    =?  rets.cache.state  !=(cole call.cole.jets.long-ska.state)  ~
    =?  inl.cache.state  !=(cole call.cole.jets.long-ska.state)  ~
    =?  sure.cache.state  !=(cole call.cole.jets.long-ska.state)  ~
    ::
    [~ ..poke]
  ::
      %full
    ::  The analysis and the compiler run compiled themselves: vere runs the
    ::  formula of a %ska hint compiled, but in a poke of this core made from
    ::  inside another one (this core compiling its own code), where it runs
    ::  in u3n (vere's u3a_flag_ska)
    ::
    =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
      ~>  %ska
      (ska-poke [&+sub.ovo fol.ovo] long-ska.state ~(key by jets-hot.state))
    ::  what is compiled holds, as do the SCCs: no new function joins an old
    ::  one's, and a function seen before keeps its ring until +ska-cole-settle
    ::
    ::  An entry that is a jetted arm itself, as when a gate that the caller
    ::  did not know is slammed on its battery: by subject through the ring,
    ::  as a caller that knew it would call it.  The driver runs, and the
    ::  arm's own program, which %dire compiles, only if the driver punts.
    ::  Else the body of the arm would run as Nock where u3n runs the jet
    ::
    =/  rin=(unit ring)  (~(get by call.cole.jets.long-ska.state) func)
    ?:  &(?=(^ rin) (~(has by jets-hot.state) u.rin))
      =/  out=straight-out
        :+  [%this ~]  1
        (~(put by *(map @uwoo blob-out)) `@uwoo`0 [~ ~ [%jsf func `@uvre`0 u.rin]])
      ::
      [[%ir func out new] ..poke]
    =^  scc=(set bell)  sccs.cache.state
      (scc-of func calls.long-ska.state sccs.cache.state)
    =^  =straight  cache.state  ~>(%ska (compiled-mono func scc))
    ::
    =/  out=straight-out  ~>(%ska (optimize straight))
    :_  ..poke
    [%ir func out new]
  ::
      %dire
    =^  scc=(set bell)  sccs.cache.state
      (scc-of b.ovo calls.long-ska.state sccs.cache.state)
    =^  =straight  cache.state
      ~>  %ska
      ?:  mono.ovo  (compiled-mono b.ovo scc)
      (compiled-nary b.ovo scc)
    ::
    =/  out=straight-out  ~>(%ska (optimize straight))
    [[%ir b.ovo out ~] ..poke]
  ==
::
++  wish  !!  ::  +10
--