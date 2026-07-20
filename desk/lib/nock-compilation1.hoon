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
::    Once the function call graph is obtained with partial evaluation of the
::    given subject/formula pair, the next step is to discover which parts of
::    the subject are actually used as data by each function.  Without it each
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
::    Call graph construction:  line 511
::    Axis usage analysis:      line 2127
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
=/  ska-verb  ~
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
=*  stub  ~|(%stub !!)
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
::
+$  sock  $~(|+~ [=cape data=*])
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
  ~%  %ca  ..zuse  ~
  |%
  ::  all is known
  ::
  ++  all
    |=  c=cape
    ^-  ?
    ?@  c  c
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
  ~%  %so  ..zuse  ~
  |%
  ::  Does b nest under a? i.e. is everything that is known by a also known
  ::  by b?
  ::
  ++  huge
    ~/  %huge
    |=  [one=sock two=sock]
    ^-  ?
    ?:  =(one two)  &
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
  ::  axis of a partial noun, never fails
  ::
  ++  pull
    ~/  %pull
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
  ::  cons
  ::
  ++  knit
    ~/  %knit
    |=  [one=sock two=sock]
    ^-  sock
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
    ~/  %pack
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
    ~/  %darn
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
  --
::  Operations on provenance
::
++  pi
  ~%  %pi  ..zuse  ~
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
  ~%  %distribute  ..zuse  ~
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
  ~%  %double-int  ..zuse  ~
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
::    The implementation below works by finding a fixed point of a function F
::    that maps a set of SKA function calls onto itself by, formally, partially
::    evaluating each callsite in the set, using the information from the
::    previous set for Nock 2 handling.  De facto this means breadth-first
::    iteration over the call graph with back-propagation of changes. This
::    appears to be the same thing as "chaotic iteration over a lattice" in
::    literature.
::
::    The algorithm assumes that the set of SKA function calls forms a complete
::    lattice, and the fixed point is found via Kleene iteration, starting from
::    the least element of the lattice that contains the root call.
::
::    Proving that F is monotonic for some ordering of the lattice, for which
::    [[[&+sub fol] *datum] ~ ~] is the least element of the lattice which
::    contains [&+sub fol] is left as an exercise for the reader. The hardest
::    part IMO is taking into account recursive calls. The rest is trivial:
::    socks for a given noun form a complete lattice with huge:so as partial
::    ordering, and we only grow products and code requirements. The only place
::    where the code requirement shrinks is going from a recursive call to a new
::    non-recursive call. However, a non-recursive call can never become recur-
::    sive again, which appears to bring some other kind of monotonicity.
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Partial noun datatypes bunt to their bottom elements
::
?>  =(|+~ *sock)
?>  =(| *cape)
?>  =(~ *spring)
|%
+$  identity  [more=sock fol=^]  ::  max subject
+$  bell      [less=sock fol=^]   ::  minimized subject
+$  nomm
  $~  [%0 0]
  $^  [nomm nomm]
  $%  [%0 p=@]
      [%1 p=*]
      [%2 p=nomm q=nomm info=(unit [b=bell k=(unit *)])]
      [%3 p=nomm]
      [%4 p=nomm]
      [%5 p=nomm q=nomm]
      [%6 p=nomm q=nomm r=nomm]
      [%7 p=nomm q=nomm]
      [%10 p=[p=_`@`1 q=nomm] q=nomm]  ::  p.p != 0
      [%11 p=$@(@ [p=@ q=nomm]) q=nomm body=*]
      [%12 p=nomm q=nomm]
  ==
+$  spring  *  ::  no union stuff
::  seat: callsite location
::  id:   identity of the callee
::
+$  callee-entry  [seat=(unit spot) id=identity]
::  A callgraph entry:
::    callees: immediate callees
::    nomm: SKA code of that function, with direct %2's annotated
::    less-code: subject requirement for a call: subject with only the parts
::               that are used as code transitively
::    less-memo: less-code + parts of the subject that might've been captured
::               by the product.
::    indi: parts of the subject that were transitively used as code but which
::          didn't have data to make a direct call
::    prod/map: product of the function with less-memo as the input subject
::    area: (approximate) location of the function's body
::
+$  datum
  $:  callees=(set callee-entry)
      =nomm
      less-code=sock
      less-memo=sock
      indi=cape
      [prod=sock map=spring]
      area=(unit spot)
  ==
::
+$  callgraph  (map identity datum)
::  A graph of functions
::
+$  jug-id  (jug identity identity)
+$  worklist  (set identity)
::  memoization map
::  formula -> less-memo -> entry
::
+$  memo  (map ^ (map sock [id=identity =datum]))
+$  sock-anno  [=sock src=spring]
+$  ring  [=path axe=@]
+$  code-entry  [=nomm pure=?]
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
        $=  cole              ::  bell <--> ring bidirectional mapping
        $:  call=(map bell ring)
            back=(jug ring bell)
    ==  ==
  ::::  finalized graph views: 
    ::
    $=  final
    $:  =memo
        graph=callgraph  :: pruned
    ==
  ::::  saved entries:
    ::
    code=(map bell code-entry)        ::  direct bell mapping
    fols=(map ^ (map bell code-entry))  ::  lookup by formula
  ==
--
::
|%
++  put-fols
  |=  [b=bell en=code-entry fols=(map ^ (map bell code-entry))]
  ^+  fols
  =/  m=(map bell code-entry)  (~(gut by fols) fol.b ~)
  (~(put by fols) fol.b (~(put by m) b en))
::  Iterate over a set with a gate (a -> (unit b)) until we get a nonempty
::  product
::
++  set-first-match
  |*  [s=(set) g=$-(* (unit))]
  ^+  $:g
  ?~  s  ~
  ?^  res=(g n.s)  res
  =/  l  $(s l.s)
  ?^  l  l
  $(s r.s)
::  Check if "big" homeomorphically embeds "smol".
::
++  he-sock
  ~%  %he-sock  ..zuse  ~
  |=  [big=sock smol=sock]
  ^-  ?
  =*  h-e  .
  ?:  =(big smol)  &
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
::  Most specific generalization of two socks. Disagreeing parts are replaced
::  with an unknown element |+~. Note that this has different behavior and
::  intent compared to +msg-ca.
::
++  msg-sock
  |=  [a=sock b=sock]
  ^-  sock
  =*  msg  .
  ?:  =(a b)  a
  ?:  |(?=(@ cape.a) ?=(@ cape.b))  |+~
  ~+
  %+  knit:so  (msg [-.cape -.data]:a [-.cape -.data]:b)
  (msg [+.cape +.data]:a [+.cape +.data]:b)
::  If we have the transitive clojure of the reversed callgraph, we can
::  use this function to detect recursive calls.
::  XX HE
::
++  recursive-call-tcb
  |=  [id-caller=identity id-kid=identity tcb=jug-id g=callgraph]
  ^-  (unit [id=identity d=datum])
  =/  fast-match=(unit [id=identity d=datum])
    ?.  =(fol.id-kid fol.id-caller)  ~
    =/  d=datum  (git-g g id-caller)
    ?:  (huge:so less-code.d more.id-kid)  `[id-caller d]
    ~
  ::
  ?^  fast-match  fast-match
  %+  set-first-match  (~(get ju tcb) id-caller)
  |=  tr-caller=identity
  ?.  =(fol.id-kid fol.tr-caller)  ~
  =/  d=datum  (git-g g tr-caller)
  ?:  (huge:so less-code.d more.id-kid)  `[tr-caller d(prod |+~, map ~)]
  ~
::  Check if a given call "id-kid" might be a recursive call to a function
::  "id-caller" or one of its transitive callers. Also check if id-kid's subject
::  homeomorphically embeds the subject of one of its transitive callers, mas-
::  king out the accumulating part with +msg-sock. This is done to stop infinite
::  chains of dynamically generated functions.
::
::  Chains before HE firing are theoretically finite but could be V A S T (see
::  TREE(3) to get the sense of scale); however in testing I could not construct
::  an example where a chain of functions would grow faster than linearly with
::  the size of the formula and the subject: the products would get masked down
::  with either the simple recursion pessimization (we erase the product of
::  simple recursive calls), or with +double-int as we intersect nouns on both
::  their values and provenances.
::
++  recursive-call
  ~%  %recursive-call  ..zuse  ~
  |=  [id-caller=identity id-kid=identity called-by=jug-id g=callgraph]
  ^-  (unit [id=identity d=datum])
  =|  visited=(set identity)
  =/  callers=(list identity)  ~[id-caller]
  |-  ^-  (unit [id=identity d=datum])
  =*  visit-loop  $
  ?:  =(~ callers)  ~
  =/  l=(list identity)  callers
  |-  ^-  (unit [id=identity d=datum])
  =*  l-loop  $
  ?^  l
    ?.  =(fol.id-kid fol.i.l)  l-loop(l t.l)
    =/  d=datum  (git-g g i.l)
    ?:  (huge:so less-code.d more.id-kid)
      `[i.l d(prod |+~, map ~)]
    ?:  (he-sock more.id-kid more.i.l)
      =/  id-msg=identity  [(msg-sock more.id-kid more.i.l) fol.id-kid]
      `[id-msg (git-g g id-msg)]
    l-loop(l t.l)
  =.  visited  (~(gas in visited) callers)
  %=    visit-loop
      callers
    %-  skip  :_  ~(has in visited)
    %~  tap  in  %-  silt
    ^-  (list identity)
    %-  zing
    %+  turn  callers
    |=  id=identity
    ~(tap in (~(get ju called-by) id))
  ==
::  A noun with provenance "src" captured something from subject "less"
::
++  unknown-sock-captured
  |=  [src=spring less=sock]
  ^-  ?
  ?~  src  |
  ?^  src  |($(src -.src) $(src +.src))
  =/  part=cape  cape:(pull:so less src)
  |-  ^-  ?
  ?@  part  !part
  |($(part -.part) $(part +.part))
::  Memoization core
::
++  mi
  |%
  ++  gut
    |=  [m=memo f=^]
    ^-  (map sock [identity datum])
    (~(gut by m) f ~)
  ::  Get a memoization hit, not necessarily the best one. Although
  ::  we do not memoize functions that captured anything from their subjects
  ::  and we check that we don't have any data in the places where the memo can-
  ::  didate tried to get code, so it should already be the best match?
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
            =/  c=cape  cape:(app:ca indi.d.i.entries s)
            ?=(%| c)
        ==
      `[id d]:i.entries
    $(entries t.entries)
  ::  Memoize, if unknown parts of the subject were not captured.
  ::
  ++  put
    ~%  %put-mi  ..zuse  ~
    |=  [m=memo id=identity d=datum]
    ^-  memo
    ::  if some part of the captured subject is unknown, do not memoize
    ::  to prevent deoptz
    ::  i.e. the result needs to be fully known wherever it captures the subject
    ::  in order to memoize the call
    ::
    ?:  (unknown-sock-captured map.d less-memo.d)  m
    =/  inner  (gut m fol.id)
    =.  inner  (~(put by inner) less-memo.d [id d])
    (~(put by m) fol.id inner)
  --
::
++  git-g
  |=  [g=callgraph i=identity]
  ^-  datum
  (~(gut by g) i *datum)
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
::  check that the formula does not crash and has no important side-effect,
::  returning constant product and nomm
::
++  safe
  =*  hint-safe  ,?(%spot %mean)
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
  =*  hint-safe  ,?(%spot %mean)
  |=  =nomm
  ^-  ?
  =*  g  .
  ?+    nomm  |
      [p=^ q=^]  &((g p.nomm) (g q.nomm))
      [%1 *]     &
  ::
      [%11 @ *]
    &(?=(hint-safe p.nomm) (g q.nomm))
  ::
      [%11 [@ *] *]
    &(?=(hint-safe p.p.nomm) (g q.p.nomm) (g q.nomm))
  ==
::  check if the formula for a formula in Nomm %2 can be safely dropped
::
++  safe-fol-fol
  =*  hint-safe  ,?(%spot %mean)
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
    &(?=(hint-safe p.nomm) (g q.nomm))
  ::
      [%11 [@ *] *]
    &(?=(hint-safe p.p.nomm) (safe-nomm q.p.nomm) (g q.nomm))
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
++  dif-ju
  |*  a=(jug)
  |*  b=_a
  ^+  a
  =/  c=_a  (~(dif by a) b)
  =/  i=_a  (~(int by a) b)
  ?:  =(~ i)  c
  %-  ~(rep by i)
  |=  [[p=_?>(?=(^ i) p.n.i) q=_?>(?=(^ i) q.n.i)] =_c]
  =/  r=_q  (~(get ju b) p)
  =/  s=_q  (~(dif in q) r)
  ?:  =(~ s)  c
  (~(put by c) p s)
::
::  Given subject and a formula, analyzes them, then goes over fresh %fast core
::  registrations and tries to disassemble their batteries, analyzing leaf ba-
::  tteries (heuristic for an arm), repeating in a loop until no more registra-
::  tions are left.
::
::  XX is it actually useful? It's not like we can get a child core before eva-
::  luating the parent-producing formula... assuming that we push everything
::  through SKA pipeline
::
++  rout
  |=  [[sub=* fol=^] lon=long-ska]
  ^-  long-ska
  =*  todo  ,[sub=sock fol=^ frame=(unit [cons=? =ring])]
  =/  q=(list todo)  ~[[&+sub fol ~]]
  =|  b=(list todo)
  |-  ^-  long-ska
  =*  cold-loop  $
  ?~  q
    ?~  b  lon
    $(q (flop b), b ~)
  ?:  ?&(?=(^ frame.i.q) cons.u.frame.i.q)
    ::  merge analysis of an autocons head and tail
    ::
    =*  p  ring.u.frame.i.q
    =*  b  back.cole.jets.lon
    =/  heds=(list bell)  ~(tap in (~(get ju b) path.p (peg axe.p 2)))
    =/  lets=(list bell)  ~(tap in (~(get ju b) path.p (peg axe.p 3)))
    :: ~&  >  [%commence-join (lent heds) (lent lets)]
    |-  ^-  long-ska
    =*  hed-loop  $
    ?~  heds
      :: ~&  >  %done-joining
      cold-loop(q t.q)
    ?.  =(fol.i.heds -.fol.i.q)
      ~&  >>  %join-head-wrong-fol
      hed-loop(heds t.heds)
    ?.  (huge:so less.i.heds sub.i.q)
      ~&  >>  %join-head-wrong-sub
      hed-loop(heds t.heds)
    =/  tels  lets
    |-  ^-  long-ska
    =*  tel-loop  $
    ?~  tels  hed-loop(heds t.heds)
    ?.  =(fol.i.tels +.fol.i.q)
      ~&  >>  %join-tail-wrong-fol
      tel-loop(tels t.tels)
    ?.  (huge:so less.i.tels sub.i.q)
      ~&  >>  %join-tail-wrong-sub
      tel-loop(tels t.tels)
    :: ~&  >  joined+p
    =/  join  (pack:so less.i.heds less.i.tels)
    =.  call.cole.jets.lon  (~(put by call.cole.jets.lon) [join fol.i.q] p)
    =.  back.cole.jets.lon  (~(put ju back.cole.jets.lon) p join fol.i.q)
    tel-loop(tels t.tels)
  ::  analyze a formula from the queue, push new tasks in the worklist
  ::
  =/  [root-bell=bell new-long=long-ska]
    (ska-poke [sub fol]:i.q lon)
  =/  new-cores  ((dif-ju core.jets.new-long) core.jets.lon)
  =.  cole.jets.new-long
    ?~  frame.i.q  cole.jets.new-long
    =*  r  ring.u.frame.i.q
    %=  cole.jets.new-long
      call  (~(put by call.cole.jets.new-long) root-bell r)
      back  (~(put ju back.cole.jets.new-long) r root-bell)
    ==
  ::
  %=    cold-loop
      q    t.q
      lon  new-long
  ::
      b
    %+  roll
      %+  sort
        %+  turn  ~(tap by new-cores)
        |=([p=path q=(set sock)] [(lent p) p q])
      |=([l=[len=@ *] r=[len=@ *]] (lth len.l len.r))
    |=  [[len=@ p=path q=(set sock)] =_b]
    ~&  >  [%enqueu p]
    %-  ~(rep in q)
    |=  [s=sock =_b]
    =/  batt  (pull:so s 2)
    ?.  (all:ca cape.batt)  ~&(>>> [%cold-miss-batt p] b)
    =*  f  data.batt
    =/  ax=@  2
    |-  ^+  b
    ?:  ?=([@ *] f)  [[s f `[| p ax]] b]
    ?.  ?=([^ ^] f)  ~&(>>> %strange-formula b)
    =.  b  $(f -.f, ax (peg ax 2))
    =.  b  $(f +.f, ax (peg ax 3))
    [[s f `[& p ax]] b]
  ==
::
+$  bell-prod  (map bell [prod=sock map=spring])
++  get-fast-regs
  |=  $:  [bus=sock =nomm]
          =bell-prod
          root=(jug * path)
          core=(jug path sock)
          batt=(jug ^ path)
      ==
  =/  gen  [miss=| root=root core=core batt=batt]
  ^+  gen
  =<  +
  |-  ^-  [sock _gen]
  =*  nomm-loop  $
  ?-    nomm
      [p=^ q=*]
    =^  h  gen  nomm-loop(nomm p.nomm)
    =^  t  gen  nomm-loop(nomm q.nomm)
    :_  gen
    (knit:so h t)
  ::
      [%0 *]
    :_  gen
    ?:  =(0 p.nomm)  *sock
    (pull:so bus p.nomm)
  ::
      [%1 *]
    :_  gen
    &+p.nomm
  ::
      [%2 *]
    ?~  info.nomm
      =.  gen  +:nomm-loop(nomm p.nomm)
      =.  gen  +:nomm-loop(nomm q.nomm)
      [*sock gen]
    =^  sub  gen  nomm-loop(nomm p.nomm)
    =.  gen     +:nomm-loop(nomm q.nomm)
    =/  [prod=sock map=spring]  (~(got by bell-prod) b.u.info.nomm)
    :_  gen
    |-  ^-  sock
    ?~  map  prod
    ?@  map  (pull:so sub map)
    %-  knit:so
    [ $(prod (hed:so prod), map -.map)
      $(prod (tel:so prod), map +.map)
    ]
  ::
      [%3 *]
    =.  gen  +:nomm-loop(nomm p.nomm)
    [*sock gen]
  ::
      [%4 *]
    =.  gen  +:nomm-loop(nomm p.nomm)
    [*sock gen]
  ::
      [%5 *]
    =.  gen  +:nomm-loop(nomm p.nomm)
    =.  gen  +:nomm-loop(nomm q.nomm)
    [*sock gen]
  ::
      [%6 *]
    =.     gen  +:nomm-loop(nomm p.nomm)
    =^  y  gen    nomm-loop(nomm q.nomm)
    =^  n  gen    nomm-loop(nomm r.nomm)
    [(purr:so y n) gen]
  ::
      [%7 *]
    =^  s  gen  nomm-loop(nomm p.nomm)
    nomm-loop(bus s, nomm q.nomm)
  ::
      [%10 *]
    =^  don  gen  nomm-loop(nomm q.p.nomm)
    =^  rec  gen  nomm-loop(nomm q.nomm)
    [(darn:so rec p.p.nomm don) gen]
  ::
      [%11 *]
    ?@  p.nomm  nomm-loop(nomm q.nomm)
    ?.  ?=(%fast p.p.nomm)
      =.  gen  +:nomm-loop(nomm q.p.nomm)
      nomm-loop(nomm q.nomm)
    =^  clue  gen  nomm-loop(nomm q.p.nomm)
    =^  prod  gen  nomm-loop(nomm q.nomm)
    :-  prod
    ^+  gen
    ?.  (all:ca cape.clue)  ~&(>>> %fast-lost-clue gen)
    =/  clue=*  data.clue
    ?.  ?=([name=$@(@tas [@tas @]) dad=^ *] clue)
      ~&(>>> fast-bad-clue+clue gen)
    =/  label=term
      ?@  name.clue  name.clue
      (cat 3 -.name.clue (scot %ud +.name.clue))
    ::
    ?.  ((sane %tas) label)  ~&(>>> fast-insane-label+label gen)
    ?~  parent=(fast-parent dad.clue)
      ~&(>>> fast-bad-clue-parent+[label clue] gen)
    ?~  u.parent
      ::  root registration
      ::
      ?.  (all:ca cape.prod)  ~&(>>> %fast-lost-root gen)
      %=  gen
        core  (~(put ju core.gen) ~[label] prod)
        root  (~(put ju root.gen) data.prod ~[label])
      ==
    ::  child core registration
    ::
    =/  axis=@  u.u.parent
    ?.  =(3 (cap axis))  ~&(>>> fast-weird-axis+[label axis] gen)
    =/  batt  (pull:so prod 2)
    ?.  (all:ca cape.batt)   ~&(>>> fast-lost-batt+label gen)
    ?.  ?=(^ data.batt)  ~&(>>> fast-atom-batt+[label data.batt] gen)
    =/  fore  (pull:so prod axis)
    =/  past=(list path)
      %~  tap  in
      %-  %~  uni  in
          ::  root registrations
          ::
          ?.  (all:ca cape.fore)  ~
          (~(get ju root.gen) data.fore)
      ::  parent core registrations
      ::
      =/  batt-fore  (pull:so fore 2)
      ?.  &((all:ca cape.batt-fore) ?=(^ data.batt-fore))  ~
      (~(get ju batt.gen) data.batt-fore)
    ::
    |-  ^+  gen
    =*  past-loop  $
    ?~  past
      ~&  >>  missed-parent+label
      gen(miss &)
    =/  pax=path  [label i.past]
    =/  socks  ~(tap in (~(get ju core.gen) i.past))
    |-  ^+  gen
    =*  sock-loop  $
    ?~  socks
      ~&  >>  missed-path+label
      past-loop(past t.past)
    ?.  (huge:so i.socks fore)  sock-loop(socks t.socks)
    =/  template=sock
      ::  put the parent into [formula *] sock
      ::
      (darn:so [[& |] data.batt ~] axis i.socks)
    ::
    ~&  >  [%matched pax]
    %=  gen
      core  (~(put ju core.gen) pax template)
      batt  (~(put ju batt.gen) data.batt pax)
    ==
  ::
      [%12 *]
    =.  gen  +:nomm-loop(nomm p.nomm)
    =.  gen  +:nomm-loop(nomm q.nomm)
    [*sock gen]
  ==  
::  Assumes finalized (fixed point).
::
++  prune-callgraph
  |=  [g=callgraph root=identity dbg=(unit callgraph)]
  ^+  g
  =|  out=callgraph
  =/  q=(list identity)  ~[root]
  =|  visit=(set identity)
  |-  ^+  out
  ?~  q  out
  ?:  (~(has in visit) i.q)  $(q t.q)
  ?~  d=(~(get by g) i.q)
    ::  call outside of the callgraph being pruned
    ::  sanity check: is the target present in the previous graph?
    ::
    ?>  |(?=(~ dbg) (~(has by u.dbg) i.q))
    $(q t.q, visit (~(put in visit) i.q))
  %=  $
        q  (weld t.q (turn ~(tap in callees.u.d) |=(callee-entry id)))
      out  (~(put by out) i.q u.d)
    visit  (~(put in visit) i.q)
  ==
::  We just analyzed a callgraph, called some new functions, maybe registered
::  some new jetted cores.
::  Did we call something from freshly registered cores? Did we call something
::  new from already registrated cores? This gate reestablishes bell <--> ring
::  mapping
::
++  ska-cole-restore
  |=  lon=long-ska
  ^-  long-ska
  =;  call=(map bell ring)
    %_    lon
        call.cole.jets  call
    ::
        back.cole.jets
      %-  ~(rep by call)
      |=  [[k=bell v=ring] acc=(jug ring bell)]
      (~(put ju acc) v k)
    ==
  ::
  %-  ~(rep by code.lon)
  |=  [[b=bell *] acc=(map bell ring)]
  =;  matching-ring=(unit ring)
    ?~  matching-ring  acc
    (~(put by acc) b u.matching-ring)
  ::
  =/  core  core.jets.lon
  |-  ^-  (unit ring)
  =*  path-loop  $
  ?~  core  ~
  =;  matching-axe-any=(unit @)
    ?^  matching-axe-any  `[p.n.core u.matching-axe-any]
    =/  l  path-loop(core l.core)
    ?^  l  l
    path-loop(core r.core)
  ::
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
  ?.  (huge:so less.b template)  ~
  =/  template-fol=sock  (hed:so template)
  =/  axis=@  2
  |-  ^-  (unit @)
  =*  fol-loop  $
  ?.  (all:ca cape.template-fol)  ~
  ?:  =(data.template-fol fol.b)  `axis
  ?.  ?=([^ *] data.template-fol)  ~
  =/  h  fol-loop(template-fol (hed:so template-fol), axis (peg axis 2))
  ?^  h  h
  fol-loop(template-fol (tel:so template-fol), axis (peg axis 3))
::
++  ska-poke
  |=  [[bus=sock fol=^] lon=long-ska]
  ^-  [bell long-ska]
  =/  root-identity=identity  [bus fol]
  =/  g=callgraph  -:(ska-callgraph root-identity memo.final.lon)
  ::
  =/  pruned=callgraph  (prune-callgraph g root-identity `graph.final.lon)
  =/  =bell-prod
    %-  ~(rep by pruned)
    |=  [[id=identity d=datum] acc=bell-prod]
    =/  b=bell  [less-code.d fol.id]
    =;  prod=[sock spring]
      ?~  have=(~(get by acc) b)  (~(put by acc) b prod)
      ?>  =(prod u.have)
      acc
    ::
    :_  map.d
    |-  ^-  sock
    ?~  map.d  prod.d
    ?@  map.d  |+~
    %-  knit:so
    [ $(prod.d (hed:so prod.d), map.d -.map.d)
      $(prod.d (tel:so prod.d), map.d +.map.d)
    ]
  ::
  =/  root-datum=datum  (~(got by pruned) root-identity)
  =/  [bg=(jug bell bell) bg-rev=(jug bell bell)]
    (simple-bell-graph-and-reversed pruned)
  ::  callees first
  ::
  =/  sccs=(list (set bell))  (flop (tarjan bg))
  =^  just-code=(map bell nomm)  lon
    =|  visit=(set identity)
    =/  q=(list identity)  ~[root-identity]
    =|  just-code=(map bell nomm)
    |-  ^-  [_just-code long-ska]
    ?~  q  [just-code lon]
    ?:  (~(has in visit) i.q)  $(q t.q)
    ?~  got=(~(get by pruned) i.q)
      ::  call outside of the freshly produced & pruned callgraph
      ::
      ?>  (~(has by graph.final.lon) i.q)
      $(q t.q, visit (~(put in visit) i.q))
    =/  d=datum  u.got
    =/  b=bell  [less-code.d fol.i.q]
    =/  callees-list=(list identity)
      ~(tap in `(set identity)`(~(run in callees.d) |=(callee-entry id)))
    ::
    %=  $
      q               (weld t.q callees-list)
      memo.final.lon  (put:mi memo.final.lon i.q d)
      just-code       (~(put by just-code) b nomm.d)
      visit           (~(put in visit) i.q)
    ==
  ::
  =.  lon
    |-  ^-  long-ska
    =*  scc-loop  $
    ?~  sccs  lon
    =/  scc  i.sccs
    =*  local  ,[code=(map bell code-entry) fols=(map ^ (map bell code-entry))]
    =/  loc1=local
      %-  ~(rep in scc)
      |=  [b=bell acc=_`local`[code.lon fols.lon]]
      :-  (~(put by code.acc) b [(~(got by just-code) b) &])
      (put-fols b [(~(got by just-code) b) &] fols.acc)
    ::
    |-  ^-  long-ska
    =*  fixpoint-loop  $
    =;  loc2=local
      ?.  =(loc1 loc2)  fixpoint-loop(loc1 loc2)
      =.  code.lon  code.loc1
      =.  fols.lon  fols.loc1
      scc-loop(sccs t.sccs)
    ::
    %-  ~(rep in scc)
    |=  [b=bell acc=_loc1]
    ^+  acc
    =/  [pure=?]  (eval-finalized b code.acc)
    =/  set-pure  |=(=code-entry code-entry(pure pure))
    =.  code.acc  (~(jab by code.acc) b set-pure)
    =.  fols.acc
      %+  ~(jab by fols.acc)  fol.b
      |=  m=(map bell code-entry)
      (~(jab by m) b set-pure)
    ::
    acc
  =.  graph.final.lon  (~(uni by graph.final.lon) pruned)
  =/  root-bell=bell  [less-code.root-datum fol]
  =/  [root=(jug * path) core=(jug path sock) batt=(jug ^ path)]
    =/  gen  [queu=pruned jets=[=_root =_core =_batt]:jets.lon]
    |-  ^+  jets.gen
    =;  [queu1=callgraph jets1=_[root core batt]:jets.lon]
      ?:  =(jets.gen jets1)  jets.gen
      ?:  =(queu1 ~)  jets1
      $(gen [queu1 jets1])
    ::
    %-  ~(rep by queu.gen)
    |=  [[id=identity d=datum] acc=_`_gen`[~ jets.gen]]
    =^  miss=?  jets.acc  (get-fast-regs [more.id nomm.d] bell-prod jets.acc)
    :_  jets.acc
    ?.  miss  queu.acc
    (~(put by queu.acc) id d)
  ::
  :-  root-bell
  lon(root.jets root, core.jets core, batt.jets batt)
::  produces data about a function
::  for now it is only purity (no crashes, no hints except %fast)
::
++  eval-finalized
  |=  [b=bell code=(map bell code-entry)]
  ^-  [pure=?]
  =/  sub=sock  less.b
  =/  =nomm  nomm:(~(got by code) b)
  =<  +
  |^  ^-  [s=sock p=?]
  =*  nomm-loop  $
  ?-    nomm
      [p=^ q=*]
    =/  p  nomm-loop(nomm p.nomm)
    =/  q  nomm-loop(nomm q.nomm)
    :-  (knit:so s.p s.q)
    &(p.p p.q)
  ::
      [%0 *]
    ?:  =(0 p.nomm)  [|+~ |]
    :-  (pull:so sub p.nomm)
    (have sub p.nomm)
  ::
      [%1 *]  [&+p.nomm &]
  ::
      [%2 *]
    :-  |+~
    ?&  p:nomm-loop(nomm p.nomm)
        p:nomm-loop(nomm q.nomm)
        |(?=(~ info.nomm) pure:(~(got by code) b.u.info.nomm))
    ==
  ::
      [%3 *]  [|+~ p:nomm-loop(nomm p.nomm)]
      [%4 *]  [|+~ p:nomm-loop(nomm p.nomm)]
      [%5 *]  [|+~ &(p:nomm-loop(nomm p.nomm) p:nomm-loop(nomm q.nomm))]
  ::
      [%6 *]
    =/  y  nomm-loop(nomm q.nomm)
    =/  n  nomm-loop(nomm r.nomm)
    :-  (purr:so s.y s.n)
    ?&  p:nomm-loop(nomm p.nomm)
        p.y
        p.n
    ==
  ::
      [%7 *]
    =/  p  nomm-loop(nomm p.nomm)
    =/  q  nomm-loop(sub s.p, nomm q.nomm)
    [s.q &(p.p p.q)]
  ::
      [%10 *]
    =/  don  nomm-loop(nomm q.p.nomm)
    =/  rec  nomm-loop(nomm q.nomm)
    :-  (darn:so s.rec p.p.nomm s.don)
    ?&  p.rec
        p.don
        (have s.rec p.p.nomm)
    ==
  ::
      [%11 *]
    ?@  p.nomm  [s:nomm-loop(nomm q.nomm) |]
    =/  tok  nomm-loop(nomm q.p.nomm)
    =/  fol  nomm-loop(nomm q.nomm)
    [s.fol &(?=(%fast p.p.nomm) p.tok p.fol)]
  ::
      [%12 *]  [|+~ |]
  ==
  ::
  ++  have
    |=  [=sock axe=@]
    ^-  ?
    ?<  =(0 axe)
    |-  ^-  ?
    ?:  =(1 axe)  &
    ?:  ?=(%| cape.sock)  |
    ?-  (cap axe)
      %2  $(sock (hed:so sock), axe (mas axe))
      %3  $(sock (tel:so sock), axe (mas axe))
    ==
  --
::  callers first
::
++  tarjan1
  ~%  %tarjan  ..zuse  ~
  |*  vertex=mold
  |=  g=(jug vertex vertex)
  =*  gen
    $:  idx=@                     ::  index generator
        vis=(map vertex @)        ::  numbered vertices
        low=(map vertex @)        ::  lowest strongly connected incl. itself
        stk=(list vertex)         ::  call stack
        cur=(set vertex)          ::  call stack as a set
        fin=(list (set vertex))   ::  finalized SCCs
    ==
  ::
  =<  fin  ^-  gen
  %-  ~(rep by g)
  |=  [[v=vertex kids=(set vertex)] acc=gen]
  =*  strongly-connect  .
  ?:  (~(has by vis.acc) v)  acc
  =^  index  idx.acc  [idx.acc +(idx.acc)]
  =.  acc
    %_  acc
      vis  (~(put by vis.acc) v index)
      low  (~(put by low.acc) v index)
      stk  [v stk.acc]
      cur  (~(put in cur.acc) v)
    ==
  ::
  =.  acc
    %-  ~(rep in kids)
    |=  [kid=vertex =_acc]
    ?^  kid-idx=(~(get by vis.acc) kid)
      ?.  (~(has in cur.acc) kid)  acc
      acc(low (~(jab by low.acc) v (curr min u.kid-idx)))
    =.  acc  (strongly-connect [kid (~(get ju g) kid)] acc)
    acc(low (~(jab by low.acc) v (curr min (~(got by low.acc) kid))))
  ::
  ?.  =(index (~(got by low.acc) v))  acc
  =;  [done=(set vertex) =_acc]  acc(fin [done fin.acc])
  =|  out=(set vertex)
  |-  ^+  [out acc]
  =*  pop-loop  $
  =^  pop=vertex  stk.acc  ?~(stk.acc !! stk.acc)
  =.  cur.acc  (~(del in cur.acc) pop)
  =.  out  (~(put in out) pop)
  ?:  =(v pop)  [out acc]
  pop-loop
::
++  simple-bell-graph-and-reversed
  |=  g=callgraph
  ^-  [(jug bell bell) (jug bell bell)]
  %-  ~(rep by g)
  |=  [[k=identity v=datum] acc=(jug bell bell) acc-r=(jug bell bell)]
  =/  caller=bell  [less-code.v fol.k]
  ?:  =(~ callees.v)
    :_  acc-r
    ?:  (~(has by acc) caller)  acc
    (~(put by acc) caller ~)
  %-  ~(rep in callees.v)
  |=  [callee=callee-entry =_acc _acc-r]
  =/  callee=bell  [less-code:(~(got by g) id.callee) fol.id.callee]
  [(~(put ju acc) caller callee) (~(put ju acc-r) callee caller)]
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
  =;  [done=(set vertex) =_acc]  acc(fin [done fin.acc])
  =|  out=(set vertex)
  |-  ^+  [out acc]
  =*  pop-loop  $
  =^  pop=vertex  stk.acc  ?~(stk.acc !! stk.acc)
  =.  cur.acc  (~(del in cur.acc) pop)
  =.  out  (~(put in out) pop)
  ?:  =(v pop)  [out acc]
  pop-loop
::
::  to incrementally construct transitive closure of a graph:
::    1. get the set of all id's whose immediate children changed ("seed");
::    2. walk the reversed graph (unified with the prev version just in
::       case), assembling the set of all id's which could reach the set
::       from step 1 ("affected");
::    3. Get the reversed subgraph of affected vertices: new-reversed from and
::       to affected;
::    5. Get SCCs of the reversed subgraph in toposorted order (caller SCCs
::       first);
::    6. For each SCC compute "closure", assign it to each member of SCC
::    7. To compute "closure": union over every immediate child of every
::       member of the SCC: {child} if child in SCC, else
::       {child} U TCB[child]
::
++  update-transitive
  ~%  %update-transitive  ..zuse  ~
  |=  $:  prev-trans=jug-id
          prev-graph=jug-id
          new-graph=jug-id
          prev-reversed=jug-id
          new-reversed=jug-id
      ==
  ^-  jug-id
  =/  seeds=(set identity)
    %-  ~(rep in (~(uni in ~(key by prev-graph)) ~(key by new-graph)))
    |=  [id=identity acc=(set identity)]
    ?:  =((~(get ju prev-graph) id) (~(get ju new-graph) id))
      acc
    (~(put in acc) id)
  ::
  =/  uno-reversed=jug-id
    %-  (~(uno by new-reversed) prev-reversed)
    |=  [identity a=(set identity) b=(set identity)]
    (~(uni in a) b)
  ::
  =/  affected=(set identity)
    =/  sinks=(list identity)  ~(tap in seeds)
    =|  out=(set identity)
    |-  ^-  (set identity)
    ?:  =(~ sinks)  out
    =.  out  (~(gas in out) sinks)
    %=    $
        sinks
      %-  skip  :_  ~(has in out)
      %~  tap  in
      %+  roll  sinks
      |=  [id=identity acc=(set identity)]
      (~(uni in acc) (~(get ju uno-reversed) id))
    ==
  ::
  =/  affected-dep-subgraph=jug-id
    %-  ~(rep in affected)
    |=  [id=identity acc=jug-id]
    %+  ~(put by acc)  id
    (~(int in affected) (~(get ju new-reversed) id))
  ::
  ::  callers first
  ::
  =/  sccs=(list (set identity))  (tarjan affected-dep-subgraph)
  =<  $
  ~%  %closures-update-prev-trans  ..zuse  ~
  |.
  %+  roll  sccs
  |=  [scc=(set identity) acc-ju=_prev-trans]
  =/  closure=(set identity)
    %-  ~(rep in scc)
    |=  [member=identity acc-se=(set identity)]
    %-  ~(rep in (~(get ju new-graph) member))
    |=  [child=identity =_acc-se]
    ?:  (~(has in scc) child)  (~(put in acc-se) child)
    %-  ~(uni in (~(put in acc-se) child))
    (~(get ju acc-ju) child)
  ::
  %-  ~(rep in scc)
  |=  [member=identity =_acc-ju]  
  (~(put by acc-ju) member closure)
::
++  check-inverses
  |=  [dir=jug-id inv=jug-id]
  ^-  ?
  =/  edges=(list (pair identity identity))
    %-  ~(rep by dir)
    |=  [[k=identity v=(set identity)] acc=(list (pair identity identity))]
    %-  ~(rep in v)
    |=  [i=identity =_acc]
    [[k i] acc]
  ::
  =.  inv
    %+  roll  edges
    |=  [[i=identity k=identity] acc=_inv]
    (~(del ju acc) k i)
  ::
  |-  ^-  ?
  ?~  inv  &
  ?&  =(~ q.n.inv)
      $(inv l.inv)
      $(inv r.inv)
  ==
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
::
::  Produces a list of callgraphs for visualization purposes. The fixpoint is
::  the first callgraph in the list
::
++  ska-callgraph
  ~%  %ska-callgraph  ..zuse  ~
  !.
  |=  [[bus=sock fol=^] memo-final=memo]
  ^-  (list callgraph)
  =|  g=callgraph
  ::  Part of the callgraph that was finalized
  ::
  :: =|  g-done=callgraph
  =|  history=(list callgraph)
  =/  root  [bus fol]
  =/  w=worklist  [root ~ ~]
  =|  calls=jug-id
  =|  called-by=jug-id
  ::  Transitive closure of the callgraph. Used in memoization of finalized
  ::  parts of the callgraph, but it's not worth it
  ::
  :: =|  transitive-calls=jug-id
  ::  Memoization table for finalized results. Needs .transitive-calls
  ::
  :: =|  memo-done=memo
  ::  Transitive closure of the inverse of the callgraph. Can be used in loop
  ::  detection, but not worth it.
  ::
  :: =|  transitive-called-by=jug-id
  ::
  :: =<  $
  :: ~%  %analysis  ..zuse  ~
  |-  ^-  (list callgraph)
  =*  fixpoint-callgraph  $
  ::  one fixpoint iteration gives us new worklists to handle, updated part of
  ::  the callgraph and updated calls
  ::
  =;  [w-new=worklist w-call=worklist new-calls=jug-id g1=callgraph]
    =.  g  g1
    =/  new-called-by=jug-id
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
    ::  update transitive closures, if defined
    ::
    =>  !@  transitive-called-by  .
        %_  .  transitive-called-by
          =<  $
          ~%  %update-transitive-called-by  ..zuse  ~
          |.
          ~>  %bout.[0 'tcb update        ']
          %:  update-transitive
            transitive-called-by
            called-by
            new-called-by
            calls
            new-calls
          ==
        ==
    ::
    =>  !@  transitive-calls  .
        %_  .  transitive-calls
          =<  $
          ~%  %update-transitive-calls  ..zuse  ~
          |.
          ~>  %bout.[0 'tc update         ']
          %:  update-transitive
            transitive-calls
            calls
            new-calls
            called-by
            new-called-by
          ==
        ==
    ::
    =.  calls      new-calls
    =.  called-by  new-called-by
    :: ?>  (check-inverses transitive-calls transitive-called-by)
    =/  w-back=worklist
      ::  worklist of functions whose immediate callees changed
      ::
      %-  ~(rep in w-call)
      |=  [callee=identity acc=worklist]
      (~(uni in acc) (~(get ju called-by) callee))
    ::
    ::  total worklist: new functions + functions whose callees changed. Nothing
    ::  else needs to be reanalysed as we'll just get the same result
    ::
    =/  w-new=worklist  (~(uni in w-new) w-back)
    ?:  =(w-new ~)  [!@(g-done g (~(uni by g-done) g)) history]
    ::
    =>  !@  memo-done  .
        =*  dot  .
        ~>  %bout.[0 'memo update       ']
        =;  res=[memo-done=memo g=callgraph g-done=callgraph]
          %_(dot memo-done memo-done.res, g g.res, g-done g-done.res)
        ::
        %-  ~(rep by g)
        |=  [[id=identity d=datum] acc=_[=_memo-done =_g =_g-done]]
        ?:  ?|  (~(has in w-new) id)
            ::
                ?=  ^
                (~(int in w-new) (~(get ju transitive-calls) id))
            ==
          acc
        [ (put:mi memo-done.acc id d)
          (~(del by g.acc) id)
          (~(put by g-done.acc) id d)
        ]
    ::
    =>  !@  ska-verb  .
        =*  dot  .
        =/  new-count   ~(wyt in ^w-new)
        =/  upd-count   ~(wyt in w-back)
        =/  uniq-count
          ~(wyt in `(set ^)`(~(run in w-new) |=(id=identity fol.id)))
        ::
        ~&  [%fixpoint new+new-count upd+upd-count uniq+uniq-count]
        dot
    ::
    %=  fixpoint-callgraph
      w        w-new
      history  [!@(g-done g (~(uni by g-done) g)) history]
    ==
  ::
  =<  !@  ska-verb  $
      ~>  %bout.[0 %callgraph-fixpoint]  $
  |.
  ::  pin .g-total if g-done is defined
  ::
  =>  !@  g-done  .  [g-total=`callgraph`(~(uni by g-done) g) .]
  =*  g-previous  !@(g-total g g-total)
  =*  calls-previous  calls
  =<  -
  %-  ~(rep in w)
  ~%  %ska-callgraph-iteration  ..zuse  ~
  !:
  |=  $:  id=identity
          ::  accumulator
          ::
          $:  [w-new=worklist w-call=worklist =_calls =_g]
              m-new=_memo-final
      ==  ==
  ^-  [[worklist worklist jug-id callgraph] memo]
  =/  data  (git-g g-previous id)
  =/  bus=sock  more.id
  =;  [memo-hit=? data-new=datum m-new=memo]
    =?  indi.data-new
        ?&  =([less-code prod map]:data-new [less-code prod map]:data)
            !=(indi.data-new indi.data)
        ==
      ::  if new datum only differs in indi.data-new,
      ::  turn disagreeing parts into %.y so that we converge
      ::
      (msg-ca indi.data-new indi.data)
    ::
    =.  g  (~(put by g) id data-new)
    =.  calls
      (~(put by calls) id (~(run in callees.data-new) |=(callee-entry id)))
    ::
    ::  don't have to put callees in the worklist on memo hit, they should
    ::  already be there
    ::
    =?  w-new  !memo-hit
      %-  ~(rep in callees.data-new)
      |=  [callee-entry acc=_w-new]
      ?:  (~(has by g-previous) id)  acc
      (~(put in acc) id)
    ::  do have to put ourselves in the callee worklist if our code usage or
    ::  product changed
    ::
    =?  w-call  ?!  .=  [less-code prod map indi]:data-new
                        [less-code prod map indi]:data
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
        indi=cape
        callees=(set callee-entry)
        area=(unit spot)
    ==
  ::
  =;  ,fol-result
    ::  construct datum & memoize
    ::
    =/  less-code  (app:ca want bus)
    =/  capture=cape  (prune:pi src.pro cape.sock.pro)
    =/  less-memo  (app:ca (uni:ca want capture) bus)
    =/  data-new=datum  [callees nomm less-code less-memo indi pro area]
    =.  m-new  (put:mi m-new id data-new)
    [| data-new m-new]
  ::
  =|  gen=[want=cape indi=cape callees=(set callee-entry) area=(unit spot)]
  =/  seat=(unit spot)  ~
  =/  memo-key=(unit *)  ~
  =/  virt-call=?  |
  ^-  [[=nomm prod=sock-anno] gen=_gen]
  =<  $
  ~%  %fol-loop  ..zuse  ~
  |.  ^-  [[=nomm prod=sock-anno] _gen]
  =*  fol-loop  $
  ?^  x=(safe fol)
    ::  This is a workaround for our cape cons denormalization breaking code
    ::  like !:([%9 2 %0 1])
    ::
    ::  If a formula is "safe" it is equivalent to Nock 1 with respect to
    ::  limiting the set of available formulas
    ::
    [[nomm.u.x [&+prod.u.x ~]] gen]
  =*  dunno  *sock-anno
  ?+    fol  [[0+0 dunno] gen]
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
    ::  memo-key might have been set by %11 %memo which redirected us here.
    ::  but there is no reason to unset it when we decend into children: if it
    ::  was set, then the child expressions will be [%0 1] and [%1 fol],
    ::  neither of which are affected by memo-key
    ::  
    =^  s  gen  fol-loop(fol p.fol)
    =^  f  gen  fol-loop(fol q.fol)
    ^-  [[nomm sock-anno] _gen]
    =<  $
    ~%  %nock-2  ..zuse  ~
    |.
    ::  Here we check that the mask is precisely & instead of cheking with
    ::  +all:ca to prevent analyzing through Nock evals with consed up formulas.
    ::  This makes the set of all callable nouns finite, guaranteeing termina-
    ::  tion of the algo when paired with homeomorphic embedding check in recur-
    ::  sive calls
    ::
    ?.  &(=(& cape.sock.prod.f) ?=(^ data.sock.prod.f) !virt-call)
      ::  indirect call
      ::
      =.  indi.gen  (uni:ca indi.gen (distribute & src.prod.f))
      [[[%2 nomm.s nomm.f ~] dunno] gen]
    =/  fol-new=^  data.sock.prod.f
    ::  Inline leaf formulas. Allows to analyze through formulas whose products
    ::  are gates, also speeds up analysis. Should be safe to comment out the
    ::  condition and the first branch - useful during debugging to rule out
    ::  stuff.
    ::
    ?:  &(?=(~ memo-key) (inlineable fol-new))
      =.  want.gen  (uni:ca want.gen (distribute & src.prod.f))
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
      =/  m  !@  memo-done  `(unit [identity datum])`~
             (git:mi memo-done fol-new sock.prod.s)
      ::
      ?^  m  u.m
      =/  par
        !@  transitive-called-by
          (recursive-call id id-there called-by g-previous)
        (recursive-call-tcb id id-there transitive-called-by g-previous)
      ::
      ?^  par  u.par
      [id-there *datum]
    ::
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
    =.  callees.gen  (~(put in callees.gen) seat id-there)
    :_  gen
    ^-  [nomm sock-anno]
    :-  [%2 nomm.s nomm.f `[[less-code.dat-there fol-new] memo-key]]
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
    ?:  ?=(%virt p.fol)
      ::  %virt hint annotates entry points into meta-circularly jetted
      ::  interpreters. No need to analyze through.
      ::
      fol-loop(fol [%2 [%0 1] 1 q.fol], virt-call &)
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
    ?:  &(?=(%memo a.fol) ?=(^ (safe h.fol)))
      ::  ?=(^ (safe h.fol)) implies fully known sock.prod.h
      ::
      fol-loop(fol [%2 [%0 1] 1 f.fol], memo-key `data.sock.prod.h)
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
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Axis usage analysis
::
::    Once we have the callgraph, but before we can start compiling SKA func-
::    tions, we need to establish which parts of the subject a function will use
::    as the data.  With that information we will be able to compile functions
::    in any order, including lazily.
::
::    To get axis usage data we start off with the cold state: we know axis
::    usage of the jetted functions.  Then, starting with the root function:
::      - if the function has a jet, immediately return the registerization;
::      - else get the SCC to which this function belongs, and start the
::        fixpoint search:
::        - initialize all registerizations of functions in the SCC to empty;
::        - iterate over functions with a worklist algorithm similar to
::          +ska-callgraph;
::        - on a call within SCC get the current guess, else get the
::          registerization recursively. This will make sure we don't do extra
::          work registerizing exclusive callees of jetted functions.
::
::    Additional attention needs to be payed to Nock 6 to prevent from pessimi-
::    zing, both here and in the compiler. Subject usage of a computation with
::    a branch consists of a union of subject usages before and after a branch
::    with the most specific generalization of the exclusive subject usages
::    of branches. This applies recursively to branches within branches
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
|%
+$  long-args
  $+  long-args
  $:
  ::::  hot state: subject usage by jetted arms
    ::
    jets=(map ring cape)
    code=(map bell cape)
  ==
::
+$  worklist  (set bell)
++  axes-lazy
  |-
  $+  axes-lazy
  $:  sure=cape
      fork=(list [y=$ n=$])
  ==
--
::
|%
++  axes-lazy-fmap
  |=  [laz=axes-lazy gat=$-(cape cape)]
  ^-  axes-lazy
  =*  fmap  $
  :-  (gat sure.laz)
  %+  turn  fork.laz
  |=  [y=axes-lazy n=axes-lazy]
  [fmap(laz y) fmap(laz n)]
::
++  collapse-axes-lazy
  |=  laz=axes-lazy
  ^-  cape
  =*  collapse  .
  ?:  =(~ fork.laz)  sure.laz
  %+  roll  fork.laz
  |=  [[y=axes-lazy n=axes-lazy] acc=cape]
  %+  uni:ca  acc
  %-  msg-ca
  [ (uni:ca sure.laz (collapse y(sure (uni:ca sure.y sure.laz))))
    (uni:ca sure.laz (collapse n(sure (uni:ca sure.n sure.laz))))
  ]
::
++  unify-lazy-usage
  |=  [a=axes-lazy b=axes-lazy]
  ^-  axes-lazy
  :-  (uni:ca sure.a sure.b)
  (weld fork.a fork.b)
::  curry right. no inner wetness
::
++  curr
  |*  [a=$-(^ *) c=*]
  |=  b=_,.+<-.a
  (a b c)
::
++  into
  ::  split lazy goal for edit: donor, then recipient
  ::
  |=  [axe=@ laz=axes-lazy]
  ^-  [axes-lazy axes-lazy]
  ?<  =(0 axe)
  ?:  =(1 axe)  [laz *axes-lazy]
  :-  (axes-lazy-fmap laz (curr lot:ca axe))
  %+  axes-lazy-fmap  laz
  |=  c=cape
  ^-  cape
  ::  poke a hole in c at axe
  ::
  ?:  ?=(%| c)  |
  ?:  =(1 axe)  |
  ?-  (cap axe)
    %2  (con:ca $(c (hed:ca c), axe (mas axe)) (tel:ca c))
    %3  (con:ca (hed:ca c) $(c (tel:ca c), axe (mas axe)))
  ==
::
++  axis-poke
  |=  [root=bell =long-ska lon=long-args]
  ^-  long-args
  =/  [bell-graph=(jug bell bell) bell-graph-reversed=(jug bell bell)]
    (simple-bell-graph-and-reversed graph.final.long-ska)
  ::
  =/  sccs=(list (set bell))  (tarjan bell-graph)
  =/  scc-map=(map bell (set bell))
    %+  roll  sccs
    |=  [scc=(set bell) acc=(map bell (set bell))]
    %-  ~(rep in scc)
    |=  [b=bell acc=_acc]
    (~(put by acc) b scc)
  ::
  (axis-find (~(got by scc-map) root) bell-graph-reversed long-ska lon scc-map)
::
++  axis-find
  |=  $:  scc=(set bell)
          rev=(jug bell bell)
          =long-ska
          lon=long-args
          scc-map=(map bell (set bell))
      ==
  ^-  long-args
  =*  axis-find  .
  =;  [new=(map bell cape) lon1=long-args]
    =.  lon  lon1
    lon(code (~(uni by code.lon) new))
  ::
  ^-  [(map bell cape) long-args]
  =|  functions-axes=(map bell cape)
  =/  w=worklist  scc
  |-  ^-  [(map bell cape) long-args]
  =*  fixpoint-axis  $
  =;  [[w-new=worklist functions-axes1=(map bell cape)] lon1=long-args]
    =.  functions-axes  functions-axes1
    =.  lon  lon1
    ::  we only care about the SCC we are focused on, don't enqueue other
    ::  callers
    ::
    =.  w-new  (~(int in w-new) scc)
    ?:  =(~ w-new)  [functions-axes lon]
    fixpoint-axis(w w-new)
  ::
  %-  ~(rep in w)
  |=  [b=bell [w-new=worklist =_functions-axes] =_lon]
  ^-  [[worklist (map bell cape)] long-args]
  =;  [[axes-data=cape axes-look=cape] lon1=long-args]
    =.  lon  lon1
    =/  axes=cape
      %+  uni:ca  axes-data
      =/  sub=sock  less.b
      |-  ^-  cape
      ?@  axes-look  |
      ?:  &(|(=(| cape.sub) ?=(@ data.sub)) ?=(@ axes-data))
        axes-look
      %-  con:ca
      [ $(sub (hed:so sub), axes-look -.axes-look, axes-data (hed:ca axes-data))
        $(sub (tel:so sub), axes-look +.axes-look, axes-data (tel:ca axes-data))
      ]
    ::
    :_  lon
    =/  axes-old=(unit cape)  (~(get by functions-axes) b)
    ?~  axes-old
      :-  ?:  =(axes |)  w-new
          (~(uni in w-new) (~(get ju rev) b))
      (~(put by functions-axes) b axes)
    ::  this is not the first iteration, get MSG of the old and the new value
    ::  to prevent divergence
    ::
    =.  axes  (msg-ca axes u.axes-old)
    ?:  =(axes u.axes-old)
      [w-new functions-axes]
    :-  (~(uni in w-new) (~(get ju rev) b))
    (~(put by functions-axes) b axes)
  ::
  =;  [[dat=axes-lazy lok=axes-lazy] lon1=long-args]
    [[(collapse-axes-lazy dat) (collapse-axes-lazy lok)] lon1]
  ::
  =/  =nomm  nomm:(~(got by code.long-ska) b)
  ::  "dat" is equivalent to "goal" in SSA compilation. It means "what parts of
  ::  the result of this computation will be used in the next computation".
  ::  In tail position we need the whole thing.
  ::
  ::  "lok" is axis usage caused by sterile Nock 0 lookups, i.e. Nock 0's whose
  ::  products are dropped
  ::
  =/  need-it  [[& ~] *axes-lazy]
  =/  drop-it  [*axes-lazy *axes-lazy]
  =/  goal=[dat=axes-lazy lok=axes-lazy]  need-it
  |^  ^-  [_goal long-args]
  =*  nomm-loop  $
  ?-    nomm
      [p=^ q=*]
    =^  p  lon  $(nomm p.nomm, goal (app-goal (curr axes-lazy-fmap hed:ca)))
    =^  q  lon  $(nomm q.nomm, goal (app-goal (curr axes-lazy-fmap tel:ca)))
    :_  lon
    (unify-goals p q)
  ::
      [%0 @]
    :_  lon
    ?:  =(0 p.nomm)  drop-it
    ?:  =(1 p.nomm)  goal
    ::  lok.goal keeps track of sterile Nock 0's here by turning empty goals
    ::  to [& ~]
    ::
    :-  (axes-lazy-fmap dat.goal (curr pat:ca p.nomm))
    %+  axes-lazy-fmap
      ?:  =(*axes-lazy lok.goal)  [& ~]
      lok.goal
    (curr pat:ca p.nomm)
  ::
      [%1 *]  [drop-it lon]
  ::
      [%2 *]
    ?~  info.nomm
      =^  p  lon  $(nomm p.nomm, goal need-it)
      =^  q  lon  $(nomm q.nomm, goal need-it)
      :_  lon
      (unify-goals p q)
    =*  b-callee  b.u.info.nomm
    =/  callee-pure=?  pure:(~(got by code.long-ska) b-callee)
    =^  q=_goal  lon
      ?:  (safe-fol-fol q.nomm)  [drop-it lon]
      $(nomm q.nomm, goal drop-it)
    ?:  &(callee-pure (drop-it-equivalent goal))
      =^  p  lon  $(nomm p.nomm, goal drop-it)
      :_  lon
      (unify-goals p q)
    =^  callee-usage=cape  lon
      ::  first try to get subject split by jets, then check if in the current
      ::  SCC, getting current assumption if yes, then look among finalized,
      ::  finally recur into the new SCC and get the result
      ::
      =*  call-cole  call.cole.jets.long-ska
      ?^  j=(biff (~(get by call-cole) b-callee) ~(get by jets.lon))
        [u.j lon]
      ?:  (~(has in scc) b-callee)
        [(~(gut by functions-axes) b-callee |) lon]
      ?^  c=(~(get by code.lon) b-callee)
        [u.c lon]
      =.  lon  (axis-find (~(got by scc-map) b-callee) rev long-ska lon scc-map)
      :_  lon
      (~(got by code.lon) b-callee)
    ::
    =^  p  lon  $(nomm p.nomm, goal [. .]:[callee-usage ~])
    :_  lon
    (unify-goals p q)
  ::
      [%3 *]  $(nomm p.nomm, goal need-it)
      [%4 *]  $(nomm p.nomm, goal need-it)
      [%5 *]
    =^  p  lon  $(nomm p.nomm, goal need-it)
    =^  q  lon  $(nomm q.nomm, goal need-it)
    :_  lon
    (unify-goals p q)
  ::
      [%6 *]
    =^  p  lon  $(nomm p.nomm, goal need-it)
    =^  q  lon  $(nomm q.nomm)
    =^  r  lon  $(nomm r.nomm)
    :_  lon
    :-  [sure.dat.p [[dat.q dat.r] fork.dat.p]]
    [sure.lok.p [[lok.q lok.r] fork.lok.p]]
  ::
      [%7 *]
    =^  q  lon  $(nomm q.nomm)
    $(nomm p.nomm, goal q)
  ::
      [%10 *]
    =/  [don-dat=axes-lazy rec-dat=axes-lazy]  (into p.p.nomm dat.goal)
    =/  [don-lok=axes-lazy rec-lok=axes-lazy]  (into p.p.nomm lok.goal)
    =^  qp  lon  $(nomm q.p.nomm, goal [don-dat don-lok])
    =^  q   lon  $(nomm q.nomm, goal [rec-dat rec-lok])
    :_  lon
    (unify-goals qp q)
  ::
      [%11 *]
    ?@  p.nomm   $(nomm q.nomm)
    =^  qp  lon  $(nomm q.p.nomm, goal need-it)
    =^  q   lon  $(nomm q.nomm)
    :_  lon
    (unify-goals q qp)
  ::
      [%12 *]
    =^  p  lon  $(nomm p.nomm, goal need-it)
    =^  q  lon  $(nomm q.nomm, goal need-it)
    :_  lon
    (unify-goals p q)
  ==
  ::
  ++  unify-goals
    |=  [a=_goal b=_goal]
    ^+  goal
    :-  (unify-lazy-usage dat.a dat.b)
    :_  (weld fork.lok.a fork.lok.b)
    ::  get deepest axes
    ::  XX maybe best to leave it a regular union for easier sync with
    ::  compilation?
    ::
    =/  a=cape  sure.lok.a
    =/  b=cape  sure.lok.b
    |-  ^-  cape
    ?@  a
      ?^  b  b
      |(a b)
    ?@  b  a
    (con:ca $(a -.a, b -.b) $(a +.a, b +.b))
  ::
  ++  app-goal
    |=  g=$-(axes-lazy axes-lazy)
    ^+  goal
    [(g dat.goal) (g lok.goal)]
  ::
  ++  drop-it-equivalent
    |=  g=_goal
    ^-  ?
    &((no-equivalent dat.g) (no-or-all-equivalent lok.g))
  ::
  ++  no-equivalent
    |=  laz=axes-lazy
    ^-  ?
    =*  this  .
    ?&  ?=(%| sure.laz)
    ::
        %+  levy  fork.laz
        |=  [y=axes-lazy n=axes-lazy]
        &((this y) (this n))
    ==
  ::
  ++  no-or-all-equivalent
    |=  laz=axes-lazy
    ^-  ?
    =*  this  .
    ?&  ?=(@ sure.laz)
    ::
        %+  levy  fork.laz
        |=  [y=axes-lazy n=axes-lazy]
        &((this y) (this n))
    ==
  --
--
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
::  Compilation
::
::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
|%
+$  hint-static  ?(%bout %xray)
+$  hint-dynamic  ?(%bout %xray %spin %loop %jinx %live hint-dynamic-stop)
+$  hint-dynamic-stop  ?(%mean %spot %slog)
+$  need
  $~  [%none ~]
  $^  [p=need q=need]
  $%  [%both r=@uvre c=? h=need t=need]
      [%this r=@uvre]
      [%none ~]
  ==
::
+$  need-ordered
  $~  [%none ~]
  $^  [p=need-ordered q=need-ordered]
  $%  [%both c=? h=need-ordered t=need-ordered]
      [%this ~]
      [%none ~]
  ==
::
+$  need-lazy
  $+  need-lazy
  $;  |-
  $:  sure=need
      fork=(list [y=[o=@uwoo laz=$] n=[o=@uwoo laz=$]])
      bond=(list [o=@uwoo laz=$])
  ==
::  there - target basic block
::  args  - arguments for that basic block
::  BBs with arguments: control flow merges (instead of phi nodes) and maybe
::  entry point block
::
+$  jmp  [args=(list @uvre) there=@uwoo]
+$  goal
  $%  [%pick z=jmp o=jmp]
      [%done ~]
      [%next laz=need-lazy then=jmp]
  ==
::
+$  next  $>(%next goal)
+$  next-resolved  [%next [ned=need ~ ~] [~ then=@uwoo]]
::  basic block
::
+$  blob  [par=(list @uvre) body=(list pole) fin=termin]
+$  straight  [need=need-ordered n-args=@ud blocks=(map @uwoo blob)]
+$  line-short
  $:  re-gen=@uvre
      bo-gen=_`@uwoo`1  ::  0 is reserved for the entry point
      blocks=(map @uwoo blob)
  ==
::
+$  pole
  $%  [%imm n=* d=@uvre]                          ::  n -> d
      [%mov s=@uvre d=@uvre]                      ::  s -> d
      [%inc s=@uvre d=@uvre]                      ::  +(s) -> d or crash
      [%con h=@uvre t=@uvre d=@uvre]              ::  [h t] -> d
      [%hed s=@uvre d=@uvre]                      ::  -.s -> d, does not crash
      [%tal s=@uvre d=@uvre]                      ::  +.s -> d, does not crash
      [%cel p=@uvre]                              ::  ?>  ?=(^ p)
      [%hsp n=hint-static f=*]                    ::  prologue of a static hint
      [%hse n=hint-static f=*]                    ::  epilogue of a static hint
      [%hdp n=hint-dynamic p=@uvre f=*]           ::  prologue of a dynamic hint
      [%hde n=hint-dynamic p=@uvre f=*]           ::  epilogue of a dynamic hint
      [%spy e=@uvre p=@uvre d=@uvre]              ::  .^(e p) -> d
      [%nok u=@uvre f=@uvre d=@uvre]              ::  .*(u f) -> d
      [%cal a=bell v=(list @uvre) d=@uvre]        ::  a(v) -> d
      [%caf a=bell v=(list @uvre) d=@uvre n=ring] ::  %cal but maybe jetted
      [%cam a=bell v=(list @uvre) d=@uvre n=*]    ::  %cal but memoized
  ==
::
+$  termin
  $%  [%clq s=@uvre z=jmp o=jmp]            ::  ?^  s
      [%eqq l=@uvre r=@uvre z=jmp o=jmp]    ::  ?:  =(l r)
      [%brn s=@uvre z=jmp o=jmp]            ::  ?:  s  (crashes on non-loobean)
      [%hop t=jmp]                          ::  unconditional block jump
      [%jmp a=bell v=(list @uvre)]          ::  %cal but in tail position
      [%jmf a=bell v=(list @uvre) n=ring]   ::  %caf but in tail position
      [%don s=@uvre]                        ::  return s
      [%bom ~]                              ::  boom! crash
  ==
::
++  get-regs
  |=  op=$%(pole termin)
  ^-  (list @uvre)
  =>  op
  ?-  -
    %imm  ~[d]
    %mov  ~[s d]
    %inc  ~[s d]
    %con  ~[h t d]
    %hed  ~[s d]
    %tal  ~[s d]
    %cel  ~[p]
    %hsp  ~
    %hse  ~
    %hdp  ~[p]
    %hde  ~[p]
    %spy  ~[e p d]
    %nok  ~[u f d]
    %cal  [d v]
    %caf  [d v]
    %cam  [d v]
    %clq  ~[s]
    %eqq  ~[l r]
    %brn  ~[s]
    %hop  ~
    %jmp  v
    %jmf  v
    %don  ~[s]
    %bom  ~
  ==
::
++  get-jmps
  |=  op=termin
  ^-  (list jmp)
  =>  op
  ?-  -
    %clq  ~[z o]
    %eqq  ~[z o]
    %brn  ~[z o]
    %hop  ~[t]
    %jmp  ~
    %jmf  ~
    %don  ~
    %bom  ~
  ==
--
::  Check that $next-resolved nests under next
::
=+  `next`*next-resolved
=>  +
::
|%
++  compile-scc
  |=  $:  scc=(set bell)
          rev=(jug bell bell)
          =long-ska
          scc-map=(map bell (set bell))
      ==
  ^-  (map bell straight)
  ~+
  =|  map-local=(map bell straight)
  =/  w=worklist  scc
  |-  ^+  map-local
  =*  fixpoint-compilation  $
  =;  [w-new=worklist map-local1=(map bell straight)]
    =.  map-local  map-local1
    =.  w-new  (~(int in w-new) scc)
    ?:  =(~ w-new)  map-local
    fixpoint-compilation(w w-new)
  ::
  %-  ~(rep in w)
  |=  [b=bell w-new=worklist =_map-local]
  ^+  [w-new map-local]
  =;  [s=straight nex=next-resolved gen=line-short]
    ?~  s-previous=(~(get by map-local) b)
      :-  ?:  ?=([%none ~] need.s)  w-new
          (~(uni in w-new) (~(get ju rev) b))
      (~(put by map-local) b s)
    =/  need-pessimized  (msg-need-ord need.s need.u.s-previous)
    :-  ?:  =(need-pessimized need.u.s-previous)  w-new
        (~(uni in w-new) (~(get ju rev) b))
    %+  ~(put by map-local)  b
    ?:  =(need-pessimized need.s)  s
    =^  coerced=next-resolved  gen  (~(coerce comp gen) need-pessimized nex)
    (~(to-straight comp gen) coerced)
  ::
  =/  [nex=next gen=line-short]
    (~(run comp *line-short) nomm:(~(got by code.long-ska) b) [%done ~])
  ::
  =^  res  gen  (~(next-lazy-collapse comp gen) nex)
  [(~(to-straight comp gen) res) res gen]
::
++  comp
  |_  gen=line-short
  ++  run
    |=  [=nomm =goal]
    |^  ^-  [next _gen]
    ?-    nomm
        [^ *]
      ?-    -.goal
          %done
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ [%don r])
        $(goal [%next [[%this r] ~ ~] ~ o])
      ::
          %pick
        bomb
      ::
          %next
        =^  [hed=need-lazy tel=need-lazy o=@uwoo]  gen  (split goal)
        =^  next-2  gen  $(nomm +.nomm, goal [%next tel ~ o])
        =^  next-1  gen  $(nomm -.nomm, goal [%next hed then.next-2])
        (copy next-1 laz.next-2)
      ==
    ::
        [%0 *]
      ?:  =(0 p.nomm)  bomb
      =^  next  gen  simple-next
      ?:  =(1 p.nomm)  [next gen]
      [[%next (from p.nomm laz.next) then.next] gen]
    ::
        [%1 *]
      ?-    -.goal
          %done
        =^  r  gen  re
        =^  o  gen  (emit ~ ~[imm+[p.nomm r]] don+r)
        [[%next [none+~ ~ ~] ~ o] gen]
      ::
          %pick
        ?+  p.nomm  bomb
          %0  [[%next [none+~ ~ ~] z.goal] gen]
          %1  [[%next [none+~ ~ ~] o.goal] gen]
        ==
      ::
          %next
        =^  o  gen  (mede then.goal p.nomm laz.goal)
        [[%next [none+~ ~ ~] ~ o] gen]
      ==
    ::
        [%2 *]  stub
    ::
        [%3 *]
      |-  ::  reenter with edited goal
      ?-    -.goal
          %done
        =^  r-0  gen  re
        =^  r-1  gen  re
        =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
        =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
        $(goal [%pick ~^o-0 ~^o-1])
      ::
          %next
        =^  a=(unit [r=@uvre o=@uwoo])  gen  (collapse-lazy-atom goal)
        ?~  a  ^$(nomm p.nomm)
        =^  [z=@uwoo o=@uwoo]  gen  (forl r.u.a o.u.a)
        $(goal [%pick ~^z ~^o])
      ::
          %pick
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ clq+[r [z o]:goal])
        ^$(nomm p.nomm, goal [%next [this+r ~ ~] ~ o])
      ==
    ::
        [%4 *]
      ?-    -.goal
          %done
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o    gen  (emit ~ [%inc arg pro]~ %don pro)
        $(nomm p.nomm, goal [%next [[%this arg] ~ ~] ~ o])
      ::
          %pick
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o    gen  (emit ~ [%inc arg pro]~ %brn pro [z o]:goal)
        $(nomm p.nomm, goal [%next [[%this arg] ~ ~] ~ o])
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
        $(nomm p.nomm, goal [%next [[%this arg] ~ ~] ~ o])
      ==
    ::
        [%5 *]
      |-  ::  reenter
      ?-    -.goal
          %done
        =^  r-0  gen  re
        =^  r-1  gen  re
        =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
        =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
        $(goal [%pick ~^o-0 ~^o-1])
      ::
          %next
        =^  a=(unit [r=@uvre o=@uwoo])  gen  (collapse-lazy-atom goal)
        ?~  a
          =^  next-q  gen  ^$(nomm q.nomm)
          =^  next-p  gen  ^$(nomm p.nomm, then.goal then.next-q)
          (copy next-p laz.next-q)
        =^  [z=@uwoo o=@uwoo]  gen  (forl r.u.a o.u.a)
        $(goal [%pick ~^z ~^o])
      ::
          %pick
        =^  r-p  gen  re
        =^  r-q  gen  re
        =^  o    gen  (emit ~ ~ eqq+[r-p r-q [z o]:goal])
        ::
        =^  next-q  gen  ^$(nomm q.nomm, goal [%next [[%this r-q] ~ ~] ~ o])
        =^  next-p  gen
          ^$(nomm p.nomm, goal [%next [[%this r-p] ~ ~] then.next-q])
        ::
        (copy next-p laz.next-q)
      ==
    ::
        [%6 *]
      ?.  ?|  ?=(%done -.goal)
              ?=(%pick -.goal)
              &(=(~ fork.laz.goal) =(~ bond.laz.goal))
          ==
        =^  r-cond  gen  re
        =^  [goal-0=^goal goal-1=^goal]  gen  (fork goal r-cond)
        =^  next-1  gen  $(nomm r.nomm, goal goal-1)
        =^  next-0  gen  $(nomm q.nomm, goal goal-0)
        =^  [lazy=need-lazy yes=@uwoo nuh=@uwoo]  gen  (sect next-0 next-1)
        =^  o=@uwoo  gen  (emit ~ ~ [%brn r-cond ~^yes ~^nuh])
        =^  cond  gen  $(nomm p.nomm, goal [%next [this+r-cond ~ ~] ~ o])
        (copy cond lazy)
      =^  [goal-0=^goal goal-1=^goal]  gen
        |-  ^-  [[^goal ^goal] _gen]
        ?-    -.goal
            %done  [[done+~ done+~] gen]
        ::
            %next
          =^  o-0  gen  oo
          =^  o-1  gen  oo
          =^  [ned-0=need ned-1=need]  gen
            (fork-sure sure.laz.goal there.then.goal o-0 o-1)
          ::
          :_  gen
          [[%next [ned-0 ~ ~] ~ o-0] [%next [ned-1 ~ ~] ~ o-1]]
        ::
            %pick  [[goal goal] gen]
        ==
      =^  next-1  gen  $(nomm r.nomm, goal goal-1)
      =^  next-0  gen  $(nomm q.nomm, goal goal-0)
      =^  [lazy=need-lazy yes=@uwoo nuh=@uwoo]  gen  (sect next-0 next-1)
      =^  cond  gen  $(nomm p.nomm, goal [%pick ~^yes ~^nuh])
      (copy cond lazy)
    ::
        [%7 *]
      =^  next  gen  $(nomm q.nomm)
      $(nomm p.nomm, goal next)
    ::
        [%10 *]
      ?-    -.goal
          %done
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %don r)
        $(goal [%next [this+r ~ ~] ~ o])
      ::
          %pick
        ?:  =(p.p.nomm 1)
          =^  r  gen  re
          =^  o  gen  (emit ~ ~ brn+[r [z o]:goal])
          $(goal [%next [[%this r] ~ ~] ~ o])
        =^  o  gen  (emit ~ ~ %bom ~)
        =^  next-rec  gen  $(nomm q.nomm, goal [%next [none+~ ~ ~] ~ o])
        =^  next-don  gen
          $(nomm q.nomm, goal [%next [none+~ ~ ~] then.next-rec])
        ::
        (copy next-don laz.next-rec)
      ::
          %next
        =^  [don=need-lazy rec=need-lazy o=@uwoo]  gen  (into goal p.p.nomm)
        =^  next-rec  gen  $(nomm q.nomm, goal [%next rec ~ o])
        =^  next-don  gen  $(nomm q.p.nomm, goal [%next don then.next-rec])
        (copy next-don laz.next-rec)
      ==
    ::
        [%11 *]
      ?@  p.nomm
        ?.  ?=(hint-static p.nomm)  $(nomm q.nomm)
        =^  next  gen  simple-next
        =^  epil  gen  (emit ~ ~[hse+[p.nomm body.nomm]] %hop then.next)
        =^  next  gen  $(nomm q.nomm, goal next(then [~ epil]))
        =^  prol  gen  (emit ~ ~[hsp+[p.nomm body.nomm]] %hop then.next)  
        [[%next laz.next ~ prol] gen]
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  next  gen  $(nomm q.nomm)
        =^  toke  gen  $(nomm q.p.nomm, goal [%next [none+~ ~ ~] then.next])
        (copy toke laz.next)
      =^  next  gen  simple-next
      =^  toke  gen  re
      =^  epil  gen  (emit ~ ~[hde+[p.p.nomm toke body.nomm]] %hop then.next)
      =^  next  gen  $(nomm q.nomm, goal next(then [~ epil]))
      =^  next  gen
        ?.  ?=(hint-dynamic-stop p.p.nomm)  [next gen]
        (lazy-bound next)
      ::
      =^  prol  gen  (emit ~ ~[hdp+[p.p.nomm toke body.nomm]] %hop then.next)  
      =^  dyna  gen  $(nomm q.p.nomm, goal [%next [this+toke ~ ~] ~ prol])
      (copy dyna laz.next)
    ::
        [%12 *]
      =^  next  gen  simple-next
      =^  [out=@uwoo pro=@uvre]  gen  (kerf next)
      =^  r-path     gen  re
      =^  r-ref      gen  re
      =^  o-spy      gen  (emit ~ [%spy r-ref r-path pro]~ %hop ~ out)
      =^  need-path  gen  $(nomm q.nomm, goal [%next [this+r-path ~ ~] ~ o-spy])
      =^  need-ref   gen
        $(nomm p.nomm, goal [%next [this+r-ref ~ ~] then.need-path])
      ::
      (copy need-ref laz.need-path)
    ==
    ::
    ++  simple-next
      ^-  [next _gen]
      ?:  ?=(%next -.goal)  [goal gen]
      =^  r  gen  re
      =^  o  gen
        %^  emit  ~  ~
        ?:  ?=(%done -.goal)  [%don r]
        [%brn r [z o]:goal]
      ::
      [[%next [this+r ~ ~] ~ o] gen]
    --
  ::
  ++  re  `[@uvre _gen]`[re-gen.gen gen(re-gen +(re-gen.gen))]
  ++  oo  `[@uwoo _gen]`[bo-gen.gen gen(bo-gen +(bo-gen.gen))]
  ++  kerf
    |=  =next
    ^-  [[@uwoo @uvre] _gen]
    =^  o  gen  (emit ~ ~ %hop then.next)
    =^  r=@uvre  gen  (kern o laz.next)
    [[o r] gen]
  ::
  ++  walk-lazy
    |=  [o=@uwoo laz=need-lazy f=$-([@uwoo need _gen] _gen)]
    ^+  gen
    =*  walk  $
    =.  gen  (f o sure.laz gen)
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
    |=  [o=@uwoo laz=need-lazy]
    ^-  [@uvre _gen]
    =^  r  gen  re
    :-  r
    %^  walk-lazy  o  laz
    |=  [o=@uwoo ned=need gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    |-  ^+  gen
    =^  l=(list pole)  gen  (kern-need r ned)
    (add-ops o l)
  ::
  ++  kern-r
    |=  [o=@uwoo ned=need]
    ^-  [@uvre _gen]
    =^  r  gen  re
    =^  ops=(list pole)  gen  (kern-need r ned)
    =.  gen  (add-ops o ops)
    [r gen]
  ::
  ++  kern-need
    |=  [r=@uvre ned=need]
    ^-  [(list pole) _gen]
    =|  ops=(list pole)
    |-  ^-  [(list pole) _gen]
    ?-    -.ned
        %none  [ops gen]
        %this  [[[%mov r r.ned] ops] gen]
    ::
        ^
      =^  r-ned  gen  re
      $(ned [%both r-ned | ned])
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
      =?  ops  !c.ned  [[%cel r.ned] ops]
      [[[%mov r r.ned] ops] gen]
    ==
  ::
  ++  lazy-bound
    |=  nex=next
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %hop then.nex)
    :_  gen
    ?>  =(~ args.then.nex)
    [%next [*need ~ [o laz.nex]~] ~ o]
  ::
  ++  sect
    |=  [nex-0=next nex-1=next]
    ^-  [[need-lazy @uwoo @uwoo] _gen]
    =^  o-0  gen  (emit ~ ~ %hop then.nex-0)
    =^  o-1  gen  (emit ~ ~ %hop then.nex-1)
    :_  gen
    ?>  =(~ args.then.nex-0)
    ?>  =(~ args.then.nex-1)
    :_  [o-0 o-1]
    [*need [[o-0 laz.nex-0] [o-1 laz.nex-1]]~ ~]
  ::
  ++  mede
    |=  [then=jmp som=* laz=need-lazy]
    ^-  [@uwoo _gen]
    =^  o=@uwoo  gen  (emit ~ ~ %hop then)
    :-  o
    %^  walk-lazy  o  laz
    |=  [o=@uwoo ned=need gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    |-  ^+  gen
    ?-    -.ned
        %none  gen
        %this  (add-ops o [%imm som r.ned]~)
    ::
        ^
      ?@  som  (emir o ~ ~ %bom ~)  ::  overwrites old block
      =.  gen  $(som -.som, ned -.ned)
      $(som +.som, ned +.ned)
    ::
        %both
      ?:  &(!c.ned ?=(@ som))  (emir o ~ ~ %bom ~)
      =.  gen  (add-ops o [%imm ?^(som som %mede-both-atom) r.ned]~)
      =.  gen  $(som -.som, ned h.ned)  ::  XX no +kern here, is OK?
      $(som +.som, ned t.ned)
    ==
  ::
  ++  none-equivalent
    |=  laz=need-lazy
    ^-  ?
    =*  none  .
    ?&  ?=([%none ~] sure.laz)
        (levy fork.laz |=([[* a=need-lazy] * b=need-lazy] &((none a) (none b))))
        (levy bond.laz |=([* n=need-lazy] (none n)))
    ==
  ::
  ::  ~: nothing needed
  ::  [~ @uvre @uwoo]: something is needed (an atom or whatever + crash)
  ::
  ++  collapse-lazy-atom
    |=  nex=next
    ^-  [(unit [@uvre @uwoo]) _gen]
    ?>  =(~ args.then.nex)
    ?:  (none-equivalent laz.nex)  [~ gen]
    =^  r  .
      =*  dot  .
      ?-    -.sure.laz.nex
          %this
        [r.sure.laz.nex dot]
      ::
          %none
        =^  r  gen  re
        [r dot]
      ::
          *
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %bom ~)
        =.  there.then.nex  o
        [r dot]
      ==
    ::
    :-  `[r there.then.nex]
    ::  add crashes wherever lazy needs need more than an atom
    ::
    %^  walk-lazy  there.then.nex  [this+r fork.laz.nex bond.laz.nex]
    |=  [o=@uwoo ned=need gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    ?:  ?=(?(%this %none) -.ned)  gen
    (emir o ~ ~ %bom ~)
  ::
  ++  flatten-need
    |=  ned=need
    ^-  (list @uvre)
    ?-  -.ned
      %none  ~
      %this  ~[r.ned]
      ^      (weld $(ned -.ned) $(ned +.ned))
      %both  [r.ned (weld $(ned h.ned) $(ned t.ned))]
    ==
  ::  fork CFG
  ::
  ::  Produces a pair of needs, emitting code into given o-0/1 provided by the
  ::  caller
  ::
  ++  fork-sure
    |=  [ned=need o=@uwoo o-0=@uwoo o-1=@uwoo]
    ^-  [[need need] _gen]
    =;  [[ned-0=need ned-1=need] gen1=_gen]
      =.  gen  gen1
      :-  [ned-0 ned-1]
      =/  args-0=(list @uvre)  (flatten-need ned-0)
      =/  args-1=(list @uvre)  (flatten-need ned-1)
      =/  args=(list @uvre)    (flatten-need ned)
      =^  barg  gen  (emit args ~ %hop ~ o)
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
      [[hed-0 tel-0] [hed-1 tel-1]]
    ::
        %both
      =^  r-0  gen  re
      =^  r-1  gen  re
      =^  [hed-0=need hed-1=need]  gen  $(ned h.ned)
      =^  [tel-0=need tel-1=need]  gen  $(ned t.ned)
      :_  gen
      [[%both r-0 c.ned hed-0 tel-0] [%both r-1 c.ned hed-1 tel-1]]  ::  XX c.ned?
    ==
  ::  o2 is empty
  ::  a -> b  ==>  a -> o' ... o'' -> b
  ::
  ++  insert-hop
    |=  [a=@uwoo o1=@uwoo o2=@uwoo]
    ^+  gen
    =/  blob-from=blob  (~(got by blocks.gen) a)
    ?>  ?=(%hop -.fin.blob-from)
    :: ?>  =(~ body.blob-from)
    ?>  =(~ par.blob-from)
    ?>  =(~ args.t.fin.blob-from)
    =/  b=@uwoo  there.t.fin.blob-from
    =.  gen  (emir o2 ~ ~ %hop ~ b)
    =.  blocks.gen  (~(put by blocks.gen) a blob-from(there.t.fin o1))
    gen
  ::
  ++  fork
    |=  [nex=next r-cond=@uvre]
    ^-  [[next next] _gen]
    =^  o-0  gen  oo
    =^  o-1  gen  oo
    =;  [[laz-0=need-lazy laz-1=need-lazy] gen1=_gen]
      =.  gen  gen1
      :_  gen
      :-  [%next laz-0 ~ o-0]
      [%next laz-1 ~ o-1]
    ::
    =/  laz=need-lazy  laz.nex
    =/  o=@uwoo  there.then.nex
    |-  ^-  [[need-lazy need-lazy] _gen]
    =*  fork-loop  $
    =^  [sure-0=need sure-1=need]  gen
      (fork-sure sure.laz o o-0 o-1)
    ::
    =*  fork  ,(list [[@uwoo need-lazy] [@uwoo need-lazy]])
    ::
    =^  [fork-0=fork fork-1=fork]  gen
      |-  ^-  [[fork fork] _gen]
      =*  fork-smol-loop  $  ::  pay attention to equivocation
      ?~  fork.laz  [[~ ~] gen]
      =^  o-0-kid-y    gen  oo
      =^  o-1-kid-y    gen  oo
      =^  o-0-kid-n    gen  oo
      =^  o-1-kid-n    gen  oo
      =^  o-insert2-y  gen  oo
      =^  o-insert2-n  gen  oo
      =^  [laz-y-0=need-lazy laz-y-1=need-lazy]  gen
        %=  fork-loop
          laz  laz.y.i.fork.laz
          o    o-insert2-y
          o-0  o-0-kid-y
          o-1  o-1-kid-y
        ==
      ::
      =^  [laz-n-0=need-lazy laz-n-1=need-lazy]  gen
        %=  fork-loop
          laz  laz.n.i.fork.laz
          o    o-insert2-n
          o-0  o-0-kid-n
          o-1  o-1-kid-n
        ==
      ::
      =^  o-insert1-y=@uwoo  gen
        (emit ~ ~ [%brn r-cond ~^o-0-kid-y ~^o-1-kid-y])
      ::
      =^  o-insert1-n=@uwoo  gen
        (emit ~ ~ [%brn r-cond ~^o-0-kid-n ~^o-1-kid-n])
      ::
      =.  gen  (insert-hop o.y.i.fork.laz o-insert1-y o-insert2-y)
      =.  gen  (insert-hop o.n.i.fork.laz o-insert1-n o-insert2-n)
      =^  [fork-0-rest=fork fork-1-rest=fork]  gen  
        fork-smol-loop(fork.laz t.fork.laz)
      ::
      :_  gen
      :-  :_  fork-0-rest
          [[o-0-kid-y laz-y-0] [o-0-kid-n laz-n-0]]
      :_  fork-1-rest
      [[o-1-kid-y laz-y-1] [o-1-kid-n laz-n-1]]
    ::
    =*  bond  ,(list [o=@uwoo laz=need-lazy])
    =^  [bond-0=bond bond-1=bond]  gen
      |-  ^-  [[bond bond] _gen]
      =*  bond-loop  $
      ?~  bond.laz  [[~ ~] gen]
      =^  o-0-kid    gen  oo
      =^  o-1-kid    gen  oo
      =^  o-insert2  gen  oo
      =^  [laz-0=need-lazy laz-1=need-lazy]  gen
        %=  fork-loop
          laz  laz.i.bond.laz
          o    o-insert2
          o-0  o-0-kid
          o-1  o-1-kid
        ==
      ::
      =^  o-insert1=@uwoo  gen  (emit ~ ~ [%brn r-cond ~^o-0-kid ~^o-1-kid])
      =.  gen  (insert-hop o.i.bond.laz o-insert1 o-insert2)
      =^  [bond-0-rest=bond bond-1-rest=bond]  gen
        bond-loop(bond.laz t.bond.laz)
      ::
      :_  gen
      :-  [[o-0-kid laz-0] bond-0-rest]
      [[o-1-kid laz-1] bond-1-rest]
    ::
    :_  gen
    :-  [sure-0 fork-0 bond-0]
    [sure-1 fork-1 bond-1]
  ::  fork CFG for loobean-producing opcodes
  ::
  ++  forl
    |=  [r=@uvre o=@uwoo]
    ^-  [[@uwoo @uwoo] _gen]
    =^  r-0   gen  re
    =^  r-1   gen  re
    =^  barg  gen  (emit ~[r] ~ %hop ~ o)
    =^  if-0  gen  (emit ~ [%imm `*`0 r-0]~ %hop ~[r-0] barg)
    =^  if-1  gen  (emit ~ [%imm `*`1 r-1]~ %hop ~[r-1] barg)
    [[if-0 if-1] gen]
  ::
  ++  emit
    |=  =blob
    ^-  [@uwoo _gen]
    =^  o  gen  oo
    [o (emir o blob)]
  ::
  ++  from-need
    |=  [axe=@ ned=need]
    ^-  need
    ?<  =(0 axe)
    |-  ^-  need
    ?:  =(1 axe)  ned
    ?-  (cap axe)
      %2  [$(axe (mas axe)) none+~]
      %3  [none+~ $(axe (mas axe))]
    ==
  ::
  ++  from
    |=  [axe=@ laz=need-lazy]
    ^-  need-lazy
    =*  from  .
    :+  (from-need axe sure.laz)
      %+  turn  fork.laz
      |=  [y=[there=@uwoo laz=need-lazy] n=[there=@uwoo laz=need-lazy]]
      =.  laz.y  (from axe laz.y)
      =.  laz.n  (from axe laz.n)
      [y n]
    %+  turn  bond.laz
    |=  [o=@uwoo laz=need-lazy]
    [o (from axe laz)]
  ::
  ++  copy
    |=  [first=next second=need-lazy]
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %hop then.first)
    =^  laz=need-lazy  gen  (copy-lazy o laz.first second)
    [[%next laz ~ o] gen]
  ::
  ++  copy-lazy
    |=  [o=@uwoo first=need-lazy second=need-lazy]
    ^-  [need-lazy _gen]
    =^  [sure=need ops=(list pole)]  gen
      (copy-sure-make-ops sure.first sure.second)
    ::
    =.  gen  (add-ops o ops)
    [[sure (weld fork.first fork.second) (weld bond.first bond.second)] gen]
  ::
  ++  into-need
    |=  [axe=@ ned=need o=@uwoo]
    ^-  [[need need] _gen]
    ?<  =(0 axe)
    ?:  =(1 axe)  [[ned none+~] gen]
    =|  tack=(list [h=? n=need])
    =|  ops=(list pole)
    |^  ^-  [[need need] _gen]
    ?:  =(1 axe)
      =.  gen  (add-ops o ops)
      =;  big=need  [[ned big] gen]
      %+  roll  tack
      |:  [*[h=? n=need] acc=`need`[%none ~]]
      ?:  h  (cons acc n)
      (cons n acc)
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
      =^  l  gen  (must h.ned)
      =^  r  gen  (must t.ned)
      =/  =pole  [%con p.l p.r r.ned]
      =+  [new old]=?:(h [q.l q.r] [q.r q.l])
      $(tack [[h old] tack], ned new, ops [pole ops], axe lat)
    ==
    ::
    ++  cons
      |=  [a=need b=need]
      ^-  need
      ?:  &(?=(%none -.a) ?=(%none -.b))  none+~
      [a b]
    --
  ::
  ++  into
    |=  [nex=next axe=@]
    ^-  [[need-lazy need-lazy @uwoo] _gen]
    =^  o=@uwoo  gen  (emit ~ ~ %hop then.nex)
    =;  [[ned-don=need-lazy ned-rec=need-lazy] gen=_gen]
      [[ned-don ned-rec o] gen]
    ::
    =/  laz=need-lazy  laz.nex
    |-  ^-  [[need-lazy need-lazy] _gen]
    =*  split-loop  $
    =^  [sure-don=need sure-rec=need]  gen  (into-need axe sure.laz o)
    =*  fork  ,(list [[@uwoo need-lazy] [@uwoo need-lazy]])
    =^  [fork-don=fork fork-rec=fork]  gen
      |-  ^-  [[fork fork] _gen]
      =*  fork-loop  $
      ?~  fork.laz  [[~ ~] gen]
      =^  [laz-y-don=need-lazy laz-y-rec=need-lazy]  gen
        split-loop(laz laz.y.i.fork.laz, o o.y.i.fork.laz)
      ::
      =^  [laz-n-don=need-lazy laz-n-rec=need-lazy]  gen
        split-loop(laz laz.n.i.fork.laz, o o.n.i.fork.laz)
      ::
      =^  [fork-don-rest=fork fork-rec-rest=fork]  gen  
        fork-loop(fork.laz t.fork.laz)
      ::
      :_  gen
      :-  :_  fork-don-rest
          [[o.y.i.fork.laz laz-y-don] [o.n.i.fork.laz laz-n-don]]
      :_  fork-rec-rest
      [[o.y.i.fork.laz laz-y-rec] [o.n.i.fork.laz laz-n-rec]]
    ::
    =*  bond  ,(list [o=@uwoo laz=need-lazy])
    =^  [bond-don=bond bond-rec=bond]  gen
      |-  ^-  [[bond bond] _gen]
      =*  bond-loop  $
      ?~  bond.laz  [[~ ~] gen]
      =^  [laz-don=need-lazy laz-rec=need-lazy]  gen
        split-loop(laz laz.i.bond.laz, o o.i.bond.laz)
      ::
      =^  [bond-don-rest=bond bond-rec-rest=bond]  gen
        bond-loop(bond.laz t.bond.laz)
      ::
      :_  gen
      :-  [[o.i.bond.laz laz-don] bond-don-rest]
      [[o.i.bond.laz laz-rec] bond-rec-rest]
    ::
    :_  gen
    :-  [sure-don fork-don bond-don]
    [sure-rec fork-rec bond-rec]
  ::
  ++  split-need
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
      =^  hed  gen  (must h.ned)
      =^  tel  gen  (must t.ned)
      =.       gen  (add-ops o [%con p.hed p.tel r.ned]~)
      [[q.hed q.tel] gen]
    ==
  ::
  ++  must
    |=  ned=need
    ^-  [(pair @uvre $>(?(%both %this) need)) _gen]
    ?-  -.ned
      %both  [[r.ned ned] gen]
      %this  [[r.ned ned] gen]
      ^      =^(r gen re [[r %both r | ned] gen])
      %none  =^(r gen re [[r %this r] gen])
    ==
  ::
  ++  split
    |=  nex=next
    ^-  [[need-lazy need-lazy @uwoo] _gen]
    ::  emit an empty basic block
    ::
    =^  o=@uwoo  gen  (emit ~ ~ %hop then.nex)
    =;  [[ned-h=need-lazy ned-t=need-lazy] gen=_gen]
      [[ned-h ned-t o] gen]
    =/  laz=need-lazy  laz.nex
    |-  ^-  [[need-lazy need-lazy] _gen]
    =*  split-loop  $
    =^  [sure-h=need sure-t=need]  gen  (split-need sure.laz o)
    =*  fork  ,(list [[@uwoo need-lazy] [@uwoo need-lazy]])
    =^  [fork-h=fork fork-t=fork]  gen
      |-  ^-  [[fork fork] _gen]
      =*  fork-loop  $
      ?~  fork.laz  [[~ ~] gen]
      =^  [laz-y-h=need-lazy laz-y-t=need-lazy]  gen
        split-loop(laz laz.y.i.fork.laz, o o.y.i.fork.laz)
      ::
      =^  [laz-n-h=need-lazy laz-n-t=need-lazy]  gen
        split-loop(laz laz.n.i.fork.laz, o o.n.i.fork.laz)
      ::
      =^  [fork-h-rest=fork fork-t-rest=fork]  gen  
        fork-loop(fork.laz t.fork.laz)
      ::
      :_  gen
      :-  :_  fork-h-rest
          [[o.y.i.fork.laz laz-y-h] [o.n.i.fork.laz laz-n-h]]
      :_  fork-t-rest
      [[o.y.i.fork.laz laz-y-t] [o.n.i.fork.laz laz-n-t]]
    ::
    =*  bond  ,(list [o=@uwoo laz=need-lazy])
    =^  [bond-h=bond bond-t=bond]  gen
      |-  ^-  [[bond bond] _gen]
      =*  bond-loop  $
      ?~  bond.laz  [[~ ~] gen]
      =^  [laz-h=need-lazy laz-t=need-lazy]  gen
        split-loop(laz laz.i.bond.laz, o o.i.bond.laz)
      ::
      =^  [bond-h-rest=bond bond-t-rest=bond]  gen
        bond-loop(bond.laz t.bond.laz)
      ::
      :_  gen
      :-  [[o.i.bond.laz laz-h] bond-h-rest]
      [[o.i.bond.laz laz-t] bond-t-rest]
    ::
    :_  gen
    :-  [sure-h fork-h bond-h]
    [sure-t fork-t bond-t]
  ::
  ++  add-ops  ::  XX order of added ops
    |=  [o=@uwoo ops=(list pole)]
    ^+  gen
    =/  =blob  (~(got by blocks.gen) o)
    =.  body.blob  (weld body.blob ops)
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  emir
    |=  [o=@uwoo =blob]
    ^+  gen
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  bomb
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %bom ~)
    [[%next [[%none ~] ~ ~] ~ o] gen]
  ::
  ++  copy-sure-make-ops
    |=  [first=need second=need]
    ^-  [[need (list pole)] _gen]
    =|  ops=(list pole)
    =|  sout=(list need)
    =/  sin=(list (each (unit [r=@uvre c=?]) [l=need r=need]))
      [|+[first second]]~
    ::
    |-  ^-  [[need (list pole)] _gen]
    ?~  sin
      ?>  ?=([* ~] sout)
      [[i.sout ops] gen]
    ?:  ?=(%& -.i.sin)
      ?>  ?=([* * *] sout)
      =/  par  [i.t.sout i.sout]
      %=  $
        sin   t.sin
        sout  :_  t.t.sout
                ?~  p.i.sin  par
                =*  both  u.p.i.sin
                [%both r.both c.both par]
      ==
    =*  l  l.p.i.sin
    =*  r  r.p.i.sin
    ?:  ?=(%none -.l)  $(sout [r sout], sin t.sin)
    ?:  ?=(%none -.r)  $(sout [l sout], sin t.sin)
    ?:  ?=(%this -.l)
      ?:  ?=(%this -.r)
        ~?  =(r.l r.r)  [%copy-this-l-a r.l r.r]
        $(ops [[%mov r.l r.r] ops], sout [l sout], sin t.sin)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x | r] gen]))
      ~?  =(r.l r.rr)  [%copy-this-l-b r.l r.rr]
      $(ops [[%mov r.rr r.l] ops], sout [rr sout], sin t.sin)
    ?:  ?=(%this -.r)
      =^  ll=$>(%both need)  gen
        ?@(-.l [l gen] =^(x gen re [[%both x | l] gen]))
      ~?  =(r.ll r.r)  [%copy-this-r r.ll r.r]
      $(ops [[%mov r.ll r.r] ops], sout [ll sout], sin t.sin)
    ?:  ?=(%both -.l)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x | r] gen]))
      ~?  =(r.l r.rr)  [%copy-both r.l r.rr]
      %=  $
        ops   [[%mov r.rr r.l] ops]
        ::  if the first computation checks that the noun in r.rr/r.l is a cell,
        ::  then the second one does not need to be checked, and in total the
        ::  computation is checked
        ::  if the first computation does not check, then it will have to be
        ::  checked upstream, so the total computation is not checked
        ::
        ::  XX reconsider mixed case ^ / %both
        ::
        sin  [|+[h.l h.rr] |+[t.l t.rr] &+`[r.rr c.l] t.sin]
      ==
    ?^  -.r
      $(sin [|+[p.l p.r] |+[q.l q.r] &+~ t.sin])
    ::  first computation does not have a cell check for r.r,
    ::  so r.r will need to be checked upstream
    ::
    $(sin [|+[p.l h.r] |+[q.l t.r] &+`[r.r |] t.sin])
  ::
  ++  coerce
    |=  [need-pessimized=need-ordered nex=next-resolved]
    ^-  [next-resolved _gen]
    =;  [ned=need gen1=_gen]  [[%next [ned ~ ~] [~ then.nex]] gen1]
    |-  ^-  [need _gen]
    ?-    -.need-pessimized
        %none
      ?>  ?=(%none -.ned.nex)
      [[%none ~] gen]
    ::
        %this
      ?:  ?=(%this -.ned.nex)  [ned.nex gen]
      =^  r  gen  (kern-r then.nex ned.nex)
      [[%this r] gen]
    ::
        ^
      ?:  ?=(%none -.ned.nex)
        =^  hed  gen  $(need-pessimized -.need-pessimized)
        =^  tel  gen  $(need-pessimized +.need-pessimized)
        [[hed tel] gen]
      ?:  ?=(%this -.ned.nex)  !!
      =^  r  gen  (kern-r then.nex ned.nex)
      [[%this r] gen]
    ::
        %both
      =^  r  gen  (kern-r then.nex ned.nex)
      [[%this r] gen]
    ==
  ::
  ++  combine
    |=  [y=[o=@uwoo ned=need] n=[o=@uwoo ned=need]]
    ^-  [need _gen]
    ?:  &(?=(%none -.ned.y) ?=(%none -.ned.n))
      [[%none ~] gen]
    ?:  |(?=(%none -.ned.y) ?=(%none -.ned.n))
      =/  [o-not-none=@uwoo ned-not-none=need]  ?:(?=(%none -.ned.y) n y)
      =^  r  gen  (kern-r o-not-none ned-not-none)
      [[%this r] gen]
    ?:  &(?=(%this -.ned.y) ?=(%this -.ned.n))
      ::  move r.ned.y -> r.ned.n: arbitrary choice
      ::
      =.  gen  (add-ops o.n [%mov r.ned.y r.ned.n]~)
      [ned.y gen]
    ?:  &(?=(^ -.ned.y) ?=(^ -.ned.n))
      =^  hed=need  gen  $(ned.y -.ned.y, ned.n -.ned.n)
      =^  tel=need  gen  $(ned.y +.ned.y, ned.n +.ned.n)
      [[hed tel] gen]
    ?:  |(?=(%this -.ned.y) ?=(%this -.ned.n))
      ::  the other is ^ or %both
      ::
      =/  [[o-not-this=@uwoo ned-not-this=need] [o-this=@uwoo ned-this=$>(%this need)]]
        ?:  ?=(%this -.ned.y)  [n y]
        ?:  ?=(%this -.ned.n)  [y n]
        ~|  %impossible
        !!
      ::
      =^  b=$>(%both need)  gen
        ?@  -.ned-not-this
          ?>  ?=(%both -.ned-not-this)
          [ned-not-this gen]
        =^  x  gen  re
        [[%both x | ned-not-this] gen]
      ::
      =.  gen  (add-ops o-this [%mov r.b r.ned-this]~)
      [b gen]
    ::  one is %both, the other is ^ or %both
    ::
    =^  b-y=$>(%both need)  gen
      ?@  -.ned.y
        ?>  ?=(%both -.ned.y)
        [ned.y gen]
      =^  x  gen  re
      [[%both x | ned.y] gen]
    ::
    =^  b-n=$>(%both need)  gen
      ?@  -.ned.n
        ?>  ?=(%both -.ned.n)
        [ned.n gen]
      =^  x  gen  re
      [[%both x | ned.n] gen]
    ::
    =^  h  gen  $(ned.y h.b-y, ned.n h.b-n)
    =^  t  gen  $(ned.y t.b-y, ned.n t.b-n)
    =.  gen  (add-ops o.n [%mov r.b-y r.b-n]~)
    =?  gen  !=(c.b-y c.b-n)
      ?:  c.b-y  (add-ops o.n [%cel r.b-n]~)
      (add-ops o.y [%cel r.b-y]~)
    ::
    [[%both r.b-y |(c.b-y c.b-n) h t] gen]
  ::
  ++  need-lazy-collapse
    |=  [o=@uwoo laz=need-lazy]
    ^-  [need _gen]
    =*  collapse  .
    ?:  &(=(~ fork.laz) =(~ bond.laz))
      [sure.laz gen]
    =^  bond-collapsed=(list need)  gen
      %^  spin  bond.laz  gen
      |=  [[o-bond=@uwoo laz-bond=need-lazy] gen-init=_gen]
      ^-  [need _gen]
      =.  gen  gen-init
      =^  [ned-forward=need ops=(list pole)]  gen
        (copy-sure-make-ops sure.laz sure.laz-bond)
      ::
      =.  gen  (add-ops o-bond ops)
      (collapse o-bond laz-bond(sure ned-forward))
    ::
    =^  sure-with-bond=need  gen
      %+  roll  bond-collapsed
      |=  [bon=need sure=_sure.laz gen-init=_gen]
      ^-  [need _gen]
      =.  gen  gen-init
      =^  [ned=need ops=(list pole)]  gen  (copy-sure-make-ops sure bon)
      [ned (add-ops o ops)]
    ::
    =^  fork-collapsed=(list [y=[o=@uwoo ned=need] n=[o=@uwoo ned=need]])  gen
      %^  spin  fork.laz  gen
      |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen-init=_gen]
      ^-  [[[@uwoo need] [@uwoo need]] _gen]
      =.  gen  gen-init
      =^  ned-y=need  gen
        =^  [ned-forward=need ops=(list pole)]  gen
          (copy-sure-make-ops sure-with-bond sure.laz.y)
        ::
        =.  gen  (add-ops o.y ops)
        (collapse o.y laz.y(sure ned-forward))
      ::
      =^  ned-n=need  gen
        =^  [ned-forward=need ops=(list pole)]  gen
          (copy-sure-make-ops sure-with-bond sure.laz.n)
        ::
        =.  gen  (add-ops o.n ops)
        (collapse o.n laz.n(sure ned-forward))
      ::
      [[[o.y ned-y] [o.n ned-n]] gen]
    ::
    =^  fork-joined=(list need)  gen
      %^  spin  fork-collapsed  gen
      |=  [[y=[o=@uwoo ned=need] n=[o=@uwoo ned=need]] gen-init=_gen]
      ^-  [need _gen]
      (combine(gen gen-init) y n)
    ::
    %+  roll  fork-joined
    |=  [jon=need sure=_sure-with-bond gen-init=_gen]
    ^-  [need _gen]
    =.  gen  gen-init
    =^  [ned=need ops=(list pole)]  gen  (copy-sure-make-ops sure jon)
    [ned (add-ops o ops)]
  ::
  ++  next-lazy-collapse
    |=  nex=next
    ^-  [next-resolved _gen]
    ?>  =(~ args.then.nex)
    =^  ned=need  gen  (need-lazy-collapse there.then.nex laz.nex)
    [[%next [ned ~ ~] ~ there.then.nex] gen]
  ::
  ::  Renumber the registers so that the input registers are 0-N, set the starting
  ::  block index to 0w0
  ::
  ++  to-straight
    |=  nex=next-resolved
    ^-  straight
    =/  blocks=(map @uwoo blob)  blocks.gen
    =/  start=blob  (~(got by blocks) then.nex)
    =.  blocks  (~(del by blocks) then.nex)
    =.  blocks  (~(put by blocks) `@`0 start)
    =|  gen=[re-gen=@uvre m=(map @uvre @uvre)]
    |^  ^-  straight
    =^  input=need-ordered  gen  (rewrite-input ned.nex)
    :+  input  (count-args input)
    =<  new
    ^-  [new=(map @uwoo blob) *]
    %-  ~(rep by blocks)
    |=  [[k=@uwoo b=blob] new=(map @uwoo blob) gen-acc=_gen]
    =.  gen  gen-acc
    =;  [b1=blob gen1=_gen]
      :_  gen1
      (~(put by new) k b1)
    ::
    =^  par1   gen  (rewrite-par par.b)
    =^  body1  gen  (rewrite-body body.b)
    =^  fin1   gen  (rewrite-fin fin.b)
    :_  gen
    [par1 body1 fin1]
    ::
    ++  rer
      |=  r=@uvre
      ^-  [@uvre _gen]
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
        [[%both c.ned h t] gen]
      ==
    ::
    ++  rewrite-par
      |=  par=(list @uvre)
      ^-  [(list @uvre) _gen]
      %^  spin  par  gen
      |=  [r=@uvre =_gen]
      (rer(gen gen) r)
    ::
    ++  rewrite-body
      |=  bod=(list pole)
      ^-  [(list pole) _gen]
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
          %hop
        =^  t1  gen  (rewrite-jump t.fin)
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
          %don
        =^  s1  gen  (rer s.fin)
        [fin(s s1) gen]
      ::
          %bom
        [fin gen]
      ==
    ::
    ++  rewrite-jump
      |=  j=jmp
      ^-  [jmp _gen]
      =^  args1  gen  (rewrite-par args.j)
      [j(args args1) gen]
    --
  --
::
::
++  count-args
  |=  args=need-ordered
  ^-  @ud
  ?-  -.args
    %none  0
    %this  1
    ^      (add $(args -.args) $(args +.args))
    %both  +((add $(args h.args) $(args t.args)))
  ==
::
++  msg-need-ord
  |=  [a=need-ordered b=need-ordered]
  ^-  need-ordered
  =*  msg  .
  ?:  =(a b)  a
  ?:  ?|  ?=(%this -.a)
          ?=(%none -.a)
          ?=(%this -.b)
          ?=(%none -.b)
      ==
    this+~
  ?:  ?=(%both -.a)
    ?:  ?=(%both -.b)
      ?>  =(c.a c.b)
      [%both c.a (msg h.a h.b) (msg t.a t.b)]
    [%both c.a (msg h.a p.b) (msg t.a q.b)]
  ?:  ?=(%both -.b)
    [%both c.b (msg p.a h.b) (msg q.a t.b)]
  [(msg p.a p.b) (msg q.a q.b)]
--