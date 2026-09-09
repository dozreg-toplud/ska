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
::    Call graph construction:  line 508
::    Compilation:              line 2143
::    IR optimization passes:   line 4469
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
::    With partial noun logic defined, we can move on to the description of call
::    graph construction.  The overall goal is, given a pair of a subject and a
::    formula, to construct:
::      - a code subject mask, which describes the code requirements of the SKA
::        function,
::      - a call graph, with that SKA function as the root,
::      - a code + data subject mask, which is used to cache the analysis
::        result.  The data mask is necessary due to potential subject capture
::        by the function.
::
::    The implementation below works by finding a fixed point of a function F
::    that maps a set of SKA function calls onto itself by, formally, partially
::    evaluating each callsite in the set, using the information from the
::    previous set for Nock 2 handling.  In practice this means breadth-first
::    iteration over the call graph with back-propagation of changes.  This
::    appears to be the same thing as "chaotic iteration over a lattice" in the
::    literature.
::
::    The algorithm assumes that the set of SKA function calls forms a complete
::    lattice, and the fixed point is found via Kleene iteration, starting from
::    the least element of the lattice that contains the root call.
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
      =/  entry  [(~(got by just-code) b) | |]
      :-  (~(put by code.acc) b entry)
      (put-fols b entry fols.acc)
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
    =;  loc2=local
      :: ?.  =(loc1 loc2)  fixpoint-loop(loc1 loc2)
      =.  code.lon  code.loc2
      =.  fols.lon  fols.loc2
      scc-loop(sccs t.sccs)
    ::
    %-  ~(rep in scc)
    |=  [b=bell acc=_loc1]
    ^+  acc
    =/  [pure=? total=?]  (eval-finalized b code.acc)
    =/  lens  |=(=code-entry code-entry(pure pure, total total))
    =.  code.acc  (~(jab by code.acc) b lens)
    =.  fols.acc
      %+  ~(jab by fols.acc)  fol.b
      |=  m=(map bell code-entry)
      (~(jab by m) b lens)
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
::  pure: no crashes + no hints excepts %fast (call to it could be omitted)
::  total: no crashes (stacktrace boundaries around them could be omitted)
::
++  eval-finalized
  =*  hint-pure  ,?(%fast %spot %mean)
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
      [%12 *]  [|+~ | |]
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
|%
+$  hint-static  ?(%bout %xray)
+$  hint-dynamic  ?(%bout %xray %spin %loop %jinx %live hint-dynamic-stop)
+$  hint-dynamic-stop  ?(%hunk %hand %lose %mean %spot %slog)
::  Data requirement of a computation. %both means both the root noun and some
::  of its descendants.
::  Normalizations: [[%none ~] [%none ~]] --> [%none ~]
::                  [%both x [%none ~] [%none ~]] --> [%this x]
+$  need
  $~  [%none ~]
  $^  [p=need q=need]
  $%  [%both r=@uvre h=need t=need]
      [%this r=@uvre]
      [%none ~]
  ==
::  Same as $need but no registers allocated, pure shape.
::
+$  need-ordered
  $~  [%none ~]
  $^  [p=need-ordered q=need-ordered]
  $%  [%both h=need-ordered t=need-ordered]
      [%this ~]
      [%none ~]
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
::  one side, a new target register is allocated that becomes the input parameter
::  in the merging block, and on the other side a dummy register is used as an
::  input with a placeholder value. The proxy register now points to the new
::  target in the merging block. At the function entry the proxies are guaran-
::  teed to be dominated by their respective defined registers, so +rewrite-cond
::  rewrites the proxies with their definitions directly.
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
::  Inner state for the linearizer
::
+$  line-short
  $:  re-gen=@uvre
      bo-gen=_`@uwoo`1  ::  0 is reserved for the entry point
      blocks=(map @uwoo blob)
      id-gen=@uxid                   ::  branch region identifiers
      tags=(map @uwoo (list @uxid))  ::  region of lazy need blocks
      =cond
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
      [%hsp n=hint-static f=*]                    ::  prologue of a static hint
      [%hse n=hint-static f=*]                    ::  epilogue of a static hint
      [%hdp n=hint-dynamic p=@uvre f=*]           ::  prologue of a dynamic hint
      [%hde n=hint-dynamic p=@uvre f=*]           ::  epilogue of a dynamic hint
      [%spy e=@uvre p=@uvre d=@uvre]              ::  .^(e p) -> d
      [%nok u=@uvre f=@uvre d=@uvre]              ::  .*(u f) -> d
      [%cal a=bell v=(list @uvre) d=@uvre]        ::  a(v) -> d
      [%caf a=bell v=(list @uvre) d=@uvre n=ring] ::  %cal but maybe jetted
      [%cam a=bell v=(list @uvre) d=@uvre k=*]    ::  %cal but memoized
      [%csl a=bell s=@uvre d=@uvre]               ::  %cal but sub is in one reg
      [%csf a=bell s=@uvre d=@uvre n=ring]        ::  %caf but sub is in one reg
      [%csm a=bell s=@uvre d=@uvre k=*]           ::  %cam but sub is in one reg
  ==
::  Control-flow ops
::
+$  termin
  $%  [%clq s=@uvre z=jmp o=jmp]            ::  ?^  s
      [%eqq l=@uvre r=@uvre z=jmp o=jmp]    ::  ?:  =(l r)
      [%brn s=@uvre z=jmp o=jmp]            ::  ?:  s  (crashes on non-loobean)
      [%hop t=jmp]                          ::  unconditional block jump
      [%jmp a=bell v=(list @uvre)]          ::  %cal but in tail position
      [%jmf a=bell v=(list @uvre) n=ring]   ::  %caf but in tail position
      [%jsp a=bell s=@uvre]                 ::  %jmp but sub is in one reg
      [%jsf a=bell s=@uvre n=ring]          ::  %jmf but sub is in one reg
      [%don s=@uvre]                        ::  return s
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
    %hsp  ~
    %hse  ~
    %hdp  ~
    %hde  ~
    %spy  ~
    %nok  ~
    %cal  ~
    %caf  ~
    %cam  ~
    %csl  ~
    %csf  ~
    %csm  ~
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
    %hsp  ~
    %hse  ~
    %hdp  ~[p]:op
    %hde  ~[p]:op
    %spy  ~[e p d]:op
    %nok  ~[u f d]:op
    %cal  [d v]:op
    %caf  [d v]:op
    %cam  [d v]:op
    %csl  ~[s d]:op
    %csf  ~[s d]:op
    %csm  ~[s d]:op
    %clq  [s.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %eqq  [l.op r.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %brn  [s.op (weld (jmp-regs z.op) (jmp-regs o.op))]
    %hop  (jmp-regs t.op)
    %jmp  v:op
    %jmf  v:op
    %jsp  ~[s]:op
    %jsf  ~[s]:op
    %don  ~[s]:op
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
    %hop  ~[t]
    %jmp  ~
    %jmf  ~
    %jsp  ~
    %jsf  ~
    %don  ~
    %bom  ~
  ==
::  Rename every register of a block, definitions included
::
++  map-regs
  |=  ren=$-(@uvre @uvre)
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
      %hsp  op
      %hse  op
      %hdp  op(p (ren p.op))
      %hde  op(p (ren p.op))
      %spy  op(e (ren e.op), p (ren p.op), d (ren d.op))
      %nok  op(u (ren u.op), f (ren f.op), d (ren d.op))
      %cal  op(v (turn v.op ren), d (ren d.op))
      %caf  op(v (turn v.op ren), d (ren d.op))
      %cam  op(v (turn v.op ren), d (ren d.op))
      %csl  op(s (ren s.op), d (ren d.op))
      %csf  op(s (ren s.op), d (ren d.op))
      %csm  op(s (ren s.op), d (ren d.op))
    ==
  =/  fin  fin.b
  ?-  -.fin
    %clq  fin(s (ren s.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %eqq
      fin(l (ren l.fin), r (ren r.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %brn  fin(s (ren s.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
    %hop  fin(t (ren-jmp t.fin))
    %jmp  fin(v (turn v.fin ren))
    %jmf  fin(v (turn v.fin ren))
    %jsp  fin(s (ren s.fin))
    %jsf  fin(s (ren s.fin))
    %don  fin(s (ren s.fin))
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
++  compile-unary
  |=  $:  func=bell
          scc=(set bell)
          rev=(jug bell bell)  ::  reversed call graph
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
      ==
  ^-  [straight (map bell straight)]
  ~+
  =*  args  +<
  ::  Compile normally
  ::
  =/  n-ary-map=(map bell straight)  (compile-scc +.args)
  :_  n-ary-map
  ^-  straight
  =/  comp  (comp scc rev long-ska scc-map jets-hot n-ary-map func)
  ::  Compile the pessimized version
  ::
  =/  [nex=next gen=line-short]
    %-  ~(run comp *line-short)
    [& nomm:(~(got by code.long-ska) func) [%done ~] ~]
  ::  Collapse the subject need to a single noun, finalize
  ::
  =^  [o=@uwoo sub=@uvre]  gen  (~(kerf comp gen) nex)
  (~(to-straight comp gen) [%next [[this+sub ~] ~ ~] ~ o])
::
++  compile-scc
  |=  $:  scc=(set bell)
          rev=(jug bell bell)
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
      ==
  ^-  (map bell straight)
  ~+
  =|  map-local=(map bell straight)
  ::  Fixed-point loop with a worklist
  ::
  =/  w=worklist  scc
  =/  done=?  |
  |-  ^+  map-local
  =*  fixpoint-compilation  $
  =;  [w-new=worklist map-local1=(map bell straight)]
    ?:  done  map-local1
    =.  w-new  (~(int in w-new) scc)
    ?:  =(~ w-new)  fixpoint-compilation(w scc, map-local map-local1, done &)
    ~&  %fixpoint-compilation
    fixpoint-compilation(w w-new, map-local map-local1)
  ::
  %-  ~(rep in w)
  |=  [b=bell w-new=worklist =_map-local]
  ^+  [w-new map-local]
  =/  comp  (comp scc rev long-ska scc-map jets-hot map-local b)
  =;  [s=straight nex=next-resolved gen=line-short]
    ::  With a compiled function candidate, requeue callers if the subject split
    ::  did not converge yet, taking MSG of subject splits to avoid divergence.
    ::
    ?~  s-previous=(~(get by map-local) b)
      :-  ?:  ?=([%none ~] need.s)  w-new
          (~(uni in w-new) (~(get ju rev) b))
      (~(put by map-local) b s)
    =/  need-pessimized  (msg-need-ord need.s need.u.s-previous cape.less.b)
    :-  ?:  =(need-pessimized need.u.s-previous)  w-new
        (~(uni in w-new) (~(get ju rev) b))
    %+  ~(put by map-local)  b
    ?:  =(need-pessimized need.s)  s
    =^  coerced=next-resolved  gen  (~(coerce-ord comp gen) need-pessimized nex)
    (~(to-straight comp gen) coerced)
  ::  Compile the function normally, collapse lazy needs, finalize
  ::
  =/  [nex=next gen=line-short]
    (~(run comp *line-short) | nomm:(~(got by code.long-ska) b) [%done ~] ~)
  ::
  =^  res  gen  (~(next-lazy-collapse comp gen) nex cape.less.b)
  [(~(to-straight comp gen) res) res gen]
::
++  need-normalize
  |=  ned=need
  ^-  need
  =*  this  .
  ?-    -.ned
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
++  norm-need-lazy
  |=  laz=need-lazy
  ^-  ?
  &
  :: =*  this  .
  :: ?&  =(sure.laz (need-normalize sure.laz))
  ::     (levy fork.laz |=([[* y=need-lazy] * n=need-lazy] &((this y) (this n))))
  ::     (levy bond.laz |=([* laz=need-lazy] (this laz)))
  :: ==
::
++  comp
  |=  $:  scc=(set bell)
          rev=(jug bell bell)
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
          map-local=(map bell straight)
          b=bell
      ==
  |_  gen=line-short
  ++  run
    |=  [mono=? =nomm =goal region=(list @uxid)]
    |^  ^-  [next _gen]
    ?-    nomm
        [^ *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      =>  =*  dot  .
          ?.  ?=(%done -.goal)  dot
          =^  r  gen  re
          =^  o  gen  (emit ~ ~ [%don r])
          dot(goal [%next (lazy-from-reg r) ~ o])
      ::
      ?-    -.goal
          %pick
        ::  Autocons product is used as a conditional: it will crash and we
        ::  don't care about the particular values of the consed formulas,
        ::  though we still need to compile them for crash correctness
        ::
        =^  o  gen  (emit ~ ~ [%bom ~])
        =^  nex-2  gen  $(nomm +.nomm, goal [%next *need-lazy ~ o])
        =^  nex-1  gen  $(nomm -.nomm, goal [%next *need-lazy then.nex-2])
        ::  Here and later +copy is used to combine together two needs for one
        ::  subject
        ::
        (copy nex-1 laz.nex-2)
      ::
          %next
        =^  [hed=need-lazy tel=need-lazy o=@uwoo]  gen  (split goal)
        =^  nex-2  gen  $(nomm +.nomm, goal [%next tel ~ o])
        =^  nex-1  gen  $(nomm -.nomm, goal [%next hed then.nex-2])
        (copy nex-1 laz.nex-2)
      ==
    ::
        [%0 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      ?:  =(0 p.nomm)  (bomb ?:(?=(%next -.goal) `there.then.goal ~))
      =^  nex  gen  simple-next
      ?:  =(1 p.nomm)  [nex gen]
      [[%next (from p.nomm laz.nex) then.nex] gen]
    ::
        [%1 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      ?-    -.goal
          %done
        =^  r  gen  re
        =^  o  gen  (emit ~ ~[imm+[p.nomm r]] don+r)
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
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
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
        =^  nex-sub  gen
          $(nomm p.nomm, goal [%next (lazy-from-need this+r-sub) then.nex-fol])
        ::
        (copy nex-sub laz.nex-fol)
      =*  b-callee  b.u.info.nomm
      =/  callee-pure=?  pure:(~(got by code.long-ska) b-callee)
      ?:  &(callee-pure ?=(%next -.goal) (none-equivalent laz.goal))
        ::  The product is not used and the function is pure: drop
        ::
        =^  nex-fol=next  gen
          ?:  (safe-fol-fol q.nomm)  [[%next *need-lazy then.goal] gen]
          $(nomm q.nomm, goal [%next *need-lazy then.goal])
        ::
        =^  nex-sub  gen  $(nomm p.nomm, goal [%next *need-lazy then.nex-fol])
        (copy nex-sub laz.nex-fol)
      =*  call-cole  call.cole.jets.long-ska
      =/  rin=(unit ring)  (~(get by call-cole) b-callee)
      ::  register-less need of the callee: jet or SCC-local best guess or recur
      ::
      =/  b-ned=need-ordered
        ?^  j=(biff rin ~(get by jets-hot))  u.j
        ?:  (~(has in scc) b-callee)
          need:(~(gut by map-local) b-callee *straight)
        =/  new-scc=(set bell)  (~(gut by scc-map) b-callee [b-callee ~ ~])
        =;  m  need:(~(got by m) b-callee)
        =/  new-scc=(set bell)  (~(gut by scc-map) b-callee [b-callee ~ ~])
        (compile-scc new-scc rev long-ska scc-map jets-hot)
      ::  allocate registers
      ::
      =^  sub-ned=need  gen  (need-ord-alloc-regs b-ned)
      =/  sub-v=(list @uvre)  (flatten-need sub-ned)
      =^  call-blocks=$@(@uwoo [opt=@uwoo pes=[sub=@uvre o=@uwoo]])  gen
        =*  key  k.u.info.nomm
        =/  call-op
          |=  [pes=(unit @uvre) pro=@uvre]
          ^-  pole
          ?^  key
            ?~  pes  [%cam b-callee sub-v pro u.key]
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
        ::  Memoized calls are never TCO'd
        ::
        ?:  &(?=(~ key) ?=(%done -.goal))
          ?.  mono  (emit ~ ~ (jump-op ~))
          =^  sub-pes  gen  re
          =^  opt  gen  (emit ~ ~ (jump-op ~))
          =^  pes  gen  (emit ~ ~ (jump-op `sub-pes))
          [[opt sub-pes pes] gen]
        =^  nex  gen  simple-next
        =^  [out=@uwoo pro=@uvre]  gen  (kerf nex)
        ?.  mono  (emit ~ ~[(call-op ~ pro)] %hop ~ out)
        =^  merged   gen  re
        =^  sub-pes  gen  re
        =^  merge    gen  (emit ~[merged] [%mov merged pro]~ %hop ~ out)
        =^  pro-opt  gen  re
        =^  pro-pes  gen  re
        =^  opt      gen
          (emit ~ ~[(call-op ~ pro-opt)] %hop ~[`pro-opt] merge)
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
      =^  nex-fol=next  gen
        ?:  (safe-fol-fol q.nomm)  [[%next *need-lazy ~ call-block] gen]
        $(nomm q.nomm, goal [%next *need-lazy ~ call-block])
      ::
      =^  nex-sub  gen
        $(nomm p.nomm, goal [%next (lazy-from-need sub-ned) then.nex-fol])
      ::
      (copy nex-sub laz.nex-fol)
    ::
        [%3 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      ?:  &(?=(%next -.goal) (none-equivalent laz.goal))
        ::  Don't care about the product
        ::
        $(nomm p.nomm)
      =>  =*  dot  .
          ?-    -.goal
              %pick  dot
          ::
              %done
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
      =^  o  gen  (emit ~ ~ clq+[r [z o]:goal])
      $(nomm p.nomm, goal [%next (lazy-from-need this+r) ~ o])
    ::
        [%4 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      ?-    -.goal
          %done
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
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      =>  =*  dot  .
          ?-    -.goal
              %pick  dot
          ::
              %done
            =^  r-0  gen  re
            =^  r-1  gen  re
            =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
            =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
            dot(goal `$>(%pick ^goal)`[%pick ~^o-0 ~^o-1])
          ::
              %next
            =^  a=(unit [r=@uvre o=@uwoo])  gen  (collapse-lazy-atom goal)
            ?~  a
              ::  Compare for the sideeffect only
              ::
              ?>  =(~ args.then.goal)
              dot(goal `$>(%pick ^goal)`[%pick [. .]:~^there.then.goal])
            =^  [z=@uwoo o=@uwoo]  gen  (forl r.u.a o.u.a)
            dot(goal `$>(%pick ^goal)`[%pick ~^z ~^o])
          ==
      ::
      =^  r-p  gen  re
      =^  r-q  gen  re
      =^  o    gen  (emit ~ ~ eqq+[r-p r-q [z o]:goal])
      ::
      =^  nex-q  gen
        $(nomm q.nomm, goal [%next (lazy-from-need this+r-q) ~ o])
      ::
      =^  nex-p  gen
        $(nomm p.nomm, goal [%next (lazy-from-need this+r-p) then.nex-q])
      ::
      (copy nex-p laz.nex-q)
    ::
        [%6 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      ?:  ?&  ?=(%next -.goal)
              !(none-equivalent laz.goal(sure *sure))
              :: |(!=(~ fork.laz.goal) !=(~ bond.laz.goal))
          ==
        ::  In general case we have to materialize the conditional to handle
        ::  lazy needs. So we check if we really have to do this.
        ::
        =^  r-cond  gen  re
        =^  [goal-0=next goal-1=next]  gen  (fork goal r-cond)
        ::  both branches are in the same region
        ::
        =^  region-id  gen  id
        =/  region-branch  [region-id region]
        =/  cond-before  cond.gen
        =^  nex-1  gen  $(nomm r.nomm, goal goal-1, region region-branch)
        =/  cond-between  cond.gen
        =^  nex-0  gen  $(nomm q.nomm, goal goal-0, region region-branch)
        =^  [lazy=need-lazy yes=@uwoo nuh=@uwoo]  gen
          %-  sect
          :*  nex-0  nex-1  there.then.goal-0  there.then.goal-1
              region-branch  cond-before  cond-between
          ==
        ::
        =^  o=@uwoo  gen  (emit ~ ~ [%brn r-cond ~^yes ~^nuh])
        =^  nex-cond  gen
          $(nomm p.nomm, goal [%next (lazy-from-need this+r-cond) ~ o])
        ::
        (copy nex-cond lazy)
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
        =.  tags.gen  (~(gas by tags.gen) ~[[yes region] [nuh region]])
        :_  gen
        ?>  =(~ args.then.nex-0)
        ?>  =(~ args.then.nex-1)
        :_  [yes nuh]
        [*sure [[yes laz.nex-0] [nuh laz.nex-1]]~ ~]
      ::
      =^  nex-cond  gen  $(nomm p.nomm, goal [%pick ~^yes ~^nuh])
      (copy nex-cond lazy)
    ::
        [%7 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      =^  nex  gen  $(nomm q.nomm)
      $(nomm p.nomm, goal nex)
    ::
        [%10 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      =^  next  gen  simple-next
      =^  [don=need-lazy rec=need-lazy o=@uwoo]  gen  (into next p.p.nomm)
      =^  nex-rec  gen  $(nomm q.nomm, goal [%next rec ~ o])
      =^  nex-don  gen  $(nomm q.p.nomm, goal [%next don then.nex-rec])
      (copy nex-don laz.nex-rec)
    ::
        [%11 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      ?@  p.nomm
        ?.  ?=(hint-static p.nomm)  $(nomm q.nomm)
        =^  nex    gen  simple-next
        =^  epil    gen  (emit ~ ~[hse+[p.nomm body.nomm]] %hop then.nex)
        =^  nex-fol  gen  $(nomm q.nomm, goal nex(then [~ epil]))
        =^  prol    gen  (emit ~ ~[hsp+[p.nomm body.nomm]] %hop then.nex-fol)
        [[%next laz.nex-fol ~ prol] gen]
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  nex-fol  gen  $(nomm q.nomm)
        ?:  (safe-nomm q.p.nomm)  [nex-fol gen]
        =^  nex-toke  gen
          $(nomm q.p.nomm, goal [%next *need-lazy then.nex-fol])
        ::
        (copy nex-toke laz.nex-fol)
      =^  nex      gen  simple-next
      =^  toke     gen  re
      =^  epil     gen  (emit ~ ~[hde+[p.p.nomm toke body.nomm]] %hop then.nex)
      =^  nex-fol1  gen  $(nomm q.nomm, goal nex(then [~ epil]))
      =^  nex-fol2=next  gen
        ?.  ?=(hint-dynamic-stop p.p.nomm)  [nex-fol1 gen]
        (lazy-bound nex-fol1 region)
      ::
      =^  prol  gen
        (emit ~ ~[hdp+[p.p.nomm toke body.nomm]] %hop then.nex-fol2)
      ::
      =^  nex-toke  gen
        $(nomm q.p.nomm, goal [%next (lazy-from-reg toke) ~ prol])
      ::
      (copy nex-toke laz.nex-fol2)
    ::
        [%12 *]
      =;  [=next =_gen]
        ?>  (norm-need-lazy laz.next)
        [next gen]
      ::
      =^  nex  gen  simple-next
      =^  [out=@uwoo pro=@uvre]  gen  (kerf nex)
      =^  r-path     gen  re
      =^  r-ref      gen  re
      =^  o-spy      gen  (emit ~ [%spy r-ref r-path pro]~ %hop ~ out)
      =^  nex-path  gen
        $(nomm q.nomm, goal [%next (lazy-from-reg r-path) ~ o-spy])
      ::
      =^  nex-ref   gen
        $(nomm p.nomm, goal [%next (lazy-from-reg r-ref) then.nex-path])
      ::
      (copy nex-ref laz.nex-path)
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
      [[%next [[this+r ~] ~ ~] ~ o] gen]
    --
  ::
  ++  re  `[@uvre _gen]`[re-gen.gen gen(re-gen +(re-gen.gen))]
  ++  oo  `[@uwoo _gen]`[bo-gen.gen gen(bo-gen +(bo-gen.gen))]
  ++  id  `[@uxid _gen]`[id-gen.gen gen(id-gen +(id-gen.gen))]
  ++  kerf
    |=  =next
    ^-  [[@uwoo @uvre] _gen]
    =^  o  gen  (emit ~ ~ %hop then.next)
    =^  r=@uvre  gen  (kern o laz.next)
    [[o r] gen]
  ::
  ++  walk-lazy
    |=  [o=@uwoo laz=need-lazy f=$-([@uwoo sure _gen] _gen)]
    ^+  gen
    =*  walk  $
    !.
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
    |=  [o-laz=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  ned  gen  (sure-require-look sur)
    ?:  ?=(%none -.ned)  gen
    =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
    =^  ops  gen  (kern-need src ned)
    (add-ops o-laz ops)
  ::  Register to read `r` through in the lazy block `o`. Recorded in cond.gen
  ::  so that +sect can thread `r` through join blocks.
  ::
  ++  proxy
    |=  [r=@uvre o=@uwoo]
    ^-  [@uvre _gen]
    =^  p  gen  re
    [p gen(cond (~(put by cond.gen) p [r (~(got by tags.gen) o)]))]
  ::
  ++  kern-r-need
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
    :: =;  [ops=(list pole) gen=_gen]
      :: ~?  (lien ops |=(op=pole ?=(%cel -.op)))  [ops ned]
      :: [ops gen]
    ::
    |-  ^-  [(list pole) _gen]
    ?-    -.ned
        %none  [ops gen]
        %this  ?<  =(r r.ned)  [[[%mov r r.ned] ops] gen]
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
  ++  lazy-bound
    |=  [nex=next region=(list @uxid)]
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %hop then.nex)
    =.  tags.gen  (~(put by tags.gen) o region)
    :_  gen
    ?>  =(~ args.then.nex)
    [%next [*sure ~ [o laz.nex]~] ~ o]
  ::
  ++  sect
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
    =^  o-0-beg  gen  (emit ~ ~ %hop then.nex-0)
    =^  o-1-beg  gen  (emit ~ ~ %hop then.nex-1)
    =.  tags.gen
      (~(gas by tags.gen) ~[[o-0-beg region-branch] [o-1-beg region-branch]])
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
    :_  gen
    ?>  =(~ args.then.nex-0)
    ?>  =(~ args.then.nex-1)
    :_  [o-0-beg o-1-beg]
    [*sure [[o-0-beg laz.nex-0] [o-1-beg laz.nex-1]]~ ~]
  ::
  ++  mede
    |=  [then=jmp som=* laz=need-lazy]
    ^-  [@uwoo _gen]
    =^  o=@uwoo  gen  (emit ~ ~ %hop then)
    :-  o
    %^  walk-lazy  o  laz
    |=  [o=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  ned  gen  (sure-require-look sur)
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
      ?:  ?=(@ som)  (emir o ~ ~ %bom ~)
      =.  gen  (add-ops o [%imm som r.ned]~)
      =.  gen  $(som -.som, ned h.ned)  ::  XX no +kern here, is OK?
      $(som +.som, ned t.ned)
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
    =^  ned-sure=need  gen  (sure-require-look sure.laz.nex)
    =^  r=@uvre  .
      =*  dot  .
      ?-    -.ned-sure
          %this
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
    ::  add moves wherever lazy needs need one noun, crashes wherever lazy needs
    ::  need more than an atom
    ::
    %^  walk-lazy  there.then.nex  laz.nex(ned.sure this+r)
    |=  [o=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  ned-sure=need  gen  (sure-require-look sur)
    ?:  ?=(%none -.ned-sure)  gen
    ?:  ?=(%this -.ned-sure)
      ?:  =(r r.ned-sure)  gen
      =^  src  gen  ?:(=(o there.then.nex) [r gen] (proxy r o))
      (add-ops o [%mov src r.ned-sure]~)
    (emir o ~ ~ %bom ~)
  ::
  ++  flatten-need
    |=  ned=need
    ^-  (list @uvre)
    =*  flat  .
    ?-  -.ned
      %none  ~
      %this  ~[r.ned]
      ^      (weld (flat -.ned) (flat +.ned))
      %both  [r.ned (weld (flat h.ned) (flat t.ned))]
    ==
  ::  fork CFG
  ::
  ::  Produces a pair of needs, emitting code into given o-0/1 provided by the
  ::  caller
  ::
  ++  fork-sure
    |=  [sur=sure o=@uwoo o-0=@uwoo o-1=@uwoo]
    ^-  [[sure sure] _gen] 
    =^  [ned-0=need ned-1=need]  gen  (fork-need ned.sur o o-0 o-1)
    [[[ned-0 lok.sur] [ned-1 lok.sur]] gen]
  ::
  ++  fork-need
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
    |=  [a=@uwoo o1=@uwoo o2=@uwoo]
    ^+  gen
    =/  blob-from=blob  (~(got by blocks.gen) a)
    ?>  ?=(%hop -.fin.blob-from)
    ?>  =(~ par.blob-from)
    :: ?>  =(~ args.t.fin.blob-from)
    =/  a-to-b=jmp  t.fin.blob-from
    =.  gen  (emir o2 ~ body.blob-from fin.blob-from)
    gen(blocks (~(put by blocks.gen) a blob-from(body ~, t.fin [~ o1])))
  ::  Here the idea is that we materialize the conditional as a register with
  ::  a loobean, then the lazy needs get forked, and the BB of that need gets
  ::  code that branches on the conditional register and fulfills the original
  ::  need with either of the two
  ::
  ++  fork
    |=  [nex=next r-cond=@uvre]
    ^-  [[next next] _gen]
    =^  o-0  gen  oo
    =^  o-1  gen  oo
    =;  [[laz-0=need-lazy laz-1=need-lazy] gen1=_gen]
      =.  gen  gen1
      :_  gen
      [[%next laz-0 ~ o-0] [%next laz-1 ~ o-1]]
    ::
    =/  laz=need-lazy  laz.nex
    =/  o=@uwoo  there.then.nex
    ?>  =(~ args.then.nex)
    |-  ^-  [[need-lazy need-lazy] _gen]
    =*  fork-loop  $
    =^  [sure-0=sure sure-1=sure]  gen  (fork-sure sure.laz o o-0 o-1)
    =*  fork  ,(list [[@uwoo need-lazy] [@uwoo need-lazy]])
    =^  [fork-0=fork fork-1=fork]  gen
      %^  spin-split  fork.laz  gen
      |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen-acc=_gen]
      =*  i  ,[[@uwoo need-lazy] [@uwoo need-lazy]]
      ^-  [[i i] _gen]
      =.  gen  gen-acc
      ::  -y/n here means y or n child. 0 or 1 means either yes or no branch
      ::  of this split. Confusing!
      ::  insert1/2 are used for splicing the code in: o -> x becomes
      ::  o -> insert1 -> ... -> insert2 -> x. 
      ::
      =^  o-0-kid-y    gen  oo
      =^  o-1-kid-y    gen  oo
      =^  o-0-kid-n    gen  oo
      =^  o-1-kid-n    gen  oo
      =^  o-insert2-y  gen  oo
      =^  o-insert2-n  gen  oo
      =/  tag-y  (~(got by tags.gen) o.y)
      =/  tag-n  (~(got by tags.gen) o.n)
      =.  tags.gen
        %-  ~(gas by tags.gen)
        :~  [o-0-kid-y tag-y]  [o-1-kid-y tag-y]
            [o-0-kid-n tag-n]  [o-1-kid-n tag-n]
        ==
      ::
      =^  [laz-y-0=need-lazy laz-y-1=need-lazy]  gen
        %=  fork-loop
          laz  laz.y
          o    o-insert2-y
          o-0  o-0-kid-y
          o-1  o-1-kid-y
        ==
      ::
      =^  [laz-n-0=need-lazy laz-n-1=need-lazy]  gen
        %=  fork-loop
          laz  laz.n
          o    o-insert2-n
          o-0  o-0-kid-n
          o-1  o-1-kid-n
        ==
      ::
      =^  p-y  gen  (proxy r-cond o.y)
      =^  p-n  gen  (proxy r-cond o.n)
      =^  o-insert1-y=@uwoo  gen
        (emit ~ ~ [%brn p-y ~^o-0-kid-y ~^o-1-kid-y])
      ::
      =^  o-insert1-n=@uwoo  gen
        (emit ~ ~ [%brn p-n ~^o-0-kid-n ~^o-1-kid-n])
      ::
      =.  gen  (insert-hop o.y o-insert1-y o-insert2-y)
      =.  gen  (insert-hop o.n o-insert1-n o-insert2-n)
      :_  gen
      :-  [[o-0-kid-y laz-y-0] [o-0-kid-n laz-n-0]]
      [[o-1-kid-y laz-y-1] [o-1-kid-n laz-n-1]]
    ::
    =*  bond  ,(list [o=@uwoo laz=need-lazy])
    =^  [bond-0=bond bond-1=bond]  gen
      %^  spin-split  bond.laz  gen
      |=  [[o-bond=@uwoo laz-bond=need-lazy] gen-acc=_gen]
      ^-  [[[@uwoo need-lazy] [@uwoo need-lazy]] _gen]
      =.  gen  gen-acc
      =^  o-0-kid    gen  oo
      =^  o-1-kid    gen  oo
      =^  o-insert2  gen  oo
      =/  tag  (~(got by tags.gen) o-bond)
      =.  tags.gen  (~(gas by tags.gen) ~[[o-0-kid tag] [o-1-kid tag]])
      =^  [laz-0=need-lazy laz-1=need-lazy]  gen
        %=  fork-loop
          laz  laz-bond
          o    o-insert2
          o-0  o-0-kid
          o-1  o-1-kid
        ==
      ::
      =^  p  gen  (proxy r-cond o-bond)
      =^  o-insert1=@uwoo  gen  (emit ~ ~ [%brn p ~^o-0-kid ~^o-1-kid])
      =.  gen  (insert-hop o-bond o-insert1 o-insert2)
      [[[o-0-kid laz-0] [o-1-kid laz-1]] gen]
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
    =^  if-0  gen  (emit ~ [%imm `*`0 r-0]~ %hop ~[`r-0] barg)
    =^  if-1  gen  (emit ~ [%imm `*`1 r-1]~ %hop ~[`r-1] barg)
    [[if-0 if-1] gen]
  ::
  ++  emit
    |=  =blob
    ^-  [@uwoo _gen]
    =^  o  gen  oo
    [o (emir o blob)]
  ::
  ++  from-sure
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
    |=  [axe=@ laz=need-lazy]
    ^-  need-lazy
    =*  from-buc  $
    :+  (from-sure axe sure.laz)
      %+  turn  fork.laz
      |=  [y=[@uwoo laz=need-lazy] n=[@uwoo laz=need-lazy]]
      [y(laz from-buc(laz laz.y)) n(laz from-buc(laz laz.n))]
    %+  turn  bond.laz
    |=  [o=@uwoo laz=need-lazy]
    [o from-buc(laz laz)]
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
    =^  [ned=need ops=(list pole)]  gen
      (copy-need-make-ops ned.sure.first ned.sure.second)
    ::
    :_  (add-ops o ops)
    :+  [ned (~(uni in lok.sure.first) lok.sure.second)]
      (weld fork.first fork.second)
    (weld bond.first bond.second)
  ::  +split-* and +into-* for autoconses and Nock 10 follow the same pattern:
  ::  they split a lazy need into two, emitting consing code into the BBs of the
  ::  children lazy needs. The split needs share the BB label, which should be
  ::  fine since they produce disjoint parts of a noun
  ::
  ++  into-sure
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
      =^  l  gen  (must h.ned)
      =^  r  gen  (must t.ned)
      =/  =pole  [%con p.l p.r r.ned]
      =+  [new old]=?:(h [q.l q.r] [q.r q.l])
      $(tack [[h old] tack], ned new, ops [pole ops], axe lat)
    ==
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
    =^  [sure-don=sure sure-rec=sure]  gen  (into-sure axe sure.laz o)
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
    :-  [sure-don fork-don bond-don]
    [sure-rec fork-rec bond-rec]
  ::
  ++  split-sure
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
      ^      =^(r gen re [[r %both r ned] gen])
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
    =^  [sure-h=sure sure-t=sure]  gen  (split-sure sure.laz o)
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
    :-  [sure-h fork-h bond-h]
    [sure-t fork-t bond-t]
  ::
  ++  add-ops
    |=  [o=@uwoo ops=(list pole)]
    ^+  gen
    =/  =blob  (~(got by blocks.gen) o)
    =.  body.blob  (weld ops body.blob)
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  emir
    |=  [o=@uwoo =blob]
    ^+  gen
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  bomb
    |=  miss=(unit @uwoo)
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %bom miss)
    [[%next *need-lazy ~ o] gen]
  ::
  ++  copy-need-make-ops
    |=  [first=need second=need]
    ^-  [[need (list pole)] _gen]
    =|  ops=(list pole)
    =|  sout=(list need)
    =/  sin=(list (each (unit [r=@uvre]) [l=need r=need]))
      [|+[first second]]~
    ::
    |-  ^-  [[need (list pole)] _gen]
    ?~  sin
      ?>  ?=([* ~] sout)
      [[i.sout ops] gen]
    ?:  ?=(%& -.i.sin)
      ?>  ?=([* * *] sout)
      ::  should not need normalization as the shapes are preserved
      ::
      =/  par  [i.t.sout i.sout]
      %=  $
        sin   t.sin
        sout  :_  t.t.sout
                ?~  p.i.sin
                  %-  cons-need  ::  XX
                  par
                =*  both  u.p.i.sin
                [%both r.both par]
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
        ?@(-.r [r gen] =^(x gen re [[%both x r] gen]))
      ~?  =(r.l r.rr)  [%copy-this-l-b r.l r.rr]
      $(ops [[%mov r.rr r.l] ops], sout [rr sout], sin t.sin)
    ?:  ?=(%this -.r)
      =^  ll=$>(%both need)  gen
        ?@(-.l [l gen] =^(x gen re [[%both x l] gen]))
      ~?  =(r.ll r.r)  [%copy-this-r r.ll r.r]
      $(ops [[%mov r.ll r.r] ops], sout [ll sout], sin t.sin)
    ?:  ?=(%both -.l)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x r] gen]))
      ~?  =(r.l r.rr)  [%copy-both r.l r.rr]
      %=  $
        ops  [[%mov r.rr r.l] ops]
        sin  [|+[h.l h.rr] |+[t.l t.rr] &+`[r.rr] t.sin]
      ==
    ?^  -.r
      $(sin [|+[p.l p.r] |+[q.l q.r] &+~ t.sin])
    ::  first computation does not have a cell check for r.r,
    ::  so r.r will need to be checked upstream
    ::
    $(sin [|+[p.l h.r] |+[q.l t.r] &+`[r.r] t.sin])
  ::
  ++  coerce-ord
    |=  [need-pessimized=need-ordered nex=next-resolved]
    ^-  [next-resolved _gen]
    =;  [ned=need gen1=_gen]  [[%next [[ned ~] ~ ~] [~ then.nex]] gen1]
    |-  ^-  [need _gen]
    ?-    -.need-pessimized
        %none
      ?>  ?=(%none -.ned.nex)
      [[%none ~] gen]
    ::
        %this
      ?:  ?=(%this -.ned.nex)  [ned.nex gen]
      =^  r  gen  (kern-r-need then.nex ned.nex)
      [[%this r] gen]
    ::
        ^
      ?:  ?=(%none -.ned.nex)
        =^  hed  gen  $(need-pessimized -.need-pessimized)
        =^  tel  gen  $(need-pessimized +.need-pessimized)
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[hed tel] gen]
      ?@  -.ned.nex  !!
      =^  hed  gen  $(need-pessimized -.need-pessimized, ned.nex -.ned.nex)
      =^  tel  gen  $(need-pessimized +.need-pessimized, ned.nex +.ned.nex)
      ?<  &(?=(%none -.hed) ?=(%none -.tel))
      [[hed tel] gen]
    ::
        %both
      ?-    -.ned.nex
          %none
        =^  r  gen  re
        =^  hed  gen  $(need-pessimized h.need-pessimized)
        =^  tel  gen  $(need-pessimized t.need-pessimized)
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[%both r hed tel] gen]
      ::
          %this
        =^  hed  gen  $(need-pessimized h.need-pessimized, ned.nex [%none ~])
        =^  tel  gen  $(need-pessimized t.need-pessimized, ned.nex [%none ~])
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[%both r.ned.nex hed tel] gen]
      ::
          ^
        =^  r  gen  re
        =^  hed  gen  $(need-pessimized h.need-pessimized, ned.nex -.ned.nex)
        =^  tel  gen  $(need-pessimized t.need-pessimized, ned.nex +.ned.nex)
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[%both r hed tel] gen]
      ::
          %both
        =^  hed  gen  $(need-pessimized h.need-pessimized, ned.nex h.ned.nex)
        =^  tel  gen  $(need-pessimized t.need-pessimized, ned.nex t.ned.nex)
        ?<  &(?=(%none -.hed) ?=(%none -.tel))
        [[%both r.ned.nex hed tel] gen]
      ==
    ==
  ++  need-ord-alloc-regs
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
    ==
  ::  With the top level need finally known, emit noun splitting code into
  ::  appropriate BBs
  ::
  ++  coerce-lazy
    |=  [ned=need o=@uwoo laz=need-lazy]
    ^+  gen
    =*  coerce-lazy  .
    =.  gen
      =/  ned-target=need  ned.sure.laz
      |-  ^+  gen
      =*  sure-loop  $
      ?-    -.ned
          %none
        ?>  ?=(%none -.ned-target)
        gen
      ::
          %this
        =^  ops  gen  (kern-need r.ned ned-target)
        (add-ops o ops)
      ::
          ^
        ?:  ?=(%none -.ned-target)  gen
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
    =.  gen
      %+  roll  bond.laz
      |=  [[o=@uwoo laz=need-lazy] gen-acc=_gen]
      =.  gen  gen-acc
      (coerce-lazy ned o laz)
    ::
    %+  roll  fork.laz
    |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] gen-acc=_gen]
    =.  gen  gen-acc
    =.  gen  (coerce-lazy ned y)
    (coerce-lazy ned n)
  ::
  ::  NB: bonds do not matter when it comes to figuring out the shape of the
  ::  need but they do matter when it comes to emitting the disassembly code
  ::  from a branch combination to a specific branch - into which block to emit
  ::  the disassembly code
  ::
  ++  next-lazy-collapse
    |=  [nex=next less=cape]
    ^-  [next-resolved _gen]
    ?>  =(~ args.then.nex)
    =^  ned-final=need  gen  (need-ord-alloc-regs (shape-collapse laz.nex less))
    :-  [%next [[ned-final ~] ~ ~] ~ there.then.nex]
    (coerce-lazy ned-final there.then.nex laz.nex)
  ::
  ::  Renumber the registers so that the input registers are 0-N, set the
  ::  starting block index to 0w0
  ::
  ++  to-straight
    |=  nex=next-resolved
    ^-  straight
    =/  blocks=(map @uwoo blob)  blocks:rewrite-cond
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
        [[%both h t] gen]
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
          %lob
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
          %bom
        [fin gen]
      ==
    ::
    ++  rewrite-jump
      |=  j=jmp
      ^-  [jmp _gen]
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
    |=  sur=sure
    ^-  [need _gen]
    %-  ~(rep in lok.sur)
    |=  [axe=@ ned=_ned.sur gen-init=_gen]
    =.  gen  gen-init
    ?:  =(1 axe)  [ned gen]
    ?<  =(0 axe)
    |-  ^-  [need _gen]
    ?:  =(1 axe)
      ?.  ?=(%none -.ned)  [ned gen]
      =^  r  gen  re
      [[%this r] gen]
    =/  [here=(unit @uvre) h=need t=need]
      ?-  -.ned
        %none  [~ [. .]:[%none ~]]
        %this  [`r.ned [. .]:[%none ~]]
        ^      [~ ned]
        %both  [`r.ned [h t]:ned]
      ==
    ::
    =^  [h-required=need t-required=need]  gen
      ?-    (cap axe)
          %2
        =^  x  gen  $(ned h, axe (mas axe))
        [[x t] gen]
      ::
          %3
        =^  x  gen  $(ned t, axe (mas axe))
        [[h x] gen]
      ==
    ::
    =/  x  (cons-need h-required t-required)
    ?~  here  [x gen]
    ?@  -.x  [[%this u.here] gen]
    [[%both u.here x] gen]
  ::
  ++  rewrite-cond
    ^+  gen
    =/  ren  |=(r=@uvre ?~(e=(~(get by cond.gen) r) r def.u.e))
    gen(blocks (~(run by blocks.gen) (map-regs ren)))
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
  ==
::
++  msg-need-ord
  |=  [a=need-ordered b=need-ordered less=cape]
  ^-  need-ordered
  =*  msg  .
  ?:  =(a b)  a
  ::  none are cells
  ::
  ?:  ?&  |(?=(%this -.a) ?=(%none -.a))
          |(?=(%this -.b) ?=(%none -.b))
      ==
    this+~
  ::  one is maybe atom, can't refine with `less`
  ::
  ?:  ?&  ?=(@ less)
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
    =/  l  (msg none+~ h-double -.less)
    =/  r  (msg none+~ t-double +.less)
    ?:  |(?=(%this -.single) ?=(%both -.double))  [%both l r]
    %-  cons-need  ::  XX 
    [l r]
  ::
  ?:  ?=(%both -.a)
    ?:  ?=(%both -.b)
      [%both (msg h.a h.b (hed:ca less)) (msg t.a t.b (tel:ca less))]
    [%both (msg h.a p.b (hed:ca less)) (msg t.a q.b (tel:ca less))]
  ?:  ?=(%both -.b)
    [%both (msg p.a h.b (hed:ca less)) (msg q.a t.b (tel:ca less))]
  %-  cons-need  ::  XX
  [(msg p.a p.b (hed:ca less)) (msg q.a q.b (tel:ca less))]
::
++  need-to-ordered
  |=  ned=need
  ^-  need-ordered
  ~+
  =*  this  .
  ?-  -.ned
    %none  [%none ~]
    %this  [%this ~]
    ^      [(this -.ned) (this +.ned)]
    %both  [%both (this h.ned) (this t.ned)]
  ==
::
++  cons-need
  |*  [a=?([%none ~] ^) b=?([%none ~] ^)]
  ?:  &(?=(%none -.a) ?=(%none -.b))  [%none ~]
  [a b]
::
++  uni-need-ord
  |=  [a=need-ordered b=need-ordered]
  ^-  need-ordered
  ?:  =(a b)  a
  ?:  ?=(%none -.a)  b
  ?:  ?=(%none -.b)  a
  ?:  ?=(%this -.a)
    ?:  ?=(%both -.b)  b
    ?>  ?=(^ -.b)
    [%both b]
  ?:  ?=(%this -.b)
    ?:  ?=(%both -.a)  a
    ?>  ?=(^ -.a)
    [%both a]
  ?:  &(?=(^ -.a) ?=(^ -.b))
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
  =/  x=need-ordered  (cons-need $(a h-a, b h-b) $(a t-a, b t-b))
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
+$  sure-inter1  [ned=need-ordered lok=(set @)]
+$  need-inter1
  $+  need-inter1
  $;  |-
  $:  sure=sure-inter1
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
  |=  laz=need-lazy
  ^-  need-inter1
  =*  lazy-to-inter  .
  %+  roll  bond.laz
  =/  ned-sure-new  (need-to-ordered ned.sure.laz)
  =/  fork-new=(list [need-inter1 need-inter1])
    %+  turn  fork.laz
    |=  [[* laz-y=need-lazy] * laz-n=need-lazy]
    [(lazy-to-inter laz-y) (lazy-to-inter laz-n)]
  ::
  =/  sure-new=sure-inter1  [ned-sure-new lok.sure.laz]
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
++  inter1-to-inter2
  |=  [intr=need-inter1 less=cape]
  ^-  need-inter2
  =*  this-buc  $
  :-  %-  ~(rep in lok.sure.intr)
      |=  [axe=@ new=_ned.sure.intr]
      ?:  =(1 axe)  new
      ?:  (axe-in-less-cape axe less)  new
      |-  ^-  need-ordered
      ?:  =(1 axe)
        ?.  ?=(%none -.new)  new
        [%this ~]
      =/  [h=need-ordered t=need-ordered]
        ?-  -.new
          ?(%none %this)  [. .]:[%none ~]
          ^               new
          %both           [h t]:new
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
  %+  turn  fork.intr
  |=  [y=need-inter1 n=need-inter1]
  [this-buc(intr y) this-buc(intr n)]
::
++  shape-collapse
  |=  [laz=need-lazy less=cape]
  ^-  need-ordered
  (inter2-collapse (inter1-to-inter2 (lazy-to-inter1 laz) less) less)
::
++  inter2-collapse
  |=  [intr=need-inter2 less=cape]
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
++  hed-need-ord
  |=  a=need-ordered
  ^-  need-ordered
  ?-  -.a
    %none  [%none ~]
    %this  [%none ~]
    %both  h.a
    ^      -.a
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
  ==
::
::  MSG of `a` and `b` while knowing that axes in `fix` exist
::
++  msg-need-ord-fix-aware
  |=  [a=need-ordered b=need-ordered fix=need-ordered less=cape]
  ^-  need-ordered
  ~+
  =*  msg  .
  ?:  =(a b)  a
  ?:  |(?=(%this -.fix) ?=(%none -.fix))
    (msg-need-ord a b less)
  ?:  &(?=(%none -.a) =(b fix))  b
  ?:  &(?=(%none -.b) =(a fix))  a
  =/  need-here=?  |(?=(%this -.a) ?=(%this -.b) ?=(%both -.a) ?=(%both -.b))
  =/  x
    %+  cons-need
      (msg (hed-need-ord a) (hed-need-ord b) (hed-need-ord fix) (hed:ca less))
    (msg (tel-need-ord a) (tel-need-ord b) (tel-need-ord fix) (tel:ca less))
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
++  none-equivalent
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
  |=  $:  n-args=@ud
          blocks=(map @uwoo blob)
          rev=(jar @uwoo @uwoo)
          topo=(list @uwoo)
      ==
  ^+  blocks
  =|  $=  gen
      $:  new=(map @uwoo blob)
          re-gen=@uvre
          old=(map @uvre @uvre)  ::  old -> new
          info=(map @uwoo (map @uvre info-reg))
          imms=(map @uwoo (jug * @uvre))
          info-local=(map @uvre info-reg)
          imms-local=(jug * @uvre)
          rev=(jug @uwoo @uwoo)
      ==
  ::
  =.  rev.gen  (~(run by rev) (bake silt (list @uwoo)))
  |^  ^+  blocks
  ?~  topo  new.gen
  =*  o  i.topo
  =/  pre=(list @uwoo)  ~(tap in (~(get ju rev.gen) o))
  ?:  &(=(~ pre) !=(0w0 o))
    ::  this block became unreachable: delete its descendants from reversed CFG
    ::
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
      |-  ^+  [info gen]
      ?:  =(n-args 0)  [info gen]
      =^  r  gen  re
      =.  info  (~(put by info) r *info-reg)
      =.  old.gen  (~(put by old.gen) r r)
      $(n-args (dec n-args))
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
    ((int-ju acc) (~(got by imms.gen) o1))
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
    ?<  (~(has by old.gen) i.par.bob)
    =^  new  gen  re
    =.  old.gen  (~(put by old.gen) i.par.bob new)
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
      =^  new=@uvre  gen
        ?<  (~(has by old.gen) d.op)
        =^  new  gen  re
        =|  info=info-reg
        =.  info-local.gen  (~(put by info-local.gen) new info(has-imm `n.op))
        =.  old.gen   (~(put by old.gen) d.op new)
        =.  imms-local.gen  (~(put ju imms-local.gen) n.op new)
        [new gen]
      ::
      [[[%imm n.op new] body-new] gen]
    ::
        %mov
      =.  old.gen  (~(put by old.gen) d.op (~(got by old.gen) s.op))
      [body-new gen]
    ::
        %inc
      =/  arg  (~(got by old.gen) s.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?^  dec-of.arg-info
        =.  old.gen  (~(put by old.gen) d.op u.dec-of.arg-info)
        [body-new gen]
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(dec-of `new)))
      ::
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%inc arg new] body-new] gen]
    ::
        %con
      =/  h  (~(got by old.gen) h.op)
      =/  t  (~(got by old.gen) t.op)
      =/  h-info  (~(got by info-local.gen) h)
      =/  t-info  (~(got by info-local.gen) t)
      ?^  intersect=(~(int in hed-of.h-info) tel-of.t-info)
        =.  old.gen  (~(put by old.gen) d.op n.intersect)
        [body-new gen]
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
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
      =.  old.gen  (~(put by old.gen) d.op new)
      [[[%con h t new] body-new] gen]
    ::
        %hed
      =/  arg  (~(got by old.gen) s.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?^  has-hed.arg-info
        =.  old.gen  (~(put by old.gen) d.op u.has-hed.arg-info)
        [body-new gen]
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =|  info=info-reg
      =.  info-local.gen  (~(put by info-local.gen) new info(hed-of [arg ~ ~]))
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(has-hed `new)))
      ::
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%hed arg new] body-new] gen]
    ::
        %tal
      =/  arg  (~(got by old.gen) s.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?^  has-tel.arg-info
        =.  old.gen  (~(put by old.gen) d.op u.has-tel.arg-info)
        [body-new gen]
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =|  info=info-reg
      =.  info-local.gen  (~(put by info-local.gen) new info(tel-of [arg ~ ~]))
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(has-tel `new)))
      ::
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%tal arg new] body-new] gen]
    ::
        %cel
      =/  arg  (~(got by old.gen) p.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?:  is-cell.arg-info
        [body-new gen]
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(is-cell &)))
      ::
      [[[%cel arg] body-new] gen]
    ::
        %lob
      =/  arg  (~(got by old.gen) p.op)
      =/  arg-info  (~(got by info-local.gen) arg)
      ?:  |(is-loob.arg-info ?=([~ ?] has-imm.arg-info))
        [body-new gen]
      =.  info-local.gen
        (~(jab by info-local.gen) arg |=(info-reg +<(is-loob &)))
      ::
      [[[%lob arg] body-new] gen]
    ::
        %hsp
      [[op body-new] gen]
    ::
        %hse
      [[op body-new] gen]
    ::
        %hdp
      =/  arg  (~(got by old.gen) p.op)
      [[[%hdp n.op arg f.op] body-new] gen]
    ::
        %hde
      =/  arg  (~(got by old.gen) p.op)
      [[[%hde n.op arg f.op] body-new] gen]
    ::
        %spy
      =/  e  (~(got by old.gen) e.op)
      =/  p  (~(got by old.gen) p.op)
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%spy e p new] body-new] gen]
    ::
        %nok
      =/  u  (~(got by old.gen) u.op)
      =/  f  (~(got by old.gen) f.op)
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%nok u f new] body-new] gen]
    ::
        %cal
      =/  v  (turn v.op ~(got by old.gen))
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%cal a.op v new] body-new] gen]
    ::
        %caf
      =/  v  (turn v.op ~(got by old.gen))
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%caf a.op v new n.op] body-new] gen]
    ::
        %cam
      =/  v  (turn v.op ~(got by old.gen))
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%cam a.op v new k.op] body-new] gen]
    ::
        %csl
      =/  s  (~(got by old.gen) s.op)
      ~|  d.op
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%csl a.op s new] body-new] gen]
    ::
        %csf
      =/  s  (~(got by old.gen) s.op)
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%csf a.op s new n.op] body-new] gen]
    ::
        %csm
      =/  s  (~(got by old.gen) s.op)
      ?<  (~(has by old.gen) d.op)
      =^  new  gen  re
      =.  info-local.gen  (~(put by info-local.gen) new *info-reg)
      =.  old.gen   (~(put by old.gen) d.op new)
      [[[%csm a.op s new k.op] body-new] gen]
    ==
  ::
  =^  fin-new=termin  gen
    ?-    -.fin.bob
        %clq
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (~(got by old.gen) s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      ?:  |(is-cell.info-cond ?=([~ ^] has-imm.info-cond))
        :-  [%hop ~ there.z.fin.bob]
        ::  if the branching instruction points to a block twice then we can't
        ::  delete the edge from the reversed graph since it still points to it
        ::  after the branch elimination
        ::
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.o.fin.bob o))
      ?:  |(is-loob.info-cond ?=([~ @] has-imm.info-cond))
        :-  [%hop ~ there.o.fin.bob]
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.z.fin.bob o))
      [fin.bob(s cond-new) gen]
    ::
        %eqq
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  l-new  (~(got by old.gen) l.fin.bob)
      =/  r-new  (~(got by old.gen) r.fin.bob)
      ?.  =(l-new r-new)  [fin.bob(l l-new, r r-new) gen]
      :-  [%hop ~ there.z.fin.bob]
      ?:  =(there.o.fin.bob there.z.fin.bob)  gen
      gen(rev (~(del ju rev.gen) there.o.fin.bob o))
    ::
        %brn
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (~(got by old.gen) s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      ?~  has-imm.info-cond  [fin.bob(s cond-new) gen]
      ?-    u.has-imm.info-cond
          %&
        :-  [%hop ~ there.z.fin.bob]
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.o.fin.bob o))
      ::
          %|
        :-  [%hop ~ there.o.fin.bob]
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
        %hop
      [fin.bob(args.t (turn args.t.fin.bob (lift ~(got by old.gen)))) gen]
    ::
        %jmp
      [fin.bob(v (turn v.fin.bob ~(got by old.gen))) gen]
    ::
        %jmf
      [fin.bob(v (turn v.fin.bob ~(got by old.gen))) gen]
    ::
        %jsp
      [fin.bob(s (~(got by old.gen) s.fin.bob)) gen]
    ::
        %jsf
      [fin.bob(s (~(got by old.gen) s.fin.bob)) gen]
    ::
        %don
      [fin.bob(s (~(got by old.gen) s.fin.bob)) gen]
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
  ++  re  `[@uvre _gen]`[re-gen.gen gen(re-gen +(re-gen.gen))]
  ++  join-info
    |=  [a=(map @uvre info-reg) b=(map @uvre info-reg)]
    ^-  (map @uvre info-reg)
    %-  ~(rep by a)
    |=  [[k=@uvre v-a=info-reg] acc=(map @uvre info-reg)]
    ?~  v-b=(~(get by b) k)  acc
    (~(put by acc) k (join-reg v-a u.v-b))
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
  |=  $:  blocks=(map @uwoo blob)
          rev=(jar @uwoo @uwoo)
          topo=(list @uwoo)
      ==
  ^-  (map @uwoo blob)
  =*  gen  ,[new=(map @uwoo blob) saw=(set @uwoo)]
  =<  new
  ^-  gen
  %+  roll  topo
  |=  [o=@uwoo =gen]
  ^+  gen
  ?:  (~(has in saw.gen) o)  gen
  =/  o-new=@uwoo  o
  =/  b-new=blob  (~(got by blocks) o)
  |-  ^+  gen
  ?.  ?=(%hop -.fin.b-new)
    gen(new (~(put by new.gen) o-new b-new))
  =/  o1=@uwoo  there.t.fin.b-new
  =/  pre-o1=(list @uwoo)  (~(get ja rev) o1)
  ?<  =(~ pre-o1)
  ?.  =(pre-o1 ~[o])
    gen(new (~(put by new.gen) o-new b-new))
  =.  saw.gen  (~(put in saw.gen) o1)
  =/  b1  (~(got by blocks) o1)
  =/  body-merge=(list pole)
    %+  weld  body.b-new
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
      ops     ?~(i.args-a ops [[%mov u.i.args-a i.args-b] ops])
    ==
  ::
  $(o o1, body.b-new body-merge, fin.b-new fin.b1)
::  If a non-crashing op assigns to a register which is never used, we can
::  omit the op.
::  XX non-crashing direct calls
::
++  remove-dead-code
  |=  [blocks=(map @uwoo blob) rev-topo=(list @uwoo)]
  ^-  (map @uwoo blob)
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
  |=  blocks=(map @uwoo blob)
  ^+  blocks
  =*  key  ,[hint=?(%spot %mean) reg=@uvre]
  =/  topo  (bb-topo blocks)
  =/  rev   (rev-cfg blocks (sy topo))
  ::  Walk in topological order carrying the hints that are open: prologue
  ::  passed, epilogue not reached yet. A hint open at an op that could crash,
  ::  or at a terminator that could crash or leave the function, is unsafe to
  ::  drop since the stack trace would change.
  ::
  =/  [seen=(set key) unsafe=(set key)]
    =|  [seen=(set key) unsafe=(set key) out=(map @uwoo (set key))]
    |-  ^-  [(set key) (set key)]
    ?~  topo  [seen unsafe]
    =/  b  (~(got by blocks) i.topo)
    =/  open=(set key)
      %+  roll  (~(get ja rev) i.topo)
      |=  [p=@uwoo acc=(set key)]
      (~(uni in acc) (~(get ju out) p))
    ::
    =/  body  body.b
    |-  ^-  [(set key) (set key)]
    ?^  body
      =/  op  i.body
      ?:  &(?=(%hdp -.op) ?=(?(%spot %mean) n.op))
        %=  $
          body  t.body
          open  (~(put in open) [n.op p.op])
          seen  (~(put in seen) [n.op p.op])
        ==
      ?:  &(?=(%hde -.op) ?=(?(%spot %mean) n.op))
        $(body t.body, open (~(del in open) [n.op p.op]))
      ?.  ?=(?(%inc %cel %lob %spy %nok %cal %caf %cam %csl %csf %csm) -.op)
        $(body t.body)
      $(body t.body, unsafe (~(uni in unsafe) open))
    =?  unsafe  !?=(?(%clq %eqq %hop) -.fin.b)  (~(uni in unsafe) open)
    ^$(topo t.topo, out (~(put by out) i.topo open))
  ::
  =/  safe  (~(dif in seen) unsafe)
  %-  ~(run by blocks)
  |=  b=blob
  %_    b
      body
    %+  skip  body.b
    |=  op=pole
    ?&  ?=(?(%hdp %hde) -.op)
        ?=(?(%spot %mean) n.op)
        (~(has in safe) [n p]:op)
    ==
  ==
::
++  remove-useless-branching
  |=  blocks=(map @uwoo blob)
  ^+  blocks
  %-  ~(run by blocks)
  |=  b=blob
  ^+  b
  =;  [epilogue=(list pole) new-fin=termin]
    b(body (weld body.b epilogue), fin new-fin)
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
  |=  blocks=(map @uwoo blob)
  |^  ^+  blocks
  %-  ~(run by blocks)
  |=  b=blob
  ^+  b
  =;  new-fin=termin  b(fin new-fin)
  ?+    -.fin.b  fin.b
      %clq  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
      %eqq  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
      %brn  fin.b(z (rewrite-jump z.fin.b), o (rewrite-jump o.fin.b))
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
  ::  the bypassed block are substituted by what the hop passes to them.
  ::
  ++  rewrite-hop
    |=  j=jmp
    ^-  jmp
    =/  nex  (~(got by blocks) there.j)
    ?.  =(~ body.nex)        j
    ?.  ?=(%hop -.fin.nex)   j
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
++  optimize
  |=  s=straight
  ^-  straight
  ?:  |  s
  =;  s1=straight
    ?:  =(s s1)  s1
    $(s s1)
  =/  topo  (bb-topo blocks.s)
  =/  rev  (rev-cfg blocks.s (sy topo))
  =.  blocks.s  (remove-hops blocks.s rev topo)
  ::
  =.  topo  (bb-topo blocks.s)
  =.  rev  (rev-cfg blocks.s (sy topo))
  =.  blocks.s  (alias n-args.s blocks.s rev topo)
  ::
  =.  topo  (bb-topo blocks.s)
  =.  blocks.s  (remove-dead-code blocks.s (flop topo))
  ::
  =.  blocks.s  (trim-trace-hints blocks.s)
  =.  blocks.s  (remove-useless-branching blocks.s)
  =.  blocks.s  (remove-empty-middle blocks.s)
  s
--
