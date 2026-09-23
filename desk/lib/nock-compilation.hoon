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
::    Call graph construction:  line 524
::    Compilation:              line 2299
::    IR optimization passes:   line 5493
::    Interactive core:         line 6479
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
=/  ska-verb  ~
::
::  check-bell-prod: check that all functions with the same bell agree on the
::  product with the parts captured from the subject masked out. Expensive:
::  walks the provenance of every product.
::
:: =/  check-bell-prod  ~
::
::  compiler verbosity
::
 =/  comp-verb  ~
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
  ~%  %ca  ..ride  ~
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
::    components, which are found on the fly with Tarjan's algorithm.  This
::    also gives finalization for free: a function popped off Tarjan's stack
::    never changes, so it can be memoized right away, without a transitive
::    closure of the graph.
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
::  Analysis state, see +ska-callgraph
::
+$  ska-state
  $:  g=callgraph             ::  functions found so far, in progress or done
      done=memo               ::  memoization of finished functions
      order=(map identity @)  ::  DFS numbers of the functions in progress
      stk=(list identity)     ::  functions in progress, latest first
      next=@                  ::  next DFS number
      runs=@                  ::  number of function analyses (statistics)
  ==
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
  ~%  %he-sock  ..ride  ~
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
::  Check if a call to "id-kid" is a recursive call to one of the functions
::  in progress, i.e. its transitive callers (the analysis stack, latest
::  caller first): a function with the same formula whose code requirement is
::  satisfied by id-kid's subject. Also check if id-kid's subject
::  homeomorphically embeds the subject of one of them, masking out the accu-
::  mulating part with +msg-sock. This is done to stop infinite chains of
::  dynamically generated functions. Produces the identity to call instead:
::  %merge, a function in progress (its product is erased by the caller, as
::  id-kid only satisfies its code requirement), or %gen, a generalized
::  identity.
::
::  Chains before HE firing are theoretically finite but could be V A S T (see
::  TREE(3) to get the sense of scale); however in testing I could not construct
::  an example where a chain of functions would grow faster than linearly with
::  the size of the formula and the subject: the products would get masked down
::  with either the simple recursion pessimization (we erase the product of
::  recursive calls), or with +double-int as we intersect nouns on both
::  their values and provenances.
::
++  recursive-call
  ~%  %recursive-call  ..ride  ~
  |=  [id-kid=identity stk=(list identity) g=callgraph]
  ^-  (unit [?(%merge %gen) identity])
  ?~  stk  ~
  ?.  =(fol.id-kid fol.i.stk)  $(stk t.stk)
  =/  d=datum  (git-g g i.stk)
  ?:  (huge:so less-code.d more.id-kid)  `[%merge i.stk]
  ?:  (he-sock more.id-kid more.i.stk)
    `[%gen [(msg-sock more.id-kid more.i.stk) fol.id-kid]]
  $(stk t.stk)
::  A noun with provenance "src" captured something unknown from subject
::  "less". Walks the capes rather than the provenance, which can be huge (a
::  product that is a big partially known noun assembled from the subject):
::  +distribute is memoized on the subtrees that provenances share, and the
::  cape of the subject is small. (A provenance axis that goes beyond an atom
::  of the subject counts as known here: the product there is unknown but the
::  subject is not, so a memoized product does not lose information.)
::
++  unknown-sock-captured
  ~%  %unknown-sock-captured  ..ride  ~
  |=  [src=spring less=sock]
  ^-  ?
  =/  got=cape  (distribute & src)
  =/  cap=cape  cape.less
  |-  ^-  ?
  ?:  ?=(%| got)  |
  ?:  ?=(%& got)  !(all:ca cap)
  ?@  cap  !cap
  |($(got -.got, cap -.cap) $(got +.got, cap +.cap))
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
    ~%  %git-mi  ..ride  ~
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
    ~%  %put-mi  ..ride  ~
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
    |-  ^-  long-ska
    =*  hed-loop  $
    ?~  heds
      cold-loop(q t.q)
    ?.  =(fol.i.heds -.fol.i.q)
      =>  !@  ska-verb  .
          ~&  >>  %join-head-wrong-fol  .
      hed-loop(heds t.heds)
    ?.  (huge:so less.i.heds sub.i.q)
      =>  !@  ska-verb  .
          ~&  >>  %join-head-wrong-sub  .
      hed-loop(heds t.heds)
    =/  tels  lets
    |-  ^-  long-ska
    =*  tel-loop  $
    ?~  tels  hed-loop(heds t.heds)
    ?.  =(fol.i.tels +.fol.i.q)
      =>  !@  ska-verb  .
          ~&  >>  %join-tail-wrong-fol  .
      tel-loop(tels t.tels)
    ?.  (huge:so less.i.tels sub.i.q)
      =>  !@  ska-verb  .
        ~&  >>  %join-tail-wrong-sub  .
      tel-loop(tels t.tels)
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
    =>  !@  ska-verb  .
        ~&  >  [%enqueu p]  .
    %-  ~(rep in q)
    |=  [s=sock =_b]
    =/  batt  (pull:so s 2)
    ?.  (all:ca cape.batt)
      =>  !@  ska-verb  .
          ~&  >>>  [%cold-miss-batt p]  .
      b
    =*  f  data.batt
    =/  ax=@  2
    |-  ^+  b
    ?:  ?=([@ *] f)  [[s f `[| p ax]] b]
    ?.  ?=([^ ^] f)
      =>  !@  ska-verb  .
          ~&  >>>  %strange-formula  .
      b
    =.  b  $(f -.f, ax (peg ax 2))
    =.  b  $(f +.f, ax (peg ax 3))
    [[s f `[& p ax]] b]
  ==
::
+$  bell-prod  (map bell [prod=sock map=spring])
::  does the code contain %fast hints?
::
++  has-fast
  |=  =nomm
  ^-  ?
  ?-  nomm
    [^ *]     |($(nomm -.nomm) $(nomm +.nomm))
    [%0 *]    |
    [%1 *]    |
    [%2 *]    |($(nomm p.nomm) $(nomm q.nomm))
    [%3 *]    $(nomm p.nomm)
    [%4 *]    $(nomm p.nomm)
    [%5 *]    |($(nomm p.nomm) $(nomm q.nomm))
    [%6 *]    |($(nomm p.nomm) $(nomm q.nomm) $(nomm r.nomm))
    [%7 *]    |($(nomm p.nomm) $(nomm q.nomm))
    [%10 *]   |($(nomm q.p.nomm) $(nomm q.nomm))
    [%12 *]   |($(nomm p.nomm) $(nomm q.nomm))
  ::
      [%11 *]
    ?@  p.nomm  $(nomm q.nomm)
    |(?=(%fast p.p.nomm) $(nomm q.p.nomm) $(nomm q.nomm))
  ==
::
++  get-fast-regs
  ~%  %get-fast-regs  ..ride  ~
  |=  $:  [bus=sock =nomm]
          g=callgraph
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
    ::  the analysis of the callee with exactly this subject, if it was one:
    ::  its product needs no masking
    ::
    ?^  there=(~(get by g) [sub fol.b.u.info.nomm])
      [prod.u.there gen]
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
    ?.  (all:ca cape.clue)
      =>  !@  ska-verb  .
          ~&  >>>  %fast-lost-clue  .
      gen
    =/  clue=*  data.clue
    ?.  ?=([name=$@(@tas [@tas @]) dad=^ *] clue)
      =>  !@  ska-verb  .
          ~&  >>>  [%fast-bad-clue clue]  .
      gen
    =/  label=term
      ?@  name.clue  name.clue
      (cat 3 -.name.clue (scot %ud +.name.clue))
    ::
    ?.  ((sane %tas) label)
      =>  !@  ska-verb  .
          ~&  >>>  fast-insane-label+label  .
      gen
    ?~  parent=(fast-parent dad.clue)
      =>  !@  ska-verb  .
          ~&  >>>  fast-bad-clue-parent+[label clue]  .
      gen
    ?~  u.parent
      ::  root registration
      ::
      ?.  (all:ca cape.prod)
        =>  !@  ska-verb  .
            ~&  >>>  %fast-lost-root  .
        gen
      %=  gen
        core  (~(put ju core.gen) ~[label] prod)
        root  (~(put ju root.gen) data.prod ~[label])
      ==
    ::  child core registration
    ::
    =/  axis=@  u.u.parent
    ?.  =(3 (cap axis))
      =>  !@  ska-verb  .
          ~&  >>>  fast-weird-axis+[label axis]  .
      gen
    =/  batt  (pull:so prod 2)
    ?.  (all:ca cape.batt)
      =>  !@  ska-verb  .
          ~&  >>>  fast-lost-batt+label  .
      gen
    ?.  ?=(^ data.batt)
      =>  !@  ska-verb  .
          ~&  >>>  fast-atom-batt+[label data.batt]  .
      gen
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
      =>  !@  ska-verb  .
          ~&  >>  missed-parent+label  .
      gen(miss &)
    =/  pax=path  [label i.past]
    =/  socks  ~(tap in (~(get ju core.gen) i.past))
    |-  ^+  gen
    =*  sock-loop  $
    ?~  socks
      =>  !@  ska-verb  .
          ~&  >>  missed-path+label  .
      past-loop(past t.past)
    ?.  (huge:so i.socks fore)  sock-loop(socks t.socks)
    =/  template=sock
      ::  put the parent into [formula *] sock
      ::
      (darn:so [[& |] data.batt ~] axis i.socks)
    ::
    =>  !@  ska-verb  .
        ~&  >  [%matched pax]  .
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
  ~%  %prune-callgraph  ..ride  ~
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
::  Match a bell against registered cores: look for its formula in the battery
::  of a core template that its subject fits. Produces the ring of the arm.
::
++  cole-match
  |=  [b=bell core=(jug path sock)]
  ^-  (unit ring)
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
::  We just analyzed a callgraph, called some new functions, maybe registered
::  some new jetted cores.
::  Did we call something from freshly registered cores? Did we call something
::  new from already registrated cores? This gate updates the bell <--> ring
::  mapping incrementally: the new bells are matched against all cores, and
::  the bells without a ring against the new cores. Bells that have a ring
::  keep it.
::
++  ska-cole-update
  |=  [lon=long-ska new-bells=(set bell) new-cores=(jug path sock)]
  ^-  long-ska
  =*  cole  cole.jets.lon
  =/  put
    |=  [b=bell r=ring c=_cole]
    ^+  c
    [(~(put by call.c) b r) (~(put ju back.c) r b)]
  ::
  =.  cole
    %-  ~(rep in new-bells)
    |=  [b=bell c=_cole]
    ?:  (~(has by call.c) b)  c
    ?~  r=(cole-match b core.jets.lon)  c
    (put b u.r c)
  ::
  ?:  =(~ new-cores)  lon
  =.  cole
    %-  ~(rep by code.lon)
    |=  [[b=bell *] c=_cole]
    ?:  (~(has by call.c) b)  c
    ?~  r=(cole-match b new-cores)  c
    (put b u.r c)
  lon
::  Reestablish the bell <--> ring mapping from scratch. +ska-poke keeps it up
::  to date, so this is only needed to check it.
::
++  ska-cole-restore
  |=  lon=long-ska
  ^-  long-ska
  =.  cole.jets.lon  [~ ~]
  (ska-cole-update lon ~(key by code.lon) core.jets.lon)
::
++  dif-so
  |=  [a=sock b=sock]
  ^-  (list (pair @ (lest (pair @ ?(%lost %data)))))
  =*  res  ,(list (pair @ (lest (pair @ ?(%lost %data)))))
  =/  rev  1
  |-  ^-  res
  ?:  |(?=(^ cape.a) ?=(^ cape.b))
    %:  weld
      $(a (hed:so a), b (hed:so b), rev (peg rev 2))
      $(a (tel:so a), b (tel:so b), rev (peg rev 3))
    ==
  ?:  ?=(%| cape.a)  ~
  ?:  ?=(%| cape.b)  ~[[rev ~[[1 %lost]]]]
  =/  rel  1
  =-  ?~  -  ~  ~[[rev -]]
  |-  ^-  (list (pair @ ?(%lost %data)))
  ?:  =(data.a data.b)  ~
  ?.  &(?=(^ data.a) ?=(^ data.b))  ~[[rel %data]]
  %:  weld
    $(data.a -.data.a, data.b -.data.b, rel (peg rel 2))
    $(data.a +.data.a, data.b +.data.b, rel (peg rel 3))
  ==
::
++  norm-so
  |=  s=sock
  ^-  sock
  =*  norm-so  .
  ?:  ?=(@ cape.s)  s
  ~+
  =;  out=sock  =+(=(out s) out)
  =/  h=sock  (norm-so -.cape.s -.data.s)
  =/  t=sock  (norm-so +.cape.s +.data.s)
  :_  [data.h data.t]
  ?:  &(?=(? cape.h) =(cape.h cape.t))  cape.h
  [cape.h cape.t]
::
++  norm-pi
  |=  m=spring
  ^-  spring
  =*  norm-pi  .
  ?@  m  m
  ~+
  =/  l  (norm-pi -.m)
  =/  r  (norm-pi +.m)
  ::  [2n 2n+1] -> n, n != 0
  ::
  ?:  ?&  ?=(@ l)
          ?=(@ r)
          !=(0 l)
          =(0 (mod l 2))
          =(+(l) r)
      ==
    (div l 2)
  [l r]
::
++  normalize-prod
  ~%  %normalize-prod  ..ride  ~
  |=  prod=[s=sock m=spring]
  ^+  prod
  [(norm-so s.prod) (norm-pi m.prod)]
::
++  ska-poke
  |=  [[bus=sock fol=^] lon=long-ska]
  ^-  [bell long-ska]
  =/  root-identity=identity  [bus fol]
  =/  g=callgraph  -:(ska-callgraph root-identity memo.final.lon)
  ::
  =/  pruned=callgraph  (prune-callgraph g root-identity `graph.final.lon)
  =.  graph.final.lon  (~(uni by graph.final.lon) pruned)
  ::  Product of a function by bell, for +get-fast-regs, which masks the parts
  ::  captured from the subject with the subject at the callsite. Functions
  ::  with the same bell agree on the product outside of the captured parts,
  ::  so any of them will do.
  ::
  =/  =bell-prod
    =<  $  ~%  %poke-bell-prod  ..ride  ~  |.
    %-  ~(rep by graph.final.lon)
    |=  [[id=identity d=datum] acc=bell-prod]
    =/  b=bell  [less-code.d fol.id]
    ?:  (~(has by acc) b)  acc
    (~(put by acc) b prod.d map.d)
  ::
  =>  !@  check-bell-prod  .
      =*  dot  .
      =<  dot
      %-  ~(rep by graph.final.lon)
      |=  [[id=identity d=datum] acc=bell-prod]
      =/  b=bell  [less-code.d fol.id]
      =;  prod=[sock spring]
        ?~  have=(~(get by acc) b)  (~(put by acc) b prod)
        ?.  =(prod u.have)
          ?.  =(`sock`-.prod `sock`-.u.have)
            ~|  (dif-so -.prod -.u.have)
            !!
          ~|  [+.prod +.u.have]
          !!
        acc
      ::
      %-  normalize-prod
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
  =/  sccs=(list (set bell))
    =<  $  ~%  %poke-tarjan  ..ride  ~  |.
    (flop (tarjan bg))
  =^  just-code=(map bell nomm)  lon
    =<  $  ~%  %poke-just-code  ..ride  ~  |.
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
    =<  $  ~%  %poke-scc-loop  ..ride  ~  |.
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
  =/  root-bell=bell  [less-code.root-datum fol]
  =/  [root=(jug * path) core=(jug path sock) batt=(jug ^ path)]
    =<  $  ~%  %poke-jets-loop  ..ride  ~  |.
    =/  queu=callgraph
      %-  ~(rep by pruned)
      |=  [[id=identity d=datum] acc=callgraph]
      ?.  (has-fast nomm.d)  acc
      (~(put by acc) id d)
    =/  gen  [queu=queu jets=[=_root =_core =_batt]:jets.lon]
    |-  ^+  jets.gen
    =;  [queu1=callgraph jets1=_[root core batt]:jets.lon]
      ?:  =(jets.gen jets1)  jets.gen
      ?:  =(queu1 ~)  jets1
      $(gen [queu1 jets1])
    ::
    %-  ~(rep by queu.gen)
    |=  [[id=identity d=datum] acc=_`_gen`[~ jets.gen]]
    =^  miss=?  jets.acc
      (get-fast-regs [more.id nomm.d] graph.final.lon bell-prod jets.acc)
    :_  jets.acc
    ?.  miss  queu.acc
    (~(put by queu.acc) id d)
  ::
  :-  root-bell
  =/  new-cores=(jug path sock)  ((dif-ju core) core.jets.lon)
  =.  lon  lon(root.jets root, core.jets core, batt.jets batt)
  (ska-cole-update lon ~(key by just-code) new-cores)
::  produces data about a function
::  pure: no crashes + no hints excepts %fast (call to it could be omitted)
::  total: no crashes (stacktrace boundaries around them could be omitted)
::
++  eval-finalized
  =*  hint-pure  ,?(%fast %spot %mean)
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
  ~%  %tarjan  ..ride  ~
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
  ~%  %update-transitive  ..ride  ~
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
  ~%  %closures-update-prev-trans  ..ride  ~
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
::  Analysis of the call graph rooted at a function. Produces a list for
::  historical reasons: the callgraph is its only element.
::
::  The graph is explored depth-first: a direct call to a function that is not
::  in the graph yet analyzes that function right away, before the caller
::  proceeds, so a function that is not on a cycle is analyzed exactly once,
::  with its callees final. Cycles are found with Tarjan's SCC algorithm on the
::  fly: a function stays on the stack (.stk) while a function below it on the
::  stack is reachable from it, and when the root of a strongly connected
::  component finishes, the component is reanalyzed in passes until no member
::  changes. A pass may discover new functions, which join the component if
::  they call back into it. A call to a function on the stack is a recursive
::  call: its product is erased and only its code requirement is used, the
::  same pessimization as for a call merged into a function in progress.
::  Code requirements only grow, so the passes converge (Kleene iteration
::  over the products would not: the least fixed point of a product like
::  [1 $] does not exist).
::
::  Functions popped off the stack are final and get memoized in .done, so
::  that a later call to the same formula with a subject that provides what a
::  finished function used resolves to that function instead of a new one.
::
++  ska-callgraph
  ~%  %ska-callgraph  ..ride  ~
  !.
  |=  [[bus=sock fol=^] memo-final=memo]
  ^-  (list callgraph)
  =|  st=ska-state
  =<  =/  res  (analyze [bus fol] st)
      =>  !@  ska-verb  .
          ~&  [%ska-callgraph functions+~(wyt by g.st.res) runs+runs.st.res]
          .
      [g.st.res ~]
  |%
  ::  Analyze a function that is not in the graph yet, and the functions it
  ::  calls. Produces the lowest DFS number of a function in progress reachable
  ::  from it (Tarjan's lowlink), or .next if none.
  ::
  ++  analyze
    ~%  %ska-analyze  ..ride  ~
    |=  [id=identity st=ska-state]
    ^-  [low=@ st=ska-state]
    ::  analyzed in a previous poke: the callees of the memoized function are
    ::  in the finalized graph already
    ::
    ?^  hit=(git:mi memo-final fol.id more.id)
      =/  d=datum  +.u.hit
      :-  next.st
      st(g (~(put by g.st) id d), done (put:mi done.st id d))
    =/  index=@  next.st
    =.  st
      %_  st
        next   +(index)
        order  (~(put by order.st) id index)
        stk    [id stk.st]
        g      (~(put by g.st) id *datum)
      ==
    =^  [low=@ back=? changed=?]  st  (run id index st)
    ?.  =(low index)  [low st]
    ::  .id is the root of a strongly connected component: everything above it
    ::  on the stack. If it is trivial, it is final.
    ::
    ?.  |(back !?=([* ~] (above id stk.st)))
      [next.st (pop id st)]
    ::  Reanalyze the component until it is stable. Members are swept latest
    ::  first, which puts callees before callers along the DFS tree. A pass may
    ::  find a call to a function below .id on the stack: then .id was not the
    ::  root after all, and the component stays on the stack for the real root
    ::  to iterate.
    ::
    |-  ^-  [@ ska-state]
    =*  pass-loop  $
    =/  members=(list identity)  (above id stk.st)
    =^  [low=@ changed=?]  st
      |-  ^-  [[@ ?] ska-state]
      ?~  members  [[index |] st]
      =^  [low-m=@ back-m=? changed-m=?]  st
        (run i.members (~(got by order.st) i.members) st)
      ?:  (lth low-m index)  [[low-m |] st]
      =^  [low-t=@ changed-t=?]  st  $(members t.members)
      [[(min low-m low-t) |(changed-m changed-t)] st]
    ?:  (lth low index)  [low st]
    ::  another pass if a member changed or new members joined
    ::
    ?:  |(changed !=((lent members) (lent (above id stk.st))))  pass-loop
    [next.st (pop id st)]
  ::  functions on the stack above and including .id, latest first
  ::
  ++  above
    |=  [id=identity stk=(list identity)]
    ^-  (list identity)
    ?~  stk  ~|(%ska-stack !!)
    ?:  =(id i.stk)  [id ~]
    [i.stk $(stk t.stk)]
  ::  pop a finished component off the stack, memoizing its members
  ::
  ++  pop
    |=  [id=identity st=ska-state]
    ^-  ska-state
    ::  no ?~ on stk.st: it would refine the type of .st, and .st could not
    ::  be edited with an empty stack anymore
    ::
    =/  top=identity  ?~(stk.st ~|(%ska-stack !!) i.stk.st)
    =/  rest=(list identity)  ?~(stk.st ~|(%ska-stack !!) t.stk.st)
    =.  st
      %_  st
        stk    rest
        order  (~(del by order.st) top)
        done   (put:mi done.st top (git-g g.st top))
      ==
    ?:  =(top id)  st
    $(st st)
  ::  One analysis pass over the formula of .id, updating its entry in the
  ::  graph. Produces its lowlink, whether it called a function in progress,
  ::  and whether the entry changed in a way that affects its callers.
  ::
  ++  run
    ~%  %ska-callgraph-iteration  ..ride  ~
    |=  [id=identity index=@ st=ska-state]
    ^-  [[low=@ back=? changed=?] st=ska-state]
    =.  runs.st  +(runs.st)
    =/  data=datum  (git-g g.st id)
    =/  bus=sock  more.id
    =/  fol  fol.id
    =/  sub=sock-anno  [bus 1]
    =*  fol-result
      $:  [=nomm pro=sock-anno]
          want=cape
          indi=cape
          callees=(set callee-entry)
          area=(unit spot)
          low=@
          back=?
          st=ska-state
      ==
    ::
    =;  ,fol-result
      ::  construct datum
      ::
      =/  less-code  (app:ca want bus)
      =/  capture=cape  (prune:pi src.pro cape.sock.pro)
      =/  less-memo  (app:ca (uni:ca want capture) bus)
      =/  data-new=datum  [callees nomm less-code less-memo indi pro area]
      =?  indi.data-new
          ?&  =([less-code prod map]:data-new [less-code prod map]:data)
              !=(indi.data-new indi.data)
          ==
        ::  if new datum only differs in indi.data-new,
        ::  turn disagreeing parts into %.y so that we converge
        ::
        (msg-ca indi.data-new indi.data)
      =/  changed=?
        !=([less-code prod map indi]:data-new [less-code prod map indi]:data)
      :-  [low back changed]
      st(g (~(put by g.st) id data-new))
    ::
    =/  gen
      ^-  $:  want=cape
              indi=cape
              callees=(set callee-entry)
              area=(unit spot)
              low=@
              back=?
              st=ska-state
          ==
      [| | ~ ~ index | st]
    =/  seat=(unit spot)  ~
    =/  memo-key=(unit *)  ~
    =/  virt-call=?  |
    ^-  [[=nomm prod=sock-anno] gen=_gen]
    =<  $
    ~%  %fol-loop  ..ride  ~
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
      ~%  %nock-2  ..ride  ~
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
      ~%  %nock-2-direct-non-inlined  ..ride  ~
      |.
      ^-  [[nomm sock-anno] _gen]
      =^  [id-there=identity dat-there=datum]  gen
        =/  id-there=identity  [sock.prod.s fol-new]
        |-  ^-  [[identity datum] _gen]
        =*  resolve  $
        ?^  d=(~(get by g.st.gen) id-there)
          ::  in the graph. A function in progress: recursive call, use its
          ::  code requirement but not its product
          ::
          ?~  ord=(~(get by order.st.gen) id-there)  [[id-there u.d] gen]
          :-  [id-there u.d(prod |+~, map ~)]
          gen(low (min low.gen u.ord), back &)
        ::  a finished function with the same formula whose subject
        ::  requirement is satisfied here
        ::
        ?^  m=(git:mi done.st.gen fol-new sock.prod.s)
          [u.m gen]
        ::  a recursive call to a function in progress with a different
        ::  subject: its product is erased, as only its code requirement is
        ::  known to be satisfied. Or a call in a chain of growing subjects,
        ::  generalized
        ::
        ?^  par=(recursive-call id-there stk.st.gen g.st.gen)
          ?-    -.u.par
              %gen  resolve(id-there +.u.par)
              %merge
            =/  d=datum  (git-g g.st.gen +.u.par)
            :-  [+.u.par d(prod |+~, map ~)]
            gen(low (min low.gen (~(got by order.st.gen) +.u.par)), back &)
          ==
        ::  a new function: analyze it now
        ::
        =^  low-there=@  st.gen  (analyze id-there st.gen)
        =.  low.gen  (min low.gen low-there)
        [[id-there (git-g g.st.gen id-there)] gen]
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
=/  shape-check  ~
::
|%
+$  hint-static  ?(%bout %xray)
+$  hint-dynamic  ?(%bout %xray %spin %jinx %live hint-dynamic-stop)
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
      bo-gen=_`@uwoo`1  ::  0 is reserved for the entry point
      id-gen=@uxid                   ::  branch region identifiers
      mode=?(%drop %run)
      blocks=(map @uwoo blob)
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
      [%equ l=@uvre r=@uvre]                      ::  =(l r) for the sideeffect
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
::  Ops that cannot crash
::
+$  pole-not-crashing
  $>(?(%imm %mov %con %hed %tal %hsp %hse %hdp %hde %equ) pole)
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
    %equ  ~[l r]:op
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
    %brz  [s.op (weld (jmp-regs z.op) (jmp-regs o.op))]
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
    %brz  ~[z o]
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
    %brz  fin(s (ren s.fin), z (ren-jmp z.fin), o (ren-jmp o.fin))
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
  ~%  %compile-unary  ..ride  ~
  |=  $:  func=bell
          scc=(set bell)
          rev=(jug bell bell)  ::  reversed call graph
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
      ==
  ^-  [straight (map bell straight)]
  ~>  %memo./ska
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
  ~%  %compile-scc  ..ride  ~
  |=  $:  scc=(set bell)
          rev=(jug bell bell)
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
      ==
  ^-  (map bell straight)
  ::  Transient memoization for local tests, persistent memoization for stateful
  ::  interaction. The latter requires running SKA core with an empty scry gate.
  ~+
  ~>  %memo./ska
  ::  Only the subject shapes in .map-local are read by the loop, so the rest
  ::  of the straight is a placeholder until the fixed point is reached, when
  ::  the whole SCC is compiled once more with .done set, this time for real
  ::
  =|  map-local=(map bell straight)
  ::  Fixed-point loop with a worklist
  ::
  =/  w=worklist  scc
  =/  done=?  |
  |-  ^+  map-local
  =*  fixpoint-compilation  $
  =;  [w-new=worklist map-local1=_map-local]
    ?:  done  map-local1
    =.  w-new  (~(int in w-new) scc)
    ?:  =(~ w-new)  fixpoint-compilation(w scc, map-local map-local1, done &)
    =>  !@  comp-verb  .
        ~&  %fixpoint-compilation  .
    fixpoint-compilation(w w-new, map-local map-local1)
  ::
  %-  ~(rep in w)
  ~%  %compile-scc-fn  ..ride  ~
  |=  [b=bell w-new=worklist =_map-local]
  ^+  [w-new map-local]
  =/  comp  (comp scc rev long-ska scc-map jets-hot map-local b)
  =/  =nomm  nomm:(~(got by code.long-ska) b)
  ::  Until the fixed point only the input shape is needed: from the shape-only
  ::  traversal, or from the full compilation with code emission dropped.  The
  ::  final pass compiles for real, emitting code right away.
  ::
  =/  gen=line-short  *line-short
  =^  [need-new=need-ordered laz=need-lazy ned-final=need o=@uwoo]  gen
    !@  dedicated-shape-pass
      =.  mode.gen  ?:(done %run %drop)
      =^  nex  gen  (~(run comp gen) | nomm [%done ~] ~)
      =^  [ned-final=need laz=need-lazy o=@uwoo]  gen
        (~(collapse-shape comp gen) nex cape.less.b)
      ::
      [[(need-to-ordered ned-final) laz ned-final o] gen]
    ?.  done
      =^  l=laze  gen  (~(run-shape comp gen) nomm [%done ~])
      [[(laze-collapse l cape.less.b) *need-lazy *need `@uwoo`0] gen]
    =.  mode.gen  %run
    =^  nex  gen  (~(run comp gen) | nomm [%done ~] ~)
    =^  [ned-final=need laz=need-lazy o=@uwoo]  gen
      (~(collapse-shape comp gen) nex cape.less.b)
    ::
    [[(need-to-ordered ned-final) laz ned-final o] gen]
  ::  Debug assert of +run-shape correctenss
  ::
  =>  =*  dot  .
      !@  shape-check  dot
      ?.  done  dot
      =/  l=laze  -:(~(run-shape comp *line-short) nomm [%done ~])
      =/  shape  (laze-collapse l cape.less.b)
      ~|  [%shape-mismatch b shape need-new]
      ?>  =(shape need-new)
      dot
  ::
  ::  Finalization: emit the subject deconsing code, coerce the subject to the
  ::  pessimized shape if there is one, and renumber the registers
  ::
  =/  finish
    ~%  %compile-scc-finish  ..ride  ~
    |=  pessimized=(unit need-ordered)
    ^-  straight
    ::  argument count and the blocks are bunted unless fixed point of the
    ::  subject shape was achieved
    ::
    ?.  done  [?~(pessimized need-new u.pessimized) 0 ~]
    =.  gen  (~(coerce-lazy comp gen) ned-final o laz)
    =/  res=next-resolved  [%next [[ned-final ~] ~ ~] ~ o]
    ?~  pessimized  (~(to-straight comp gen) res)
    =^  coerced=next-resolved  gen  (~(coerce-ord comp gen) u.pessimized res)
    (~(to-straight comp gen) coerced)
  ::  With a compiled function candidate, requeue callers if the subject split
  ::  did not converge yet, taking MSG of subject splits to avoid divergence.
  ::
  ?~  s-previous=(~(get by map-local) b)
    :-  ?:  ?=([%none ~] need-new)  w-new
        (~(uni in w-new) (~(get ju rev) b))
    (~(put by map-local) b (finish ~))
  =/  need-pessimized  (msg-need-ord need-new need.u.s-previous cape.less.b)
  :-  ?:  =(need-pessimized need.u.s-previous)  w-new
      (~(uni in w-new) (~(get ju rev) b))
  %+  ~(put by map-local)  b
  ?:  =(need-pessimized need-new)  (finish ~)
  (finish `need-pessimized)
::
++  need-normalize
  ~%  %need-normalize  ..ride  ~
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
    ~%  %comp-run  ..ride  ~
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
      =^  r-p  gen  re
      =^  r-q  gen  re
      =^  o=@uwoo  gen
        ?-    -.goal
            %pick  (emit ~ ~ eqq+[r-p r-q [z o]:goal])
        ::
            %done
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
        =.  gen  (set-tag yes region)
        =.  gen  (set-tag nuh region)
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
    |=  [=nomm goal=goal-shape]
    ^-  [laze _gen]
    =/  none=laze  *laze
    =/  this=laze  [[this+~ ~] ~ ~]
    ::  what +simple-next does to the goal
    ::
    =/  simple=$>(%next goal-shape)  ?:(?=(%next -.goal) goal [%next this])
    ?-    nomm
        [^ *]
      ?-    -.goal
          %done  $(goal [%next this])
      ::
          %pick
        =^  l-2  gen  $(nomm +.nomm, goal [%next none])
        =^  l-1  gen  $(nomm -.nomm, goal [%next none])
        [(laze-copy l-1 l-2) gen]
      ::
          %next
        =/  [hed=laze tel=laze]  (laze-split laz.goal)
        =^  l-2  gen  $(nomm +.nomm, goal [%next tel])
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
      =^  l-sub  gen
        ?:  drop  $(nomm p.nomm, goal [%next none])
        $(nomm p.nomm, goal [%next [[(callee-need b-callee) ~] ~ ~]])
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
      =^  l-p  gen  $(nomm p.nomm, goal [%next this])
      [(laze-copy l-p l-q) gen]
    ::
        [%6 *]
      ?:  ?&  ?=(%next -.goal)
              !(laze-none-equivalent laz.goal(sure *sure-ordered))
          ==
        =^  [goal-0=laze goal-1=laze]  gen  (laze-branch laz.goal)
        =^  l-1  gen  $(nomm r.nomm, goal [%next goal-1])
        =^  l-0  gen  $(nomm q.nomm, goal [%next goal-0])
        =^  lazy  gen  (laze-sect l-0 l-1)
        =^  l-cond  gen  $(nomm p.nomm, goal [%next this])
        [(laze-copy l-cond lazy) gen]
      =/  goal-branch=goal-shape
        ?.  ?=(%next -.goal)  goal
        [%next [sure.laz.goal ~ ~]]
      =^  l-1  gen  $(nomm r.nomm, goal goal-branch)
      =^  l-0  gen  $(nomm q.nomm, goal goal-branch)
      =^  lazy  gen  (laze-sect l-0 l-1)
      =^  l-cond  gen  $(nomm p.nomm, goal [%pick ~])
      [(laze-copy l-cond lazy) gen]
    ::
        [%7 *]
      =^  l  gen  $(nomm q.nomm)
      $(nomm p.nomm, goal [%next l])
    ::
        [%10 *]
      ?>  ?=(%next -.simple)
      =/  [don=laze rec=laze]  (laze-into p.p.nomm laz.simple)
      =^  l-rec  gen  $(nomm q.nomm, goal [%next rec])
      =^  l-don  gen  $(nomm q.p.nomm, goal [%next don])
      [(laze-copy l-don l-rec) gen]
    ::
        [%11 *]
      ?@  p.nomm
        ?.  ?=(hint-static p.nomm)  $(nomm q.nomm)
        $(nomm q.nomm, goal simple)
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  l-fol  gen  $(nomm q.nomm)
        ?:  (safe-nomm q.p.nomm)  [l-fol gen]
        =^  l-toke  gen  $(nomm q.p.nomm, goal [%next none])
        [(laze-copy l-toke l-fol) gen]
      =^  l-fol=laze  gen  $(nomm q.nomm, goal simple)
      =^  l-fol=laze  gen
        ?.  ?=(hint-dynamic-stop p.p.nomm)  [l-fol gen]
        =^  i  gen  id
        [[*sure-ordered ~ [i l-fol]~] gen]
      =^  l-toke  gen  $(nomm q.p.nomm, goal [%next this])
      [(laze-copy l-toke l-fol) gen]
    ::
        [%12 *]
      =^  l-q  gen  $(nomm q.nomm, goal [%next this])
      =^  l-p  gen  $(nomm p.nomm, goal [%next this])
      [(laze-copy l-p l-q) gen]
    ==
  ::  register-less need of the callee: jet or SCC-local best guess or recur
  ::
  ++  callee-need
    |=  b-callee=bell
    ^-  need-ordered
    =/  rin=(unit ring)  (~(get by call.cole.jets.long-ska) b-callee)
    ?^  j=(biff rin ~(get by jets-hot))  u.j
    ?:  (~(has in scc) b-callee)
      need:(~(gut by map-local) b-callee *straight)
    =/  new-scc=(set bell)  (~(gut by scc-map) b-callee [b-callee ~ ~])
    =<  need
    (~(got by (compile-scc new-scc rev long-ska scc-map jets-hot)) b-callee)
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
  ::  +must for shapes
  ::
  ++  laze-must
    |=  ned=need-ordered
    ^-  need-ordered
    ?-  -.ned
      %both  ned
      %this  ned
      ^      [%both ned]
      %none  [%this ~]
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
      ==
    ::
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
    :-  [[ned-h lok-h] (turn forks head) (turn bonds head)]
    [[ned-t lok-t] (turn forks tail) (turn bonds tail)]
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
      ==
    ::
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
    :-  [[ned-don lok-don] (turn forks head) (turn bonds head)]
    [[ned-rec lok-rec] (turn forks tail) (turn bonds tail)]
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
    :+  sur
      %+  turn  fork.laz
      |=  [y=[o=@uxid laz=laze] n=[o=@uxid laz=laze]]
      [y(laz (laze-from axe laz.y)) n(laz (laze-from axe laz.n))]
    %+  turn  bond.laz
    |=  [o=@uxid laz=laze]
    [o (laze-from axe laz)]
  ::  +copy for shapes
  ::
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
  ::  +fork for shapes: the same shape for both branches, fresh identifiers
  ::
  ++  laze-branch
    ~%  %comp-laze-branch  ..ride  ~
    |=  laz=laze
    ^-  [[laze laze] _gen]
    =^  forks=(list [laze-fork laze-fork])  gen
      %^  spin  fork.laz  gen
      |=  [[y=[o=@uxid laz=laze] n=[o=@uxid laz=laze]] gen-acc=_gen]
      ^-  [[laze-fork laze-fork] _gen]
      =.  gen  gen-acc
      =^  o-0-y  gen  id
      =^  o-1-y  gen  id
      =^  o-0-n  gen  id
      =^  o-1-n  gen  id
      =^  [y-0=laze y-1=laze]  gen  (laze-branch laz.y)
      =^  [n-0=laze n-1=laze]  gen  (laze-branch laz.n)
      :_  gen
      [[[o-0-y y-0] [o-0-n n-0]] [[o-1-y y-1] [o-1-n n-1]]]
    ::
    =^  bonds=(list [laze-bond laze-bond])  gen
      %^  spin  bond.laz  gen
      |=  [[o=@uxid laz=laze] gen-acc=_gen]
      ^-  [[laze-bond laze-bond] _gen]
      =.  gen  gen-acc
      =^  o-0  gen  id
      =^  o-1  gen  id
      =^  [l-0=laze l-1=laze]  gen  (laze-branch laz)
      [[[o-0 l-0] [o-1 l-1]] gen]
    ::
    :_  gen
    :-  [sure.laz (turn forks head) (turn bonds head)]
    [sure.laz (turn forks tail) (turn bonds tail)]
  ::  +sect for shapes
  ::
  ++  laze-sect
    |=  [l-0=laze l-1=laze]
    ^-  [laze _gen]
    =^  o-0  gen  id
    =^  o-1  gen  id
    [[*sure-ordered [[o-0 l-0] [o-1 l-1]]~ ~] gen]
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
    =^  ned  gen  (sure-require-look sur)
    ?:  ?=(%none -.ned)  gen
    =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
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
    ~%  %comp-collapse-lazy-atom  ..ride  ~
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
    ?:  dropping  gen
    ::  add moves wherever lazy needs need one noun, crashes wherever lazy
    ::  needs need more than an atom
    ::
    =/  o  there.then.nex
    %^  walk-lazy  o  laz.nex(ned.sure this+r)
    |=  [o-laz=@uwoo sur=sure gen-init=_gen]
    ^+  gen
    =.  gen  gen-init
    =^  ned-sure=need  gen  (sure-require-look sur)
    ?:  ?=(%none -.ned-sure)  gen
    ?:  ?=(%this -.ned-sure)
      ?:  =(r r.ned-sure)  gen
      =^  src  gen  ?:(=(o-laz o) [r gen] (proxy r o-laz))
      (add-ops o-laz [%mov src r.ned-sure]~)
    (emir o-laz ~ ~ %bom ~)
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
    ==
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
  ::  Here the idea is that we materialize the conditional as a register with
  ::  a loobean, then the lazy needs get forked, and the BB of that need gets
  ::  code that branches on the conditional register and fulfills the original
  ::  need with either of the two
  ::
  ++  fork
    ~%  %comp-fork  ..ride  ~
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
      =.  gen  (copy-tag o.y ~[o-0-kid-y o-1-kid-y])
      =.  gen  (copy-tag o.n ~[o-0-kid-n o-1-kid-n])
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
      =^  o-insert1-y=@uwoo  gen  (emit ~ ~ [%brz p-y ~^o-0-kid-y ~^o-1-kid-y])
      =^  o-insert1-n=@uwoo  gen  (emit ~ ~ [%brz p-n ~^o-0-kid-n ~^o-1-kid-n])
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
      =.  gen  (copy-tag o-bond ~[o-0-kid o-1-kid])
      =^  [laz-0=need-lazy laz-1=need-lazy]  gen
        %=  fork-loop
          laz  laz-bond
          o    o-insert2
          o-0  o-0-kid
          o-1  o-1-kid
        ==
      ::
      =^  p  gen  (proxy r-cond o-bond)
      =^  o-insert1=@uwoo  gen  (emit ~ ~ [%brz p ~^o-0-kid ~^o-1-kid])
      =.  gen  (insert-hop o-bond o-insert1 o-insert2)
      [[[o-0-kid laz-0] [o-1-kid laz-1]] gen]
    ::
    :_  gen
    :-  [sure-0 fork-0 bond-0]
    [sure-1 fork-1 bond-1]
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
    :+  (from-sure axe sure.laz)
      %+  turn  fork.laz
      |=  [y=[@uwoo laz=need-lazy] n=[@uwoo laz=need-lazy]]
      [y(laz from-buc(laz laz.y)) n(laz from-buc(laz laz.n))]
    %+  turn  bond.laz
    |=  [o=@uwoo laz=need-lazy]
    [o from-buc(laz laz)]
  ::
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
      =^  l  gen  (must h.ned)
      =^  r  gen  (must t.ned)
      =/  =pole  [%con p.l p.r r.ned]
      =+  [new old]=?:(h [q.l q.r] [q.r q.l])
      $(tack [[h old] tack], ned new, ops [pole ops], axe lat)
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
      =^  hed  gen  (must h.ned)
      =^  tel  gen  (must t.ned)
      =.       gen  (add-ops o [%con p.hed p.tel r.ned]~)
      [[q.hed q.tel] gen]
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
    ==
  ::
  ++  split
    ~%  %comp-split  ..ride  ~
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
    ~%  %comp-add-ops  ..ride  ~
    |=  [o=@uwoo ops=(list pole)]
    ^+  gen
    ?:  dropping  gen
    =/  =blob  (~(got by blocks.gen) o)
    =.  body.blob  (weld ops body.blob)
    gen(blocks (~(put by blocks.gen) o blob))
  ::
  ++  emir
    ~%  %comp-emir  ..ride  ~
    |=  [o=@uwoo =blob]
    ^+  gen
    ?:  dropping  gen
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
    ~%  %comp-coerce-ord  ..ride  ~
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
    ==
  ::  With the top level need finally known, emit noun splitting code into
  ::  appropriate BBs
  ::
  ++  coerce-lazy
    ~%  %comp-coerce-lazy  ..ride  ~
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
    =^  [ned-final=need laz=need-lazy o=@uwoo]  gen  (collapse-shape nex less)
    :-  [%next [[ned-final ~] ~ ~] ~ o]
    (coerce-lazy ned-final o laz)
  ::  Shape of the subject with registers allocated, without the deconsing
  ::  code: the input shape is all that the compilation fixed point reads
  ::
  ++  collapse-shape
    ~%  %comp-collapse-shape  ..ride  ~
    |=  [nex=next less=cape]
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
    ++  rer
      |=  r=@uvre
      ^-  [@uvre _gen]
      =.  r  (unproxy r)
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
  ~%  %msg-need-ord  ..ride  ~
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
++  inter1-to-inter2
  ~%  %inter1-to-inter2  ..ride  ~
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
++  laze-to-inter1
  ~%  %laze-to-inter1  ..ride  ~
  |=  laz=laze
  ^-  need-inter1
  =*  laze-to-inter  .
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
++  laze-collapse
  ~%  %laze-collapse  ..ride  ~
  |=  [laz=laze less=cape]
  ^-  need-ordered
  (inter2-collapse (inter1-to-inter2 (laze-to-inter1 laz) less) less)
::
++  shape-collapse
  ~%  %shape-collapse  ..ride  ~
  |=  [laz=need-lazy less=cape]
  ^-  need-ordered
  (inter2-collapse (inter1-to-inter2 (lazy-to-inter1 laz) less) less)
::
++  inter2-collapse
  ~%  %inter2-collapse  ..ride  ~
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
  ~%  %msg-need-ord-fix-aware  ..ride  ~
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
    ?:  =(p.n.a p.n.b)
      %=  b
        n  [p.n.b (join-reg q.n.a q.n.b)]
        l  $(b l.b, a l.a)
        r  $(b r.b, a r.a)
      ==
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
    ?:  =(p.n.a p.n.b)
      =/  v  (~(int in q.n.a) q.n.b)
      =/  l  $(b l.b, a l.a)
      =/  r  $(b r.b, a r.a)
      ?:  =(~ v)  (~(uni by l) r)
      [[p.n.b v] l r]
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
      ops     ?~(i.args-a ops [[%mov u.i.args-a i.args-b] ops])
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
  =*  key  ,[hint=?(%spot %mean) reg=@uvre]
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
      ?:  &(?=(%hdp -.op) ?=(?(%spot %mean) n.op))
        $(body t.body, open (~(put in open) [n.op p.op]))
      ?:  &(?=(%hde -.op) ?=(?(%spot %mean) n.op))
        $(body t.body, open (~(del in open) [n.op p.op]))
      ?:  ?=(pole-not-crashing op)  $(body t.body)
      $(body t.body, unsafe (~(uni in unsafe) open))
    =?  unsafe  !?=(?(%clq %eqq %brz %hop) -.fin.b)  (~(uni in unsafe) open)
    ^$(topo t.topo, out (~(put by out) i.topo open))
  ::
  %-  ~(rep by blocks)
  |=  [[o=@uwoo b=blob] new=(map @uwoo blob)]
  =/  body
    %+  skip  body.b
    |=  op=pole
    ?&  ?=(?(%hdp %hde) -.op)
        ?=(?(%spot %mean) n.op)
        !(~(has in unsafe) [n p]:op)
    ==
  ::
  (~(put by new) o b(body body))
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
++  optimize
  ~%  %optimize  ..ride  ~
  |=  s=straight
  ^-  straight
  ?:  |  s
  =^  changed=?  s  (optimize-once s)
  ?.  changed  s
  $(s s)
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
      [%jets p=(list (pair ring need-ordered))]
      [%dire b=bell]
  ==
::
+$  prod
  $@  ~
  $%  [%ir b=bell p=straight]
  ==
::
++  validate-ovum
  |=  n=*
  ^-  ovum
  =;  out  =+(=(n out) out)
  ?@  n  !!
  ?+  -.n  !!
    ?(%full %jets)  ;;(ovum n)
    %dire  [%dire (validate-bell +.n)]
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
--
::
=|  state=[%0 =long-ska jets-hot=(map ring need-ordered)]
|%
++  version  -.state
++  graph-info
  ^-  [rev=(jug bell bell) scc-map=(map bell (set bell))]
  ~>  %memo./ska  ::  proper explicit memoization?
  =/  [bell-graph=(jug bell bell) rev=(jug bell bell)]  ::  XX make incremental?
    (simple-bell-graph-and-reversed graph.final.long-ska.state)
  ::
  :-  rev
  =/  sccs=(list (set bell))  (tarjan bell-graph)  ::  XX make incremental?
  =|  out=(map bell (set bell))
  |-  ^+  out
  ?~  sccs  out
  =.  out
    %-  ~(rep in i.sccs)
    |=  [b=bell acc=_out]
    (~(put by acc) b i.sccs)
  ::
  $(sccs t.sccs)
--
::
|%
++  load  !!  ::  +4
++  peek      ::  +22
  |=  pax=path
  ^-  (unit (pair @tas *))
  ?+  pax  !!
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
      %jets  [~ ..poke(jets-hot.state (malt p.ovo))]
  ::
      %full
    =^  func=bell  long-ska.state  (ska-poke [&+sub.ovo fol.ovo] long-ska.state)
    =/  [rev=(jug bell bell) scc-map=(map bell (set bell))]  graph-info
    =/  scc=(set bell)  (~(gut by scc-map) func [func ~ ~])
    =/  =straight
      =<  -
      %-  compile-unary
      [func scc rev [code jets]:long-ska.state scc-map jets-hot.state]
    ::
    =.  straight  (optimize straight)
    [[%ir func straight] ..poke]
  ::
      %dire
    =/  [rev=(jug bell bell) scc-map=(map bell (set bell))]  graph-info
    =/  scc=(set bell)  (~(gut by scc-map) b.ovo [b.ovo ~ ~])
    =/  =straight
      =-  (~(got by -) b.ovo)
      %-  compile-scc
      [scc rev [code jets]:long-ska.state scc-map jets-hot.state]
    ::
    =.  straight  (optimize straight)
    [[%ir b.ovo straight] ..poke]
  ==
::
++  wish  !!  ::  +10
--