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
::    Call graph construction:  line 462
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
::    As the analysis results are going to be persisted, we will need to keep
::    track of all the functions we discovered so far, as well as the cold
::    state.  We can use a pair [sock formula] as a unique identifier of a
::    function.
::
::    We also need to keep track of the accumulated cold state, with jet
::    registrations represented as pairs [path axis].
::
::    We need to distinguish between memoized entries and merely saved ones.
::    A memoized entry could be safely reused during another instance of
::    analysis, while the saved entry can be found given a [sock formula] pair
::    but will not be reused even if a call in an analysis matches it. It is
::    done when the function has indirect calls itself or if it has one
::    transitively through one of its callees, and the indirect call is caused
::    by the lack of knowledge in the function's subject and not by e.g. a call
::    with a formula that is produced by Nock 6. The goal is to prevent future
::    pessimization - imagine if +turn got memoized with an unknown gate as its
::    argument, then any call to +turn would produce indirect calls even if the
::    function argument is known at that particular callsite.
::
::    To save the callgraph it is sufficient to save a map:
::
::      +$  code  (map [sock formula] nomm)
::
::    , where `nomm` is a Nock formula with Nock 2 annotated with call
::    information (unit [sock formula]). Given a [sock formula] pair of the
::    entry point function, the call graph can be trivially restored by walking
::    the nomm body, descending into non-recursive callees.
::
::    In addition to the call annotations, Nomm omits Nock 8 and 9, replacing
::    them with their desugared variants.
::
::  High-level description of the algorithm
::
::    When a Nock 2 site is encountered, code usage information is recorded for
::    each function down the stack, whose subject could've contributed to the
::    Nock formula that is about to be evaluated.  For this we keep track of:
::      - global registry of functions and their code requirements:
::        want=(map @uxsite cape)
::      - subject provenance, recorded as (lest (lest *))
::
::    @uxsite label is used for two reasons: firstly, we don't yet have a sock
::    for an analyzed function, so we need some other unique identifier;
::    secondly, since the functions are going to be entered in depth-first, head
::    first order, this will simplify the condition for SCC merging which will
::    be described later.
::
::    The choice of the data structure for the subject provenance may seem
::    unusual, but it is required due to the way structural sharing works in the
::    Nock runtime.
::
::    What the subject provenance tells us, on a higher level, is "from which
::    parts of which subjects of functions deeper in the stack the noun
::    (or its subtrees) could have come".  Initially, in the sword implementation
::    of SKA this was recorded with something like:
::      +$  provenance  (tree (list [site=@uxsite axe=@]))
::
::    , where the list corresponds to the provenance union: if a noun was a
::    product of a Nock 6 branch, it could have been produced by either branch.
::
::    The problem with this approach was that the tree would be mutated on each
::    Nock 6, making ~+ and .= shortcuts impossible, making the analysis grind
::    to a halt when a product of many branches was used as a subject, like in
::    Hoon parsers.
::
::    To preserve structural sharing, the union of provenances was recorded as a
::    non-empty list of all possible provenances, and instead of eagerly
::    constructing the provenance of the product of a function from the
::    provenance of its subject, a "provenance from the input subject" was
::    simply consed on top of the outer non-empty list of provenance unions
::    from the callers of the given function.  This lazy provenance would then
::    be collapsed to propagate the subject need on Nock 2, or top-level
::    (lest *) would be composed with the next one on function return.
::
::  Loop handling
::
::    This is the most critical part of the call graph analysis.  Call graph
::    cycles are abundant in Nock: any sort of control flow loop is expressed
::    as recursion.  In the absence of recursion, figuring out code usage by
::    a function is trivial:
::
::      1. Code usage of leaf functions is nil (%| in cape terms);
::      2. Code usage of all other functions can be calculated from their Nock 2
::        calls: code usage given by the computations for formula-formula *[a c]
::        plus the code usage by the called function through the constructed
::        subject, which may have inherited something from the original
::        function's subject.
::
::    That is, in order to find the code usage of a function, we need to know
::    the code usage of its callees. But what if a function calls itself? What
::    if there is mutual recursion?
::
::    The problem is that the shape of the call graph is unknown to us; the
::    purpose of this first step **is** to reconstruct the call graph.  We can't
::    know for sure if a given Nock 2 call is a call to a function that is
::    already on the call stack: knowing so would require us to have analyzed
::    all transitive callees of that function, which would include itself.  To
::    go around the paradox we use a loop call heuristic: if the Nock 2 call
::    uses the same formula and a compatible subject as a function on the stack
::    does, we assume that what we have is a recursive call to that function:
::
::      1. We record that assumption in `cycles` data structure
::      2. The product of that recursive call is unknown.
::      3. We assume that the recursive call uses no code from the subject.
::
::    Once we analyze the entirety of the loop (formally a strongly connected
::    component of the graph, or SCC), we use the Kleene fixpoint algorithm on
::    each recorded recursive call, with two goals in mind: we want to find the
::    actual code usage mask of the recursive functions, and we want to check
::    if the assumptions still hold.  If an assumption is violated, the entirety
::    of the analysis of a given SCC has to be discarded, and the Nock 2 call
::    has to be treated as some other function call during reanalysis.  Note
::    that doing one sweep over the set of recursive calls is not enough: what
::    we need instead is the fixpoint of the sweep itself, thus we need to
::    repeat fixpoint searches in the loop until all code usage masks converge.
::    This method will yield a least fixed point of the code usages of functions
::    from the given SCC, which is guaranteed by the fact that the set of
::    (normalized) socks for a given noun forms a complete lattice with +huge:so
::    as a comparator, and it can be proven that any amount of sweeps would
::    yield code usages that are <= lfp.
::
::    Without the loop heuristic, the analysis would never terminate as we would
::    infinitely follow the recursion path in a cycle.  A similar problem is the
::    problem of reusing the work that was done in the current SCC: we don't
::    yet know the full code usage mask of a given function but we would like
::    to recognise a call to it to prevent us from reanalyzing the entire SCC
::    again and again.  A technique called "meloization" (memoization + loop) is
::    used, where the formula and the sock are compared with what was
::    accumulated so far in the SCC prior to finalization.  In the process
::    described above we would have to go over all meloization assumptions as
::    well, updating the code usage masks and checking if the assumptions still
::    hold.  The only difference is that the fixpoint search is not necessary,
::    as the code usage of a meloized function is guaranteed to not depend on
::    the code usage of a caller of a meloized function.
::
::    We have complete knowledge of an SCC only once we have visited all
::    transitive callees of the entry point of the SCC. Moreover, we do not know
::    if a given function is an entry into an SCC until we return from that
::    function, having visited all of its transitive callees.
::
::    This can lead to situations when two initially separate SCCs are learned
::    to be the same SCC. In this case these two SCCs and all SCCs between them
::    get merged: the entry point of the top-level SCC becomes the entry point
::    of the new SCC, the call assumptions are merged etc.
::
::    Since @uxsite labels are assigned in depth-first order, the condition
::    for SCC merging (or for adding a new recursive call into the latest SCC vs
::    forming a new one, which is just a special case of the same thing) is:
::    compare the index of the call target (call deeper in the stack or the
::    meloized call) to the deep-most, right-most member of the SCC, or
::    the "latch".  If the parent is >= than the latch then the SCCs are not
::    strongly connected.
::
|%
::  lazily concatenated list
::
++  deep
  |$  [m]
  $%  [%deep p=(deep m) q=(deep m)]
      [%list p=(list m)]
  ==
::
++  dive
  |*  [a=(deep) b=*]
  ^+  a
  ?-  -.a
    %list  a(p [b p.a])
    %deep  a(p $(a p.a))
  ==
::
++  roll-deep
  |*  [a=(deep) g=_=>(~ |=([* *] +<+))]
  |-  ^+  ,.+<+.g
  ?-  -.a
    %list  (roll p.a g)
    %deep  $(a q.a, +<+.g $(a p.a))
  ==
::
++  reel-deep
  |*  [a=(deep) g=_=>(~ |=([* *] +<+))]
  |-  ^+  ,.+<+.g
  ?-  -.a
    %list  (reel p.a g)
    %deep  $(a p.a, +<+.g $(a q.a))
  ==
::  mold builder from deep, cannot safely bunt
::
++  peer
  |*  a=(deep)
  $_
  ?>  ?=(%list -.a)
  i.-.p.a
::
++  flatten
  |*  a=(deep)
  ^-  (list (peer a))
  %-  zing
  =|  out=(list (list (peer a)))
  |-  ^-  (list (list (peer a)))
  ?-  -.a
    %list  [p.a out]
    %deep  $(a p.a, out $(a q.a))
  ==
::
++  jib
  |*  [m=(map) k=* v=(trap *) g=$-(* *)]
  ^+  m
  ?~  v-old=(~(get by m) k)
    (~(put by m) k $:v)
  (~(put by m) k (g u.v-old))
::  check that the formula does not crash, returning constant product
::
++  safe
  |=  fol=^
  ^-  (unit *)
  ?+  fol  ~
    [%1 p=*]       `p.fol
    [%11 @ p=^]    $(fol p.fol)
    [%11 [@ h=^] p=^]  ?~(s=(safe h.fol) ~ $(fol p.fol))
  ==
::  treat %fast hint formula
::  returns ~ on failure, [~ ~] on root registration, [~ ~ @] on child
::  registration
::
++  fast-parent
  |=  fol=^
  ^-  (unit (unit @))
  ?+  fol  ~
    [%1 %0]        `~
    [%0 p=@]       ``p.fol
    [%11 @ p=^]    $(fol p.fol)
    [%11 [@ f=^] p=^]  ?~(s=(safe f.fol) ~ $(fol p.fol))
  ==
::
+$  bell  [sub=sock fol=*]
+$  ring  [=path axe=@]
+$  nomm
  $+  nomm
  $~  [%0 0]
  $^  [nomm nomm]
  $%  [%1 p=*]
      [%2 p=nomm q=nomm info=(unit bell)]
      [%3 p=nomm]
      [%4 p=nomm]
      [%5 p=nomm q=nomm]
      [%6 p=nomm q=nomm r=nomm]
      [%7 p=nomm q=nomm]
      [%10 p=[p=@ q=nomm] q=nomm]
      [%11 p=$@(@ [p=@ q=nomm]) q=nomm body=*]  ::  body is hinted Nock formula
      [%12 p=nomm q=nomm]
      [%0 p=@]
  ==
--
::
|%
++  ska
  |%
  ::  same as $nomm but with calls to unfinalized functions
  ::
  +$  nomm-local
    $+  nomm-local
    $~  [%0 0]
    $^  [nomm-local nomm-local]
    $%  [%1 p=*]
        [%2 p=nomm-local q=nomm-local info=(unit $@(@uxsite bell))]
        [%3 p=nomm-local]
        [%4 p=nomm-local]
        [%5 p=nomm-local q=nomm-local]
        [%6 p=nomm-local q=nomm-local r=nomm-local]
        [%7 p=nomm-local q=nomm-local]
        [%10 p=[p=@ q=nomm-local] q=nomm-local]
        [%11 p=$@(@ [p=@ q=nomm-local]) q=nomm-local body=*]
        [%12 p=nomm-local q=nomm-local]
        [%0 p=@]
    ==
  ::  Type definitions
  ::
  ::  ~ : fresh noun, no provenance
  ::  @ : comes from axis
  ::  ^ : cons
  ::  Normalization requirements:
  ::    [~ ~] -> ~
  ::    does NOT normalize [2n 2n+1] -> n
  ::
  +$  spring  *
  +$  source  (lest (lest spring))
  +$  sock-anno  [=sock src=source]
  +$  meme
    $:  fol=^
        code=nomm
        less-memo=sock
        less-code=sock
        prod=sock
        map=(lest spring)
        area=(unit spot)
    ==
  ::
  +$  meal
    $:  site=@uxsite
        code=nomm-local
        capture=cape
        sub=sock-anno
        prod=sock
        map=(lest spring)
        area=(unit spot)
    ==
  ::  Long-term analysis information. Retained across instances of analysis.
  ::
  +$  long
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
    ::::  memoized entries: 
      ::
      memo=(jar ^ meme)
    ::::  saved entries:
      ::
      code=(map bell nomm)        ::  direct bell mapping
      fols=(jar ^ [=bell =nomm])  ::  lookup by formula
    ::::  memoization (as in %11 %memo) keys
      ::
      mize=(map bell *)
    ==
  ::
  +$  frond
    %-  deep
    $:  par=@uxsite
        kid=@uxsite
        par-sub=sock
        kid-sub=sock-anno
        kid-tak=(lest @uxsite)
    ==
  ::
  +$  hit
    $:  new-tak=(lest @uxsite)
        new=@uxsite
        new-sub=sock-anno
        fol-block=*
        less-block=sock
        =meal
    ==
  ::
  +$  cycle
    $:  entry=@uxsite
        latch=@uxsite
        =frond
        set=(deep @uxsite)
        melo=(jar * meal)
        hits=(deep hit)
        $=  process
        %-  deep
        $:  site=@uxsite
            sub=sock
            fol=^
            code=nomm-local
            prod=sock
            mize=(unit *)
            area=(unit spot)
            =flags
    ==  ==
  ::  Code usage information. Absence in the map == uses nothing from the
  ::  subject of that call
  ::
  +$  urge  (map @uxsite cape)
  ::  Short-term analysis information. Initialized upon the start of the
  ::  analysis, eventually discarded after the entire call graph was analyzed.
  ::
  +$  short
    $+  short-ska
    $:  long
        site-gen=@uxsite
        cycles=(list cycle)
        want=urge
        bars=@ud
        block-loop=(jug @uxsite @uxsite)
        block-melo=(set ^)
        area=(unit spot)
        finalized=(list [=bell code=nomm])
      ==
  ::  backward-flowing data in the analysis flow
  ::  loopy - part of an SCC
  ::  direct - fully direct including transitively, to be memoized
  ::  
  +$  flags  [loopy=? direct=?]
  ++  fold-flag
    |=  l=(lest flags)
    ^-  flags
    =/  out=flags  i.l
    %+  roll  t.l
    |:  [f=*flags out=out]
    [ |(loopy.f loopy.out)
      &(direct.f direct.out)
    ]
  ::  different views of the call stack
  ::
  +$  stack
    $:
      ::  list: linear stack of evalsites
      ::    
      list=(list @uxsite)
      ::  fols: search by formula
      ::
      fols=(jar * (pair sock-anno @uxsite))
      ::  set: set of evalsites on the stack
      ::
      :: set=(set @uxsite)
      areas=(map @uxsite spot)
    ==
  ::  Provenance tree logic.  The implementation of some of these functions
  ::  include performance-related heuristics
  ::
  ++  src
    |%
    ::  Check if "old" spring (one possible provenance from the subject of the 
    ::  current function) contains at least as much info as "new".
    ::  This is done because (lest spring) forms a union of possible
    ::  provenances, and if we need to add "new" to the list of old provenances,
    ::  we might not have to do that if that provenance is already recorded
    ::  in the list.
    ::
    ::  OTOH if provenance trees are too deep, then checking the trees for
    ::  duplication gets too expensive, and at that point it is best to add
    ::  that tree to the list. Hence the max-depth parameter, which was tuned
    ::  in testing
    ::  
    ++  compat
      =/  max-depth  10
      |=  [old=spring new=spring]
      !.
      ::  old contains new? yes is a guarantee, no is a guess
      ::
      =/  depf  0
      |-  ^-  ?
      ?:  =(old new)  &
      ?~  old  |
      ?~  new  &
      ?:  =(max-depth depf)
        |
      =.  depf  +(depf)
      ?@  old
        ?@  new  |
        ?&  $(old (peg old 2), new -.new)
            $(old (peg old 3), new +.new)
        ==
      ?@  new
        ?&  $(old -.old, new (peg new 2))
            $(old +.old, new (peg new 3))
        ==
      ?&  $(old -.old, new -.new)
          $(old +.old, new +.new)
      ==
    ::  Given two lists of springs and a binary function for them, apply that
    ::  function to all pairs from these lists and assemble them into a single
    ::  list, removing duplicates if requested and if possible.
    ::
    ::  Again, if the product list gets too long we don't bother to check
    ::  duplication across all members of the list, we just check the first ten.
    ::
    ++  mul-springs
      |=  [a=(lest spring) b=(lest spring) g=$-([spring spring] spring) check=?]
      ^-  (lest spring)
      =>  .(a `(list spring)`a, b `(list spring)`b)
      =-  ?~(- !! -)
      %+  roll  a
      |=  [pin-a=spring acc=(list spring)]
      %+  roll  b
      |=  [pin-b=spring acc=_acc]
      =/  pin-c  (g pin-a pin-b)
      ?:  &(check (lien (scag 10 acc) |=(spring (compat +< pin-c))))  acc
      [pin-c acc]
    ::  Map (lest spring) with a gate, removing duplicates if possible
    ::
    ++  turn-spring
      |=  [a=(lest spring) g=$-(spring spring)]
      ^-  (lest spring)
      =>  .(a `(list spring)`a)
      =-  ?~(- !! -)
      %+  roll  a
      |=  [pin-a=spring acc=(list spring)]
      =/  pin-b  (g pin-a)
      ?:  (lien acc |=(spring (compat +< pin-b)))  acc
      [pin-b acc]
    ::  Apply a mask to a spring
    ::
    ++  mask-spring
      |=  cap=cape
      |=  pin=spring
      ^-  spring
      |-  ^-  spring
      ?~  pin  ~
      ?:  ?=(%| cap)  ~
      ?:  ?=(%& cap)  pin
      ~+
      %+  cons-spring  $(cap -.cap, pin ?@(pin (peg pin 2) -.pin))
      $(cap +.cap, pin ?@(pin (peg pin 3) +.pin))
    ::  Same as above, but keep provenance if it is an atom, i.e. don't deepen
    ::  the provenance tree. Used when calculating code usage distribution maps,
    ::  where overestimating provenance for cell-case capes doesn't hurt the
    ::  semantics of the algorithm but helps the performance.
    ::
    ++  mask-spring-cut
      |=  cap=cape
      |=  pin=spring
      ^-  spring
      ?~  pin  ~
      ?:  ?=(%| cap)  ~
      ?:  ?=(%& cap)  pin
      ?@  pin  pin
      ~+
      %+  cons-spring  $(cap -.cap, pin -.pin)
      $(cap +.cap, pin +.pin)
    ::
    ++  mask
      |=  [src=source cap=cape]
      ^-  source
      :_  t.src
      (turn-spring i.src (mask-spring cap))
    ::
    ++  cons-spring
      |=  [a=spring b=spring]
      ^-  spring
      ?:  &(?=(~ a) ?=(~ b))  ~
      [a b]
    ::  Similarly to +pat:ca, pushes a spring to a non-zero axis. Think of it
    ::  as an inverse of slot
    ::
    ++  push-spring
      |=  axe=@
      |=  pin=spring
      ^-  spring
      ?~  pin  ~
      |-  ^-  spring
      ?:  =(1 axe)  pin
      ?-  (cap axe)
        %2  [$(axe (mas axe)) ~]
        %3  [~ $(axe (mas axe))]
      ==
    ::
    ++  push-spring-hed
      |=  pin=spring
      ^-  spring
      ?~  pin  ~
      [pin ~]
    ::
    ++  push-spring-tel
      |=  pin=spring
      ^-  spring
      ?~  pin  ~
      [~ pin]
    ::  There are two ways to cons two provenances: a multiplicative and an
    ::  additive. The choice comes down to using this elaborate inequality:
    ::    n + n <= n * n, n >= 2
    ::  That is, if we have two lists of provenances, each with one to two
    ::  springs, it is better to cons them multiplicatively, by consing each
    ::  spring from the head provenance with each spring from the tail
    ::  provenance.  But once the lists are big enough it is better to cons
    ::  them additively: cons each spring from head source with ~, cons ~ with
    ::  each spring from tail source, then concatenate two lists. This works
    ::  because the list represents a union of provenances, so these two are
    ::  equivalent:
    ::    ~[[a b]] == ~[[a ~] [~ b]]
    ::
    ++  cons
      |=  [a=source b=source]
      ^-  source
      :_  t.a
      =/  len-a  (lent i.a)
      =/  len-b  (lent i.b)
      =/  out=(lest spring)  (mul-springs i.a i.b cons-spring |)
      =/  len-out  (lent out)
      ?:  (lte len-out (add len-a len-b))  out
      ?:  (lte len-out 9)  out
      =-  ?~(- ~[~] -)
      ?:  =(~[~] i.a)
        ?:  =(~[~] i.b)  ~
        (turn i.b push-spring-tel)
      ?:  =(~[~] i.b)
        (turn i.a push-spring-hed)
      %+  weld
        (turn i.a push-spring-hed)
      (turn i.b push-spring-tel)
    ::
    ++  uni
      |=  [a=source b=source]
      ^-  source
      :_  t.a
      =-  ?~(- !! -)
      %+  roll  `(list spring)`i.a
      |=  [pin=spring acc=_`(list spring)`i.b]
      ?:  (lien `(list spring)`i.b |=(spring (compat +< pin)))  acc
      [pin acc]
    ::
    ++  slot-spring
      |=  ax=@
      |=  pin=spring
      ^-  spring
      ?:  =(ax 1)  pin
      ?~  pin  ~
      ?@  pin  (peg pin ax)
      ?-  (cap ax)
        %2  $(pin -.pin, ax (mas ax))
        %3  $(pin +.pin, ax (mas ax))
      ==
    ::
    ++  slot
      |=  [src=source ax=@]
      ^-  source
      :_  t.src
      (turn-spring i.src (slot-spring ax))
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
    ++  edit-spring
      |=  ax=@
      |=  [rec=spring don=spring]
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
        %2  $(don (cons-spring don p.i.tack), tack t.tack)
        %3  $(don (cons-spring p.i.tack don), tack t.tack)
      ==
    ::
    ++  edit
      |=  [rec=source ax=@ don=source]
      ^-  source
      :_  t.rec
      (mul-springs i.rec i.don (edit-spring ax) &)
    ::
    ++  uni-urge
      |=  [a=^urge b=^urge]
      ^-  ^urge
      %-  (~(uno by a) b)
      =>  ..ca  ^~
      |=  [@uxsite a=cape b=cape]
      (uni:ca a b)
    ::
    ++  compose-spring
      |=  [a=spring b=spring]
      ^-  spring
      ?~  b  ~
      |-  ^-  spring
      ?~  a  ~
      ~+
      ?@  a  ((slot-spring a) b)
      (cons-spring $(a -.a) $(a +.a))
    ::
    ++  compose
      |=  [a=(lest spring) b=(lest spring)]
      ^-  (lest spring)
      ~+ 
      (mul-springs a b compose-spring &)
    ::  Given the provenance of a noun and our interest in it,
    ::  distribute code need to the function labels.
    ::  The interest is & for a formula in a direct call, and cape from the bell
    ::  of a memoized call in memo case.
    ::
    ++  urge
      |=  [src=source cap=cape tak=(lest @uxsite)]
      ^-  ^urge
      ?:  =([~ ~] i.src)  ~
      =^  comps=(lest (lest spring))  tak
        =/  hed  i.src
        =/  tel  t.src
        |-  ^-  [(lest (lest spring)) (lest @uxsite)]
        ?~  tel  [~[hed] tak]
        =.  hed  (turn-spring hed (mask-spring-cut cap))
        ?:  ?=([~ ~] hed)  [~[hed] ~[i.tak]]
        =/  site  i.tak
        =^  r=(list (lest spring))  tak
          =/  comp  (compose hed i.tel)
          $(hed comp, tel t.tel, tak ?~(t.tak !! t.tak))
        ::
        [[hed r] [site tak]]
      ::
      =|  out=^urge
      |-  ^-  ^urge
      ?:  |(?=(%| cap) ?=([~ ~] i.comps))  out
      =/  need=cape
        =>  [comps=comps cap=cap ..urge]
        ~+
        %+  roll  `(list spring)`i.comps
        |=  [pin=spring acc=cape]
        ?~  pin  acc
        %+  uni:ca  acc
        =>  [pin=`spring`pin cap=`cape`cap ..ca]
        |-  ^-  cape
        ?~  pin  |
        ?:  ?=(%| cap)  |
        ?@  pin  (pat:ca cap pin)
        =/  [p=cape q=cape]  ?@(cap [& &] cap)
        =/  l  $(pin -.pin, cap p)
        =/  r  $(pin +.pin, cap q)
        (uni:ca l r)
      ::
      =.  out  (jib out i.tak _need |=(c=cape (uni:ca c need)))
      ?~  t.comps  out
      ?~  t.tak  !!
      $(tak t.tak, comps t.comps)
    ::
    ++  prune-spring
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
    ++  prune
      |=  [src=(list spring) cap=cape]
      ^-  cape
      %+  roll  src
      |=  [pin=spring acc=_`cape`|]
      (uni:ca acc (prune-spring pin cap))
    --
  ::
  ++  error
    |$  [m]
    %+  each  m
        ::  kid -> parent call which is not actually recursive
        ::
    $%  $:  %loop
            par=@uxsite
            kid=@uxsit
            lon=long
            par-spot=(unit spot)
            kid-spot=(unit spot)
            block-melo=(set ^)
        ==
    ::::  new -> old call which is proven to be wrong
      ::
        $:  %melo
            fol=^
            lon=long
            old-spot=(unit spot)
            new-spot=(unit spot)
            block-melo=(set ^)
        ==
    ==
  ::
  ++  mux
    |=  n=*
    ^-  @ux
    (mug n)
  ::  ignorant sock-anno
  ::
  ++  dunno
    |=  sub=sock-anno
    ^-  sock-anno
    [|+~ [~[~] t.src.sub]]
  ::
  ++  uni-melo
    |=  l=(list (jar ^ meal))
    ^-  (jar ^ (pair @ meal))
    ~+  ::  surprisingly not that important
    =>  !@(verb . ~&(>> %uni-melo-recalc .))
    ?~  l  ~
    =/  out=(jar ^ (pair @ meal))
      %-  ~(run by i.l)
      |=  l=(list meal)
      (turn l (lead 0))
    ::
    =/  c  1
    =/  rest  t.l
    |-  ^+  out
    ?~  rest  out
    =/  next=(jar ^ (pair @ meal))
      %-  ~(run by i.l)
      |=  l=(list meal)
      (turn l (lead c))
    ::
    =.  out
      %-  (~(uno by out) next)
      |=  [* ls=[(list [@ meal]) (list [@ meal])]]
      (weld ls)
    ::
    $(c +(c), rest t.rest)
  ::
  ++  weld-meal
    |=  [* ls=[(list meal) (list meal)]]
    (weld ls)
  ::
  ++  scux  ^~((cury scot %ux))
  ++  scuv  ^~((cury scot %uv))
  ::  printing core
  ::
  ++  p
    !@  ska-verb  !!
    =,  ska-verb
    |%
    ++  print
      |=  [bars=@ud tag=cord comment=tank diff=@s]
      ^+  bars
      ?.  p-bars  ((slog [%rose [~ ~ ~] tag ': ' comment ~]~) 0)
      =/  [bars-print=@ bars-return=@]
        ?+  diff  ~|(%weird-diff !!)
          %--0  [bars bars]
          %--1  [. .]:(succ bars)
          %-1   [bars ~|(%bars-underrun (dec bars))]
        ==
      ::
      %.  bars-return
      %-  slog
      :_  ~
      =/  bars=tank
        ?.  f-bars  leaf+(reap bars-print '|')
        ?:  (lte bars-print 5)  leaf+(reap bars-print '|')
        =/  num  (scow %ud bars-print)
        =/  len  (lent num)
        =?  num  (lth len 3)  (weld (reap (sub 3 len) ' ') num)
        [%rose [~ "|" "|"] leaf+num ~]
      ::
      [%rose [~ ~ ~] tag ': ' bars ' ' comment ~]
    ::
    ++  ren
      |=  pot=spot
      ^-  tank
      =/  loc=tank
        =*  l   p.q.pot
        =*  r   q.q.pot
        =/  ud  |=(a=@u (scow %ud a))
        leaf+"<[{(ud p.l)} {(ud q.l)}].[{(ud p.r)} {(ud q.r)}]>"
      ::
      ?.  p-file  loc
      [%rose [":" ~ ~] (smyt p.pot) loc ~]
    ::
    ++  step
      |=  [site=@uxsite seat=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'step' - --1)
      ^-  tank
      ?~  seat  (scux site)
      [%rose [" " ~ ~] (scux site) (ren u.seat) ~]
    ::
    ++  loop
      |=  $:  kid=@uxsite
              par=@uxsite
              kid-seat=(unit spot)
              par-area=(unit spot)
              bars=@ud
          ==
      ^+  bars
      =-  (print bars 'loop' - --0)
      ^-  tank
      ?:  |(?=(~ kid-seat) ?=(~ par-area))
        [%rose [" =?= " ~ ~] (scux kid) (scux par) ~]
      :+  %rose  ["; " ~ ~]
      :~
        [%rose [" =?= " ~ ~] ~[(scux kid) (scux par)]]
        [%rose [" =?> " ~ ~] (ren u.kid-seat) (ren u.par-area) ~]
      ==
    ::
    ++  done
      |=  [site=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'done' - -1)
      ^-  tank
      ?~  area  (scux site)
      :+  %rose  ["; " ~ ~]
      :~
        (scux site)
        [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
      ==
    ::
    ++  indi
      |=  [seat=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'indi' - --0)
      ^-  tank
      ?~  seat  ''
      (ren u.seat)
    ::
    ++  fini
      |=  [site=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'fini' - -1)
      ^-  tank
      ?~  area  (scux site)
      :+  %rose  ["; " ~ ~]
      :~
        (scux site)
        [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
      ==
    ::
    ++  ciao
      |=  [site=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'ciao' - -1)
      ^-  tank
      ?~  area  (scux site)
      :+  %rose  ["; " ~ ~]
      :~
        (scux site)
        [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
      ==
    ::
    ++  memo
      |=  [from=bell seat=(unit spot) area=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'memo' - --0)
      ^-  tank
      ?~  area
        (scux (mux from))
      :+  %rose  ["; " ~ ~]
      :~
        (scux (mux from))
        [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
      ==
    ::
    ++  melo
      |=  [here=@uxsite from=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
      ^+  bars
      =-  (print bars 'melo' - --0)
      ^-  tank
      ?~  area
        [%rose [" =?= " ~ ~] (scux here) (scux from) ~]
      :+  %rose  ["; " ~ ~]
      :~
        [%rose [" =?= " ~ ~] (scux here) (scux from) ~]
        [%rose [" =?> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
      ==
    --
  ::
  ++  try-inline
    |=  f=^
    ^-  (unit nomm-local)
    =*  try-inline  .
    ?+    f  ~
        [p=^ q=^]
      ?~  h=(try-inline p.f)  ~
      ?~  t=(try-inline q.f)  ~
      `[u.h u.t]
    ::
        [%0 @]  `f
        [%1 *]  `f
        [%2 *]  ~
    ::
        [%3 p=^]
      ?~  p=(try-inline p.f)  ~
      `[%3 u.p]
    ::
        [%4 p=^]
      ?~  p=(try-inline p.f)  ~
      `[%4 u.p]
    ::
        [%5 p=^ q=^]
      ?~  p=(try-inline p.f)  ~
      ?~  q=(try-inline q.f)  ~
      `[%5 u.p u.q]
    ::
        [%6 p=^ q=^ r=^]
      ?~  p=(try-inline p.f)  ~
      ?~  q=(try-inline q.f)  ~
      ?~  r=(try-inline r.f)  ~
      `[%6 u.p u.q u.r]
    ::
        [%7 p=^ q=^]
      ?~  p=(try-inline p.f)  ~
      ?~  q=(try-inline q.f)  ~
      `[%7 u.p u.q]
    ::
        [%8 p=^ q=^]
      $(f [%7 [p.f 0+1] q.f])
    ::
        [%9 *]
      ~
    ::
        [%10 [a=@ don=^] rec=^]
      ?~  don=(try-inline don.f)  ~
      ?~  rec=(try-inline rec.f)  ~
      `[%10 [a.f u.don] u.rec]
    ::
        [%11 a=@ p=^]
      ?~  p=(try-inline p.f)  ~
      `[%11 a.f u.p p.f]
    ::
        [%11 [a=@ p=^] q=^]
      ?~  p=(try-inline p.f)  ~
      ?~  q=(try-inline q.f)  ~
      `[%11 [a.f u.p] u.q q.f]
    ::
        [%12 p=^ q=^]
      ?~  p=(try-inline p.f)  ~
      ?~  q=(try-inline q.f)  ~
      `[%12 u.p u.q]
    ==
  ::
  ++  finalize-nomm
    |=  [m=(map @uxsite bell) n=nomm-local]
    ^-  nomm
    =/  transform  |=($@(@uxsite bell) ?^(+< +< (~(got by m) +<)))
    ~+
    ?+  -.n  n
      ^    [$(n -.n) $(n +.n)]
      %2   n(p $(n p.n), q $(n q.n), info (bind info.n transform))
      %3   n(p $(n p.n))
      %4   n(p $(n p.n))
      %5   n(p $(n p.n), q $(n q.n))
      %6   n(p $(n p.n), q $(n q.n), r $(n r.n))
      %7   n(p $(n p.n), q $(n q.n))
      %10  n(q.p $(n q.p.n), q $(n q.n))
      %12  n(p $(n p.n), q $(n q.n))
      %11  ?@  p.n  n(q $(n q.n))
           n(q.p $(n q.p.n), q $(n q.n))
    ==
  ::  Stateful analysis of [sock formula] pair. Assumes that this [sock formula]
  ::  was not encountered yet, check fols.lon before analysis
  ::
  ++  scan
    ::  default flags: not loopy, fully direct
    ::
    =*  deff  `flags`[| &]
    |=  lon=long
    =|  memoize-key-here=(unit *)   ::  our memo key
    =|  memoize-key-there=(unit *)  ::  memo key of a callee (set in %11 case)
    |=  [bus=sock fol=^]
    ^-  short
    =|  gen=short
    =.  -.gen  lon
    =|  =stack
    ::  provenance is updated by the caller
    ::  length of the provenance list must match stack depth during analysis
    ::
    =/  sub=sock-anno  [bus ~[~[1]]]
    =^  here-site  site-gen.gen    [site-gen.gen +(site-gen.gen)]
    =|  seat=(unit spot)  ::  call site
    =<  gen
    ::  Partial interpreter loop
    ::
    |-  ^-  [[sock-anno flags] gen=short]
    =*  eval-loop  $
    =|  trace=(list spot)
    ::  SCC reanalysis loop. If a speculative call to a non-finalized function
    ::  is proven to be wrong, the call is added to a respective exclusion list
    ::  and the entire SCC is reanalyzed. As a reminder, the possible speculative
    ::  calls are: recursive calls, i.e. calls to functions that are already on
    ::  the stack, and non-recursive calls to functions that are part of the
    ::  current SCC (aka "meloization" mechanism).
    ::
    |-  ^-  [[sock-anno flags] short]
    =*  redo-loop  $
    =;  res=(error [[sock-anno flags] short])
      ?-    -.res
          %&  p.res
          %|
        =>  !@  ska-verb  .
            ~&  >>>
              :-  %redo
              ?-    -.p.res
                  %loop  [par kid par-spot kid-spot]:p.res
                  %melo  [%melo fol=(mux fol.p.res) [old-spot new-spot]:p.res]
              ==
            .
        ::
        ?-    -.p.res
            %loop
          =,  p.res
          %=  redo-loop
            -.gen           lon
            block-loop.gen  (~(put ju block-loop.gen) par kid)
            block-melo.gen  (~(uni in block-melo.gen) block-melo)
          ==
        ::
            %melo
          =,  p.res
          %=  redo-loop
            -.gen           lon
            block-melo.gen  (~(put in (~(uni in block-melo.gen) block-melo)) fol)
          ==
        ==
      ==
    ^-  (error [[sock-anno flags] short])
    =.  list.stack  [here-site list.stack]
    =.  fols.stack  (~(add ja fols.stack) fol sub here-site)
    =*  fol-res  ,[code=nomm-local prod=sock-anno =flags]
    =^  [code=nomm-local prod=sock-anno =flags]  gen
      =>  !@(ska-verb . .(bars.gen (step:p here-site seat bars.gen)))
      |-  ^-  [fol-res short]
      =*  fol-loop  $
      ?+    fol  [[[%0 0] (dunno sub) deff] gen]
          [p=^ q=^]
        =^  l=fol-res  gen  fol-loop(fol p.fol)
        =^  r=fol-res  gen  fol-loop(fol q.fol)
        :_  gen
        :+  [code.l code.r]
          :-  (knit:so sock.prod.l sock.prod.r)
          (cons:src src.prod.l src.prod.r)
        (fold-flag flags.l flags.r ~)
      ::
          [%1 p=*]
        :_  gen
        [fol [&+p.fol [~[~] t.src.sub]] deff]
      ::
          [%2 p=^ q=^]
        =^  s=fol-res  gen  fol-loop(fol p.fol)
        =^  f=fol-res  gen  fol-loop(fol q.fol)
        ?.  =(& cape.sock.prod.f)
          ::  formula is not known: indirect call
          ::
          =>  !@  verb  .
              .(bars.gen (indi:p ?~(trace ~ `i.trace) bars.gen))
          ::
          :_  gen
          :+  [%2 code.s code.f ~]
            (dunno sub)
          ::  if indirect due to dynamically generated formula (fork/unknown
          ::  result) as opposed to missing data in the original subject
          ::  - don't mark as indirect
          ::  XX indirectness should also be ignored for virtual interpreter
          ::  stuff that has to be jetted
          ::
          =/  indi=?  &(?=([@ ~] i.src.prod.f) !=(~[~] i.src.prod.f))
          (fold-flag flags.s flags.f [| !indi] ~)
        ::  direct call
        ::  Firstly we need to propagate the code usage info to all our callers
        ::  as we might have used parts of their subjects as code
        ::
        =/  fol-new  data.sock.prod.f
        =/  fol-urge  (urge:src src.prod.f & ?~(list.stack !! list.stack))
        =.  want.gen  (uni-urge:src want.gen fol-urge)
        ::  if not a %11 %memo "virtual" function - try to inline
        ::
        =/  inlined=(unit nomm-local)
          ?^  memoize-key-there  ~
          ?@  fol-new  ~
          (try-inline fol-new)
        ::
        ?^  inlined
          =^  pro=fol-res  gen  fol-loop(fol ;;(^ fol-new), sub prod.s)
          ?>  =(code.pro u.inlined)
          :_  gen
          :+  [%7 code.s code.pro]
            prod.pro
          (fold-flag flags.s flags.f flags.pro ~)
        ::  XX memo, loop, melo, step
        ::
        stub
      ::
          [%3 p=^]
        =^  p=fol-res  gen  fol-loop(fol p.fol)
        :_  gen
        :+  [%3 code.p]
          (dunno sub)
        flags.p
      ::
          [%4 p=^]
        =^  p=fol-res  gen  fol-loop(fol p.fol)
        :_  gen
        :+  [%4 code.p]
          (dunno sub)
        flags.p
      ::
          [%5 p=^ q=^]
        =^  p=fol-res  gen  fol-loop(fol p.fol)
        =^  q=fol-res  gen  fol-loop(fol q.fol)
        :_  gen
        :+  [%5 code.p code.q]
          (dunno sub)
        (fold-flag flags.p flags.q ~)
      ::
          [%6 c=^ y=^ n=^]
        =^  c=fol-res  gen  fol-loop(fol c.fol)
        =^  y=fol-res  gen  fol-loop(fol y.fol)
        =^  n=fol-res  gen  fol-loop(fol n.fol)
        =/  int=sock  (purr:so sock.prod.y sock.prod.n)
        =/  uni-src=source
          =,  src
          (uni (mask src.prod.y cape.int) (mask src.prod.n cape.int))
        ::
        :_  gen
        :+  [%6 code.c code.y code.n]
          [int uni-src]
        (fold-flag flags.c flags.y flags.n ~)
      ::
          [%7 p=^ q=^]
        =^  p=fol-res  gen  fol-loop(fol p.fol)
        =^  q=fol-res  gen  fol-loop(fol q.fol, sub prod.p)
        :_  gen
        :+  [%7 code.p code.q]
          prod.q
        (fold-flag flags.p flags.q ~)
      ::
          [%8 p=^ q=^]
        fol-loop(fol [%7 [p.fol 0+1] q.fol])
      ::
          [%9 p=@ q=^]
        fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
      ::
          [%10 [a=@ don=^] rec=^]
        ?:  =(0 a.fol)  [[[%0 0] (dunno sub) deff] gen]
        =^  don=fol-res  gen  fol-loop(fol don.fol)
        =^  rec=fol-res  gen  fol-loop(fol rec.fol)
        :_  gen
        :+  [%10 [a.fol code.don] code.rec]
          :-  (darn:so sock.prod.rec a.fol sock.prod.don)
          (edit:src src.prod.rec a.fol src.prod.don)
        (fold-flag flags.rec flags.don ~)
      ::
          [%11 p=@ q=^]
        =^  q=fol-res  gen  fol-loop(fol q.fol)
        :_  gen
        :+  [%11 p.fol code.q q.fol]
          prod.q
        flags.q
      ::
          [%11 [a=@ h=^] f=^]
        =^  h=fol-res  gen  fol-loop(fol h.fol)
        =>  !@  ska-verb  .
            =*  dot  .
            =/  pot=(unit spot)
              ?.  =(%spot a.fol)  ~
              ((soft spot) data.sock.prod.h)
            ::
            ?~  pot  dot
            %_  dot
              area.gen  ?~(area.gen pot area.gen)
              trace  [u.pot trace]
            ==
        ::  on %memo hint introduce a function to be memoized
        ::
        ?:  &(?=(%memo a.fol) ?=(%& cape.sock.prod.h) ?=(^ (safe h.fol)))
          fol-loop(fol [%2 [%0 1] 1 f.fol], memoize-key-there `data.sock.prod.h)
        =^  f=fol-res  gen  fol-loop(fol f.fol)
        :-  :+  [%11 [a.fol code.h] code.f f.fol]
              prod.f
            (fold-flag flags.f flags.h ~)
        ::  treat the hint (just %fast stuff for cold state for now)
        ::
        ?+    a.fol  gen
            %fast
          =/  [clue=sock prod=sock]  [sock.prod.h sock.prod.f]
          ?.  =(& cape.clue)  ~&(>>> %fast-lost-clue gen)
          =/  clue  data.clue
          ?.  ?=([name=$@(@tas [@tas @]) dad=^ *] clue)
            ~&(>>> fast-bad-clue+clue gen)
          =/  label=cord
            ?@  name.clue  name.clue
            (rap 3 -.name.clue (scot %ud +.name.clue) ~)
          ::
          ?~  parent=(fast-parent dad.clue)  ~&(>>> fast-bad-clue+clue gen)
          ?~  u.parent
            ::  register root
            ::
            ?.  =(& cape.prod)  ~&(>>> %fast-lost-root gen)
            %=  gen
              core.jets  (~(put ju core.jets.gen) ~[label] prod)
              root.jets  (~(put ju root.jets.gen) data.prod ~[label])
            ==
          ::  register child core
          ::
          =/  axis=@  u.u.parent
          ?.  =(3 (cap axis))  ~&(>>> fast-weird-axis+axis gen)
          =/  batt  (pull:so prod 2)
          ?.  =(& cape.batt)   ~&(>>> fast-lost-batt+label gen)
          ?.  ?=(^ data.batt)  ~&(>>> fast-atom-batt+data.batt gen)
          =/  fore  (pull:so prod axis)
          =/  past=(set path)
            %-  %~  uni  in
                ::  root registrations
                ::
                ?.  =(& cape.fore)  ~
                (~(get ju root.jets.gen) data.fore)
            ::  parent core registrations
            ::
            =/  batt-fore  (pull:so fore 2)
            ?.  &(=(& cape.batt-fore) ?=(^ data.batt-fore))  ~
            (~(get ju batt.jets.gen) data.batt-fore)
          ::
          =/  past-list  ~(tap in past)
          |-  ^-  short
          =*  past-loop  $
          ?~  past-list  gen
          =/  pax=path  [label i.past-list]
          =/  socks  ~(tap in (~(get ju core.jets.gen) i.past-list))
          |-  ^-  short
          =*  sock-loop  $
          ?~  socks  past-loop(past-list t.past-list)
          ?.  (huge:so i.socks fore)  sock-loop(socks t.socks)
          =/  just-fol=sock  [[& |] data.batt ~]
          =/  template=sock  (darn:so just-fol axis i.socks)
          ::
          %=  gen
            core.jets  (~(put ju core.jets.gen) pax template)
            batt.jets  (~(put ju batt.jets.gen) data.batt pax)
          ==
        ==
      ::
          [%12 p=^ q=^]
        =^  p=fol-res  gen  fol-loop(fol p.fol)
        =^  q=fol-res  gen  fol-loop(fol q.fol)
        :_  gen
        :+    [%12 code.p code.q]
          (dunno sub)
        (fold-flag flags.p flags.q ~)
      ==
    ::  provenance of the result from the subject, i.e. subject capture
    ::
    =/  move=(lest spring)  i.src.prod
    =;  fin=(error [loopy=? gen=short])
      ?:  ?=(%| -.fin)  fin
      &+[[prod flags(loopy loopy.p.fin)] gen.p.fin]
    ::
    ?.  loopy.flags
      ::  success, not a part of a non-trivial SCC, can be finalized immediately
      ::
      :+  %&  %|
      ^-  short
      =/  code=nomm  ;;(nomm code)  ::  XX debug assert, should use unsafe cast
      =>  !@(ska-verb . .(bars.gen (done:p here-site seat area.gen bars.gen)))
      =/  want=cape  (~(gut by want.gen) here-site |)
      %-  finalize-function
      [ sock.sub  code
        fol  sock.prod
        move  want
        direct.flags
        memoize-key-here
        area.gen  gen
      ]
    ?~  cycles.gen  !!
    ?.  =(here-site entry.i.cycles.gen)
      ::  returning from a function that is not an entry point into its
      ::  non-trivial SCC
      ::  Success for now, validation is deferred until we return from the SCC
      ::  entry point
      ::
      :+  %&  %&
      ^-  short
      =>  !@(ska-verb . .(bars.gen (ciao:p here-site seat area.gen bars.gen)))
      =.  set.i.cycles.gen      (dive set.i.cycles.gen here-site)
      =.  process.i.cycles.gen
        %+  dive  process.i.cycles.gen
        [ here-site
          sock.sub
          fol
          code
          sock.prod
          memoize-key-here
          area.gen
          flags
        ]
      ::
      =.  melo.i.cycles.gen
        =/  capture=cape  (prune:src move cape.sock.prod)
        =/  =meal  [here-site code capture sub sock.prod move area.gen]
        (~(add ja melo.i.cycles.gen) fol meal)
      ::
      gen
    ::  SCC entry point: not part of some other SCC if finalized
    ::
    =-  ?:  ?=(%| -<)  -  &+[| p]
    ^-  (error short)
    =>  .(cycles.gen `(list cycle)`cycles.gen)
    =^  pop=cycle  cycles.gen  ?~(cycles.gen !! cycles.gen)
    =*  sub-pre-sweep-fix  .
    ::  fixpoint over the speculative function calls
    ::
    =/  sweep-fix=(error [m=(map @uxsite bell) gen=short])
      stub
    ::
    ?:  ?=(%| -.sweep-fix)  sweep-fix
    ::  success
    ::
    =.  gen  gen.p.sweep-fix
    =>  [m=m.p.sweep-fix sub-pre-sweep-fix]
    =>  !@(ska-verb . .(bars.gen (fini:p here-site seat area.gen bars.gen)))
    ::  finalize non-entry functions in SCC 
    ::
    =.  gen
      %+  roll-deep  process.pop
      |=  $:  $:  site=@uxsite
                  sub=sock
                  fol=^
                  code=nomm-local
                  prod=sock
                  mize=(unit *)
                  area=(unit spot)
                  =^flags
                ==
          ::
              gen=_gen
          ==
      ^-  short
      =/  want=cape  (~(gut by want.gen) site |)
      %-  finalize-function
      [ sub  (finalize-nomm m code)
        fol  prod
        *(lest spring)  want
        |
        mize  area
        gen
      ]
    ::  finalize entry point
    ::
    =/  want  (~(gut by want.gen) here-site |)
    =/  code-global  (finalize-nomm m code)
    :-  %&
    %-  finalize-function
    [ sock.sub  (finalize-nomm m code)
      fol  sock.prod
      move  want
      direct.flags
      memoize-key-here
      area.gen  gen
    ]
  ::  save function data in all appropriate tables. "move" only used if
  ::  "memoize" = %.y
  ::
  ++  finalize-function
    |=  $:  sub=sock
            code=nomm
            fol=^
            pro=sock
            move=(lest spring)
            want=cape
            memoize=?
            mize=(unit *)
            area=(unit spot)
            gen=short
        ==
    ^-  short
    =/  less-code=sock  (app:ca want sub)
    =/  =bell  [less-code fol]
    %_  gen
      mize  ?~  mize  mize.gen
            (~(put by mize.gen) bell u.mize)
    ::
      memo  ?.  memoize  memo.gen
            =/  capture=cape  (prune:src move cape.pro)
            =/  mask=cape  (uni:ca want capture)
            =/  less-memo  (app:ca mask sub)
            %+  ~(add ja memo.gen)  fol
            [fol code less-memo less-code pro move area]
    ::
      code  (~(put by code.gen) bell code)
      fols  (~(add ja fols.gen) fol [bell code])
    ==
  --
--
