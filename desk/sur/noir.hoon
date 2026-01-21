/+  *soak
:: =/  check-noir  ~
|%
::  call label for Nomm 2: indirect call or entry in global
::  code table or arm-local callsite
::
+$  call
  $~  ~
  $@(~ glob)
::
+$  glob
  $%  [%memo p=@uxmemo]
      [%site p=(pair @uvarm @uxsite)]
  ==
+$  glob-atom  @uwglob  ::  more efficient?
++  en-glob
  |=  $=  call
      $%  [%memo p=@uxmemo]
          [%site p=(pair @uvarm @uxsite)]
      ==
  ^-  glob-atom
  ?:  ?=(%memo -.call)  (lsh 0 p.call)
  .+
  %+  lsh  0
  ::  cantor pairing
  ::
  %+  add  q.p.call
  %+  rsh  0
  %+  mul  (add p.call)
  +((add p.call))
::
++  de-glob
  |=  g=glob-atom
  ^-  $%  [%memo p=@uxmemo]
          [%site p=(pair @uvarm @uxsite)]
      ==
  ?:  =(0 (end 0 g))  [%memo (rsh 0 g)]
  =.  g  (rsh 0 g)
  =/  w  p:(sqt (lsh 0 g))
  =/  t  (rsh 0 (mul w +(w)))
  =?  .  (lth g t)
    =.  w  (dec w)
    =.  t  (rsh 0 (mul w +(w)))
    .
  ::
  =/  y  (sub g t)
  =/  x  (sub w y)
  [%site x y]
::    Nomm (Nock--)
::
::  [%9 p q] => [%7 q %2 [%0 1] %0 p]
::  [%8 p q] => [%7 [p %0 1] q]  (assert p is a cell)
::
+$  nomm
  $^  [nomm nomm]                             ::  autocons
  $%  [%1 p=*]                                ::  Nock 1
    ::                                        ::  Nock 2
      [%i2 p=nomm q=nomm]                     ::    Indirect call
      [%ds2 p=nomm site=glob]                 ::    Direct, safe formula
      [%dus2 p=nomm q=nomm site=glob]         ::    Direct, unsafe formula
    ::                                        ::
      [%3 p=nomm]                             ::  Nock 3
      [%4 p=nomm]                             ::  Nock 4
      [%5 p=nomm q=nomm]                      ::  Nock 5
      [%6 p=nomm q=nomm r=nomm]               ::  Nock 6
      [%7 p=nomm q=nomm]                      ::  Nock 7
      [%10 p=[p=@ q=nomm] q=nomm]             ::  Nock 10
      [%s11 p=@ q=nomm body=*]                ::  Nock 11 (static)
      [%d11 p=[p=@ q=nomm] q=nomm body=*]     ::  Nock 11 (dynamic)
      [%12 p=nomm q=nomm]                     ::  "Nock 12"
      [%0 p=@]                                ::  Nock 0
  ==
::
+$  nomm-1
  $^  [nomm-1 nomm-1]
  $%  [%1 p=*]
      [%2 p=nomm-1 q=(unit nomm-1) info=(unit bell)]
      [%3 p=nomm-1]
      [%4 p=nomm-1]
      [%5 p=nomm-1 q=nomm-1]
      [%6 p=nomm-1 q=nomm-1 r=nomm-1]
      [%7 p=nomm-1 q=nomm-1]
      [%10 p=[p=@ q=nomm-1] q=nomm-1]
      [%11 p=$@(@ [p=@ q=nomm-1]) q=nomm-1 body=*]
      [%12 p=nomm-1 q=nomm-1]
      [%0 p=@]
  ==
::  formula registration coordinate: path + axis in the core
::
+$  ring  (pair path @)
::  memoization table entry
::
+$  meme
  $:  idx=@uxmemo
      arm=@uvarm
      site=@uxsite
      fol=*
      code=nomm
      less-memo=sock
      less-code=sock
      prod=sock
      map=(lest spring:source)
      area=(unit spot)
  ==
::  meloization table entry
::
+$  meal
  $:  site=@uxsite
      =nomm
      capture=cape
      sub=sock-anno
      prod=sock
      map=(lest spring:source)
      area=(unit spot)
  ==
::  cross-arm analysis global state
::
+$  long
  $+  long
  $:
    ::  arm index generator
    ::
    arm-gen=@uvarm
  ::::  memo index generator
    ::
    memo-gen=@uxmemo
  ::::  cold state
    ::
    $=  jets
    $:  root=(jug * path)
        core=(jug path sock)
        batt=(jug ^ path)
        ::  [sub fol]  <--> ring bidirectional mapping
        ::
        $=  cole
        $:  call=(map bell ring)
            back=(jug ring [sub=sock fol=*])
    ==  ==
  ::::  global code table for memoized entries
    ::
    $=  memo
    $:  fols=(jar * meme)
        idxs=(map @uxmemo meme)
        sits=(map [@uvarm @uxsite] meme)
    ==
  ::::  arm-local info
    ::    areas: call target spots
    ::    doors: entry points into arms: either memo hits or a 0x0 code entry
    ::    sites: finalized code entries for non-0x0 sites
    ::
    $=  arms
    $:  areas=(map @uvarm spot)
        doors=(map @uvarm [less=sock fol=* =nomm])
        sites=(map [@uvarm @uxsite] [less=sock fol=* =nomm])
    ==
  ==
::
+$  boil
  $:  cole=(map bell ring)
      code=(map bell nomm-1)
      fols=(jar * [less=sock code=nomm-1])
  ==
::
+$  bell  [bus=sock fol=*]
::  %hole - the sub-noun is not needed (but its descendants might be needed)
::  %look - test shape for presence, do not include in the args
::  %arg  - one of the arguments
::
+$  args  (tree ?(%hole %look %arg))
+$  args-locations  (map bell args)
::
++  blind
  |=  [l=args r=args]
  ^-  args
  ?:  &(?=(~ l) ?=(~ r))  ~
  ?:  &(?=(^ r) ?=(%look n.r) ?=(^ l))
    [%hole l ~]
  ?:  &(?=(^ l) ?=(%look n.l) ?=(^ r))
    [%hole ~ r]
  [%hole l r]
::
++  max-args
  |=  [a=args b=args]
  ^-  (unit ?(%arg %look))
  ~+
  ?~  a
    ?~  b  ~
    ?.  ?=(%hole n.b)  `n.b
    (max-args l.b r.b)
  ?~  b
    ?.  ?=(%hole n.a)  `n.a
    (max-args l.a r.a)
  ?:  |(?=(%arg n.a) ?=(%arg n.b))    `%arg
  ?:  &(?=(%look n.a) ?=(%look n.b))  `%look
  ?:  ?=(%look n.a)  (max-args l.b r.b)
  ?:  ?=(%look n.b)  (max-args l.a r.a)
  =/  from-a  (need (max-args l.a r.a))
  =/  from-b  (need (max-args l.b r.b))
  ?:  |(?=(%arg from-a) ?=(%arg from-b))  `%arg
  `%look
::
:: ++  subtract-cape-args-final
::   |=  [a=args c=cape]
::   ^-  args
::   =-  ?:  =(- (normalize-args -))  -
::       ~|  `*`-
::       ~|  `*`(normalize-args -)
::       !!
::   ^-  args
::   ?@  c
::     ?:  c  ~
::     ?~  a  ~
::     ?:  ?=(?(%arg %look) n.a)  a
::     ~&  [%max l.a r.a]
::     ~&  (max-args l.a r.a)
::     [(need (max-args l.a r.a)) ~ ~]
::   ?~  a  ~
::   ?-    n.a
::       %hole
::     =-  ?:  =(- (normalize-args -))  -
::         ~|  `*`-
::         ~|  `*`(normalize-args -)
::         !!
::     =/  l=args  $(a l.a, c -.c)
::     =/  r=args  $(a r.a, c +.c)
::     (blind l r)
::   ::
::       %arg  [%arg ~ ~]
::   ::
::       %look  ~
::   ==
:: ::
:: ++  subtract-cape-args
::   |=  [a=args c=cape]
::   ^-  args
::   =-  ?:  =(- (normalize-args -))  -
::       ~|  `*`-
::       ~|  `*`(normalize-args -)
::       !!
::   ^-  args
::   ?@  c
::     ?:  c  ~
::     a
::   ?~  a  ~
::   ?-    n.a
::       %hole
::     =-  ?:  =(- (normalize-args -))  -
::         ~|  `*`-
::         ~|  `*`(normalize-args -)
::         !!
::     =/  l=args  $(a l.a, c -.c)
::     =/  r=args  $(a r.a, c +.c)
::     (blind l r)
::   ::
::       %arg  [%arg ~ ~]
::   ::
::       %look  ~
::   ==
::
++  normalize-args
  |=  =args
  ^+  args
  :: args
  ?~  args  ~
  =.  l.args  $(args l.args)
  =.  r.args  $(args r.args)
  ?:  ?=(%arg n.args)
    ?:  =([~ ~] +.args)  args
    ~&  [%norm args]
    [n.args ~ ~]
  ?:  ?=(%look n.args)
    ?:  =([~ ~] +.args)  args
    ~&  [%norm args]
    [%hole +.args]
  ::  n.args == %hole
  ::
  ?:  =([~ ~] +.args)
    ~&  [%norm args]
    ~
  (blind l.args r.args)
::
::  union of data needs, used to compute a data need of
::  a sequential computation
::
::  note that if one need is more "refined" than the other
::  (e.g. [%arg ~ ~] is less refined than [%hole arg+~+~ ~])
::  then we weaken the need of the more refined computation,
::  as we do not want to have both a noun and its child to avoid
::  having to recons things
::
++  uni-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  =(a b)  a
  ?~  a  b
  ?~  b  a
  ?:  |(?=(%arg n.a) ?=(%arg n.b))  [%arg ~ ~]
  ?:  &(?=(%look n.a) ?=(%look n.b))  [%look ~ ~]
  ?:  ?=(%look n.a)  b
  ?:  ?=(%look n.b)  a
  ::  both are %hole, cons unions of head and tail
  ::
  ~+
  (blind (uni-args l.a l.b) (uni-args r.a r.b))
::
++  uni-args-loc
  |=  [a=args-locations b=args-locations]
  ^-  args-locations
  %-  (~(uno by a) b)
  |=  [bell a=args b=args]
  (uni-args a b)
::  data that is required by both branches
::
::  %arg and %look are intersected to %arg because we are going to merge
::  the residuals and unify the merged result with the intersection anyway
::
::  similar to union, we pessimize a computation with a more detailed arg
::  requirement
::
++  int-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  =(a b)  a
  ?~  a  ~
  ?~  b  ~
  ?:  |(?=(%arg n.a) ?=(%arg n.b))  [%arg ~ ~]
  ?:  &(?=(%look n.a) ?=(%look n.b))  [%look ~ ~]
  ?:  ?=(%look n.a)  b
  ?:  ?=(%look n.b)  a
  ~+
  (blind (int-args l.a l.b) (int-args r.a r.b))
::  (a - b), i.e. args in a that are not in b
::
::  residual arg requirement. used to calculate what locations
::  are required by only one branch. `b` is the requirement by previous code
::  plus the conditional formula plus the intersection of requirements
::
::  thus `b` includes the intersection of `a` with the arg requirement
::  from the other branch, so `a` and `b` are correlated, which we can leverage
::
++  dis-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  =(a b)  ~
  ?~  a  ~
  ?~  b  a
  ?:  ?=(%arg n.b)  ~
  ?:  ?=(%look n.b)
    ::  since `a` is not empty then it has to be %look
    ::  otherwise this %look would not be present in `b`
    ::  due to intersection rules
    ::
    ?>  ?=(%look n.a)
    ~
  ::  `b` is %hole, so `a` also has to be %hole or %look, otherwise
  ::  `b` would be %arg here or above
  ::
  ?<  ?=(%arg n.a)
  ?:  ?=(%look n.a)  ~
  ~+
  (blind (dis-args l.a l.b) (dis-args r.a r.b))
::  get greatest common ancestor of `a` and `b`
::
::  once we calculated what data is required by only first and only second
::  branches, we merge these requirements into one
::
::  `a` and `b` are disjoint: if `a` is %arg then `b` is ~ etc.
::
++  join-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?~  a  b
  ?~  b  a
  ::  assert disjointness
  ::
  ?>  ?=(%hole n.a)
  ?>  ?=(%hole n.b)
  ?:  &(?=(~ l.a) ?=(~ l.b))  [%hole ~ (join-args r.a r.b)]
  ?:  &(?=(~ r.a) ?=(~ r.b))  [%hole (join-args l.a l.b) ~]
  ::  requirements are both in head and tail: require the common ancestor
  ::
  :_  [~ ~]
  %-  need
  %+  max-args  [(need (max-args l.a r.a)) ~ ~]
  [(need (max-args l.b r.b)) ~ ~]
::
++  args-branches
  |=  [old=args-locations y=args-locations n=args-locations]
  ^-  args-locations
  =/  keys  (~(uni in ~(key by y)) ~(key by n))
  %-  ~(rep in keys)
  |=  [key=bell acc=_old]
  ^+  acc
  =/  args-y=args    (~(gut by y) key ~)
  =/  args-n=args    (~(gut by n) key ~)
  =/  args-old=args  (~(gut by acc) key ~)
  =/  args-sure  (uni-args args-old (int-args args-y args-n))
  =/  only-y=args  (dis-args args-y args-sure)
  =/  only-n=args  (dis-args args-n args-sure)
  =/  join  (join-args only-y only-n)
  (~(put by acc) key (uni-args args-sure join))
::
++  push-args
  |=  [a=args ax=@]
  ^-  args
  ?:  =(1 ax)  a
  ~+
  ?-  (cap ax)
    %2  [%hole $(ax (mas ax)) ~]
    %3  [%hole ~ $(ax (mas ax))]
  ==
::
++  hed-args
  |=  a=args
  ^-  args
  ?~  a  ~
  ?:  ?=(%hole n.a)  l.a
  a
::
++  tel-args
  |=  a=args
  ^-  args
  ?~  a  ~
  ?:  ?=(%hole n.a)  r.a
  a
::
++  urge-args
  |=  [src=source tak=(lest bell) =args]
  ^-  args-locations
  ?:  =([~ ~] i.src)  ~
  =^  comps=(lest (lest spring:source))  tak
    =/  hed  i.src
    =/  tel  t.src
    |-  ^-  [(lest (lest spring:source)) (lest bell)]
    ?~  tel  [~[hed] tak]
    =.  hed  (turn-spring:source hed (mask-spring-cut-args:source args) %args)
    ?:  ?=([~ ~] hed)  [~[hed] ~[i.tak]]
    =/  site  i.tak
    =^  r=(list (lest spring:source))  tak
      =/  comp  (compose:source hed i.tel)
      $(hed comp, tel t.tel, tak ?~(t.tak !! t.tak))
    ::
    [[hed r] [site tak]]
  ::
  =|  out=args-locations
  |-  ^+  out
  ?:  ?=([~ ~] i.comps)  out
  =/  a=^args
    %+  roll  `(list spring:source)`i.comps
    |=  [pin=spring:source acc=^args]
    ?~  pin  acc
    %+  uni-args  acc
    =>  .(pin `spring:source`pin)
    =-  ?:  =(- (normalize-args -))  -
        ~|  `*`-
        ~|  `*`(normalize-args -)
        !!
    |-  ^-  ^args
    ?~  pin         ~
    ?:  =(~ args)   ~
    ?@  pin  (push-args args pin)
    %+  uni-args
      $(pin -.pin, args (hed-args args))
    $(pin +.pin, args (tel-args args))
  ::
  =.  out  (jib out i.tak _a |=(b=^args (uni-args a b)))
  ?~  t.comps  out
  ?~  t.tak  !!
  $(tak t.tak, comps t.comps)
::
++  update-args-loc
  |=  [old=args-locations src=source tak=(lest bell) =args]
  ^-  args-locations
  (uni-args-loc old (urge-args +<+))
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
      process=(deep @uxsite)
      melo=(jar * meal)
      hits=(deep hit)
  ==
::
+$  blocklist  (jug @uxsite @uxsite)
::  arm-local analysis state
::
::    site: evalsite index generator
::    cycles:   stack of call graph cycles (aka natural loops aka strongly
::    connected components)
::      entry: top-most entry into a cyclical call graph
::      latch: right-most, bottom-most evalsite of the cycle
::      frond: set of parent-kid pairs of loop assumptions
::             (target of hypothetical backedge, target of the actual edge,
::              subject socks at the par/kid evalsites)
::      set: set of all vertices in the cycle (to delete from want.gen when
::           done)
::      process: same as set but without kids, melo hits and loop entry
::      melo: cycle-local meloization cache
::      hits: melo hits to validate
::
::      When new assumptions are made, we either extend an old cycle, possibly
::      merging multiple predecessor cycles, or add a new one if its
::      finalization does not depend on previous cycles. Thus, when we finish
::      analysis of a site which is recorded as an entry in `cycles`, we only
::      have to check top cycle entry and we can finalize that loop
::      independently of loops deeper in the stack.
::
::      New cycle condition for a parent-kid pair:
::        parent > latch.i.-.cycles (compare site labels)
::      If false, extend top cycle (set latch to kid, entry to
::      min(entry, parent)), then iterate over the rest of the list, 
::      merging if new cycle overlaps with the predecessor
::      (new entry <= previous latch)
::
::    want: evalsite subject requirements of non-finalized evalsites: parts of
::      the subject that are used as code
::
::    what: subject sock of an unfinalized eval
::
::    bars: number of bars for printing
::    block-loop/melo: blocklists for future guesses during retries
::    area: outermost spot in the current eval
::    locals: finalized call entries that were not memoized
::    memo-entry: potential memo hit for the entry point
::    process: map of non-finalized calls
::
+$  short
  $+  short
  $:  long
      here-arm=@uvarm
      site-gen=@uxsite
      cycles=(list cycle)
      want=urge
      bars=@ud
      block-loop=blocklist
      nope-melo=(jar * sock)
      area=(unit spot)
      locals=(list [site=@uxsite less=sock fol=* =nomm])
      memo-entry=(unit @uxmemo)
      memo-loop-entry=(list (pair @uxsite @uxmemo))
      $=  process
      %+  map  @uxsite
      $:  sub=sock
          fol=*
          =nomm
          prod=sock
          area=(unit spot)
  ==  ==
::  urge: evalsite subject requirements
::
+$  urge  (map @uxsite cape)
::  provenance tree: axes of the subject of evalsite
::
++  source
  |^  source
  ::  spring: unit of subject transformation
  ::    ~ : fresh noun
  ::    @ : comes from axis
  ::    ^ : cons
  ::    normalization: [~ ~] -> ~
  ::    doesn't normalize [2n 2n+1]
  ::
  ::  source: full provenance info
  ::    p: call stack
  ::    q: all possible unique transformations from the subject of a call to
  ::    a use site of the noun (next call site for all but last, current
  ::    use site in the formula by last), per call.
  ::
  +$  spring  *
  :: +$  spring
  ::   $~  [%null ~]
  ::   $%  [%null ~]
  ::       [%axis p=@]
  ::       [%cons p=spring q=spring]
  ::   ==
  ::
  +$  source  (lest (lest spring))
  ::
  ++  compat
    =/  max-depf  10
    |=  [old=spring new=spring]
    !.
    ::  old contains new? yes is a guarantee, no is a guess
    ::
    =/  depf  0
    |-  ^-  ?
    ?:  =(old new)  &
    ?~  old  |
    ?~  new  &
    ?:  =(max-depf depf)
      :: ~&   >>>  %depf-exceeded
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
  ::
  ++  mul-springs-1
    |=  [a=(lest spring) b=(lest spring) g=$-([spring spring] spring) check=?]
    ^-  (lest spring)
    =>  .(a `(list spring)`a, b `(list spring)`b)
    ~&  mul-springs+[(lent a) (lent b)]
    =-  ~&  out+(lent -)  -
    =-  ~?  =((lent -) 1)  out+-  -
    =-  ?~(- !! -)
    %+  roll  a
    |=  [pin-a=spring acc=(list spring)]
    %+  roll  b
    |=  [pin-b=spring acc=_acc]
    =/  pin-c
      :: ~>  %bout.[0 %mul-springs-cb]
      (g pin-a pin-b)
    ::
    :: ~>  %bout.[0 %mul-springs-append]
    ?:  &(check (lien (scag 10 acc) |=(spring (compat +< pin-c))))  acc
    [pin-c acc]
  ::
  ++  turn-spring
    |=  [a=(lest spring) g=$-(spring spring) who=@tas]
    ^-  (lest spring)
    =>  .(a `(list spring)`a)
    =-  ?~(- !! -)
    %+  roll  a
    |=  [pin-a=spring acc=(list spring)]
    =/  pin-b  (g pin-a)
    :: =-  ?:  =(%slot who)
    ::       ~>  %bout.[0 %add-turn-slot]
    ::       ~&  pin-b
    ::       $
    ::     $
    :: |.
    ?:  (lien acc |=(spring (compat +< pin-b)))  acc
    [pin-b acc]
  ::
  ++  mask-spring
    |=  cap=cape
    |=  pin=spring
    ^-  spring
    |-  ^-  spring
    ?~  pin  ~
    ?:  ?=(%| cap)  ~
    ?:  ?=(%& cap)  pin
    ~+  ::  helps with backtracking?
    %+  cons-spring  $(cap -.cap, pin ?@(pin (peg pin 2) -.pin))
    $(cap +.cap, pin ?@(pin (peg pin 3) +.pin))
  ::
  ++  mask-spring-cut
    |=  cap=cape
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?:  ?=(%| cap)  ~
    ?:  ?=(%& cap)  pin
    ?@  pin  pin
    ~+  ::  helps with backtracking?
    %+  cons-spring  $(cap -.cap, pin -.pin)
    $(cap +.cap, pin +.pin)
  ::
  ++  mask-spring-cut-args
    |=  =args
    =.  args  (normalize-args args)
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?~  args  ~
    ?:  ?=(?(%arg %look) n.args)  pin
    ?@  pin  pin
    %+  cons-spring  $(args l.args, pin -.pin)
    $(args r.args, pin +.pin)
  ::
  ++  mask
    |=  [src=source cap=cape]
    ^-  source
    :_  t.src
    (turn-spring i.src (mask-spring cap) %mask)
  ::
  ++  cons-spring
    |=  [a=spring b=spring]
    ^-  spring
    ?:  &(?=(~ a) ?=(~ b))  ~
    [a b]
    :: ?:  &(?=(%null -.a) ?=(%null -.b))  null+~
    :: [%cons a b]
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
  ::
  ++  hole-spring
    |=  ax=@
    |=  pin=spring
    ^-  spring
    ?:  =(1 ax)  ~
    ?:  =(~ pin)  ~
    =|  acc=(list (pair ?(%2 %3) spring))
    |-  ^-  spring
    ?.  |(=(1 ax) =(~ pin))
      ?-  (cap ax)
        %2  $(pin (hed pin), acc [2+(tel pin) acc], ax (mas ax))
        %3  $(pin (tel pin), acc [3+(hed pin) acc], ax (mas ax))
      ==
    =/  out=spring  ~
    |-  ^-  spring
    ?~  acc  out
    ?-  p.i.acc
      %2  $(out (cons-spring out q.i.acc), acc t.acc)
      %3  $(out (cons-spring q.i.acc out), acc t.acc)
    ==
  ::
  ++  cons
    |=  [a=source b=source]
    ^-  source
    :_  t.a
    :: ~<  %slog.[0 %cons-done]
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
    (turn-spring i.src (slot-spring ax) %slot)
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
    :: ~&  [(lent i.rec) (lent i.don) ax=ax]
    :: ~?  =(55.296 (lent i.don))  [i.rec ax]
    :: ~?  =(55.296 (lent i.don))  (spring-diff &1.i.don &3.i.don)
    :: ~?  =(55.296 (lent i.don))  (spring-diff &2.i.don &3.i.don)
    :: ~>  %bout.[0 %edit]
    :_  t.rec
    =/  check=?  (lth (mul (lent rec) (lent don)) 100)
    (mul-springs i.rec i.don (edit-spring ax) check)
  ::
  ++  hed
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 2)
    -.pin
    :: ?:  ?=(%null -.pin)  null+~
    :: ?:  ?=(%axis -.pin)  pin(p (peg p.pin 2))
    :: p.pin
  ::
  ++  tel
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 3)
    +.pin
    :: ?:  ?=(%null -.pin)  null+~
    :: ?:  ?=(%axis -.pin)  pin(p (peg p.pin 3))
    :: q.pin
  ::  unify urges
  ::
  ++  uni-urge
    |=  [a=^urge b=^urge]
    ^-  ^urge
    %-  (~(uno by a) b)
    =>  ..ca  ^~
    |=  [@uxsite a=cape b=cape]
    (~(uni ca a) b)
  ::
  ++  compose-spring
    |=  [a=spring b=spring]
    ^-  spring
    ?~  b  ~
    |-  ^-  spring
    ?~  a  ~
    ~+  ::  load-bearing
    ?@  a  ((slot-spring a) b)
    (cons-spring $(a -.a) $(a +.a))
  ::
  ++  compose
    |=  [a=(lest spring) b=(lest spring)]
    ^-  (lest spring)
    ~+  ::  helps with backtracking?
    (mul-springs a b compose-spring &)
  ::
  ++  spring-diff
    |=  [a=spring b=spring]
    ^-  ~
    =/  rev  1
    =-  ~&  >>>  "diff done a: {<`@ux`(mug a)>}, b: {<`@ux`(mug b)>}"  -
    |-  ^-  ~
    ?:  =(a b)  ~
    ?:  |(?=(~ a) ?=(~ b))
      ~&  [where=rev a=a b=b]
      ~
    ?:  |(&(?=(@ a) ?=(^ b)) &(?=(@ b) ?=(^ a)))
      ~&  [where=rev a=a b=b]
      ~
    ?:  |(?=(@ a) ?=(@ b))
      ~&  [where=rev a=a b=b]
      ~
    =+  $(a -.a, b -.b, rev (peg rev 2))
    $(a +.a, b +.b, rev (peg rev 3))
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
      =.  hed  (turn-spring hed (mask-spring-cut cap) %urge)
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
      ~+  ::  helps with backtracking?
      %+  roll  `(list spring)`i.comps
      |=  [pin=spring acc=cape]
      ?~  pin  acc
      %-  ~(uni ca acc)
      =>  [pin=`spring`pin cap=`cape`cap ..ca]
      |-  ^-  cape
      ?~  pin  |
      ?:  ?=(%| cap)  |
      ?@  pin  (~(pat ca cap) pin)
      =/  [p=cape q=cape]  ?@(cap [& &] cap)
      =/  l  $(pin -.pin, cap p)
      =/  r  $(pin +.pin, cap q)
      (~(uni ca l) r)
    ::
    =.  out  (jib out i.tak _need |=(c=cape (~(uni ca c) need)))
    ?~  t.comps  out
    ?~  t.tak  !!
    $(tak t.tak, comps t.comps)
  ::
  ++  prune-spring
    |=  [pin=spring cap=cape]
    ^-  cape
    ?:  ?=(%| cap)  |
    ?~  pin  |
    ~+  ::  load-bearing
    ?@  pin  (~(pat ca cap) pin)
    =/  [p=cape q=cape]  ?@(cap [& &] cap)
    =/  l  $(pin -.pin, cap p)
    =/  r  $(pin +.pin, cap q)
    (~(uni ca l) r)
  ::
  ++  prune
    |=  [src=(list spring) cap=cape]
    ^-  cape
    %+  roll  src
    |=  [pin=spring acc=_`cape`|]
    (~(uni ca acc) (prune-spring pin cap))
  ::
  --
::
::    axis after axis
::
::  computes the remainder of axis {b} when navigating to {a}.
::  (crashes if b is not in a)
::
++  hub
  |=  [a=@ b=@]
  :: ::  fast (not actually fast?)
  :: ::
  :: =/  out
  ::   :: ~>  %bout
  ::   =/  met-a  (met 0 a)
  ::   =/  met-b  (met 0 b)
  ::   =/  dif  (sub met-b met-a)
  ::   (con (bex dif) (end [0 dif] b))
  :: ::
  :: =-  ?>  =(out -)  out
  ?<  =(0 a)
  ?<  =(0 b)
  |-  ^-  @
  ?:  =(a 1)  b
  ?>  =((cap a) (cap b))
  $(a (mas a), b (mas b))
::  update a value or push a new one
::
++  jib
  |*  [m=(map) k=* v=(trap *) g=$-(* *)]
  ^+  m
  ?~  v-old=(~(get by m) k)
    (~(put by m) k $:v)
  (~(put by m) k (g u.v-old))
  ::
  :: |*  [m=(map) k=* v=(trap *) g=$-(* *)]
  :: ^+  m
  :: =-  ?^(- u (~(put by m) k $:v))
  :: |-  ^-  (unit _m)
  :: ?~  m  ~
  :: ?:  =(k p.n.m)
  ::   `m(q.n (g q.n.m))
  :: ?:  (gor k p.n.m)
  ::   =/  l  $(m l.m)
  ::   ?~  l  ~
  ::   `m(l u.l)
  :: =/  r  $(m r.m)
  :: ?~  r  ~
  :: `m(r u.r)
::
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
++  gave
  |^  gave
  ::
  +$  gave
    $~  [%full ~]
    $^  [gave gave]   ::  cons
    $%  [%full ~]     ::  no capture
        [%hole hole]  ::  capture backedge product
    ==
  ::
  +$  hole  [ax=@axis par=@uxsite kid=@uxsite]
  +$  guess
    $%  [%know p=sock q=hole]  ::  equality to a sock
        [%qual p=hole q=hole]  ::  equality of holes
    ==
  ::
  ++  full  full+~
  ::
  ++  norm
    |=  a=gave
    ^-  gave
    ?@  -.a  a
    =.  -.a  ~=(-.a $(a -.a))
    =.  +.a  ~=(+.a $(a +.a))
    ?:  ?=([[%full ~] %full ~] a)  full
    a
  ::
  ++  cons
    |=  [a=gave b=gave]
    ^-  gave
    ?:  &(?=(%full -.a) ?=(%full -.b))  full
    [a b]
  ::
  ++  slot
    |=  [a=gave ax=@]
    ^-  gave
    ?:  =(ax 1)  a
    ?:  ?=(%full -.a)  a
    ?@  -.a  a(ax (peg ax.a ax))
    ?-  (cap ax)
      %2  $(ax (mas ax), a -.a)
      %3  $(ax (mas ax), a +.a)
    ==
  ::
  ++  hed
    |=  a=gave
    ^-  gave
    ?:  ?=(%full -.a)  full
    ?^  -.a  -.a
    a(ax (lsh 0 ax.a))
  ::
  ++  tel
    |=  a=gave
    ^-  gave
    ?:  ?=(%full -.a)  full
    ?^  -.a  +.a
    a(ax +((lsh 0 ax.a)))
  ::
  ::  intersect socks where they don't capture loops, unify when one of them
  ::  does. Returns intersected-unified sock-gave pair and a list of assumptions
  ::  to be validated.
  ::  
  ::
  ++  int-uni
    |=  [a=[=sock gav=gave] b=[=sock gav=gave]]
    ^-  [[sock gave] (list guess)]
    =-  [[s g] (flatten dip)]
    |-  ^-  [[s=sock g=gave] dip=(deep guess)]
    ::
    =/  gav-a1  (norm gav.a)
    =/  gav-b1  (norm gav.b)
    ~?  >>>  |(!=(gav-a1 gav.a) !=(gav-b1 gav.b))  %gave-int-uni-norm
    =.  gav.a  gav-a1
    =.  gav.b  gav-b1
    ::
    ::  both don't capture loop products: intersect
    ::
    ?:  &(?=(%full -.gav.a) ?=(%full -.gav.b))
      [[(~(purr so sock.a) sock.b) full] list+~]
    ::  both capture: overwrite with the product of latest parent (does it
    ::  matter?), guess equality
    ::  
    ?:  &(?=(%hole -.gav.a) ?=(%hole -.gav.b))
      [?:((gth par.gav.a par.gav.b) a b) list+~[[%qual +.gav.a +.gav.b]]]
    ::  one doesn't capture, another captures: overwrite with known, guess
    ::  that we know the product
    ::
    ?:  &(?=(%full -.gav.a) ?=(%hole -.gav.b))
      [a list+~[[%know sock.a +.gav.b]]]
    ?:  &(?=(%full -.gav.b) ?=(%hole -.gav.a))
      [b list+~[[%know sock.b +.gav.a]]]
    ::  all other cases (at least one cons case): split sock-gaves, decend,
    ::  cons products and guesses
    ::
    =/  l-a=[sock gave]  [~(hed so sock.a) (hed gav.a)]
    =/  r-a=[sock gave]  [~(tel so sock.a) (tel gav.a)]
    =/  l-b=[sock gave]  [~(hed so sock.b) (hed gav.b)]
    =/  r-b=[sock gave]  [~(tel so sock.b) (tel gav.b)]
    =/  l  $(a l-a, b l-b)
    =/  r  $(a r-a, b r-b)
    [[(~(knit so s.l) s.r) (cons g.l g.r)] [%deep dip.l dip.r]]
  ::
  ++  edit
    |=  [rec=gave ax=@ don=gave]
    ^-  gave
    ?:  =(1 ax)  don
    =/  [p=gave q=gave]
      ::  [(slot 2 rec) (slot 3 rec)] inlined
      ::
      ?-  -.rec
        ^      rec
        %full  [full full]
        %hole  [rec(ax (lsh 0 ax.rec)) rec(ax +((lsh 0 ax.rec)))]
      ==
    ::
    %-  cons
    ?-  (cap ax)
      %2  [$(rec p, ax (mas ax)) q]
      %3  [p $(rec q, ax (mas ax))]
    ==
  --
::
+$  sock-anno  [=sock src=source]
--