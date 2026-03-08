::    $args-with-branches: describes argument usage by a function, with usages
::    by branches separated out in a recursive structure
::
::  This is necessary because we can't know the data usage of a %6 before we
::  know the data usage before **and** after it, otherwise we would pessimize
::  branch registerization later on
::  
++  args-with-branches
  |-
  $:
    ::  data that is guaranteed to be accessed in the codepath we are currently
    ::  in
    ::
    sure=args
    ::  data that is accessed by the branches
    ::
    ::        | sure
    ::        |
    ::        | =,  branches
    ::        | position
    ::       / \
    ::      /   \
    ::      |y n|
    ::      \   /
    ::       \ /
    ::        |  also sure
    ::
    ::  we need `position` so that we can use it to identify every Nomm 6 in the
    ::  source, so that later we can registerize the branch correctly in the
    ::  linearizer
    ::
    ::  further `args` are data usage of the subject at %6 site
    ::
    branches=(list [position=@axis sub-prov=(lest spring) y=$ n=$])
  ==
::
+$  spring  spring:source
+$  sock-prep  [=sock prov=(lest spring)]
++  dunno-prep
  |=  s=sock-prep
  ^+  s
  :: [|+~ ~[~] ?~(prov-branch.s ~ `~[~])]
  [|+~ ~[~]]
::
++  cons-prov
  |=  [a=(lest spring) b=(lest spring)]
  ^-  (lest spring)
  =/  out=(lest spring)  (mul-springs:source a b cons-spring:source |)
  =/  len-a  (lent a)
  =/  len-b  (lent b)
  =/  len-out  (lent out)
  ?:  (lte len-out (add len-a len-b))  out
  ?:  (lte len-out 9)  out
  =-  ?~(- ~[~] -)
  ?:  =(~[~] a)
    ?:  =(~[~] b)  ~
    (turn b push-spring-tel:source)
  ?:  =(~[~] b)
    (turn a push-spring-hed:source)
  %+  weld
    (turn a push-spring-hed:source)
  (turn b push-spring-tel:source)
::
:: ++  app-branch
::   |*  [g=$-((lest spring) *) a=(unit (lest spring))]
::   ^-  (unit _$:g)
::   (bind a g)
:: ::
:: ++  app-branch-2
::   |*  $:  g=$-((pair (lest spring) (lest spring)) *)
::           a=(unit (lest spring))
::           b=(unit (lest spring))
::       ==
::   ^-  (unit _$:g)
::   ?:  &(?=(^ a) ?=(^ b))  `(g u.a u.b)
::   ?>  &(?=(~ a) ?=(~ b))
::   ~
::
++  slot-prov
  |=  [prov=(lest spring) ax=@]
  ^-  (lest spring)
  (turn-spring:source prov (slot-spring:source ax) %slot-prov)
::
++  edit-prov
  |=  [ax=@ rec=(lest spring) don=(lest spring)]
  ^-  (lest spring)
  =/  check=?  (lth (mul (lent rec) (lent don)) 100)
  (mul-springs:source rec don (edit-spring:source ax) check)
::
++  uni-prov
  |=  [a=(lest spring) b=(lest spring)]
  ^-  (lest spring)
  -:(uni:source ~[a] ~[b])
::
++  mask-prov
  |=  [prov=(lest spring) cap=cape]
  ^-  (lest spring)
  -:(mask:source ~[prov] cap)
::
++  find-args
  |=  code=(map bell nomm-1)
  |=  [b=bell n=nomm-1 memo=(map bell meme-args)]
  ^+  memo
  =/  sccs=(map bell (set bell))
    ~>  %bout.[0 'find sccs']
    (find-sccs-all code)
  ::
  :: ~&  %validity-check
  :: ?>  ~>  %bout.[0 'validity check']  (valid-sccs sccs)
  =|  stack-set=(set bell)
  =/  sub=sock-prep  [bus.b ~[1] ~]
  =+  ^=  gen
      ^-  $:  memo=(map bell meme-args)
              usage=args-with-branches
              loop-calls=(map bell args)
              melo=(map bell meme-args)
          ==
      [memo [~ ~] ~ ~]
  ::
  =/  position=@axis  `@`1
  =<  memo
  |^  ^+  gen
  =*  call-loop  $
  =.  stack-set  (~(put in stack-set) b)
  ~&  [%enter (mux b)]
  =;  [branch-args=(map @axis args) gen1=_gen]
    ::  fixpoint search done, finalize
    ::  branches were collapsed by this point
    ::  and captured subject was taken into account
    ::
    =.  gen  gen1
    ?^  branches.usage.gen  !!
    =/  meme=meme-args  [sure.usage.gen branch-args]
    ?:  (~(has by sccs) b)
      =.  memo.gen  (~(put by memo.gen) b meme)
      =.  memo.gen  (~(uni by memo.gen) melo.gen)
      =.  melo.gen  ~
      gen
    =.  melo.gen  (~(put by melo.gen) b meme)
    gen
  =/  counter=@  0
  |-  ^-  [(map @axis args) _gen]
  =*  fixpoint-loop  $
  =;  [prod=sock-prep gen1=_gen]
    ::  collapse branches
    ::
    =^  branch-args=(map @axis args)  gen1
      ^-  [(map @axis args) _gen]
      =.  gen  gen1
      stub
    ::
    :-  branch-args
    ^+  gen
    ::  subject capture by the product
    ::
    =.  sure.usage.gen1  (update-loc-gen prov.prod arg+~+~)
    ::  traversal of the function body and its callees done,
    ::  check if we converged
    ::
    ?~  args-loop-mayb=(~(get by loop-calls.gen1) b)  gen1
    stub
  |-  ^-  [prod=sock-prep _gen]
  =*  nomm-loop  $
  ?-  n
      [p=^ q=*]
    =^  l  gen  nomm-loop(n p.n, position (peg position 2))
    =^  r  gen  nomm-loop(n q.n, position (peg position 3))
    :_  gen
    :-  (~(knit so sock.prod.l) sock.prod.r)
    (cons-prov prov.prod.l prov.prod.r)
  ::
      [%0 *]
    ?:  =(0 p.n)  [(dunno-prep sub) gen]
    =/  prod=sock-prep
      ?:  =(1 p.n)  sub
      :-  (~(pull so sock.sub) p.n)
      (slot-prov prov.sub p.n)
    ::
    =?  sure.usage.gen  !=(1 p.n)  (update-loc-gen prov.prod look+~+~)
    [prod gen]
  ::
      [%1 *]
    :_  gen
    [&+p.n ~[~]]
  ::
      [%2 *]
    ?~  info.n
      ?~  q.n  !!
      ?>  .=  6   =<  +  !.  =>  n  !=  p
      ?>  .=  29  =<  +  !.  =>  n  !=  u.q
      =^  s  gen  nomm-loop(n p.n, position (peg position 6))
      =^  f  gen  nomm-loop(n u.q.n, position (peg position 29))
      =.  sure.usage.gen  (update-loc-gen prov.prod.s [%arg ~ ~])
      =.  sure.usage.gen  (update-loc-gen prov.prod.f [%arg ~ ~])
      :_  gen
      (dunno-prep sub)
    =^  s  gen  nomm-loop(n p.n, position (peg position 6))
    ?>  .=  6  !.  =>  n  !=  p
    =?  gen  ?=(^ q.n)
      ?>  .=  29  =<  +  !.  =>  n  !=  u.q
      +:nomm-loop(n u.q.n)
    ::
    =^  args-callee=args  gen
      ^-  [args _gen]
      ?:  (~(has in stack-set) u.info.n)
        ?^  args-loop=(~(get by loop-calls.gen) u.info.n)  [u.args-loop gen]
        =.  loop-calls.gen  (~(put by loop-calls.gen) u.info.n ~)
        [~ gen]
      ?^  meme=(~(get by memo.gen) u.info.n)  [args.u.meme gen]
      ?^  meal=(~(get by melo.gen) u.info.n)  [args.u.meal gen]
      =.  gen
        %=  call-loop
          sub  s(prov.prod ~[1])
          n    (~(got by code) u.info.n)
          b    u.info.n
        ==
      ::
      :_  gen
      ?^  meal=(~(get by melo.gen) u.info.n)  args.u.meal
      args:(~(got by memo.gen) u.info.n)
    ::
    =.  sure.usage.gen  (update-loc-gen prov.prod.s args-callee)
    [(dunno-prep sub) gen]
  ::
      ?([%3 *] [%4 *])
    =^  p  gen  nomm-loop(n p.n, position (peg position 3))
    =.  sure.usage.gen  (update-loc-gen prov.prod.p [%arg ~ ~])
    :_  gen
    (dunno-prep sub)
  ::
      [%5 *]
    =^  p  gen  nomm-loop(n p.n, position (peg position 6))
    =^  q  gen  nomm-loop(n q.n, position (peg position 7))
    =.  sure.usage.gen  (update-loc-gen prov.prod.p [%arg ~ ~])
    =.  sure.usage.gen  (update-loc-gen prov.prod.q [%arg ~ ~])
    :_  gen
    (dunno-prep sub)
  ::
      [%6 *]
    =^  c  gen  nomm-loop(n p.n, position (peg position 6))
    =.  sure.usage.gen  (update-loc-gen prov.prod.c [%arg ~ ~])
    =/  [y=sock-prep gen-y=_gen]
      %=  nomm-loop
        n          q.n
        prov.sub   ~[1]
        position   (peg position 14)
        usage.gen  [~ ~]
      ==
    ::
    =/  [n=sock-prep gen-n=_gen]
      %=  nomm-loop
        n          r.n
        prov.sub   ~[1]
        position   (peg position 15)
        gen        gen-y(usage [~ ~])
      ==
    ::
    =/  new-branch-info     [position prov.sub usage.gen-y usage.gen-n]
    =.  branches.usage.gen  [new-branch-info branches.usage.gen]
    =.  gen  gen-n(usage usage.gen)
    =/  int=sock  (~(purr so sock.y) sock.n)
    =/  uni-prov=(lest spring)
      (uni-prov (mask-prov prov.y cape.int) (mask-prov prov.n cape.int))
    ::
    :_  gen
    [int uni-prov]
  ::
      [%7 *]
    =^  p  gen  nomm-loop(n p.n, position (peg position 6))
    nomm-loop(n q.n, sub prod.p, position (peg position 7))
  ::
      [%10 *]
    =^  rec  gen  nomm-loop(n q.n, position (peg position 7))
    =^  don  gen  nomm-loop(n q.p.n, position (peg position 13))
    ::  edit site needs to exist for safe arg disassembly
    ::
    =/  edit-site-src  (slot-prov prov.prod.rec p.p.n)
    =?  sure.usage.gen  !=(1 p.n)  (update-loc-gen edit-site-src look+~+~)
    :_  gen
    :-  (~(darn so sock.prod.rec) p.p.n sock.prod.don)
    (edit-prov p.p.n prov.prod.rec prov.prod.don)
  ::
      [%11 *]
    ?@  p.n  nomm-loop(n q.n, position (peg position 14))
    =.  gen  +:nomm-loop(n q.p.n, position (peg position 13))
    nomm-loop(n q.n, position (peg position 14))
  ::
      [%12 *]
    =^  p  gen  nomm-loop(n p.n, position (peg position 6))
    =^  q  gen  nomm-loop(n q.n, position (peg position 7))
    =.  sure.usage.gen  (update-loc-gen prov.prod.p [%arg ~ ~])
    =.  sure.usage.gen  (update-loc-gen prov.prod.q [%arg ~ ~])
    :_  gen
    (dunno-prep sub)
  ==
  ::
  ++  distribute-args
    |=  [prov=(list spring) =args]
    ^+  args
    %+  roll  prov
    |=  [pin=spring acc=^args]
    ?:  =(~ pin)  acc
    %+  uni-args  acc
    |-  ^-  ^args
    ?:  =(~ pin)   ~
    ?:  =(~ args)  ~
    ?@  pin  (push-args args pin)
    %+  uni-args
      $(pin -.pin, args (hed-args args))
    $(pin +.pin, args (tel-args args))
  ::
  ++  update-loc-gen
    |=  [prov=(list spring) =args]
    ^+  args
    ?:  =([~ ~] prov)  sure.usage.gen
    (uni-args sure.usage.gen (distribute-args prov args))
  --