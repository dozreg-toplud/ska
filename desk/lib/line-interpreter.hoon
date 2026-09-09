/+  *nock-compilation1
::
=*  stub  ~|(%stub !!)
|%
++  jet-driver-array
  |=  =ring
  ^-  (unit $-((list *) (unit *)))
  ?.  =(2 axe.ring)  ~
  =>  [=_ring ..zuse]
  ?+    path.ring  ~
      [%add %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(add a.l b.l)
  ::
      [%dec %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ ~] l)
    `(dec a.l)
  ::
      [%div %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(div a.l b.l)
  ::
      [%dvr %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(dvr a.l b.l)
  ::
      [%gte %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(gte a.l b.l)
  ::
      [%gth %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(gth a.l b.l)
  ::
      [%lte %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(lte a.l b.l)
  ::
      [%lth %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(lth a.l b.l)
  ::
      [%max %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(max a.l b.l)
  ::
      [%min %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(min a.l b.l)
  ::
      [%mod %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(mod a.l b.l)
  ::
      [%mul %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(mul a.l b.l)
  ::
      [%sub %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ b=@ ~] l)
    `(sub a.l b.l)
  ::
      [%bex %two %one %k135 ~]
    :-  ~
    |=  l=(pole *)
    ^-  (unit *)
    ?>  ?=([a=@ ~] l)
    `(bex a.l)
  ==
::
++  jet-driver-mono
  |=  =ring
  ^-  (unit $-(* (unit *)))
  ?.  =(2 axe.ring)  ~
  ?+    path.ring  ~
      [%add %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(add a.s b.s)
  ::
      [%dec %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* a=@ *] s)
    `(dec a.s)
  ::
      [%div %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(div a.s b.s)
  ::
      [%dvr %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(dvr a.s b.s)
  ::
      [%gte %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(gte a.s b.s)
  ::
      [%gth %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(gth a.s b.s)
  ::
      [%lte %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(lte a.s b.s)
  ::
      [%lth %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(lth a.s b.s)
  ::
      [%max %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(max a.s b.s)
  ::
      [%min %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(min a.s b.s)
  ::
      [%mod %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(mod a.s b.s)
  ::
      [%mul %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(mul a.s b.s)
  ::
      [%sub %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* [a=@ b=@] *] s)
    `(sub a.s b.s)
  ::
      [%bex %two %one %k135 ~]
    :-  ~
    |=  s=*
    ?>  ?=([* a=@ *] s)
    `(bex a.s)
  ==
::
++  run
  |=  $:  args=(each (list *) *)  ::  optimized/pessimized call
          =bell
          scc=(set bell)
          rev=(jug bell bell)
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
      ==
  =*  sam  +<
  ^-  (unit *)
  =/  =straight
    =*  sam  +<
    =*  con  +>
    =/  f  -.args
    =>  [=_f +.sam con]  ~+
    =/  =straight
      ~>  %bout.[0 %compile]
      ~&  %compile-start
      ?:  f
        (~(got by (compile-scc scc rev long-ska scc-map jets-hot)) bell)
      -:(compile-unary bell scc rev long-ska scc-map jets-hot)
    ::
    ~&  %optimize-start
    ~&  `@ux`(mug bell)
    ~>  %bout.[0 %optimize]
    (optimize -)
  ::
  =/  bob  (~(got by blocks.straight) 0w0)
  =/  regs=(map @uvre *)
    ?:  ?=(%| -.args)  [[0v0 p.args] ~ ~]
    =/  r=@uvre  0v0
    %-  malt
    |-  ^-  (list [@uvre *])
    ?~  p.args
      ?>  =(r n-args.straight)
      ~
    [[r i.p.args] $(p.args t.p.args, r +(r))]
  ::
  =|  params=(list *)
  |^  ^-  (unit *)
  =*  bob-loop  $
  =?  regs  .?(params)
    |-  ^+  regs
    ?~  params
      ?>  ?=(~ par.bob)
      regs
    ?>  ?=(^ par.bob)
    =.  regs  (put i.par.bob i.params)
    $(params t.params, par.bob t.par.bob)
  ::
  |-  ^-  (unit *)
  =*  body-loop  $
  ?:  ?=(^ body.bob)
    ?~  nex=(exec-op i.body.bob)  ~
    body-loop(regs u.nex, body.bob t.body.bob)
  =*  got-blocks  ~(got by blocks.straight)
  =/  fin  fin.bob
  |-  ^-  (unit *)
  =*  fin-retry  $  ::  no looping here
  ?-    -.fin
      %clq
    =/  j=jmp  ?^((get s.fin) z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get-arg))
  ::
      %eqq
    =/  j=jmp  ?:(=((get l.fin) (get r.fin)) z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get-arg))
  ::
      %brn
    =/  cond  (get s.fin)
    ?.  ?=(? cond)  ~
    =/  j=jmp  ?:(cond z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get-arg))
  ::
      %brz
    =/  j=jmp  ?:(=(0 (get s.fin)) z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get-arg))
  ::
      %hop
    bob-loop(bob (got-blocks there.t.fin), params (turn args.t.fin get-arg))
  ::
      %jmp
    =/  sam-callee
      %=  sam
        args  &+(turn v.fin get)
        bell  a.fin
        scc   (~(gut by scc-map) a.fin [a.fin ~ ~])
      ==
    ::
    (run sam-callee)
  ::
      %jmf
    ?~  j=(jet-driver-array n.fin)  fin-retry(fin [%jmp a v]:fin)
    (u.j (turn v.fin get))
  ::
      %jsp
    =/  sam-callee
      %=  sam
        args  |+(get s.fin)
        bell  a.fin
        scc   (~(gut by scc-map) a.fin [a.fin ~ ~])
      ==
    ::
    (run sam-callee)
  ::
      %jsf
    ?~  j=(jet-driver-mono n.fin)  fin-retry(fin [%jsp a s]:fin)
    (u.j (get s.fin))
  ::
      %don
    `(get s.fin)
  ::
      %bom
    ~
  ==
  ::
  ++  put
    |=  [r=@uvre n=*]
    ^+  regs
    (~(put by regs) r n)
  ::
  ++  get-arg
    |=  a=(unit @uvre)
    ^-  *
    ?~(a %value-should-be-unreachable (get u.a))
  ::
  ++  get
    |=  r=@uvre
    ^-  *
    ?^  res=(~(get by regs) r)  u.res
    ~&  >>  [%missing-reg r `@ux`(mug bell)]
    %non-init-reg
    :: !!
  ::
  ++  exec-op
    |=  op=pole
    ^-  (unit _regs)
    ?-    -.op
      %imm
    `(put d.op n.op)
  ::
      %equ
    `regs
  ::
      %mov
    `(put d.op (get s.op))
  ::
      %inc
    =/  a=*  (get s.op)
    ?^  a  ~
    `(put d.op +(a))
  ::
      %con
    `(put d.op [(get h.op) (get t.op)])
  ::
      %hed
    =/  a=*  (get s.op)
    =/  hed
      ?^  a  -.a
      ~&  >>  %missing-head
      %missing-head
    ::
    `(put d.op hed)
  ::
      %tal
    =/  a=*  (get s.op)
    =/  tal
      ?^  a  +.a
      ~&  >>  %missing-tail
      %missing-tail
    ::
    `(put d.op tal)
  ::
      %cel
    ?@  (get p.op)  ~
    `regs
  ::
      %lob
    ?.  ?=(? (get p.op))  ~
    `regs
  ::
      %hsp
    :: ~&  [%hint n.op]
    `regs
  ::
      %hse
    `regs
  ::
      %hdp
    :: ~&  [%hint n.op]
    `regs
  ::
      %hde
    `regs
  ::
      %spy
    ~|  %scry-not-yet-implemented
    !!
  ::
      %nok
    ::  XX reenter analysis (unless jetted? and/or unless %virt?)
    ::
    !!
    :: =/  sub  (get u.op)
    :: =/  fol  (get f.op)
    :: ?~  res=(mole |.(.*(sub fol)))  ~
    :: `(put d.op u.res)
  ::
      %cal
    =/  sam-callee
      %=  sam
        args  &+(turn v.op get)
        bell  a.op
        scc   (~(gut by scc-map) a.op [a.op ~ ~])
      ==
    ::
    ?~  res=(run sam-callee)  ~
    `(put d.op u.res)
  ::
      %caf
    ?~  j=(jet-driver-array n.op)  $(op [%cal a v d]:op)
    ?~  res=(u.j (turn v.op get))  ~
    `(put d.op u.res)
  ::
      %cam
    ::  no memo yet
    ::
    $(op [%cal a v d]:op)
  ::
      %csl
    =/  sam-callee
      %=  sam
        args  |+(get s.op)
        bell  a.op
        scc   (~(gut by scc-map) a.op [a.op ~ ~])
      ==
    ::
    ?~  res=(run sam-callee)  ~
    `(put d.op u.res)
  ::
      %csf
    ?~  j=(jet-driver-mono n.op)  $(op [%csl a s d]:op)
    ?~  res=(u.j (get s.op))  ~
    `(put d.op u.res)
  ::
      %csm
    $(op [%csl a s d]:op)
    ==
  --
::
++  print-straight
  |=  [prefix=tape =straight]
  |^  ^-  tape
  ~>  %bout.[0 %print-straight]
  =/  blocks=tape
    %-  zing
    %+  join  "\0a"
    %+  turn  ~(tap by blocks.straight)
    |=  [k=@uwoo v=blob]
    `tape`(weld prefix "{<k>}: {(p-blob v)}")
  ::
  %:  zing
    prefix
    (shape need.straight)
    "\0a"  prefix
    (scow %ud n-args.straight)
    "\0a"
    blocks
    ~
  ==
  ::
  ++  shape
    |=  need=need-ordered
    ^-  tape
    =;  axes=(list @)  <axes>
    =/  axe=@  1
    |-  ^-  (list @)
    ?-    -.need
        %none
      ~
    ::
        %this
      ~[axe]
    ::
        ^
      (weld $(need -.need, axe (peg axe 2)) $(need +.need, axe (peg axe 3)))
    ::
        %both
      :-  axe
      (weld $(need h.need, axe (peg axe 2)) $(need t.need, axe (peg axe 3)))
    ==
  ::
  ++  p-blob
    |=  b=blob
    ^-  tape
    %-  zing
    %+  join  "\0a"
    ^-  (list tape)
    =-  ?:  =(~ par.b)  -
        :_  -
        (zing prefix "params: " <par.b> ~)
    ::
    ^-  (list tape)
    :_  ~
    ^-  tape
    =/  body-ops=(list tape)  (turn body.b p-pole)
    %-  zing
    ?:  =(~ body-ops)
      (zing ~["\{"] ~[(p-termin fin.b) "}"] ~)
    (zing ~["\{"] (join " " body-ops) ~[" "] ~[(p-termin fin.b) "}"] ~)
  ::
  ++  print-noun
    |=  n=*
    ^-  tape
    =/  fuel=@  200
    =<  -
    |-  ^-  [tape @]
    =*  top-loop  $
    ?@  n
      =/  len  +((div (xeb n) 4))
      ?:  (gth len (mul 2 fuel))  ["..." 0]
      [(scow %ud n) (sub fuel (min fuel len))]
    ?:  (lth fuel 2)  ["..." 0]
    =<  [['[' -] +]
    =>  .(n `*`n)
    =.  fuel  (sub fuel 2)
    |-  ^-  [tape @]
    =*  cell-loop  $
    ?@  n
      =/  len  +((div (xeb n) 4))
      ?:  (gth len (mul 2 fuel))  ["...]" 0]
      ["{(scow %ud n)}]" (sub fuel (min fuel len))]
    ?:  =(0 fuel)  ["...]" 0]
    =.  fuel  (dec fuel)
    =^  h  fuel  top-loop(n -.n)
    =^  t  fuel  cell-loop(n +.n)
    ["{h} {t}" fuel]
  ::
  ++  p-pole
    |=  op=pole
    ^-  tape
    ?+    -.op  <op>
        %imm
      =/  n-tape=tape  (print-noun n.op)
      =?  n-tape  (gth (lent n-tape) 100)  "\{{(scag 100 n-tape)}...}"
      "[%imm n={n-tape} d={<d.op>}]"
    ::
        %hsp  <[%hsp n=n.op]>
        %hse  <[%hse n=n.op]>
        %hdp  <[%hdp n=n.op p=p.op]>
        %hde  <[%hde n=n.op p=p.op]>
    ::
        %cal
      <op(a `@ux`(mug a.op))>
    ::
        %caf
      <op(a `@ux`(mug a.op))>
    ::
        %cam
      <op(a `@ux`(mug a.op))>
    ::
        %csl
      <op(a `@ux`(mug a.op))>
    ::
        %csf
      <op(a `@ux`(mug a.op))>
    ::
        %csm
      <op(a `@ux`(mug a.op))>
    ==
  ::
  ++  p-termin
    |=  op=termin
    ^-  tape
    ?+    -.op  <op>
        %jmp
      <op(a `@ux`(mug a.op))>
    ::
        %jmf
      <op(a `@ux`(mug a.op))>
    ::
        %jsp
      <op(a `@ux`(mug a.op))>
    ::
        %jsf
      <op(a `@ux`(mug a.op))>
    ==
  --
--