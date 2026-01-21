::::  TODO
::  arity:
::    - walk the callgraph to reestablish SCCs
::      - done, but maybe double check with another approach? maybe it will also
::        be faster...
::    - use SCC knowledge to propagate finalized parts of memo cache (basically
::      robust meloization without guesses)
::  vere:
::    - experiment with full integration: replace cold state, lean on read-only
::      nature of programs
::   refactor (eventually):
::    - merge +scan, +cook and any other walks into one (maybe two?) traversals
::      - case for two traversals: the first one does more work due to
::        backtracking if loop/melo guess fails, the second one could do more 
::        heavy stuff
/-  *noir
/+  hoot
/+  playpen
::    
=*  stub  ~|(%stub !!)
=*  mure  mure:vi
=*  one  `@`1
::  Wing for compile-time branching in printing routines
::
=/  verb  ~
::  print bars?
::
=/  p-bars  &
::  fixed width of barstack?
::
=/  f-bars  |
::  print filename?
::
=/  p-file  |
::
::  first pass of the analysis
::
|%
::  ignorant sock-anno
::
++  dunno
  |=  sub=sock-anno
  ^-  sock-anno
  [|+~ [~[~] t.src.sub]]
::  check that the formula does not crash, returning constant product
::
++  safe
  |=  fol=*
  ^-  (unit *)
  ?+  fol  ~
    [%1 p=*]       `p.fol
    [%11 @ p=*]    $(fol p.fol)
    [%11 [@ h=^] p=*]  ?~(s=(safe h.fol) ~ $(fol p.fol))
  ==
::  treat %fast hint formula
::  returns ~ on failure, [~ ~] on root registration, [~ ~ @] on child
::  registration
::
++  fast-parent
  |=  fol=*
  ^-  (unit (unit @))
  ?+  fol  ~
    [%1 %0]        `~
    [%0 p=@]       ``p.fol
    [%11 @ p=*]    $(fol p.fol)
    [%11 [@ f=^] p=*]  ?~(s=(safe f.fol) ~ $(fol p.fol))
  ==
::
++  uni-melo
  |=  l=(list (jar * meal))
  ^-  (jar * (pair @ meal))
  ~+  ::  surprisingly not that important
  =>  !@(verb . ~&(>> %uni-melo-recalc .))
  ?~  l  ~
  =/  out=(jar * (pair @ meal))
    %-  ~(run by i.l)
    |=  l=(list meal)
    (turn l (lead 0))
  ::
  =/  c  1
  =/  rest  t.l
  |-  ^+  out
  ?~  rest  out
  =/  next=(jar * (pair @ meal))
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
::  print analysis stack
::
++  p
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
    |=  [from=(pair @uvarm @uxsite) seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'memo' - --0)
    ^-  tank
    ?~  area
      [%rose ["/" ~ ~] (scuv p.from) (scux q.from) ~]
    :+  %rose  ["; " ~ ~]
    :~
      [%rose ["/" ~ ~] (scuv p.from) (scux q.from) ~]
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
::  redo blocklist parent -> children
::
+$  blocklist  (jug @uxsite @uxsite)
::  a formula is loopy if it is a Nock 2 that was estimated to be a loop or
::  if the formula contains a loopy formula.
::  if eval'd formula is loopy then it cannot be finalized unless it is
::  an entry point into a loop, in which case it is finalized by checking
::  the assumptions made when analyzing the call graph cycle. entry points
::  and assumptions are recorded in cycles.gen
::
::  invariant: if a formula is loopy then cycles.gen is not empty and its
::  first element is the cycle we are currently in
::
::  direct: fully direct, to avoid memoizing evals that are too generic,
::  otherwise more specific evals would not be reanalyzed
::
+$  flags  [loopy=? direct=? crash-safe=?]
::  default flags: not loopy, fully direct, crash unsafe
::
++  deff  `flags`[| & |]
::  error: either m or parent-kid assumption pair which turned out to be false
::
++  error
  |$  [m]
  %+  each  m
  $%  [%loop p=@uxsite q=@uxsite]  ::  parent-kid
      [%melo p=* q=sock]  ::  [formula-subject pair that shouldn't be memoized]
  ==
::
+$  err-state  (error short)
::
++  add-frond
  |=  $:  new=[par=@uxsite kid=@uxsite sock sock-anno (lest @uxsite)]
          cycles=(list cycle)
      ==
  ^-  (list cycle)
  ?:  |(?=(~ cycles) (gth par.new latch.i.cycles))
    ::  push new cycle
    ::
    :_  cycles
    ^-  cycle
    [par.new kid.new [%list new ~] [%list ~[kid.new]] list+~ ~ list+~]
  ::  pop and extend top cycle
  ::
  =/  new-cycle=cycle
    :*  (min par.new entry.i.cycles)
        kid.new
        (dive frond.i.cycles new)
        (dive set.i.cycles kid.new)
        process.i.cycles
        melo.i.cycles
        hits.i.cycles
    ==
  ::
  =/  rest  t.cycles
  ::
  |-  ^-  (list cycle)
  ?:  |(?=(~ rest) (gth entry.new-cycle latch.i.rest))
    ::  push extended cycle
    ::
    [new-cycle rest]
  ::  pop and merge overlapping cycle
  ::
  =.  entry.new-cycle    (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle    [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle      [%deep set.new-cycle set.i.rest]
  =.  process.new-cycle  [%deep process.new-cycle process.i.rest]
  =.  melo.new-cycle     ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  =.  hits.new-cycle     [%deep hits.new-cycle hits.i.rest]
  ::
  $(rest t.rest)
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
::  call info
::
+$  info  [memo=(unit @uxmemo)]
::  stateful analysis of bus/fol pair
::
++  scan
  =|  gen=short
  |=  [bus=sock fol=*]
  ^-  short
  =|  =stack  ::  lexically scoped
  ::  provenance is updated by the caller
  ::  length of the provenance list must match stack depth during analysis
  ::
  =/  sub=sock-anno  [bus ~[~[1]]]
  :: =/  sub=sock-anno  [bus ~[~[axis+1]]]
  =;  res-eval-entry=short
    ::  debug asserts
    ::
    ?>  =(~ cycles.res-eval-entry)
    :: ?.  =(~ want.res-eval-entry)
    ::   ~|  ~(key by want.res-eval-entry)
    ::   !!
    ?>  =(~ process.res-eval-entry)
    res-eval-entry
  =^  here-site  site-gen.gen  [site-gen.gen +(site-gen.gen)]
  ?>  =(0x0 here-site)
  ::  check global memo cache
  ::
  =/  meme-0  (~(get ja fols.memo.gen) fol)
  |-  ^-  short
  =*  memo-loop  $
  ?^  meme-0
    =*  i  i.meme-0
    ?.  (~(huge so less-memo.i) sock.sub)  memo-loop(meme-0 t.meme-0)
    ::  memo hit for 0x0: record entry
    ::
    =>  !@  verb  .
        %=    .
            bars.gen
          (memo:p [arm.i site.i] ~ area.i bars.gen)
        ==
    gen(memo-entry `idx.i)
  =<  gen
  =|  seat=(unit spot)  ::  call site
  |-  ^-  [[sock-anno flags info] gen=short]
  =*  eval-loop  $
  =|  trace=(list spot)
  ::  retry evalsite analysis if a loop assumption was wrong
  ::
  |-  ^-  [[sock-anno flags info] short]
  =*  redo-loop  $
  =;  res=(error [[sock-anno flags info] short])
    ?-  -.res
      %&  p.res
      %|  =>  !@  verb  .
          ~&  >>>
            :-  %redo
            ?-  -.p.res
              %loop  res
              %melo  [fol=`@ux`(mug p.p.res) sock=`@ux`(mug q.p.res)]
            ==
          .
          ::
          ?-    -.p.res
              %loop
            redo-loop(block-loop.gen (~(put ju block-loop.gen) p.p.res q.p.res))
          ::
              %melo
            redo-loop(nope-melo.gen (~(add ja nope-melo.gen) p.p.res q.p.res))
          ::
    ==    ==
  ^-  (error [[sock-anno flags info] short])
  ::  enter analysis
  ::
  ::  push on the stack
  ::
  =.  list.stack  [here-site list.stack]
  =.  fols.stack  (~(add ja fols.stack) fol sub here-site)
  ::
  =*  fol-res  ,[code=nomm prod=sock-anno =flags]
  =^  [code=nomm prod=sock-anno =flags]  gen
    =>  !@(verb . .(bars.gen (step:p here-site seat bars.gen)))
    |-  ^-  [fol-res short]
    =*  fol-loop  $
    ?+    fol  [[[%0 0] (dunno sub) deff] gen]
        [p=^ q=*]
      =^  l=fol-res  gen  fol-loop(fol p.fol)
      =^  r=fol-res  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [code.l code.r]
        :-  (~(knit so sock.prod.l) sock.prod.r)
        (cons:source src.prod.l src.prod.r)
      (fold-flag flags.l flags.r ~)
    ::
        [%0 p=@]
      ?:  =(0 p.fol)  [[fol (dunno sub) deff] gen]
      =/  prod=sock-anno
        ?:  =(1 p.fol)  sub
        :-  (~(pull so sock.sub) p.fol)
        (slot:source src.sub p.fol)
      ::
      =/  f=flags  deff
      =.  crash-safe.f  (~(find so sock.sub) p.fol)
      [[fol prod f] gen]
    ::
        [%1 p=*]
      :_  gen
      [fol [&+p.fol [~[~] t.src.sub]] [| & &]]
    ::
        [%2 p=* q=*]
      =^  s=fol-res  gen  fol-loop(fol p.fol)
      =^  f=fol-res  gen  fol-loop(fol q.fol)
      ?.  =(& cape.sock.prod.f)
        ::  indirect call
        ::
        =>  !@  verb  .
            .(bars.gen (indi:p ?~(trace ~ `i.trace) bars.gen))
        :_  gen
        :+  [%i2 code.s code.f]
          (dunno sub)
        ::  if indirect due to dynamically generated formula (fork/unknown
        ::  result) as opposed to a missing data in the original subject
        ::  - don't mark as indirect
        ::
        =/  indi=?  &(?=([@ ~] i.src.sub) !=(~[~] i.src.sub))
        (fold-flag flags.s flags.f [| !indi |] ~)
      ::  direct call
      ::
      =/  emit-two
        |=  [code-s=nomm code-f=nomm =glob]
        ^-  nomm
        ::  safety condition to compile fol-fol away
        ::  XX sufficient but not necessary, smarter condition?
        ::
        ?:  ?=(?(%0 %1) -.code-f)  [%ds2 code-s glob]
        [%dus2 code-s code-f glob]
      ::
      =/  fol-new  data.sock.prod.f
      =/  fol-urge  (urge:source src.prod.f & ?~(list.stack !! list.stack))
      =.  want.gen  (uni-urge:source want.gen fol-urge)
      ::  check memo cache
      ::  XX save crash safety?
      ::
      ?^  m=(memo fol-new prod.s gen stack)
        =>  !@  verb  .
            %=    .
                bars.gen.u.m
              (memo:p from.u.m ?~(trace ~ `i.trace) area.u.m bars.gen.u.m)
            ==
        :_  gen.u.m
        :+  (emit-two code.s code.f memo+idx.u.m)
          pro.u.m
        (fold-flag flags.s flags.f deff ~)
      ::  fallible checks or analyse through: allocate new evalsite
      ::
      =^  there-site  site-gen.gen  [site-gen.gen +(site-gen.gen)]
      ::  check for loop:
      ::    Check if there is formula in the stack above us that has a
      ::    quasi-compatible sock (heuristic), if yes we guess that this is
      ::    a loop and record both socks.
      ::
      ::    When finalizing, check that the differing parts of socks are not
      ::    used as code.
      ::
      ::    If they are, the guess was wrong, redo the analysis, putting
      ::    the parent-child pair in the blocklist
      ::
      ::  stack filtered by formula
      ::
      =/  tak  (~(get ja fols.stack) fol-new)
      |-  ^-  [fol-res short]
      =*  stack-loop  $
      ?^  tak
        ::  loop heuristic:
        ::  equal formulas, not in the blocklist, quasi matching subjects
        ::
        ?:  (~(has ju block-loop.gen) q.i.tak there-site)
          stack-loop(tak t.tak)
        ?~  want=(close sock.prod.s sock.p.i.tak q.i.tak gen)
          stack-loop(tak t.tak)
        ::  loop hit
        ::
        ::  CAREFUL: ackchyually, here-site is the backedge root,
        ::  there-site/q.i.tak are the backedge targets that are assumed to be
        ::  the same (kid/parent) (but it should be totally fine to use kid as
        ::  latch, since we don't analyse through kid and all other calls that
        ::  would be greater than the latch would also be greater than the kid,
        ::  and vice versa)
        ::
        =>  !@  verb  .
            %=    .
                bars.gen
              =/  kid-seat  ?~(trace ~ `i.trace)
              =/  par-area=(unit spot)
                ?:  =(q.i.tak here-site)  area.gen
                (~(get by areas.stack) q.i.tak)
              ::
              (loop:p there-site q.i.tak kid-seat par-area bars.gen)
            ==
        =.  cycles.gen
          %+  add-frond
            [ q.i.tak
            there-site
            sock.p.i.tak
            prod.s
            ?~(list.stack !! list.stack)
            ]
          cycles.gen
        ::
        :_  gen
        :+  (emit-two code.s code.f site+[here-arm.gen q.i.tak])
          (dunno sub)
        (fold-flag flags.s flags.f [& & |] ~)
      ::  check melo cache
      ::
      ?^  m=(melo there-site fol-new prod.s gen stack)
        =>  !@  verb  .
            %=    .
                bars.gen.u.m
              %:  melo:p
                there-site
                from.u.m
                ?~(trace ~ `i.trace)
                area.u.m
                bars.gen.u.m
              ==
            ==
        :_  gen.u.m
        :+  (emit-two code.s code.f site+[here-arm.gen from.u.m])
          pro.u.m
        (fold-flag flags.s flags.f [& & |] ~)
      ::  non-loop case: analyse through
      ::
      =/  area-stash  area.gen
      =/  need-call=cape  (prune:source i.src.prod.s cape.sock.prod.s)
      =^  [pro=sock-anno =flags =info]  gen
        %=  eval-loop
          sub          prod.s(src [~[1] src.prod.s])
          fol          fol-new
          here-site    there-site
          seat         ?~(trace ~ `i.trace)
          area.gen     ~
          areas.stack  ?~  area.gen  areas.stack
                       (~(put by areas.stack) here-site u.area.gen)
        ==
      ::
      =/  code=nomm
        %^  emit-two  code.s  code.f 
        ?^  memo.info
          ::  the call got memoized
          ::
          memo+u.memo.info
        site+[here-arm.gen there-site]
      ::
      :_  gen(area area-stash)
      ^-  fol-res
      :+  code
        ?~  t.src.pro  !!
        %=  pro
          t.src  t.t.src.pro
          i.src  (compose:source i.src.pro i.t.src.pro)
        ==
      (fold-flag flags flags.s flags.f ~)
    ::
        [%3 p=*]
      =^  p=fol-res  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%3 code.p]
        (dunno sub)
      flags.p
    ::
        [%4 p=*]
      =^  p=fol-res  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%4 code.p]
        (dunno sub)
      flags.p(crash-safe |)
    ::
        [%5 p=* q=*]
      =^  p=fol-res  gen  fol-loop(fol p.fol)
      =^  q=fol-res  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%5 code.p code.q]
        (dunno sub)
      (fold-flag flags.p flags.q ~)
    ::
        [%6 c=* y=* n=*]
      =^  c=fol-res  gen  fol-loop(fol c.fol)
      =^  y=fol-res  gen  fol-loop(fol y.fol)
      =^  n=fol-res  gen  fol-loop(fol n.fol)
      =/  int=sock  (~(purr so sock.prod.y) sock.prod.n)
      =/  uni-src=source
        =,  source
        (uni (mask src.prod.y cape.int) (mask src.prod.n cape.int))
      ::
      :_  gen
      :+  [%6 code.c code.y code.n]
        [int uni-src]
      (fold-flag flags.c flags.y flags.n deff ~)
    ::
        [%7 p=* q=*]
      =^  p=fol-res  gen  fol-loop(fol p.fol)
      =^  q=fol-res  gen  fol-loop(fol q.fol, sub prod.p)
      :_  gen
      :+  [%7 code.p code.q]
        prod.q
      (fold-flag flags.p flags.q ~)
    ::
        [%8 p=* q=*]
      fol-loop(fol [%7 [?@(p.fol 0+0 p.fol) 0+1] q.fol])
    ::
        [%9 p=@ q=*]
      fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
    ::
        [%10 [a=@ don=*] rec=*]
      ?:  =(0 a.fol)  [[[%0 0] (dunno sub) deff] gen]
      =^  don=fol-res  gen  fol-loop(fol don.fol)
      =^  rec=fol-res  gen  fol-loop(fol rec.fol)
      :_  gen
      :+  [%10 [a.fol code.don] code.rec]
        :-  (~(darn so sock.prod.rec) a.fol sock.prod.don)
        (edit:source src.prod.rec a.fol src.prod.don)
      =/  f=flags  (fold-flag flags.rec flags.don ~)
      f(crash-safe &(crash-safe.f (~(find so sock.prod.rec) a.fol)))
    ::
        [%11 p=@ q=^]
      =^  q=fol-res  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%s11 p.fol code.q q.fol]
        prod.q
      flags.q
    ::
        [%11 [a=@ h=^] f=^]
      =^  h=fol-res  gen  fol-loop(fol h.fol)
      =>  !@  verb  .
          =/  pot=(unit spot)
            ?.  =(%spot a.fol)  ~
            ((soft spot) data.sock.prod.h)
          ::
          ?~  pot  +
          %_  +
            area.gen  ?~(area.gen pot area.gen)
            trace  [u.pot trace]
          ==
      =^  f=fol-res  gen  fol-loop(fol f.fol)
      :_  (hint a.fol prod.h prod.f gen)
      :+  [%d11 [a.fol code.h] code.f f.fol]
        prod.f
      (fold-flag flags.f flags.h ~)
    ::
        [%12 p=^ q=^]
      =^  p=fol-res  gen  fol-loop(fol p.fol)
      =^  q=fol-res  gen  fol-loop(fol q.fol)
      :_  gen
      :+    [%12 code.p code.q]
        (dunno sub)
      (fold-flag flags.p flags.q deff ~)
    ==
  ::
  =/  move=(lest spring:source)  i.src.prod
  =/  capture=cape  (prune:source move cape.sock.prod)
  ::
  =;  fin=(error [loopy=? =info gen=short])
    ?:  ?=(%| -.fin)  fin
    &+[[prod flags(loopy loopy.p.fin) info.p.fin] gen.p.fin]
  ?.  loopy.flags
    ::  success, non-loopy
    ::
    :+  %&  %|
    ::  finalize simple
    ::
    ^-  [info short]
    =>  !@(verb . .(bars.gen (done:p here-site seat area.gen bars.gen)))
    =/  mayb-site=(unit cape)  (~(get by want.gen) here-site)
    =/  want-site=cape  ?~(mayb-site | u.mayb-site)
    ::  minified subject for codegen
    ::
    =/  less-code=sock  (~(app ca want-site) sock.sub)
    ::  we start off with more knowledge in the subject and mask down, 
    ::  so the intersection of want-site and cape.sock.sub should be exactly
    ::  equal to want-site?
    ::
    :: ?.  =(want-site cape.less-code)
    ::   ~_  'cape.less-code < want-site'
    ::   ~|  cape.less-code
    ::   ~|  want-site
    ::   !!
    ::  memoize globally or save locally
    ::
    =^  =info  gen
      ?.  direct.flags  `gen(locals [[here-site less-code fol code] locals.gen])
      =^  idx  memo-gen.gen  [memo-gen.gen +(memo-gen.gen)]
      =/  mask=cape  (~(uni ca want-site) capture)
      =/  less-memo  (~(app ca mask) sock.sub)
      :: ?.  =(mask cape.less-memo)
      ::   ~_  'cape.less-memo < mask'
      ::   ~|  cape.less-memo
      ::   ~|  mask
      ::   !!
      =/  =meme
        :^  idx  here-arm.gen  here-site
        [fol code less-memo less-code sock.prod move area.gen]
      ::
      =.  fols.memo.gen  (~(add ja fols.memo.gen) fol meme)
      =.  idxs.memo.gen  (~(put by idxs.memo.gen) idx meme)
      =.  sits.memo.gen  (~(put by sits.memo.gen) [here-arm.gen here-site] meme)
      [`idx gen]
    ::
    :: =?  want.gen  ?=(^ mayb-site)  (~(del by want.gen) here-site)
    [info gen]
  ?~  cycles.gen  !!
  ?.  =(here-site entry.i.cycles.gen)
    ::  success, loopy
    ::
    :+  %&  %&
    ::  return without finalizing
    ::
    ^-  [info short]
    ::  never memoized
    ::
    :-  ~
    ^-  short
    =>  !@(verb . .(bars.gen (ciao:p here-site seat area.gen bars.gen)))
    =.  set.i.cycles.gen      (dive set.i.cycles.gen here-site)
    =.  process.i.cycles.gen  (dive process.i.cycles.gen here-site)
    =.  melo.i.cycles.gen
      %+  ~(add ja melo.i.cycles.gen)  fol
      :*  here-site
          code
          capture
          sub
          sock.prod
          move
          area.gen
      ==
    ::
    =.  process.gen
      %+  ~(put by process.gen)  here-site
      [sock.sub fol code sock.prod area.gen]
    ::
    gen
  ::  cycle entry not loopy if finalized
  ::
  =-  ?:  ?=(%| -<)  -  &+[| p]
  ::  attempt to finalize cycle entry
  ::
  ^-  (error (pair info short))
  =>  .(cycles.gen `(list cycle)`cycles.gen)
  =^  pop=cycle  cycles.gen  ?~(cycles.gen !! cycles.gen)
  ::  validate fronds, expanding wants
  ::
  =/  err-gen=err-state
    %+  reel-deep  frond.pop
    |:  :-  ^*
            $:  par=@uxsite
                kid=@uxsite
                par-sub=sock
                kid-sub=sock-anno
                kid-tak=(lest @uxsite)
            ==
        err-gen=`err-state`&+gen
    ^+  err-gen
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =^  par-final=sock  gen
      =/  par-want-1=cape  (~(gut by want.gen) par |)
      =/  par-masked-1=sock  (~(app ca par-want-1) par-sub)
      |-  ^-  [sock short]
      =/  kid-sub-urge  (urge:source src.kid-sub cape.par-masked-1 kid-tak)
      =.  want.gen  (uni-urge:source want.gen kid-sub-urge)
      =/  par-want-2=cape  (~(gut by want.gen) par |)
      =/  par-masked-2=sock  (~(app ca par-want-2) par-sub)
      ?:  =(cape.par-masked-1 cape.par-masked-2)
        [par-masked-1 gen]
      =>  !@(verb . ~&(>> %fixpoint-loop .))
      $(par-masked-1 par-masked-2)
    ::
    ?.  (~(huge so par-final) sock.kid-sub)  |+[%loop par kid]
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  ::  remove err-gen
  ::
  =>  +
  ::  validate melo hits, expanding what.gen
  ::
  =/  err-gen=err-state
    %+  reel-deep  hits.pop
    |:  :-  ^*  $:  new-tak=(lest @uxsite)
                    new=@uxsite
                    new-sub=sock-anno
                    fol-block=*
                    less-block=sock
                    old=@uxsite
                    code=nomm
                    cape  ::  melo hit validation does not require capture
                    old-sub=sock-anno
                    *
                ==
        err-gen=`err-state`&+gen
    ^-  err-state
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =/  old-want  (~(gut by want.gen) old |)
    =.  want.gen
      (uni-urge:source want.gen (urge:source src.new-sub old-want new-tak))
    ::
    =/  old-less  (~(app ca old-want) sock.old-sub)
    ?.  (~(huge so old-less) sock.new-sub)  |+[%melo fol-block less-block]
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  =>  +
  =>  !@(verb . .(bars.gen (fini:p here-site seat area.gen bars.gen)))
  ::
  ::  finalize in-process sites
  ::
  =.  gen
    %+  roll-deep  process.pop
    |:  [site=*@uxsite gen=gen]
    ^-  short
    =/  proc  (~(got by process.gen) site)
    =/  want-site=cape  (~(gut by want.gen) site |)
    =/  less-code=sock  (~(app ca want-site) sub.proc)
    :: ?.  =(want-site cape.less-code)
    ::   ~_  'cape.less-code < want-site'
    ::   ~|  cape.less-code
    ::   ~|  want-site
    ::   !!
    =.  locals.gen  [[site less-code fol.proc nomm.proc] locals.gen]
    =.  process.gen  (~(del by process.gen) site)
    gen
  ::  memoize or save loop entry point
  ::
  =^  =info  gen
    =/  want-site  (~(gut by want.gen) here-site |)
    =/  less-code=sock  (~(app ca want-site) sock.sub)
    :: ?.  =(want-site cape.less-code)
    ::   ~_  'cape.less-code < want-site'
    ::   ~|  cape.less-code
    ::   ~|  want-site
    ::   !!
    ?.  direct.flags  `gen(locals [[here-site less-code fol code] locals.gen])
    =^  idx  memo-gen.gen  [memo-gen.gen +(memo-gen.gen)]
    =.  memo-loop-entry.gen  [[here-site idx] memo-loop-entry.gen]
    =/  memo-mask=cape  (~(uni ca want-site) capture)
    =/  memo-less  (~(app ca memo-mask) sock.sub)
    :: ?.  =(memo-mask cape.memo-less)
    ::   ~_  'cape.less < mask'
    ::   ~|  cape.memo-less
    ::   ~|  memo-mask
    ::   !!
    =/  meme
      :^  idx  here-arm.gen  here-site
      [fol code memo-less less-code sock.prod move area.gen]
    ::
    =.  fols.memo.gen  (~(add ja fols.memo.gen) fol meme)
    =.  idxs.memo.gen  (~(put by idxs.memo.gen) idx meme)
    =.  sits.memo.gen  (~(put by sits.memo.gen) [here-arm.gen here-site] meme)
    [`idx gen]
  ::
  =.  set.pop  (dive set.pop here-site)
  :: =.  gen
  ::   %+  roll-deep  set.pop
  ::   |:  [v=*@uxsite gen=gen]
  ::   =.  want.gen  (~(del by want.gen) v)
  ::   gen
  ::
  &+[info gen]
::  given that b > a, for each axis that used to be %.n in a and became not that
::  in b, what subaxes are set to %.y?
::
++  dif-ca
  |=  [a=cape b=cape]
  ^-  (list (trel @ @ (lest @)))
  =/  rev  1
  |-  ^-  (list (trel @ @ (lest @)))
  ?:  ?=(%& a)  ~
  ?:  ?=(%| a)
    ?~  yea=~(yea ca b)  ~
    ~[[(xeb rev) rev yea]]
  %:  weld
    $(a -.a, b ?@(b b -.b), rev (peg rev 2))
    $(a +.a, b ?@(b b +.b), rev (peg rev 3))
  ==
::  (~(huge so a) b) failed, what are the offending subsocks?
::
++  dif-so
  |=  [a=sock b=sock]
  ^-  (list (pair @ (lest (pair @ ?(%lost %data)))))
  =*  res  ,(list (pair @ (lest (pair @ ?(%lost %data)))))
  =/  rev  1
  |-  ^-  res
  ?:  |(?=(^ cape.a) ?=(^ cape.b))
    %:  weld
      $(a ~(hed so a), b ~(hed so b), rev (peg rev 2))
      $(a ~(tel so a), b ~(tel so b), rev (peg rev 3))
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
++  max-xeb-ax
  |=  n=*
  ^-  @
  =/  rev  1
  |-  ^-  @
  ?@  n  (xeb rev)
  (max $(n -.n, rev (peg rev 2)) $(n +.n, rev (peg rev 3)))
::
++  memo
  |=  [fol=* sub=sock-anno gen=short =stack]
  ^-  %-  unit
      $:  idx=@uxmemo
          from=[@uvarm @uxsite]
          area=(unit spot)
          pro=sock-anno
          gen=short
      ==
  =/  meme  (~(get ja fols.memo.gen) fol)
  |-
  ?~  meme  ~
  =*  i  i.meme
  ?.  (~(huge so less-memo.i) sock.sub)  $(meme t.meme)
  ::  memo hit: propagate subject wants
  :: 
  =/  sub-urge
    (urge:source src.sub cape.less-code.i ?~(list.stack !! list.stack))
  ::
  =.  want.gen  (uni-urge:source want.gen sub-urge)
  =/  src  src.sub(i (compose:source map.i i.src.sub))
  `[idx.i [arm.i site.i] area.i [prod.i src] gen]
::
++  melo
  |=  $:  site=@uxsite
          fol=*
          sub=sock-anno
          gen=short
          =stack
      ==
  ^-  (unit [from=@uxsite area=(unit spot) pro=sock-anno gen=short])
  ?:  =(~ cycles.gen)  ~
  =/  bads=(list sock)  (~(get ja nope-melo.gen) fol)
  =/  any-bad=?  (lien bads |=(bad=sock (~(huge so bad) sock.sub)))
  ?:  any-bad  ~
  =*  res  ,(unit [out=[@uxsite (unit spot) sock-anno gen=short] =hit depth=@])
  =/  =res
    =/  melo-dep  (uni-melo (turn cycles.gen |=(cycle melo)))
    =/  mele  (~(get ja melo-dep) fol)
    |-  ^-  res
    ?~  mele  ~
    =*  i  q.i.mele
    =/  want-site=cape  (~(gut by want.gen) site.i |)
    =/  mask=cape  (~(uni ca want-site) capture.i)
    =/  less  (~(app ca mask) sock.sub.i)
    ?.  (~(huge so less) sock.sub)  $(mele t.mele)
    =/  src  src.sub(i (compose:source map.i i.src.sub))
    =/  tak  ?~(list.stack !! list.stack)
    `[[site.i area.i [prod.i src] gen] [tak site sub fol less q.i.mele] p.i.mele]
  ::
  ::
  ?~  res  ~
  ::  top melo hit: no merging necessary
  ::
  ?:  =(0 depth.u.res)
    ?~  cycles.gen.out.u.res  !!
    =*  i   i.cycles.gen.out.u.res
    =.  hits.i     (dive hits.i hit.u.res)
    =.  set.i      (dive set.i site)
    =.  latch.i    site
    `out.u.res
  =/  depth  depth.u.res
  =/  gen  gen.out.u.res
  =/  new-cycle  ,.-.cycles.gen
  =/  rest  ,.+.cycles.gen
  |-
  ?:  =(0 depth)
    =.  hits.new-cycle     (dive hits.new-cycle hit.u.res)
    =.  set.new-cycle      (dive set.new-cycle site)
    =.  latch.new-cycle    site
    =.  cycles.gen  [new-cycle rest]
    `out.u.res(gen gen)
  ?~  rest  !!
  =.  entry.new-cycle    (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle    [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle      [%deep set.new-cycle set.i.rest]
  =.  process.new-cycle  [%deep process.new-cycle process.i.rest]
  =.  melo.new-cycle     ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  =.  hits.new-cycle     [%deep hits.new-cycle hits.i.rest]
  $(rest t.rest, depth (dec depth))
::  given kid and parent subject socks and parent evalsite label, check if
::  the kid sock is compatible with parent for a loop call. heuristic.
::  returns code usage cape if compatible
::
++  close
  |=  [kid-sub=sock par-sub=sock par-site=@uxsite gen=short]
  ^-  (unit cape)
  =/  par-want=cape  (~(gut by want.gen) par-site |)
  =/  par-masked=sock  (~(app ca par-want) par-sub)
  ?.  (~(huge so par-masked) kid-sub)  ~
  `par-want
::  fold flags of children expressions
::
++  fold-flag
  |=  l=(lest flags)
  ^-  flags
  =/  out=flags  i.l
  %+  roll  t.l
  |:  [f=*flags out=out]
  [ |(loopy.f loopy.out)
    &(direct.f direct.out)
    &(crash-safe.f crash-safe.out)
  ]
::
++  hint
  |=  [tag=@ hint=sock-anno result=sock-anno gen=short]
  ^-  short
  ?+    tag  gen
      %fast
    ?.  =(& cape.sock.hint)  ~&(>>> %fast-lost-clue gen)
    =*  clue  data.sock.hint
    ?.  ?=([name=$@(@tas [@tas @]) dad=* *] clue)
      ~&(>>> fast-bad-clue+clue gen)
    =/  label=cord
      ?@  name.clue  name.clue
      (rap 3 -.name.clue (scot %ud +.name.clue) ~)
    ::
    ?~  parent=(fast-parent dad.clue)  ~&(>>> fast-bad-clue+clue gen)
    ?~  u.parent
      ::  register root
      ::
      ?.  =(& cape.sock.result)  ~&(>>> %fast-lost-root gen)
      %=  gen
        core.jets  (~(put ju core.jets.gen) ~[label] sock.result)
        root.jets  (~(put ju root.jets.gen) data.sock.result ~[label])
      ==
    ::  register child core
    ::
    =/  axis=@  u.u.parent
    ?.  =(3 (cap axis))  ~&(>>> fast-weird-axis+axis gen)
    =/  batt  (~(pull so sock.result) 2)
    ?.  =(& cape.batt)   ~&(>>> fast-lost-batt+label gen)
    ?.  ?=(^ data.batt)  ~&(>>> fast-atom-batt+data.batt gen)
    =/  fore  (~(pull so sock.result) axis)
    =/  past=(set path)
      %-  %~  uni  in
          ::  root registrations
          ::
          ?.  =(& cape.fore)  ~
          (~(get ju root.jets.gen) data.fore)
      ::  child registrations
      ::
      =/  batt-fore  (~(pull so fore) 2)
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
    ?.  (~(huge so i.socks) fore)  sock-loop(socks t.socks)
    =/  just-fol=sock  [[& |] data.batt ~]
    =/  template=sock  (~(darn so just-fol) axis i.socks)
    ::
    %=  gen
      core.jets  (~(put ju core.jets.gen) pax template)
      batt.jets  (~(put ju batt.jets.gen) data.batt pax)
    ==
  ==
::
++  jet-simple-gate-hoot
  =/  l=(list)
    =>  hoot
    :~  dec  add  sub  mul  div  mod  dvr  gte  gth
        lte  lth  max  min  cap  mas  peg  bex  can
        cat  cut  end  fil  hew  lsh  met  rap  rep
        rev  rig  rip  rsh  run  rut  sew  swp  xeb
        mug  mor  gor  aor
    ==
  |=  [s=* f=*]
  ^-  (unit (unit))
  ?~  l  ~
  ?:  &(=(f -.i.l) =(-.s -.i.l) =(+>.s +>.i.l))
    `(mure |.((slum i.l +<.s)))
  $(l t.l)
::
++  jet-simple-gate-play
  =/  l=(list)
    =>  playpen
    :~  dec  add  sub  mul  div  mod  dvr  gte  gth
        lte  lth  bex  can  cat  cut  end  fil  lsh
        met  rap  rep  rev  rip  rsh  swp  xeb  mug
        mor  gor
    ==
  |=  [s=* f=*]
  ^-  (unit (unit))
  ?~  l  ~
  ?:  &(=(f -.i.l) =(-.s -.i.l) =(+>.s +>.i.l))
    `(mure |.((slum i.l +<.s)))
  $(l t.l)
::
++  jet
  |=  [s=* f=*]
  ^-  (unit (unit))
  :: ~
  ?^  res=(jet-simple-gate-hoot s f)  res
  ?^  res=(jet-simple-gate-play s f)  res
  ::  place for jets with nontrivial templates
  ::
  ~
::
++  rewrite-memo
  |=  memoized=(map @uxsite @uxmemo)
  |=  n=nomm
  ^-  nomm
  ~+
  ?^  -.n  [$(n -.n) $(n +.n)]
  ?-    -.n
      %ds2
    :+  %ds2  $(n p.n)
    ?.  ?=([%site *] site.n)               site.n
    ?~  m=(~(get by memoized) q.p.site.n)  site.n
    memo+u.m
  ::
      %dus2
    :^  %dus2  $(n p.n)  $(n q.n)
    ?.  ?=([%site *] site.n)               site.n
    ?~  m=(~(get by memoized) q.p.site.n)  site.n
    memo+u.m
  ::
    ?(%0 %1)          n
    ?(%3 %4)          n(p $(n p.n))
    %s11              n(q $(n q.n))
    ?(%5 %7 %12 %i2)  n(p $(n p.n), q $(n q.n))
    %d11              n(q.p $(n q.p.n), q $(n q.n))
    %10               n(q.p $(n q.p.n), q $(n q.n))
    %6                n(p $(n p.n), q $(n q.n), r $(n r.n))
  ==
::  Analyze s/f pair, then run Nomm interpreter on the result
::  Indirect calls reanalyze
::  Direct calls are verified with subject sock nest checking
::
++  run-nomm
  |=  [s=* f=*]
  ^-  (unit)
  !.
  =/  gen
    ~>  %bout
    (scan &+s f)
  ::
  =/  map-locals=(map @uxsite [less=sock fol=* =nomm])  (malt locals.gen)
  =/  edit  (rewrite-memo (malt memo-loop-entry.gen))
  =.  map-locals
    %-  ~(run by map-locals)
    |=  [sock * =nomm]
    +<(nomm (edit nomm))
  ::
  =.  idxs.memo.gen
    %-  ~(run by idxs.memo.gen)
    |=  meme
    +<(code (edit code))
  ::
  =.  sits.memo.gen
    %-  ~(run by sits.memo.gen)
    |=  meme
    +<(code (edit code))
  ::
  =.  fols.memo.gen
    %-  ~(run by fols.memo.gen)
    |=  l=(list meme)
    %+  turn  l
    |=  meme
    +<(code (edit code))
  ::
  =/  n=nomm
    ?^  m=(~(get by sits.memo.gen) 0v0 0x0)
      code.u.m
    =/  loc  (~(got by map-locals) 0x0)
    ?>  =(f fol.loc)
    nomm.loc
  ::
  =|  trace=(list spot)
  |-  ^-  (unit)
  ?-    n
      [p=^ q=*]
    =/  l  $(n p.n)
    ?~  l  ~
    =/  r  $(n q.n)
    ?~  r  ~
    `[u.l u.r]
  ::
      [%0 p=@]
    ?:  =(0 p.n)
      ~&  '[%0 0]'
      ~&  trace
      ~
    ?:  =(1 p.n)  `s
    =-  ~?  ?=(~ -)  '%0 crash'  -
    (mole |.(.*(s [0 p.n])))
  ::
      [%1 p=*]
    `p.n
  ::
      [%i2 *]
    ~&  %indirect
    =/  s1  $(n p.n)
    ?~  s1  ~
    =/  f1  $(n q.n)
    ?~  f1  ~
    ~>  %bout.[0 %indirect]
    (mole |.(.*(u.s1 u.f1)))
  ::
      [%ds2 *]
    =/  s1  $(n p.n)
    ?~  s1  ~
    =;  [fol=* new=nomm]
      ?^  res=(jet u.s1 fol)  u.res
      $(s u.s1, n new)
    ?-    -.site.n
        %memo
      =/  m  (~(got by idxs.memo.gen) p.site.n)
      [fol code]:m
    ::
        %site
      =/  loc  (~(got by map-locals) q.p.site.n)
      [fol nomm]:loc
    ==
  ::
      [%dus2 *]
    =/  s1  $(n p.n)
    ?~  s1  ~
    =/  f1  $(n q.n)
    ?~  f1  ~
    =;  [fol=* new=nomm]
      ?>  =(fol u.f1)
      ?^  res=(jet u.s1 fol)  u.res
      $(s u.s1, n new)
    ?-    -.site.n
        %memo
      =/  m  (~(got by idxs.memo.gen) p.site.n)
      [fol code]:m
    ::
        %site
      =/  loc  (~(got by map-locals) q.p.site.n)
      [fol nomm]:loc
    ==
  ::
      [%3 *]
    =/  p  $(n p.n)
    ?~  p  ~
    `.?(u.p)
  ::
      [%4 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?^  u.p  ~&  '%4 cell'  ~
    `+(u.p)
  ::
      [%5 *]
    =/  p  $(n p.n)
    ?~  p  ~
    =/  q  $(n q.n)
    ?~  q  ~
    `=(u.p u.q)
  ::
      [%6 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?+  u.p  ~&('%6 non-loobean' ~)
      %&  $(n q.n)
      %|  $(n r.n)
    ==
  ::
      [%7 *]
    =/  p  $(n p.n)
    ?~  p  ~
    $(s u.p, n q.n)
  ::
      [%10 *]
    ?:  =(0 p.p.n)  ~&  '%10 0'  ~
    =/  don  $(n q.p.n)
    ?~  don  ~
    =/  rec  $(n q.n)
    ?~  rec  ~
    =-  ~?  ?=(~ -)  '%10 crash'  -
    (mole |.(.*([u.don u.rec] [%10 [p.p.n %0 2] %0 3])))
  ::
      [%s11 *]
    $(n q.n)
  ::
      [%d11 *]
    =?  trace  =(p.p.n %spot)
      =/  pot=(unit spot)  ((soft spot) +.q.p.n)
      ?~  pot  trace
      [u.pot trace]
    ::
    =/  h  $(n q.p.n)
    ?~  h  ~
    $(n q.n)
  ::
      [%12 *]
    ~|  %no-scry  !!
  ==
::
++  match-sock
  |=  [a=sock lit=(list [less=sock code=nomm-1])]
  ^-  (unit nomm-1)
  =|  acc=(unit [less=sock out=nomm-1])
  |-  ^-  (unit nomm-1)
  ?~  lit
    ?~  acc  ~
    `out.u.acc
  =?  acc  (~(huge so less.i.lit) a)
    ?~  acc  `i.lit
    ::  found better match
    ::
    ?:  (~(huge so less.u.acc) less.i.lit)  `i.lit
    acc
  ::
  $(lit t.lit)
::  unit of work: subject, formula, if comes from jetted core dissasembly:
::    cons frame? jet registration coordinate
::
+$  todo  [sub=sock fol=* break=(unit [cons=? point=ring])]
::  analysis engine
::
++  ka
  |_  lon=long
  +*  this  .
  ::  Analyze subject/formula pair, descending into jetted cores
  ::
  ++  rout
    |=  [s=* f=*]
    ^+  this
    =/  queu=(list todo)  [[& s] f ~]~
    =|  load=(list todo)
    |-  ^+  this
    =*  cold-loop  $
    ?~  queu
      ?~  load
        :: ~&  ~(wyt by core.jets.lon)
        this
      =>  !@  verb  .
          ~&  >>  cold-loop+(lent load)  .
      cold-loop(queu (flop load), load ~)
    ?:  ?&(?=(^ break.i.queu) cons.u.break.i.queu)
      ::  merge analysis of an autocons head and tail
      ::
      =*  p  point.u.break.i.queu
      =*  b  back.cole.jets.lon
      =/  heds=(list [sub=sock fol=*])  ~(tap in (~(get ju b) p.p (peg q.p 2)))
      =/  lets=(list [sub=sock fol=*])  ~(tap in (~(get ju b) p.p (peg q.p 3)))
      =>  !@  verb  .
          ~&  >  [%commence-join (lent heds) (lent lets)]  .
      ?@  fol.i.queu  !!
      |-  ^+  this
      =*  hed-loop  $
      ?~  heds
        =>  !@  verb  .
            ~&  >  %done-joining  .
        cold-loop(queu t.queu)
      ?.  =(fol.i.heds -.fol.i.queu)
        =>  !@  verb  .
            ~&  >>  %join-head-wrong-fol  .
        hed-loop(heds t.heds)
      ?.  (~(huge so sub.i.heds) sub.i.queu)
        =>  !@  verb  .
            ~&  >>  %join-head-wrong-sub  .
        hed-loop(heds t.heds)
      =/  tels  lets
      |-  ^+  this
      =*  tel-loop  $
      ?~  tels  hed-loop(heds t.heds)
      ?.  =(fol.i.tels +.fol.i.queu)
        =>  !@  verb  .
            ~&  >>  %join-tail-wrong-fol  .
        tel-loop(tels t.tels)
      ?.  (~(huge so sub.i.tels) sub.i.queu)
        =>  !@  verb  .
            ~&  >>  %join-tail-wrong-sub  .
        tel-loop(tels t.tels)
      =>  !@  verb  .
          ~&  >  joined+p  .
      =/  join  (~(pack so sub.i.heds) sub.i.tels)
      =.  call.cole.jets.lon  (~(put by call.cole.jets.lon) [join fol.i.queu] p)
      =.  back.cole.jets.lon  (~(put ju back.cole.jets.lon) p join fol.i.queu)
      tel-loop(tels t.tels)
    ::  analyze a formula from a queue, push new tasks in the back queu
    ::
    ::  prepare state
    ::
    =^  here-arm  arm-gen.lon  [arm-gen.lon +(arm-gen.lon)]
    =/  can  scan
    =.  -.gen.can  lon
    =.  here-arm.gen.can  here-arm
    ::  analyze
    ::
    =>  !@  verb  .
        ~?  >  ?=(^ break.i.queu)  [%enter here-arm point.u.break.i.queu]
        ~?  >  ?=(~ break.i.queu)  [%enter here-arm]
        .
    =/  gen=short
      !@  verb  (can [sub fol]:i.queu)
      ~>  %bout.[0 %skan]
      (can [sub fol]:i.queu)
    ::
    ::  propagate updates
    ::
    =/  new  ((dif-ju core.jets.gen) core.jets.lon)
    =.  lon  -.gen
    =/  edit  (rewrite-memo (malt memo-loop-entry.gen))
    ::  XX iterate only over the new? might have to keep track of old and new
    ::  memo in short
    ::
    =.  idxs.memo.lon
      %-  ~(run by idxs.memo.lon)
      |=  m=meme
      ?.  =(here-arm arm.m)  m
      m(code (edit code.m))
    ::
    =.  sits.memo.lon
      %-  ~(run by sits.memo.lon)
      |=  m=meme
      ?.  =(here-arm arm.m)  m
      m(code (edit code.m))
    ::
    =.  fols.memo.lon
      %-  ~(run by fols.memo.lon)
      |=  l=(list meme)
      %+  turn  l
      |=  m=meme
      ?.  =(here-arm arm.m)  m
      m(code (edit code.m))
    ::
    =?  areas.arms.lon  ?=(^ area.gen)
      (~(put by areas.arms.lon) here-arm u.area.gen)
    ::
    =^  sub-0x0=sock  doors.arms.lon
      ?^  memo-entry.gen
        =/  m  (~(got by idxs.memo.lon) u.memo-entry.gen)
        :-  less-code.m
        (~(put by doors.arms.lon) here-arm [less-code fol code]:m)
      ?^  m=(~(get by sits.memo.lon) here-arm 0x0)
        :-  less-code.u.m
        (~(put by doors.arms.lon) here-arm [less-code fol code]:u.m)
      ?~  locals.gen  !!
      ?>  =(0x0 site.i.locals.gen)
      :-  less.i.locals.gen
      (~(put by doors.arms.lon) here-arm +.i.locals.gen)
    ::
    =/  new-sites=(map [@uvarm @uxsite] [less=sock fol=* =nomm])
      ?~  locals.gen  ~
      %+  roll
        ?.  =(0x0 site.i.locals.gen)  locals.gen
        t.locals.gen
      |=  $:  [site=@uxsite less=sock fol=* =nomm]
              acc=(map [@uvarm @uxsite] [less=sock fol=* =nomm])
          ==
      ^+  acc
      (~(put by acc) [here-arm site] less fol (edit nomm))
    ::
    =.  sites.arms.lon  (~(uni by sites.arms.lon) new-sites)
    %=    cold-loop
        queu  t.queu
    ::
        cole.jets.lon
      ?~  break.i.queu  cole.jets.lon
      =*  p  point.u.break.i.queu
      =/  boot=(pair sock *)  [sub-0x0 fol.i.queu]
      %=  cole.jets.lon
        call  (~(put by call.cole.jets.lon) boot p)
        back  (~(put ju back.cole.jets.lon) p boot)
      ==
    ::
        load
      ::  we sort the list of new jet registrations by ascending order of path
      ::  length, to analyze short paths before the long ones. roll here and 
      ::  flop above cancel each other out
      ::
      %+  roll
        %+  sort
          %+  turn  ~(tap by new)
          |=([p=path q=(set sock)] [(lent p) p q])
        |=([l=[len=@ *] r=[len=@ *]] (lth len.l len.r))
      |:  [[len=*@ p=*path q=*(set sock)] load=load]
      =>  !@  verb  .
          ~&  >  [%enqueu p]  .
      %-  ~(rep in q)
      |:  [s=*sock load=load]
      =/  batt  (~(pull so s) 2)
      ?.  =(& cape.batt)  ~&(>>> [%cold-miss-batt p] load)
      =*  f  data.batt
      =/  ax=@  2
      |-  ^+  load
      ?.  ?=([^ *] f)  [[s f `[| p ax]] load]
      =.  load  $(f -.f, ax (peg ax 2))
      =.  load  $(f +.f, ax (peg ax 3))
      [[s f `[& p ax]] load]
    ==
  --
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
++  skim-by
  |*  a=(map)
  |*  s=(set _?~(a !! p.n.a))
  |-  ^+  a
  ?~  a  ~
  %.  $(a r.a)
  %~  uni  in
  %.  $(a l.a)
  %~  uni  in
  ?.  (~(has in s) p.n.a)  ~
  [n.a ~ ~]
--
::  second pass of the analysis
|%
++  run-nomm-1
  |=  [s=* f=*]
  ^-  (unit *)
  =/  cor  ka
  =.  cor  (rout:cor s f)  ::  XX properly stateful analysis
  =/  bol=boil  (cook lon.cor)
  =/  matches=(list [less=sock code=nomm-1])  (~(get ja fols.bol) f)
  =/  match  (match-sock &+s matches)
  ?~  match  !!
  =/  n=nomm-1  u.match
  =|  trace=(list spot)
  ::  exec loop
  ::
  |-  ^-  (unit)
  ?-    n
      [p=^ q=*]
    =/  l  $(n p.n)
    ?~  l  ~
    =/  r  $(n q.n)
    ?~  r  ~
    `[u.l u.r]
  ::
      [%0 p=@]
    ?:  =(0 p.n)
      ~&  '[%0 0]'
      ~&  trace
      ~
    ?:  =(1 p.n)  `s
    =-  ~?  ?=(~ -)  '%0 crash'  -
    (mole |.(.*(s [0 p.n])))
  ::
      [%1 p=*]
    `p.n
  ::
      [%2 *]
    ?~  info.n
      ~&  %indirect
      =/  s1  $(n p.n)
      ?~  s1  ~
      ?~  q.n  !!
      =/  f1  $(n u.q.n)
      ?~  f1  ~
      ~>  %bout.[0 %indirect]
      (mole |.(.*(u.s1 u.f1)))
    =/  s1  $(n p.n)
    ?~  s1  ~
    ?>
      ?~  q.n  &
      =/  f1  $(n u.q.n)
      ?~  f1  |
      =(fol.u.info.n u.f1)
    ::
    =/  new=nomm-1  (~(got by code.bol) u.info.n)
    ?^  res=(jet u.s1 fol.u.info.n)  u.res
    $(s u.s1, n new)
  ::
      [%3 *]
    =/  p  $(n p.n)
    ?~  p  ~
    `.?(u.p)
  ::
      [%4 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?^  u.p  ~&  '%4 cell'  ~
    `+(u.p)
  ::
      [%5 *]
    =/  p  $(n p.n)
    ?~  p  ~
    =/  q  $(n q.n)
    ?~  q  ~
    `=(u.p u.q)
  ::
      [%6 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?+  u.p  ~&('%6 non-loobean' ~)
      %&  $(n q.n)
      %|  $(n r.n)
    ==
  ::
      [%7 *]
    =/  p  $(n p.n)
    ?~  p  ~
    $(s u.p, n q.n)
  ::
      [%10 *]
    ?:  =(0 p.p.n)  ~&  '%10 0'  ~
    =/  don  $(n q.p.n)
    ?~  don  ~
    =/  rec  $(n q.n)
    ?~  rec  ~
    =-  ~?  ?=(~ -)  '%10 crash'  -
    (mole |.(.*([u.don u.rec] [%10 [p.p.n %0 2] %0 3])))
  ::
      [%11 @ *]
    $(n q.n)
  ::
      [%11 [@ *] *]
    =?  trace  =(p.p.n %spot)
      =/  pot=(unit spot)  ((soft spot) +.q.p.n)
      ?~  pot  trace
      [u.pot trace]
    ::
    =/  h  $(n q.p.n)
    ?~  h  ~
    $(n q.n)
  ::
      [%11 *]
    ~|  %impossible  !!
  ::
      [%12 *]
    ~|  %no-scry  !!
  ==
::
++  cook
  |=  lon=long
  ^-  boil
  =/  code=(map [sock *] nomm-1)
    %-  ~(rep by idxs.memo.lon)
    |=  [[k=* v=meme] acc=(map [sock *] nomm-1)]
    (~(put by acc) [less-code.v fol.v] (rewrite code.v lon))
  ::
  =.  code
    %-  ~(rep by doors.arms.lon)
    |=  [[k=* v=[less=sock fol=* =nomm]] acc=_code]
    (~(put by acc) [less.v fol.v] (rewrite nomm.v lon))
  ::
  =.  code
    %-  ~(rep by sites.arms.lon)
    |=  [[k=* v=[less=sock fol=* =nomm]] acc=_code]
    (~(put by acc) [less.v fol.v] (rewrite nomm.v lon))
  ::
  =/  fols=(jar * [less=sock code=nomm-1])
    %-  ~(rep by code)
    |=  [[k=[less=sock fol=*] v=nomm-1] acc=(jar * [less=sock code=nomm-1])]
    (~(add ja acc) fol.k less.k v)
  ::
  [call.cole.jets.lon code fols]
::
++  rewrite
  |=  [n=nomm lon=long]
  ^-  nomm-1
  ?-    -.n
      ^         [$(n -.n) $(n +.n)]
      ?(%0 %1)  n
      %3        [%3 $(n p.n)]
      %4        [%4 $(n p.n)]
      %5        [%5 $(n p.n) $(n q.n)]
      %7        [%7 $(n p.n) $(n q.n)]
      %12       [%12 $(n p.n) $(n q.n)]
      %s11      [%11 p.n $(n q.n) body.n]
      %6        [%6 $(n p.n) $(n q.n) $(n r.n)]
      %10       [%10 [p.p.n $(n q.p.n)] $(n q.n)]
      %d11      [%11 [p.p.n $(n q.p.n)] $(n q.n) body.n]
  ::
      %i2       [%2 $(n p.n) `$(n q.n) ~]
      %ds2
    :^  %2  $(n p.n)  ~
    ^-  (unit [sock *])
    :-  ~
    ?-  -.site.n
      %memo  [less-code fol]:(~(got by idxs.memo.lon) p.site.n)
      %site  ?:  =(0x0 q.p.site.n)
               [less fol]:(~(got by doors.arms.lon) p.p.site.n)
             [less fol]:(~(got by sites.arms.lon) p.site.n)
    ==
  ::
      %dus2
    :^  %2  $(n p.n)  `$(n q.n)
    ^-  (unit [sock *])
    :-  ~
    ?-  -.site.n
      %memo  [less-code fol]:(~(got by idxs.memo.lon) p.site.n)
      %site  ?:  =(0x0 q.p.site.n)
               [less fol]:(~(got by doors.arms.lon) p.p.site.n)
             [less fol]:(~(got by sites.arms.lon) p.site.n)
    ==
  ==
::
++  walk-nock
  |=  gat=$-(* (unit *))
  |=  fol=*
  ^-  *
  =-  ?:(=(- fol) fol -)
  ?^  pro=(gat fol)  u.pro
  ?+  fol  !!
    [^ *]                [$(fol -.fol) $(fol +.fol)]
    [%0 *]               fol
    [%1 *]               fol
    [%2 p=* q=*]         [%2 $(fol p.fol) $(fol q.fol)]
    [%3 p=*]             [%3 $(fol p.fol)]
    [%4 p=*]             [%4 $(fol p.fol)]
    [%5 p=* q=*]         [%5 $(fol p.fol) $(fol q.fol)]
    [%6 p=* q=* r=*]     [%6 $(fol p.fol) $(fol q.fol) $(fol r.fol)]
    [%7 p=* q=*]         [%7 $(fol p.fol) $(fol q.fol)]
    [%8 p=* q=*]         [%8 $(fol p.fol) $(fol q.fol)]
    [%9 p=@ q=*]         [%9 p.fol $(fol q.fol)]
    [%10 [p=@ q=*] r=*]  [%10 [p.fol $(fol q.fol)] $(fol r.fol)]
    [%11 p=@ q=*]        [%11 p.fol $(fol q.fol)]
    [%11 [p=@ q=*] r=*]  [%11 [p.fol $(fol q.fol)] $(fol r.fol)]
    [%12 p=* q=*]        [%12 $(fol p.fol) $(fol q.fol)]
  ==
::
++  strip-hints
  %-  walk-nock
  |=  fol=*
  ^-  (unit *)
  ?.  ?=([%11 * p=*] fol)  ~
  `p
::  product: map SCC entry -> SCC members (including itself)
::
++  find-sccs-all
  |=  code=(map bell nomm-1)
  ^-  (map bell (set bell))
  %-  ~(rep by code)
  |=  [[k=bell v=nomm-1] acc=(map bell (set bell))]
  ?:  (~(has by acc) k)  acc
  ((find-sccs code) k v acc)
::
++  find-sccs
  |=  code=(map bell nomm-1)
  |=  [b=bell n=nomm-1 sccs-init=(map bell (set bell))]
  ^+  sccs-init
  =|  stack-set=(set bell)
  =|  stack-list=(list bell)
  =<
    ?>  =(~ ongoing)
    final
  ::  final: finalized SCCs: map entry -> members (including the entry)
  ::  ongoing: stack of SCCs
  ::
  =/  gen=[final=_sccs-init ongoing=(list [entry=bell members=(set bell)])]
    [sccs-init ~]
  ::
  |^  ^-  [loopy=? _gen]
  =*  call-loop  $
  ^-  [loopy=? _gen]
  =.  stack-set  (~(put in stack-set) b)
  =.  stack-list  [b stack-list]
  =;  [loopy=? gen1=_gen]
    ::  call done, check if we are an entry point
    ::
    =.  gen  gen1
    ?.  loopy
      =.  final.gen  (~(put by final.gen) b [b ~ ~])
      |+gen
    ?~  ongoing.gen  !!
    ?.  =(b entry.i.ongoing.gen)  &+gen
    :-  |
    %=  gen
      ongoing  t.ongoing.gen
      final    (~(put by final.gen) b members.i.ongoing.gen)
    ==
  ::
  |-  ^-  [loopy=? _gen]
  =*  nomm-loop  $
  ^-  [loopy=? _gen]
  ?-    n
      [p=^ q=*]
    =^  l  gen  nomm-loop(n p.n)
    =^  r  gen  nomm-loop(n q.n)
    :_  gen
    |(loopy.l loopy.r)
  ::
      [%0 *]  |+gen
      [%1 *]  |+gen
  ::
      [%2 *]
    ^-  [loopy=? _gen]
    ?~  info.n
      ?~  q.n  !!
      =^  s  gen  nomm-loop(n p.n)
      =^  f  gen  nomm-loop(n u.q.n)
      :_  gen
      |(loopy.s loopy.f)
    =^  s  gen  nomm-loop(n p.n)
    =^  f  gen
      ?~  q.n  [loopy=| gen]
      nomm-loop(n u.q.n)
    ::
    ?:  (~(has by final.gen) u.info.n)  |+gen
    =^  present=?  gen  (find-merge u.info.n)
    ?:  present
      ?~  ongoing.gen  !!
      =/  members=(set bell)
        %-  silt
        =/  out=(list bell)  ~[entry.i.ongoing.gen]
        |-  ^-  (list bell)
        ?~  stack-list  !!
        ?:  =(entry.i.ongoing.gen i.stack-list)  out
        $(stack-list t.stack-list, out [i.stack-list out])
      ::
      =.  members.i.ongoing.gen  (~(uni in members.i.ongoing.gen) members)
      &+gen
    ?.  (~(has in stack-set) u.info.n)
      =^  call  gen  call-loop(b u.info.n, n (~(got by code) u.info.n))
      :_  gen
      |(loopy.s loopy.f loopy.call)
    =/  members=(set bell)
      %-  silt
      =/  out=(list bell)  ~[u.info.n]
      |-  ^-  (list bell)
      ?~  stack-list  !!
      ?:  =(u.info.n i.stack-list)  out
      $(stack-list t.stack-list, out [i.stack-list out])
    ::
    =.  ongoing.gen  [[u.info.n members] ongoing.gen]
    &+merge
  ::
      [%3 *]  nomm-loop(n p.n)
      [%4 *]  nomm-loop(n p.n)
  ::
      [%5 *]
    =^  p  gen  nomm-loop(n p.n)
    =^  q  gen  nomm-loop(n q.n)
    :_  gen
    |(loopy.p loopy.q)
  ::
      [%6 *]
    =^  p  gen  nomm-loop(n p.n)
    =^  q  gen  nomm-loop(n q.n)
    =^  r  gen  nomm-loop(n r.n)
    :_  gen
    |(loopy.p loopy.q loopy.r)
  ::
      [%7 *]
    =^  p  gen  nomm-loop(n p.n)
    =^  q  gen  nomm-loop(n q.n)
    :_  gen
    |(loopy.p loopy.q)
  ::
      [%10 *]
    =^  qp  gen  nomm-loop(n q.p.n)
    =^  q   gen  nomm-loop(n q.n)
    :_  gen
    |(loopy.qp loopy.q)
  ::
      [%11 *]
    ?@  p.n  nomm-loop(n q.n)
    =^  qp  gen  nomm-loop(n q.p.n)
    =^  q   gen  nomm-loop(n q.n)
    :_  gen
    |(loopy.qp loopy.q)
  ::
      [%12 *]
    =^  p  gen  nomm-loop(n p.n)
    =^  q  gen  nomm-loop(n q.n)
    :_  gen
    |(loopy.p loopy.q)
  ==
  ::
  ++  merge
    ^+  gen
    ?~  ongoing.gen  !!
    =/  scc  i.ongoing.gen
    =/  top=(list [entry=bell members=(set bell)])  (flop t.ongoing.gen)
    =|  bot=(list [entry=bell members=(set bell)])
    |-  ^+  gen
    ?~  top  gen
    ?:  =(~ (~(int in members.scc) members.i.top))
      $(top t.top, bot [i.top bot])
    %=    gen
        ongoing
      :_  bot
      :-  (min-entry entry.scc entry.i.top)
      %+  roll  `(list [bell (set bell)])`top
      |=  [[entry=bell members=(set bell)] acc=_members.scc]
      (~(uni in acc) members)
    ==
  ::
  ++  min-entry
    |=  [a=bell b=bell]
    ^-  bell
    ?:  =(a b)  a
    |-  ^-  bell
    ?~  stack-list  !!
    ?:  =(a i.stack-list)
      ?>  ?=(^ (find ~[b] t.stack-list))
      b
    ?:  =(b i.stack-list)
      ?>  ?=(^ (find ~[a] t.stack-list))
      a
    $(stack-list t.stack-list)
  ::
  ++  find-merge
    |=  b=bell
    ^-  [? _gen]
    =|  top=(list [entry=bell members=(set bell)])
    =/  bot=(list [entry=bell members=(set bell)])  ongoing.gen
    |-  ^-  [? _gen]
    ?~  bot  [| gen]
    ?.  (~(has in members.i.bot) b)
      $(bot t.bot, top [i.bot top])
    :-  &
    %=    gen
        ongoing
      :_  t.bot
      :-  entry.i.bot
      %+  roll  top
      |=  [[entry=bell members=(set bell)] acc=_members.i.bot]
      (~(uni in acc) members)
    ==
  --
::
++  find-args-all
  |=  code=(map bell nomm-1)
  ^-  (map bell meme-args)
  %-  ~(rep by code)
  |=  [[k=bell v=nomm-1] acc=(map bell meme-args)]
  ?:  (~(has by acc) k)  acc
  ((find-args code) k v acc)
::
+$  meme-args
  $:  =bell
      prod=sock
      map=(lest spring:source)
      args-transitive=args
      args-top=args
  ==
::
++  mug-set-bell
  |=  s=(tree bell)
  ^-  (tree @ux)
  ?~  s  ~
  [(mug n.s) $(s l.s) $(s r.s)]
::
++  valid-sccs
  |=  sccs=(map bell (set bell))
  ^-  ?
  ::  a member of SCC must not be present anywhere else, nor
  ::  be a key to another SCC other than its own
  ::
  %-  ~(rep by sccs)
  |=  [[k-out=bell v-set-out=(set bell)] acc=?]
  %-  ~(rep in v-set-out)
  |=  [v-bell=bell acc=?]
  %-  ~(rep by sccs)
  |=  [[k-in=bell v-set-in=(set bell)] acc=?]
  ?&  acc
      ?|  =(k-in k-out)
          &(!=(v-bell k-in) !(~(has in v-set-in) v-bell))
  ==  ==
::
++  find-args
  |=  code=(map bell nomm-1)
  |=  [b=bell n=nomm-1 memo=(map bell meme-args)]
  ^-  (map bell meme-args)
  =/  sccs=(map bell (set bell))
    ~>  %bout.[0 'find sccs']
    (find-sccs-all code)
  ::
  :: ~&  %validity-check
  :: ?>  ~>  %bout.[0 'validity check']  (valid-sccs sccs)
  =|  stack-set=(set bell)
  =|  stack-list=(list bell)
  =/  sub=sock-anno  [bus.b ~[~[1]]]
  =+  ^=  gen
      ^-  $:  memo=(map bell meme-args)
              loc=args-locations
              loop-calls=(map bell args)
              melo=(map bell meme-args)  ::  memo inside of a nontrivial scc
          ==
      [memo ~ ~ ~]
  ::
  =<  memo
  |^  ^-  [sock-anno _gen]
  =*  call-loop  $
  =.  stack-set  (~(put in stack-set) b)
  =.  stack-list  [b stack-list]
  ~&  [%enter `@ux`(mug b)]
  =;  [prod=sock-anno gen1=_gen]
    ::  fixpoint search done, finalize
    ::
    =.  gen  gen1
    =/  map=(lest spring:source)  i.src.prod
    =/  final-args=(unit args)  (~(get by loc.gen) b)
    =/  =args  ?~(final-args ~ u.final-args)
    ::  captured parts of the subject are required as arguments
    ::
    =/  args-capture=^args
      =.  stack-list  [-.stack-list ~]
      =.  loc.gen  ~
      =.  loc.gen  (update-loc-gen ~[map] [%arg ~ ~])
      ?~  loc.gen  ~
      ?>  ?=([* ~ ~] loc.gen)
      q.n.loc.gen
    ::
    =/  arg-with-captured  (uni-args args args-capture)
    ::
    =/  meme=meme-args  [b sock.prod map args arg-with-captured]
    ?:  (~(has by sccs) b)
      =.  memo.gen  (~(put by memo.gen) b meme)
      =.  memo.gen  (~(uni by memo.gen) melo.gen)
      =?  loc.gen  ?=(^ final-args)  (~(del by loc.gen) b)
      =.  melo.gen  ~
      [prod gen]
    =.  melo.gen  (~(put by melo.gen) b meme)
    =?  loc.gen  ?=(^ final-args)  (~(del by loc.gen) b)
    [prod gen]
  ^-  [sock-anno _gen]
  =/  counter=@  0
  |-  ^-  [sock-anno _gen]
  =*  fixpoint-loop  $
  =;  [prod=sock-anno gen1=_gen]
    ::  traversal of nomm and callees done, check if we converged
    ::
    ?~  args-loop-mayb=(~(get by loop-calls.gen1) b)  [prod gen1]
    =/  =args  (normalize-args (~(gut by loc.gen1) b ~))
    ?:  =(u.args-loop-mayb args)
      [prod gen1(loop-calls (~(del in loop-calls.gen1)))]
    ?:  =(4 counter)
      ::  ugly hack: if we didn't converge in three tries we use the entire
      ::  subject as an argument for the loop calls and for this call
      ::  XX but why we don't converge in complete:musk?
      ::
      :: =.  loc.gen1  (~(put by loc.gen1) b [%arg ~ ~])
      :: [prod gen1(loop-calls (~(del in loop-calls.gen1)))]
      !!
    ~&  [%fixpoint counter `@ux`(mug b)]
    %=    fixpoint-loop
        loop-calls.gen
      :: (~(put by loop-calls.gen1) b ?:(=(counter 3) [%arg ~ ~] args))
      (~(put by loop-calls.gen1) b ?:(=(counter 3) !! args))
    ::
        memo.gen  memo.gen1
        counter   +(counter)
    ==
  |-  ^-  [prod=sock-anno _gen]
  =*  nomm-loop  $
  ?-    n
      [p=^ q=*]
    =^  l  gen  nomm-loop(n p.n)
    =^  r  gen  nomm-loop(n q.n)
    :_  gen
    :-  (~(knit so sock.prod.l) sock.prod.r)
    (cons:source src.prod.l src.prod.r)
  ::
      [%0 *]
    ?:  =(0 p.n)  [(dunno sub) gen]
    =/  prod=sock-anno
      ?:  =(1 p.n)  sub
      :-  (~(pull so sock.sub) p.n)
      (slot:source src.sub p.n)
    ::
    =?  loc.gen  !=(1 p.n)  (update-loc-gen src.prod [%look ~ ~])
    [prod gen]
  ::
      [%1 *]
    :_  gen
    [&+p.n [~[~] t.src.sub]]
  ::
      [%2 *]
    ?~  info.n
      ?~  q.n  !!
      =^  s  gen  nomm-loop(n p.n)
      =^  f  gen  nomm-loop(n u.q.n)
      =.  loc.gen  (update-loc-gen src.prod.s [%arg ~ ~])
      =.  loc.gen  (update-loc-gen src.prod.f [%arg ~ ~])
      :_  gen
      (dunno sub)
    =^  s  gen            nomm-loop(n p.n)
    =?  gen  ?=(^ q.n)  +:nomm-loop(n u.q.n)
    =^  [args-callee=args prod=sock-anno]  gen
      ?:  (~(has in stack-set) u.info.n)
        ?~  args-loop-mayb=(~(get by loop-calls.gen) u.info.n)
          =.  loop-calls.gen  (~(put by loop-calls.gen) u.info.n ~)
          [[~ (dunno sub)] gen]
        [[u.args-loop-mayb (dunno sub)] gen]
      ?^  meme=(~(get by memo.gen) u.info.n)
        =/  src  src.sub(i (compose:source map.u.meme i.src.sub))
        [[args-transitive.u.meme [prod.u.meme src]] gen]
      ?^  meal=(~(get by melo.gen) u.info.n)
        =/  src  src.sub(i (compose:source map.u.meal i.src.sub))
        [[args-transitive.u.meal [prod.u.meal src]] gen]
      ::  analyze through
      ::
      =^  pro=sock-anno  gen
        %=  call-loop
          sub  s(src.prod [~[1] src.prod.s])
          n    (~(got by code) u.info.n)
          b    u.info.n
        ==
      ::
      :_  gen
      =/  args-transitive=args
        ?^  meal=(~(get by melo.gen) u.info.n)  args-transitive.u.meal
        args-transitive:(~(got by memo.gen) u.info.n)
      ::
      :-  args-transitive
      ?~  t.src.pro  !!
      %=  pro
        t.src  t.t.src.pro
        i.src  (compose:source i.src.pro i.t.src.pro)
      ==
    ::
    =.  loc.gen  (update-loc-gen src.prod.s args-callee)
    [prod gen]
  ::
      ?([%3 *] [%4 *])
    =^  p  gen  nomm-loop(n p.n)
    =.  loc.gen  (update-loc-gen src.prod.p [%arg ~ ~])
    :_  gen
    (dunno sub)
  ::
      [%5 *]
    =^  p  gen  nomm-loop(n p.n)
    =^  q  gen  nomm-loop(n q.n)
    =.  loc.gen  (update-loc-gen src.prod.p [%arg ~ ~])
    =.  loc.gen  (update-loc-gen src.prod.q [%arg ~ ~])
    :_  gen
    (dunno sub)
  ::
      [%6 *]
    =^  c  gen  nomm-loop(n p.n)
    ::  only the condition is the true argument here
    ::
    =.  loc.gen  (update-loc-gen src.prod.c [%arg ~ ~])
    ::  We find the "deepest common argument usage" between branches
    ::  and unify that with the usage accumulated so far + %6 condition
    ::  expression argument usage
    ::
    =/  [y=sock-anno gen-y=_gen]  nomm-loop(n q.n, loc.gen ~)
    =/  [n=sock-anno gen-n=_gen]  nomm-loop(n r.n, gen gen-y(loc ~))
    =.  gen
      [ memo.gen-n
        (args-branches loc.gen loc.gen-y loc.gen-n)
        loop-calls.gen-n
        melo.gen-n
      ]
    ::
    =/  int=sock  (~(purr so sock.y) sock.n)
    =/  uni-src=source
      =,  source
      (uni (mask src.y cape.int) (mask src.n cape.int))
    ::
    :_  gen
    [int uni-src]
  ::
      [%7 *]
    =^  p  gen  nomm-loop(n p.n)
    nomm-loop(n q.n, sub prod.p)
  ::
      [%10 *]
    =^  rec  gen  nomm-loop(n q.n)
    =^  don  gen  nomm-loop(n q.p.n)
    ::  edit site needs to exist for safe arg disassembly
    ::
    =/  edit-site-src  (slot:source src.prod.rec p.p.n)
    =?  loc.gen  !=(1 p.p.n)  (update-loc-gen edit-site-src [%look ~ ~])
    :_  gen
    :-  (~(darn so sock.prod.rec) p.p.n sock.prod.don)
    (edit:source src.prod.rec p.p.n src.prod.don)
  ::
      [%11 *]
    ?@  p.n  nomm-loop(n q.n)
    :: ~?  &(=(%spot p.p.n) =(0x2a97.a282 (mug b)))
    ::   ((soft spot) +.q.p.n)
    ::
    =.  gen  +:nomm-loop(n q.p.n)
    nomm-loop(n q.n)
  ::
      [%12 *]
    =^  p  gen  nomm-loop(n p.n)
    =^  q  gen  nomm-loop(n q.n)
    =.  loc.gen  (update-loc-gen src.prod.p [%arg ~ ~])
    =.  loc.gen  (update-loc-gen src.prod.q [%arg ~ ~])
    :_  gen
    (dunno sub)
  ==  
  ::
  ++  update-loc-gen
    |=  [src=source =args]
    (update-args-loc loc.gen src ?~(stack-list !! stack-list) args)
  --
--
