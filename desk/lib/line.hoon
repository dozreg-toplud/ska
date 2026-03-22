/-  gene
/+  *skan
::
=,  gene
=*  stub  ~|(%stub !!)
=*  direct-entrypoint  0w1
|_  lon=line-long
+*  this  .
++  span-args
  |=  n=@
  ^-  (list @uvre)
  ?~  n  ~
  (gulf `@uvre`0 `@uvre`(dec n))
::  XX rewrite the registers again to compress the space
::
++  back
  ^-  (list tape)
  =/  bell-to-idx=(map bell @uxor)
    =<  +
    %-  ~(rep by code.lon)
    |=  [[k=bell v=*] acc=[i=@uxor m=(map bell @uxor)]]
    [+(i.acc) (~(put by m.acc) k i.acc)]
  ::
  |^
  %+  weld
    ::  function declarations
    ::
    ^-  (list tape)
    %-  ~(rep by code.lon)
    |=  [[k=bell v=straight] txt=(list tape)]
    :_  txt
    =/  input  (render-input-args n-args.v)
    =/  func-idx  (~(got by bell-to-idx) k)
    "static u3_noun _function_{<func-idx>}({input});\0a"
  ^-  (list tape)
  %-  ~(rep by code.lon)
  |=  [[k=bell v=straight] txt=(list tape)]
  :_  txt
  =/  max-reg=@  (get-max-register blocks.v)
  =/  num-regs-tape=tape  |2:(scow %ui +(max-reg))
  """
  static u3_noun
  _function_{<(~(got by bell-to-idx) k)>}({(render-input-args n-args.v)})
  \{
    u3_noun rs[{num-regs-tape}];
  {(render-prelude-with-indentation n-args.v)}
  {(render-body-with-indentation blocks.v)}
  }
  """
  ::
  ++  render-prelude-with-indentation
    |=  n=@
    ^-  tape
    ?~  n  ""
    %+  weld  $(n (dec n))
    "\0a  {(r (dec n))} = reg_{<`@uv`(dec n)>};"
  ::
  ++  get-max-register
    |=  blocks=(map @uwoo blob)
    ^-  @uvre
    =/  max-r=@uvre  `@`0
    %-  ~(rep by blocks)
    |=  [[k=* v=blob] max-r=@uvre]
    (max max-r (max-reg-blob v))
  ::
  ++  max-reg-blob
    |=  =blob
    ^-  @uvre
    ?>  =(~ phi.blob)
    %+  max  (max-reg-site bend.blob)
    (roll body.blob |=([p=pole max-r=@uvre] (max max-r (max-reg-pole p))))
  ::
  ++  max-reg-site
    |=  s=site
    ^-  @uvre
    (roll (get-regs-site s) max)
  ::
  ++  max-reg-pole
    |=  p=pole
    ^-  @uvre
    (roll (get-regs-pole p) max)
  ::
  ++  render-input-args
    |=  n=@ud
    ^-  tape
    ?~  n  ""
    =/  out=tape  "u3_noun reg_0v0"
    =/  i=@uv  `@`1
    |-  ^-  tape
    ?:  =(n i)  out
    $(i +(i), out (weld out ", u3_noun reg_{<i>}"))
  ::
  ++  render-body-with-indentation
    |=  blocks=(map @uwoo blob)
    ^-  tape
    =/  first  (~(got by blocks) direct-entrypoint)
    """
    {(render-block-with-indentation first)}
    //
    {(render-blocks-with-indentation (~(del by blocks) direct-entrypoint))}
    """
  ::  all but first
  ::
  ++  render-blocks-with-indentation
    |=  blocks=(map @uwoo blob)
    ^-  tape
    %-  ~(rep by blocks)
    |=  [[k=@uwoo v=blob] txt=tape]
    %-  weld
    :_  txt
    """
    _{<k>}:
    {(render-block-with-indentation v)}
    \0a
    """
  ::
  ++  render-block-with-indentation
    |=  =blob
    ^-  tape
    ?>  =(~ phi.blob)
    =/  lines-body=(list tape)  (turn body.blob render-pole)
    =/  end  (render-site-with-indentation bend.blob)
    ?:  =(~ lines-body)  end
    =.  lines-body  (turn lines-body (cury (bake weld ,[tape tape]) "  "))
    =/  body=tape  (zing (snoc (join ";\0a" lines-body) ";\0a"))
    (weld body end)
  ::
  ++  render-pole
    |=  p=pole
    ^-  tape
    ?-  -.p
      %imm  "{(r d.p)} = {(render-noun n.p)}"
      %mov  "{(r d.p)} = {(r s.p)}"
      %inc  "{(r d.p)} = INC({(r s.p)})"
      %con  "{(r d.p)} = CON({(r h.p)}, {(r t.p)})"
      %hed  "{(r d.p)} = HED({(r s.p)})"
      %tal  "{(r d.p)} = TAL({(r s.p)})"
      %cel  "CEL({(r p.p)})"
      ::  skipped for now
      %his  "//  his"
      %hos  "//  hos"
      %hid  "//  hid"
      %hod  "//  hod"
      %spy  "//  spy"
      %mem  "//  mem"
      %hys  "//  hys"
      %hyd  "//  hyd"
    ==
  ::
  ++  render-site-with-indentation
    |=  s=site
    ^-  tape
    ?-    -.s
        %clq
      """
        if ( c3y == u3du({(r s.s)}) ) \{
          goto _{<z.s>};
        }
        else \{
          goto _{<o.s>};
        }
      """
    ::
        %eqq
      """
        if ( c3y == u3r_sing({(r l.s)}, {(r r.s)}) ) \{
          goto _{<z.s>};
        }
        else \{
          goto _{<o.s>};
        }
      """
    ::
        %brn
      """
        if ( c3y == u3x_loob({(r s.s)}) ) \{
          goto _{<z.s>};
        }
        else \{
            goto _{<o.s>};
          }
      """
    ::
        %hop
      "  goto _{<t.s>};"
    ::
        %hip
      ~|  %no-hip-in-c-source  !!
    ::
        %lnk
      ::  skip indirect nock for now
      ::
      stub
    ::
        %cal
      =/  callee  (~(got by bell-to-idx) a.s)
      """
        {(r d.s)} = _function_{<callee>}({(render-args-callee v.s)});
        goto _{<t.s>};
      """
    ::
        %caf
      $(s [%cal a v d t]:s)
    ::
        %lnt
      stub
    ::
        %jmp
      =/  callee  (~(got by bell-to-idx) a.s)
      "  return _function_{<callee>}({(render-args-callee v.s)});"
    ::
        %jmf
      $(s [%jmp a v]:s)
    ::
        %don
      "  return {(r s.s)};"
    ::
        %dom
      "  return {(render-noun r.s)};"
    ::
        %bom
      "  u3m_bail(c3__exit);"
    ::
        %mim
      ::  no %memo stuff for now
      stub
    ::
    ==
  ::
  ++  render-args-callee
    |=  v=(list @uvre)
    ^-  tape
    ?~  v  ""
    =/  out=tape  (r i.v)
    |-  ^-  tape
    ?~  t.v  out
    $(t.v t.t.v, out (weld out ", {(r i.t.v)}"))
  ::  XX make a jam buffer with all the nouns needed so we can reference it
  ::  later
  ::
  ::  XX large atoms
  ::
  ++  render-noun
    |=  n=*
    ^-  tape
    ?-  n
      @                  |2:(scow %ui n)
      [p=* q=@]          "u3nc({$(n p.n)}, {$(n q.n)})"
      [p=* q=* r=@]      "u3nt({$(n p.n)}, {$(n q.n)}, {$(n r.n)})"
      [p=* q=* r=* s=*]  "u3nq({$(n p.n)}, {$(n q.n)}, {$(n r.n)}, {$(n s.n)})"
    ==
  ::
  ++  r
    |=  r=@uvre
    ^-  tape
    "rs[{|2:(scow %ui r)}]"
  --
::
++  eval
  |=  [sub=* bel=bell]
  ^-  (unit *)
  =/  =straight  (~(got by code.lon) bel)
  =/  regs=(unit (map @uvre *))
    =|  regs=(map @uvre *)
    |-  ^-  (unit (map @uvre *))
    ?-    -.need.straight
        %none  `regs
        %this  `(~(put by regs) r.need.straight sub)
        %both  !!
    ::
        ^
      ?@  sub  ~
      =/  l  $(need.straight p.need.straight, sub -.sub)
      ?~  l  ~
      $(need.straight q.need.straight, sub +.sub, regs u.l)
    ==
  ::
  ?~  regs
    ~&  >>  %eval-init-split
    ~
  =/  gen
    :*
      ::  current function context
      ::
      arm=straight
      ::  register space
      ::
      regs=`(map @uvre *)`u.regs
      ::  code
      ::
      `=blob`(~(got by blocks.straight) direct-entrypoint)
      ::  come-from label
      ::
      hip=*@uwoo
    ==
  ::
  =>  .(gen `$+(gen _gen)`gen)
  =<  -
  |^  ^-  [(unit *) $+(gen _gen)]
  =*  block-loop  $
  ::  no phi stuff if +defi is applied
  ::  in this case ops-loop and block-loop are the same thing, and can be
  ::  modelled with a single loop
  ::
  ?>  =(~ phi.blob.gen)
  :: =?  gen  .?(phi.blob.gen)
  ::   %-  ~(rep by phi.blob.gen)
  ::   |=  [[destination=@uvre sources=(map @uwoo @uvre)] acc=_gen]
  ::   =.  gen  acc
  ::   =/  source=@uvre  (~(got by sources) hip.gen)
  ::   (r-put destination (r-get source))
  ::
  |-  ^-  [(unit *) $+(gen _gen)]
  =*  ops-loop  $
  ?:  =(~ body.blob.gen)
    =/  end  bend.blob.gen
    ?-    -.end
        %clq
      =/  s  (r-get s.end)
      ?^  s  block-loop(gen (hop z.end))
      block-loop(gen (hop o.end))
    ::
        %eqq
      =/  l  (r-get l.end)
      =/  r  (r-get r.end)
      ?:  =(l r)  block-loop(gen (hop z.end))
      block-loop(gen (hop o.end))
    ::
        %brn
      ?-  (r-get s.end)
        %&  block-loop(gen (hop z.end))
        %|  block-loop(gen (hop o.end))
        *   `gen
      ==
    ::
        %hop
      block-loop(gen (hop t.end))
    ::
        %hip
      =.  hip.gen  c.end
      block-loop(gen (hop t.end))
    ::
        %lnk
      =/  u  (r-get u.end)
      =/  f  (r-get f.end)
      ?~  res=(mole |.(.*(u f)))
        ~&  %indi-crash
        `gen
      =.  gen  (r-put d.end u.res)
      block-loop(gen (hop t.end))
    ::
        %cal
      =/  res=(unit *)
        =/  args-noun  (turn v.end r-get)
        =/  arm-new  (~(got by code.lon) a.end)
        =.  gen  [arm-new ~ (~(got by blocks.arm-new) direct-entrypoint) *@uwoo]
        =.  gen  (r-puts (span-args n-args.arm-new) args-noun)
        -:block-loop
      ::
      ?~  res  `gen
      =.  gen  (r-put d.end u.res)
      block-loop(gen (hop t.end))
    ::
        %caf
      ::  no jet stuff now
      ::
      ops-loop(bend.blob.gen [%cal a v d t]:end)
    ::
        %lnt
      =/  u  (r-get u.end)
      =/  f  (r-get f.end)
      ?~  res=(mole |.(.*(u f)))
        ~&  %indi-crash
        `gen
      [res gen]
    ::
        %jmp
      =/  args-noun  (turn v.end r-get)
      =/  arm-new  (~(got by code.lon) a.end)
      =.  gen  [arm-new ~ (~(got by blocks.arm-new) direct-entrypoint) *@uwoo]
      =.  gen  (r-puts (span-args n-args.arm-new) args-noun)
      block-loop
    ::
        %jmf
      ::  no jet stuff now
      ::
      ops-loop(bend.blob.gen [%jmp a v]:end)
    ::
        %don
      [`(r-get s.end) gen]
    ::
        %dom
      [`r.end gen]
    ::
        %bom
      `gen
    ::
        %mim
      ~|  %no-memo-now
      stub
    ::
    ==
  =^  op=pole  body.blob.gen  body.blob.gen
  =-  ?~  -  `gen  ops-loop(gen u)
  ^-  (unit $+(gen _gen))
  ?-    -.op
      %imm
    :-  ~
    (r-put d.op n.op)
  ::
      %mov
    :-  ~
    =/  n  (r-get s.op)
    (r-put d.op n)
  ::
      %inc
    =/  n  (r-get s.op)
    ?^  n  ~
    `(r-put d.op +(n))
  ::
      %con
    :-  ~
    =/  h  (r-get h.op)
    =/  t  (r-get t.op)
    (r-put d.op [h t])
  ::
      %hed
    :-  ~
    =/  n  (r-get s.op)
    ?^  n  (r-put d.op -.n)
    ~&  >>  %hed-atom
    (r-put d.op %hed-atom)
  ::
      %tal
    :-  ~
    =/  n  (r-get s.op)
    ?^  n  (r-put d.op +.n)
    ~&  >>  %tal-atom
    (r-put d.op %tal-atom)
  ::
      %cel
    =/  p  (r-get p.op)
    ?@  p  ~
    `gen
  ::
      %his
    `gen
  ::
      %hos
    `gen
  ::
      %hid
    :-  ~
    ?+    n.op  gen
      ::   %spot
      :: =/  tok  (r-get p.op)
      :: ?~  pot=((soft spot) tok)  gen
      :: ~>  %slog.[0 (ren:p u.pot)]
      :: gen
    ::
        %slog
      =/  tok  (r-get p.op)
      ~&  tok
      gen
    ==
  ::
      %hod
    `gen
  ::
      %spy
    :-  ~
    =/  e  (r-get e.op)
    =/  p  (r-get p.op)
    =/  pro  .*(~ [%12 1+e 1+p])
    (r-put d.op pro)
  ::
      %mem
    ~|  %no-memo-now
    stub
  ::
      %hys  `gen
      %hyd  `gen
  ::
  ==
  ::
  ++  r-get
    |=  r=@uvre
    ^-  *
    =/  n  (~(get by regs.gen) r)
    ?~  n
      ~&  >>  %r-get-missing-register
      ~
    u.n
  ::
  ++  r-put
    |=  [r=@uvre x=*]
    ^+  gen
    =.  regs.gen  (~(put by regs.gen) r x)
    gen
  ::
  ++  r-puts
    |=  [rs=(list @uvre) xs=(list *)]
    ^+  gen
    ?~  rs
      ?^  xs  !!
      gen
    =.  gen  (r-put i.rs -.xs)
    $(rs t.rs, xs +.xs)
  ::
  ++  hop
    |=  o=@uwoo
    ^+  gen
    ~|  %no-block
    ~|  o
    gen(blob (~(got by blocks.arm.gen) o))
  --
::
++  compile-all
  |=  code=(map bell nomm-1)
  ^+  this
  %-  ~(rep by code)
  |=  [[k=bell *] acc=_this]
  =.  lon  lon.acc
  (compile k)
::
++  compile
  |=  =bell
  ^+  this
  =/  meme-args  (~(got by arity.lon) bell)
  =|  gen=line-short
  =.  -.gen  lon
  ::
  =^  nex=next  gen  (~(cuts line gen) bell branches-shapes.meme-args)
  ::
  =^  [args-need=need args-list=(list @uvre)]  gen
    (~(shape-to-need line gen) shape-final.meme-args)
  ::
  =.  gen
    ~|  line-need+what.nex
    ~|  arity-need+args-need
    ~|  arity+shape-final.meme-args
    (~(coerce line gen) nex args-need bus.bell)
  ::
  =/  blocks  blocks.here.gen
  =.  blocks  (remove-hops blocks)
  =.  blocks  (remove-movs blocks)
  =^  old-to-new  blocks
    (rewrite-registers-from-start blocks args-list)
  ::  defi needs to be last: the registers are no longer single-assignment
  ::  and multiple blocks can be targeted with %hop's
  ::
  =.  blocks  (defi blocks)
  =.  args-need
    |-  ^-  need
    ?^  -.args-need  [$(args-need -.args-need) $(args-need +.args-need)]
    ?:  ?=(%none -.args-need)  args-need
    ?:  ?=(%both -.args-need)  !!
    args-need(r (~(got by old-to-new) r.args-need))
  ::
  =.  code.lon
    %+  ~(put by code.lon)  bell
    :: =-  ~&(code+- -)
    ^-  straight
    [args-need (lent args-list) blocks bell]
  ::
  this
::  simplify interpretation by replacing phi tables with moves and %hip's with
::  %hop's
::
++  defi
  |=  blocks=(map @uwoo blob)
  ^+  blocks
  =|  new-blocks=(map @uwoo blob)
  =/  here-o=@uwoo  direct-entrypoint
  =/  here=blob  (~(got by blocks) here-o)
  |^  ^+  blocks
  ?-    -.bend.here
      ?(%don %dom %bom %lnt %jmp %jmf)
    (~(put by new-blocks) here-o here)
  ::
      ?(%lnk %cal %caf %hop)
    =/  t=@uwoo  (get-target bend.here)
    =.  new-blocks  $(here (~(got by blocks) t), here-o t)
    (~(put by new-blocks) here-o here)
  ::
      ?(%clq %eqq %brn %mim)
    =/  [z=@uwoo o=@uwoo]  (get-z-o bend.here)
    =.  new-blocks  $(here (~(got by blocks) z), here-o z)
    =.  new-blocks  $(here (~(got by blocks) o), here-o o)
    (~(put by new-blocks) here-o here)
  ::
      %hip
    =/  t  t.bend.here
    =/  target-blob  (~(got by blocks) t)
    =.  new-blocks  $(here target-blob, here-o t)
    =.  new-blocks  (~(put by new-blocks) t target-blob(phi ~))
    =/  moves=(list [from=@uvre to=@uvre])
      %-  ~(rep by phi.target-blob)
      |=  [[k-reg-to=@uvre v=(map @uwoo @uvre)] acc=(list [@uvre @uvre])]
      ?~  from=(~(get by v) c.bend.here)
        ~&  >>>  %hip-weird
        acc
      [[u.from k-reg-to] acc]
    ::
    %+  ~(put by new-blocks)  here-o
    %=  here
      bend  [%hop t.bend.here]
      body  (welp body.here (turn moves (lead %mov)))
    ==
  ==
  ::
  ++  get-target
    |=  s=_`$>(?(%hop %lnk %cal %caf) site)`[%hop *@uw]
    ^-  @uwoo
    ?-  -.s
      %hop  t.s
      %lnk  t.s
      %cal  t.s
      %caf  t.s
    ==
  ::
  ++  get-z-o
    |=  s=$>(?(%clq %eqq %brn %mim) site)
    ^-  [@uwoo @uwoo]
    ?-  -.s
      %clq  [z.s o.s]
      %eqq  [z.s o.s]
      %brn  [z.s o.s]
      %mim  [z.s o.s]
    ==
  -- 
::  if block A %hop's to block B, then block B is necessarily only targeted
::  by A, as control flow merges are done with %hip's. This means that blocks A
::  and B can be safely merged into one block without any code duplication
::
++  remove-hops
  |=  blocks=(map @uwoo blob)
  ^+  blocks
  =|  new-blocks=(map @uwoo blob)
  =/  here-o=@uwoo  direct-entrypoint
  =/  here=blob  (~(got by blocks) here-o)
  |^  ^+  blocks
  ?-    -.bend.here
      ?(%don %dom %bom %lnt %jmp %jmf)
    (~(put by new-blocks) here-o here)
  ::
      ?(%hip %lnk %cal %caf)
    =/  t=@uwoo  (get-target bend.here)
    =.  new-blocks  $(here (~(got by blocks) t), here-o t)
    (~(put by new-blocks) here-o here)
  ::
      ?(%clq %eqq %brn %mim)
    =/  [z=@uwoo o=@uwoo]  (get-z-o bend.here)
    =.  new-blocks  $(here (~(got by blocks) z), here-o z)
    =.  new-blocks  $(here (~(got by blocks) o), here-o o)
    (~(put by new-blocks) here-o here)
  ::
      %hop
    =/  next  (~(got by blocks) t.bend.here)
    ?^  phi.next  !!
    =.  new-blocks  $(here next, here-o t.bend.here)
    =/  next  (~(got by new-blocks) t.bend.here)
    ::  sanity check: the target block must not have a phi table as it is not
    ::  targeted with %hip
    ::
    ?^  phi.next  !!
    =.  new-blocks
      =/  merged  [phi.here (weld body.here body.next) bend.next]
      (~(put by new-blocks) here-o merged)
    ::
    (~(del by new-blocks) t.bend.here)
  ==
  ::
  ++  get-target
    |=  s=_`$>(?(%hip %lnk %cal %caf) site)`[%hip *@uw *@uw]
    ^-  @uwoo
    ?-  -.s
      %hip  t.s
      %lnk  t.s
      %cal  t.s
      %caf  t.s
    ==
  ::
  ++  get-z-o
    |=  s=$>(?(%clq %eqq %brn %mim) site)
    ^-  [@uwoo @uwoo]
    ?-  -.s
      %clq  [z.s o.s]
      %eqq  [z.s o.s]
      %brn  [z.s o.s]
      %mim  [z.s o.s]
    ==
  --
::  As we generate the code from the end to the beginning, we do not know if
::  two given register will contain the same data, so we generate %mov
::  instructions (that are actually copies) when we learn that two registers
::  correspond to the same noun.
::
::  But once we generated all the code for a function, we know which registers
::  are mere aliases, so we can eliminate the moves and instead rename the
::  registers
::
++  remove-movs
  |=  blocks=(map @uwoo blob)
  ^+  blocks
  =/  here-o=@uwoo  direct-entrypoint
  =/  here=blob  (~(got by blocks) here-o)
  =|  gen=[new-blocks=(map @uwoo blob) old-to-new=(map @uvre @uvre)]
  =<  -
  |^  ^+  gen
  =/  phi  (update-phi phi.here)
  =^  body  gen  (update-body body.here)
  =/  site  (update-site bend.here)
  =.  new-blocks.gen  (~(put by new-blocks.gen) here-o [phi body site])
  ?-    -.bend.here
      ?(%don %dom %bom %lnt %jmp %jmf)  gen
  ::
      ?(%hip %lnk %cal %caf %hop)
    =/  t=@uwoo  (get-target bend.here)
    $(here (~(got by blocks) t), here-o t)
  ::
      ?(%clq %eqq %brn %mim)
    =/  [z=@uwoo o=@uwoo]  (get-z-o bend.here)
    =.  gen  $(here (~(got by blocks) z), here-o z)
    $(here (~(got by blocks) o), here-o o)
  ==
  ::
  ++  update-phi
    |=  phi=(map @uvre (map @uwoo @uvre))
    ^+  phi
    %-  ~(rep by phi)
    |=  $:  [k-out=@uvre v-out=(map @uwoo @uvre)]
            phi-new=(map @uvre (map @uwoo @uvre))
        ==
    =/  k-out-new=@uvre  (update-r k-out)
    =-  (~(put by phi-new) k-out-new -)
    %-  ~(rep by v-out)
    |=  [[k-in=@uwoo v-in=@uvre] v-out-new=(map @uwoo @uvre)]
    (~(put by v-out-new) k-in (update-r v-in))
  ::
  ++  update-body
    |=  body=(list pole)
    ^+  [body gen]
    =|  new-body=(list pole)
    =-  -(b (flop b))
    |-  ^+  [b=new-body gen]
    ?~  body  [new-body gen]
    ?:  ?=(%mov -.i.body)
      =,  i.body
      ?~  old=(~(get by old-to-new.gen) s)
        $(body t.body, old-to-new.gen (~(put by old-to-new.gen) d s))
      $(body t.body, old-to-new.gen (~(put by old-to-new.gen) d u.old))
    =-  $(body t.body, new-body [- new-body])
    ^-  pole
    =*  op  i.body
    ?-  -.op
      ?(%his %hos)  op
      %imm  op(d (update-r d.op))
      %inc  op(d (update-r d.op), s (update-r s.op))
      %con  op(h (update-r h.op), t (update-r t.op), d (update-r d.op))
      %hed  op(d (update-r d.op), s (update-r s.op))
      %tal  op(d (update-r d.op), s (update-r s.op))
      %cel  op(p (update-r p.op))
      %hid  op(p (update-r p.op))
      %hod  op(p (update-r p.op))
      %spy  op(e (update-r e.op), p (update-r p.op), d (update-r d.op))
      %mem  op(k (update-r k.op), s (update-r s.op), r (update-r r.op))
      %hys  op(p (update-r p.op))
      %hyd  op(p (update-r p.op), q (update-r q.op))
    ==
  ::
  ++  update-r
    |=  r=@uvre
    ^-  @uvre
    (~(gut by old-to-new.gen) r r)
  ::
  ++  update-site
    |=  =site
    ^+  site
    ?-  -.site
      %clq  site(s (update-r s.site))
      %eqq  site(l (update-r l.site), r (update-r r.site))
      %brn  site(s (update-r s.site))
      %hop  site
      %hip  site
      %lnk  site(u (update-r u.site), f (update-r f.site), d (update-r d.site))
      %cal  site(d (update-r d.site), v (turn v.site update-r))
      %caf  site(d (update-r d.site), v (turn v.site update-r), u (update-r u.site))
      %lnt  site(u (update-r u.site), f (update-r f.site))
      %jmp  site(v (turn v.site update-r))
      %jmf  site(v (turn v.site update-r), u (update-r u.site))
      %don  site(s (update-r s.site))
      %bom  site
      %dom  site
      %mim  site(k (update-r k.site), s (update-r s.site), d (update-r d.site))
    ==
  ::
  ++  get-target
    |=  s=_`$>(?(%hop %hip %lnk %cal %caf) site)`[%hip *@uw *@uw]
    ^-  @uwoo
    ?-  -.s
      %hop  t.s
      %hip  t.s
      %lnk  t.s
      %cal  t.s
      %caf  t.s
    ==
  ::
  ++  get-z-o
    |=  s=$>(?(%clq %eqq %brn %mim) site)
    ^-  [@uwoo @uwoo]
    ?-  -.s
      %clq  [z.s o.s]
      %eqq  [z.s o.s]
      %brn  [z.s o.s]
      %mim  [z.s o.s]
    ==
  --
::  To make the calling convention simpler we want the argument registers to
::  be sequential values (0v0, 0v1, 0v2, ...), but since we codegen from the end
::  to the beginning, the input registers end up having high values, and return
::  registers are low.
::  So, once we have all the code for a function, we iterate from the beginning
::  to the end, renaming the registers.
::
++  rewrite-registers-from-start
  |=  [blocks=(map @uwoo blob) args-old=(list @uvre)]
  ^-  [(map @uvre @uvre) _blocks]
  =|  gen=[new-reg=@uvre old-to-new=(map @uvre @uvre)]
  |^
  =.  gen
    ::  we iterate over the old argument registers first so that they are
    ::  sequential
    ::
    |-  ^+  gen
    ?~  args-old  gen
    =^  new  gen  next-new-reg
    =.  old-to-new.gen  (~(put by old-to-new.gen) i.args-old new)
    $(args-old t.args-old)
  ::
  =<  [+> -]
  %-  ~(rep by blocks)
  |=  [[k=@uwoo v=blob] acc=[new-blocks=(map @uwoo blob) _gen=gen]]
  ^+  acc
  =.  gen  gen.acc
  =^  new-blob  gen  (rewrite-blob v)
  [(~(put by new-blocks.acc) k new-blob) gen]
  ::
  ++  rewrite-blob
    |=  =blob
    ^+  [blob gen]
    =^  phi-new   gen  (rewrite-phi phi.blob)
    =^  body-new  gen  (rewrite-body body.blob)
    =^  site-new  gen  (rewrite-site bend.blob)
    [[phi-new body-new site-new] gen]
  ::
  ++  rewrite-phi
    |=  phi=(map @uvre (map @uwoo @uvre))
    ^+  [phi gen]
    %-  ~(rep by phi)
    |=  [[k=@uvre v=(map @uwoo @uvre)] acc=_[phi-new=`_phi`~ gen=gen]]
    =.  gen  gen.acc
    =^  k-new  gen  (old-to-new k)
    =^  v-new  gen
      %-  ~(rep by v)
      |=  [[k-in=@uwoo v-in=@uvre] acc-in=_[v-new=*(map @uwoo @uvre) gen=gen]]
      =.  gen  gen.acc-in
      =^  v-in-new  gen  (old-to-new v-in)
      [(~(put by v-new.acc-in) k-in v-in-new) gen]
    ::
    [(~(put by phi-new.acc) k-new v-new) gen]
  ::
  ++  next-new-reg
    ^-  [@uvre _gen]
    [new-reg.gen gen(new-reg +(new-reg.gen))]
  ::
  ++  old-to-new
    |=  old=@uvre
    ^-  [@uvre _gen]
    ?^  val=(~(get by old-to-new.gen) old)  [u.val gen]
    =^  new  gen  next-new-reg
    =.  old-to-new.gen  (~(put by old-to-new.gen) old new)
    [new gen]
  ::
  ++  rewrite-body
    |=  body=(list pole)
    ^+  [body gen]
    =-  -(l-out (flop l-out))
    %+  roll  body
    |=  [i=pole acc=_[l-out=*(list pole) gen=gen]]
    ^+  acc
    =.  gen  gen.acc
    =^  i-new  gen  (rewrite-pole i)
    [[i-new l-out.acc] gen]
  ::
  ++  rewrite-site
    |=  =site
    ^+  [site gen]
    ?-    -.site
        %clq
      =^  s-new  gen  (old-to-new s.site)
      [site(s s-new) gen]
    ::
        %eqq
      =^  l-new  gen  (old-to-new l.site)
      =^  r-new  gen  (old-to-new r.site)
      [site(l l-new, r r-new) gen]
    ::
        %brn
      =^  s-new  gen  (old-to-new s.site)
      [site(s s-new) gen]
    ::
        %hop
      [site gen]
    ::
        %dom
      [site gen]
    ::
        %hip
      [site gen]
    ::
        %lnk
      =^  u-new  gen  (old-to-new u.site)
      =^  f-new  gen  (old-to-new f.site)
      =^  d-new  gen  (old-to-new d.site)
      [site(u u-new, f f-new, d d-new) gen]
    ::
        %cal
      =^  v-new  gen
        =-  -(v-out (flop v-out))
        %+  roll  v.site
        |=  [i=@uvre acc=_[v-out=*(list @uvre) gen=gen]]
        =.  gen  gen.acc
        =^  i-new  gen  (old-to-new i)
        [[i-new v-out.acc] gen]
      ::
      =^  d-new  gen  (old-to-new d.site)
      [site(v v-new, d d-new) gen]
    ::
        %caf
      =^  v-new  gen
        =-  -(v-out (flop v-out))
        %+  roll  v.site
        |=  [i=@uvre acc=_[v-out=*(list @uvre) gen=gen]]
        =.  gen  gen.acc
        =^  i-new  gen  (old-to-new i)
        [[i-new v-out.acc] gen]
      ::
      =^  d-new  gen  (old-to-new d.site)
      =^  u-new  gen  (old-to-new u.site)
      [site(v v-new, d d-new, u u-new) gen]
    ::
        %lnt
      =^  u-new  gen  (old-to-new u.site)
      =^  f-new  gen  (old-to-new f.site)
      [site(u u-new, f f-new) gen]
    ::
        %jmp
      =^  v-new  gen
        =-  -(v-out (flop v-out))
        %+  roll  v.site
        |=  [i=@uvre acc=_[v-out=*(list @uvre) gen=gen]]
        =.  gen  gen.acc
        =^  i-new  gen  (old-to-new i)
        [[i-new v-out.acc] gen]
      ::
      [site(v v-new) gen]
    ::
        %jmf
      =^  v-new  gen
        =-  -(v-out (flop v-out))
        %+  roll  v.site
        |=  [i=@uvre acc=_[v-out=*(list @uvre) gen=gen]]
        =.  gen  gen.acc
        =^  i-new  gen  (old-to-new i)
        [[i-new v-out.acc] gen]
      ::
      =^  u-new  gen  (old-to-new u.site)
      [site(v v-new, u u-new) gen]
    ::
        %don
      =^  s-new  gen  (old-to-new s.site)
      [site(s s-new) gen]
    ::
        %bom
      [site gen]
    ::
        %mim
      =^  k-new  gen  (old-to-new k.site)
      =^  s-new  gen  (old-to-new s.site)
      =^  d-new  gen  (old-to-new d.site)
      [site(k k-new, s s-new, d d-new) gen]
    ==
  ::
  ++  rewrite-pole
    |=  =pole
    ^+  [pole gen]
    ?-    -.pole
        %imm
      =^  d-new  gen  (old-to-new d.pole)
      [pole(d d-new) gen]
    ::
        ?(%mov %inc %hed %tal)
      =^  s-new  gen  (old-to-new s.pole)
      =^  d-new  gen  (old-to-new d.pole)
      [pole(d d-new, s s-new) gen]
    ::
        %con
      =^  h-new  gen  (old-to-new h.pole)
      =^  t-new  gen  (old-to-new t.pole)
      =^  d-new  gen  (old-to-new d.pole)
      [pole(d d-new, h h-new, t t-new) gen]
    ::
        %cel
      =^  p-new  gen  (old-to-new p.pole)
      [pole(p p-new) gen]
    ::
        %his
      [pole gen]
    ::
        %hos
      [pole gen]
    ::
        %hid
      =^  p-new  gen  (old-to-new p.pole)
      [pole(p p-new) gen]
    ::
        %hod
      =^  p-new  gen  (old-to-new p.pole)
      [pole(p p-new) gen]
    ::
        %spy
      =^  e-new  gen  (old-to-new e.pole)
      =^  p-new  gen  (old-to-new p.pole)
      =^  d-new  gen  (old-to-new d.pole)
      [pole(d d-new, e e-new, p p-new) gen]
    ::
        %mem
      =^  k-new  gen  (old-to-new k.pole)
      =^  s-new  gen  (old-to-new s.pole)
      =^  r-new  gen  (old-to-new r.pole)
      [pole(k k-new, s s-new, r r-new) gen]
    ::
        %hys
      =^  p-new  gen  (old-to-new p.pole)
      [pole(p p-new) gen]
    ::
        %hyd
      =^  p-new  gen  (old-to-new p.pole)
      =^  q-new  gen  (old-to-new q.pole)
      [pole(p p-new, q q-new) gen]
    ==
  --
::
++  line
  |_  gen=line-short
  ::  given argument need from arity prepass, satisfy entry point need with it,
  ::  or satisfy the need with the noun from `bus` if known, or crash
  ::
  ::  this is where the very first code is emitted, and this code is bound
  ::  to hard-coded 0w1 entry point
  ::
  ::  XX need to update the arity and redo the linearization step for
  ::  completeness
  ::
  ++  coerce
    |=  [entry=next args=need bus=sock]
    ^+  gen
    =^  ops=(list pole)  gen  (coerce-ops what.entry args bus)
    (emir direct-entrypoint ~ ops %hop then.entry)
  ::
  ++  coerce-ops
    |=  [entry=need args=need bus=sock]
    ^-  [(list pole) _gen]
    ::  ops1: instructions to move args into registers before entry,
    ::       or to fill those with constants, or cons them up
    ::
    ::  ops2: instructions that split these intermediary regs into what.entry
    ::
    =|  acc=[ops1=(list pole) ops2=(list pole) =_gen]
    =;  acc-out=_acc  [(weld ops1.acc-out ops2.acc-out) gen.acc-out]
    |-  ^+  acc
    ::  easy ways out:
    ::
    ::  nothing needed
    ::
    ?:  ?=(%none -.entry)  acc
    ::  noun is known
    ::
    ?:  ?=(%& cape.bus)
      =^  [prod=@uvre ops=(list pole)]  gen.acc  (kern(gen gen.acc) entry)
      =.  ops1.acc  [[%imm data.bus prod] ops1.acc]
      =.  ops2.acc  (weld ops ops2.acc)
      acc
    ::  argument has all
    ::
    ?:  ?=(%this -.args)
      =^  [prod=@uvre ops=(list pole)]  gen.acc  (kern(gen gen.acc) entry)
      =.  ops1.acc  [[%mov r.args prod] ops1.acc]
      =.  ops2.acc  (weld ops ops2.acc)
      acc
    ::
    ::  now we assert
    ::
    ?:  ?=(%none -.args)  ~|(%coerce-lost !!)
    ::  shape-to-need never produces %both
    ::
    ?:  ?=(%both -.args)  !!
    ?:  ?=(^ -.entry)
      =.  acc  $(entry p.entry, args p.args, bus ~(hed so bus))
      $(entry q.entry, args q.args, bus ~(tel so bus))
    ~&  >>  %coerce-entry-greedier-than-args
    ?:  ?=(%this -.entry)
      =^  r-h  gen.acc  re(gen gen.acc)
      =^  r-t  gen.acc  re(gen gen.acc)
      =.  ops1.acc  [[%con r-h r-t r.entry] ops1.acc]
      =.  acc  $(entry this+r-h, args p.args, bus ~(hed so bus))
      $(entry this+r-t, args q.args, bus ~(tel so bus))
    =^  h=[prod=@uvre ops=(list pole)]  gen.acc  (kern(gen gen.acc) h.entry)
    =^  t=[prod=@uvre ops=(list pole)]  gen.acc  (kern(gen gen.acc) t.entry)
    =.  ops1.acc  [[%con prod.h prod.t r.entry] ops1.acc]
    =.  ops2.acc  :(weld ops.t ops.h ops2.acc)
    =.  acc  $(entry this+prod.h, args p.args, bus ~(hed so bus))
    $(entry this+prod.t, args q.args, bus ~(tel so bus))
  ::  core linearizer
  ::
  ++  cuts
    =/  axe-2-p=@  6
    =/  axe-2-uq=@
      ;;  @  =<  +  !.
      =>  `nomm-1`[%2 *nomm-1 `*nomm-1 ~]
      ?>  ?=(%2 -)
      ?@  q  !!
      ;;  [%0 @]  !=
      u.q
    ::
    =/  axe-11-qp=@
      ;;  @  =<  +  !.
      =>  `nomm-1`[%11 [0 *nomm-1] *nomm-1 ~]
      ?>  ?=(%11 -)
      ?@  p  !!
      ;;  [%0 @]  !=
      q.p
    ::
    =/  axe-11-q=@
      ;;  @  =<  +  !.
      =>  `nomm-1`[%11 0 *nomm-1 ~]
      ?>  ?=(%11 -)
      ;;  [%0 @]  !=
      q
    ::
    ?>  =(axe-11-q 14)
    ?>  =(axe-11-qp 13)
    ?>  =(axe-2-uq 29)
    ::
    =/  =goal  [%done ~]
    |=  [=bell branches-shapes=(map @axis shape-final)]
    ^-  [next line-short]
    =/  nomm=nomm-1  (~(got by code.boil.gen) bell)
    =/  pos=@axis  `@`1
    |-  ^-  [next _gen]
    ?-    -.nomm
        ^
      ?-    -.goal
          %done
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %don r)
        $(goal [%next [%this r] o])
      ::
          %pick
        bomb
      ::
          %next
        =^  [hed=need tel=need t=@uwoo]  gen  (split goal)
        =^  next-2  gen  $(nomm +.nomm, goal [%next tel t], pos (peg pos 2))
        =^  next-1  gen
          $(nomm -.nomm, goal [%next hed then.next-2], pos (peg pos 3))
        ::
        (copy next-1 what.next-2)
      ==
    ::
        %0
      ?:  =(0 p.nomm)  bomb
      =^  goal  gen  (simple-next goal)
      [[%next (from p.nomm what.goal) then.goal] gen]        
    ::
        %1
      ?-    -.goal
          %done
        =^  o  gen  (emit ~ ~ %dom p.nomm)
        [[%next none+~ o] gen]
      ::
          %pick
        ?+  p.nomm  bomb
          %0  [[%next [%none ~] zero.goal] gen]
          %1  [[%next [%none ~] once.goal] gen]
        ==
      ::
          %next
        =^  o  gen  (mede then.goal p.nomm what.goal)
        [[%next none+~ o] gen]
      ==
    ::
        %2
      ?:  ?=(%pick -.goal)
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %brn r [zero once]:goal)
        $(goal [%next [%this r] o])
      ?~  info.nomm
        ::  indirect call
        ::
        ?~  q.nomm  !!
        =^  s  gen  re
        =^  f  gen  re
        ::  build block to jump from formula execution,
        ::  splitting result to register in need if necessary
        ::
        =^  o  gen
          ?-    -.goal
              %done  (emit ~ ~ %lnt s f)
          ::
              %next
            =^  [aftr=@uwoo prod=@uvre]  gen  (kerf goal)
            (emit ~ ~ %lnk s f prod aftr)
          ==
        ::
        =^  need-f  gen
          $(nomm u.q.nomm, goal [%next this+f o], pos (peg pos axe-2-uq))
        ::
        =^  need-s  gen
          $(nomm p.nomm, goal [%next this+s then.need-f], pos (peg pos axe-2-p))
        ::
        (copy need-s what.need-f)
      =/  meme-args  (~(got by arity.gen) u.info.nomm)
      =^  [args-need=need args-list=(list @uvre)]  gen
        (shape-to-need shape-final.meme-args)
      ::
      ::  XX no jet stuff for now
      ::
      =^  tar=@uwoo  gen
        ?-    -.goal
            %done  (emit ~ ~ %jmp u.info.nomm args-list)
        ::
            %next
          =^  [aftr=@uwoo prod=@uvre]  gen  (kerf goal)
          (emit ~ ~ %cal u.info.nomm args-list prod aftr)
        ==
      ::
      =^  fol-next=next  gen
        ::  if the formula-formula was removed: do nothing
        ::  else compute formula-formula and drop the result to preserve crashes
        ::
        ?~  q.nomm  [[%next none+~ tar] gen]
        $(nomm u.q.nomm, goal [%next none+~ tar], pos (peg pos axe-2-uq))
      ::
      =^  sub-next  gen
        =*  g  [%next args-need then.fol-next]
        $(nomm p.nomm, goal g, pos (peg pos axe-2-p))
      (copy sub-next what.fol-next)
    ::
        %3
      ?-    -.goal
          %done
        =^  r-0  gen  re
        =^  r-1  gen  re
        =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
        =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
        $(goal [%pick o-0 o-1])
      ::
          %next
        ?:  ?=(?(^ %both) -.what.goal)
          ?.  ?=([%both @ %& *] what.goal)  bomb
          (mine r.what.goal then.goal)
        ?:  ?=(%none -.what.goal)
          ::  the product will be discarded anyway, no checks necessary
          ::
          $(nomm p.nomm, pos (peg pos 3))
        =^  [z=@uwoo o=@uwoo]  gen  (phin r.what.goal then.goal)
        $(goal [%pick z o])
      ::
          %pick
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %clq r [zero once]:goal)
        $(nomm p.nomm, goal [%next [%this r] o], pos (peg pos 3))
      ==
    ::
        %4
      ?-    -.goal
          %done
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o     gen  (emit ~ [%inc arg pro]~ %don pro)
        $(nomm p.nomm, goal [%next [%this arg] o], pos (peg pos 3))
      ::
          %pick
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o     gen  (emit ~ [%inc arg pro]~ %brn pro [zero once]:goal)
        $(nomm p.nomm, goal [%next [%this arg] o], pos (peg pos 3))
      ::
          %next
        ?:  ?=(?(^ %both) -.what.goal)
          ?.  ?=([%both @ %& *] what.goal)  bomb
          (mine r.what.goal then.goal)
        =^  pro  gen
          ?:  ?=(%none -.what.goal)  re
          [r.what.goal gen]
        ::
        =^  arg  gen  re
        =^  o     gen  (emit ~ [%inc arg pro]~ %hop then.goal)
        $(nomm p.nomm, goal [%next [%this arg] o], pos (peg pos 3))
      ==
    ::
        %5
      ?-    -.goal
          %done
        =^  r-0  gen  re
        =^  r-1  gen  re
        =^  o-0  gen  (emit ~ [%imm 0 r-0]~ %don r-0)
        =^  o-1  gen  (emit ~ [%imm 1 r-1]~ %don r-1)
        $(goal [%pick o-0 o-1])
      ::
          %next
        ?:  ?=(?(^ %both) -.what.goal)
          ?.  ?=([%both @ %& *] what.goal)  bomb
          (mine r.what.goal then.goal)
        ?:  ?=(%none -.what.goal)
          ::  kinda like autocons compilation, since we drop the result
          ::  and the op never crashes
          ::
          =^  next-q  gen  $(nomm q.nomm, pos (peg pos 7))
          =^  next-p  gen
            $(nomm p.nomm, then.goal then.next-q, pos (peg pos 6))
          ::
          (copy next-p what.next-q)
        =^  [z=@uwoo o=@uwoo]  gen  (phin r.what.goal then.goal)
        $(goal [%pick z o])
      ::
          %pick
        =^  r-p     gen  re
        =^  r-q     gen  re
        =^  o       gen  (emit ~ ~ %eqq r-p r-q [zero once]:goal)
        =^  next-q  gen
          $(nomm q.nomm, goal [%next [%this r-q] o], pos (peg pos 7))
        ::
        =^  next-p  gen
          $(nomm p.nomm, goal [%next [%this r-p] then.next-q], pos (peg pos 6))
        ::
        (copy next-p what.next-q)
      ::
      ==
    ::
        %6
      =^  [goal-0=^goal goal-1=^goal]  gen
        ?:  ?=(%next -.goal)  (phil goal)
        [[goal goal] gen]
      ::
      =^  next-1  gen  $(nomm r.nomm, goal goal-1, pos (peg pos 15))
      =^  next-0  gen  $(nomm q.nomm, goal goal-0, pos (peg pos 14))
      ::
      ::  XX feels strange... maybe we should have info about the exclusive
      ::  data usage by the branches and use that to pessimize if the actual
      ::  registerizations happen to use stuff from those places?
      ::
      =^  [both=need *]  gen  (shape-to-need (~(got by branches-shapes) pos))
      =^  ops-o  gen  (coerce-ops what.next-1 both |+~)
      =^  ops-z  gen  (coerce-ops what.next-0 both |+~)
      =^  then   gen  (emit ~ ops-z %hop then.next-0)
      =^  else   gen  (emit ~ ops-o %hop then.next-1)
      =^  cond   gen  $(nomm p.nomm, goal [%pick then else], pos (peg pos 6))
      (copy cond both)
    ::
        %7
      =^  nex  gen  $(nomm q.nomm, pos (peg pos 7))
      $(nomm p.nomm, goal nex, pos (peg pos 6))
    ::
        %10
      ?-    -.goal
          %done
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %don r)
        $(goal [%next [%this r] o])
      ::
          %pick
        ?.  =(p.p.nomm 1)  bomb
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %brn r [zero once]:goal)
        $(goal [%next [%this r] o])
      ::
          %next
        =^  [don=need rec=need o=@uwoo]  gen  (into p.p.nomm goal)
        =^  next-rec  gen  $(nomm q.nomm, goal [%next rec o], pos (peg pos 7))
        =^  next-don  gen
          $(nomm q.p.nomm, goal [%next don then.next-rec], pos (peg pos 13))
        ::
        (copy next-don what.next-rec)
      ::
      ==
    ::
        %11
      ?@  p.nomm
        ::  Atomic hint
        ::
        ?.  ?=(hint-static p.nomm)  $(nomm q.nomm, pos (peg pos axe-11-q))
        ?>  ?=(hint-static-mute p.nomm)
        =^  goal  gen  (simple-next goal)
        =^  epil  gen  (emit ~ [%hos p.nomm body.nomm]~ %hop then.goal)
        =^  nex   gen
          $(nomm q.nomm, goal goal(then epil), pos (peg pos axe-11-q))
        ::
        =^  prol  gen  (emit ~ [%his p.nomm body.nomm]~ %hop then.nex)
        [[%next what.nex prol] gen]
      ?:  ?=(%memo p.p.nomm)
        ::  %memo hint
        ::
        =^  key   gen  re
        =^  sub   gen  re
        =^  goal  gen  (simple-next goal)
        =^  [phi-hit=next phi-mis=next]  gen  (phil goal)
        ::  prod.hit will be filled by a cached value
        ::  prod.hit will be filled by the hinted formula and saved
        ::
        =^  hit=[aftr=@uwoo prod=@uvre]  gen  (kerf phi-hit)
        =^  mis=[aftr=@uwoo prod=@uvre]  gen  (kerf phi-mis)
        =^  next-mis  gen
          =^  save  gen
            (emit ~ [%mem key sub body.nomm prod.mis]~ %hop aftr.mis)
          ::
          $(nomm q.nomm, goal [%next this+prod.mis save], pos (peg pos axe-11-q))
        ::  unsatisfied so far: prod.hit, what.next-mis, sub
        ::  %mim will satisfy prod.hit or miss, only what.next-mis is left
        ::  so +sect is not needed to align the needs of branches
        ::
        =^  check  gen
          (emit ~ ~ %mim key sub body.nomm prod.hit aftr.hit then.next-mis)
        ::
        =^  next-key  gen
          $(nomm q.p.nomm, goal [%next this+key check], pos (peg pos axe-11-qp))
        ::
        =^  key-fol   gen  (copy next-key what.next-mis)
        ::  fill the subject register
        ::
        (copy key-fol this+sub)
      ::
      ::  Dynamic hint
      ::
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  nex  gen  $(nomm q.nomm, pos (peg pos axe-11-q))
        =^  hin  gen
          $(nomm q.p.nomm, goal [%next none+~ then.nex], pos (peg pos axe-11-qp))
        ::
        (copy hin what.nex)
      =^  goal  gen  (simple-next goal)
      =^  toke  gen  re
      =^  epil-ops=(list pole)  .
        ::  produce epilogue ops while potentially emitting code
        ::  to split the hinted formula's product into the registers
        ::  in the original need if the hint's epilogue needs the value
        ::  of the hinted formula
        ::
        ::  XX are there actually no hints that require the product of the
        ::  hinted formula besides %memo?
        ::
        =*  dot  .
        :: ?:  ?=(hint-dynamic-mute p.p.nomm)
          [[%hod p.p.nomm toke body.nomm]~ dot]
        :: =^  [aftr=@uwoo prod=@uvre]  gen  (kerf goal)
        :: [[%hyd p.p.nomm toke prod body.nomm]~ dot(goal [%next this+prod aftr])]
      ::
      =^  epil  gen  (emit ~ epil-ops %hop then.goal)
      =^  nex   gen
        $(nomm q.nomm, goal goal(then epil), pos (peg pos axe-11-q))
      ::
      ::  if the hint is not crash-relocation safe: put a relocation boundary
      ::
      =?  .  ?=(hint-dynamic-mute-stop p.p.nomm)
        =*  dot  .
        =^  top  gen  (stop nex)
        dot(nex top)
      ::
      =^  prol  gen  (emit ~ [%hid p.p.nomm toke body.nomm]~ %hop then.nex)
      =^  dyn   gen
        $(nomm q.p.nomm, goal [%next this+toke prol], pos (peg pos axe-11-qp))
      ::
      (copy dyn what.nex)
    ::
        %12
      =^  goal  gen  (simple-next goal)
      =^  [out=@uwoo pro=@uvre]  gen  (kerf goal)
      =^  r-path     gen  re
      =^  r-ref      gen  re
      =^  o-spy      gen  (emit ~ [%spy r-ref r-path pro]~ %hop out)
      =^  need-path  gen
        $(nomm q.nomm, goal [%next this+r-path o-spy], pos (peg pos 7))
      ::
      =^  need-ref   gen
        $(nomm p.nomm, goal [%next this+r-ref then.need-path], pos (peg pos 6))
      ::
      (copy need-ref what.need-path)
    ==
  ::
  ++  shape-to-need
    |=  shape=shape-final
    ^-  [[need (list @uvre)] _gen]
    =^  ned=need  gen
      |-  ^-  [need _gen]
      ?@  shape
        ?.  shape  [none+~ gen]
        =^  r  gen  re
        [this+r gen]
      =^  l  gen  $(shape -.shape)
      =^  r  gen  $(shape +.shape)
      [[l r] gen]
    ::
    :_  gen
    :-  ned
    |-  ^-  (list @uvre)
    ?-    -.ned
        %both  !!
        %none  ~
        %this  ~[r.ned]
        ^      (weld $(ned p.ned) $(ned q.ned))
    ==
  ::  simplify goal to next
  ::
  ++  simple-next
    |=  g=goal
    ^-  [next _gen]
    ?:  ?=(%next -.g)  [g gen]
    =^  r  gen  re
    =^  o  gen
      %^  emit  ~  ~
      ?:  ?=(%done -.g)  [%don r]
      [%brn r [zero once]:g]
    ::
    [[%next this+r o] gen]
  ::  place a crash relocation boundary
  ::
  ++  stop
    |=  nex=next
    ^-  [next _gen]
    =^  [ops=(list pole) ned=need]  gen  (aver what.nex)
    =^  o  gen  (emit ~ ops %hop then.nex)
    [[%next ned o] gen]
  ::  emit %cel asserts, update need
  ::
  ++  aver
    |=  ned=need
    ^-  [[(list pole) need] _gen]
    =|  acc=[ops=(list pole) gen=_gen]
    =<  [[ops.acc n] gen.acc]
    ^-  [n=need acc=_acc]
    |-  ^-  [need _acc]
    ?+    -.ned  [ned acc]
        ^
      =^  tel  acc      $(ned q.ned)
      =^  hed  acc      $(ned p.ned)
      =^  r    gen.acc  re(gen gen.acc)
      =.  ops.acc  [cel+r ops.acc]
      :_  acc
      [%both r & hed tel]
    ::
        %both
      =^  tel  acc  $(ned t.ned)
      =^  hed  acc  $(ned h.ned)
      =?  ops.acc  !c.ned  [cel+r.ned ops.acc]
      :_  acc
      [%both r.ned & hed tel]
    ==
  ::  split need for edit: donor, then recipient
  ::
  ++  into
    |=  [axe=@ nex=next]
    ^-  [[need need @uwoo] _gen]
    ?<  =(0 axe)
    ?:  =(1 axe)  [[what.nex none+~ then.nex] gen]
    =|  tack=(list [h=? n=need])
    =|  ops=(list pole)
    =*  ned  what.nex
    |^  ^-  [[need need @uwoo] _gen]
    ?:  =(1 axe)
      =^  o=@uwoo  gen
        ?~  ops  [then.nex gen]
        (emit ~ ops %hop then.nex)
      ::
      =;  big=need  [[ned big o] gen]
      %+  roll  tack
      |:  [*[h=? n=need] acc=`need`[%none ~]]
      ^+  acc
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
  ::  split constant into registers according to a need
  ::
  ++  mede
    |=  [o=@uwoo n=* ned=need]
    ^-  [@uwoo _gen]
    =|  ops=(list pole)
    =/  sin=(list [non=* ned=need])  [n ned]~
    |-  ^-  [@uwoo _gen]
    ?~  sin  (emit ~ ops %hop o)
    =*  no  non.i.sin
    =*  ne  ned.i.sin
    ?-    -.ne
        %none  $(sin t.sin)
        %this  $(ops [[%imm no r.ne] ops], sin t.sin)
    ::
        ^
      ?^  no  $(sin [[+.no q.ne] [-.no p.ne] t.sin])
      (emit ~ ~ %bom ~)
    ::
        %both
      ?:  &(!c.ne ?=(@ no))  (emit ~ ~ %bom ~)
      =^  [o1=@uwoo r=@uvre]  gen  (kerf %next ne o)
      $(sin t.sin, o o1, ops [[%imm ?^(no no %ska-line-mede) r] ops])
    ==
  ::  push need
  ::  axe != 0
  ::
  ++  from
    |=  [axe=@ ned=need]
    ^-  need
    ?<  =(0 axe)
    |-  ^-  need
    ?:  =(1 axe)  ned
    ?-  (cap axe)
      %2  [$(axe (mas axe)) none+~]
      %3  [none+~ $(axe (mas axe))]
    ==
  ::  merge needs of two sequential computation
  ::
  ++  copy1
    |=  [feed=next seed=need]
    ^-  [next _gen]
    =^  [ops=(list pole) =need]  gen
      ^-  [[(list pole) need] _gen]
      =/  needs=(pair need need)  [what.feed seed]
      |-  ^-  [[(list pole) need] _gen]
      ?+    needs  ~|(%impossible !!)
          [[%none *] *]  [[~ q.needs] gen]
          [* [%none *]]  [[~ p.needs] gen]
      ::
          [[%this *] [%this *]]
        =,  needs
        ~?  =(r.p r.q)  [%copy-this-this r.p]
        ::  by copying `p` -> `q` we fulfill need of `q`
        ::  then we return `p` to be fulfilled
        ::
        [[~[[%mov r.p r.q]] p] gen]
      ::
          [[%this *] *]
        ::  normalize `q` to %both, as it is going
        ::  to fulfill the need of `p`
        ::
          ?<  ?=(?(%this %none) -.q.needs)
        =^  qq=$>(%both need)  gen
          ?@(-.q.needs [q.needs gen] =^(x gen re [[%both x | q.needs] gen]))
        ::
        =,  needs
        ~?  =(r.p r.qq)  [%copy-this-cell r.p]
        [[~[[%mov r.qq r.p]] qq] gen]
      ::
          [* [%this *]]
        ?<  ?=(?(%this %none) -.p.needs)
        =^  pp=$>(%both need)  gen
          ?@(-.p.needs [p.needs gen] =^(x gen re [[%both x | p.needs] gen]))
        ::
        =,  needs
        ~?  =(r.q r.pp)  [%copy-cell-this r.q]
        [[~[[%mov r.pp r.q]] pp] gen]
      ::
          [[%both *] *]
        ?<  ?=(?(%this %none) -.q.needs)
        =^  qq=$>(%both need)  gen
          ?@(-.q.needs [q.needs gen] =^(x gen re [[%both x | q.needs] gen]))
        ::
        =,  needs
        ~?  =(r.p r.qq)  [%copy-both-cell r.p]
        =/  top-move=(list pole)  ~[[%mov r.qq r.p]]
        =^  [head-move=(list pole) head-need=need]  gen  $(needs [h.p h.qq])
        =^  [tail-move=(list pole) tail-need=need]  gen  $(needs [t.p t.qq])
        :_  gen
        :-  (zing tail-move head-move top-move ~)
        [%both r.qq c.p head-need tail-need]
      ::
          [[^ *] [^ *]]
        =,  needs
        =^  [head-move=(list pole) head-need=need]  gen  $(needs [p.p p.q])
        =^  [tail-move=(list pole) tail-need=need]  gen  $(needs [q.p q.q])
        :_  gen
        :-  (weld tail-move head-move)
        [head-need tail-need]
      ::
          [[^ *] [%both *]]
        =,  needs
        =^  [head-move=(list pole) head-need=need]  gen  $(needs [p.p h.q])
        =^  [tail-move=(list pole) tail-need=need]  gen  $(needs [q.p t.q])
        :_  gen
        :-  (weld tail-move head-move)
        [%both r.q | head-need tail-need]
      ==
    ::
    =^  o  gen  (emit ~ ops %hop then.feed)
    [[%next need o] gen]
  ::
  ++  copy
    |=  [feed=next seed=need]
    ^-  [next _gen]
    =^  [ned=need ops=(list pole)]  gen  (copy-give-ops what.feed seed)
    =^  o  gen  (emit ~ ops %hop then.feed)
    [[%next ned o] gen]
  ::
  ++  copy-give-ops
    |=  [feed=need seed=need]
    ^-  [[need (list pole)] _gen]
    =|  ops=(list pole)
    =|  sout=(list need)
    =/  sin=(list (each (unit [r=@uvre c=?]) [l=need r=need]))
      [|+[feed seed]]~
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
  ::  given a control flow merge destination, generate a phi block
  ::  and comefrom blocks for branches, returning branch destinations
  ::
  ++  phil1
    |=  nex=next
    ^-  [[next next] _gen]
    =^  from-z  gen  oo
    =^  from-o  gen  oo
    =|  acc=[dispatch=(map @uvre (map @uwoo @uvre)) gen=_gen]
    =;  [[need-z=need need-o=need] acc=_acc]
      =.  gen  gen.acc
      =^  phi=@uwoo  gen  (emit dispatch.acc ~ %hop then.nex)
      =.  gen  (come from-z phi)
      =.  gen  (come from-o phi)
      [[[%next need-z from-z] [%next need-o from-o]] gen]
    ::
    =/  ned=need  what.nex
    ::  attention: gen is captured by acc and will be returned later
    ::  use gen.acc instead of gen
    ::
    |-  ^-  [[need need] _acc]
    ?-    -.ned
        %none
      [[ned ned] acc]
    ::
        ^
      =^  h=[z=need o=need]  acc  $(ned p.ned)
      =^  t=[z=need o=need]  acc  $(ned q.ned)
      =/  cons-z  [z.h z.t]
      =/  cons-o  [o.h o.t]
      [[cons-z cons-o] acc]
    ::
        %this
      =^  r-z  gen.acc  re(gen gen.acc)
      =^  r-o  gen.acc  re(gen gen.acc)
      =/  patch  (~(gas by *(map @uwoo @uvre)) ~[[from-z r-z] [from-o r-o]])
      =.  dispatch.acc  (~(put by dispatch.acc) r.ned patch)
      [[this+r-z this+r-o] acc]
    ::
        %both
      =^  r-z  gen.acc  re(gen gen.acc)
      =^  r-o  gen.acc  re(gen gen.acc)
      =/  patch  (~(gas by *(map @uwoo @uvre)) ~[[from-z r-z] [from-o r-o]])
      =.  dispatch.acc  (~(put by dispatch.acc) r.ned patch)
      =^  h=[z=need o=need]  acc  $(ned h.ned)
      =^  t=[z=need o=need]  acc  $(ned t.ned)
      =/  cons-z  [z.h z.t]
      =/  cons-o  [o.h o.t]
      [[[%both r-z c.ned cons-z] [%both r-o c.ned cons-o]] acc]
    ==
  ::
  ++  phil
    |=  nex=next
    ^-  [[next next] _gen]
    =/  sin=(list (each (unit [c=? z=@uvre o=@uvre]) need))  ~[|+what.nex]
    =|  sout=(list [z=need o=need])
    =|  dispatch=(map @uvre (map @uwoo @uvre))
    =^  from-z  gen  oo
    =^  from-o  gen  oo
    |-  ^-  [[next next] _gen]
    ?~  sin
      ?>  ?=([* ~] sout)
      =^  phi=@uwoo  gen  (emit dispatch ~ %hop then.nex)
      =.  gen  (come from-z phi)
      =.  gen  (come from-o phi)
      [[[%next z.i.sout from-z] [%next o.i.sout from-o]] gen]
    ::
    ?:  ?=(%& -.i.sin)
      ?>  ?=([* * *] sout)
      =/  zo=[need need]
        =/  cons-z  [z.i.t.sout z.i.sout]
        =/  cons-o  [o.i.t.sout o.i.sout]
        ?~  p.i.sin  [cons-z cons-o]
        =*  r-z  z.u.p.i.sin
        =*  o-z  z.u.p.i.sin
        =*  c    c.u.p.i.sin
        [[%both r-z c cons-z] [%both o-z c cons-o]]
      ::
      $(sin t.sin, sout [zo t.t.sout])
    =/  dest=need  p.i.sin
    ?:  ?=(%none -.dest)
      $(sout [[dest dest] sout], sin t.sin)
    ?^  -.dest
      $(sin [|+p.dest |+q.dest &+~ t.sin])
    ::  %both or %this
    ::
    =^  r-z  gen  re
    =^  r-o  gen  re
    =/  patch  (~(gas by *(map @uwoo @uvre)) ~[[from-z r-z] [from-o r-o]])
    ?-    -.dest
        %this
      %=  $
        dispatch   (~(put by dispatch) r.dest patch)
        sout  [[this+r-z this+r-o] sout]
        sin   t.sin
      ==
    ::
        %both
      %=  $
        dispatch   (~(put by dispatch) r.dest patch)
        sin  [|+h.dest |+t.dest &+`[c.dest r-z r-o] t.sin]
      ==
    ==
  ::  like +phil but for loobean-producing opcodes
  ::  two branches will produce a loobean to put in `r`, and they merge in `o`
  ::
  ++  phin
    |=  [r=@uvre o=@uwoo]
    ^-  [[@uwoo @uwoo] _gen]
    =^  got-0  gen  re
    =^  got-1  gen  re
    =^  if-0   gen  oo
    =^  if-1   gen  oo
    =^  phi    gen
      =-  (emit - ~ %hop o)
      %+  ~(put by *(map @uvre (map @uwoo @uvre)))  r
      (~(gas by *(map @uwoo @uvre)) ~[[if-0 got-0] [if-1 got-1]])
    ::
    =.  gen  (come if-0 phi)
    =.  gen  (come if-1 phi)
    =^  from-0  gen  (emit ~ [%imm 0 got-0]~ %hop if-0)
    =^  from-1  gen  (emit ~ [%imm 1 got-1]~ %hop if-1)
    [[from-0 from-1] gen]
  ::  emit comefrom block de -> en
  ::
  ++  come
    |=  [de=@uwoo en=@uwoo]
    ^+  gen
    (emir de [~ ~ %hip de en])
  ::  merge subject needs of two branches. like +copy, except
  ::  used for conditional branches instead of sequential computations.
  ::  resulting need will be a maximally common split
  ::
  ++  sect
    |=  [zero=next once=next]
    ^-  [[need @uwoo @uwoo] _gen]
    =|  ops-z=(list (list pole))
    =|  ops-o=(list (list pole))
    =|  sout=(list need)
    =/  sin=(list (each (unit [r=@uvre c=?]) [z=need o=need]))
      [|+[what.zero what.once]]~
    |-  ^-  [[need @uwoo @uwoo] _gen]
    ?~  sin
      ?>  ?=([* ~] sout)
      =^  to-z  gen  (emit ~ (zing (flop ops-z)) %hop then.zero)
      =^  to-o  gen  (emit ~ (zing (flop ops-o)) %hop then.once)
      [[i.sout to-z to-o] gen]
    ?:  ?=(%& -.i.sin)
      ?>  ?=([* * *] sout)
      =/  cons  [i.t.sout i.sout]
      =/  out=need
        ?~  p.i.sin  cons
        [%both r.u.p.i.sin c.u.p.i.sin cons]
      ::
      $(sin t.sin, sout [out t.t.sout])
    =/  z-need  z.p.i.sin
    =/  o-need  o.p.i.sin
    ?:  ?=(?(%none %this) -.z-need)
      ?:  ?=(%none -.o-need)
        $(sin t.sin, sout [z-need sout])
      =^  res-o=[r=@uvre p=(list pole)]  gen  (kern o-need)
      =?  ops-z  ?=(%this -.z-need)  [[%mov r.res-o r.z-need]~ ops-z]
      %=  $
        ops-o      [p.res-o ops-o]
        sin   t.sin
        sout  [[%this r.res-o] sout]
      ==
    ?:  ?=(?(%none %this) -.o-need)
      =^  res-z=[r=@uvre p=(list pole)]  gen  (kern z-need)
      =?  ops-o  ?=(%this -.o-need)  [[%mov r.res-z r.o-need]~ ops-o]
      %=  $
        ops-z  [p.res-z ops-z]
        sin  t.sin
        sout  [[%this r.res-z] sout]
      ==
    ?:  &(?=(^ -.z-need) ?=(^ -.o-need))
      $(sin [|+[p.z-need p.o-need] |+[q.z-need q.o-need] &+~ t.sin])
    =^  z-both=$>(%both need)  gen
      ?@  -.z-need  [z-need gen]
      =^  x  gen  re
      [[%both x | z-need] gen]
    ::
    =^  o-both=$>(%both need)  gen
      ?@  -.o-need  [o-need gen]
      =^  x  gen  re
      [[%both x | o-need] gen]
    ::
    =?  .  |(c.z-both c.o-both)
      =?  ops-z  !c.z-both  [[%cel r.z-both]~ ops-z]
      =?  ops-o  !c.o-both  [[%cel r.o-both]~ ops-o]
      .
    ::
    %=  $
      ops-o  [[%mov r.z-both r.o-both]~ ops-o]
      sin    [ |+[h.z-both h.o-both]
               |+[t.z-both t.o-both]
               &+`[r.z-both |(c.z-both c.o-both)]
               t.sin
             ]
    ==
  ::
  ++  sect1
    |=  [zero=next once=next]
    ^-  [[need @uwoo @uwoo] _gen]
    =|  acc=[ops-z=(list (list pole)) ops-o=(list (list pole)) gen=_gen]
    =;  [ned=need acc=_acc]
      =.  gen  gen.acc
      =^  to-z  gen  (emit ~ (zing (flop ops-z.acc)) %hop then.zero)
      =^  to-o  gen  (emit ~ (zing (flop ops-o.acc)) %hop then.once)
      [[ned to-z to-o] gen]
    =/  z-need  what.zero
    =/  o-need  what.once
    |-  ^-  [need _acc]
    ?:  ?=(?(%none %this) -.z-need)
      ?:  ?=(%none -.o-need)  [z-need acc]
      =^  res-o=[r=@uvre p=(list pole)]  gen.acc  (kern(gen gen.acc) o-need)
      =?  ops-z.acc  ?=(%this -.z-need)  [[%mov r.res-o r.z-need]~ ops-z.acc]
      =.  ops-o.acc  [p.res-o ops-o.acc]
      [[%this r.res-o] acc]
    ?:  ?=(?(%none %this) -.o-need)
      =^  res-z=[r=@uvre p=(list pole)]  gen.acc  (kern(gen gen.acc) z-need)
      =?  ops-o.acc  ?=(%this -.o-need)  [[%mov r.res-z r.o-need]~ ops-o.acc]
      =.  ops-z.acc  [p.res-z ops-z.acc]
      [[%this r.res-z] acc]
    ?:  &(?=(^ -.z-need) ?=(^ -.o-need))
      =^  h  acc  $(z-need p.z-need, o-need p.o-need)
      =^  t  acc  $(z-need q.z-need, o-need q.o-need)
      [[h t] acc]
    =^  z-both=$>(%both need)  acc
      ?@  -.z-need  [z-need acc]
      =^  x  gen.acc  re(gen gen.acc)
      [[%both x | z-need] acc]
    ::
    =^  o-both=$>(%both need)  acc
      ?@  -.o-need  [o-need acc]
      =^  x  gen.acc  re(gen gen.acc)
      [[%both x | o-need] acc]
    ::
    =?  .  |(c.z-both c.o-both)
      =?  ops-z.acc  !c.z-both  [[%cel r.z-both]~ ops-z.acc]
      =?  ops-o.acc  !c.o-both  [[%cel r.o-both]~ ops-o.acc]
      .
    ::
    =.  ops-o.acc  [[%mov r.z-both r.o-both]~ ops-o.acc]
    =^  h  acc  $(z-need h.z-both, o-need h.o-both)
    =^  t  acc  $(z-need t.z-both, o-need t.o-both)
    [[%both r.z-both |(c.z-both c.o-both) h t] acc]
  ::  split noun in a register into goal
  ::  or, since we are going backwards, fulfill the given need by generating
  ::  code that splits a noun in a register, and return that register + the
  ::  block index
  ::
  ++  kerf
    |=  nex=next
    ^-  [[@uwoo @uvre] _gen]
    =^  [r=@uvre p=(list pole)]  gen  (kern what.nex)
    ?~  p  [[then.nex r] gen]
    =^  o  gen  (emit ~ p %hop then.nex)
    [[o r] gen]
  ::  split noun in a register to need, produce instruction list
  ::
  ++  kern
    |=  ned=need
    ^-  [[@uvre (list pole)] _gen]
    =;  [[r=(unit @uvre) l=(list pole)] =_gen]
      ?^  r  [[u.r l] gen]
      ?>  ?=(~ l)
      =^(r gen re [[r ~] gen])
    ::
    =|  ops=(list pole)
    |-  ^-  [(pair (unit @uvre) (list pole)) _gen]
    ?-    -.ned
        %none  [[~ ops] gen]
        %this  [[`r.ned ops] gen]
    ::
        ^
      =^  r  gen  re
      $(ned [%both r | ned])
    ::
        %both
      =^  tel  gen  $(ned t.ned)
      =.  ops
        ?~  p.tel  q.tel
        [[%tal r.ned u.p.tel] q.tel]
      ::
      =^  hed  gen  $(ned h.ned)
      =.  ops
        ?~  p.hed  q.hed
        [[%hed r.ned u.p.hed] q.hed]
      =?  ops  !c.ned  [[%cel r.ned] ops]
      [[`r.ned ops] gen]
    ==
  ::  split a goal into two for autocons, emitting cons code if needed
  ::
  ++  split
    |=  nex=next
    ^-  [[need need @uwoo] _gen]
    =*  ned  what.nex
    ?-    -.ned
        ^      [[p.ned q.ned then.nex] gen]
        %none  [[ned ned then.nex] gen]
        %this
      =^  hed  gen  re
      =^  tel  gen  re
      =^  o  gen  (emit ~ [%con hed tel r.ned]~ %hop then.nex)
      [[this+hed this+tel o] gen]
    ::
        %both
      =^  hed  gen  (must h.ned)
      =^  tel  gen  (must t.ned)
      =^    o  gen  (emit ~ [%con p.hed p.tel r.ned]~ %hop then.nex)
      [[q.hed q.tel o] gen]
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
  ++  emit
    |=  =blob
    ^-  [@uwoo _gen]
    =^  o  gen  oo
    [o (emir o blob)]
  ::
  ++  emir
    |=  [o=@uwoo =blob]
    ^+  gen
    gen(blocks.here (~(put by blocks.here.gen) o blob))
  ::
  ++  oo
    ^-  [@uwoo _gen]
    [bo-gen.gen gen(bo-gen +(bo-gen.gen))]
  ::
  ++  re
    ^-  [@uvre _gen]
    [re-gen.gen gen(re-gen +(re-gen.gen))]
  ::
  ++  bomb
    ^-  [next _gen]
    =^  o  gen  (emit ~ ~ %bom ~)
    [[%next [%none ~] o] gen]
  ::
  ++  mine
    |=  [r=@uvre t=@uwoo]
    ^-  [next _gen]
    =^  mile  gen  (emit ~ [%imm %ska-line-mine r]~ %hop t)
    [[%next [%none ~] mile] gen]
  --  ::  |line
--