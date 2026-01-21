/-  gene
/+  *skan
::
=,  gene
=*  stub  ~|(%stub !!)
=|  lon=line-long
|_  bol=boil
+*  this  .
++  line
  |_  gen=line-short
  ++  cuts
    =/  =goal  [%done ~]
    |=  =bell
    ^-  [next line-short]
    =|  gen=line-short
    =.  -.gen  lon
    =/  nomm=nomm-1  (~(got by code.bol) bell)
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
        =^  next-2  gen  $(nomm +.nomm, goal [%next tel t])
        =^  next-1  gen  $(nomm -.nomm, goal [%next hed then.next-2])
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
        =^  r  gen  re
        =^  o  gen  (emit ~ [%imm p.nomm r]~ %don r)
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
        =^  need-f  gen  $(nomm u.q.nomm, goal [%next this+f o])
        =^  need-s  gen  $(nomm p.nomm, goal [%next this+s then.need-f])
        (copy need-s what.need-f)
      =/  armor=@uxor  (~(got by bells.gen) u.info.nomm)
      =/  args  (~(got by arity.gen) u.info.nomm)
      =^  [args-need=need args-list=(list @uvre)]  gen  (args-to-need args)
      ::  XX no jet stuff for now
      ::
      =^  tar=@uwoo  gen
        ?-    -.goal
            %done  (emit ~ ~ %jmp armor args-list)
        ::
            %next
          =^  [aftr=@uwoo prod=@uvre]  gen  (kerf goal)
          (emit ~ ~ %cal armor args-list prod aftr)
        ==
      ::
      =^  fol-next=next  gen
        ::  if the formula-formula was removed: do nothing
        ::  else compute formula-formula and drop the result to preserve crashes
        ::
        ?~  q.nomm  [[%next none+~ tar] gen]
        $(nomm u.q.nomm, goal [%next none+~ tar])
      ::
      =^  sub-next  gen  $(nomm p.nomm, goal [%next args-need then.fol-next])
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
          $(nomm p.nomm)
        =^  [z=@uwoo o=@uwoo]  gen  (phin r.what.goal then.goal)
        $(goal [%pick z o])
      ::
          %pick
        =^  r  gen  re
        =^  o  gen  (emit ~ ~ %clq r [zero once]:goal)
        $(nomm p.nomm, goal [%next [%this r] o])
      ==
    ::
        %4
      ?-    -.goal
          %done
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o     gen  (emit ~ [%inc arg pro]~ %don pro)
        $(nomm p.nomm, goal [%next [%this arg] o])
      ::
          %pick
        =^  pro  gen  re
        =^  arg  gen  re
        =^  o     gen  (emit ~ [%inc arg pro]~ %brn pro [zero once]:goal)
        $(nomm p.nomm, goal [%next [%this arg] o])
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
        $(nomm p.nomm, goal [%next [%this arg] o])
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
          =^  next-q  gen  $(nomm q.nomm)
          =^  next-p  gen  $(nomm p.nomm, then.goal then.next-q)
          (copy next-p what.next-q)
        =^  [z=@uwoo o=@uwoo]  gen  (phin r.what.goal then.goal)
        $(goal [%pick z o])
      ::
          %pick
        =^  r-p     gen  re
        =^  r-q     gen  re
        =^  o       gen  (emit ~ ~ %eqq r-p r-q [zero once]:goal)
        =^  next-q  gen  $(nomm q.nomm, goal [%next [%this r-q] o])
        =^  next-p  gen  $(nomm p.nomm, goal [%next [%this r-p] then.next-q])
        (copy next-p what.next-q)
      ::
      ==
    ::
        %6
      ?:  ?=(%next -.goal)
        =^  [phi-0=next phi-1=next]  gen  (phil goal)
        =^  next-1  gen  $(nomm r.nomm, goal phi-1)
        =^  next-0  gen  $(nomm q.nomm, goal phi-0)
        =^  [both=need then=@uwoo else=@uwoo]  gen  (sect next-0 next-1)
        =^  cond  gen  $(nomm p.nomm, goal [%pick then else])
        (copy cond both)
      ::  either %6 is in tail position or the result is used to %pick,
      ::  so we don't need to generate merge blocks
      ::
      =^  next-1  gen  $(nomm r.nomm)
      =^  next-0  gen  $(nomm q.nomm)
      =^  [both=need then=@uwoo else=@uwoo]  gen  (sect next-0 next-1)
      =^  cond  gen  $(nomm p.nomm, goal [%pick then else])
      (copy cond both)
    ::
        %7
      =^  nex  gen  $(nomm q.nomm)
      $(nomm p.nomm, goal nex)
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
        =^  next-rec  gen  $(nomm q.nomm, goal [%next rec o])
        =^  next-don  gen  $(nomm q.p.nomm, goal [%next don then.next-rec])
        (copy next-don what.next-rec)
      ::
      ==
    ::
        %11
      ?@  p.nomm
        ?.  ?=(hint-static-mute p.nomm)  $(nomm q.nomm)
        =^  goal  gen  (simple-next goal)
        =^  epil  gen  (emit ~ [%hos p.nomm q.nomm]~ %hop then.goal)
        =^  nex   gen  $(nomm q.nomm, goal goal(then epil))
        =^  prol  gen  (emit ~ [%his p.nomm q.nomm]~ %hop then.nex)
        [[%next what.nex prol] gen]
      ?:  ?=(%memo p.p.nomm)
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
          =^  save  gen  (emit ~ [%mem key sub q.nomm prod.mis]~ %hop aftr.mis)
          $(nomm q.nomm, goal [%next this+prod.mis save])
        ::  unsatisfied so far: prod.hit, what.next-mis
        ::  %mim will satisfy prod.hit or miss, only what.next-mis is left
        ::  so +sect is not needed to align the needs of branches
        ::
        =^  check  gen
          (emit ~ ~ %mim key sub q.nomm prod.hit aftr.hit then.next-mis)
        ::
        =^  next-key  gen  $(nomm q.p.nomm, goal [%next this+key check])
        =^  key-fol   gen  (copy next-key what.next-mis)
        ::  fill the subject register
        ::
        (copy key-fol this+sub)
      ?.  ?=(hint-dynamic p.p.nomm)
        =^  nex  gen  $(nomm q.nomm)
        =^  hin  gen  $(nomm q.p.nomm, goal [%next none+~ then.nex])
        (copy hin what.nex)
      =^  goal  gen  (simple-next goal)
      =^  toke  gen  re
      =^  epil-ops=(list pole)  .
        ::  produce epilogue ops while potentially emitting code
        ::  to split the hinted formula's product into the registers
        ::  in the original need if the hint's epilogue needs the value
        ::  of the hinted formula
        ::
        =*  dot  .
        ?:  ?=(hint-dynamic-mute p.p.nomm)
          [[%hod p.p.nomm toke q.nomm]~ dot]
        =^  [aftr=@uwoo prod=@uvre]  gen  (kerf goal)
        [[%hyd p.p.nomm toke prod q.nomm]~ dot(goal [%next this+prod aftr])]
      ::
      =^  epil  gen  (emit ~ epil-ops %hop then.goal)
      =^  nex   gen  $(nomm q.nomm, goal goal(then epil))
      ::  if the hint is not crash-relocation safe: put a relocation boundary
      ::
      =?  .  ?=(hint-dynamic-mute-stop p.p.nomm)
        =*  dot  .
        =^  top  gen  (stop nex)
        dot(nex top)
      ::
      =^  prol  gen  (emit ~ [%hid p.p.nomm toke q.nomm]~ %hop then.nex)
      =^  dyn   gen  $(nomm q.p.nomm, goal [%next this+toke prol])
      (copy dyn what.nex)
    ::
        %12
      =^  goal  gen  (simple-next goal)
      =^  [out=@uwoo pro=@uvre]  gen  (kerf goal)
      =^  r-path     gen  re
      =^  r-ref      gen  re
      =^  o-spy      gen  (emit ~ [%spy r-ref r-path pro]~ %hop out)
      =^  need-path  gen  $(nomm q.nomm, goal [%next this+r-path o-spy])
      =^  need-ref   gen  $(nomm p.nomm, goal [%next this+r-ref then.need-path])
      (copy need-ref what.need-path)
    ==
  ::
  ++  args-to-need
    |=  =args
    ^-  [[need (list @uvre)] _gen]
    =^  ned=need  gen
      |-  ^-  [need _gen]
      ?~  args  [none+~ gen]
      ?-    -.args
          ::  XX special case %look somehow?..
          ::
          ?(%arg %look)
        =^  r  gen  re
        [this+r gen]
      ::
          %hole
        =^  l  gen  $(args l.args)
        =^  r  gen  $(args r.args)
        [[l r] gen]
      ==
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
      =^  r    gen.acc  re
      =.  ops.acc  [cel+r ops.acc]
      :_  acc
      [%both r & hed tel]
    ::
        %both
      ?:  c.ned  [ned acc]
      =^  tel  acc  $(ned t.ned)
      =^  hed  acc  $(ned h.ned)
      =.  ops.acc  [cel+r.ned ops.acc]
      :_  acc
      ned(c &, h hed, t tel)
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
      =^  r  gen  re
      $(i.sin i.sin(ned [%both r | ne]))
    ::
        %both
      ?.  |(c.ne ?=(^ no))
        =^  o1  gen  (emit ~ ~ %bom ~)
        $(o o1, sin t.sin)
      =^  [o1=@uwoo r=@uvre]  gen  (kerf %next ne o)
      $(sin t.sin, o o1, ops [[%imm ?^(no no %ska-line-mede) r] ops])
    ==
  ::
  ++  mede1
    |=  [o=@uwoo n=* ned=need]
    ^-  [@uwoo _gen]
    =|  acc=[ops=(list pole) o=_o gen=_gen]
    =;  acc=_acc
      =.  gen  gen.acc
      (emit ~ ops.acc %hop o.acc)
    |-  ^+  acc
    ?-    -.ned
        %none  acc
        %this  acc(ops [[%imm n r.ned] ops.acc])
    ::
        ^
      ?^  n
        =.  acc  $(n +.n, ned q.ned)
        $(n -.n, ned p.ned)
      =^  r  gen.acc  re
      $(ned [%both r | ned])
    ::
        %both
      ?.  |(c.ned ?=(^ n))
        =^  o1  gen.acc  (emit ~ ~ %bom ~)
        acc(o o1)
      =^  [o1=@uwoo r=@uvre]  gen.acc  (kerf %next ned o)
      %=  acc
        o    o1
        ops  [[%imm ?^(n n %ska-line-mede) r] ops.acc]
      ==
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
        ::          | XX shouldn't this be "or"?
        ::          v
        ::
        [%both r.qq &(c.p c.qq) head-need tail-need]
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
    =|  ops=(list pole)
    =|  sout=(list need)
    =/  sin=(list (each (unit [r=@uvre c=?]) [l=need r=need]))
      [|+[what.feed seed]]~
    ::
    |-  ^-  [next _gen]
    ?~  sin
      ?>  ?=([* ~] sout)
      =^  o  gen  (emit ~ ops %hop then.feed)
      [[%next i.sout o] gen]
    ?:  ?=(%& -.i.sin)
      ?>  ?=([* * ~] sout)
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
        sin  [|+[h.l h.rr] |+[t.l t.rr] &+`[r.rr |(c.l c.rr)] sin]
      ==
    ?^  -.r
      $(sin [|+[p.l p.r] |+[q.l q.r] &+~ sin])
    $(sin [|+[p.l h.r] |+[q.l t.r] &+`[r.r c.r] sin])
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
      =^  r-z  gen.acc  re
      =^  r-o  gen.acc  re
      =/  patch  (~(gas by *(map @uwoo @uvre)) ~[[from-z r-z] [from-o r-o]])
      =.  dispatch.acc  (~(put by dispatch.acc) r.ned patch)
      [[this+r-z this+r-o] acc]
    ::
        %both
      =^  r-z  gen.acc  re
      =^  r-o  gen.acc  re
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
      =^  res-o=[r=@uvre p=(list pole)]  gen  (kern o-need)
      =?  ops-z.acc  ?=(%this -.z-need)  [[%mov r.res-o r.z-need]~ ops-z.acc]
      =.  ops-o.acc  [p.res-o ops-o.acc]
      [[%this r.res-o] acc]
    ?:  ?=(?(%none %this) -.o-need)
      =^  res-z=[r=@uvre p=(list pole)]  gen  (kern z-need)
      =?  ops-o.acc  ?=(%this -.o-need)  [[%mov r.res-z r.o-need]~ ops-o.acc]
      =.  ops-z.acc  [p.res-z ops-z.acc]
      [[%this r.res-z] acc]
    ?^  -.z-need
      ?^  -.o-need
        =^  h  acc  $(z-need p.z-need, o-need p.o-need)
        =^  t  acc  $(z-need q.z-need, o-need q.o-need)
        [[h t] acc]
      =^  h  acc  $(z-need p.z-need, o-need h.o-need)
      =^  t  acc  $(z-need q.z-need, o-need t.o-need)
      [[%both r.o-need | h t] acc]
    ?^  -.o-need
      =^  h  acc  $(z-need h.z-need, o-need p.o-need)
      =^  t  acc  $(z-need t.z-need, o-need q.o-need)
      [[%both r.z-need | h t] acc]
    =^  h  acc  $(z-need h.z-need, o-need h.o-need)
    =^  t  acc  $(z-need t.z-need, o-need t.o-need)
    =.  ops-o.acc  [[%mov r.z-need r.o-need]~ ops-o.acc]
    ::  XX &, not | again, why?
    ::               v
    [[%both r.z-need &(c.z-need c.o-need) h t] acc]
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
    ~!  next
    ^-  [next _gen]
    =^  mile  gen  (emit ~ [%imm %ska-line-mine r]~ %hop t)
    [[%next [%none ~] mile] gen]
  --  ::  |line
--