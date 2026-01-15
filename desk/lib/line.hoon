/-  gene
/+  *skan
::
=,  gene
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
    ?+    -.nomm  !!
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
        =^  neet  gen  $(nomm +.nomm, goal [%next tel t])
        =^  neeh  gen  $(nomm -.nomm, goal [%next hed then.neet])
        (copy neeh what.neet)
      ==
    ==
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
        ::          | XX ?
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
    =|  stack=(list need)
    =/  work=(list (each (unit [r=@uvre c=?]) [l=need r=need]))
      [|+[what.feed seed]]~
    ::
    |-  ^-  [next _gen]
    ?~  work
      ?>  ?=([* ~] stack)
      =^  o  gen  (emit ~ ops %hop then.feed)
      [[%next i.stack o] gen]
    ?:  ?=(%& -.i.work)
      ?>  ?=([* * ~] stack)
      =/  par  [i.t.stack i.stack]
      %=  $
        work   t.work
        stack  :_  t.t.stack
               ?~  p.i.work  par
               =*  both  u.p.i.work
               [%both r.both c.both par]
      ==
    =*  l  l.p.i.work
    =*  r  r.p.i.work
    ?:  ?=(%none -.l)  $(stack [r stack], work t.work)
    ?:  ?=(%none -.r)  $(stack [l stack], work t.work)
    ?:  ?=(%this -.l)
      ?:  ?=(%this -.r)
        ~?  =(r.l r.r)  [%copy-this-l-a r.l r.r]
        $(ops [[%mov r.l r.r] ops], stack [l stack], work t.work)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x | r] gen]))
      ~?  =(r.l r.rr)  [%copy-this-l-b r.l r.rr]
      $(ops [[%mov r.rr r.l] ops], stack [rr stack], work t.work)
    ?:  ?=(%this -.r)
      =^  ll=$>(%both need)  gen
        ?@(-.l [l gen] =^(x gen re [[%both x | l] gen]))
      ~?  =(r.ll r.r)  [%copy-this-r r.ll r.r]
      $(ops [[%mov r.ll r.r] ops], stack [ll stack], work t.work)
    ?:  ?=(%both -.l)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen re [[%both x | r] gen]))
      ~?  =(r.l r.rr)  [%copy-both r.l r.rr]
      %=  $
        ops   [[%mov r.rr r.l] ops]
        work  [|+[h.l h.rr] |+[t.l t.rr] &+`[r.rr &(c.l c.rr)] work]
      ==
    ?^  -.r
      $(work [|+[p.l p.r] |+[q.l q.r] &+~ work])
    $(work [|+[p.l h.r] |+[q.l t.r] &+`[r.r |] work])
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