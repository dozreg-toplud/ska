::  +trim-trace-hints on formulas where it drops hints.  For every case: the
::  rounds of +optimize replayed pass by pass; at each call of
::  +trim-trace-hints its result against the model of lemmas/Ska/OptTrim.lean
::  written again here (m-body, m-walk, m-opened, m-run: the open keys
::  counted in a map, a key of count 0 absent, the join over predecessors a
::  pointwise max folded by hand, the unsafe keys a list), and the
::  ops it drops; then the optimized code of the subject unknown run by
::  +eval-blob, and +eval-top (subject known), both through +eval-mook,
::  against +mook of +mink on every subject of .subs
::
=/  inc  [4 0 1]
=/  sel  [6 [5 [0 1] [1 0]] [1 5] [0 0]]
::  a constant %mean (the trap's product known) and a deferred one (the trap
::  returns its payload, the subject)
::
=/  kc  =>  ~  !=(~>(%mean.|.(%foo) 5))
=/  dc  =>  ~  !=(~>(%mean.|.(+) 5))
?>  ?=([%11 [%mean *] *] kc)
?>  ?=([%11 [%mean *] *] dc)
=/  kh  +<.kc
=/  dh  +<.dc
=/  cases=(list [nam=@tas fol=^])
  :~  [%konst kc]
      [%konst-crash [11 kh inc]]
      [%defer dc]
      [%defer-crash [11 dh inc]]
      [%konst-in-spot [11 [%spot 1 0] [11 kh 1 5]]]
      [%defer-in-spot [11 [%spot 1 0] [11 dh [0 1] [1 5]]]]
      [%spot-in-defer-crash [11 dh [[11 [%spot 1 0] 1 5] inc]]]
      [%konst-shared [6 [5 [0 1] [1 0]] [11 kh 0 2] [7 [1 [1 2]] [11 [%spot 1 0] [11 kh 0 2]]]]]
      [%konst-twice-nested [11 kh [[11 kh 1 5] inc]]]
      [%const [11 [%spot 1 0] 1 5]]
      [%cons [11 [%spot 1 0] [1 5] [1 6]]]
      [%subj [11 [%mean 1 0] 0 1]]
      [%subj-cons [11 [%mean 1 0] [0 1] [0 1]]]
      [%lose [11 [%lose 1 0] 1 5]]
      [%hunk [11 [%hunk 1 0] 1 5]]
      [%hand [11 [%hand 1 0] 1 5]]
      [%crash-in [11 [%spot 1 0] 4 0 1]]
      [%slot-unknown [11 [%spot 1 0] 0 2]]
      [%slot-known [7 [[1 1] [0 1]] [11 [%spot 1 0] 0 2]]]
      [%slot-known-deep [7 [[1 1] [[0 1] [1 2]]] [11 [%spot 1 0] 0 6]]]
      [%branch-other-crash [6 [5 [0 1] [1 0]] [11 [%spot 1 0] 1 5] [0 0]]]
      [%branch-in [11 [%spot 1 0] [6 [5 [0 1] [1 0]] [1 5] [1 6]]]]
      [%branch-in-crash [11 [%spot 1 0] sel]]
      [%join-after [7 [6 [5 [0 1] [1 0]] [1 5] [1 6]] [11 [%spot 1 0] [0 1] [1 7]]]]
      [%nest-both [11 [%spot 1 0] [11 [%mean 1 7] 1 5]]]
      [%nest-inner [11 [%spot 1 0] [[11 [%mean 1 7] 1 5] inc]]]
      [%nest-inner-b [11 [%spot 1 0] [inc [11 [%mean 1 7] 1 5]]]]
      [%nest-three [11 [%spot 1 0] [11 [%mean 1 7] [11 [%spot 1 8] [1 5] [0 1]]]]]
      [%same-clue-const [11 [%spot 1 0] [[11 [%spot 1 0] 1 5] inc]]]
      [%same-clue-subj [11 [%spot 0 1] [[11 [%spot 0 1] 1 5] inc]]]
      [%same-clue-mean [11 [%mean 1 0] [[11 [%mean 1 0] 1 5] inc]]]
      [%same-clue-seq [[11 [%spot 1 0] 1 5] [11 [%spot 1 0] inc]]]
      [%same-clue-seq-b [[11 [%spot 1 0] inc] [11 [%spot 1 0] 1 5]]]
      [%clue-subj [11 [%spot 0 1] 1 5]]
      [%clue-crash [11 [%spot 0 2] 1 5]]
      [%call-in [11 [%spot 1 0] [8 [1 [1 5]] [9 2 0 1]]]]
      [%call-in-crash [11 [%spot 1 0] [8 [1 [4 0 3]] [9 2 0 1]]]]
      [%nok-in [11 [%spot 1 0] [2 [0 1] [1 1 5]]]]
      [%after-hint-crash [7 [11 [%spot 1 0] 1 5] inc]]
      [%before-hint-crash [7 inc [11 [%spot 1 0] 0 1]]]
      [%both-branches [6 [5 [0 1] [1 0]] [11 [%spot 1 0] 1 5] [11 [%mean 1 1] 1 6]]]
      [%branch-hint-join [7 [6 [5 [0 1] [1 0]] [11 [%spot 1 0] 1 5] [1 6]] inc]]
      [%edit-in [11 [%spot 1 0] [10 [2 [1 9]] [[1 1] [1 2]]]]]
      [%edit-in-crash [11 [%spot 1 0] [10 [2 [1 9]] [0 1]]]]
      [%memo-in [11 [%spot 1 0] [11 [%memo 1 0] 1 5]]]
      [%static-in [11 [%spot 1 0] [11 %xray 1 5]]]
      [%eq-in [11 [%spot 1 0] [5 [0 1] [1 0]]]]
      [%cell-test-in [11 [%spot 1 0] [3 0 1]]]
      [%deep-nest-crash [11 [%spot 1 0] [11 [%mean 1 1] [11 [%spot 1 2] inc]]]]
      [%hunk-around [11 [%hunk 1 0] [11 [%spot 1 1] [1 5]]]]
      [%spot-around-lose [11 [%spot 1 0] [11 [%lose 1 1] [1 5]]]]
  ==
=/  subs=(list *)  ~[0 1 5 [0 0] [1 2] [[1 2] 3] [0 [1 2]]]
::  the model of lemmas/Ska/OptTrim.lean
::
=/  m-key
  |=  op=pole
  ^-  (unit [o=? k=*])
  ?+  op  ~
    [%hdp ?(%spot %mean) *]  `[& %clue n.op p.op]
    [%hde ?(%spot %mean) *]  `[| %clue n.op p.op]
    [%hmp *]                 `[& %defer a.op v.op f.op]
    [%hme *]                 `[| %defer a.op v.op f.op]
    [%hcp *]                 `[& %konst n.op f.op]
    [%hce *]                 `[| %konst n.op f.op]
  ==
=/  m-quiet
  |=  op=pole
  ?=(?(%imm %mov %con %hed %tal %hsp %hse %hdp %hde %hmp %hme %hcp %hce %equ) -.op)
::  the count of a key (Cnt of the model: absent is 0), its update (Cnt.set:
::  0 deletes), the keys of positive count (Uns.add)
::
=/  m-cnt
  |=  [m=(map * @ud) k=*]
  ^-  @ud
  (fall (~(get by m) k) 0)
=/  m-set
  |=  [m=(map * @ud) k=* n=@ud]
  ^-  (map * @ud)
  ?:  =(0 n)  (~(del by m) k)
  (~(put by m) k n)
=/  m-pos
  |=  m=(map * @ud)
  ^-  (list *)
  (murn ~(tap by m) |=([k=* n=@ud] ?:(=(0 n) ~ `k)))
=/  m-body
  |=  [body=(list pole) opn=(map * @ud) uns=(list *)]
  ^-  [(map * @ud) (list *)]
  |-
  ?~  body  [opn uns]
  =/  h  (m-key i.body)
  ?^  h
    =/  n  (m-cnt opn k.u.h)
    ?:  o.u.h  $(body t.body, opn (m-set opn k.u.h +(n)))
    $(body t.body, opn (m-set opn k.u.h ?:((lte n 1) 0 (dec n))))
  ?:  (m-quiet i.body)  $(body t.body)
  $(body t.body, uns (weld (m-pos opn) uns))
::  Cnt.join: a pointwise max, folded over the entries of the second map
::
=/  m-join
  |=  [a=(map * @ud) b=(map * @ud)]
  ^-  (map * @ud)
  %+  roll  ~(tap by b)
  |=  [[k=* n=@ud] acc=_a]
  (m-set acc k (max n (m-cnt acc k)))
=/  m-walk
  |=  [bl=(map @uwoo blob) rev=(jar @uwoo @uwoo) topo=(list @uwoo)]
  =|  out=(map @uwoo (map * @ud))
  =|  uns=(list *)
  |-  ^-  (list *)
  ?~  topo  uns
  =/  b  (~(got by bl) i.topo)
  =/  opn=(map * @ud)
    %+  roll  (~(get ja rev) i.topo)
    |=  [p=@uwoo acc=(map * @ud)]
    (m-join acc (fall (~(get by out) p) ~))
  =/  r  (m-body body.b opn uns)
  %=  $
    topo  t.topo
    out   (~(put by out) i.topo -.r)
    uns   ?:(?=(?(%clq %eqq %brz %hop) -.fin.b) +.r (weld (m-pos -.r) +.r))
  ==
=/  m-opened
  |=  bl=(map @uwoo blob)
  ^-  (list *)
  %+  roll  ~(tap by bl)
  |=  [[* b=blob] acc=(list *)]
  %+  roll  body.b
  |=  [op=pole acc=_acc]
  =/  h  (m-key op)
  ?~  h  acc
  ?.  o.u.h  acc
  [k.u.h acc]
=/  m-trim
  |=  [bl=(map @uwoo blob) topo=(list @uwoo) rev=(jar @uwoo @uwoo)]
  ^-  (map @uwoo blob)
  =/  uns  (m-walk bl rev topo)
  =/  opd  (m-opened bl)
  %-  ~(run by bl)
  |=  b=blob
  %_  b
    body
  %+  skip  body.b
  |=  op=pole
  =/  h  (m-key op)
  ?~  h  |
  &(=(~ (find ~[k.u.h] uns)) !=(~ (find ~[k.u.h] opd)))
  ==
=/  dropped
  |=  [a=(map @uwoo blob) b=(map @uwoo blob)]
  ^-  (list pole)
  %-  zing
  %+  turn  ~(tap by a)
  |=  [o=@uwoo x=blob]
  =/  y  body:(~(got by b) o)
  %+  skip  body.x
  |=(op=pole !=(~ (find ~[op] y)))
::  TrimBr of lemmas/Ska/OptTrim.lean (brOp, brBody): a stack of open frames
::  at the start of every block reached from 0, empty at 0, that the body pops
::  only on top with the key it pushed (a frame without key for a %hde of
::  %hunk %hand %lose), and hands alike to every jump target.  A key may be
::  pushed while it is open (the counted pass allows it)
::
=/  br-key
  |=  op=pole
  ^-  (unit [o=? k=*])
  ?+  op  ~
    [%hdp ?(%spot %mean) *]  `[& %clue n.op p.op]
    [%hde ?(%spot %mean) *]  `[| %clue n.op p.op]
    [%hmp *]                 `[& %defer a.op v.op f.op]
    [%hme *]                 `[| %defer a.op v.op f.op]
    [%hcp *]                 `[& %konst n.op f.op]
    [%hce *]                 `[| %konst n.op f.op]
  ==
=/  br-op
  |=  [g=(list (unit *)) op=pole]
  ^-  (unit (list (unit *)))
  =/  h  (br-key op)
  ?^  h
    ?:  o.u.h  `[`k.u.h g]
    ?.  ?=([[~ *] *] g)  ~
    ?.  =(u.i.g k.u.h)  ~
    `t.g
  ?+  op  `g
    [%hdp ?(%hunk %hand %lose) *]  `[~ g]
    [%hde ?(%hunk %hand %lose) *]
      ?.  ?=([~ *] g)  ~
      `t.g
  ==
=/  br-body
  |=  [g=(list (unit *)) l=(list pole)]
  ^-  (unit (list (unit *)))
  ?~  l  `g
  =/  n  (br-op g i.l)
  ?~  n  ~
  $(g u.n, l t.l)
=/  brok
  |=  bl=(map @uwoo blob)
  ^-  ?
  =/  topo  (bb-topo bl)
  =/  k=(map @uwoo (list (unit *)))  (my [`@uwoo`0 ~]~)
  |-  ^-  ?
  ?~  topo  &
  =/  b  (~(got by bl) i.topo)
  =/  g0  (~(get by k) i.topo)
  ?~  g0  |
  =/  g  (br-body u.g0 body.b)
  ?~  g  |
  =/  js  (get-jmps fin.b)
  |-  ^-  ?
  ?~  js  ^$(topo t.topo)
  =/  e  (~(get by k) there.i.js)
  ?~  e  $(js t.js, k (~(put by k) there.i.js u.g))
  ?.  =(u.e u.g)  |
  $(js t.js)
::  one round of +optimize-once, checking every call of +trim-trace-hints
::
=/  once
  |=  [s=straight nd=(list pole) mis=@ud]
  ^-  [? straight (list pole) @ud]
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
  =^  f-alias=?  blocks.s  (alias n-args.s blocks.s rev topo)
  =.  topo  (skim topo ~(has by blocks.s))
  =.  rev  (rev-cfg blocks.s (sy topo))
  =/  pre  blocks.s
  ~?  !(brok pre)  %br-trim-fail-next
  =.  blocks.s  (trim-trace-hints blocks.s topo rev)
  =/  mod  (m-trim pre topo rev)
  =?  mis  !=(mod blocks.s)  +(mis)
  ~?  !=(mod blocks.s)  [%model-differs pre=pre real=blocks.s model=mod]
  =.  nd  (weld nd (dropped pre blocks.s))
  =.  blocks.s  (remove-dead-code blocks.s (flop topo))
  =^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)
  =^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)
  =^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)
  [|(f-alias c-hops c-branch c-middle) s nd mis]
=|  cnt=[cases=@ud drop-cases=@ud ops=@ud mis=@ud runs=@ud bad=@ud same=@ud]
=/  kinds=(list ?)  ~[| &]
|-  ^-  @
?~  cases
  ~&  [%summary cnt]
  0
=/  run-kind
  |=  [kno=? sub=*]
  ^-  [straight (list pole) @ud straight-out _state]
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [?:(kno [& sub] [| ~]) fol.i.cases] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  ~?  !(brok blocks.raw)  [%br-raw-fail fol.i.cases]
  =/  res=[s=straight nd=(list pole) mis=@ud]
    =/  s=straight  raw
    =|  nd=(list pole)
    =|  mis=@ud
    |-  ^-  [straight (list pole) @ud]
    =/  o  (once s nd mis)
    ?.  -.o  +.o
    $(s +<.o, nd +>-.o, mis +>+.o)
  =/  out=straight-out  s.res(blocks (switch-chains blocks.s.res))
  ?>  =(out (optimize raw))
  [raw nd.res mis.res out state]
::  subject unknown: one compile, run on every subject
::
=/  u  (run-kind | 0)
=.  state  +>+>.u
=/  code=straight-out  +>+<.u
~&  [nam.i.cases %unknown dropped=+<.u]
=.  cnt  cnt(cases +(cases.cnt), mis (add mis.cnt +>-.u), ops (add ops.cnt (lent +<.u)))
=?  drop-cases.cnt  !=(~ +<.u)  +(drop-cases.cnt)
=/  ss  subs
|-  ^-  @
?^  ss
  =/  a=toon  (mook (mink [i.ss fol.i.cases] ~))
  ::  the code of the subject unknown
  ::
  =/  blob  (~(got by blocks.code) 0w0)
  =/  ton=tone  -:(eval-blob [[[`@`0 `i.ss] ~ ~] ~] blob code ~ ~)
  =/  b=toon  -:(eval-mook ton)
  ::  +eval-top, the subject known
  ::
  =/  k  (run-kind & i.ss)
  =.  state  +>+>.k
  =?  drop-cases.cnt  !=(~ +<.k)  +(drop-cases.cnt)
  =.  cnt  cnt(cases +(cases.cnt), mis (add mis.cnt +>-.k), ops (add ops.cnt (lent +<.k)))
  ~?  !=(~ +<.k)  [nam.i.cases %known i.ss dropped=+<.k]
  =/  ton2=tone  -:(eval-top [i.ss fol.i.cases] ~)
  =/  c=toon  -:(eval-mook ton2)
  =.  runs.cnt  (add 2 runs.cnt)
  =/  ok  &(=(a b) =(a c))
  =?  bad.cnt  !ok  +(bad.cnt)
  ~?  !ok  [nam.i.cases %differ sub=i.ss mock=a unknown=b known=c]
  $(ss t.ss)
^$(cases t.cases)
