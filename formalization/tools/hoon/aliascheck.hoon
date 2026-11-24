::  +alias on formulas made to have it act.  For every case: the rounds of
::  +optimize replayed by +optimize-once with +alias called on the blocks of
::  each round (as +optimize-once does), and at each call what it did: %mov
::  ops eliminated, other ops dropped (and of those, in blocks with two
::  predecessors or more), two-way ends folded to a %hop, %brn ends made
::  %brz, %brn ends made [%bom ~], blocks dropped; then the optimized code of
::  the subject unknown run by +eval-blob, and +eval-top (subject known),
::  both through +eval-mook, against +mook of +mink on every subject
::
=/  sp  |=(f=* [11 [%spot 1 0] f])
=/  cases=(list [nam=@tas fol=* subs=(list *)])
  :~  [%mov [7 [0 2] [0 1]] ~[[1 2] 5]]
      [%mov-cons [[0 2] [0 2] [0 3]] ~[[1 2] 5]]
      [%eq-self [6 [5 [0 1] [0 1]] [1 1] [1 2]] ~[0 [1 2]]]
      [%eq-self-push [8 [0 1] [6 [5 [0 2] [0 2]] [1 1] [1 2]]] ~[0 [1 2]]]
      [%cell-twice [6 [3 0 1] [6 [3 0 1] [1 1] [1 2]] [1 3]] ~[0 [1 2]]]
      [%cell-twice-hed [6 [3 0 1] [6 [3 0 2] [1 1] [1 2]] [6 [3 0 1] [1 3] [1 4]]] ~[0 [1 2] [[1 2] 3]]]
      [%loob-yes [6 [0 1] [6 [0 1] [1 5] [1 6]] [1 7]] ~[0 1 2 [1 2]]]
      [%loob-no [6 [0 1] [1 7] [6 [0 1] [1 5] [1 6]]] ~[0 1 2 [1 2]]]
      [%loob-push [8 [5 [0 2] [0 3]] [6 [0 2] [1 5] [1 6]]] ~[[1 1] [1 2] 0]]
      [%loob-push2 [8 [5 [0 2] [0 3]] [6 [0 2] [6 [0 2] [1 5] [1 6]] [1 7]]] ~[[1 1] [1 2] 0]]
      [%loob-join [8 [6 [3 0 1] [1 0] [1 1]] [6 [0 2] [1 5] [1 6]]] ~[0 [1 2]]]
      [%nonloob-join [8 [6 [3 0 1] [1 7] [1 7]] [6 [0 2] [1 5] [1 6]]] ~[0 [1 2]]]
      [%nonloob-join2 [8 [6 [3 0 1] [1 7] [1 9]] [6 [0 2] [1 5] [1 6]]] ~[0 [1 2]]]
      [%nonloob-inc [8 [4 0 1] [6 [5 [0 2] [1 0]] [1 5] [6 [0 2] [1 6] [1 7]]]] ~[0 1 5]]
      [%join-cell [7 [6 [5 [0 2] [1 0]] [0 1] [0 1]] [6 [3 0 1] [1 1] [1 2]]] ~[0 [0 2] [1 2]]]
      [%join-cell-one [7 [6 [3 0 1] [0 1] [0 1]] [6 [3 0 1] [1 1] [1 2]]] ~[0 [0 2] [1 2]]]
      [%join-hed [8 [6 [3 0 1] [0 2] [0 1]] [[0 2] [0 6]]] ~[0 [0 2] [[1 2] 3]]]
      [%hed-twice [[0 2] [0 2] [0 3] [0 3]] ~[0 [1 2]]]
      [%hed-cons [7 [[0 1] [1 5]] [0 2]] ~[0 [1 2]]]
      [%inc-dec [7 [4 0 1] [0 1]] ~[0 5 [1 2]]]
      [%imm-twice [[1 5] [1 5] [1 6]] ~[0]]
      [%imm-join [8 [6 [3 0 1] [1 5] [1 5]] [[0 2] [1 5]]] ~[0 [1 2]]]
      [%drop-block [6 [0 1] [6 [0 1] [0 0] [1 6]] [1 7]] ~[0 1 2]]
      [%spot-fold (sp [6 [3 0 1] [6 [3 0 1] [0 2] [0 0]] [0 0]]) ~[0 [1 2] [[1 2] 3]]]
      [%spot-loob (sp [6 [0 1] [6 [0 1] (sp [0 0]) [1 6]] (sp [0 2])]) ~[0 1 2 [1 2]]]
      [%spot-join [7 [6 [3 0 1] (sp [0 2]) (sp [4 0 1])] (sp [0 2])] ~[0 [1 2] [[1 2] 3]]]
      [%spot-brn (sp [8 [5 [0 2] [0 3]] [6 [0 2] (sp [0 0]) [1 6]]]) ~[[1 1] [1 2] 0]]
      [%spot-nonloob (sp [8 [6 [3 0 1] [1 7] [1 7]] [6 [0 2] [1 5] [1 6]]]) ~[0 [1 2]]]
      ::  facts at a block with two predecessors: agreeing, disagreeing, one side
      ::
      [%j-agree-cell [6 [3 0 1] [7 [6 [5 [0 2] [1 0]] [0 1] [0 1]] [6 [3 0 1] [1 4] [1 5]]] [1 3]] ~[0 [0 2] [1 2]]]
      [%j-agree-cell3 [6 [3 0 3] [7 [6 [5 [0 2] [1 0]] [0 1] [0 1]] [6 [3 0 3] [1 4] [1 5]]] [1 3]] ~[0 [0 2] [1 2] [1 2 3]]]
      [%j-agree-loob [6 [0 2] [7 [6 [5 [0 3] [1 0]] [0 1] [0 1]] [6 [0 2] [1 4] [1 5]]] [1 3]] ~[[0 0] [1 0] [0 1] [2 0]]]
      [%j-agree-hed [8 [0 2] [7 [6 [5 [0 7] [1 0]] [0 1] [0 1]] [[0 6] [0 2]]]] ~[0 [0 2] [1 0] [1 2 3]]]
      [%j-agree-imm [8 [4 0 2] [7 [6 [5 [0 7] [1 0]] [0 1] [0 1]] [6 [5 [0 2] [4 0 6]] [1 4] [1 5]]]] ~[0 [0 2] [1 0] [1 2 3]]]
      [%j-disagree-loob [7 [6 [0 2] [0 1] [0 1]] [6 [0 2] [1 4] [1 5]]] ~[[0 0] [1 0] [2 0] 0]]
      [%j-one-cell [7 [6 [5 [0 2] [1 0]] [6 [3 0 3] [0 1] [0 0]] [0 1]] [6 [3 0 3] [1 4] [1 5]]] ~[[0 0] [0 1 2] [1 0] [1 1 2] 0]]
      [%j-two-cell [7 [6 [5 [0 2] [1 0]] [6 [3 0 3] [0 1] [0 0]] [6 [3 0 3] [0 1] [0 0]]] [6 [3 0 3] [1 4] [1 5]]] ~[[0 0] [0 1 2] [1 0] [1 1 2] 0]]
      [%j-par-agree [8 [6 [5 [0 2] [1 0]] [0 3] [0 3]] [6 [3 0 2] [1 4] [1 5]]] ~[[0 0] [0 1 2] [1 0] [1 1 2] 0]]
      [%j-par-loob [8 [6 [3 0 1] [5 [0 2] [0 3]] [1 1]] [6 [0 2] [1 4] [1 5]]] ~[0 [1 2] [1 1]]]
      ::  aimed at a %brn on a known non-loobean ([%bom ~])
      ::
      [%bom-a [6 [8 [1 7] [0 2]] [1 4] [1 5]] ~[0]]
      [%bom-b [8 [1 7] [7 [6 [3 0 3] [0 1] [0 1]] [6 [0 2] [1 4] [1 5]]]] ~[0 [1 2]]]
      [%bom-c [8 [6 [3 0 1] [1 7] [0 0]] [6 [0 2] [1 4] [1 5]]] ~[0 [1 2]]]
  ==
=*  mb  ,[par=(list @) body=(list *) fin=*]
=/  n-op
  |=  [t=@tas bl=(map @ mb)]
  ^-  @ud
  =/  l=(list *)  (zing (turn ~(val by bl) |=(b=mb body.b)))
  (lent (skim l |=(p=* &(?=(^ p) =(t -.p)))))
=/  n-body  |=(bl=(map @ mb) (lent (zing (turn ~(val by bl) |=(b=mb body.b)))))
=/  two  |=(f=* ?=([?(%clq %eqq %brn %brz) *] f))
::  what one call of +alias did: [mov other other-at-join folded brz bom dropped
::  jfold], jfold the ends folded (to %hop, %brz or %bom) in a block with two
::  distinct predecessors or more whose test register no op of the block defines
::
=/  acts
  |=  [pre0=(map @uwoo blob) post0=(map @uwoo blob) rev=(jar @uwoo @uwoo)]
  ^-  [@ud @ud @ud @ud @ud @ud @ud @ud]
  =/  pre  ;;((map @ mb) pre0)
  =/  post  ;;((map @ mb) post0)
  =/  mov  (sub (n-op %mov pre) (n-op %mov post))
  =/  oth  (sub (sub (n-body pre) (n-body post)) mov)
  =/  ps=(list [p=@ q=mb])  ~(tap by post)
  =|  a=[j=@ud f=@ud z=@ud m=@ud g=@ud]
  |-
  ?~  ps
    [mov oth j.a f.a z.a m.a (sub ~(wyt by pre) ~(wyt by post)) g.a]
  =/  b  (~(got by pre) p.i.ps)
  =/  c  q.i.ps
  =/  np=@ud  (lent `(list @)`(~(get ja rev) p.i.ps))
  =?  j.a  (gte np 2)
    %+  add  j.a
    %+  sub  (lent body.b)
    (add (lent body.c) (sub (n-op %mov (my [p.i.ps b]~)) (n-op %mov (my [p.i.ps c]~))))
  =?  f.a  &((two fin.b) ?=([%hop *] fin.c))  +(f.a)
  =?  z.a  &(?=([%brn *] fin.b) ?=([%brz *] fin.c))  +(z.a)
  =?  m.a  &(?=([%brn *] fin.b) ?=([%bom *] fin.c))  +(m.a)
  =/  nd=@ud  ~(wyt in (silt `(list @)`(~(get ja rev) p.i.ps)))
  =/  ts=(unit @)
    ?.  ?=([?(%clq %brn %brz) @ *] fin.b)  ~
    `+<.fin.b
  =/  dst
    |=  p=*
    ^-  (unit @)
    ?:  ?=([?(%imm %mov %inc %hed %tal) * @] p)  `+>.p
    ?:  ?=([?(%con %spy %nok %cal %csl) * * @] p)  `+>+.p
    ?:  ?=([?(%caf %cam %csf %csm) * * @ *] p)  `+>+<.p
    ~
  =/  loc  |=(r=@ (lien body.b |=(p=* =(`r (dst p)))))
  =/  chg  ?|(&((two fin.b) ?=([%hop *] fin.c)) &(?=([%brn *] fin.b) ?=([?(%brz %bom) *] fin.c)))
  =?  g.a  &((gte nd 2) chg ?=(^ ts) !(loc u.ts))  +(g.a)
  $(ps t.ps)
=|  cnt=[comp=@ud calls=@ud acted=@ud mov=@ud oth=@ud join=@ud fold=@ud brz=@ud bom=@ud drop=@ud jfold=@ud runs=@ud bad=@ud]
|-  ^-  @
?~  cases
  ~&  [%summary cnt]
  0
=/  fol=^  ?>(?=(^ fol.i.cases) fol.i.cases)
=/  run-kind
  |=  [kno=? sub=*]
  ^-  [(list [@ud @ud @ud @ud @ud @ud @ud @ud]) straight-out _state]
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [?:(kno [& sub] [| ~]) fol] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  =|  log=(list [@ud @ud @ud @ud @ud @ud @ud @ud])
  =/  s=straight  raw
  |-
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
  =/  pre  blocks.s
  =^  f-alias=?  blocks.s  (alias n-args.s blocks.s rev topo)
  =.  log  [(acts pre blocks.s rev) log]
  =.  topo  (skim topo ~(has by blocks.s))
  =.  rev  (rev-cfg blocks.s (sy topo))
  =.  blocks.s  (trim-trace-hints blocks.s topo rev)
  =.  blocks.s  (remove-dead-code blocks.s (flop topo))
  =^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)
  =^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)
  =^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)
  ?:  |(f-alias c-hops c-branch c-middle)  $
  =/  out=straight-out  s(blocks (switch-chains blocks.s))
  ?>  =(out (optimize raw))
  [log out state]
=/  tally
  |=  [c=_cnt log=(list [@ud @ud @ud @ud @ud @ud @ud @ud])]
  ^+  cnt
  ?~  log  c
  =/  [a=@ud b=@ud j=@ud f=@ud z=@ud m=@ud d=@ud g=@ud]  i.log
  =/  any  !=(0 :(add a b f z m d))
  %=  $
    log  t.log
    calls.c  +(calls.c)
    acted.c  ?:(any +(acted.c) acted.c)
    mov.c  (add mov.c a)
    oth.c  (add oth.c b)
    join.c  (add join.c j)
    fold.c  (add fold.c f)
    brz.c  (add brz.c z)
    bom.c  (add bom.c m)
    drop.c  (add drop.c d)
    jfold.c  (add jfold.c g)
  ==
=/  u  (run-kind | 0)
=.  state  +>.u
=/  code=straight-out  +<.u
~&  [nam.i.cases %unknown (flop -.u)]
=.  cnt  (tally cnt(comp +(comp.cnt)) -.u)
=/  ss  subs.i.cases
|-  ^-  @
?^  ss
  =/  a=toon  (mook (mink [i.ss fol] ~))
  =/  blob  (~(got by blocks.code) 0w0)
  =/  ton=tone  -:(eval-blob [[[`@`0 `i.ss] ~ ~] ~] blob code ~ ~)
  =/  b=toon  -:(eval-mook ton)
  =/  k  (run-kind & i.ss)
  =.  state  +>.k
  =.  cnt  (tally cnt(comp +(comp.cnt)) -.k)
  =/  ton2=tone  -:(eval-top [i.ss fol] ~)
  =/  c=toon  -:(eval-mook ton2)
  =.  runs.cnt  (add 2 runs.cnt)
  =/  ok  &(=(a b) =(a c))
  =?  bad.cnt  !ok  +(bad.cnt)
  ~?  !ok  [nam.i.cases %differ sub=i.ss mock=a unknown=b known=c]
  $(ss t.ss)
^$(cases t.cases)
