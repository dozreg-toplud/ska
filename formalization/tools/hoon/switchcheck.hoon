::  +switch-chains on formulas made to have chains of tests of one
::  register.  For every case: the rounds of +optimize replayed by
::  +optimize-once, then +switch-chains; whether it fired (its output is not
::  its input) and how many %lti ends it made; then the optimized code of the
::  subject unknown run by +eval-blob, and +eval-top (subject known), both
::  through +eval-mook, against +mook of +mink on every subject of the case
::
::  a test of the head of the subject against .c (as ?= of [%c *]), and
::  the same with the operands of %5 swapped
::
=/  tag   |=(c=@ [6 [3 0 1] [5 [1 c] [0 2]] [1 1]])
=/  tag2  |=(c=@ [6 [3 0 1] [5 [0 2] [1 c]] [1 1]])
::  a test of the subject itself against .c, both orders
::
=/  pla   |=(c=@ [5 [1 c] [0 1]])
=/  pla2  |=(c=@ [5 [0 1] [1 c]])
::  a chain: tests .ts with hits .hs, default .df
::
=/  chn
  |=  [ts=(list *) hs=(list *) df=*]
  ^-  *
  ?~  ts  df
  ?~  hs  df
  [6 i.ts i.hs $(ts t.ts, hs t.hs)]
=/  ks   |=(n=@ (turn (gulf 1 n) |=(i=@ [1 (mul 10 i)])))
=/  tg   |=(cs=(list @) (turn cs tag))
=/  tg2  |=(cs=(list @) (turn cs tag2))
=/  pl   |=(cs=(list @) (turn cs pla))
=/  pl2  |=(cs=(list @) (turn cs pla2))
=/  big  (bex 31)
=/  cases=(list [nam=@tas fol=* subs=(list *)])
  :~  [%tag4 (chn (tg ~[1 2 3 4]) (ks 4) [1 99]) ~[[1 0] [2 0] [3 0] [4 0] [5 0] 0 [[1 2] 3] [big 0]]]
      [%tag4-crash (chn (tg ~[1 2 3 4]) (ks 4) [0 0]) ~[[1 0] [2 0] [3 0] [4 0] [5 0] 0 [[1 2] 3]]]
      [%tag5 (chn (tg ~[7 3 9 1 5]) (ks 5) [1 99]) ~[[7 0] [3 0] [9 0] [1 0] [5 0] [2 0] 0 [[1 2] 3]]]
      [%tag8 (chn (tg ~[8 7 6 5 4 3 2 1]) (ks 8) [0 3]) ~[[8 1] [1 2] [4 3] [5 4] [0 5] [9 6] 7 [[1 2] 3]]]
      [%tag3 (chn (tg ~[1 2 3]) (ks 3) [1 99]) ~[[1 0] [2 0] [3 0] [4 0] 0]]
      [%tag-dup (chn (tg ~[1 2 1 3 2]) (ks 5) [1 99]) ~[[1 0] [2 0] [3 0] [4 0] 0]]
      [%tag-dup4 (chn (tg ~[5 5 5 5 6]) (ks 5) [1 99]) ~[[5 0] [6 0] [4 0] 0]]
      [%tag-swap (chn (tg2 ~[1 2 3 4 5]) (ks 5) [1 99]) ~[[1 0] [2 0] [3 0] [4 0] [5 0] [6 0] 0]]
      [%tag-big (chn (tg ~[1 2 big 3 4]) (ks 5) [1 99]) ~[[1 0] [2 0] [big 0] [3 0] [4 0] [5 0] 0]]
      [%tag-hit-tail (chn (tg ~[1 2 3 4]) ~[[0 3] [4 0 3] [0 2] [0 1]] [0 3]) ~[[1 0] [2 0] [3 0] [4 0] [5 5] [2 [1 1]] 0]]
      [%tag-mixed (chn ~[(tag 1) (tag 2) (pla2 0) (tag 3) (tag 4) (tag 5) (tag 6)] (ks 7) [1 99]) ~[[1 0] [2 0] [3 0] [4 0] [5 0] [6 0] [7 0] 0]]
      [%tag-other (chn ~[(tag 1) (tag 2) [5 [1 3] [0 3]] (tag 3) (tag 4) (tag 5) (tag 6)] (ks 7) [1 99]) ~[[1 0] [2 3] [2 0] [3 3] [4 0] [5 0] [6 0] 0]]
      [%tag-nest (chn (tg ~[1 2 3 4]) ~[[7 [0 3] (chn (tg ~[5 6 7 8]) (ks 4) [1 77])] [1 2] [1 3] [1 4]] [1 99]) ~[[1 5 0] [1 6 0] [1 8 0] [1 9 0] [1 0] [2 0] [5 0] [1 7] 0]]
      [%pla4 (chn (pl ~[1 2 3 4]) (ks 4) [1 99]) ~[1 2 3 4 5 0 [1 2] big]]
      [%pla4-crash (chn (pl ~[1 2 3 4]) (ks 4) [0 0]) ~[1 2 3 4 5 0 [1 2]]]
      [%pla5 (chn (pl ~[9 3 7 1 5]) (ks 5) [1 99]) ~[9 3 7 1 5 2 [1 2]]]
      [%pla-swap (chn (pl2 ~[1 2 3 4 5]) (ks 5) [1 99]) ~[1 2 3 4 5 6 [1 2]]]
      [%pla3 (chn (pl ~[1 2 3]) (ks 3) [1 99]) ~[1 2 3 4]]
      [%pla-dup (chn (pl ~[1 2 1 3 2 4]) (ks 6) [1 99]) ~[1 2 3 4 5]]
      [%pla-big (chn (pl ~[1 2 big 3 4]) (ks 5) [1 99]) ~[1 2 3 4 big 5]]
      [%pla9 (chn (pl ~[0 1 2 3 4 5 6 7 8]) (ks 9) [0 0]) ~[0 1 2 3 4 5 6 7 8 9 [0 0]]]
      [%pla-hit-subj (chn (pl ~[1 2 3 4]) ~[[0 1] [4 0 1] [1 0] [0 1]] [4 0 1]) ~[1 2 3 4 5 [1 2]]]
      [%pla-nest (chn (pl ~[1 2 3 4]) ~[[7 [1 6] (chn (pl ~[5 6 7 8]) (ks 4) [1 77])] [1 2] [1 3] [1 4]] [1 99]) ~[1 2 3 4 5]]
      [%pla-head [7 [0 2] (chn (pl ~[1 2 3 4]) (ks 4) [1 99])] ~[[1 0] [2 0] [3 0] [4 0] [5 0] 0 [[1 2] 3]]]
      [%pla-mixed (chn ~[(pla 1) (pla 2) (tag 3) (pla 4) (pla 5) (pla 6) (pla 7)] (ks 7) [1 99]) ~[1 2 3 4 5 6 7 8 [3 0] [4 0]]]
      [%pla-in-tag (chn (tg ~[1 2 3 4]) ~[[7 [0 3] (chn (pl ~[5 6 7 8]) (ks 4) [1 77])] [1 2] [1 3] [1 4]] [1 99]) ~[[1 5] [1 6] [1 8] [1 9] [1 0 0] [2 0] [5 0] 0]]
  ==
::  the model of lemmas/Ska/OptSwitch.lean (switchChains), written again
::  with lists, on the blocks as nouns (the library's list types do not
::  fuse with ours): usesOf, testOf, chainOf, plainOf, plainsOf, casesOf
::  (hsort, casesAcc), stree, nexOf, freshIds, switchTag, switchPlain,
::  switchWalk
::
=*  mb  ,[par=(list @) body=(list *) fin=*]
=/  m-ment
  |=  b=blob
  ^-  (list @uvre)
  =/  x=(list @uvre)  (get-regs fin.b)
  =/  y=(list @uvre)  (zing (turn `(list $%(pole termin))`body.b get-regs))
  =/  z=(list @uvre)  par.b
  (weld z (weld x y))
=/  m-uses
  |=  [bl=(map @uwoo blob) r=@]
  ^-  @ud
  =/  l=(list @)  (zing (turn ~(val by bl) m-ment))
  (lent (skim l |=(x=@ =(x r))))
=/  m-small  |=(n=* ^-((unit @) ?.(?=(@ n) ~ ?.((lth n (bex 31)) ~ `n))))
=*  mt  ,[s=@ c=@ hit=@ miss=@ y=@ d=@ r=@]
=*  mp  ,[d=@ c=@ hit=@ miss=@ r=@]
=*  mc  ,[c=@ hit=@ r=@]
=/  m-test
  |=  [bl0=(map @uwoo blob) bl=(map @ mb) rev=(jar @uwoo @uwoo) p=@]
  ^-  (unit mt)
  =/  b  (~(got by bl) p)
  =/  f  fin.b
  ?.  ?=([%clq @ [~ @] [~ @]] f)  ~
  =/  y  +.+>-.f
  =/  n  +.+>+.f
  ?.  =((~(get ja rev) y) ~[p])  ~
  =/  yb  (~(got by bl) y)
  ?.  =(~ par.yb)  ~
  =/  g  fin.yb
  ?.  ?=([%eqq @ @ [~ @] [~ @]] g)  ~
  ?.  =(n +.+>+>.g)  ~
  =/  bod  body.yb
  ?.  ?=([* * ~] bod)  ~
  =/  i0  i.bod
  =/  i1  i.t.bod
  =/  h=(unit [@ @])
    ?:  ?=([%hed @ @] i0)  `[+<.i0 +>.i0]
    ?:  ?=([%hed @ @] i1)  `[+<.i1 +>.i1]
    ~
  =/  m=(unit [* @])
    ?:  ?=([%imm * @] i0)  `[+<.i0 +>.i0]
    ?:  ?=([%imm * @] i1)  `[+<.i1 +>.i1]
    ~
  ?~  h  ~
  ?~  m  ~
  ?.  =(-.u.h +<.f)  ~
  =/  c  (m-small -.u.m)
  ?~  c  ~
  ?.  |(=([+<.g +>-.g] [+.u.h +.u.m]) =([+<.g +>-.g] [+.u.m +.u.h]))  ~
  ?.  &(=(2 (m-uses bl0 +.u.h)) =(2 (m-uses bl0 +.u.m)))  ~
  `[+<.f u.c +.+>+<.g n y +.u.h +.u.m]
=/  m-chain
  |=  [bl0=(map @uwoo blob) bl=(map @ mb) rev=(jar @uwoo @uwoo) p=@]
  ^-  (list mt)
  =/  t  (m-test bl0 bl rev p)
  ?~  t  ~
  :-  u.t
  =/  nb  (~(got by bl) miss.u.t)
  ?.  &(=(~ par.nb) =(~ body.nb))  ~
  =/  rm  (~(get ja rev) miss.u.t)
  ?.  |(=(rm ~[p y.u.t]) =(rm ~[y.u.t p]))  ~
  =/  t2  (m-test bl0 bl rev miss.u.t)
  ?~  t2  ~
  ?.  =(s.u.t2 s.u.t)  ~
  $(p miss.u.t)
=/  m-imm-into
  |=  [l=@ r=@ bod=(list *)]
  ^-  (unit [* @])
  ?~  bod  ~
  =/  i  i.bod
  ?:  &(?=([%imm * @] i) |(=(+>.i l) =(+>.i r)))  `[+<.i +>.i]
  $(bod t.bod)
=/  m-plain
  |=  [bl0=(map @uwoo blob) bl=(map @ mb) p=@]
  ^-  (unit mp)
  =/  b  (~(got by bl) p)
  =/  g  fin.b
  ?.  ?=([%eqq @ @ [~ @] [~ @]] g)  ~
  =/  m  (m-imm-into +<.g +>-.g body.b)
  ?~  m  ~
  =/  c  (m-small -.u.m)
  ?~  c  ~
  ?:  =(+<.g +>-.g)  ~
  ?.  =(2 (m-uses bl0 +.u.m))  ~
  `[?:(=(+.u.m +<.g) +>-.g +<.g) u.c +.+>+<.g +.+>+>.g +.u.m]
=/  m-plains
  |=  [bl0=(map @uwoo blob) bl=(map @ mb) rev=(jar @uwoo @uwoo) p=@]
  ^-  (list [p=@ t=mp])
  =/  t  (m-plain bl0 bl p)
  ?~  t  ~
  :-  [p u.t]
  =/  nb  (~(got by bl) miss.u.t)
  ?.  =(~ par.nb)  ~
  =/  bod  body.nb
  ?.  ?=([[%imm *] ~] bod)  ~
  ?.  =((~(get ja rev) miss.u.t) ~[p])  ~
  =/  t2  (m-plain bl0 bl miss.u.t)
  ?~  t2  ~
  ?.  =(d.u.t2 d.u.t)  ~
  $(p miss.u.t)
=/  m-hsort
  |=  l=(list mc)
  ^-  (list mc)
  ?~  l  ~
  =/  p  (skim t.l |=(x=mc (lth c.x c.i.l)))
  =/  q  (skip t.l |=(x=mc (lth c.x c.i.l)))
  (weld $(l p) [i.l $(l q)])
=/  m-cases
  |=  ces=(list mc)
  =|  [saw=(list @) acc=(list mc)]
  |-  ^-  (list mc)
  ?~  ces  (m-hsort acc)
  ?^  (find ~[c.i.ces] saw)  $(ces t.ces)
  $(ces t.ces, saw [c.i.ces saw], acc [i.ces acc])
=/  m-tree
  |=  [d=@ mis=@ cas=(list mc) ids=(list @) out=(map @ *)]
  ^-  [(list *) * (list @) (map @ *)]
  ?>  ?=(^ cas)
  ?~  t.cas
    [~[[%imm c.i.cas r.i.cas]] [%eqq d r.i.cas [~ hit.i.cas] [~ mis]] ids out]
  =/  haf  (div (lent cas) 2)
  =/  hi  (slag haf `(list mc)`cas)
  ?>  ?=(^ hi)
  ?>  ?=([* * *] ids)
  =/  l  $(cas (scag haf `(list mc)`cas), ids t.t.ids)
  =/  lout  (~(put by +>+.l) i.ids [~ -.l +<.l])
  =/  r  $(cas hi, ids +>-.l, out lout)
  [~ [%lti c.i.hi d [~ i.ids] [~ i.t.ids]] +>-.r (~(put by +>+.r) i.t.ids [~ -.r +<.r])]
=/  m-fresh
  |=  [ids=(list @) ned=@ud nex=@]
  |-  ^-  [(list @) @]
  ?:  (gte (lent ids) ned)  [ids nex]
  $(ids [nex ids], nex +(nex))
=/  m-switch
  |=  bl0=(map @uwoo blob)
  ^-  (map @ *)
  =/  bl  ;;((map @ mb) bl0)
  =/  topo=(list @)  (bb-topo bl0)
  =/  rev  (rev-cfg bl0 (sy (bb-topo bl0)))
  =/  out=(map @ *)  bl
  =|  done=(list @)
  =/  ks=(list @)  ~(tap in ~(key by bl))
  =/  nex=@  (roll ks |=([o=@ m=@] ?:((gte o m) +(o) m)))
  |-  ^-  (map @ *)
  ?~  topo  out
  ?^  (find ~[i.topo] done)  $(topo t.topo)
  =/  cs=(list mt)  (m-chain bl0 bl rev i.topo)
  ?:  (gte (lent cs) 4)
    ?>  ?=(^ cs)
    =/  mis  miss:(rear cs)
    =/  ids=(list @)  (weld (turn t.cs |=(t=mt y.t)) (turn (snip `(list mt)`cs) |=(t=mt miss.t)))
    =.  done  (weld ids done)
    =.  out  (roll ids |=([o=@ a=_out] (~(del by a) o)))
    =/  cas  (m-cases (turn `(list mt)`cs |=(t=mt [c hit r]:t)))
    =/  nod  (m-tree d.i.cs mis cas ids out)
    =.  out  (~(put by +>+.nod) y.i.cs [~ [[%hed s.i.cs d.i.cs] -.nod] +<.nod])
    =/  b  (~(got by bl) i.topo)
    =.  out  (~(put by out) i.topo [par.b body.b [%clq s.i.cs [~ y.i.cs] [~ mis]]])
    $(topo t.topo)
  =/  ps=(list [p=@ t=mp])  (m-plains bl0 bl rev i.topo)
  ?:  (lth (lent ps) 4)  $(topo t.topo)
  ?>  ?=(^ ps)
  =/  mis  miss.t:(rear ps)
  =/  old=(list @)  (turn t.ps |=([p=@ *] p))
  =.  done  (weld old done)
  =.  out  (roll old |=([o=@ a=_out] (~(del by a) o)))
  =/  cas  (m-cases (turn `(list [p=@ t=mp])`ps |=(x=[p=@ t=mp] [c hit r]:t.x)))
  =/  ned  (sub (mul 2 (lent cas)) 2)
  =/  fr  (m-fresh (scag ned old) ned nex)
  =.  nex  +.fr
  =/  nod  (m-tree d.t.i.ps mis cas -.fr out)
  =/  b  (~(got by bl) i.topo)
  =/  bod=(list *)  (skip body.b |=(op=* &(?=([%imm * @] op) =(+>.op r.t.i.ps))))
  =.  out  (~(put by +>+.nod) i.topo [par.b (weld bod -.nod) +<.nod])
  $(topo t.topo)
=|  cnt=[cases=@ud fired=@ud lti=@ud runs=@ud bad=@ud mis=@ud]
|-  ^-  @
?~  cases
  ~&  [%summary cnt]
  0
=/  fol=^  ?>(?=(^ fol.i.cases) fol.i.cases)
=/  run-kind
  |=  [kno=? sub=*]
  ^-  [? @ud straight-out _state]
  =^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
    (ska-poke [?:(kno [& sub] [| ~]) fol] long-ska.state ~(key by jets-hot.state))
  =^  scc=(set bell)  sccs.cache.state
    (scc-of func calls.long-ska.state sccs.cache.state)
  =^  raw=straight  cache.state  (compiled-mono func scc)
  =/  pre=straight
    =/  s=straight  raw
    |-  ^-  straight
    =/  o  (optimize-once s)
    ?.  -.o  +.o
    $(s +.o)
  =/  bo=(map @uwoo blob-out)  (switch-chains blocks.pre)
  =/  mo  (m-switch blocks.pre)
  ~?  !=(`*`mo `*`bo)  [%model-differs pre=blocks.pre real=bo model=mo]
  =/  out=straight-out  pre(blocks bo)
  ?>  =(out (optimize raw))
  =/  nl=@ud
    %-  lent
    %+  skim  ~(val by bo)
    |=(b=blob-out ?=(%lti -.fin.b))
  [!=(`*`bo `*`blocks.pre) nl out state]
=/  u  (run-kind | 0)
=.  state  +>+.u
=/  code=straight-out  +>-.u
~&  [nam.i.cases %unknown fired=-.u lti=+<.u]
=.  cnt  cnt(cases +(cases.cnt), lti (add lti.cnt +<.u))
=?  fired.cnt  -.u  +(fired.cnt)
=/  ss  subs.i.cases
|-  ^-  @
?^  ss
  =/  a=toon  (mook (mink [i.ss fol] ~))
  =/  blob  (~(got by blocks.code) 0w0)
  =/  ton=tone  -:(eval-blob [[[`@`0 `i.ss] ~ ~] ~] blob code ~ ~)
  =/  b=toon  -:(eval-mook ton)
  =/  k  (run-kind & i.ss)
  =.  state  +>+.k
  =.  cnt  cnt(cases +(cases.cnt), lti (add lti.cnt +<.k))
  =?  fired.cnt  -.k  +(fired.cnt)
  ~?  -.k  [nam.i.cases %known-fired i.ss]
  =/  ton2=tone  -:(eval-top [i.ss fol] ~)
  =/  c=toon  -:(eval-mook ton2)
  =.  runs.cnt  (add 2 runs.cnt)
  =/  ok  &(=(a b) =(a c))
  =?  bad.cnt  !ok  +(bad.cnt)
  ~?  !ok  [nam.i.cases %differ sub=i.ss mock=a unknown=b known=c]
  $(ss t.ss)
^$(cases t.cases)
