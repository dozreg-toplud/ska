::  The baking half of +ska-poke against the model (track P, README Gaps 23,
::  SpRestGood step 1): 21 %full pokes in a row (fresh state first; two ~%
::  roots; repeats whose root is in the memo; a mutual recursion).  At each
::  poke, from the state before it, the driver reruns the analysis half of
::  +ska-poke as the arm does (dats, memo, dat, root-bell, jetted,
::  +bake-graph), calls +ska-poke itself, and prints, per poke, whether:
::  %root  the root bell is [less-code.root-datum fol]          (E.root)
::  %memo  memo.lon' is the memo of the =^ dats                (r.2.2.1)
::  %vars  vars.lon' is the vars of +bake-graph                 (bg.2)
::  %keys  code, calls, seek of lon' have the keys of code.lon and baked
::  %old   an old bell keeps its code, calls, seek entries     (addCode)
::  %new   a new bell's nomm, calls, seek are baked's           (newCode)
::  %same  baked bells already in code.lon are skipped          (newCode)
::  %close every callee of an entry of lon' is a key of code.lon'
::  %flags the flags of every entry of lon' (old and new) are the replay
::         of the SCC loop over the WHOLE table of lon' from [| |]
::         (callees first, members in ~(rep in scc) order): the flags are a
::         function of the table, not of the history of pokes
::  %jets  jets.lon' is +ska-cole-update of jets.lon with root, core, batt,
::         arms of the regs and pend uni-ju the new cores, on the new keys
::  and the counts: new bells, SCCs of new-code, the largest SCC.
::
=/  fk=*
  !=
  =>  ~
  =<  a
  ~%  %k  ~  ~
  |%
  ++  a  42
  --
=/  fc=*
  !=
  =>  ~
  =<  b
  ~%  %c  ~  ~
  |%
  ++  a  42
  ++  b  [a 3]
  --
=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  even=*  [6 [5 [1 0] 0 6] [1 0] 6 [5 [1 1] 0 6] [1 1] 9 2 10 [6 8 [9 2 10 [6 0 14] 0 7] 9 2 0 1] 0 1]
=/  ma=*  [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  mc=*  [6 [3 [0 3]] [8 [9 5 [10 [3 [0 7]] [0 1]]] [9 4 [10 [3 [0 15]] [0 3]]]] [1 2]]
=/  pairs=(list [* *])
  :~  [0 fk]
      [0 [4 0 1]]
      [0 fc]
      [[0 [fid [fw fm2]]] [0 0]]
      [5 [0 1]]
      [7 dec]
      [0 fk]
      [[0 [fid [fw fm2]]] fid]
      [9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [3 [11 1.886.217.588 [1 0]]]
      [4 [11 [1.886.217.588 1 1] 0 1]]
      [[0 [fid [fw fm2]]] [2 [0 1] 1 fid]]
      [[0 [fw fm2]] [2 [0 1] 0 2]]
      [[even [5 0]] [9 2 0 1]]
      [0 [4 0 1]]
      [7 dec]
      [[0 [fid [fw fm2]]] fid]
      [0 fc]
      [[[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [[[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [[[ma mb] [9 8 7 0]] [9 5 [0 1]]]
  ==
=/  replay
  |=  lon=long-ska
  ^-  (map bell code-entry)
  =/  tab=(map bell code-entry)
    (~(run by code.lon) |=(e=code-entry e(pure |, total |)))
  ?:  =(~ tab)  tab
  =/  sccs=(list (set bell))
    %-  flop
    %-  tarjan
    ^-  (jug bell bell)
    %-  ~(rep by calls.lon)
    |=  [[b=bell cs=(set bell)] acc=(jug bell bell)]
    (~(put by acc) b (silt (skim ~(tap in cs) |=(c=bell (~(has by code.lon) c)))))
  |-  ^-  (map bell code-entry)
  ?~  sccs  tab
  =/  loc2=(map bell code-entry)
    %-  ~(rep in i.sccs)
    |=  [b=bell acc=_tab]
    =/  [pure=? total=?]  (eval-finalized b acc)
    (~(jab by acc) b |=(e=code-entry e(pure pure, total total)))
  $(sccs t.sccs, tab loc2)
=|  n=@ud
|-
?~  pairs  0
=/  lon=long-ska  long-ska.state
=/  hot=(set ring)  ~(key by jets-hot.state)
=/  fol=^  ;;(^ +.i.pairs)
=/  root-identity=identity  [[& -.i.pairs] fol]
=/  [g=callgraph =regs]
  (ska-callgraph root-identity memo.lon [root core batt arms ~]:jets.lon)
=/  pruned=callgraph  (prune-callgraph g root-identity)
=/  root-datum=datum  (~(got by pruned) root-identity)
=/  [dats=(map bell datum) memo=_memo.lon]
  %-  ~(rep by pruned)
  |=  [[id=identity d=datum] dats=(map bell datum) =_memo.lon]
  :-  (~(put by dats) [less-code.d fol.id] d)
  =/  entry  (memo-final-entry id d)
  (put:mi memo -.entry +.entry)
=.  memo.lon  memo
=/  dat
  |=  b=bell
  ^-  (unit datum)
  ?^  d=(~(get by dats) b)  d
  ?^  m=(~(get by (gut:mi memo.lon fol.b)) less.b)  `+.u.m
  ~
=/  root-bell=bell  [less-code.root-datum fol]
=/  jetted
  |=  c=bell
  ^-  ?
  ?|  (~(has by call.cole.jets.lon) c)
      ?=(^ (cole-match c ?~(d=(dat c) & seek.u.d) core.regs arms.regs hot))
  ==
=/  [baked=(map bell [=nomm calls=(set bell) seek=cape]) vars=(jug bell bell)]
  (bake-graph root-bell dat jetted vars.lon)
=/  old=long-ska  long-ska.state
=/  [[rb=bell new=*] lon1=long-ska]
  (ska-poke [[& -.i.pairs] fol] old hot)
=/  new-keys=(set bell)
  (silt (skim ~(tap in ~(key by baked)) |=(b=bell !(~(has by code.old) b))))
=/  all-keys=(set bell)  (~(uni in ~(key by code.old)) ~(key by baked))
=/  ok-keys=?
  ?&  =(~(key by code.lon1) all-keys)
      =(~(key by calls.lon1) all-keys)
      =(~(key by seek.lon1) all-keys)
  ==
=/  ok-old=?
  %+  levy  ~(tap in ~(key by code.old))
  |=  b=bell
  ?&  =((~(get by code.lon1) b) (~(get by code.old) b))
      =((~(get by calls.lon1) b) (~(get by calls.old) b))
      =((~(get by seek.lon1) b) (~(get by seek.old) b))
  ==
=/  ok-new=?
  %+  levy  ~(tap in new-keys)
  |=  b=bell
  =/  v  (~(got by baked) b)
  ?&  =(nomm:(~(got by code.lon1) b) nomm.v)
      =((~(got by calls.lon1) b) calls.v)
      =((~(got by seek.lon1) b) seek.v)
  ==
=/  ok-same=?
  %+  levy  ~(tap by baked)
  |=  [b=bell *]
  ?.  (~(has by code.old) b)  &
  =((~(get by code.lon1) b) (~(get by code.old) b))
=/  ok-close=?
  %+  levy  ~(tap by calls.lon1)
  |=  [b=bell cs=(set bell)]
  (levy ~(tap in cs) |=(c=bell (~(has by code.lon1) c)))
=/  ok-flags=?  =((replay lon1) code.lon1)
=/  new-cores=(jug path sock)
  (~(gas ju *(jug path sock)) (turn new.regs |=([p=path s=sock *] [p s])))
=/  jets-want=long-ska
  =/  l=long-ska  lon1
  =.  jets.l
    %=  jets.old
      root  root.regs
      core  core.regs
      batt  batt.regs
      arms  arms.regs
      pend  ((uni-ju pend.jets.old) new-cores)
    ==
  (ska-cole-update l new-keys hot)
=/  ok-jets=?  =(jets.lon1 jets.jets-want)
=/  nsccs=(list (set bell))
  ?:  =(~ new-keys)  ~
  %-  tarjan
  ^-  (jug bell bell)
  %-  ~(rep in new-keys)
  |=  [b=bell acc=(jug bell bell)]
  =/  v  (~(got by baked) b)
  (~(put by acc) b (silt (skim ~(tap in calls.v) |=(c=bell (~(has in new-keys) c)))))
=/  big=@ud  (roll (turn nsccs |=(s=(set bell) ~(wyt in s))) max)
~&  :*  %p  n  %root  =(rb root-bell)  %memo  =(memo.lon1 memo)  %vars  =(vars.lon1 vars)
        %keys  ok-keys  %old  ok-old  %new  ok-new  %same  ok-same  %close  ok-close
        %flags  ok-flags  %jets  ok-jets
        %nnew  ~(wyt in new-keys)  %nsccs  (lent nsccs)  %big  big  %ncode  ~(wyt by code.lon1)
    ==
=^  p  ..poke  (poke [%full -.i.pairs fol])
=/  ok-poke=?  =(long-ska.state lon1)
~?  !ok-poke  [%p n %poke-differs]
$(pairs t.pairs, n +(n))
