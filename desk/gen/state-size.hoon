::  Sizes of the components of the persistent SKA state after the boot
::  poke and after the ride poke, with the pokes timed.  For each component:
::  entry counts and two sizes, both with the kernel the analysis ran on
::  (its subject and formulas, which the state shares) taken as present
::  already:
::    alone:    the component by itself
::    marginal: what the whole state loses without it, i.e. what it does
::              not share with the other components
::  each in jam bytes and in distinct nouns (cells, and bytes of indirect
::  atoms): sizes as if structure were shared perfectly, which jam does and
::  the loom does only for what was built once.  Then the parts of the
::  datums alone, and the time of the state operations the pokes do.
::
::  Usage: +ska!state-size, =walk | to skip the noun walks
::
/+  *nock-compilation
/+  hoot
/+  hoot-fol
::
=>  |%
    +$  size  [cells=@ud bytes=@ud]
    ::  distinct cells, and bytes of indirect atoms, of .n not in .seen
    ::
    ++  walk-noun
      |=  [n=* seen=(set *)]
      ^-  [size (set *)]
      =|  acc=size
      =/  stk=(list *)  ~[n]
      |-  ^-  [size (set *)]
      ?~  stk  [acc seen]
      =/  i=*  i.stk
      ?:  &(?=(@ i) (lth i (bex 31)))  $(stk t.stk)
      ?:  (~(has in seen) i)  $(stk t.stk)
      =.  seen  (~(put in seen) i)
      ?@  i  $(stk t.stk, bytes.acc (add bytes.acc (met 3 i)))
      $(stk [-.i +.i t.stk], cells.acc +(cells.acc))
    ::
    ++  jam-size  |=(n=* (met 3 (jam n)))
    ::
    ++  jug-edges
      |=  j=(map * (set *))
      ^-  @ud
      (~(rep by j) |=([[* s=(set *)] n=@ud] (add n ~(wyt in s))))
    ::
    ++  memo-entries
      |=  m=memo
      ^-  @ud
      (~(rep by m) |=([[* i=(map sock *)] n=@ud] (add n ~(wyt by i))))
    ::  the memoized functions
    ::
    ++  memo-list
      |=  m=memo
      ^-  (list [id=identity d=datum])
      %-  zing
      %+  turn  ~(val by m)
      |=(i=(map sock [id=identity =datum]) ~(val by i))
    ::
    ++  kb  |=(b=@ud "{(scow %ud (div b 1.024))}KB")
    ++  ks  |=(s=size "{(scow %ud cells.s)} cells, {(kb bytes.s)} atoms")
    --
::
:-  %say  |=  [* ~ walk=_&]
=*  do-walk  walk
=/  subject  ..ride:hoot
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::  what the state shares with the world: not counted
::
=/  base=*  [subject hoot-fol formula]
=|  lon=long-ska
=.  lon
  ~>  %bout.[0 leaf+"boot poke"]
  +:(ska-poke [&+~ hoot-fol] lon)
=/  boot=long-ska  lon
=^  res  lon
  ~>  %bout.[0 leaf+"ride poke"]
  (ska-poke [&+subject formula] lon)
=/  ride=long-ska  lon
=/  root=bell  -.res
::  the same poke on the state that has it: memo hits only
::
=^  res-again  lon
  ~>  %bout.[0 leaf+"ride poke again (memo hits)"]
  (ska-poke [&+subject formula] ride)
?>  =(root -.res-again)
::
=/  base-jam=@ud  (jam-size base)
=|  seen=(set *)
=^  base-size=size  seen
  ?.  do-walk  [*size ~]
  ~>  %bout.[0 leaf+"walk kernel"]
  (walk-noun base ~)
=/  over-jam  |=(n=* (sub (jam-size [base n]) base-jam))
=/  over-walk
  |=  n=*
  ^-  size
  ?.  do-walk  *size
  -:(walk-noun n seen)
::
=/  parts=(list [name=tape get=$-(long-ska *) del=$-(long-ska long-ska)])
  :~  ["jets" |=(l=long-ska jets.l) |=(l=long-ska l(jets [~ ~ ~ ~ ~ ~ ~]))]
      ["memo" |=(l=long-ska memo.l) |=(l=long-ska l(memo ~))]
      ["code" |=(l=long-ska code.l) |=(l=long-ska l(code ~))]
      ["calls" |=(l=long-ska calls.l) |=(l=long-ska l(calls ~))]
      ["vars" |=(l=long-ska vars.l) |=(l=long-ska l(vars ~))]
  ==
::
=/  measure
  |=  [label=tape l=long-ska]
  ^-  (list tape)
  =/  whole-jam=@ud  (over-jam l)
  =/  whole-size=size  (over-walk l)
  %+  weld
    ^-  (list tape)
    :~  "== {label}: whole state over the kernel: jam {(kb whole-jam)}, {(ks whole-size)}"
          "   counts: jets root {(scow %ud ~(wyt by root.jets.l))} core {(scow %ud ~(wyt by core.jets.l))} batt {(scow %ud ~(wyt by batt.jets.l))} arms {(scow %ud ~(wyt by arms.jets.l))} pend {(scow %ud ~(wyt by pend.jets.l))} cole {(scow %ud ~(wyt by call.cole.jets.l))}/{(scow %ud ~(wyt by back.cole.jets.l))}"
          "   counts: memo fols {(scow %ud ~(wyt by memo.l))} entries {(scow %ud (memo-entries memo.l))}; code bells {(scow %ud ~(wyt by code.l))}; calls bells {(scow %ud ~(wyt by calls.l))} edges {(scow %ud (jug-edges calls.l))}; vars code bells {(scow %ud ~(wyt by vars.l))} variants {(scow %ud (jug-edges vars.l))}"
      ==
  %+  turn  parts
  |=  [name=tape get=$-(long-ska *) del=$-(long-ska long-ska)]
  =/  alone-jam  (over-jam (get l))
  =/  alone-size  (over-walk (get l))
  =/  rest=long-ska  (del l)
  =/  marg-jam  (sub whole-jam (over-jam rest))
  =/  rest-size  (over-walk rest)
  =/  marg-size=size
    [(sub cells.whole-size cells.rest-size) (sub bytes.whole-size bytes.rest-size)]
  "   {name}: alone jam {(kb alone-jam)}, {(ks alone-size)}; marginal jam {(kb marg-jam)}, {(ks marg-size)}"
::  the parts of the datums, alone over the kernel
::
=/  datum-parts
  |=  l=long-ska
  ^-  (list tape)
  =/  ds=(list [id=identity d=datum])  (memo-list memo.l)
  =/  per=(list [name=tape n=*])
    :~  ["memo identities (subjects masked to indi)" (turn ds |=([id=identity *] more.id))]
        ["callees" (turn ds |=([* d=datum] callees.d))]
        ["nomm" (turn ds |=([* d=datum] nomm.d))]
        ["less-code" (turn ds |=([* d=datum] less-code.d))]
        ["prod+map" (turn ds |=([* d=datum] [prod map]:d))]
        ["indi+area" (turn ds |=([* d=datum] [indi area]:d))]
        ["code entries" ~(val by code.l)]
        ["code keys (bells)" ~(key by code.l)]
    ==
  %+  turn  per
  |=  [name=tape n=*]
  "   datum part {name}: alone jam {(kb (over-jam n))}, {(ks (over-walk n))}"
::  time of the operations the pokes do on the state
::
=/  timings
  |=  l=long-ska
  ^-  (list tape)
  =/  rev=(jug bell bell)
    ~>  %bout.[0 leaf+"reverse calls (as hot-stale)"]
    (reverse-bell-graph calls.l)
  =/  sccs
    ~>  %bout.[0 leaf+"tarjan calls"]
    (tarjan calls.l)
  =/  scc
    ~>  %bout.[0 leaf+"scc-of root in calls, no cache"]
    (scc-of root calls.l ~)
  =/  hits
    ~>  %bout.[0 leaf+"git:mi of every code bell"]
    %+  roll  ~(tap by code.l)
    |=  [[b=bell *] n=@ud]
    ?~((git:mi memo.l fol.b less.b) n +(n))
  :~  "   calls reversed {(scow %ud (jug-edges rev))}; sccs {(scow %ud (lent sccs))}; root scc {(scow %ud ~(wyt in -.scc))}; memo hits for code bells {(scow %ud hits)}"
  ==
::
:-  %tang
%-  flop
%+  turn
  %-  zing
  :~  ~["kernel (subject, formulas): jam {(kb base-jam)}, {(ks base-size)}"]
      (measure "after boot poke" boot)
      (measure "after ride poke" ride)
      (datum-parts ride)
      (timings ride)
      ~["%state-size-done"]
  ==
|=(t=tape leaf+t)
