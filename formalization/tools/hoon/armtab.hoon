::  armtab.hoon (track T, README Gaps 32): the arm table of the library's
::  core, read from its TYPE (the library's +need is a mold: not used here).  The test's subject is the library's core, so
::  -:!>(.) is the type that the compiler gave it.  The walk:
::
::    the spine: the payload of the subject, through %cell (a =/ pushes a
::    cell) and %core, each %core a spine core `s<i>` at its axis;
::
::    each core: every arm of its battery (the chapters of the coil), with
::    its axis in the battery (+loot) and in the core (+peg 2), and the type
::    of its product (+play of the limb, %holds opened with +repo, at most
::    20 deep); a product that is a core is told apart by its payload:
::    the payload is the arm's subject (%core, %trap if its battery is the
::    one arm $), or a cell of a sample and that subject (%door, %gate), or
::    anything else (%cory, e.g. a core under a =/);
::
::    descent: into every product that is a core, to depth 4 from a spine
::    core of the library and 1 from one of hoon.hoon (the cores from the
::    one with +ride down), each battery once (by mug of its chapters).
::
::  Rows, one ~& cord each, tab-separated, between 'armtab-begin' and
::  'armtab-end' (the harness evaluates twice: tools/armtab/armtab.py keeps
::  the first block):
::
::    C  path  abs  kind  hoon   a core: abs its axis in the core (- if it
::                               is built at run time), hoon y for hoon.hoon
::    A  path  bax  cax  abs  kind   an arm: bax its axis in the battery,
::                               cax in the core, abs in the subject or -
::
=/  top=type  -:!>(.)
|^
~&  'armtab-begin'
=/  r  (spine top 1 0 | ~)
~&  'armtab-end'
-.r
::
++  dec-a  |=(n=@ (a-co:co n))
++  pax-t
  |=  pax=(list term)
  ^-  tape
  =/  out=tape  ~
  =/  fir=?  &
  |-  ^-  tape
  ?~  pax  out
  =/  nam=tape  ?:(=(%$ i.pax) "$" (trip i.pax))
  $(pax t.pax, fir |, out ?:(fir nam :(weld out "/" nam)))
++  unh
  |=  t=type
  =|  k=@ud
  |-  ^-  type
  ?:  (gth k 20)  t
  ?+  t  t
    [%hold *]  $(t ~(repo ut t), k +(k))
    [%face *]  $(t q.t)
    [%hint *]  $(t q.t)
  ==
::  the spine of the subject
::
++  spine
  |=  [t=type ax=@ i=@ud hon=? vis=(set @)]
  ^-  [@ud (set @)]
  =.  t  (unh t)
  ?+  t  [0 vis]
    [%cell *]  $(t q.t, ax (peg ax 3))
    [%core *]
    =?  hon  ?=(^ (loot %ride q.r.q.t))  &
    =/  nam=term  (crip "s{(dec-a i)}")
    =^  n  vis  (core t `ax ~[nam] ?:(hon 1 4) hon %spine vis)
    =^  m  vis  $(t p.t, ax (peg ax 3), i +(i))
    [(add n m) vis]
  ==
::  the arms of a core, and the cores they build
::
++  arm-names
  |=  dom=(map term (map term hoon))
  ^-  (list term)
  =|  out=(list term)
  |-  ^-  (list term)
  ?~  dom  out
  =.  out  (names-in q.n.dom out)
  =.  out  $(dom l.dom)
  $(dom r.dom)
::  (no +turn, +sort or +zing over these: wet gates on them fail with
::  fuse-loop, as tools/hoon/README.md says of shapecoldump.hoon)
++  names-in
  |=  [w=(map term hoon) out=(list term)]
  ^-  (list term)
  ?~  w  out
  =.  out  [p.n.w out]
  =.  out  $(w l.w)
  $(w r.w)
++  core
  |=  [t=type ab=(unit @) pax=(list term) lim=@ud hon=? kic=@tas vis=(set @)]
  ^-  [@ud (set @)]
  ?>  ?=([%core *] t)
  =/  dom  q.r.q.t
  ?:  (~(has in vis) (mug dom))  [0 vis]
  =.  vis  (~(put in vis) (mug dom))
  ~&  %-  crip
      ;:  weld  "C\09"  (pax-t pax)  "\09"  ?~(ab "-" (dec-a u.ab))  "\09"
        (trip kic)  "\09"  ?:(hon "y" "n")
      ==
  =/  nams  (arm-names dom)
  =/  cnt=@ud  0
  |-  ^-  [@ud (set @)]
  ?~  nams  [cnt vis]
  =/  nam  i.nams
  =/  lot  (loot nam dom)
  ?>  ?=(^ lot)
  =/  bax=@  p.u.lot
  =/  cax=@  (peg 2 bax)
  =/  abs=(unit @)  ?~(ab ~ `(peg u.ab cax))
  =/  hol=type  (~(play ut t) [%limb nam])
  =/  sub=type  ?:(?=([%hold *] hol) p.hol %void)
  =/  pro=type  (unh hol)
  =/  kin=@tas
    ?.  ?=([%core *] pro)  %value
    =/  one=?  =(~[%$] (arm-names q.r.q.pro))
    ?:  =(p.pro sub)  ?:(one %trap %core)
    =/  pay=type  p.pro
    ?.  ?=([%cell *] pay)  %cory
    ?.  =(q.pay sub)  %cory
    ?:(one %gate %door)
  =/  pat  (weld pax ~[nam])
  ~&  %-  crip
      ;:  weld  "A\09"  (pax-t pat)  "\09"  (dec-a bax)  "\09"  (dec-a cax)
        "\09"  ?~(abs "-" (dec-a u.abs))  "\09"  (trip kin)
      ==
  =^  n  vis
    ?.  &(?=([%core *] pro) (gth lim 0))  [0 vis]
    (core pro ~ pat (dec lim) hon kin vis)
  $(nams t.nams, cnt (add +(cnt) n))
--
