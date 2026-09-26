::  Bells of the ride poke. With no argument: the sorted list of bell mugs.
::  With a list of mugs: [mug area formula-head less-code-known-axes] of the
::  bells with those mugs, for diffing analysis variants.
::
/+  *nock-compilation
/+  hoot
/+  hoot-fol
::
:-  %say  |=  [* args=* ~]
=/  mugs=(list @ux)  ?~(args ~ ;;((list @ux) -:;;(^ args)))
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-fol] long-ska)
=/  subject  ..ride:hoot
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=/  g  graph.final.long-ska
=/  areas=(map bell (unit spot))
  %-  ~(rep by g)
  |=  [[id=identity d=datum] acc=(map bell (unit spot))]
  (~(put by acc) [less-code.d fol.id] area.d)
::
=/  count-2
  |=  =nomm
  ^-  [direct=@ indirect=@]
  =*  cnt  $
  ?-  nomm
    [^ *]    =/(a $(nomm -.nomm) =/(b $(nomm +.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%0 *]   [0 0]
    [%1 *]   [0 0]
    [%2 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add ?~(info.nomm 0 1) (add direct.a direct.b)) (add ?~(info.nomm 1 0) (add indirect.a indirect.b))]))
    [%3 *]   $(nomm p.nomm)
    [%4 *]   $(nomm p.nomm)
    [%5 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%6 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) =/(c $(nomm r.nomm) [:(add direct.a direct.b direct.c) :(add indirect.a indirect.b indirect.c)])))
    [%7 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%10 *]  =/(a $(nomm q.p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%11 *]  ?@(p.nomm $(nomm q.nomm) =/(a $(nomm q.p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)])))
    [%12 *]  =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
  ==
=/  totals=[direct=@ indirect=@]
  %-  ~(rep by code.long-ska)
  |=  [[b=bell c=code-entry] acc=[direct=@ indirect=@]]
  =/  n  (count-2 nomm.c)
  [(add direct.n direct.acc) (add indirect.n indirect.acc)]
::
::  indirect call sites with their innermost source spot
::
=/  indirect-sites
  |=  =nomm
  =|  here=(unit spot)
  |-  ^-  (list (unit spot))
  ?-  nomm
    [^ *]    (weld $(nomm -.nomm) $(nomm +.nomm))
    [%0 *]   ~
    [%1 *]   ~
    [%2 *]   (weld ?~(info.nomm [here ~] ~) (weld $(nomm p.nomm) $(nomm q.nomm)))
    [%3 *]   $(nomm p.nomm)
    [%4 *]   $(nomm p.nomm)
    [%5 *]   (weld $(nomm p.nomm) $(nomm q.nomm))
    [%6 *]   :(weld $(nomm p.nomm) $(nomm q.nomm) $(nomm r.nomm))
    [%7 *]   (weld $(nomm p.nomm) $(nomm q.nomm))
    [%10 *]  (weld $(nomm q.p.nomm) $(nomm q.nomm))
    [%11 *]  ?@  p.nomm  $(nomm q.nomm)
             =/  spot-here=(unit spot)
               ?.  &(=(%spot p.p.nomm) ?=([%1 *] q.p.nomm))  here
               =/  soft  (soft-spot p.q.p.nomm)
               ?~(soft here soft)
             (weld $(nomm q.p.nomm) $(nomm q.nomm, here spot-here))
    [%12 *]  (weld $(nomm p.nomm) $(nomm q.nomm))
  ==
::
?:  ?=([%0x4 @ ~] mugs)
  =/  axes  |=(c=cape (roll (turn (scag 16 (yea:ca c)) |=(a=@ "{(a-co:co a)} ")) |=([a=tape b=tape] (weld b a))))
  =/  spot-tape
    |=  s=(unit spot)
    ^-  tape
    ?~  s  "~"
    "{(a-co:co p.p.q.u.s)}:{(a-co:co q.p.q.u.s)}"
  :-  %tang
  %-  flop
  %+  turn
    %+  murn  ~(tap by g)
    |=  [id=identity d=datum]
    ?.  =((mug fol.id) i.t.mugs)  ~
    :-  ~
    %-  crip
    ;:  weld
      "FUNCTION {(scow %ux (mug fol.id))} more=[{(axes cape.more.id)}] prod=[{(axes cape.prod.d)}]"
      %-  roll
      :_  |=([a=tape b=tape] (weld b a))
      %+  turn  ~(tap in callees.d)
      |=  c=callee-entry
      =/  cd=datum  (~(gut by g) id.c *datum)
      ;:  weld
        " | {(spot-tape seat.c)} {(scow %ux (mug fol.id.c))}"
        " more=[{(axes cape.more.id.c)}]"
        " less=[{(axes cape.less-code.cd)}]"
        " prod=[{(axes cape.prod.cd)}]"
        ?:((~(has by g) id.c) " in-graph" " NOT-in-graph")
      ==
    ==
  |=(t=@t leaf+(trip t))
?:  =(mugs ~[0x1])
  =/  spot-tape
    |=  s=(unit spot)
    ^-  tape
    ?~  s  "~"
    "{(a-co:co p.p.q.u.s)}:{(a-co:co q.p.q.u.s)}"
  :-  %tang
  %-  flop
  %+  turn
    %+  murn  ~(tap by code.long-ska)
    |=  [b=bell c=code-entry]
    =/  sites  (indirect-sites nomm.c)
    ?~  sites  ~
    :-  ~
    %-  crip
    ;:  weld
      "BELL {(scow %ux (mug b))} fol {(scow %ux (mug fol.b))} area "
      (spot-tape (~(gut by areas) b ~))
      " n={(a-co:co (lent sites))} sites:"
      (roll (turn sites |=(s=(unit spot) " {(spot-tape s)}")) |=([a=tape b=tape] (weld b a)))
    ==
  |=(t=@t leaf+(trip t))
:-  %noun
::  ~[0x3 formula-mug]: the indirect call sites of that formula's bells, as
::  a prefix of the subject expression of each
::
?:  ?=([%0x3 @ ~] mugs)
  =/  sites
    |=  =nomm
    =|  here=(unit spot)
    |-  ^-  (list tape)
    ?-  nomm
      [^ *]    (weld $(nomm -.nomm) $(nomm +.nomm))
      [%0 *]   ~
      [%1 *]   ~
      [%2 *]   %+  weld  ?~(info.nomm [(scag 110 ~(ram re (sell !>([here p.nomm])))) ~] ~)
               (weld $(nomm p.nomm) $(nomm q.nomm))
      [%3 *]   $(nomm p.nomm)
      [%4 *]   $(nomm p.nomm)
      [%5 *]   (weld $(nomm p.nomm) $(nomm q.nomm))
      [%6 *]   :(weld $(nomm p.nomm) $(nomm q.nomm) $(nomm r.nomm))
      [%7 *]   ?:  ?&  ?=([%2 [%0 %1] * ~] q.nomm)
                   ==
                 :-  (scag 130 ~(ram re (sell !>([here core=p.nomm arm=q.q.nomm]))))
                 $(nomm p.nomm)
               (weld $(nomm p.nomm) $(nomm q.nomm))
      [%10 *]  (weld $(nomm q.p.nomm) $(nomm q.nomm))
      [%11 *]  ?@  p.nomm  $(nomm q.nomm)
               =/  spot-here=(unit spot)
                 ?.  &(=(%spot p.p.nomm) ?=([%1 *] q.p.nomm))  here
                 =/  soft  (soft-spot p.q.p.nomm)
                 ?~(soft here soft)
               (weld $(nomm q.p.nomm) $(nomm q.nomm, here spot-here))
      [%12 *]  (weld $(nomm p.nomm) $(nomm q.nomm))
    ==
  %+  murn  ~(tap by code.long-ska)
  |=  [b=bell c=code-entry]
  ?.  =((mug fol.b) i.t.mugs)  ~
  `[`@ux`(mug b) (lent (yea:ca cape.less.b)) (turn (sites nomm.c) crip)]
::  ~[0x4 formula-mug]: callees of that formula's functions: [seat callee
::  formula mug, less-code axes, product known axes, first product axes]
::
::  ~[0x5 formula-mug line]: the analyzed nomm under the spot hint starting
::  on that line, calls marked D (direct) or I (indirect)
::
?:  ?=([%0x5 @ @ ~] mugs)
  =/  render
    |=  =nomm
    ^-  tape
    ?-  nomm
      [^ *]    "[{$(nomm -.nomm)} {$(nomm +.nomm)}]"
      [%0 *]   "0.{(a-co:co p.nomm)}"
      [%1 *]   ?@(p.nomm "1.{(a-co:co p.nomm)}" "1.cell")
      [%2 *]   "(2{?~(info.nomm "I" "D")} {$(nomm p.nomm)} {$(nomm q.nomm)})"
      [%3 *]   "(3 {$(nomm p.nomm)})"
      [%4 *]   "(4 {$(nomm p.nomm)})"
      [%5 *]   "(5 {$(nomm p.nomm)} {$(nomm q.nomm)})"
      [%6 *]   "(6 {$(nomm p.nomm)} {$(nomm q.nomm)} {$(nomm r.nomm)})"
      [%7 *]   "(7 {$(nomm p.nomm)} {$(nomm q.nomm)})"
      [%10 *]  "(10 {(a-co:co p.p.nomm)} {$(nomm q.p.nomm)} {$(nomm q.nomm)})"
      [%11 *]  ?@  p.nomm  "(11 {$(nomm q.nomm)})"
               ?:  =(%spot p.p.nomm)
                 =/  soft  ?.(?=([%1 *] q.p.nomm) ~ (soft-spot p.q.p.nomm))
                 ?~  soft  "(11spot {$(nomm q.nomm)})"
                 "(spot {(a-co:co p.p.q.u.soft)}:{(a-co:co q.p.q.u.soft)} {$(nomm q.nomm)})"
               "(11 {(trip p.p.nomm)} {$(nomm q.p.nomm)} {$(nomm q.nomm)})"
      [%12 *]  "(12 {$(nomm p.nomm)} {$(nomm q.nomm)})"
    ==
  =/  find
    |=  =nomm
    ^-  (unit ^nomm)
    ?-  nomm
      [^ *]    =/(a $(nomm -.nomm) ?^(a a $(nomm +.nomm)))
      [%0 *]   ~
      [%1 *]   ~
      [%2 *]   =/(a $(nomm p.nomm) ?^(a a $(nomm q.nomm)))
      [%3 *]   $(nomm p.nomm)
      [%4 *]   $(nomm p.nomm)
      [%5 *]   =/(a $(nomm p.nomm) ?^(a a $(nomm q.nomm)))
      [%6 *]   =/(a $(nomm p.nomm) ?^(a a =/(b $(nomm q.nomm) ?^(b b $(nomm r.nomm)))))
      [%7 *]   =/(a $(nomm p.nomm) ?^(a a $(nomm q.nomm)))
      [%10 *]  =/(a $(nomm q.p.nomm) ?^(a a $(nomm q.nomm)))
      [%11 *]  ?@  p.nomm  $(nomm q.nomm)
               ?:  ?&  =(%spot p.p.nomm)  ?=([%1 *] q.p.nomm)
                       =/  soft  (soft-spot p.q.p.nomm)
                       ?~(soft | =(p.p.q.u.soft i.t.t.mugs))
                   ==
                 `nomm
               =/(a $(nomm q.p.nomm) ?^(a a $(nomm q.nomm)))
      [%12 *]  =/(a $(nomm p.nomm) ?^(a a $(nomm q.nomm)))
    ==
  %+  murn  ~(tap by code.long-ska)
  |=  [b=bell c=code-entry]
  ?.  =((mug fol.b) i.t.mugs)  ~
  =/  hit  (find nomm.c)
  ?~  hit  ~
  `(crip (render u.hit))
?:  =(~ mugs)
  [totals (sort (turn ~(tap by code.long-ska) |=([b=bell *] `@ux`(mug b))) lth)]
=/  id-bell=(map identity bell)
  %-  ~(rep by g)
  |=  [[id=identity d=datum] acc=(map identity bell)]
  (~(put by acc) id [less-code.d fol.id])
::
%+  murn  ~(tap by code.long-ska)
|=  [b=bell *]
=/  m=@ux  (mug b)
=/  fm=@ux  (mug fol.b)
?:  =(mugs ~[0x0])  ?:(=(b func) `[m fm ~ 0 direct.totals indirect.totals] ~)
?.  (lien mugs |=(x=@ux |(=(x m) =(x fm))))  ~
=/  seats=(list [(unit spot) @ux])
  %-  ~(rep by g)
  |=  [[id=identity d=datum] acc=(list [(unit spot) @ux])]
  %-  ~(rep in callees.d)
  |=  [c=callee-entry acc=_acc]
  ?.  =(b (~(gut by id-bell) id.c *bell))  acc
  [[seat.c `@ux`(mug fol.id)] acc]
:-  ~
:*  m
    `@ux`(mug fol.b)
    (~(gut by areas) b ~)
    -.fol.b
    (lent (yea:ca cape.less.b))
    (scag 3 seats)
    (crip (scag 150 ~(ram re (sell !>(fol.b)))))
==
