::  Bells of the ride poke. With no argument: the sorted list of bell mugs.
::  With a list of mugs: [mug area formula-head less-code-known-axes] of the
::  bells with those mugs, for diffing analysis variants.
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  [* args=* ~]
=/  mugs=(list @ux)  ?~(args ~ ;;((list @ux) -:;;(^ args)))
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..ride:hoot-zpdt
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
:-  %noun
::  ~[0x3 formula-mug]: the indirect call sites of that formula's bells, as
::  a prefix of the subject expression of each
::
?:  ?=([%0x3 @ ~] mugs)
  =/  sites
    |=  =nomm
    |-  ^-  (list tape)
    ?-  nomm
      [^ *]    (weld $(nomm -.nomm) $(nomm +.nomm))
      [%0 *]   ~
      [%1 *]   ~
      [%2 *]   %+  weld  ?~(info.nomm [(scag 110 ~(ram re (sell !>(p.nomm)))) ~] ~)
               (weld $(nomm p.nomm) $(nomm q.nomm))
      [%3 *]   $(nomm p.nomm)
      [%4 *]   $(nomm p.nomm)
      [%5 *]   (weld $(nomm p.nomm) $(nomm q.nomm))
      [%6 *]   :(weld $(nomm p.nomm) $(nomm q.nomm) $(nomm r.nomm))
      [%7 *]   ?:  ?&  ?=([%2 [%0 %1] * ~] q.nomm)
                   ==
                 :-  (scag 110 ~(ram re (sell !>([core=p.nomm arm=q.q.nomm]))))
                 $(nomm p.nomm)
               (weld $(nomm p.nomm) $(nomm q.nomm))
      [%10 *]  (weld $(nomm q.p.nomm) $(nomm q.nomm))
      [%11 *]  ?@(p.nomm $(nomm q.nomm) (weld $(nomm q.p.nomm) $(nomm q.nomm)))
      [%12 *]  (weld $(nomm p.nomm) $(nomm q.nomm))
    ==
  %+  murn  ~(tap by code.long-ska)
  |=  [b=bell c=code-entry]
  ?.  =((mug fol.b) i.t.mugs)  ~
  `[`@ux`(mug b) (lent (yea:ca cape.less.b)) (turn (sites nomm.c) crip)]
?:  =(mugs ~[0x1])
  %+  murn  ~(tap by code.long-ska)
  |=  [b=bell c=code-entry]
  =/  sites  (indirect-sites nomm.c)
  ?~  sites  ~
  `[`@ux`(mug b) `@ux`(mug fol.b) (~(gut by areas) b ~) (lent sites) sites]
::  ~[0x2 lo hi]: bells whose area starts on a hoot-zpdt line in [lo hi]
::
?:  ?=([%0x2 @ @ ~] mugs)
  %+  murn  ~(tap by code.long-ska)
  |=  [b=bell c=code-entry]
  =/  area  (~(gut by areas) b ~)
  ?~  area  ~
  =/  line  p.p.q.u.area
  ?.  &((gte line i.t.mugs) (lte line i.t.t.mugs))  ~
  =/  n  (count-2 nomm.c)
  `[`@ux`(mug b) line+line direct+direct.n indirect+indirect.n (lent (yea:ca cape.less.b))]
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
