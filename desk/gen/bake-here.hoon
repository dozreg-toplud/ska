::  The arguments of one function and its component, with and without
::  baking: the code bell with the given mug (a bell as the analysis makes
::  it: [less-code formula]), its variants, and for each the argument
::  registers of its compiled form, by axis, with whether the bell knows
::  the noun there (none should be known after baking).
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  [* [target=@ud ~] ~]
:-  %noun
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..ride:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::  the identity graph of the ride poke, with whole subjects: the memo keeps
::  only what +git:mi reads of them
::
=/  g=callgraph  (ska-graph [&+subject formula] long-ska)
=^  [root=bell *]  long-ska
  ~>  %bout.[0 leaf+"ride poke"]
  (ska-poke [&+subject formula] long-ska)
::  the code bells of +here's inner gate: its formula is one for every
::  instance of the wet gate, so the bells differ by their code (hez, sef)
::
=/  fol-here=*
  =>  ..ride:hoot-zpdt
  -:(here |=([a=pint b=*] [a b]) |=(tub=nail *edge))
=/  codes=(list bell)
  %+  skim  ~(tap in ~(key by vars.long-ska))
  |=(c=bell =(fol.c fol-here))
?~  codes  [%no-here-bells `@ux`(mug fol-here) ~(wyt by vars.long-ska)]
=/  variants=(list bell)
  %-  zing
  %+  turn  codes
  |=(c=bell ~(tap in (~(get ju vars.long-ska) c)))
=/  jets-hot=jets-comp
  %-  malt
  ^-  (list [ring jets-comp-info])
  =/  unary=need-ordered  [none+~ this+~ none+~]
  =/  binary=need-ordered  [none+~ [this+~ this+~] none+~]
  :~  [/add/one/k135^2 binary]
      [/dec/one/k135^2 unary]
      [/div/one/k135^2 binary]
      [/dvr/one/k135^2 binary]
      [/gte/one/k135^2 binary]
      [/gth/one/k135^2 binary]
      [/lte/one/k135^2 binary]
      [/lth/one/k135^2 binary]
      [/max/one/k135^2 binary]
      [/min/one/k135^2 binary]
      [/mod/one/k135^2 binary]
      [/mul/one/k135^2 binary]
      [/sub/one/k135^2 binary]
      [/bex/two/one/k135^2 unary]
  ==
::  the leaves of a shape: axis, whether the whole is also taken, whether
::  the bell knows the noun there, and what the analysis knew there (the
::  subject of an identity of the bell in the ride analysis, +ska-graph):
::  an atom, a cell by mug, or ~ for unknown
::
=/  what
  |=  [more=sock axe=@]
  ^-  *
  =/  k=sock  (pull:so more axe)
  ?.  ?=(^ k)  ~
  ?.  (all:ca cape.k)  ?:(?=(%| cape.k) ~ [%part (mug data.k)])
  ?@  data.k  [%atom data.k]
  [%cell (mug data.k)]
=/  leaves
  |=  [ned=need-ordered less=sock more=sock]
  ^-  (list [axe=@ kind=?(%this %both) known=? what=*])
  =/  axe=@  1
  |-  ^-  (list [axe=@ kind=?(%this %both) known=? what=*])
  =/  k=sock  (pull:so less axe)
  =/  known=?  &(?=(^ k) (all:ca cape.k))
  ?-  -.ned
    %none  ~
    %this  [axe %this known (what more axe)]~
    ^      (weld $(ned p.ned, axe (peg axe 2)) $(ned q.ned, axe (peg axe 3)))
  ::
      %both
    :-  [axe %both known (what more axe)]
    (weld $(ned h.ned, axe (peg axe 2)) $(ned t.ned, axe (peg axe 3)))
  ==
::  compile the component of each variant
::
=/  cache=comp-cache  *comp-cache
=/  rows=(list *)
  =|  rows=(list *)
  |-  ^+  rows
  ?~  variants  rows
  =/  v=bell  i.variants
  =^  scc=(set bell)  sccs.cache  (scc-of v calls.long-ska sccs.cache)
  =^  m=(map bell straight)  cache
    ~>  %bout.[0 leaf+"compile the component"]
    (compile-scc scc [code jets calls]:long-ska jets-hot cache)
  =/  s=straight  (optimize (~(got by m) v))
  ::  the analysis identity of the code bell, for what the callers knew
  ::
  =/  more=sock
    =/  c=bell
      =/  cs  (skim `(list bell)`codes |=(c=bell (~(has in (~(get ju vars.long-ska) c)) v)))
      ?~(cs v i.cs)
    =/  ids=(list identity)
      %+  murn  ~(tap by g)
      |=  [id=identity d=datum]
      ?.(=(c [less-code.d fol.id]) ~ `id)
    ?~(ids |+~ more.i.ids)
  =/  lv  (leaves need.s less.v more)
  =/  scc-args=@ud
    (roll ~(tap by m) |=([[b=bell st=straight] n=@ud] (add n n-args.st)))
  =/  row
    :*  bell+`@ux`(mug v)
        fol+`@ux`(mug fol.v)
        args+n-args.s
        known+(lent (skim lv |=([* * k=? *] k)))
        scc+~(wyt in scc)
        scc-args+scc-args
        compiled+~(wyt by m)
        leaves+lv
    ==
  $(variants t.variants, rows [row rows])
:*  %bake-here
    fol+`@ux`(mug fol-here)
    codes+(turn codes |=(c=bell `@ux`(mug c)))
    variants+(lent variants)
    rows
==
