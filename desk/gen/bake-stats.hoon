::  Baking statistics on the ride graph: the analysis (boot poke, ride
::  poke), the variants made, then every function compiled: argument
::  registers per function, the functions with the most, totals.
::
/+  *nock-compilation
/+  hoot
/+  hoot-fol
::
:-  %say  |=  *
:-  %noun
=|  =long-ska
=.  long-ska
  ~>  %bout.[0 leaf+"boot poke"]
  +:(ska-poke [&+~ hoot-fol] long-ska)
=/  subject  ..ride:hoot
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
=^  [root=bell *]  long-ska
  ~>  %bout.[0 leaf+"ride poke"]
  (ska-poke [&+subject formula] long-ska)
::  the variants: code bells, variants, variants with data baked
::
=/  n-code  ~(wyt by vars.long-ska)
=/  n-bells  ~(wyt by code.long-ska)
=/  n-baked
  %-  ~(rep by vars.long-ska)
  |=  [[c=bell vs=(set bell)] n=@ud]
  (add n (lent (skim ~(tap in vs) |=(v=bell !=(less.v less.c)))))
::  compile every function, with the jets of the arithmetic arms
::
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
=/  bells=(list bell)  ~(tap in ~(key by code.long-ska))
=/  [straights=(map bell straight) cache=comp-cache]
  ~>  %bout.[0 leaf+"compile all"]
  %+  roll  bells
  |=  [b=bell straights=(map bell straight) cache=comp-cache]
  ?:  (~(has by straights) b)  [straights cache]
  =^  scc=(set bell)  sccs.cache  (scc-of b calls.long-ska sccs.cache)
  =^  m=(map bell straight)  cache
    (compile-scc scc [code jets calls]:long-ska jets-hot cache)
  [(~(uni by straights) m) cache]
::  per function: arguments, ops, literal ops, blocks, after optimization
::
=/  rows=(list [args=@ud ops=@ud imms=@ud blocks=@ud b=bell])
  %+  turn  ~(tap by straights)
  |=  [b=bell s=straight]
  =/  o  (optimize s)
  =/  [ops=@ud imms=@ud]
    %-  ~(rep by blocks.o)
    |=  [[* blob=blob] ops=@ud imms=@ud]
    :-  (add ops (lent body.blob))
    (add imms (lent (skim body.blob |=(p=pole ?=(%imm -.p)))))
  [n-args.o ops imms ~(wyt by blocks.o) b]
=/  tot
  %+  roll  rows
  |=  $:  [args=@ud ops=@ud imms=@ud blocks=@ud *]
          acc=[args=@ud ops=@ud imms=@ud blocks=@ud]
      ==
  [(add args args.acc) (add ops ops.acc) (add imms imms.acc) (add blocks blocks.acc)]
=/  top
  %+  scag  15
  %+  sort  rows
  |=([a=[args=@ud *] b=[args=@ud *]] (gth args.a args.b))
=/  hist=(map @ud @ud)
  %+  roll  rows
  |=  [[args=@ud *] acc=(map @ud @ud)]
  (~(put by acc) args +((~(gut by acc) args 0)))
:*  %bake-stats
    code-bells+n-code
    bells+n-bells
    baked+n-baked
    functions+(lent rows)
    totals+tot
    :-  %top
    %+  turn  top
    |=  [args=@ud ops=@ud imms=@ud blocks=@ud b=bell]
    [args ops imms blocks `@ux`(mug fol.b) `@ux`(mug b)]
    hist+(sort ~(tap by hist) |=([a=[@ud @ud] b=[@ud @ud]] (lth -.a -.b)))
==
