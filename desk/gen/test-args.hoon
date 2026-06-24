/+  *nock-compilation1
/+  hoot, hoot-zpdt, hoot-fol, hoot-zpdt-fol
::
|%
++  print-long-args
  |=  [=long-args =long-ska]
  ^-  (list tape)
  %+  turn  ~(tap by code.long-args)
  |=  [k=bell v=cape]
  "bell {<`@ux`(mug k)>}: {<v>}"
--
::
:-  %say  |=  *
::
=/  sub  hoot-zpdt
=/  fol
  ;;  ^  =>  sub  !.  !=
  (dec 42)
::
~&  fol
=/  =long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] *long-ska)
=^  root=bell  long-ska  (ska-poke [&+sub fol] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
=/  =long-args
  =/  unary   [| & |]
  =/  binary  [| [& &] |]
  :_  ~
  ^-  (map ring cape)
  %-  malt
  ^-  (list [ring cape])
  :~
    [/add/one/k135^2 binary]
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
  ==
::
=.  long-args  (axis-poke root long-ska long-args)
:-  %tang  %-  flop
%-  turn  :_  (lead %leaf)
(print-long-args long-args long-ska)