::  Growing subject chain: a trap that wraps the previous trap on every
::  iteration. The analysis must stop the chain with the homeomorphic
::  embedding check.
::
/+  *nock-compilation
:-  %say  |=  *
=/  fol=^
  ;;  ^
  =>  ~
  !=
  =/  t  |.(0)
  |-  ^-  ~
  ?:  =(3 $:t)  ~
  $(t |.(+($:t)))
=/  lon
  ~>  %bout.[0 'trap poke']
  +:(ska-poke [&+~ fol] *long-ska)
=/  g  graph.final.lon
:-  %noun
:-  functions+~(wyt by g)
%+  turn  ~(tap by g)
|=  [id=identity d=datum]
[`@ux`(mug fol.id) more=cape.more.id prod=cape.prod.d]
