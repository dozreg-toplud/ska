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
=/  g
  ~>  %bout.[0 'trap poke']
  (ska-graph [&+~ fol] *long-ska)
:-  %noun
:-  functions+~(wyt by g)
%+  turn  ~(tap by g)
|=  [id=identity d=datum]
?>  &(?=(^ more.id) ?=(^ prod.d))
[`@ux`(mug fol.id) more=cape.more.id prod=cape.prod.d]
