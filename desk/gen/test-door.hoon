::  A gate returning its own core after recursion: how known is the product?
::
/+  *nock-compilation
:-  %say  |=  *
=/  sub
  =+  c=0
  |%
  ++  this  .
  ++  add
    |=  n=@
    ^+  this
    ?~  n  this
    $(c +(c), n (dec n))
  ::
  ++  foo
    =>  (add 42)
    this(c +(c))
  --
=/  fol=^  ;;(^ =>(sub !=(foo)))
=/  lon  +:(ska-poke [&+sub fol] *long-ska)
=/  g  graph.final.lon
=/  root  (~(got by g) [&+sub fol])
=/  count-2
  |=  =nomm
  ^-  [direct=@ indirect=@]
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
:-  %noun
:*  functions+~(wyt by g)
    root-prod-cape+cape.prod.root
    :-  %prods
    %+  turn  ~(tap by g)
    |=  [id=identity d=datum]
    [`@ux`(mug fol.id) more=cape.more.id prod=cape.prod.d (count-2 nomm.d)]
==
