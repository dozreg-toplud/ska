::  A recursive gate that is entered with an unknown gate argument and
::  recurses with a known one. The first call can only call its argument
::  indirectly. The recursion knows the gate, so it does not merge into the
::  first call (+recursive-call) and gets its own function with a direct
::  call; its product is known, so the first call can call it directly too.
::  Expect two functions for f, with one and with no indirect calls: with
::  the merge there was a single one with two.
::  Produces [formula-mug is-f direct indirect] for each function.
::
/+  *nock-compilation
:-  %say  |=  *
=/  sub
  |%
  ++  mk  |=(a=@ |=(b=@ +(b)))
  ++  mu  |=(a=@ |=(b=@ b))
  ++  f
    |=  [g=$-(@ $-(@ @)) n=@]
    ^-  $-(@ @)
    ?:  =(n 0)  (g n)
    =/  h  $(g mk, n (dec n))
    (mk (h 1))
  ::
  ++  foo  (f ?:(=(0 (dec 1)) mk mu) 3)
  --
=/  fol=^  ;;(^ =>(sub !=(foo)))
=/  f-bat=*  -:f:sub
=/  lon  +:(ska-poke [&+sub fol] *long-ska)
=/  g  graph.final.lon
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
:-  functions+~(wyt by g)
%+  turn  ~(tap by g)
|=  [id=identity d=datum]
[`@ux`(mug fol.id) f==(f-bat fol.id) (count-2 nomm.d)]
