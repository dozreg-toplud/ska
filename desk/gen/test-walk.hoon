::  A gate that rebuilds its (known) argument cell by cell: how many passes
::  does the product take to converge, depending on the depth of the argument?
::
/+  *nock-compilation
:-  %say  |=  [* [n=@ ~] ~]
=/  sub
  =+  l=(reap n 7)
  |%
  ++  walk
    |=  t=*
    ^-  *
    ?@  t  t
    [$(t -.t) $(t +.t)]
  ::
  ++  foo  (walk l)
  --
=/  fol=^  ;;(^ =>(sub !=(foo)))
=/  lon
  ~>  %bout.[0 'walk poke']
  +:(ska-poke [&+sub fol] *long-ska)
=/  g  graph.final.lon
=/  root  (~(got by g) [&+sub fol])
:-  %noun
[n=n functions+~(wyt by g) root-prod+?@(prod.root %void cape.prod.root)]
