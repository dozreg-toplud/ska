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
=/  g
  ~>  %bout.[0 'walk poke']
  (ska-graph [&+sub fol] *long-ska)
=/  root  (~(got by g) [&+sub fol])
:-  %noun
[n=n functions+~(wyt by g) root-prod+?@(prod.root %void cape.prod.root)]
