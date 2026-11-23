=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%smallest [1 5 7 8] [7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [1 1] [0 0] [0 3]]]]
      [%not-const [1 1 8] [7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [3 [0 1]] [0 2] [1 9]]]]
      [%other-axes [1 1 8] [7 [6 [0 2] [0 1] [6 [0 6] [3 [0 7]] [0 1]]] [6 [3 [0 1]] [0 3] [1 9]]]]
      [%three [1 5 7 8] [7 [6 [1 1] [0 14] [6 [1 1] [6 [0 2] [1 0] [0 2]] [0 6]]] [6 [0 2] [0 14] [0 12]]]]
  ==
|-  ^-  @
?~  cases  0
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=^  p  ..poke  (poke [%full sub fol]:i.cases)
?>  ?=([%ir *] p)
::  the code of +comp before +optimize, as +compiled-mono cached it
=/  raw  (~(got by mono.cache.state) b.p)
=/  r
  %-  mule  |.
  -:(eval-blob [[[`@`0 `sub.i.cases] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ ~)
=/  blk  ~(wyt by blocks.raw)
~&  :*  nam.i.cases
        mock=a
        ^=  unoptimized
        ?:  ?=(%| -.r)  %interpreter-crashed
        =/  t=tone  p.r
        ?:(?=(%0 -.t) [%0 product.t] ?:(?=(%1 -.t) %1 [%2 (lent trace.t)]))
        blocks=[raw=blk optimized=~(wyt by blocks.p.p)]
    ==
$(cases t.cases)
