=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%smallest [1 5 7 8] [7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [1 1] [0 0] [0 3]]]]
      [%smallest-b [1 5 9] [7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [1 1] [0 0] [0 3]]]]
      [%not-const [1 1 8] [7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [3 [0 1]] [0 2] [1 9]]]]
      [%other-axes [1 1 8] [7 [6 [0 2] [0 1] [6 [0 6] [3 [0 7]] [0 1]]] [6 [3 [0 1]] [0 3] [1 9]]]]
      [%control [0 5 7 8] [7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [1 1] [0 0] [0 3]]]]
  ==
|-  ^-  @
?~  cases  0
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=/  r  (mule |.((eval-top [sub fol]:i.cases ~)))
~&  :*  nam.i.cases
        mock=a
        ^=  ska
        ?:  ?=(%| -.r)  %interpreter-crashed
        =/  t=tone  -.p.r
        ?:(?=(%0 -.t) [%0 product.t] ?:(?=(%1 -.t) %1 [%2 (lent trace.t)]))
    ==
$(cases t.cases)
