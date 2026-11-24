=/  cases=(list [nam=@tas sub=* fol=*])
  :~  [%dead-slot 0 [7 [0 2] [1 5]]]
      [%dead-cons 0 [7 [[0 2] [0 3]] [1 5]]]
      [%dead-inc [1 2] [7 [4 [0 1]] [1 5]]]
      [%dead-deep [1 2] [7 [0 6] [1 5]]]
      [%dead-eight [1 2] [8 [4 [0 1]] [1 5]]]
      [%dead-branch 0 [6 [1 0] [7 [0 3] [1 5]] [1 6]]]
      [%dead-ten 0 [7 [10 [2 [1 1]] [0 1]] [1 5]]]
      [%dead-five-ok 0 [7 [5 [0 2] [0 3]] [1 5]]]
      [%dead-hed-of-inc 0 [7 [0 2] [7 [4 [1 1]] [1 5]]]]
  ==
|-  ^-  @
?~  cases  0
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=/  r  (mule |.((eval-top [sub fol]:i.cases ~)))
=/  k
  ?:  ?=(%| -.r)  %interpreter-crashed
  =/  t=tone  -.p.r
  ?:(?=(%0 -.t) [%0 product.t] ?:(?=(%1 -.t) %1 [%2 ~]))
=/  m  ?:(?=(%0 -.a) [%0 p.a] ?:(?=(%1 -.a) %1 [%2 ~]))
~&  [nam.i.cases ?:(=(m k) %same [%differ mock=m ska=k])]
$(cases t.cases)
