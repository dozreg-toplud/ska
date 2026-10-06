::  Does a ~+ entry saved inside another ~+ computation survive?
::
:-  %say  |=  *
:-  %noun
=/  f  |=(a=@ ~+(~&([%f-miss a] (mul a 2))))
=/  g  |=(a=@ ~+(~&([%g-miss a] (add a (f 1)))))
=/  j  |=(a=@ ~+((mul a 3)))
~&  %step-1-g0
=/  a  (g 0)
~&  %step-2-f1-expect-no-miss
=/  b  (f 1)
~&  %step-3-g0-expect-no-miss
=/  c  (g 0)
~&  %step-4-f2-direct
=/  d  (f 2)
~&  %step-5-f2-again-expect-no-miss
=/  e  (f 2)
~&  %step-6-junk-100k-silent
=/  junk  (roll (gulf 1 100.000) |=([i=@ acc=@] (add acc (j i))))
~&  %step-7-f1-f2-g0-after-junk
=/  h  [(f 1) (f 2) (g 0)]
~&  %step-8-done
[a b c d e h junk]
