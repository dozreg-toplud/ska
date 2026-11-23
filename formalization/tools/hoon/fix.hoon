=/  lib  .
=/  spot  [11 [%spot 1 0] 0 0]
=/  raw=(list [nam=@tas sub=* fol=*])
  :~  [%cell-tag 0 [11 [[1 0] 1 0] 1 42]]
      [%inline-drop 42 [2 [0 1] 7 [0 0] 1 0 1]]
      [%inline-ok 42 [2 [0 1] 7 [0 1] 1 0 1]]
      [%five 0 [5 spot 0]]
      [%two 0 [2 spot 0]]
      [%seven 0 [7 spot 0]]
      [%six-skip 0 [6 [1 1] 0 [1 42]]]
      [%six-take 0 [6 [1 0] 0 [1 42]]]
      [%six-after 0 [6 spot 0 0]]
      [%ten 0 [10 [2 0] [1 1 2]]]
      [%eleven 0 [11 [%spot 1 0] 0]]
      [%twelve 0 [12 [1 0] 0]]
      [%cons 0 [[1 1] 0]]
      [%eight 0 [8 [1 1] 0]]
      [%bare 0 [11 %bare 1 42]]
      [%bare-crash 0 [11 %bare 11 [%spot 1 0] 0 0]]
      [%bare-in 7 [7 [0 1] 11 %bare 4 0 1]]
  ==
=/  hoon=(list [nam=@tas sub=* fol=*])
  %+  turn
    ^-  (list [@tas *])
    =>  lib
    :~  [%add !=((add 2 3))]
        [%dec !=((dec 0))]
        [%roll !=((roll (gulf 1 6) add))]
        [%mean !:(!=(~|([%a (add 1 2)] (dec 0))))]
        [%sort !=((sort ~[3 1 2] lth))]
    ==
  |=([n=@tas f=*] [n lib f])
=/  cases  (weld raw hoon)
=/  bad=@ud  0
|-  ^-  @
?~  cases  ~&([%done %bad bad] bad)
=/  a=toon  (mook (mink [sub fol]:i.cases ~))
=^  ton=tone  ..^poke  (eval-top [sub fol]:i.cases ~)
=^  b=toon  ..^poke  (eval-mook ton)
~&  ?:  =(a b)  [nam.i.cases %same ?:(?=(%2 -.a) [%2 (lent p.a)] ?:(?=(%0 -.a) ?@(p.a a %0) a))]
    [nam.i.cases %differ mock=a ska=b]
$(cases t.cases, bad ?:(=(a b) bad +(bad)))
