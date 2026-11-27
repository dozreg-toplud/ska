::  Can a poke plant an untidy sock (data under a |, a cell cape over an atom,
::  a cape [| |]) where the analysis reads it?  (lemmas/Ska/PassMeasureT.lean)
::  %fast: the template is clammed with its junk, +register-template
::  normalizes it before it is kept; a cell cape over an atom crashes the poke.
::  %dire: an untidy bell that is not in the code crashes the poke.
::  Then a %full poke on a formula that runs the registered battery returns.
=/  tidy
  |=  s=sock
  ^-  ?
  ?@  s  &
  =/  c=cape  cape.s
  =/  d=*  data.s
  |-  ^-  ?
  ?:  ?=(%| c)  =(0 d)
  ?:  ?=(%& c)  &
  ?:  &(?=(%| -.c) ?=(%| +.c))  |
  ?@  d  |
  &($(c -.c, d -.d) $(c +.c, d +.d))
=/  bat=*  [[0 6] [4 0 6]]
=/  junk=sock  [[& |] [bat 7]]
=/  pair=sock  [[& [| |]] [bat [7 8]]]
=/  r1  (mule |.((poke [%fast | ~[[/foo/bar junk]]])))
~&  [%fast-junk-returned ?=(%& -.r1)]
=?  ..poke  ?=(%& -.r1)  +.p.r1
=/  r2  (mule |.((poke [%fast | ~[[/foo/baz pair]]])))
~&  [%fast-pair-returned ?=(%& -.r2)]
=?  ..poke  ?=(%& -.r2)  +.p.r2
=/  r3  (mule |.((poke [%fast | ~[[/foo/qux [[& |] 5]]]])))
~&  [%fast-atom-returned ?=(%& -.r3)]
=/  tems=(list [path sock])
  %-  zing
  %+  turn  ~(tap by core.jets.long-ska.state)
  |=  [p=path s=(set sock)]
  (turn ~(tap in s) |=(u=sock [p u]))
~&  [%templates tems]
~&  [%templates-tidy (levy tems |=([q=path u=sock] (tidy u)))]
=/  r4  (mule |.((poke [%dire [junk [0 1]] &])))
~&  [%dire-returned ?=(%& -.r4)]
~&  %full-start
=^  p  ..poke  (poke [%full [bat 5] [9 2 0 1]])
~&  [%full-returned ?=(^ p)]
=/  mem=(list sock)
  %-  zing
  %+  turn  ~(tap by memo.long-ska.state)
  |=  [* m=(map sock [id=[more=sock fol=^] *])]
  (turn ~(tap by m) |=([l=sock [id=[more=sock fol=^] *]] more.id))
~&  [%memo-subjects-tidy (lent mem) (levy mem tidy)]
0
