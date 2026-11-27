::  %10 at axis 0 (track P, README Gaps 23, ninth session): +fol-loop turns
::  [10 [0 d] r] into the nomm [%0 0] (its case `?:  =(0 a.fol)`), so no
::  nomm of code.lon has a %10 at axis 0 and +eval-finalized never reaches
::  the assert of +have.  Four %full pokes in a row (axis 0 at the top, in
::  the untaken and the taken branch of a %6, and with a constant), then the
::  nomm and the flags of every entry of code.
::
=/  fols=(list *)
  :~  [10 [0 [0 1]] [0 1]]
      [6 [1 0] [0 1] [10 [0 [0 1]] [0 1]]]
      [6 [1 1] [0 1] [10 [0 [0 1]] [0 1]]]
      [10 [1 [0 1]] [0 1]]
  ==
|-
?~  fols  0
=^  p  ..poke  (poke [%full 0 i.fols])
=/  ent=(list [bell code-entry])  ~(tap by code.long-ska.state)
~&  [%poke i.fols %returned ?=(^ p) %entries (lent ent)]
~&  (turn ent |=([b=bell e=code-entry] [fol.b nomm.e pure.e total.e]))
$(fols t.fols)
