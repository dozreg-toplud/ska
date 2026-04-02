/-  *gene
/+  line-dor=line
/+  skan
/+  hoot-zpdt
/+  hoot
::
:-  %say  |=  *  :-  %noun
::
|^
=/  sub
  =>  ..dec:hoot-zpdt
  |=  [m=@ n=@]
  ^-  @
  ?:  =(0 m)  +(n)
  ?:  =(0 n)  $(m (dec m), n 1)
  $(m (dec m), n $(n (dec n)))
::
=/  fol
  !.
  =>  sub  !=
  (. 1 0)
::
::  do SKA, find result
::
=/  ka-dor  ka:line-dor
=.  ka-dor  (rout:ka-dor sub fol)
=/  =boil  (cook:skan lon.ka-dor)
=.  boil  (boil-transform-nomm:skan boil fold-hints:skan)
=/  =bell  (need:..zuse (find fols.boil sub fol))
::  prep line-long state, find arities
::
=|  =line-long
=.  boil.line-long  boil
=.  arity.line-long  (find-args-all:skan code.boil)
::  linearize, compile to C
::
=.  line-dor  (~(compile-all line-dor line-long) code.boil)
(crip (snoc `tape`(zing (join "\0a" back:line-dor)) '\0a'))
:: %-  ~(rep by arity.line-long)
:: |=  [[k=^bell v=meme-args] acc=~]
:: ~&  [(mux k) shape-final.v fol.k]
:: ~
::
::  XX no sock maximization logic
::
++  find
  |=  [fols=(jar * [less=sock code=nomm-1]) sub=* fol=*]
  ^-  (unit bell)
  =-  ?~  -  ~  `[u fol]
  ^-  (unit sock)
  =/  l=(list [s=sock *])  (~(get ja fols) fol)
  |-  ^-  (unit sock)
  ?~  l  ~
  ?:  (~(huge so s.i.l) &+sub)  `s.i.l
  $(l t.l)
::
++  mux
  |=  n=*
  ^-  @ux
  (mug n)
--