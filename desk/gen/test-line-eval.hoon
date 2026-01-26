/-  *gene
/+  line-dor=line
/+  skan
::
:-  %say  |=  *  :-  %noun
::
|^
=/  ka-dor  ka:line-dor
=/  sub  41
=/  fol  [4 0 1]
=.  ka-dor  (rout:ka-dor sub fol)
=/  =boil  (cook:skan lon.ka-dor)
=/  all-args  (find-args-all:skan code.boil)
=/  =bell  (need:..zuse (find fols.boil sub fol))
=|  =line-long
=.  boil.line-long  boil
=.  arity.line-long  all-args
=.  line-dor  ~(. line-dor line-long)
=.  line-dor  (~(compile line-dor line-long) bell)
=/  entry=@uxor  (~(got by bells.lon.line-dor) bell)
(eval:line-dor sub entry)
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
--