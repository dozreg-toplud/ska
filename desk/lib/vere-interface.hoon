/+  skan
/+  line-dor=line
::
=/  ka-dor  ka:skan
=*  sock  sock:skan
|%
++  vere-straighten
  |=  b=bell:skan
  ^-  [@ud (list vere-op:line-dor)]
  =/  =straight:line-dor  (~(got by code.lon.line-dor) b)
  :-  n-args.straight
  (straighten:line-dor blocks.straight)
::
++  compile
  |=  [s=* f=*]
  ^-  [sock _..compile]
  =.  ka-dor  (rout:ka-dor s f)
  =.  boil.lon.line-dor  (cook:skan lon.ka-dor)
  =/  =sock  (need:..zuse (find fols.boil.lon.line-dor s f))
  =.  arity.lon.line-dor  (find-args-all:skan code.boil.lon.line-dor)
  =.  line-dor  (compile-all:line-dor code.boil.lon.line-dor)
  [sock ..compile]
::
++  find
  |=  [fols=(jar * [less=sock code=nomm-1:skan]) sub=* fol=*]
  ^-  (unit sock)
  =/  l=(list [s=sock *])  (~(get ja fols) fol)
  %+  roll  l
  |=  [[s=sock *] max=(unit sock)]
  ?:  ?|  !(~(huge so:skan s) &+sub)
          ?&  ?=(^ max)
              (~(huge so:skan s) u.max)
      ==  ==
    max
  `s
--