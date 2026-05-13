/+  skan
/+  line-dor=line
::
=/  ka-dor  ka:skan
=*  sock  sock:skan
=*  shape-final  shape-final:line-dor
=*  ring  ring:line-dor
=.  jet-args.lon.line-dor
  =/  unary=shape-final  [| & |]
  =/  binary=shape-final  [| [& &] |]
  ^-  (map ring shape-final)
  %-  malt
  ^-  (list [ring shape-final])
  :~
    [/dec/one/k135^2 unary]
    [/add/one/k135^2 binary]
  ==
|%
++  add-jet-registerization
  |=  l=*
  ^+  ..add-jet-registerization
  %_    ..add-jet-registerization
      jet-args.lon.line-dor
    (~(gas by jet-args.lon.line-dor) ;;((list [ring shape-final]) l))
  ==
::
++  vere-straighten
  |=  [b=bell:skan entry=?]
  ^-  [(list vere-op:line-dor) @]
  =/  =straight:line-dor  (~(got by code.lon.line-dor) b)
  :_  (get-max-register:line-dor blocks.straight)
  (straighten:line-dor blocks.straight entry)
::
++  compile
  |=  [s=* f=*]
  ^-  [sock _..compile]
  =.  ka-dor  (rout:ka-dor s f)
  =.  boil.lon.line-dor  (cook:skan lon.ka-dor)
  =/  =sock  (need:..zuse (find fols.boil.lon.line-dor s f))
  =/  bell  [sock f]
  =.  arity.lon.line-dor
    =/  code  code.boil.lon.line-dor
    =/  nomm  (~(got by code) bell)
    ((find-args:skan code) bell nomm ~)
  ::
  =.  line-dor  (compile:line-dor bell)
  [sock ..compile]
::
:: ++  ska
::   |=  [s=* f=*]
::   ^+  ..ska
::   =.  ka-dor  (rout:ka-dor s f)
::   =.  boil.lon.line-dor  (cook:skan lon.ka-dor)
::   ..ska
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