/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
::  BELL <mug of bell> <mug of its formula with %spot/%mean hints stripped>
::
:-  %say  |=  *
:-  %noun
=/  res
  %-  ~(mule vi |)
  |.
  ~>  %jinx.~m5
  =|  =long-ska
  =.   long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
  =/  subject  ..scow:hoot-zpdt
  =/  formula=^
    =>  subject
    ;;  ^
    !=
    (scow %ud 5)
  ::
  =^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
  =/  subject  ..ride:hoot-zpdt
  =/  formula=^
    =>  subject
    ;;  ^
    !=
    (ride %noun '42')
  ::
  =^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
  =/  strip
    |=  f=*
    ^-  *
    =*  strip  .
    ?@  f  f
    ~+
    ?:  ?&  =(11 -.f)
            ?=([[?(%spot %mean) *] *] +.f)
        ==
      (strip +>.f)
    [(strip -.f) (strip +.f)]
  ::
  =/  rows=(list tape)
    %+  turn  ~(tap by graph.final.long-ska)
    |=  [id=identity d=datum]
    =/  b=bell  [less-code.d fol.id]
    :(weld "BELL " (scow %ud (mug b)) " " (scow %ud (mug (strip fol.id))))
  ::
  %-  (slog (turn rows |=(t=tape leaf+t)))
  [%bells (lent rows)]
?:  ?=(%& -.res)  p.res
(mean p.res)
