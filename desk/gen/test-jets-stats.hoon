::  Sizes of the %fast registration state and the bell <--> ring mapping after
::  the boot poke and the ride poke.
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
=/  stats
  |=  lon=long-ska
  =/  sizes=(list @)
    (turn ~(tap by core.jets.lon) |=([* s=(set sock)] ~(wyt in s)))
  :*  paths+~(wyt by core.jets.lon)
      templates+(roll sizes add)
      max-templates+(roll sizes max)
      roots+~(wyt by root.jets.lon)
      batts+~(wyt by batt.jets.lon)
      arms+~(wyt by arms.jets.lon)
      rings+~(wyt by call.cole.jets.lon)
      jets+`@ux`(mug [root core batt cole]:jets.lon)
      bells+~(wyt by code.lon)
  ==
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  boot  (stats long-ska)
=/  subject  ..ride:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::
=^  func=bell  long-ska
  ~>  %bout.[0 'poke ride']
  (ska-poke [&+subject formula] long-ska)
:-  %noun
[boot+boot ride+(stats long-ska)]
