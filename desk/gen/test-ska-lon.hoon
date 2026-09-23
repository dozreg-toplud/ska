::  Produce the persistent SKA state after the boot poke and the ride poke,
::  for experiments in the dojo: =lon +ska!test-ska-lon
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
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
noun+long-ska
