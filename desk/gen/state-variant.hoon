::  The persistent state after the boot and ride pokes, with the kernel it
::  shares, in a variant layout, to bind to a dojo variable for |mass to
::  size in the loom:  =lon +ska!state-variant %full  then  |mass  (gall,
::  dojo).  The difference between two variants is what the loom pays for
::  what one has and the other has not.
::    %none     ~
::    %base     the kernel and formulas the state shares
::    %full     [base state]
::
/+  *nock-compilation
/+  hoot
/+  hoot-fol
::
:-  %say  |=  [* [mode=@tas ~] ~]
:-  %noun
?:  ?=(%none mode)  ~
=/  subject  ..ride:hoot
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
=/  base=*  [subject hoot-fol formula]
?:  ?=(%base mode)  base
=|  lon=long-ska
=.  lon  +:(ska-poke [&+~ hoot-fol] lon)
=.  lon  +:(ska-poke [&+subject formula] lon)
:-  base
?>  ?=(%full mode)
lon
