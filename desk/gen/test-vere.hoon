/+  v=vere-interface
/+  hoot-zpdt-fol
/+  hoot-zpdt
::
=/  memo-call
  =>  ..ride
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  !.  ~>  %memo./user
  (g v)  
::
=/  invert
  |*  m=(map)
  ?:  =(~ m)  ~
  %-  ~(gas by *(map _,.->.m _,.-<.m))
  (turn ~(tap by m) |=([a=_,.-<.m b=_,.->.m] [b a]))
::
|=  *
%-  need  %-  ~(mole vi |)  |.
:: =.  v  (memo-call ska:v ~ hoot-zpdt-fol)
=.  v  +:(memo-call compile:v ~ hoot-zpdt-fol)
=/  sub  ..dec:hoot-zpdt
=/  fol
  !.  =>  sub  !=
  (dec 41)
::
=^  sock  v  (compile:v sub fol)
=+  (vere-straighten:v [sock fol] &)
~