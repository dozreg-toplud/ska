/+  skan
/+  line
::
:-  %say  |=  *  :-  %noun
::
=/  sub
  !.  =>  ~
  |.
  =/  once  |=(@ +(+<))
  =/  dabl  =>  +  |=(@ +(+(+<)))
  =/  slam  |=(g=$-(@ @) |=(n=@ (g n)))
  [((slam once) 1) ((slam dabl) 1)]
::
=/  fol
  [9 2 0 1]
::
=/  cor  ka:skan
=.  cor  (rout:cor sub fol)
=/  rope  (compile-all:line lon.cor)
(exec:line sub fol rope)