/+  skan
/+  line
/+  play-fol
/+  playpen
::
:-  %say  |=  *  :-  %noun
::
=/  cor  ka:skan
=/  sub  .*(0 q.play-fol)
=/  fol  +:(~(mint ut p.play-fol) %noun (ream '(add 2 3)'))
::
~&  %poke-playpen
=.  cor  (rout:cor 0 play-fol)
~&  %poke-sub-fol
=.  cor  (rout:cor sub fol)
~&  %compile
=/  rope  (compile-all:line lon.cor)
~&  %exec
(exec:line sub fol rope)