:: medesoft.hoon (track I, 2026-11-28): +mede asks +soft-ask through +crash-need at a soft block.
:: Run on the library of sccreal.py (it dumps the soft map after the %done run as [%ds mug-scc mug-b ~(tap by soft.gen)]):
::   python3 tools/hoon/sccreal.py OUT --shape-lib
::   RUNHOON_LIB=OUT/lib.hoon tools/hoon/runhoon.sh tools/hoon/medesoft.hoon 600
:: In every case the soft tail call passes the constant 5 (or [5 x]) where the callee, entered with that part
:: unknown (the loop heuristic +close drops the constant from its sock), splits it on every path but not first
:: thing; the first %done run then records req [2 [[%this 1] %none 0]]: a cell need, a try (the model medeL asks nothing).

=/  cases=(list [nam=@tas gat=*])
  :~  :-  %w14  =>  ~  |=(s=[i=@ j=* k=*] |-(?:(.=(i.s 9) -.j.s $(i.s .+(i.s), j.s 5, k.s -.j.s))))
      :-  %w15  =>  ~  |=(s=[i=@ j=* k=*] |-(?:(.=(i.s 9) -.j.s $(i.s .+(i.s), j.s ~>(%xx 5), k.s -.j.s))))
      :-  %w17  =>  ~  =<  b
        |%  ++  a  |=([n=@ x=*] ?:(.=(n 9) 0 (b n 5)))
            ++  b  |=([m=@ y=*] ?:(.=(m 0) -.y (a .+(m) +.y)))
        --
      :-  %w18  =>  ~  =<  b
        |%  ++  a  |=([n=@ x=*] ?:(.=(n 9) 0 (b n [5 x])))
            ++  b  |=([m=@ y=*] ?:(.=(m 0) -.-.y (a .+(m) +.-.y)))
        --
      :-  %w19  =>  ~  |=(s=[i=@ j=* k=*] |-(?:(.=(i.s 9) [-.j.s +.j.s] $(i.s .+(i.s), j.s 5, k.s [+.j.s -.j.s]))))
  ==
|-  ^-  @
?~  cases  0
~&  ^-(* [%case nam.i.cases])
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=.  sure.cache.state  ~
=.  inl.cache.state  ~
=/  fol=*  [8 [1 gat.i.cases] [9 2 [10 [6 [0 7]] [0 2]]]]
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol) fol)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
$(cases t.cases)
