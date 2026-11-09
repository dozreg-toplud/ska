/+  *nock-compilation
/+  li=line-interpreter
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
::
=/  memo-call
  =>  ..ride  !.
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  ~>  %memo./user
  (g v)
::
=|  =long-ska
=.   long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..scow:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (scow %ud 5)
::
=^  [func=bell *]  long-ska  (ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
::
=/  formula=^
  =>  subject
  ;;  ^
  !=
  %.  ~[1]
  |=  l=(list @)
  ^-  (list @)
  ?~  l  ~
  [(dec i.l) $(l t.l)]
::
=^  [func=bell *]  long-ska  (memo-call ska-poke [&+subject formula] long-ska)
=.  long-ska  (ska-cole-restore long-ska)
=/  [rev=(jug bell bell) scc-map=(map bell (set bell))]  (graph-info:li long-ska)
=/  [scc-here=(set bell) sccs=(map bell (set bell))]  (scc-of func calls.long-ska ~)
=/  jets-hot=jets-comp
  %-  malt
  ^-  (list [ring jets-comp-info])
  =/  unary=need-ordered  [none+~ this+~ none+~]
  =/  binary=need-ordered  [none+~ [this+~ this+~] none+~]
  :~  [/add/one/k135^2 binary]
      [/dec/one/k135^2 unary]
      [/div/one/k135^2 binary]
      [/dvr/one/k135^2 binary]
      [/gte/one/k135^2 binary]
      [/gth/one/k135^2 binary]
      [/lte/one/k135^2 binary]
      [/lth/one/k135^2 binary]
      [/max/one/k135^2 binary]
      [/min/one/k135^2 binary]
      [/mod/one/k135^2 binary]
      [/mul/one/k135^2 binary]
      [/sub/one/k135^2 binary]
      [/bex/two/one/k135^2 unary]
  ==
::
?:  |
  noun+(run:li |+subject func scc-here rev long-ska scc-map jets-hot)
=/  cache=comp-cache  [~ ~ sccs]
=/  todo=(list (set bell))  ~(tap in (silt ~(val by scc-map)))
=|  all-straights=(map bell straight)
=^  all-straights  cache
  |-  ^-  [(map bell straight) comp-cache]
  ?~  todo  [all-straights cache]
  =^  m=(map bell straight)  cache
    (compile-scc i.todo [code jets calls]:long-ska jets-hot cache)
  $(todo t.todo, all-straights (~(uni by all-straights) m))
::
:: :-  %tang
:: %-  flop
~>  %bout.[0 'test-run-ir total']
:-  %noun
%-  to-wain:format  %-  crip
^-  tape
%-  zing
^-  (list tape)
=-  ?:  |  -  :_  -
    =/  pessimistic=straight
      -<:(compile-unary func scc-here [code jets calls]:long-ska ~ cache)
    ::
    =.  pessimistic  (optimize pessimistic)
    "{<`@ux`(mug func)>} pessimistic:\0a{(print-straight:li "  " pessimistic)}\0a"
%+  turn  ~(tap by all-straights)
|=  [k=bell v=straight]
=.  v  (optimize v)
"{<`@ux`(mug k)>}:\0a{(print-straight:li "  " v)}\0a"