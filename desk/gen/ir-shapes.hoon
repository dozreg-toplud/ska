/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  *
:-  %noun
::  The whole computation runs with scrying disabled, so that %memo hints
::  save into the persistent cache
::
=/  res
  %-  ~(mule vi |)
  |.
  =|  =long-ska
  =.   long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
  =/  subject  ..scow:hoot-zpdt
  =/  formula=^
    =>  subject
    ;;  ^
    !=
    (scow %ud 5)
  ::
  =^  func=bell  long-ska
    ~>  %bout.[1 'ska-poke 1']
    (ska-poke [&+subject formula] long-ska)
  ::
  =/  subject  ..ride:hoot-zpdt
  =/  formula=^
    =>  subject
    ;;  ^
    !=
    (ride %noun '42')
  ::
  =^  func=bell  long-ska
    ~>  %bout.[1 'ska-poke 3']
    (ska-poke [&+subject formula] long-ska)
  ::
  =/  [bell-graph=(jug bell bell) rev=(jug bell bell)]
    (simple-bell-graph-and-reversed graph.final.long-ska)
  ::
  =/  sccs=(list (set bell))  (tarjan bell-graph)
  =/  scc-map=(map bell (set bell))
    =|  out=(map bell (set bell))
    |-  ^+  out
    ?~  sccs  out
    =.  out
      %-  ~(rep in i.sccs)
      |=  [b=bell acc=_out]
      (~(put by acc) b i.sccs)
    ::
    $(sccs t.sccs)
  ::
  =/  jets-hot=(map ring need-ordered)
    %-  malt
    ^-  (list [ring need-ordered])
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
  ::  SCC size statistics
  ::
  =/  sizes=(list @ud)  (turn sccs |=(s=(set bell) ~(wyt in s)))
  =/  multi  (lent (skim sizes |=(n=@ud (gth n 1))))
  =/  big=(set bell)
    %+  roll  sccs
    |=  [s=(set bell) acc=(set bell)]
    ?:((gth ~(wyt in s) ~(wyt in acc)) s acc)
  ::
  ~&  :*  %sccs  (lent sccs)
          %functions  ~(wyt by scc-map)
          %multi-member  multi
          %max-size  ~(wyt in big)
          %sum-squares  (roll (turn sizes |=(n=@ud (mul n n))) add)
          %top-sizes  (scag 8 (sort sizes gth))
      ==
  ::
  =/  big-1=(map bell straight)
    ~>  %bout.[1 'compile biggest scc']
    (compile-scc big rev [code jets]:long-ska scc-map jets-hot)
  ::
  =/  big-2=(map bell straight)
    ~>  %bout.[1 'compile biggest scc again']
    (compile-scc big rev [code jets]:long-ska scc-map jets-hot)
  ::
  ~&  [%biggest-same =(big-1 big-2)]
  ::
  =/  all-straights=(map bell straight)
    ~>  %bout.[1 'compile all distinct sccs']
    %+  roll  sccs
    |=  [s=(set bell) acc=(map bell straight)]
    (~(uni by acc) (compile-scc s rev [code jets]:long-ska scc-map jets-hot))
  ::
  ::  one line per function: SHAPE <mug> <encoded subject shape>
  ::
  =/  enc
    |=  n=need-ordered
    ^-  tape
    =*  enc  .
    ?-  -.n
      %none  "n"
      %this  "t"
      %both  :(weld "b(" (enc h.n) "," (enc t.n) ")")
      ^      :(weld "(" (enc -.n) "," (enc +.n) ")")
    ==
  ::
  =/  rows=(list [@ud tape])
    %+  turn  ~(tap by all-straights)
    |=  [k=bell v=straight]
    [(mug k) (enc need.v)]
  ::
  =.  rows  (sort rows |=([[a=@ud *] [b=@ud *]] (lth a b)))
  =/  args  (roll (turn ~(val by all-straights) |=(s=straight n-args.s)) add)
  %-  (slog (turn rows |=([m=@ud t=tape] leaf+:(weld "SHAPE " (scow %ud m) " " t))))
  [%functions ~(wyt by all-straights) %args args]
?:  ?=(%& -.res)  p.res
(mean p.res)
