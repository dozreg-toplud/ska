/-  *noir
/+  skan
/+  map-locals-gen=ream-gen-test
/+  hoot
::
:-  %say  |=  *  :-  %noun
::
=+  [map-locals gen]=map-locals-gen
=/  s  `*`['42' hoot]
=/  n=nomm
  ?^  m=(~(get by sits.memo.gen) 0v0 0x0)
    code.u.m
  =/  loc  (~(got by map-locals) 0x0)
  nomm.loc
::
=|  trace=(list spot)
~&  %nomm-eval
~>  %bout
|-  ^-  (unit)
?-    n
    [p=^ q=*]
  =/  l  $(n p.n)
  ?~  l  ~
  =/  r  $(n q.n)
  ?~  r  ~
  `[u.l u.r]
::
    [%0 p=@]
  ?:  =(0 p.n)
    ~&  '[%0 0]'
    ~&  trace
    ~
  ?:  =(1 p.n)  `s
  =-  ~?  ?=(~ -)  '%0 crash'  -
  (mole |.(.*(s [0 p.n])))
::
    [%1 p=*]
  `p.n
::
    [%2 *]
  =/  s1  $(n p.n)
  ?~  s1  ~
  =/  f1  $(n q.n)
  ?~  f1  ~
  ?~  site.n
    ~&  %indirect
    ~<  %slog.[0 '%indirect-done']
    :: !!
    :: (run-nomm u.s1 u.f1)
    (mole |.(.*(u.s1 u.f1)))
  =;  new=nomm
    ?^  res=(jet:skan u.s1 u.f1)  u.res
    $(s u.s1, n new)
  ?-    -.site.n
      %memo
    =/  m  ~|  p.site.n  (~(got by idxs.memo.gen) p.site.n)
    ?>  =(u.f1 fol.m)  
    code.m
  ::
      %site
    =/  loc  ~|  q.p.site.n  (~(got by map-locals) q.p.site.n)
    ?>  =(u.f1 fol.loc)
    nomm.loc
  ==
::
    [%3 *]
  =/  p  $(n p.n)
  ?~  p  ~
  `.?(u.p)
::
    [%4 *]
  =/  p  $(n p.n)
  ?~  p  ~
  ?^  u.p  ~&  '%4 cell'  ~
  `+(u.p)
::
    [%5 *]
  =/  p  $(n p.n)
  ?~  p  ~
  =/  q  $(n q.n)
  ?~  q  ~
  `=(u.p u.q)
::
    [%6 *]
  =/  p  $(n p.n)
  ?~  p  ~
  ?+  u.p  ~&('%6 non-loobean' ~)
    %&  $(n q.n)
    %|  $(n r.n)
  ==
::
    [%7 *]
  =/  p  $(n p.n)
  ?~  p  ~
  $(s u.p, n q.n)
::
    [%10 *]
  ?:  =(0 p.p.n)  ~&  '%10 0'  ~
  =/  don  $(n q.p.n)
  ?~  don  ~
  =/  rec  $(n q.n)
  ?~  rec  ~
  =-  ~?  ?=(~ -)  '%10 crash'  -
  (mole |.(.*([u.don u.rec] [%10 [p.p.n %0 2] %0 3])))
::
    [%s11 *]
  $(n q.n)
::
    [%d11 *]
  =?  trace  =(p.p.n %spot)
    =/  pot=(unit spot)  ((soft spot) +.q.p.n)
    ?~  pot  trace
    ~&  u.pot
    [u.pot trace]
  ::
  =/  h  $(n q.p.n)
  ?~  h  ~
  $(n q.n)
::
    [%12 *]
  ~|  %no-scry  !!
==