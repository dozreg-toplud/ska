::  Functions of the ride poke's graph whose formula contains a given atom
::  (a constant such as a %tas from a ~| or ~&): [formula-mug less-code-axes
::  direct indirect prod-known-axes], for reachability questions when source
::  spots are absent.
::
/+  *nock-compilation
/+  hoot-zpdt
/+  hoot-zpdt-fol
::
:-  %say  |=  [* [needle=@ ~] ~]
=|  =long-ska
=.  long-ska  +:(ska-poke [&+~ hoot-zpdt-fol] long-ska)
=/  subject  ..ride:hoot-zpdt
=/  formula=^
  =>  subject
  ;;  ^
  !=
  (ride %noun '42')
::
=^  func=bell  long-ska  (ska-poke [&+subject formula] long-ska)
=/  g  graph.final.long-ska
=/  has-atom
  |=  n=*
  ^-  ?
  ?@  n  =(n needle)
  ~+
  |($(n -.n) $(n +.n))
=/  count-2
  |=  =nomm
  ^-  [direct=@ indirect=@]
  ?-  nomm
    [^ *]    =/(a $(nomm -.nomm) =/(b $(nomm +.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%0 *]   [0 0]
    [%1 *]   [0 0]
    [%2 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add ?~(info.nomm 0 1) (add direct.a direct.b)) (add ?~(info.nomm 1 0) (add indirect.a indirect.b))]))
    [%3 *]   $(nomm p.nomm)
    [%4 *]   $(nomm p.nomm)
    [%5 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%6 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) =/(c $(nomm r.nomm) [:(add direct.a direct.b direct.c) :(add indirect.a indirect.b indirect.c)])))
    [%7 *]   =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%10 *]  =/(a $(nomm q.p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
    [%11 *]  ?@(p.nomm $(nomm q.nomm) =/(a $(nomm q.p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)])))
    [%12 *]  =/(a $(nomm p.nomm) =/(b $(nomm q.nomm) [(add direct.a direct.b) (add indirect.a indirect.b)]))
  ==
:-  %noun
%+  murn  ~(tap by g)
|=  [id=identity d=datum]
?.  (has-atom fol.id)  ~
=/  n  (count-2 nomm.d)
`[`@ux`(mug fol.id) (lent (yea:ca cape.less-code.d)) n (lent (yea:ca cape.prod.d))]
