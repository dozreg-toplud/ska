=/  lib  .
=/  fols=(list *)
  =>  lib
  :~  !=(=/(f |=(a=* .*(a a)) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=(a=* [a .*(a a)]) [(f (add 2 3)) (f 5) (f 7)]))
      !=(=/(f |=(a=* [.*(a a) a 7]) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=([a=* b=*] [b .*(a a)]) [(f (add 2 3) 4) (f 5 4) (f 5 (add 1 1))]))
      !=(=/(f |=(a=* ?:(=(a 5) 1 .*(a a))) [(f (add 2 3)) (f 5)]))
      !=(=/(f |=(a=* .*(a a)) [(f (add 2 3)) (f 5) (f [1 2])]))
      !=(=/(g |=(a=* .*(a a)) =/(f |=(a=* [(g a) (g 6)]) [(f (add 2 3)) (f 5)])))
  ==
=/  no
  |=  c=cape
  ^-  ?
  ?@  c  !c
  &($(c -.c) $(c +.c))
=/  meets
  |=  [ca=cape da=* cb=cape db=*]
  ^-  ?
  ?:  |((no ca) (no cb))  &
  ?:  &(?=(%& ca) ?=(%& cb))  =(da db)
  ?:  |(?=(@ da) ?=(@ db))  |
  =/  ha=cape  ?@(ca ca -.ca)
  =/  ta=cape  ?@(ca ca +.ca)
  =/  hb=cape  ?@(cb cb -.cb)
  =/  tb=cape  ?@(cb cb +.cb)
  ?&  $(ca ha, da -.da, cb hb, db -.db)
      $(ca ta, da +.da, cb tb, db +.db)
  ==
=/  mets  |=([a=sock b=sock] ^-(? ?@(a | ?@(b | (meets cape.a data.a cape.b data.b)))))
::  a sock has a noun: not %void, and a cape that knows something of a
::  cell has a cell of data
::
=/  wf
  |=  [c=cape d=*]
  ^-  ?
  ?@  c  &
  ?:  (no c)  &
  ?@  d  |
  &($(c -.c, d -.d) $(c +.c, d +.d))
=/  inhab  |=(s=sock ^-(? ?@(s | (wf cape.s data.s))))
::  %10 at axis 0 in a nomm
::
=/  ax0
  |=  n=nomm
  ^-  @ud
  ?-  n
    [^ *]      (add $(n -.n) $(n +.n))
    [%0 *]     0
    [%1 *]     0
    [%2 *]     (add $(n p.n) $(n q.n))
    [%3 *]     $(n p.n)
    [%4 *]     $(n p.n)
    [%5 *]     (add $(n p.n) $(n q.n))
    [%6 *]     :(add $(n p.n) $(n q.n) $(n r.n))
    [%7 *]     (add $(n p.n) $(n q.n))
    [%10 *]    :(add ?:(=(0 p.p.n) 1 0) $(n q.p.n) $(n q.n))
    [%11 *]    ?@(p.n $(n q.n) (add $(n q.p.n) $(n q.n)))
    [%12 *]    (add $(n p.n) $(n q.n))
    [%mean *]  (add $(n p.n) $(n q.n))
  ==
::  the residue: two identities of one code bell in the pruned graph whose
::  products, patched for a sock, share no noun
::
=/  resid
  |=  pruned=callgraph
  ^-  [@ud @ud @ud @ud]
  =/  groups=(map bell (list [identity datum]))
    %-  ~(rep by pruned)
    |=  [[id=identity d=datum] acc=(map bell (list [identity datum]))]
    =/  b=bell  [less-code.d fol.id]
    (~(put by acc) b [[id d] (~(gut by acc) b ~)])
  %-  ~(rep by groups)
  |=  [[b=bell l=(list [identity datum])] ng=@ud np=@ud fm=@ud fe=@ud]
  ?:  (lth (lent l) 2)  [ng np fm fe]
  =/  ps=(list [[identity datum] [identity datum]])
    %-  zing
    %+  turn  l
    |=  x=[identity datum]
    (turn l |=(y=[identity datum] [x y]))
  =/  r
    %+  roll  ps
    |=  [[x=[id=identity d=datum] y=[id=identity d=datum]] n=@ud m=@ud e=@ud]
    ?:  =(x y)  [n m e]
    =/  ks=(list sock)  ~[less.b more.id.x more.id.y]
    =/  bad=?
      %+  lien  ks
      |=  k=sock
      ^-  ?
      !(mets sock:(patch-prod [prod map]:d.x k) sock:(patch-prod [prod map]:d.y k))
    =/  neq=?
      !=(sock:(patch-prod [prod map]:d.x less.b) sock:(patch-prod [prod map]:d.y less.b))
    ~?  bad  [%resid-fail fol=(mug fol.b)]
    [+(n) ?:(bad +(m) m) ?:(neq +(e) e)]
  [+(ng) (add np -.r) (add fm +<.r) (add fe +>.r)]
::  the facts about the datums of a state
::
=/  facts
  |=  lon=long-ska
  ^-  [@ud @ud @ud @ud]
  %+  roll  ~(tap by memo.lon)
  |=  [[fol=^ m=(map sock [identity datum])] n=@ud fp=@ud fl=@ud fa=@ud]
  %+  roll  ~(tap by m)
  |=  [[l=sock [id=identity d=datum]] n=_n fp=_fp fl=_fl fa=_fa]
  :*  +(n)
      ?:((inhab prod.d) fp +(fp))
      ?:((inhab l) fl +(fl))
      (add fa (ax0 nomm.d))
  ==
=|  lon=long-ska
=/  n=@ud  0
|-  ^-  @
?~  fols  0
=/  f=^  ?>(?=(^ i.fols) i.fols)
=/  root-identity=identity  [&+lib f]
=/  gr  (mule |.((ska-callgraph root-identity memo.lon [root core batt arms ~]:jets.lon)))
?:  ?=(%| -.gr)  ~&  [%crash-graph n]  $(fols t.fols, n +(n))
=/  pruned=callgraph  (prune-callgraph -.p.gr root-identity)
=/  rs  (resid pruned)
=/  r  (mule |.((ska-poke [&+lib f] lon ~)))
?:  ?=(%| -.r)  ~&  [%crash n]  $(fols t.fols, n +(n))
=.  lon  +.p.r
=/  fs  (facts lon)
~&  [n entries=~(wyt by pruned) groups=-.rs pairs=+<.rs resid-fail=+>-.rs unequal=+>+.rs memo=-.fs prod-void=+<.fs less-void=+>-.fs ax0=+>+.fs]
$(fols t.fols, n +(n))
