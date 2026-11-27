
=/  cases=(list [nam=@tas gat=*])
  :~  :-  %dec   =>  ~  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
      :-  %lent  =>  ~  |=(l=* =|(n=@ |-(?@(l n $(l +.l, n .+(n))))))
      :-  %lfl   =>  ~  |=(t=* |-(?@(t t $(t -.t))))
      :-  %flat  =>  ~  |=(t=* =|(a=* |-(?@(t [t a] $(t -.t, a $(t +.t))))))
      :-  %evod
        =>  ~  =<  ev
        |%  ++  ev  |=(n=@ ?:(.=(0 n) & (od (dc n))))
            ++  od  |=(n=@ ?:(.=(0 n) | (ev (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %cyc3
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) 0 (b (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) 1 (c (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) 2 (a (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %pq
        =>  ~  =<  p
        |%  ++  p  |=(x=* ?@(x 0 (q +.x)))
            ++  q  |=(x=* ?@(x 1 (p -.x)))
        --
      :-  %pq2
        =>  ~  =<  p
        |%  ++  p  |=(x=* ?@(x 0 ?@(-.x 1 (q +.x))))
            ++  q  |=(x=* ?@(x 1 (r -.x)))
            ++  r  |=(x=* ?@(x 2 ?@(+.x (p x) (p +.x))))
        --
      :-  %swap  =>  ~  |=([a=@ b=@ c=@] |-(?:(.=(a 0) b $(a +(a), b c, c b))))
      :-  %fld   =>  ~  |=(s=[i=@ j=@ k=*] |-(?:(.=(i.s 0) k.s $(i.s .+(i.s), k.s [j.s k.s]))))
      :-  %self2
        =>  ~  =<  a
        |%  ++  a  |=(x=* ?@(x 0 ?@(-.x (a +.x) (b -.x))))
            ++  b  |=(x=* ?@(x 1 (a [+.x -.x])))
        --
      :-  %deep
        =>  ~  =<  a
        |%  ++  a  |=(x=[p=* q=*] ?@(p.x q.x (b [-.p.x q.x])))
            ++  b  |=(y=[p=* q=*] ?@(q.y (a [+.y p.y]) (c [q.y p.y])))
            ++  c  |=(z=[p=* q=*] ?@(p.z (a z) (a [+.p.z q.z])))
        --
      :-  %ack
        =>  ~  =<  ack
        |%  ++  ack
              |=  [m=@ n=@]
              ?:  .=(0 m)  .+(n)
              ?:  .=(0 n)  (ack (dc m) 1)
              (ack (dc m) (ack m (dc n)))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %tree
        =>  ~  =<  sz
        |%  ++  sz  |=(t=* ?@(t 0 (ad (sz -.t) (sz +.t))))
            ++  ad  |=([a=@ b=@] |-(?:(.=(0 a) b $(a (dc a), b .+(b)))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %grow
        =>  ~  =<  a
        |%  ++  a  |=(x=* ?@(x 0 (b x)))
            ++  b  |=(x=* ?@(x 1 ?@(+.x (a -.x) (c x))))
            ++  c  |=(x=* ?@(x 2 ?@(-.x (a +.x) (b [-.-.x +.x]))))
        --
      :-  %deep4
        =>  ~  =<  a
        |%  ++  a  |=(x=[p=* q=*] ?@(p.x q.x (b [-.p.x q.x])))
            ++  b  |=(y=[p=* q=*] ?@(q.y (c [+.y p.y]) (c [q.y p.y])))
            ++  c  |=(z=[p=* q=*] ?@(p.z (d z) (d [+.p.z q.z])))
            ++  d  |=(w=[p=* q=*] ?@(q.w (a w) (a [q.w p.w])))
        --
      :-  %deep2
        =>  ~  =<  a
        |%  ++  a  |=(x=[p=* q=*] ?@(p.x q.x ?@(q.x (b x) (c [-.p.x q.x]))))
            ++  b  |=(y=[p=* q=*] (a [q.y p.y]))
            ++  c  |=(z=[p=* q=*] ?@(q.z (a [+.z p.z]) (b [-.q.z p.z])))
        --
      :-  %rot3
        =>  ~  =<  a
        |%  ++  a  |=(s=[i=* j=* k=*] ?@(i.s j.s (b [j.s k.s -.i.s])))
            ++  b  |=(s=[i=* j=* k=*] ?@(j.s k.s (c [k.s +.j.s i.s])))
            ++  c  |=(s=[i=* j=* k=*] ?@(k.s i.s (a [i.s j.s -.k.s])))
        --
  ==

=/  subs=(list [nam=@tas sub=*])
  :~
      [%swap [0 0 1 2]]
      [%swap [0 5]]
      [%fld [0 0 1 2]]
      [%fld [0 0 1 [2 3]]]
      [%rot3 [0 [1 2] 3 4]]
      [%rot3 [0 [1 2] [3 4] [5 6]]]
      [%rot3 [0 [[1 2] 3] [[4 5] 6] [[7 8] 9]]]
      [%rot3 [0 [1 2] [3 4] 5]]
      [%rot3 [0 [[[1 2] [3 4]] [[5 6] [7 8]] [[9 10] [11 12]]]]]
  ==
=/  bad=@ud  0
|-  ^-  @
?~  subs  ~&([%done %bad bad] bad)
=/  gat=*
  =/  c  cases
  |-  ?~  c  !!  ?:  =(nam.i.c nam.i.subs)  gat.i.c  $(c t.c)
=/  fol=*  [8 [1 gat] [9 2 [10 [6 [0 7]] [0 2]]]]
=/  a=toon  (mook (mink [sub.i.subs fol] ~))
=^  ton=tone  ..^poke  (eval-top [sub.i.subs fol] ~)
=^  b=toon  ..^poke  (eval-mook ton)
~&  ?:  =(a b)  [nam.i.subs %same ?:(?=(%2 -.a) [%2 (lent p.a)] ?:(?=(%0 -.a) a a))]
    [nam.i.subs %differ mock=a ska=b]
$(subs t.subs, bad ?:(=(a b) bad +(bad)))
