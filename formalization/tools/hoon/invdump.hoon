::  The clauses of PGood2 (track P, README Gaps 23, fifth session) on the
::  21 %full pokes of sprestdump.hoon: after each poke, whether
::  %ccall  every callee in calls is a key of code              (Closed)
::  %cinfo  every %2 info bell of an entry's nomm is a key of code (Closed)
::  %smap   sure.cache is a treap                              (IsMap sure)
::  %skey   sure.cache and nary.cache have the same keys
::  %imap   inl.cache is a treap                               (IsMap inl)
::  %ikey   every key of inl.cache is a key of code
::  %ival   every entry of inl.cache is +inlined of its bell on the
::          state with inl.cache emptied (a function of the table)
::  %sccs   SccsGood: every sccs entry S of k is a treap set holding k,
::          and every member k' of S has the entry S
::  %nary   NaryClosed: the keys of nary.cache are whole SCCs of sccs
::  and the sizes of code, inl, sure, nary, sccs.
::
=/  fk=*
  !=
  =>  ~
  =<  a
  ~%  %k  ~  ~
  |%
  ++  a  42
  --
=/  fc=*
  !=
  =>  ~
  =<  b
  ~%  %c  ~  ~
  |%
  ++  a  42
  ++  b  [a 3]
  --
=/  fw=*   [6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]
=/  fm2=*  [6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]
=/  fid=*  [8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]
=/  dec=*  [8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
=/  even=*  [6 [5 [1 0] 0 6] [1 0] 6 [5 [1 1] 0 6] [1 1] 9 2 10 [6 8 [9 2 10 [6 0 14] 0 7] 9 2 0 1] 0 1]
=/  ma=*  [6 [3 [0 3]] [9 5 [10 [3 [0 7]] [0 1]]] [1 0]]
=/  mb=*  [6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [1 1]]
=/  mc=*  [6 [3 [0 3]] [8 [9 5 [10 [3 [0 7]] [0 1]]] [9 4 [10 [3 [0 15]] [0 3]]]] [1 2]]
=/  pairs=(list [* *])
  :~  [0 fk]
      [0 [4 0 1]]
      [0 fc]
      [[0 [fid [fw fm2]]] [0 0]]
      [5 [0 1]]
      [7 dec]
      [0 fk]
      [[0 [fid [fw fm2]]] fid]
      [9 [6 [5 [0 1] 1 0] [1 0] 0 0]]
      [3 [11 1.886.217.588 [1 0]]]
      [4 [11 [1.886.217.588 1 1] 0 1]]
      [[0 [fid [fw fm2]]] [2 [0 1] 1 fid]]
      [[0 [fw fm2]] [2 [0 1] 0 2]]
      [[even [5 0]] [9 2 0 1]]
      [0 [4 0 1]]
      [7 dec]
      [[0 [fid [fw fm2]]] fid]
      [0 fc]
      [[[ma mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [[[mc mb] [1 2 3 4 5 6 0]] [9 4 [0 1]]]
      [[[ma mb] [9 8 7 0]] [9 5 [0 1]]]
  ==
=/  infos
  |=  n=*
  ^-  (list *)
  ?@  n  ~
  ?^  -.n  (weld $(n -.n) $(n +.n))
  ?+  -.n  ~
    %2     =/  inf=*  +>+.n
           =/  rest=(list *)  (weld $(n +<.n) $(n +>-.n))
           ?@  inf  rest
           [+<.inf rest]
    %3     $(n +<.n)
    %4     $(n +<.n)
    %5     (weld $(n +<.n) $(n +>.n))
    %6     :(weld $(n +<.n) $(n +>-.n) $(n +>+.n))
    %7     (weld $(n +<.n) $(n +>.n))
    %10    (weld $(n +<+.n) $(n +>.n))
    %11    ?@  +<.n  $(n +>.n)
           (weld $(n +<+.n) $(n +>.n))
    %12    (weld $(n +<.n) $(n +>.n))
    %mean  (weld $(n +<.n) $(n +>.n))
  ==
=|  n=@ud
|-
?~  pairs  0
=^  p  ..poke  (poke [%full -.i.pairs ;;(^ +.i.pairs)])
=/  lon=long-ska  long-ska.state
=/  ks=(set *)  (silt (turn ~(tap in ~(key by code.lon)) |=(b=bell `*`b)))
=/  ok-ccall=?
  %+  levy  ~(tap by calls.lon)
  |=  [b=bell cs=(set bell)]
  (levy ~(tap in cs) |=(c=bell (~(has by code.lon) c)))
=/  ok-cinfo=?
  %+  levy  ~(tap by code.lon)
  |=  [b=bell e=code-entry]
  (levy (infos `*`nomm.e) |=(c=* (~(has in ks) c)))
=/  ca  cache.state
=/  ok-smap=?  ~(apt by sure.ca)
=/  ok-skey=?  =(~(key by sure.ca) ~(key by nary.ca))
=/  ok-imap=?  ~(apt by inl.ca)
=/  ok-ikey=?  (levy ~(tap in ~(key by inl.ca)) |=(b=bell (~(has by code.lon) b)))
=/  ok-ival=?
  %+  levy  ~(tap by inl.ca)
  |=  [b=bell v=nomm]
  =(v -:(inlined b [code jets calls]:lon jets-hot.state ca(inl ~)))
=/  ok-sccs=?
  %+  levy  ~(tap by sccs.ca)
  |=  [k=bell s=(set bell)]
  ?&  ~(apt in s)
      (~(has in s) k)
      (levy ~(tap in s) |=(k2=bell =((~(get by sccs.ca) k2) `s)))
  ==
=/  ok-nary=?
  %+  levy  ~(tap in ~(key by nary.ca))
  |=  k=bell
  ?~  s=(~(get by sccs.ca) k)  |
  (levy ~(tap in u.s) |=(k2=bell (~(has by nary.ca) k2)))
~&  :*  %i  n  %ccall  ok-ccall  %cinfo  ok-cinfo  %smap  ok-smap  %skey  ok-skey
        %imap  ok-imap  %ikey  ok-ikey  %ival  ok-ival  %sccs  ok-sccs  %nary  ok-nary
        %sizes  ~(wyt by code.lon)  ~(wyt by inl.ca)  ~(wyt by sure.ca)  ~(wyt by nary.ca)  ~(wyt by sccs.ca)
    ==
$(pairs t.pairs, n +(n))
