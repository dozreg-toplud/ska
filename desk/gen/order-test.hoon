::  Synthetic check of the callee-first postorder used by compile-scc
::
:-  %say  |=  *
:-  %noun
=/  scc=(set @)  (sy ~[1 2 3 4 5])
::  rev: callee -> callers.  calls: 1->2, 2->3, 3->4, 4->1 (cycle), 1->5
=/  rev=(jug @ @)
  %-  ~(gas ju *(jug @ @))
  ~[[2 1] [3 2] [4 3] [1 4] [5 1]]
=/  fwd=(jug @ @)
  %-  ~(rep in scc)
  |=  [m=@ acc=(jug @ @)]
  %-  ~(rep in (~(int in (~(get ju rev) m)) scc))
  |=  [c=@ acc=_acc]
  (~(put ju acc) c m)
::
~&  [%fwd fwd]
=/  visit
  |=  [n=@ seen=(set @) post=(list @)]
  ^-  [(list @) (set @)]
  =*  visit  .
  =.  seen  (~(put in seen) n)
  =/  kids  ~(tap in (~(get ju fwd) n))
  ~&  [%visit n kids]
  |-  ^-  [(list @) (set @)]
  ?~  kids  [[n post] seen]
  ?:  (~(has in seen) i.kids)  $(kids t.kids)
  =/  sub  (visit i.kids seen post)
  $(kids t.kids, post -.sub, seen +.sub)
::
=/  res
  %+  roll  ~(tap in scc)
  |=  [r=@ seen=(set @) post=(list @)]
  ~&  [%root r seen post]
  ?:  (~(has in seen) r)  [seen post]
  =^  post  seen  (visit r seen post)
  [seen post]
::
=/  post=(list @)  +.res
[%order (flop post) %seen -.res]
