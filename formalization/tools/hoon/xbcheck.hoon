::  +alias on xbBlocks of lemmas/Compiler/AuditOptTotal.lean: block 0 checks
::  that register 1 is a loob (%lob) and ends in a %brn on it, blocks 1 and 2
::  return.  (1) +alias on it, (2) +optimize on it (rounds of +optimize-once,
::  capped, then +optimize itself), (3) +alias again on what (1) returned
::
=/  b0=blob  [~ ~[[%lob 0v1]] [%brn 0v1 [~ 0w1] [~ 0w2]]]
=/  b1=blob  [~ ~ [%don 0v1]]
=/  b2=blob  [~ ~ [%don 0v0]]
=/  blocks=(map @uwoo blob)  (my ~[[0w0 b0] [0w1 b1] [0w2 b2]])
=/  topo=(list @uwoo)  ~[0w0 0w1 0w2]
=/  rev=(jar @uwoo @uwoo)  (rev-cfg blocks (sy topo))
=/  srt
  |=  m=(map @uwoo blob)
  (sort ~(tap by m) |=([a=[p=@uwoo q=blob] b=[p=@uwoo q=blob]] (lth p.a p.b)))
~&  [%input-bb-topo (bb-topo blocks)]
~&  [%input-rev ~(tap by rev)]
::  (1)
::
=/  r1  (alias 2 blocks rev topo)
~&  [%alias-1-folded -.r1]
~&  [%alias-1-blocks (srt +.r1)]
::  (2)
::
=/  s0=straight  [[%both [%this ~] [%this ~]] 2 blocks]
=/  cap=@ud  50
=/  res=(unit [n=@ud s=straight])
  =/  s=straight  s0
  =/  n=@ud  0
  |-  ^-  (unit [n=@ud s=straight])
  ?:  (gte n cap)  ~
  =^  ch=?  s  (optimize-once s)
  ~&  [%optimize-once-round +(n) %changed ch %blocks (srt blocks.s)]
  ?.  ch  `[+(n) s]
  $(n +(n))
=/  p2=@
  ?~  res
    ~&  [%optimize-no-fixed-point-after-rounds cap]
    0
  =/  out=straight-out  (optimize s0)
  ~&  [%optimize-rounds n.u.res]
  ~&  :-  %optimize-blocks
      %+  sort  ~(tap by blocks.out)
      |=([a=[p=@uwoo q=blob-out] b=[p=@uwoo q=blob-out]] (lth p.a p.b))
  ~&  [%optimize-equals-capped-loop =(out `straight-out`[need.s.u.res n-args.s.u.res (switch-chains blocks.s.u.res)])]
  0
::  (3)
::
=/  bl1=(map @uwoo blob)  +.r1
=/  topo1=(list @uwoo)  (skim topo ~(has by bl1))
=/  rev1=(jar @uwoo @uwoo)  (rev-cfg bl1 (sy topo1))
=/  r2  (alias 2 bl1 rev1 topo1)
~&  [%alias-2-folded -.r2]
~&  [%alias-2-blocks (srt +.r2)]
~&  [%alias-2-same-blocks =(+.r2 bl1)]
p2
