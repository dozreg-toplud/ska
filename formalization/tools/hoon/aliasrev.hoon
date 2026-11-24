::  +alias trusts rev: a block of topo that rev lists as a successor of a
::  walked block is walked, even when no jump reaches it.  Here 0w1 is not
::  reachable (block 0w0 hops to 0w2), but rev lists 0w0 as its predecessor:
::  its %mov renames 0v2 to 0v5 in the global old, and the later %don of
::  0v2 in 0w2, after the one live definition [%imm 5 0v2], reads 0v5.
::  TopoInv holds (topo has every reachable block, in order, and rev lists
::  every jump of a member of topo); rev-cfg alone never lists 0w1 there.
::
=/  b0=blob  [~ ~ [%hop ~ 0w2]]
=/  b1=blob  [~ ~[[%mov 0v5 0v2]] [%bom ~]]
=/  b2=blob  [~ ~[[%imm 5 0v2]] [%don 0v2]]
=/  bl=(map @uwoo blob)  (my ~[[0w0 b0] [0w1 b1] [0w2 b2]])
=/  topo=(list @uwoo)  ~[0w0 0w1 0w2]
=/  rev0  (rev-cfg bl (sy topo))
=/  rev  (~(add ja rev0) `@uwoo`0w1 `@uwoo`0w0)
=/  out  (alias 6 bl rev topo)
=/  out0  (alias 6 bl rev0 topo)
=/  cb=straight-out  [*need-ordered 6 bl]
=/  ca=straight-out  [*need-ordered 6 +.out]
=/  regs=(map @uvre (unit *))  (my ~[[0v0 `0] [0v1 `0] [0v2 `0] [0v3 `0] [0v4 `0] [0v5 `7]])
=/  tb  -:(eval-blob [regs ~] (~(got by blocks.cb) 0w0) cb ~ ~)
=/  ta  -:(eval-blob [regs ~] (~(got by blocks.ca) 0w0) ca ~ ~)
~&  [%rev rev0 rev]
~&  [%after-alias out]
~&  [%after-alias-revcfg out0]
~&  [%before tb %after ta]
0
