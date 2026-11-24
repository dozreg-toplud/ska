::  +alias renames a read of an eliminated register in a later block, which
::  is sound only if the source register is not written again in between.
::  Blocks with the block invariant DInvT (no parameters, no hints, acyclic)
::  where register 0v1 is read by a %mov and then written by an %imm: the
::  pass makes the %don of 0v2 a %don of 0v1, so the code returns 5 where
::  it returned the input register 0v1 (here 7)
::
=/  b0=blob  [~ ~[[%mov 0v1 0v2] [%imm 5 0v1]] [%hop ~ 0w1]]
=/  b1=blob  [~ ~ [%don 0v2]]
=/  bl=(map @uwoo blob)  (my ~[[0w0 b0] [0w1 b1]])
=/  topo  (bb-topo bl)
=/  rev  (rev-cfg bl (sy topo))
=/  out  (alias 2 bl rev topo)
=/  cb=straight-out  [*need-ordered 2 bl]
=/  ca=straight-out  [*need-ordered 2 +.out]
=/  regs=(map @uvre (unit *))  (my ~[[0v0 `0] [0v1 `7]])
=/  tb  -:(eval-blob [regs ~] (~(got by blocks.cb) 0w0) cb ~ ~)
=/  ta  -:(eval-blob [regs ~] (~(got by blocks.ca) 0w0) ca ~ ~)
~&  [%after-alias out]
~&  [%before tb %after ta]
0
