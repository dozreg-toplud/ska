::  +alias on wBl of lemmas/Compiler/OptLinkTotalAlias.lean (the witness of
::  not_aliasRet): the one block [%cel 0v1] [%bom ~], which reads register 1
::  and defines nothing.  (1) +alias with two arguments returns, (2) with one
::  argument it crashes (register 1 is neither an argument nor defined), as
::  the model's none, (3) the same through +optimize with n-args 1
::
=/  b0=blob  [~ ~[[%cel 0v1]] [%bom ~]]
=/  blocks=(map @uwoo blob)  (my ~[[0w0 b0]])
=/  topo=(list @uwoo)  ~[0w0]
=/  rev=(jar @uwoo @uwoo)  (rev-cfg blocks (sy topo))
~&  [%input-bb-topo (bb-topo blocks)]
::  (1)
::
=/  r2  (mule |.((alias 2 blocks rev topo)))
~&  [%alias-nargs-2 r2]
::  (2)
::
=/  r1  (mule |.((alias 1 blocks rev topo)))
~&  [%alias-nargs-1-ok -.r1]
~&  [%alias-nargs-1 ?:(-.r1 r1 [%crash (flop (scag 3 (flop ;;((list) +.r1))))])]
::  (3)
::
=/  s0=straight  [[%both [%this ~] [%this ~]] 1 blocks]
=/  r3  (mule |.((optimize s0)))
~&  [%optimize-nargs-1-ok -.r3]
0
