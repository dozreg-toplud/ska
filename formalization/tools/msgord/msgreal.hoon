=/  btt=need-ordered  [%both [%this ~] [%this ~]]
=/  big=need-ordered  [%both btt btt]
=/  c=cape  [[| |] [| |]]
=/  e1  (msg-need-ord btt [%this ~] c)
=/  e2  (msg-need-ord big e1 c)
=/  e3  (msg-need-ord [%this ~] e2 c)
~&  [%cycle e1 e2 e3]
=/  a=need-ordered  [%this ~]
=/  b=need-ordered  [%both [%none ~] [%both [[%none ~] [%this ~]] [%this ~]]]
=/  d=need-ordered  [%both [%both [%this ~] [%this ~]] [%this ~]]
~&  [%assoc (msg-need-ord (msg-need-ord a b c) d c) (msg-need-ord a (msg-need-ord b d c) c)]
~&  [%deep (msg-need-ord [[%this ~] [%this ~]] [[%this ~] [%both [%this ~] [%this ~]]] |)]
0
