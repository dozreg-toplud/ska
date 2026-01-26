/-  *noir
::
=/  pin1
  ;;  spring:source
  %-  cue
  0w1.nhS-8.7r1TZ.geZ1T.-U7vM.t-o5K.NOSMI.DT3Ud.gYMgT.tMqsg.Tu435.URPdg.Z5e7L.
  21UYr.5URtK.kfw4d.P13tT.1FN3t.Ugf7z.oL6ID.T3x-U.snzmK.zIMgR.HEXfe.6Je33.sMgTu.
  42RQs.ND3Tx.0HcpM.YMgTu.42RQu.ea7e3.3tT1T.x0HQW.xPwMT.c4dTs.7u42R.Quea7.JgpMo.
  rKUeY.85ssk.fl66X.k6s66.McMTc.4dTs7.u42JZ.33tc7.l66Xk.6s66M.cMTw4.dP13t.T1Tx0.
  YudyY.qJLVM.frJKX.KXTrB.E1QMu.TrtTr.KUS0u.XF0Xk.7JSTt.SXKZS.VS0uT.rtTtM.Q0ZKS.
  UQ1TN.wtT1T.VgeY8.7JSXC.wfrJK.ZPU2I.Pdjoo.aS45p
::
=/  pin2
  ;;  spring:source
  (cue 0w2.KzJI7.uwJSe.mqWeQ.MtG2I.Pdjoo.aS45p)
::
=>
  |%
  ++  what-where
    |=  pin=spring:source
    ^-  (jar @ @)
    =|  j=(jar @ @)
    =/  rev  1
    |-  ^+  j
    ?~  pin  j
    =.  j
      %+  roll  n.pin
      |=  [ax=@ acc=_j]
      (~(add ja acc) rev ax)
    ::
    =.  j  $(pin l.pin, rev (peg rev 2))
    $(pin r.pin, rev (peg rev 3))
  ::
  ++  deep-tree
    |$  [node]
    $@  ~
    [depf=$~(1 @) n=node l=(deep-tree node) r=(deep-tree node)]
  ::
  ++  sink  (deep-tree (list @))
  :: ++  invert
  ::   =|  out=sink
  ::   =/  rev  1
  ::   |=  pin=spring:source
  ::   ^-  sink
  ::   ?~  pin  out
  ::   =.  out
  ::     %+  roll  n.pin
  ::     |=  [ax=@ acc=_out]
  ::     (push-sink rev ax acc)
  ::   ::
  ::   =.  out  $(pin l.pin, rev (peg rev 2))
  ::   $(pin r.pin, rev (peg rev 3))
  ::
  ++  ward
    |=  [a=@ b=@]
    ^-  [@ @]
    ?:  =(1 a)  [1 b]
    ?:  =(1 b)  [a 1]
    ?.  =((cap a) (cap b))  [a b]
    $(a (mas a), b (mas b))
  ::
  :: ++  push-sink
  ::   |=  [where=@ ax=@ sik=sink]
  ::   ^-  sink
  ::   ?~  sik  [ax ~[1] ~ ~]
  ::   =/  [ax-rest depf-rest]  (ward ax depf.sik)
  ::   ?:  =(1 depf-rest)  sik(n [ax-rest n.sik])
  ::   !!
  ::


  :: ++  push-sink
  ::   |=  [where=@ ax=@ sik=sink]
  ::   ^-  sink
  ::   ?:  =(ax 1)
  ::     ?~  sik  [~[where] [1 ~] [1 ~]]
  ::     sik(n [where n.sik])
  ::   =/  [n=(list @) l=(pair @ sink) r=(pair @ sink)]  ?~(sik [~ [1 ~] [1 ~]] sik)
  ::   ?-    (cap ax)
  ::       %2
  ::     =.  l  (push-deep where (mas ax) l)
  ::     ?:  &(=(~ n) =(~ q.l) =(~ q.r))  ~
  ::     [n l r]
  ::   ::
  ::       %3
  ::     =.  r  (push-deep where (mas ax) r)
  ::     ?:  &(=(~ n) =(~ q.l) =(~ q.r))  ~
  ::     [n l r]
  ::   ==
  :: ::
  :: ++  push-deep
  ::   |=  [where=@ ax=@ depf=@ sik=sink]
  ::   ^-  [@ sink]
  ::   =/  [ax-rest=@ depf-rest=@]  (ward ax depf)
  ::   ?:  =(1 depf-rest)
  ::     :-  depf
  ::     ?~  sik  [~[ax-rest] [1 ~] [1 ~]]
  ::     sik(n [ax-rest n.sik])
  ::   =/  depf-rem  (hub depf-rest depf)
  ::   =/  old=[@ sink]  [(mas depf-rem) sik]
  ::   :-  depf-rest
  ::   :-  ~[ax-rest]
  ::   ^-  [[@ sink] [@ sink]]
  ::   ?-  (cap depf-rem)
  ::     %2  [old [1 ~]]
  ::     %3  [[1 ~] old]
  ::   ==
  :: ++  push-sink
  ::   |=  where=@ ax=@ sik=sink
  --
:: :-  %say  |=  *  :-  %tang
:-  %say  |=  *  :-  %noun
::
::
~&  (measure pin1)
:: %+  turn
::   %+  sort  ~(tap by (what-where pin1))
::   |=([a=[w=@ *] b=[w=@ *]] (gth w.a w.b))
:: |=  [where=@ what=(list @)]
:: ^-  tank
:: :+  %rose  [": " ~ ~]
:: :-  (scot %ud where)
:: :_  ~
:: :+  %rose  [" " ~ ~]
:: (turn (sort what lth) (cury scot %ud))
:: ^-  (tree (list @))
:: (invert pin2)
pin2