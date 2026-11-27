:: The pass loop of +analyze does not end (README Gaps 16, track F, 2026-11-27): R (EvFrozen) and
:: FinPushes are false of this compiler, so CgHalts is.  Case de3-24-44-111 of family d of
:: passmeasure-take.py (batch3, td-03.hoon case 0, there called by +ska-callgraph on [[& |] [B 0]]).  Here
:: one %full poke, subject 0 (known), formula [7 [[1 B] [4 [1 0]]] [9 4 [0 1]]]: R (arm 4 of the core
:: [B sam], B = [R f_5 .. f_11], sam the increment of a constant, unknown)
:: has a shift register of 3 slots; each f_t (tag t, 5..11) a register of 4.  Sites of R in order:
::   (every kid is [[[1 t] [p 7]] K]: a tag, a formula slot p, a constant)
::   k   f_5 with p = [R.0 |], from pass 3 on the constant drained p = | (kid [[[1 5] [| 7]] K]);
::   two chains of relays, each relay f_t with p = X.1, slot 1 of the register in the
::   product of the site before it, taken WHOLE (cape &, a direct call, in less-code): tags 6, 7 from
::   k's target, tags 8, 9, 10, 11 from k's target;
::   a   f_5 with p = [Z7.1 |] (Z7: end of the chain of 2), b   f_5 with p = [| Z11.1] (end of 4).
:: A relay member with p known needs p (less-code) so it does not cover the drained kid, and the drained
:: member keeps p in indi so it does not cover the known kid: every drain or restart of its input pushes
:: the other one afresh (culled the pass before).  The two chains bring a's and b's sources fresh at
:: different passes, so the members [V |] and [| V] of f_5 are culled and pushed again in turn, and each
:: takes over k by %rec: k's target is [V |] at pass 7, [| V] at 8..11, [V |] at 12..19, [| V] at
:: 20..23, [V |] at 24, and so on.  With the library of passmeasure.py: 12,707 root passes in 900 s,
:: the %st hash (the stack above the root with every datum) periodic with period 18 from pass 7 on
:: (24 values), each period 4 takeovers at k and 2 pushes of each f_5 member after a cull; this poke:
:: 33,135 passes of R's loop in 300 s, the same 24 values, period 18 from pass 7.  Plain library: no
:: answer in 600 s, here and on the direct call (runhoon.sh takecycle.hoon 600: %poke-1, then nothing).
~&  %poke-1
=^  p  ..poke  (poke [%full 0 [7 [[1 [[6 [[3 [0 3]] [[1 [7 [[0 1] [[0 1] [0 1]]]]] [8 [[2 [[0 1] [0 4]]] [8 [[2 [[[[1 [1 5]] [[[0 10] [0 7]] [0 4]]] [0 3]] [0 26]]] [8 [[2 [[[[1 [1 6]] [[0 22] [0 12]]] [0 7]] [0 118]]] [8 [[2 [[[[1 [1 7]] [[0 22] [0 28]]] [0 15]] [0 494]]] [8 [[2 [[[[1 [1 8]] [[0 118] [0 60]]] [0 31]] [0 2.014]]] [8 [[2 [[[[1 [1 9]] [[0 22] [0 124]]] [0 63]] [0 8.126]]] [8 [[2 [[[[1 [1 10]] [[0 22] [0 252]]] [0 127]] [0 32.638]]] [8 [[2 [[[[1 [1 11]] [[0 22] [0 508]]] [0 255]] [0 65.407]]] [8 [[2 [[[[1 [1 5]] [[[0 502] [0 1.023]] [0 1.020]]] [0 511]] [0 4.090]]] [8 [[2 [[[[1 [1 5]] [[[0 2.047] [0 54]] [0 2.044]]] [0 1.023]] [0 8.186]]] [[1 7] [[0 16.374] [[0 16.375] [0 4.095]]]]]]]]]]]]]]]]]]]]]]]]]]] [[6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 26]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]] [[6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 54]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]] [[6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 110]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]] [[6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 222]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]] [[6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 446]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]] [[6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 894]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]] [6 [[3 [0 7]] [[[[2 [[0 1] [0 4]]] [2 [[0 1] [0 10]]]] [1 [[0 1] [[0 1] [[0 1] [0 1]]]]]] [8 [[2 [[0 1] [0 895]]] [8 [[2 [[0 7] [0 28]]] [[[2 [[0 7] [0 28]]] [2 [[0 7] [0 58]]]] [[0 54] [[0 110] [[0 111] [0 31]]]]]]]]]]]]]]]]]]]] [4 [1 0]]] [9 [4 [0 1]]]]])
~&  [%poke-1-returned ?=(^ p)]
0
