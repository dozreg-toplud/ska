:: point (b) of README Gaps 16 is false: an identity that +cull drops is pushed again.
:: R (arm 4 of the core [[R 0] sam], sam unknown: the increment of a constant) is a recursive
:: function whose product [P Q] is two shift registers: P = [a x x x], Q = [x x x x x x]
:: (a = 7, x = [0 1]); each run shifts both left with an unknown at the end, so P and Q lose
:: their last known slot one per pass.  Site Y calls f on [P K]; site X calls f on
:: [[a Q.1 Q.2 Q.3] K].  f runs the formulas at the axes 22 and 23 of its subject (P.14, P.15:
:: inlined when known, indirect when not) and calls R back, so every identity of f is a member.
:: Y's subject is s = [[a x x |] K] at run 3 only; X's is s at run 6 only.  In between nobody
:: calls s, so +cull drops it (end of pass 3), and at pass 5 X pushes it again: the members of
:: formula f on the stack do not pass +hit-test at s (the one at [a x x x] needs P.15, the ones
:: at [a x | |] and [a | | |] made the calls at 22 and 23 indirect: their indi says s knows more).
:: The second poke has four sites (registers of 3, 6, 9, 12): s is pushed four times.
:: The third poke has ONE site Z calling f, on [[a G.y1 G.y2 G.y3] K], G the product of g at
:: site Y1, whose subject [[a Pr.1] K] loses Pr.1 at pass 9.  g needs its subject's x (it runs
:: it, inlined), so Y1 then pushes a fresh g whose shift register restarts at [b x x x]: Z's
:: subject goes back up from s = [a x x |] to t = [a x x x], and Z pushes t again, then s again
:: (2026-11-27: two identities each pushed twice by the one site, 12 passes).  So a call site's
:: subject does not only fall, and a (site, subject) pair can push more than once.
:: The trace of the instrumented poke 3 (pass numbers of R's loop; f(t), f(s) the identities
:: of f at t and s, g(u1), g(u2) those of g):
::   pass 1  %pm-new f(t) 1.039.111.523     pass 2  %pm-new f(s) 2.111.097.607, %pm-cull f(t)
::   pass 9  %pm-new g(u2) 430.631.694, %pm-new f(t) 1.039.111.523 (again), %pm-cull f(s) g(u1)
::   pass 10 %pm-new f(s) 2.111.097.607 (again), %pm-cull f(t)        pass 12 ends
:: Poke 1: %pm-new 490.975.898 at pass 2, %pm-cull of it at pass 3, %pm-new 490.975.898 at
:: pass 5, %pm-cull at pass 6, 8 passes.  Poke 2: 887.246.800 pushed at passes 2, 5, 8, 11.
::
:: Run with the instrumented library of passmeasure.py:
::   RUNHOON_LIB=OUT/lib.hoon runhoon.sh repush.hoon 600
:: and look for a %pm-new whose mug an earlier %pm-cull printed (2026-11-27: the first poke
:: pushes mug 590.545.063 at passes 2 and 5, 8 passes; the second pushes one identity 4 times,
:: 14 passes).  On the plain library both pokes return.
::
=/  f1=*  [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]
~&  %poke-1
=^  p  ..poke  (poke [%full 0 [7 [[[1 [[6 [[3 [0 3]] [[1 [[7 [[0 1] [[0 1] [0 1]]]] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [0 1]]]]]]]] [8 [[9 [4 [0 1]]] [7 [[[[2 [[[0 4] [0 3]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]] [2 [[[[1 7] [[0 10] [[0 22] [0 46]]]] [0 3]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]]] [0 1]] [[[0 24] [[0 102] [[0 103] [0 15]]]] [[0 54] [[0 110] [[0 222] [[0 446] [[0 447] [0 15]]]]]]]]]]]]]] 0]] [4 [1 0]]] [9 [4 [0 1]]]]]])
~&  [%poke-1-returned ?=(^ p)]
~&  %poke-2
=^  q  ..poke  (poke [%full 0 [7 [[[1 [[6 [[3 [0 3]] [[1 [[[0 1] [[0 1] [0 1]]] [[[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [0 1]]]]]] [[[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [0 1]]]]]]]]] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [0 1]]]]]]]]]]]]]]]] [8 [[9 [4 [0 1]]] [7 [[[[2 [[[[1 7] [[0 8] [[0 18] [0 19]]]] [0 3]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]] [[2 [[[[1 7] [[0 20] [[0 42] [0 86]]]] [0 3]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]] [[2 [[[[1 7] [[0 44] [[0 90] [0 182]]]] [0 3]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]] [2 [[[[1 7] [[0 46] [[0 94] [0 190]]]] [0 3]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]]]]] [0 1]] [[[0 50] [[0 51] [0 15]]] [[[0 106] [[0 214] [[0 430] [[0 862] [[0 863] [0 15]]]]]] [[[0 218] [[0 438] [[0 878] [[0 1.758] [[0 3.518] [[0 7.038] [[0 14.078] [[0 14.079] [0 15]]]]]]]]] [[0 222] [[0 446] [[0 894] [[0 1.790] [[0 3.582] [[0 7.166] [[0 14.334] [[0 28.670] [[0 57.342] [[0 114.686] [[0 114.687] [0 15]]]]]]]]]]]]]]]]]]]]]] 0]] [4 [1 0]]] [9 [4 [0 1]]]]]])
~&  [%poke-2-returned ?=(^ q)]
~&  %poke-3
=^  r  ..poke  (poke [%full 0 [7 [[[1 [[6 [[3 [0 3]] [[1 [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [[0 1] [0 1]]]]]]]]] [8 [[9 [4 [0 1]]] [8 [[2 [[[[1 7] [0 4]] [0 3]] [1 [6 [[3 [0 7]] [[7 [[2 [[0 1] [0 5]]] [1 [9 [[0 1] [[0 1] [0 1]]]]]]] [8 [[2 [[0 1] [0 26]]] [7 [[[9 [4 [0 7]]] [0 1]] [[0 12] [[0 54] [[0 55] [0 31]]]]]]]]]]]]]] [8 [[2 [[[[1 7] [[0 10] [[0 22] [0 23]]]] [0 7]] [1 [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]] [[0 58] [[0 118] [[0 238] [[0 478] [[0 958] [[0 1.918] [[0 1.919] [0 31]]]]]]]]]]]]]]]]] [[6 [[3 [0 7]] [[7 [[2 [[0 1] [0 5]]] [1 [9 [[0 1] [[0 1] [0 1]]]]]]] [8 [[2 [[0 1] [0 26]]] [7 [[[9 [4 [0 7]]] [0 1]] [[0 12] [[0 54] [[0 55] [0 31]]]]]]]]]]] [[2 [[0 1] [0 22]]] [[2 [[0 1] [0 23]]] [9 [4 [0 3]]]]]]]] [4 [1 0]]] [9 [4 [0 1]]]]]])
~&  [%poke-3-returned ?=(^ r)]
0
