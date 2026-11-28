Enumeration of `msgOrd` (README Gaps 21.8): `msgpy.py` is `msgOrd` of `lemmas/Ska/ShapeCol.lean`
line for line; `enum1.py K KC` checks `msgAbs`, commutativity and `msg (msg a b) b` on all
shapes with at most K inner nodes and capes with at most KC (`3 3`: 4,588,164 triples, 15 s);
`enum2.py` the cycle and associativity up to two inner nodes; `enum4.py` random associativity up
to three, with and without `split-max`; `msgreal.hoon` the cycle and the associativity witness on
the real `+msg-need-ord` (`tools/hoon/runhoon.sh msgreal.hoon 600`).

The kept join (README Gaps 30): `enumkept.py K KC` is `msgOrdKept` of
`lemmas/Ska/ShapeColKept.lean` over `msgpy.py` and checks `kept_climbs`, `kept_canon` and
`kept_pot` on all canonical shapes (`3 3`: 3,359,889 triples; run it under `heavy.sh 4G`);
`msgkept.hoon` the `decide`s of that file on the real arm (`RUNHOON_LIB=<a worktree at
2a5b618 or later>/desk/lib/nock-compilation.hoon tools/hoon/runhoon.sh msgkept.hoon 600`).
