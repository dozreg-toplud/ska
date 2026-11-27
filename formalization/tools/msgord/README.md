Enumeration of `msgOrd` (README Gaps 21.8): `msgpy.py` is `msgOrd` of `lemmas/Ska/ShapeCol.lean`
line for line; `enum1.py K KC` checks `msgAbs`, commutativity and `msg (msg a b) b` on all
shapes with at most K inner nodes and capes with at most KC (`3 3`: 4,588,164 triples, 15 s);
`enum2.py` the cycle and associativity up to two inner nodes; `enum4.py` random associativity up
to three, with and without `split-max`; `msgreal.hoon` the cycle and the associativity witness on
the real `+msg-need-ord` (`tools/hoon/runhoon.sh msgreal.hoon 600`).
