import lemmas.Compiler.CompMember

/-!
# `+inlined` on a nomm with no call

```hoon
++  inlined
  ~%  %inlined  ..ride  ~
  |=  $:  b=bell
          long-ska=_[=_code =_jets =_calls]:*long-ska
          jets-hot=jets-comp
          cache=comp-cache
      ==
  ^-  [nomm comp-cache]
  =*  inlined-loop  $
  ?^  n=(~(get by inl.cache) b)  [u.n cache]
  =/  hot  |=(c=bell ...)
  =-  [new cache(inl (~(put by inl.cache) b new))]
  ^-  [new=nomm =_cache]
  =/  =nomm  nomm:(~(got by code.long-ska) b)
  ?:  inline-off  [nomm cache]
  |-  ^-  [^nomm comp-cache]
  ?-  nomm  ...  ==
```

What the arm does in general (lines 3298 to 3388 of `nock-compilation.hoon`):
it returns the nomm of `b` with the direct calls that can be inlined
replaced by the callee's body, and memoizes the result in `inl.cache`.  On a
hit in `inl.cache` it returns the memoized nomm and the cache unchanged.  On a
miss it takes the nomm of `b` from `code.long-ska` and walks it with the
trap: every case rebuilds the node from its walked parts, and only the case
`%2` with an `info` may change it, to `[%7 p m]` with `m` the inlined nomm of
the callee `c` (itself through `+inlined`), when the call has no memo key,
`+safe-fol-fol` holds of its formula, `c` is not a hot jet, the SCC of `c`
(`+scc-of`, which extends `sccs.cache`) is `c` alone, `c` does not call
itself and `m` has at most `inline-max` (`48`) nodes.  The walked nomm is then
put into `inl.cache` at `b`.

The case linked here is a pure nomm (`Nomm.pure`: no `%2`, no hint, no
`%12`): the walk is the identity and leaves the cache unchanged
(`inl_trap_pure`), so the gate returns the nomm of the code map and the cache
whose `inl` has that nomm put at `b` (`inl_gate_miss`), or, when `inl.cache`
holds the nomm of `b` already, that nomm and the cache unchanged
(`inl_gate_hit`).  `InlOK` names the two cases and `inl_gate` joins them.

The nouns are cut by `tools/gen/inlined.py`; `inl_body_at` ties them to the
pill and `inlBody_eq` to the slot `inlBody` of `CompMember.lean`.  The flag
`inline-off` is arm `84` of `K`, the constant `|` (`inline_off_at`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The branch cons of the trap of `+inlined`. -/
def inlBCons : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 4087)))))))))))))))))))

/-- The branch `%2` of the trap of `+inlined`. -/
def inlB2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (C (A 1) (A 2)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 247))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 503)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 8183))) (C (A 8) (C (C (A 0) (A 2014)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4063)))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2038))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x1777f) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 0xffeb)) (C (A 0) (A 0x3ffbe))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffbe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 5))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 11)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffeb))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 14)) (C (A 0) (A 0x7ff7))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 55) (C (A 0) (A 0x7ff7))) (C (A 10) (C (C (A 12) (C (A 0) (A 6))) (C (A 0) (A 1023)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0xfff7) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x5ddd5) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5ddc) (C (A 0) (A 8191)))))))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 30)) (C (A 0) (A 0xfff7))) (C (C (C (A 1) (A 7)) (C (C (A 0) (A 126)) (C (A 0) (A 2)))) (C (A 0) (A 0xfff7))))))))))))))))) (C (C (A 0) (A 14)) (C (A 0) (A 0x7ff7)))))))))))))) (C (C (A 0) (A 6)) (C (A 0) (A 0x3ff7)))))))))))))))))))))))))))))

/-- The branch `%3` of the trap of `+inlined`. -/
def inlB3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 3)) (C (A 0) (A 2))) (C (A 0) (A 2039)))))))))))

/-- The branch `%4` of the trap of `+inlined`. -/
def inlB4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 4)) (C (A 0) (A 2))) (C (A 0) (A 2039)))))))))))

/-- The branch `%5` of the trap of `+inlined`. -/
def inlB5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 5)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 4087)))))))))))))))))))

/-- The branch `%6` of the trap of `+inlined`. -/
def inlB6 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 247))) (C (A 0) (A 7)))))))) (C (A 7) (C (C (A 10) (C (C (A 8183) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (A 0) (A 2))))) (C (A 0) (A 8183)))))))))))))))))))))))))))

/-- The branch `%7` of the trap of `+inlined`. -/
def inlB7 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 7)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 4087)))))))))))))))))))

/-- The branch `%10` of the trap of `+inlined`. -/
def inlB10 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 53))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 10)) (C (C (C (A 0) (A 244)) (C (A 0) (A 6))) (C (A 0) (A 2)))) (C (A 0) (A 4087)))))))))))))))))))

/-- The branch `%11` of the trap of `+inlined`. -/
def inlB11 : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 26))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 11)) (C (C (A 0) (A 58)) (C (C (A 0) (A 2)) (C (A 0) (A 119))))) (C (A 0) (A 2039))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 53))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 11)) (C (C (C (A 0) (A 244)) (C (A 0) (A 6))) (C (C (A 0) (A 2)) (C (A 0) (A 247))))) (C (A 0) (A 4087))))))))))))))))))))))

/-- The branch `%12` of the trap of `+inlined`. -/
def inlB12 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 12)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 4087)))))))))))))))))))

/-- The branch `%mean` of the trap of `+inlined` (under a `%toss` hint). -/
def inlBMean : Noun :=
  (C (A 11) (C (C (A 0x73736f74) (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 12)))) (C (A 1) (A 1)))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 2039) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 4087) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x6e61656d)) (C (C (A 0) (A 6)) (C (C (A 0) (A 246)) (C (C (A 0) (A 2)) (C (C (A 0) (A 990)) (C (A 0) (A 991))))))) (C (A 0) (A 4087)))))))))))))))))))))

/-- The trap of `+inlined` over the nomm: the `?-` over its head. -/
def inlTrap : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 3) (C (A 0) (A 12))) (C (A 1) (A 1))))) (C inlBCons (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (C (A 0) (A 6)) (C (A 0) (A 1015))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (C (A 0) (A 6)) (C (A 0) (A 1015))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB2 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB3 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 4)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB4 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB5 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB6 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB7 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB10 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB11 (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 12)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C inlB12 inlBMean))))))))))))))))))))))))))))))))))))

/-- `(~(get by inl.cache) b)`. -/
def inlGet : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 1918))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

/-- `[u.n cache]`. -/
def inlHit : Noun :=
  (C (C (A 0) (A 5)) (C (A 0) (A 119)))

/-- The gate `hot`. -/
def inlHot : Noun :=
  (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fabe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 1014))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 3) (C (A 0) (A 2)))))) (C (A 0) (A 1)))))

/-- `nomm:(~(got by code.long-ska) b)`. -/
def inlGot : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 500))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))

/-- `[new cache(inl (~(put by inl.cache) b new))]`. -/
def inlAfter : Noun :=
  (C (C (A 0) (A 4)) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 222))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 12)))) (C (A 0) (A 2))))))))) (C (A 0) (A 5)))))

/-- The nomm, the test of `inline-off` and the trap. -/
def inlInner : Noun :=
  (C (A 8) (C inlGot (C (A 6) (C (C (A 9) (C (A 84) (C (A 0) (A 63)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 503))) (C (A 8) (C (C (A 1) inlTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))

/-- The branch where `inl.cache` has no nomm of `b`. -/
def inlMiss : Noun :=
  (C (A 8) (C inlHot (C (A 8) (C inlInner inlAfter))))

/-- The gate body of `+inlined`. -/
def inlBodyN : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C inlGet (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C inlMiss inlHit)))))))

/-- `+inlined` in `K`, with its body cut into named parts. -/
theorem inl_body_at : slot? 0x5dde compK
    = some (C (A 7) (C (C (A 8) (C (C (A 1) inlBunt) (C (C (A 1) inlBodyN) (C (A 0) (A 1))))) inlHint)) := by
  kernel_rfl

/-- The slot `inlBody` of `CompMember.lean` is `inlBodyN`. -/
theorem inlBody_eq : inlBody = inlBodyN := by
  have h1 := inl_at
  rw [inl_body_at] at h1
  simp only [Option.some.injEq, Noun.cell.injEq, true_and, and_true] at h1
  exact h1.symm

/-- `inline-off` is arm `84` of `K`: the constant `|`. -/
theorem inline_off_at : slot? 84 compK = some (C (A 1) (A 1)) := by kernel_rfl

/-! ## The trap on a pure nomm -/

theorem nomm_cell : ∀ nm : Nomm, ∃ a b, nm.toNoun = C a b := by
  intro nm; cases nm <;> exact ⟨_, _, rfl⟩

/-- The rest of the core of the trap after the nomm: `[hot [n [battery
[[b long-ska jets-hot cache] K]]]]`.  The trap reads `cache` at axis `1015`. -/
def inlR (HOT N BAT B LONG JH CA KK : Noun) : Noun := C HOT (C N (C BAT (C (C B (C LONG (C JH CA))) KK)))

/-- **The trap of `+inlined` on a pure nomm** is the identity on the nomm and
returns the cache it was given. -/
theorem inl_trap_pure : ∀ nm : Nomm, nm.pure = true → ∀ (HOT N BAT B LONG JH CA KK : Noun),
    nock (C inlTrap (C nm.toNoun (inlR HOT N BAT B LONG JH CA KK))) inlTrap = some (C nm.toNoun CA) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    obtain ⟨a, b, hab⟩ := nomm_cell p
    rw [hab] at hp
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq ⊢
    simp [nock_exec, Nomm.toNoun, hab, inlBCons, hp, hq]
  | n0 ax =>
    intro hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR
    simp [nock_exec, Nomm.toNoun]
  | n1 k =>
    intro hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR
    simp [nock_exec, Nomm.toNoun]
  | n2 p q info => intro hpu; simp [Nomm.pure] at hpu
  | n3 p ihp =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure] at hpu
    have hp := ihp hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp ⊢
    simp [nock_exec, Nomm.toNoun, inlB3, hp]
  | n4 p ihp =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure] at hpu
    have hp := ihp hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp ⊢
    simp [nock_exec, Nomm.toNoun, inlB4, hp]
  | n5 p q ihp ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq ⊢
    simp [nock_exec, Nomm.toNoun, inlB5, hp, hq]
  | n6 p q r ihp ihq ihr =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.1.2 HOT N BAT B LONG JH CA KK
    have hr := ihr hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq hr ⊢
    simp [nock_exec, Nomm.toNoun, inlB6, hp, hq, hr]
  | n7 p q ihp ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq ⊢
    simp [nock_exec, Nomm.toNoun, inlB7, hp, hq]
  | n10 a v q ihv ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    have hv := ihv hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hv hq ⊢
    simp [nock_exec, Nomm.toNoun, inlB10, hv, hq]
  | n11s _ _ _ => intro hpu; simp [Nomm.pure] at hpu
  | n11d _ _ _ _ => intro hpu; simp [Nomm.pure] at hpu
  | n12 _ _ => intro hpu; simp [Nomm.pure] at hpu
  | mean _ _ _ _ _ => intro hpu; simp [Nomm.pure] at hpu

/-! ## The gate -/

/-- **`+inlined` on a miss in `inl.cache`, for a pure nomm**: the nomm of `b`
in `code.long-ska` (`+got:by`, `hgot`, `hv`), walked to itself, and the cache
whose `inl` has it put at `b` (`hput`). -/
theorem inl_gate_miss (B CODE LSR JH C1 C2 C3 INL SURE V INL' : Noun) (nm : Nomm) (hpu : nm.pure = true)
    (hinl : getF mugF B INL = some (A 0))
    (hgot : getF mugF B CODE = some (C (A 0) V)) (hv : slot? 2 V = some nm.toNoun)
    (hput : putF mugF B nm.toNoun INL = some INL') :
    nock (C inlBody (C (C B (C (C CODE LSR) (C JH (cacheN C1 C2 C3 INL SURE)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 INL' SURE)) := by
  have hL := compK_layer2
  have hoff := inline_off_at
  have hg := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ B INL (A 0) hinl
  have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B CODE V hgot
  have hp := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 B nm.toNoun INL INL' hput
  obtain ⟨v1, v2, rfl⟩ : ∃ a b, V = C a b := by
    cases V with
    | atom _ => simp [nock_exec] at hv
    | cell a b => exact ⟨a, b, rfl⟩
  simp only [nock_exec, Option.some.injEq] at hv
  subst hv
  have ht := fun HOT => inl_trap_pure nm hpu HOT (A 0) inlBodyN B (C CODE LSR) JH (cacheN C1 C2 C3 INL SURE) compK
  rw [inlBody_eq]
  conv => { lhs; arg 2; unfold inlBodyN }
  unfold cacheN inlR at *
  generalize compK = KC at hL hoff ht ⊢
  simp [nock_exec, hL, inlGet, inlMiss, inlInner, inlGot, inlAfter, inlHot, by.arm_at, by_arm, by.get.arm_at,
    get_arm, hg, by.got.arm_at, got_arm, hgt, hoff, ht, by.put.arm_at, put_arm, hp]

/-- **`+inlined` on a hit in `inl.cache`**: the memoized nomm and the cache
unchanged. -/
theorem inl_gate_hit (B LONG JH C1 C2 C3 INL SURE N : Noun)
    (hinl : getF mugF B INL = some (C (A 0) N)) :
    nock (C inlBody (C (C B (C LONG (C JH (cacheN C1 C2 C3 INL SURE)))) compK)) inlBody
      = some (C N (cacheN C1 C2 C3 INL SURE)) := by
  have hL := compK_layer2
  have hg := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ B INL _ hinl
  rw [inlBody_eq]
  conv => { lhs; arg 2; unfold inlBodyN }
  unfold cacheN at *
  generalize compK = KC at hL ⊢
  simp [nock_exec, hL, inlGet, inlHit, by.arm_at, by_arm, by.get.arm_at, get_arm, hg]

/-- **What `+inlined` finds for `b`** with the pure nomm `nm`: either
`inl.cache` holds `nm` at `b` and stays (`INL' = INL`), or it has nothing at
`b`, `code.long-ska` has a value at `b` whose head is `nm`, and `INL'` is
`inl.cache` with `nm` put at `b`.  A statement on the nouns of the maps
only. -/
def InlOK (B CODE INL : Noun) (nm : Nomm) (INL' : Noun) : Prop :=
  (getF mugF B INL = some (C (A 0) nm.toNoun) ∧ INL' = INL) ∨
  (getF mugF B INL = some (A 0) ∧ (∃ V, getF mugF B CODE = some (C (A 0) V) ∧ slot? 2 V = some nm.toNoun) ∧
    putF mugF B nm.toNoun INL = some INL')

/-- **`+inlined` on a pure nomm**: under `InlOK`, the gate returns `nm` and
the cache with `inl` replaced by `INL'`. -/
theorem inl_gate (B CODE LSR JH C1 C2 C3 INL SURE INL' : Noun) (nm : Nomm) (hpu : nm.pure = true)
    (hok : InlOK B CODE INL nm INL') :
    nock (C inlBody (C (C B (C (C CODE LSR) (C JH (cacheN C1 C2 C3 INL SURE)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 INL' SURE)) := by
  rcases hok with ⟨h, e⟩ | ⟨h, ⟨V, hg, hv⟩, hp⟩
  · rw [e]; exact inl_gate_hit B (C CODE LSR) JH C1 C2 C3 INL SURE nm.toNoun h
  · exact inl_gate_miss B CODE LSR JH C1 C2 C3 INL SURE V INL' nm hpu h hg hv hp

end Compiler
end Formalization
