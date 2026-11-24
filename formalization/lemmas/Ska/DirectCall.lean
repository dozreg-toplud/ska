import lemmas.Ska.Analysis

/-!
# Which formulas are called directly

Item 3 of the termination argument in `AnaEnds.lean` rests on the claim that
the formulas called directly from a root are finitely many.  It rests on two
facts about socks: the first is proved here, the second was proved
before.

1. `callStep_res_cape`: a `%2` calls `res` (a direct call) only when the
   product sock of its formula part is `&+[fa fb]`, a cape exactly `&`; on
   any other sock `callStep` does not depend on `res`.  For example a
   formula part whose sock is `[[& &] [fa fb]]` makes an indirect call.
2. `knit_ne_yes` (of `FolLoopFacts.lean`): `+knit:so` never makes the cape
   `&`, as `+con:ca` normalizes `[| |]` to `|` but leaves `[& &]` alone.  For example the knit
   of `&+1` and `&+2` is `[[& &] [1 2]]`, not `&+[1 2]`.

So a formula consed at run time is called indirectly.  Not proved: the claim
itself, that the data of the socks with cape exactly `&` that reach a `%2`
lie in a finite set fixed by the root (the parts of the root's subject and
formula, the constants of formulas, the memo's products); it needs every
other arm that makes a sock (`+pull:so`, `+darn:so`, `+patch-prod`,
`+double-int`, `+msg-anno`) followed in the same way.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **A direct call needs a formula sock whose cape is exactly `&`**: when the
product sock of the formula part of a `%2` is not `&+[fa fb]` for some cell,
`callStep` does not depend on `res`. -/
theorem callStep_res_cape {res1 res2 : ResGo M R} {go : FolGoS M R} {seat mk : Option Noun} {bc df : Bool}
    {s f : FolOut} (hf : ∀ fa fb, f.prod.sock ≠ Sock.mk Cape.yes (C fa fb)) (gen : GenS M R) :
    callStep res1 go seat mk bc df s f gen = callStep res2 go seat mk bc df s f gen := by
  unfold callStep
  split
  · rfl
  · split
    · rename_i fa fb heq
      exact absurd heq (hf fa fb)
    · rfl

end Ana

end SkaModel
end Formalization
