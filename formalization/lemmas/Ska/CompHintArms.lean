import lemmas.Ska.CompRunLCM
import lemmas.Ska.FolLoop

/-!
# The arms the hint cases of `+run` use (README Gaps 24)

* `pastIfL snd nex nom region`: `+past-if` (line 5153).  The sure need of
  the product goes to a block of its own past the hint's epilogue, unless its
  lock is small and `+sound` of `nom` holds of its ordered form; `snd` is
  `+sound` (`+sound-far` with the code table and depth `3`), a parameter of
  the run model (`SofModel.lean` has its model, `soundFar`).
* `meanKonst env b k`: `+mean-konst` (line 4627), the constant pushed for a
  deferred `%mean` instead of its arm: `k` when the arm's code entry is pure.
* `Nomm.noHint`: no `%11`, `%12`, `%mean` anywhere.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- `+past-if`. -/
def pastIfL (snd : Nomm → NeedOrd → Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    CM Map (NextL S) :=
  if HoonSet.small nex.laz.sure.lok = true ∧ snd nom (needToOrd nex.laz.sure.ned) = true then
    pure nex else do
  let o ← emit ⟨[], [], Termin.hop nex.th⟩
  setTag o region
  pure ⟨mk Sure.bunt nex.laz.fork ((o, mk nex.laz.sure [] []) :: nex.laz.bond), jmp0 o⟩

/-- `+mean-konst`. -/
def meanKonst (env : CallEnv) (b : Bell) (k : Option Noun) : Option Noun :=
  match k with
  | Option.none => Option.none
  | some n => if env.pure b then some n else Option.none

end Comp

/-- No hint, no scry, no `%mean`. -/
def Nomm.noHint : Nomm → Bool
  | Nomm.cons p q => p.noHint && q.noHint
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q _ => p.noHint && q.noHint
  | Nomm.n3 p => p.noHint
  | Nomm.n4 p => p.noHint
  | Nomm.n5 p q => p.noHint && q.noHint
  | Nomm.n6 p q r => p.noHint && q.noHint && r.noHint
  | Nomm.n7 p q => p.noHint && q.noHint
  | Nomm.n10 _ v q => v.noHint && q.noHint
  | Nomm.n11s _ _ _ => false
  | Nomm.n11d _ _ _ _ => false
  | Nomm.n12 _ _ => false
  | Nomm.mean _ _ _ _ _ => false

end SkaModel
end Formalization
