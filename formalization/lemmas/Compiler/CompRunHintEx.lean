import lemmas.Compiler.CompRunHintClass

/-!
# The run link with kept hints: examples (README Gaps 25)

`sfSnd CODE` is the model of `+sound` on the code table `CODE` (`+sound-far`
at depth `3`); `soundAt_sf`: `SoundAt` of every nomm closed for it.  The
examples are what `!:` emits: the dynamic `%spot` with a constant clue around
a cons, the same in a branch of a `%6`, and two nested spots, each on every
goal with `GInv`, against `runLCH env (sfSnd cod) true msup`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ctx : Noun}

/-- The model of `+sound` on the code table `CODE`. -/
noncomputable def sfSnd (CODE : Noun) : Nomm → NeedOrd → Bool :=
  fun n d => (soundFar (nommOf CODE) 3 n d).getD false

theorem soundAt_sf (h7 : slot? 7 ctx = some compK) {CODE : Noun} (hcode : slot? 52 ctx = some CODE) {nom : Nomm}
    (hc : SfClosed (nommOf CODE) 3 nom) : SoundAt ctx (sfSnd CODE) nom :=
  soundAt_of h7 hcode fun ned => by
    obtain ⟨s, hs⟩ := soundFar_some _ 3 nom hc ned
    simp [sfSnd, hs]

/-- **`!:` around a cons**: `[11 [%spot [1 s]] [[0 2] [1 k]]]`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (s k body : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup)
      (Nomm.n11d 0x746f7073 (Nomm.n1 s) (Nomm.cons (Nomm.n0 2) (Nomm.n1 k)) body) goal region g :=
by
  refine comp_run_hintX h7 hcode env _ E _ rfl msup region (by simp [HintCalls]) ?_ goal g hi
  exact ⟨fun _ => soundAt_sf h7 hcode (by simp [SfClosed, SfNoAx0, sfBells]), by simp [HintSound]⟩

/-- **`!:` in a branch of a `%6`**: `[6 [0 2] [11 [%spot [1 s]] [[0 2] [1 k]]] [1 k]]`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (s k body : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup)
      (Nomm.n6 (Nomm.n0 2) (Nomm.n11d 0x746f7073 (Nomm.n1 s) (Nomm.cons (Nomm.n0 2) (Nomm.n1 k)) body) (Nomm.n1 k))
      goal region g :=
by
  refine comp_run_hintX h7 hcode env _ E _ rfl msup region (by simp [HintCalls]) ?_ goal g hi
  exact ⟨trivial, ⟨fun _ => soundAt_sf h7 hcode (by simp [SfClosed, SfNoAx0, sfBells]), by simp [HintSound]⟩,
    trivial⟩

/-- **Nested spots**: `[11 [%spot [1 s]] [11 [%spot [1 t]] [[0 2] [1 k]]]]`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (s t k body body' : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup)
      (Nomm.n11d 0x746f7073 (Nomm.n1 s)
        (Nomm.n11d 0x746f7073 (Nomm.n1 t) (Nomm.cons (Nomm.n0 2) (Nomm.n1 k)) body') body) goal region g :=
by
  refine comp_run_hintX h7 hcode env _ E _ rfl msup region (by simp [HintCalls]) ?_ goal g hi
  exact ⟨fun _ => soundAt_sf h7 hcode (by simp [SfClosed, SfNoAx0, sfBells]), trivial,
    ⟨fun _ => soundAt_sf h7 hcode (by simp [SfClosed, SfNoAx0, sfBells]), by simp [HintSound]⟩⟩

end Compiler
end Formalization
