import lemmas.Compiler.FolLoopStep
import lemmas.Iter

/-!
# `Ana.folStep` is monotone in its calls

One level of the model of `fol-loop` is monotone in the order `Below?` of
`Iter.lean` ("whatever the first returns, the second returns") in both of its
calls: the trap's calls to itself `go` and the loop `resolve` `res`
(`folStep_mono`, through `callStep_mono` and `meanArm_mono`).  For example, if
`go` returns `r` on the operand `[a b]` of `[%4 a b]`, so does every `go'`
above it, and the step returns the same `[%4 ...]` for both.

This is what the induction on the depth of the pill's calls needs, in both
directions, so that the case theorems need no second version for an order:

1. From the pill: at depth `k + 1`, `go` is the decoded run of the trap at
   depth `k` (exact by the hypothesis of the induction, so `GoIs` holds of it
   with `iterN k` in place of `nock`), and the model's `folLoop m` lies above it
   from some `m` on, so by `folStep_mono` the step of the model returns what the
   step on the decoded runs returns.
2. From the model: once every return of the pill decodes (direction 1), the
   decoded run of the pill is a `go` with `GoIs` for `nock`, and `folLoop n`
   lies below it by induction on `n`, so `fol_loop_step_all` and
   `folStep_mono` give what the pill returns.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel SkaModel.Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- `go` is below `go'` on every argument. -/
def GoBelow (go go' : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gen, Below? (go fol sub seat mk bc df gen) (go' fol sub seat mk bc df gen)

/-- `res` is below `res'` on every argument. -/
def ResBelow (res res' : ResGo M R) : Prop := ∀ i gen, Below? (res i gen) (res' i gen)

theorem callStep_mono {res res' : ResGo M R} {go go' : FolGoS M R} (hres : ResBelow res res')
    (hgo : GoBelow go go') (seat mk : Option Noun) (bc df : Bool) (s f : FolOut) (gen : GenS M R) :
    Below? (Ana.callStep res go seat mk bc df s f gen) (Ana.callStep res' go' seat mk bc df s f gen) := by
  unfold Ana.callStep
  split
  · exact Below?.refl _
  · split
    · split
      · exact Below?.bind (hgo _ _ _ _ _ _ _) fun _ => Below?.refl _
      · exact Below?.bind (hres _ _) fun _ => Below?.refl _
    · exact Below?.refl _

omit [Treap M] in
theorem meanArm_mono {go go' : FolGoS M R} (hgo : GoBelow go go') (tag : Nat) (h : FolOut)
    (seat mk : Option Noun) (bc : Bool) (gen : GenS M R) :
    Below? (Ana.meanArm go tag h seat mk bc gen) (Ana.meanArm go' tag h seat mk bc gen) := by
  unfold Ana.meanArm
  split
  · exact Below?.refl _
  · refine Below?.bind (Below?.refl _) fun bat => ?_
    split
    · exact Below?.bind (hgo _ _ _ _ _ _ _) fun _ => Below?.refl _
    · exact Below?.refl _

/-- One level of the model is monotone in `go` and `res`. -/
theorem folStep_mono (env : Env R) {res res' : ResGo M R} {go go' : FolGoS M R}
    (hres : ResBelow res res') (hgo : GoBelow go go') (fol : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS M R) :
    Below? (Ana.folStep env res go fol sub seat mk bc df gen)
      (Ana.folStep env res' go' fol sub seat mk bc df gen) := by
  unfold Ana.folStep
  split <;> (try dsimp only) <;>
    repeat (first
      | exact Below?.refl _
      | exact hgo _ _ _ _ _ _ _
      | exact callStep_mono hres hgo _ _ _ _ _ _ _
      | (refine Below?.bind (meanArm_mono hgo _ _ _ _ _ _) fun _ => ?_)
      | (refine Below?.bind (hgo _ _ _ _ _ _ _) fun _ => ?_)
      | (refine Below?.bind (Below?.refl _) fun _ => ?_)
      | split)


open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-- Every return of the trap's battery on its subject is the noun of a result
of `fol-loop`: the shape fact that the direction from the pill gives. -/
def FolDecodes (regsNoun : R → Noun) (rest : Noun) : Prop :=
  ∀ fol sub seat mk bc df gen x,
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery = some x →
      ∃ r, x = folOutNoun regsNoun r

/-- `go` where it returns, else the decoded run of the pill. -/
noncomputable def goPatch (regsNoun : R → Noun) (rest : Noun) (go : FolGoS FinMap R) :
    FolGoS FinMap R := fun fol sub seat mk bc df gen => by
  classical
  exact match go fol sub seat mk bc df gen with
  | some r => some r
  | none =>
    if h : ∃ r, nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
        = some (folOutNoun regsNoun r) then some (Classical.choose h) else none

theorem goPatch_below (regsNoun : R → Noun) (rest : Noun) (go : FolGoS FinMap R) :
    GoBelow go (goPatch regsNoun rest go) := by
  intro fol sub seat mk bc df gen r h
  simp [goPatch, h]

/-- If the pill returns what `go` returns and every return of the pill decodes,
the patched `go` is exact. -/
theorem goIs_patch (regsNoun : R → Noun) (rest : Noun) (go : FolGoS FinMap R)
    (hdec : FolDecodes regsNoun rest)
    (hle : ∀ fol sub seat mk bc df gen r, go fol sub seat mk bc df gen = some r →
      nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
        = some (folOutNoun regsNoun r)) :
    GoIs regsNoun rest (goPatch regsNoun rest go) := by
  intro fol sub seat mk bc df gen
  cases e : go fol sub seat mk bc df gen with
  | some r => simp [goPatch, e, hle _ _ _ _ _ _ _ r e]
  | none =>
    by_cases h : ∃ r, nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
        = some (folOutNoun regsNoun r)
    · simp only [goPatch, e, dif_pos h, Option.map_some]
      exact Classical.choose_spec h
    · simp only [goPatch, e, dif_neg h, Option.map_none]
      cases ex : nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery with
      | none => rfl
      | some x =>
        obtain ⟨r, rfl⟩ := hdec _ _ _ _ _ _ _ x ex
        exact absurd ⟨r, ex⟩ h

/-- What the model of `fol-loop` returns at any fuel, the pill's trap returns,
given that every return of the trap decodes (`FolDecodes`), that at every fuel
the model's `resolve` is below some `resP` that the pill's loop `resolve`
computes (`ResIs`), `+register-fast` as `env` says, `+soft-spot` the model
`softSpotF`, and `ana` at axis `511` of the rest. -/
theorem fol_loop_le (regsNoun : R → Noun) (env : Env R) (hsoft : env.softSpot = softSpotF)
    (memoF : Memo FinMap) (rest : Noun) (hana : slot? 511 rest = some ana)
    (hreg : RegisterFastIs regsNoun env) (hdec : FolDecodes regsNoun rest)
    (hres : ∀ n, ∃ resP, ResIs regsNoun rest resP ∧ ResBelow (Ana.resolveR env memoF n) resP) :
    ∀ n fol sub seat mk bc df gen r, Ana.folLoop env memoF n fol sub seat mk bc df gen = some r →
      nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
        = some (folOutNoun regsNoun r) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ r h; simp [Ana.folLoop] at h
  | succ n ih =>
    intro fol sub seat mk bc df gen r h
    obtain ⟨resP, hrP, hrB⟩ := hres n
    have hgo := goIs_patch regsNoun rest (Ana.folLoop env memoF n) hdec ih
    have hm := folStep_mono env hrB (goPatch_below regsNoun rest (Ana.folLoop env memoF n))
      fol sub seat mk bc df gen r (by unfold Ana.folLoop at h; exact h)
    rw [fol_loop_step_all' regsNoun env hsoft resP _ rest hgo hana hreg hrP, hm]
    rfl

end Compiler
end Formalization
