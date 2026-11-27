import lemmas.Ska.RawInvFragX
import lemmas.Ska.RawInvTopX
import lemmas.Ska.CompFragX

/-!
# Raw `+comp` output on `FragX`: the run-level invariant

README Gaps 14, track D, step 2 of the class `FragX` (a `%6` anywhere, no
calls).  The run-level invariant over `runL`, stated for the fork-free
goals `CGoal.toL goal` that the cases of `FragX` give their sub-runs.

* `lazK o laz`: the kills of a lazy need entered at `o`: each entry of the
  lazy tree (`(o, laz) :: entries laz`) first defines the registers of its
  sure need.  What `optIn_toStraight_prep` asks to be live at nothing.
* **`RawIHX X nm`**: every run of `runL nm` for a fork-free goal from a
  state with `SIP X (upRk g0.blocks) g0.bo` (blocks that hop up as `%6`
  makes them) keeps that invariant in the end state's rank, and for every
  `K` that vanishes from `g0.bo` on leaves live at its entry, with the
  kills `K` and those of its result's lazy tree, only what its goal's
  continuation needs beyond the goal with the kills `K` (`GLiveK`).  Under
  `%done` nothing is live there, the hypothesis `hl` of
  `optIn_toStraight_prep`.
* The cases, whole cases of `FragX` at a time: `rawX_frag` (`run_rawUK`
  and `runL_frag`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X]

/-- **The kills of a lazy need entered at `o`**: each entry of its lazy
tree first defines the registers of its sure need. -/
def lazK (o : Nat) (laz : Lazy S) (x r : Nat) : Prop :=
  ∃ e ∈ (o, laz) :: entries laz, e.1 = x ∧ NMem e.2.sure.ned r

theorem lazK_ofSure {o : Nat} {s : Sure S} {x r : Nat} : lazK o (ofSure s) x r ↔ x = o ∧ NMem s.ned r := by
  unfold lazK
  rw [entries_ofSure]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    rw [List.mem_singleton] at he
    subst he
    exact ⟨h1.symm, h2⟩
  · rintro ⟨rfl, h2⟩
    exact ⟨_, List.mem_singleton_self _, rfl, h2⟩

/-- **The run-level invariant on `FragX`.** -/
def RawIHX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (X : Map Blob → Prop)
    (nm : Nomm) : Prop :=
  ∀ (goal : CGoal S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S) (K : Nat → Nat → Prop),
    KVan K g0.bo → SIP X (upRk g0.blocks) g0.bo g0 → GoalIn g0.re goal → GDist goal → GJ g0.bo goal →
    GArgs goal → (∀ r, Defd g0.blocks r → ¬ GMem goal r) →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) →
    SIP X (upRk g1.blocks) g1.bo g1 ∧
      ∀ r, LiveK g1.blocks (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
        GLiveK g0.blocks K goal r

/-- **The case `frag`**: a nomm of the first fragment, by `run_rawUK`. -/
theorem rawX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : RawIHX S Map X nm := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hfd hr
  rw [runL_frag (hf goal) region g0] at hr
  obtain ⟨⟨nex', g1'⟩, hr', e⟩ := Option.map_eq_some_iff.mp hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨S1, L1⟩ := run_rawUK (K := K) h hg hD hj ha hfd hr'
  refine ⟨S1, fun r hl => ?_⟩
  have hnk := hl.nk
  simp only [Next.toL] at hl hnk
  rcases L1 r (hl.mono fun x y h => Or.inl h) with e | e
  · exact absurd (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩)) hnk
  · exact e

end Raw
end SkaModel
end Formalization
