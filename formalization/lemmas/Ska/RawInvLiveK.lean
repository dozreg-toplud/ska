import lemmas.Ska.RawInvStep
import lemmas.Ska.CompGrowU

/-!
# Raw `+comp` output with `%6` below the top: the liveness with kills and the ranked fields

README Gaps 14, the class `FragX`.  The checks of `RawInvCheckX.lean` show
that the first fragment's invariant `SI` is false there in three places: the
fork blocks hop up (`JDown`), the join of `+fork-need` has several
parameters (`Par1`), and a register live at a lazy entry may be one that the
code before the entry defines (`[[0 3] [6 [0 6] [0 2] [0 1]]]`: the head's
register, defined at the entry and read after the join), so liveness cannot
restart at the lazy entries.  This file has the replacements.

* `LiveK bl K k r`: liveness in which the block at each label `k` first
  defines the registers `K k`.  The run-level fact that the checks support
  is `¬ LiveK bl K entry r` for every `r` when `K` gives each lazy entry the
  registers of its sure need (`liveKB`).
* `Prep P bl bl'`: `bl'` is `bl` with the ops `P k` in front of the block at
  every `k` (what `+coerce-lazy` does at the lazy entries, and what the
  parents' `+copy` and `+split` do after a run).  **`live_prep`**: a
  register live in `bl'` is live with the kills in `bl`, or read first by a
  prologue, when each prologue defines its label's kills.
  **`live_entry_of_prep`**: so a run whose blocks leave nothing live at the
  entry with the kills, followed by prologues that read only `X`, leaves only
  registers of `X` live there, the hypothesis `hl` of `optIn_toStraight`.
  `prep_trans`: prologues compose.
* The ranked forms of `JDown` and `ArgsAbove` (`JDownR ρ`, `ArgsAboveR ρ`,
  `ρ := upRk bl` for `FragX`, `id` for the first fragment) give `Acyclic`,
  `PassOK` and `DownPar` (`acyclic_of_jdownR`, `passOK_ofR`,
  `downPar_of_argsR`); prologues keep them, and `upRk` itself
  (`upRk_prep`, `jdownR_prep`, `argsAboveR_prep`, `parNodup_prep`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt

variable {Map : Type → Type} [HoonMap Map]

/-! ## Liveness with kills -/

/-- **`r` is live at `k` when the block at each label `x` first defines the
registers `K x`.** -/
inductive LiveK (bl : Map Blob) (K : Nat → Nat → Prop) : Nat → Nat → Prop
  | here {k : Nat} {b : Blob} {r : Nat} : HoonMap.get bl k = some b → BlockRF b r → ¬ K k r → LiveK bl K k r
  | next {k : Nat} {b : Blob} {j : Jmp} {r : Nat} : HoonMap.get bl k = some b → j ∈ getJmps b.fin →
      LiveK bl K j.there r → r ∉ blockDefs b → ¬ K k r → LiveK bl K k r

theorem LiveK.live {bl : Map Blob} {K : Nat → Nat → Prop} {k r : Nat} (h : LiveK bl K k r) : Live bl k r := by
  induction h with
  | here hb hr _ => exact Live.here hb hr
  | next hb hj _ hd _ ih => exact Live.next hb hj ih hd

/-- With no kills it is `Live`. -/
theorem liveK_of_live {bl : Map Blob} {k r : Nat} (h : Live bl k r) : LiveK bl (fun _ _ => False) k r := by
  induction h with
  | here hb hr => exact LiveK.here hb hr id
  | next hb hj _ hd ih => exact LiveK.next hb hj ih hd id

/-- Fewer kills, more liveness. -/
theorem LiveK.mono {bl : Map Blob} {K K' : Nat → Nat → Prop} (hK : ∀ x r, K' x r → K x r) {k r : Nat}
    (h : LiveK bl K k r) : LiveK bl K' k r := by
  induction h with
  | here hb hr hk => exact LiveK.here hb hr fun h => hk (hK _ _ h)
  | next hb hj _ hd hk ih => exact LiveK.next hb hj ih hd fun h => hk (hK _ _ h)

/-! ## Prologues -/

/-- `bl'` is `bl` with the ops `P k` in front of the block at every `k`. -/
def Prep (P : Nat → List Pole) (bl bl' : Map Blob) : Prop :=
  ∀ k, HoonMap.get bl' k = (HoonMap.get bl k).map (pre (P k))

theorem prep_nil (bl : Map Blob) : Prep (fun _ => []) bl bl := by
  intro k
  cases HoonMap.get bl k <;> simp [pre]

theorem prep_trans {P Q : Nat → List Pole} {bl bl' bl'' : Map Blob} (h : Prep P bl bl') (h' : Prep Q bl' bl'') :
    Prep (fun k => Q k ++ P k) bl bl'' := by
  intro k
  rw [h', h]
  cases HoonMap.get bl k <;> simp [pre, List.append_assoc]

/-- One block with `A` in front, the others unchanged. -/
theorem prep_put {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole} (hb : HoonMap.get bl o = some b) :
    Prep (fun k => if k = o then A else []) bl (HoonMap.put bl o (pre A b)) := by
  intro k
  by_cases e : k = o
  · subst e; rw [get_put_self, hb]; simp
  · rw [get_put_ne e]; cases HoonMap.get bl k <;> simp [e, pre]

theorem blockRF_pre {A : List Pole} {b : Blob} {r : Nat} (h : BlockRF (pre A b) r) :
    OpsRF A r ∨ (r ∉ defsOf A ∧ BlockRF b r) := by
  obtain ⟨hp, h⟩ := h
  rcases h with h | ⟨hd, hf⟩
  · rcases opsRF_append.mp h with h | ⟨hd, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hd, hp, Or.inl h⟩
  · rw [defsOf_append, List.mem_append, not_or] at hd
    exact Or.inr ⟨hd.1, hp, Or.inr ⟨hd.2, hf⟩⟩

/-- **A register live after prologues is live with the kills before them,
or read first by a prologue**, when each prologue defines its label's
kills. -/
theorem live_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {K : Nat → Nat → Prop}
    (hK : ∀ k r, K k r → r ∈ defsOf (P k)) {k r : Nat} (h : Live bl' k r) :
    LiveK bl K k r ∨ ∃ k', OpsRF (P k') r := by
  induction h with
  | here hb hr =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases blockRF_pre hr with h | ⟨hd, h⟩
    · exact Or.inr ⟨_, h⟩
    · exact Or.inl (LiveK.here h0 h fun hk => hd (hK _ _ hk))
  | next hb hj _ hd ih =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases ih with ih | ih
    · exact Or.inl (LiveK.next h0 hj ih (fun hm => hd (mem_blockDefs_pre.mpr (Or.inl hm)))
        fun hk => hd (mem_blockDefs_pre.mpr (Or.inr (hK _ _ hk))))
    · exact Or.inr ih

/-- **What is live at the entry after the prologues**: only registers that
the prologues read first, when nothing is live there with the kills. -/
theorem live_entry_of_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl')
    {K : Nat → Nat → Prop} (hK : ∀ k r, K k r → r ∈ defsOf (P k)) {o : Nat} (hl : ∀ r, ¬ LiveK bl K o r)
    {X : Nat → Prop} (hX : ∀ k r, OpsRF (P k) r → X r) {r : Nat} (h : Live bl' o r) : X r := by
  rcases live_prep hP hK h with h | ⟨k, h⟩
  · exact absurd h (hl r)
  · exact hX k r h

/-- Prologues keep the definitions of the blocks and add their own. -/
theorem defd_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {r : Nat} :
    Defd bl' r ↔ ∃ k b, HoonMap.get bl k = some b ∧ (r ∈ blockDefs b ∨ r ∈ defsOf (P k)) := by
  rw [defd_iff]
  constructor
  · rintro ⟨k, b', hb', hm⟩
    rw [hP] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
    exact ⟨k, b, hb, mem_blockDefs_pre.mp hm⟩
  · rintro ⟨k, b, hb, hm⟩
    exact ⟨k, pre (P k) b, by rw [hP, hb]; rfl, mem_blockDefs_pre.mpr hm⟩

/-! ## The ranked fields -/

/-- Every block jumps to labels of lower rank. -/
def JDownR (ρ : Nat → Nat) (bl : Map Blob) : Prop :=
  ∀ k b, HoonMap.get bl k = some b → ∀ j ∈ getJmps b.fin, ρ j.there < ρ k

/-- Every argument of a jump is above every parameter of every block whose
rank is at most the target's. -/
def ArgsAboveR (ρ : Nat → Nat) (bl : Map Blob) : Prop :=
  ∀ z bz y b j r x, HoonMap.get bl z = some bz → HoonMap.get bl y = some b → j ∈ getJmps b.fin →
    some r ∈ j.args → ρ z ≤ ρ j.there → x ∈ bz.par → x < r

theorem jdownR_id {bl : Map Blob} : JDownR id bl ↔ JDown bl := Iff.rfl
theorem argsAboveR_id {bl : Map Blob} : ArgsAboveR id bl ↔ ArgsAbove bl := Iff.rfl

theorem acyclic_of_jdownR {ρ : Nat → Nat} {bl : Map Blob} (h : JDownR ρ bl) : Acyclic bl :=
  ⟨ρ, fun o b j hb hj => h o b hb j hj⟩

theorem rFrom_leR {ρ : Nat → Nat} {bl : Map Blob} (hd : JDownR ρ bl) {x z : Nat} (h : RFrom bl x z) : ρ z ≤ ρ x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hb hj _ ih => exact Nat.le_trans ih (Nat.le_of_lt (hd _ _ hb _ hj))

theorem passOK_ofR {ρ : Nat → Nat} {bl : Map Blob} (h : ArgsAboveR ρ bl) : PassOK bl :=
  fun o b j b2 hb hj hb2 r hr hp => Nat.lt_irrefl r (h j.there b2 o b j r r hb2 hb hj hr (Nat.le_refl _) hp)

theorem downPar_of_argsR {ρ : Nat → Nat} {bl : Map Blob} (h : ArgsAboveR ρ bl) (hd : JDownR ρ bl) : DownPar bl :=
  fun y b j hb hj r hr z bz hz hbz hp => Nat.lt_irrefl r (h z bz y b j r r hbz hb hj hr (rFrom_leR hd hz) hp)

/-! ## Prologues keep the ranked fields -/

theorem upRk_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') (k : Nat) :
    Comp.upRk bl' k = Comp.upRk bl k := by
  unfold Comp.upRk
  rw [hP k]
  cases HoonMap.get bl k with
  | none => rfl
  | some b => obtain ⟨p, bd, f⟩ := b; simp only [Option.map_some]; cases f <;> rfl

theorem get_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {k : Nat} {b' : Blob}
    (h : HoonMap.get bl' k = some b') : ∃ b, HoonMap.get bl k = some b ∧ b' = pre (P k) b := by
  rw [hP] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b, hb, rfl⟩

theorem jdownR_prep {ρ : Nat → Nat} {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl')
    (h : JDownR ρ bl) : JDownR ρ bl' := by
  intro k b' hb' j hj
  obtain ⟨b, hb, rfl⟩ := get_prep hP hb'
  exact h k b hb j hj

theorem argsAboveR_prep {ρ : Nat → Nat} {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl')
    (h : ArgsAboveR ρ bl) : ArgsAboveR ρ bl' := by
  intro z bz' y b' j r x hz hy hj hr hzj hx
  obtain ⟨bz, hz0, rfl⟩ := get_prep hP hz
  obtain ⟨b, hy0, rfl⟩ := get_prep hP hy
  exact h z bz y b j r x hz0 hy0 hj hr hzj hx

theorem parNodup_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') (h : ParNodup bl) :
    ParNodup bl' := by
  intro k b' hb'
  obtain ⟨b, hb, rfl⟩ := get_prep hP hb'
  exact h k b hb

/-- With `ρ := upRk`, the rank of the blocks after prologues is the rank
before them. -/
theorem jdownR_upRk_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl')
    (h : JDownR (Comp.upRk bl) bl) : JDownR (Comp.upRk bl') bl' := by
  have e : Comp.upRk bl' = Comp.upRk bl := funext (upRk_prep hP)
  rw [e]; exact jdownR_prep hP h

theorem argsAboveR_upRk_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl')
    (h : ArgsAboveR (Comp.upRk bl) bl) : ArgsAboveR (Comp.upRk bl') bl' := by
  have e : Comp.upRk bl' = Comp.upRk bl := funext (upRk_prep hP)
  rw [e]; exact argsAboveR_prep hP h

end Raw
end SkaModel
end Formalization
