import lemmas.Ska.RawInvIHXSix

/-!
# Raw `+comp` output on `FragX`: the concrete predicate `Xup`

README Gaps 14, track D, step 3 of the class `FragX`.  `runX_rawIHX` holds
for every predicate `X` of the blocks with `XSix X`.  The final pass
(`optIn_toStraight_prep`) asks `ArgsAboveR (upRk bl) bl` of the raw blocks,
which the label order alone does not give once fork blocks hop up.

* `Xup bl`: the label-order `ArgsAbove`, a block that hops up (`HopsUp`)
  has no parameter, and no jump with arguments targets a block that hops
  up.  Checked on the 4,080 nomms of `enumX` (and under `%next`, `%pick`)
  before the proof; in 3,360 of them a block hops up and a jump has
  arguments.
* **`argsAboveR_upRk_of_xup`**: `Xup bl → ArgsAboveR (upRk bl) bl` (a block
  with parameters, and the target of a jump with arguments, have the rank
  `3 * k`, so the ranked order is the label order there).
* The instances `XOK Xup` (a new block that `+emit` puts, with
  `EmitOK.nup`; ops in front of a block) and `XSix Xup` (the blocks only;
  the three blocks of `+fork-sure`: the fork blocks have no parameter and
  pass fresh registers above every old one to the join, which hops down).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {Map : Type → Type} [HoonMap Map]

theorem hopsUp_of_fin {bl bl' : Map Blob} {k : Nat}
    (h : (HoonMap.get bl k).map Blob.fin = (HoonMap.get bl' k).map Blob.fin) (hu : HopsUp bl k) : HopsUp bl' k := by
  obtain ⟨b, j, hb, hf, hlt⟩ := hu
  rw [hb] at h
  cases e : HoonMap.get bl' k with
  | none => rw [e] at h; cases h
  | some b' =>
    rw [e] at h
    simp at h
    exact ⟨b', j, e, by rw [← h, hf], hlt⟩

theorem hopsUp_iff_of_get {bl bl' : Map Blob} {k : Nat} (h : HoonMap.get bl' k = HoonMap.get bl k) :
    HopsUp bl' k ↔ HopsUp bl k := ⟨hopsUp_of_fin (by rw [h]), hopsUp_of_fin (by rw [h])⟩

theorem not_hopsUp_of {bl : Map Blob} {k : Nat} {b : Blob} (hb : HoonMap.get bl k = some b)
    (hj : ∀ j ∈ getJmps b.fin, j.there ≤ k) : ¬ HopsUp bl k := by
  rintro ⟨b', j, hb', hf, hlt⟩
  rw [hb] at hb'; cases hb'
  have := hj j (by rw [hf]; simp [getJmps])
  omega

/-- A block that does not hop up has the rank of its label. -/
theorem upRk_of_not_hopsUp {bl : Map Blob} {k : Nat} (h : ¬ HopsUp bl k) : upRk bl k = 3 * k := by
  unfold upRk
  split
  next p bd j e =>
    split
    next hlt => exact absurd ⟨_, j, e, rfl, hlt⟩ h
    next => rfl
  next => rfl

/-- **The predicate of the blocks for `FragX`.** -/
def Xup (bl : Map Blob) : Prop :=
  ArgsAbove bl ∧ (∀ k b, HoonMap.get bl k = some b → b.par ≠ [] → ¬ HopsUp bl k) ∧
    ∀ y b j r, HoonMap.get bl y = some b → j ∈ getJmps b.fin → some r ∈ j.args → ¬ HopsUp bl j.there

/-- **`Xup` gives the ranked `ArgsAboveR` in `upRk`.** -/
theorem argsAboveR_upRk_of_xup {bl : Map Blob} (h : Xup bl) : ArgsAboveR (upRk bl) bl := by
  intro z bz y b j r x hz hy hj hr hle hx
  have n1 : ¬ HopsUp bl z := h.2.1 z bz hz (List.ne_nil_of_mem hx)
  have n2 := h.2.2 y b j r hy hj hr
  rw [upRk_of_not_hopsUp n1, upRk_of_not_hopsUp n2] at hle
  exact h.1 z bz y b j r x hz hy hj hr (by omega) hx

/-- `argsAbove_put` with the old blocks' jumps below the new label in place
of `JDown`. -/
theorem argsAbove_putT {bl : Map Blob} {l : Nat} {b : Blob} (ha : ArgsAbove bl)
    (ht : ∀ k b', HoonMap.get bl k = some b' → ∀ j ∈ getJmps b'.fin, j.there < l)
    (hb : ∀ j ∈ getJmps b.fin, ∀ r, some r ∈ j.args →
      ∀ z bz, HoonMap.get (HoonMap.put bl l b) z = some bz → z ≤ j.there → ∀ x ∈ bz.par, x < r) :
    ArgsAbove (HoonMap.put bl l b) := by
  intro z bz y b' j r x hz hy hj hr hzj hx
  rcases get_put_cases hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
  · exact hb j hj r hr z bz hz hzj x hx
  · have hlt := ht y b' hy j hj
    rcases get_put_cases hz with ⟨rfl, rfl⟩ | ⟨_, hz⟩
    · omega
    · exact ha z bz y b' j r x hz hy hj hr hzj hx

instance : XOK (Xup (Map := Map)) where
  put := fun {bl l b} hx _ ht hj _ ha hn => by
    have nl : ¬ HopsUp (HoonMap.put bl l b) l :=
      not_hopsUp_of get_put_self (fun j hj' => Nat.le_of_lt (hj j hj'))
    have eq : ∀ k, k ≠ l → (HopsUp (HoonMap.put bl l b) k ↔ HopsUp bl k) := fun k hk =>
      hopsUp_iff_of_get (get_put_ne hk)
    refine ⟨argsAbove_putT hx.1 ht ha, fun k b' hb' hp => ?_, fun y b' j r hy hj' hr => ?_⟩
    · rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨ne, hb'⟩
      · exact nl
      · rw [eq k ne]; exact hx.2.1 k b' hb' hp
    · rcases get_put_cases hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
      · rw [eq _ (Nat.ne_of_lt (hj j hj'))]; exact hn j hj' r hr
      · rw [eq _ (Nat.ne_of_lt (ht y b' hy j hj'))]; exact hx.2.2 y b' j r hy hj' hr
  prep := fun {bl o b A} hx hb => by
    have eq : ∀ k, HopsUp (HoonMap.put bl o (pre A b)) k ↔ HopsUp bl k := fun k => by
      by_cases e : k = o
      · subst e
        exact ⟨hopsUp_of_fin (by rw [get_put_self, hb]; rfl), hopsUp_of_fin (by rw [get_put_self, hb]; rfl)⟩
      · exact hopsUp_iff_of_get (get_put_ne e)
    refine ⟨argsAbove_prepend hx.1 hb, fun k b' hb' hp => ?_, fun y b' j r hy hj hr => ?_⟩
    · rw [eq]
      rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, hb'⟩
      · exact hx.2.1 _ b hb hp
      · exact hx.2.1 k b' hb' hp
    · rw [eq]
      rcases get_put_cases hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
      · exact hx.2.2 _ b j r hb hj hr
      · exact hx.2.2 y b' j r hy hj hr

instance : XSix (Xup (Map := Map)) where
  ext := fun {bl bl'} hx E => by
    have eq : ∀ k, HopsUp bl' k ↔ HopsUp bl k := fun k => hopsUp_iff_of_get (E k)
    refine ⟨fun z bz y b j r x hz hy hj hr hzj hx' => ?_, fun k b hb hp => ?_, fun y b j r hy hj hr => ?_⟩
    · rw [E] at hz hy; exact hx.1 z bz y b j r x hz hy hj hr hzj hx'
    · rw [eq]; rw [E] at hb; exact hx.2.1 k b hb hp
    · rw [eq]; rw [E] at hy; exact hx.2.2 y b j r hy hj hr
  fork := fun {bl bl' l t R ned a0 a1} hx _ ht hreg _ h2 hn ha0 ha1 _ hold hb0 hb1 hb2 hnone => by
    have cs : ∀ k b, HoonMap.get bl' k = some b → (k < l ∧ HoonMap.get bl k = some b) ∨
        (k = l ∧ b = ⟨[], [], Termin.hop ⟨a0.map some, l + 2⟩⟩) ∨
        (k = l + 1 ∧ b = ⟨[], [], Termin.hop ⟨a1.map some, l + 2⟩⟩) ∨
        (k = l + 2 ∧ b = ⟨flattenNeed ned, [], Termin.hop (jmp0 t)⟩) := by
      intro k b hb
      by_cases k0 : k < l
      · exact Or.inl ⟨k0, by rw [← hold k k0]; exact hb⟩
      by_cases e0 : k = l
      · subst e0; rw [hb0] at hb; exact Or.inr (Or.inl ⟨rfl, (Option.some.inj hb).symm⟩)
      by_cases e1 : k = l + 1
      · subst e1; rw [hb1] at hb; exact Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj hb).symm⟩))
      by_cases e2 : k = l + 2
      · subst e2; rw [hb2] at hb; exact Or.inr (Or.inr (Or.inr ⟨rfl, (Option.some.inj hb).symm⟩))
      rw [hnone k (by omega)] at hb; cases hb
    have upOld : ∀ k, k < l → (HopsUp bl' k ↔ HopsUp bl k) := fun k hk => hopsUp_iff_of_get (hold k hk)
    have nup2 : ¬ HopsUp bl' (l + 2) :=
      not_hopsUp_of hb2 (fun j hj => by simp [getJmps] at hj; subst hj; simp [jmp0]; omega)
    -- a parameter of a block of `bl'` is below `R`
    have parR : ∀ z bz x, HoonMap.get bl' z = some bz → x ∈ bz.par → x < R := fun z bz x hz hx' => by
      rcases cs z bz hz with ⟨-, hz'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (hreg z bz hz').1 x hx'
      · simp at hx'
      · simp at hx'
      · exact hn x hx'
    refine ⟨fun z bz y b j r x hz hy hj hr hzj hx' => ?_, fun k b hb hp => ?_, fun y b j r hy hj hr => ?_⟩
    · rcases cs y b hy with ⟨-, hy'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have hlt := ht y b hy' j hj
        have hz' : HoonMap.get bl z = some bz := by rw [← hold z (by omega)]; exact hz
        exact hx.1 z bz y b j r x hz' hy' hj hr hzj hx'
      · simp [getJmps] at hj; subst hj; simp at hr
        have := ha0 r hr; have := parR z bz x hz hx'; omega
      · simp [getJmps] at hj; subst hj; simp at hr
        have := ha1 r hr; have := parR z bz x hz hx'; omega
      · simp [getJmps] at hj; subst hj; simp [jmp0] at hr
    · rcases cs k b hb with ⟨k0, hb'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [upOld k k0]; exact hx.2.1 k b hb' hp
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact nup2
    · rcases cs y b hy with ⟨-, hy'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [upOld _ (ht y b hy' j hj)]; exact hx.2.2 y b j r hy' hj hr
      · simp [getJmps] at hj; subst hj; exact nup2
      · simp [getJmps] at hj; subst hj; exact nup2
      · simp [getJmps] at hj; subst hj; simp [jmp0] at hr

/-- **`runX_rawIHX` for `Xup`.** -/
theorem runX_rawIHX_up {S : Type} [HoonSet S] [HoonMapKeys Map] {nm : Nomm} (x : FragX (S := S) nm) :
    RawIHX S Map (Xup (Map := Map)) nm :=
  runX_rawIHX x

end Raw
end SkaModel
end Formalization
