import lemmas.Ska.RawInvCLFrameRun

/-!
# The run-level liveness with calls: `+copy`

README Gaps 14 (b), track D.  The step that closes `%5`, cons, `%10` and the
call `%2`: `copyL first second` merges the result `first` of the second run
with the parked result `second` of the first run (its continuation at
`s2`).

* `LabUniq l`: at every node of the tree the bonds lie at distinct labels
  and the forks at distinct `yes` labels.  `+copy` merges by label: with two
  bonds of `second` at one label it keeps one and drops the other's need
  (`gD` of `RawInvCLCheckCopy.lean`), so the spec is false without it.
* `TreesApart`: the registers of the two trees are apart.
* **`CopySpecL`**: the spec of `+copy` (checked at every copy of every run
  of `PlainN`, `RawInvCLCheckCopy.lean`): `IL` of the merged goal, and a
  register live at the merged entry is live at `first.th.there` with the
  kills of both trees (`second`'s entered at `s2`).  Not proved yet.
* `copyNeed_dist`: the merged sure need is `Distinct` when the two needs
  are distinct, apart and below `re`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **At every node of the tree, bonds at distinct labels and forks at
distinct `yes` labels.** -/
def LabUniq (l : Lazy S) : Prop :=
  ∀ e ∈ ((0 : Nat), l) :: entries l, (e.2.bond.map (·.1)).Nodup ∧ (e.2.fork.map (·.1.1)).Nodup

/-- **The registers of two trees are apart.** -/
def TreesApart (o1 : Nat) (l1 : Lazy S) (o2 : Nat) (l2 : Lazy S) : Prop :=
  ∀ e ∈ (o1, l1) :: entries l1, ∀ e' ∈ (o2, l2) :: entries l2, ∀ y, NMem e.2.sure.ned y → ¬ NMem e'.2.sure.ned y

/-- **The spec of `+copy`** (checked by `copyC` of `RawInvCLCheckCopy.lean`
at every copy of the 2,856 `PlainN` runs under the seven goals; false
without `LabUniq`): the merged goal holds `IL`, and a register live at its
entry, the merged tree killing its needs, is live at `first.th.there` in the
unproxied blocks before the copy with the outer kills, those of `second`'s
tree entered at `s2` and those of `first`'s tree. -/
def CopySpecL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (first : NextL S) (second : Lazy S) (s2 : Nat) (g g' : Comp.Gen Map) (nex : NextL S),
    IL K first.goal g → IL K (CGoalL.next second (jmp0 s2)) g →
    TreesApart first.th.there first.laz s2 second → LabUniq first.laz → LabUniq second →
    copyL first second g = some (nex, g') →
    IL K nex.goal g' ∧ ∀ r, LiveK (unpM g') (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      LiveK (unpM g) (fun x y => (K x y ∨ lazK s2 second x y) ∨ lazK first.th.there first.laz x y)
        first.th.there r

/-! ## The merged sure need -/

/-- Two needs whose registers lie in apart sets below `R0`, fresh ones of
two consecutive ranges from `R0` on, are apart. -/
theorem nmem_apart_parts {l1 r1 l2 r2 a' b' : Need} {R0 R1 R2 : Nat}
    (m1 : ∀ y, NMem a' y → (NMem l1 y ∨ NMem r1 y) ∨ (R0 ≤ y ∧ y < R1))
    (m2 : ∀ y, NMem b' y → (NMem l2 y ∨ NMem r2 y) ∨ (R1 ≤ y ∧ y < R2))
    (lt1 : ∀ y, NMem l1 y ∨ NMem r1 y → y < R0) (lt2 : ∀ y, NMem l2 y ∨ NMem r2 y → y < R0)
    (ap : ∀ y, NMem l1 y ∨ NMem r1 y → ¬ (NMem l2 y ∨ NMem r2 y)) (hR : R0 ≤ R1) :
    ∀ y, NMem a' y → ¬ NMem b' y := by
  intro y ha hb
  rcases m1 y ha with h1 | h1 <;> rcases m2 y hb with h2 | h2
  · exact ap y h1 h2
  · have := lt1 y h1; omega
  · have := lt2 y h2; omega
  · omega

/-- A register below `R0` outside both needs is outside the merge. -/
theorem nmem_out_part {l r a' : Need} {R0 R1 x : Nat}
    (m : ∀ y, NMem a' y → (NMem l y ∨ NMem r y) ∨ (R0 ≤ y ∧ y < R1)) (hx : x < R0)
    (hl : ¬ NMem l x) (hr : ¬ NMem r x) : ¬ NMem a' x := fun h => by
  rcases m x h with (h | h) | h
  · exact hl h
  · exact hr h
  · omega

theorem distinct_consNeed {a b : Need} (h : Distinct (Need.pair a b)) : Distinct (consNeed a b) := by
  unfold consNeed
  split
  · trivial
  · exact h

/-- **The merged sure need is distinct.** -/
theorem copyNeed_dist : ∀ (a b : Need) (ops : List Pole) (g g' : Comp.Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → Distinct (Need.pair a b) → NB g.re a → NB g.re b → Distinct x.1 := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h dab _ _
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dab.2.1
  | this rl =>
    intro b ops g g' x h dab na nb
    obtain ⟨-, db, -⟩ := dab
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; trivial
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; trivial
    | both x' hh tt =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact db
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨dp, dq, apq⟩ := db
      exact ⟨dp, dq, apq, fun e => by have := nb _ (Or.inl e); omega,
        fun e => by have := nb _ (Or.inr e); omega⟩
  | pair pl ql ihp ihq =>
    intro b ops g g' x h dab na nb
    obtain ⟨⟨dpl, dql, apl⟩, db, ap⟩ := dab
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨dpl, dql, apl⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨dpl, dql, apl, fun e => by have := na _ (Or.inl e); omega,
        fun e => by have := na _ (Or.inr e); omega⟩
    | both x' hr tr =>
      obtain ⟨dhr, dtr, aphtr, nxh, nxt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨l2, m2⟩ := copy_mem h2
      have xlt := nb x' (Or.inl rfl)
      have D1 := ihp hr _ g g1 _ h1 ⟨dpl, dhr, fun y hy e => ap y (Or.inl hy) (Or.inr (Or.inl e))⟩
        (fun y hy => na y (Or.inl hy)) (fun y hy => nb y (Or.inr (Or.inl hy)))
      have D2 := ihq tr _ g1 g2 _ h2 ⟨dql, dtr, fun y hy e => ap y (Or.inr hy) (Or.inr (Or.inr e))⟩
        (fun y hy => Nat.lt_of_lt_of_le (na y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nb y (Or.inr (Or.inr hy))) l1)
      refine ⟨D1, D2, nmem_apart_parts m1 m2 ?_ ?_ ?_ l1, nmem_out_part m1 xlt
        (fun e => ap x' (Or.inl e) (Or.inl rfl)) nxh, nmem_out_part (R0 := g.re) (R1 := g2.re) (fun y hy => ?_) xlt
        (fun e => ap x' (Or.inr e) (Or.inl rfl)) nxt⟩
      · rintro y (e | e)
        · exact na y (Or.inl e)
        · exact nb y (Or.inr (Or.inl e))
      · rintro y (e | e)
        · exact na y (Or.inr e)
        · exact nb y (Or.inr (Or.inr e))
      · rintro y (e | e) (e' | e')
        · exact apl y e e'
        · exact ap y (Or.inl e) (Or.inr (Or.inr e'))
        · exact ap y (Or.inr e') (Or.inr (Or.inl e))
        · exact aphtr y e e'
      · rcases m2 y hy with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Nat.le_trans l1 h.1, h.2⟩
    | pair pr qr =>
      obtain ⟨dpr, dqr, apr⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨l2, m2⟩ := copy_mem h2
      have D1 := ihp pr _ g g1 _ h1 ⟨dpl, dpr, fun y hy e => ap y (Or.inl hy) (Or.inl e)⟩
        (fun y hy => na y (Or.inl hy)) (fun y hy => nb y (Or.inl hy))
      have D2 := ihq qr _ g1 g2 _ h2 ⟨dql, dqr, fun y hy e => ap y (Or.inr hy) (Or.inr e)⟩
        (fun y hy => Nat.lt_of_lt_of_le (na y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nb y (Or.inr hy)) l1)
      refine distinct_consNeed ⟨D1, D2, nmem_apart_parts m1 m2 ?_ ?_ ?_ l1⟩
      · rintro y (e | e)
        · exact na y (Or.inl e)
        · exact nb y (Or.inl e)
      · rintro y (e | e)
        · exact na y (Or.inr e)
        · exact nb y (Or.inr e)
      · rintro y (e | e) (e' | e')
        · exact apl y e e'
        · exact ap y (Or.inl e) (Or.inr e')
        · exact ap y (Or.inr e') (Or.inl e)
        · exact apr y e e'
  | both rl hl tl ihh iht =>
    intro b ops g g' x h dab na nb
    obtain ⟨⟨dhl, dtl, aphtl, nrh, nrt⟩, db, ap⟩ := dab
    have hlt := na rl (Or.inl rfl)
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨dhl, dtl, aphtl, nrh, nrt⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨dhl, dtl, aphtl, nrh, nrt⟩
    | both x' hr tr =>
      obtain ⟨dhr, dtr, aphtr, nxh, nxt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨l2, m2⟩ := copy_mem h2
      have xlt := nb x' (Or.inl rfl)
      have D1 := ihh hr _ g g1 _ h1 ⟨dhl, dhr, fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inr (Or.inl e))⟩
        (fun y hy => na y (Or.inr (Or.inl hy))) (fun y hy => nb y (Or.inr (Or.inl hy)))
      have D2 := iht tr _ g1 g2 _ h2 ⟨dtl, dtr, fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr (Or.inr e))⟩
        (fun y hy => Nat.lt_of_lt_of_le (na y (Or.inr (Or.inr hy))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nb y (Or.inr (Or.inr hy))) l1)
      refine ⟨D1, D2, nmem_apart_parts m1 m2 ?_ ?_ ?_ l1, nmem_out_part m1 xlt
        (fun e => ap x' (Or.inr (Or.inl e)) (Or.inl rfl)) nxh, nmem_out_part (R0 := g.re) (R1 := g2.re) (fun y hy => ?_) xlt
        (fun e => ap x' (Or.inr (Or.inr e)) (Or.inl rfl)) nxt⟩
      · rintro y (e | e)
        · exact na y (Or.inr (Or.inl e))
        · exact nb y (Or.inr (Or.inl e))
      · rintro y (e | e)
        · exact na y (Or.inr (Or.inr e))
        · exact nb y (Or.inr (Or.inr e))
      · rintro y (e | e) (e' | e')
        · exact aphtl y e e'
        · exact ap y (Or.inr (Or.inl e)) (Or.inr (Or.inr e'))
        · exact ap y (Or.inr (Or.inr e')) (Or.inr (Or.inl e))
        · exact aphtr y e e'
      · rcases m2 y hy with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Nat.le_trans l1 h.1, h.2⟩
    | pair p q =>
      obtain ⟨dp, dq, apq⟩ := db
      simp only [copyNeed] at h
      obtain ⟨x', g0, h0, h⟩ := bind_some h
      rw [re_apply] at h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨l2, m2⟩ := copy_mem h2
      simp only at l1 m1
      have D1 := ihh p _ _ g1 _ h1 ⟨dhl, dp, fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inl e)⟩
        (fun y hy => Nat.lt_succ_of_lt (na y (Or.inr (Or.inl hy)))) (fun y hy => Nat.lt_succ_of_lt (nb y (Or.inl hy)))
      have D2 := iht q _ g1 g2 _ h2 ⟨dtl, dq, fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr e)⟩
        (fun y hy => by have := na y (Or.inr (Or.inr hy)); omega)
        (fun y hy => by have := nb y (Or.inr hy); omega)
      refine ⟨D1, D2, nmem_apart_parts m1 m2 (R0 := g.re + 1) ?_ ?_ ?_ l1,
        nmem_out_part m1 (Nat.lt_succ_self _) (fun e => by have := na _ (Or.inr (Or.inl e)); omega)
          (fun e => by have := nb _ (Or.inl e); omega),
        nmem_out_part (R0 := g.re + 1) (R1 := g2.re) (fun y hy => ?_) (Nat.lt_succ_self _)
          (fun e => by have := na _ (Or.inr (Or.inr e)); omega) (fun e => by have := nb _ (Or.inr e); omega)⟩
      · rintro y (e | e)
        · have := na y (Or.inr (Or.inl e)); omega
        · have := nb y (Or.inl e); omega
      · rintro y (e | e)
        · have := na y (Or.inr (Or.inr e)); omega
        · have := nb y (Or.inr e); omega
      · rintro y (e | e) (e' | e')
        · exact aphtl y e e'
        · exact ap y (Or.inr (Or.inl e)) (Or.inr e')
        · exact ap y (Or.inr (Or.inr e')) (Or.inl e)
        · exact apq y e e'
      · rcases m2 y hy with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Nat.le_trans l1 h.1, h.2⟩

end Raw
end SkaModel
end Formalization
