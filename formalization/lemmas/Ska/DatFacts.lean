import lemmas.Ska.BridgeD

/-!
# Facts about the datums the analysis writes

`KnowMeets.lean` needs three facts about the datums `+bake-graph` reads
(`DatInhab`, `LessInhab`, `NoAx0Dat`).  This file proves what they rest on:

1. `NoAx0` (moved here from `KnowMeets.lean`): no `%10` of a nomm has axis
   `0`.  Every nomm `fol-loop` returns has it (`folLoop_noAx0`): the case
   `%10` turns axis `0` into `[0 0]`, and every other case builds its nomm
   from the nomms of its calls to itself.  For example `[10 [0 [1 5]] [0 1]]`
   is analysed to `Nomm.n0 0`.
2. A well-formed sock that is not `%void` has a noun (`wf_inhab`): its data,
   since a cell cape over atom data knows nothing.
3. `+patch-prod` of a product with a noun, for a subject sock with a noun,
   has a noun (`patchProd_inhab`).

The convergence invariant `CInv` (`ConvInv.lean`) carries the per-entry form
(`CInv.dat`): every entry of the graph is a memo hit of the persistent memo
that `order` does not hold, or its nomm has `NoAx0`, its code requirement has
a noun, and its product is not `%void` once `order` does not hold it (`+pop`
turns `%void` into `|+~`).
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Bake

/-- No `%10` of the nomm has axis `0`. -/
def NoAx0 : Nomm → Prop
  | Nomm.cons p q => NoAx0 p ∧ NoAx0 q
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n2 p q _ => NoAx0 p ∧ NoAx0 q
  | Nomm.n3 p => NoAx0 p
  | Nomm.n4 p => NoAx0 p
  | Nomm.n5 p q => NoAx0 p ∧ NoAx0 q
  | Nomm.n6 p q r => NoAx0 p ∧ NoAx0 q ∧ NoAx0 r
  | Nomm.n7 p q => NoAx0 p ∧ NoAx0 q
  | Nomm.n10 a v q => a ≠ 0 ∧ NoAx0 v ∧ NoAx0 q
  | Nomm.n11s _ q _ => NoAx0 q
  | Nomm.n11d _ h q _ => NoAx0 h ∧ NoAx0 q
  | Nomm.n12 p q => NoAx0 p ∧ NoAx0 q
  | Nomm.mean p _ q _ _ => NoAx0 p ∧ NoAx0 q

end Bake

open Bake

/-! ## Socks with a noun -/

/-- The data of a well-formed sock fits it. -/
theorem wf_fitsCape : ∀ (c : Cape) (d : Noun), WellFormed (Sock.mk c d) → FitsCape c d d
  | Cape.yes, _, _ => rfl
  | Cape.no, _, _ => trivial
  | Cape.cell c1 c2, Noun.atom k, h => Or.inl (h [] c1 c2 k rfl)
  | Cape.cell c1 c2, Noun.cell d1 d2, h => by
    have h1 : WellFormed (Sock.mk c1 d1) := by simpa [So.hed] using wf_hed h
    have h2 : WellFormed (Sock.mk c2 d2) := by simpa [So.tel] using wf_tel h
    exact Or.inr ⟨d1, d2, d1, d2, rfl, rfl, wf_fitsCape c1 d1 h1, wf_fitsCape c2 d2 h2⟩

/-- **A well-formed sock that is not `%void` has a noun**: its data. -/
theorem wf_inhab {s : Sock} (hw : WellFormed s) (hv : s ≠ Sock.void) : ∃ y, Fits s y := by
  cases s with
  | void => exact absurd rfl hv
  | mk c d => exact ⟨d, wf_fitsCape c d hw⟩

theorem hed_inhab {s : Sock} (h : ∃ y, Fits s y) : ∃ y, Fits (So.hed s) y := by
  obtain ⟨y, hy⟩ := h
  cases y with
  | cell a b => exact ⟨a, hed_fits hy⟩
  | atom k =>
    cases s with
    | void => exact absurd hy id
    | mk c d => exact ⟨A 0, (hed_tel_blank_of_atom (k := k) hy).1.fits _⟩

theorem tel_inhab {s : Sock} (h : ∃ y, Fits s y) : ∃ y, Fits (So.tel s) y := by
  obtain ⟨y, hy⟩ := h
  cases y with
  | cell a b => exact ⟨b, tel_fits hy⟩
  | atom k =>
    cases s with
    | void => exact absurd hy id
    | mk c d => exact ⟨A 0, (hed_tel_blank_of_atom (k := k) hy).2.fits _⟩

theorem pull_inhab {a r : Sock} {p : Nat} (ha : ∃ y, Fits a y) (hp : p ≠ 0) (h : So.pull a p = some r) :
    ∃ y, Fits r y := by
  obtain ⟨y, hy⟩ := ha
  cases hs : slot? p y with
  | some m => exact ⟨m, pull_fits hy hs h⟩
  | none => exact ⟨A 0, (pull_blank_of_none hy hp hs h).fits _⟩

/-- **`+patch-prod` keeps a noun**: a product with a noun, patched for a
subject sock with a noun. -/
theorem patchProd_inhab {k : Sock} (hk : ∃ y, Fits k y) :
    ∀ (src : Noun) (s : Sock), (∃ y, Fits s y) → ∃ y, Fits (patchProd s src k).sock y := by
  intro src
  induction src with
  | atom a =>
    intro s hy
    by_cases h0 : a = 0
    · subst h0
      rw [patchProd, if_pos rfl]
      exact hy
    · have hs : s ≠ Sock.void := by rintro rfl; obtain ⟨y, hy⟩ := hy; exact hy
      have hne : Noun.atom a ≠ A 0 := fun h => h0 (by cases h; rfl)
      rw [patchProd, if_neg hne, if_neg hs]
      obtain ⟨y, hky⟩ := hk
      obtain ⟨r, hr⟩ : ∃ r, So.pull k a = some r := by
        unfold So.pull
        rw [if_neg h0]
        cases k with
        | void => exact absurd hky id
        | mk c d => exact ⟨_, rfl⟩
      simp only [hr, Option.getD_some]
      exact pull_inhab ⟨y, hky⟩ h0 hr
  | cell h t ih1 ih2 =>
    intro s hy
    have hs : s ≠ Sock.void := by rintro rfl; obtain ⟨y, hy⟩ := hy; exact hy
    have hne : Noun.cell h t ≠ A 0 := fun h => by cases h
    rw [patchProd, if_neg hne, if_neg hs]
    obtain ⟨y1, h1⟩ := ih1 _ (hed_inhab hy)
    obtain ⟨y2, h2⟩ := ih2 _ (tel_inhab hy)
    exact ⟨C y1 y2, knit_fits h1 h2⟩

/-! ## `fol-loop` never makes a `%10` at axis `0` -/

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- Every nomm that `go` returns has no `%10` at axis `0`. -/
def GoNoAx0 (go : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gen out gen', go fol sub seat mk bc df gen = some (out, gen') → NoAx0 out.nomm

theorem callStep_noAx0 {res : ResGo M R} {go : FolGoS M R} (hg : GoNoAx0 go) {seat mk : Option Noun}
    {bc df : Bool} {s f out : FolOut} {g g' : GenS M R} (hs : NoAx0 s.nomm) (hf : NoAx0 f.nomm)
    (h : callStep res go seat mk bc df s f g = some (out, g')) : NoAx0 out.nomm := by
  unfold callStep at h
  split at h
  · cases h; exact ⟨hs, hf⟩
  · split at h
    · split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨i, gi⟩, hi, rfl, rfl⟩ := h
        exact ⟨hs, hg _ _ _ _ _ _ _ _ _ hi⟩
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨r, _, h⟩ := h
        split at h
        · cases h
        · cases h; exact ⟨hs, hf⟩
    · cases h; exact ⟨hs, hf⟩

/-- **One level of `fol-loop` keeps `NoAx0`**: the case `%10` at axis `0`
returns `[0 0]`, every other case builds on its calls to itself. -/
theorem folStep_noAx0 (env : Env R) (res : ResGo M R) {go : FolGoS M R} (hg : GoNoAx0 go) :
    GoNoAx0 (folStep env res go) := by
  intro fol sub seat mk bc df gs out gs' h
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    exact ⟨hg _ _ _ _ _ _ _ _ _ h1, hg _ _ _ _ _ _ _ _ _ h2⟩
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, _, rfl, rfl⟩ := h
    trivial
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    exact callStep_noAx0 hg (hg _ _ _ _ _ _ _ _ _ h1) (hg _ _ _ _ _ _ _ _ _ h2) h3
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    have := hg _ _ _ _ _ _ _ _ _ h1
    exact this
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    have := hg _ _ _ _ _ _ _ _ _ h1
    exact this
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact ⟨hg _ _ _ _ _ _ _ _ _ h1, hg _ _ _ _ _ _ _ _ _ h2⟩
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    exact ⟨hg _ _ _ _ _ _ _ _ _ h1, hg _ _ _ _ _ _ _ _ _ h2, hg _ _ _ _ _ _ _ _ _ h3⟩
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact ⟨hg _ _ _ _ _ _ _ _ _ h1, hg _ _ _ _ _ _ _ _ _ h2⟩
  | op8 a b q =>
    simp only [folStep, hs] at h
    exact hg _ _ _ _ _ _ _ _ _ h
  | op9 p a b =>
    simp only [folStep, hs] at h
    exact hg _ _ _ _ _ _ _ _ _ h
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      trivial
    · rename_i hx
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', _, rfl, rfl⟩ := h
      exact ⟨hx, hg _ _ _ _ _ _ _ _ _ h1, hg _ _ _ _ _ _ _ _ _ h2⟩
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · exact hg _ _ _ _ _ _ _ _ _ h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      have := hg _ _ _ _ _ _ _ _ _ h1
      exact this
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    split at h
    · exact hg _ _ _ _ _ _ _ _ _ h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, g2⟩, _, ⟨fr, g3⟩, h3, g4, _, rfl, rfl⟩ := h
      have a1 := hg _ _ _ _ _ _ _ _ _ e1
      have a2 := hg _ _ _ _ _ _ _ _ _ h3
      cases arm with
      | none => exact ⟨a1, a2⟩
      | some p => obtain ⟨bl, k⟩ := p; exact ⟨a1, a2⟩
  | op11c x y h1 h2 f =>
    simp only [folStep, hs] at h
    exact hg _ _ _ _ _ _ _ _ _ h
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact ⟨hg _ _ _ _ _ _ _ _ _ h1, hg _ _ _ _ _ _ _ _ _ h2⟩
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial

/-- **Every nomm of `fol-loop` has no `%10` at axis `0`**, at every fuel. -/
theorem folLoop_noAx0 (env : Env R) (memoF : Memo M) : ∀ n, GoNoAx0 (folLoop env memoF n)
  | 0 => fun _ _ _ _ _ _ _ _ _ h => by rw [folLoop_zero] at h; cases h
  | n + 1 => by
    rw [folLoop_succ]
    exact folStep_noAx0 env _ (folLoop_noAx0 env memoF n)

end Ana

end SkaModel
end Formalization
