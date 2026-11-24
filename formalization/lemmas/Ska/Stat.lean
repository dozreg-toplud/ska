import lemmas.Ska.AppPath

/-!
# The static condition, kept by every sock operation of `fol-loop`

`StatOK T S σ` is the static condition of a sock-annotated noun `[S σ]` in a
function on the subject sock `T`:

* `stat`: at each part whose provenance is an axis of the subject, `S`
  generalizes what `T` knows at that axis (`GenLe`);
* `shape`: at each part whose provenance is a cell, `S` may stand for a cell
  (`Cellish`).

Both are only asked of a sock that is not `%void`, since `fol-loop` makes
`%void` products with any provenance (a pull from a `%void` subject, a
patched `%void` product).

`GenLe T S` is the structural form of "`S` knows no more than `T`": `S` is
`T`, or knows nothing, or is the knit of generalizations of `T`'s head and
tail.  It gives `PosLe` (`GenLe.toPosLe`), and unlike `PosLe` it keeps
`Cellish` and commutes with `+app:ca` on socks with malformed parts (a cell
cape over atom data), which `PosLe` does not: a sock that no noun fits is
`PosLe` below every sock.

The operations: `+pull:so` with `+slot:pi` (`statOK_slot`), `+knit:so` with
`+cons:pi` (`statOK_knit`, `statOK_consProd`), `+double-int`
(`statOK_doubleInt_left`, `statOK_doubleInt_right`), `+darn:so` with
`+edit:pi` (`statOK_darn`), `+compose:pi` (`statOK_compose`, given the
callee's own condition on its subject sock), and `+patch-prod`
(`statOK_patchProd`).
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Generalization by forgetting

`GenLe` itself is defined in `CallGraph.lean`, where `Answers.hitGen` uses
it. -/

theorem knit_void_inv {S1 S2 : Sock} (h : So.knit S1 S2 = Sock.void) :
    S1 = Sock.void ∨ S2 = Sock.void := by
  cases S1 with
  | void => exact Or.inl rfl
  | mk l d1 =>
    cases S2 with
    | void => exact Or.inr rfl
    | mk r d2 => simp only [So.knit] at h; split at h <;> simp [Sock.dunno] at h

/-- The head and the tail of a knit of socks that are not `%void`: the two
socks, unless the knit knows nothing at all. -/
theorem knit_parts {S1 S2 : Sock} (h1 : S1 ≠ Sock.void) (h2 : S2 ≠ Sock.void) :
    So.knit S1 S2 = Sock.dunno ∨ (So.hed (So.knit S1 S2) = S1 ∧ So.tel (So.knit S1 S2) = S2) := by
  cases S1 with
  | void => exact absurd rfl h1
  | mk l d1 =>
    cases S2 with
    | void => exact absurd rfl h2
    | mk r d2 =>
      simp only [So.knit]
      split
      · exact Or.inl rfl
      · rename_i hc
        rw [con_ne_no hc]
        exact Or.inr ⟨rfl, rfl⟩

theorem sockAt_dunno_eq : ∀ π, sockAt Sock.dunno π = Sock.dunno := sockAt_dunno

theorem sockAt_knit_cons {S1 S2 : Sock} (h1 : S1 ≠ Sock.void) (h2 : S2 ≠ Sock.void) (b : Bool)
    (ρ : List Bool) :
    sockAt (So.knit S1 S2) (b :: ρ) = Sock.dunno ∨
      sockAt (So.knit S1 S2) (b :: ρ) = sockAt (if b then S2 else S1) ρ := by
  rcases knit_parts h1 h2 with he | ⟨eh, et⟩
  · left; rw [he]; exact sockAt_dunno _
  · right; cases b
    · show sockAt (So.hed _) ρ = _; rw [eh]; rfl
    · show sockAt (So.tel _) ρ = _; rw [et]; rfl

theorem knit_cellish {S1 S2 : Sock} (h1 : S1 ≠ Sock.void) (h2 : S2 ≠ Sock.void) :
    Cellish (So.knit S1 S2) := by
  cases S1 with
  | void => exact absurd rfl h1
  | mk l d1 =>
    cases S2 with
    | void => exact absurd rfl h2
    | mk r d2 =>
      simp only [So.knit]
      split
      · exact trivial
      · rename_i hc
        rw [con_ne_no hc]
        exact trivial

theorem sockAt_no (d : Noun) : ∀ π, ∃ d', sockAt (Sock.mk Cape.no d) π = Sock.mk Cape.no d'
  | [] => ⟨d, rfl⟩
  | false :: π => ⟨A 0, by show sockAt Sock.dunno π = _; rw [sockAt_dunno]; rfl⟩
  | true :: π => ⟨A 0, by show sockAt Sock.dunno π = _; rw [sockAt_dunno]; rfl⟩

theorem sockAt_void_inv {S : Sock} {π : List Bool} (h : sockAt S π ≠ Sock.void) : S ≠ Sock.void := by
  intro e; subst e; exact h (sockAt_void π)

theorem hed_void_inv {T : Sock} (h : So.hed T = Sock.void) : T = Sock.void :=
  Classical.byContradiction fun hT => hed_ne_void hT h

theorem tel_void_inv {T : Sock} (h : So.tel T = Sock.void) : T = Sock.void :=
  Classical.byContradiction fun hT => tel_ne_void hT h

theorem GenLe.void_inv {T S : Sock} (h : GenLe T S) : S = Sock.void → T = Sock.void := by
  induction h with
  | refl => exact id
  | no => intro h; cases h
  | knit _ _ ih1 ih2 =>
    intro h
    rcases knit_void_inv h with e | e
    · exact hed_void_inv (ih1 e)
    · exact tel_void_inv (ih2 e)

/-- A generalization is one at every part. -/
theorem GenLe.part {T S : Sock} (h : GenLe T S) : ∀ ρ, GenLe (sockAt T ρ) (sockAt S ρ) := by
  induction h with
  | refl T => intro ρ; exact GenLe.refl _
  | no T d =>
    intro ρ
    obtain ⟨d', e⟩ := sockAt_no d ρ
    rw [e]; exact GenLe.no _ _
  | @knit T S1 S2 h1 h2 ih1 ih2 =>
    intro ρ
    cases ρ with
    | nil => exact GenLe.knit h1 h2
    | cons b ρ =>
      by_cases hv : S1 = Sock.void ∨ S2 = Sock.void
      · have hT : T = Sock.void := by
          rcases hv with e | e
          · exact hed_void_inv (h1.void_inv e)
          · exact tel_void_inv (h2.void_inv e)
        subst hT
        have : So.knit S1 S2 = Sock.void := by
          rcases hv with e | e
          · rw [e]; cases S2 <;> rfl
          · rw [e]; cases S1 <;> rfl
        simp only [this, sockAt_void]
        exact GenLe.refl _
      · simp only [not_or] at hv
        rcases sockAt_knit_cons hv.1 hv.2 b ρ with e | e
        · rw [e]; exact GenLe.no _ _
        · rw [e]
          cases b
          · exact ih1 ρ
          · exact ih2 ρ

/-- A generalization holds of every noun, maybe absent, of the sock it
generalizes. -/
theorem GenLe.fitsOpt {T S : Sock} (h : GenLe T S) : ∀ o, FitsOpt T o → FitsOpt S o := by
  induction h with
  | refl T => exact fun _ h => h
  | no T d => intro o _; exact fitsOpt_blank ⟨Cape.no, d, rfl, rfl⟩ o
  | @knit T S1 S2 h1 h2 ih1 ih2 =>
    intro o hf
    have hb : T.Blank → (So.knit S1 S2).Blank := fun hT =>
      knit_blank (ih1 none (hed_blank hT)) (ih2 none (tel_blank hT))
    cases o with
    | none => exact hb hf
    | some n =>
      cases n with
      | cell a b =>
        exact knit_fits (ih1 (some a) (hed_fits hf)) (ih2 (some b) (tel_fits hf))
      | atom k =>
        cases T with
        | void => exact absurd hf id
        | mk c d =>
          obtain ⟨bh, bt⟩ := hed_tel_blank_of_atom (k := k) hf
          exact (knit_blank (ih1 none bh) (ih2 none bt)).fits _

theorem GenLe.toPosLe {T S : Sock} (h : GenLe T S) : PosLe T S :=
  fun ρ o hf => (h.part ρ).fitsOpt o hf

theorem GenLe.blank {T S : Sock} (h : GenLe T S) (hT : T.Blank) : S.Blank := h.fitsOpt none hT

theorem GenLe.cellish {T S : Sock} (h : GenLe T S) : Cellish T → Cellish S := by
  induction h with
  | refl T => exact id
  | no T d => intro _; exact trivial
  | @knit T S1 S2 h1 h2 _ _ =>
    intro hc
    by_cases hv : S1 = Sock.void ∨ S2 = Sock.void
    · have hT : T = Sock.void := by
        rcases hv with e | e
        · exact hed_void_inv (h1.void_inv e)
        · exact tel_void_inv (h2.void_inv e)
      subst hT; exact absurd hc id
    · simp only [not_or] at hv
      exact knit_cellish hv.1 hv.2

theorem GenLe.trans {R S U : Sock} (h1 : GenLe R S) (h2 : GenLe S U) : GenLe R U := by
  induction h2 generalizing R with
  | refl => exact h1
  | no => exact GenLe.no _ _
  | knit _ _ ih1 ih2 => exact GenLe.knit (ih1 (h1.part [false])) (ih2 (h1.part [true]))

/-! ## The static condition -/

/-- **The static condition** of `[S σ]` in a function on the subject sock
`T`, for a sock that is not `%void`. -/
structure StatOK (T S : Sock) (σ : Noun) : Prop where
  stat : S ≠ Sock.void → ∀ π b, springAt σ π = A b → b ≠ 0 →
    ∃ q, axisPath b = some q ∧ GenLe (sockAt T q) (sockAt S π)
  shape : S ≠ Sock.void → ∀ π, isCellN (springAt σ π) = true → Cellish (sockAt S π)

theorem StatOK.toStatS {T S : Sock} {σ : Noun} (h : StatOK T S σ) (hne : S ≠ Sock.void) :
    StatS T S σ := fun π b e hb =>
  let ⟨q, hq, hg⟩ := h.stat hne π b e hb
  ⟨q, hq, hg.toPosLe⟩

theorem StatOK.toShapeOK {T S : Sock} {σ : Noun} (h : StatOK T S σ) (hne : S ≠ Sock.void) :
    ShapeOK S σ := h.shape hne

theorem statOK_void (T : Sock) (σ : Noun) : StatOK T Sock.void σ :=
  ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩

theorem statOK_zero (T S : Sock) : StatOK T S (A 0) where
  stat := fun _ π b e hb => by rw [springAt_zero] at e; cases e; exact absurd rfl hb
  shape := fun _ π e => by rw [springAt_zero] at e; cases e

theorem statOK_no (T : Sock) (d σ : Noun) : StatOK T (Sock.mk Cape.no d) σ where
  stat := fun _ π b _ hb => by
    obtain ⟨q, hq⟩ := axisPath_pos b (by omega)
    obtain ⟨d', e⟩ := sockAt_no d π
    exact ⟨q, hq, by rw [e]; exact GenLe.no _ _⟩
  shape := fun _ π _ => by
    obtain ⟨d', e⟩ := sockAt_no d π
    rw [e]; exact trivial

theorem statOK_dunno (T : Sock) (σ : Noun) : StatOK T Sock.dunno σ := statOK_no T (A 0) σ

theorem StatOK.part {T S : Sock} {σ : Noun} (h : StatOK T S σ) (π : List Bool) :
    StatOK T (sockAt S π) (springAt σ π) where
  stat := fun hne ρ b e hb => by
    obtain ⟨q, hq, hg⟩ := h.stat (sockAt_void_inv hne) (π ++ ρ) b (by rw [springAt_app]; exact e) hb
    exact ⟨q, hq, by rw [← sockAt_app]; exact hg⟩
  shape := fun hne ρ e => by
    rw [← sockAt_app]
    exact h.shape (sockAt_void_inv hne) (π ++ ρ) (by rw [springAt_app]; exact e)

theorem StatOK.congr {T S : Sock} {σ σ' : Noun} (he : ∀ π, springAt σ' π = springAt σ π)
    (h : StatOK T S σ) : StatOK T S σ' where
  stat := fun hne π b e hb => h.stat hne π b (by rw [← he]; exact e) hb
  shape := fun hne π e => h.shape hne π (by rw [← he]; exact e)

/-- **Nock 0 keeps the static condition.** -/
theorem statOK_slot {T S : Sock} {σ : Noun} {b : Nat} {q : List Bool} (h : StatOK T S σ)
    (hb : 1 ≤ b) (hq : axisPath b = some q) : StatOK T (sockAt S q) (Pi.slot σ b) :=
  (h.part q).congr fun π => by rw [springAt_slot b σ q π hb hq, springAt_app]

/-- The part of the subject at an axis, as the function's subject sock knows
it. -/
theorem statOK_axis (T : Sock) {a : Nat} {q : List Bool} (ha : a ≠ 0) (hq : axisPath a = some q) :
    StatOK T (sockAt T q) (A a) where
  stat := fun _ π b e _ => by
    rw [springAt_atom a π ha] at e
    cases e
    exact ⟨q ++ π, axisPath_pegPath a π q (by omega) hq, by rw [sockAt_app]; exact GenLe.refl _⟩
  shape := fun _ π e => by rw [springAt_atom a π ha] at e; cases e

/-- The subject `[T 1]` of a function. -/
theorem statOK_top (T : Sock) : StatOK T T (A 1) := statOK_axis T (q := []) (by omega) rfl

/-- **A cons keeps the static condition.** -/
theorem statOK_knit {T Sl Sr : Sock} {σl σr : Noun} (hl : StatOK T Sl σl) (hr : StatOK T Sr σr) :
    StatOK T (So.knit Sl Sr) (Pi.cons σl σr) := by
  have hv : So.knit Sl Sr ≠ Sock.void → Sl ≠ Sock.void ∧ Sr ≠ Sock.void := fun hne =>
    ⟨fun e => hne (by rw [e]; cases Sr <;> rfl), fun e => hne (by rw [e]; cases Sl <;> rfl)⟩
  constructor
  · intro hne π b e hb
    obtain ⟨h1, h2⟩ := hv hne
    cases π with
    | nil => exact absurd (cons_ne_atom e).1 hb
    | cons c ρ =>
      rw [springAt_cons_cons] at e
      have key : ∀ (S : Sock) (σ : Noun), StatOK T S σ → S ≠ Sock.void → springAt σ ρ = A b →
          (sockAt (So.knit Sl Sr) (c :: ρ) = Sock.dunno ∨ sockAt (So.knit Sl Sr) (c :: ρ) = sockAt S ρ) →
          ∃ q, axisPath b = some q ∧ GenLe (sockAt T q) (sockAt (So.knit Sl Sr) (c :: ρ)) := by
        intro S σ hS hne' e' hc
        obtain ⟨q, hq, hg⟩ := hS.stat hne' ρ b e' hb
        refine ⟨q, hq, ?_⟩
        rcases hc with hc | hc
        · rw [hc]; exact GenLe.no _ _
        · rw [hc]; exact hg
      cases c
      · exact key Sl σl hl h1 e (by simpa using sockAt_knit_cons h1 h2 false ρ)
      · exact key Sr σr hr h2 e (by simpa using sockAt_knit_cons h1 h2 true ρ)
  · intro hne π e
    obtain ⟨h1, h2⟩ := hv hne
    cases π with
    | nil => exact knit_cellish h1 h2
    | cons c ρ =>
      rw [springAt_cons_cons] at e
      rcases sockAt_knit_cons h1 h2 c ρ with hc | hc
      · rw [hc]; exact trivial
      · rw [hc]
        cases c
        · exact hl.shape h1 ρ e
        · exact hr.shape h2 ρ e

/-- A cons of provenances over a sock that may stand for a cell. -/
theorem statOK_cons_cellish {T S : Sock} {x z : Noun} (hc : S ≠ Sock.void → Cellish S)
    (hl : StatOK T (So.hed S) x) (hr : StatOK T (So.tel S) z) : StatOK T S (Pi.cons x z) where
  stat := fun hne π b e hb => by
    cases π with
    | nil => exact absurd (cons_ne_atom e).1 hb
    | cons c ρ =>
      rw [springAt_cons_cons] at e
      cases c
      · exact hl.stat (hed_ne_void hne) ρ b e hb
      · exact hr.stat (tel_ne_void hne) ρ b e hb
  shape := fun hne π e => by
    cases π with
    | nil => exact hc hne
    | cons c ρ =>
      rw [springAt_cons_cons] at e
      cases c
      · exact hl.shape (hed_ne_void hne) ρ e
      · exact hr.shape (tel_ne_void hne) ρ e

/-- The product of a cons in `fol-loop`. -/
theorem statOK_consProd {T : Sock} {l r : FolOut} (hl : StatOK T l.prod.sock l.prod.src)
    (hr : StatOK T r.prod.sock r.prod.src) :
    StatOK T (consProd l r).1.sock (consProd l r).1.src := by
  unfold consProd
  split
  · exact statOK_zero _ _
  · exact statOK_knit hl hr

/-- A generalization of the sock keeps the static condition. -/
theorem StatOK.mono {T S S' : Sock} {σ : Noun} (h : StatOK T S σ) (hg : GenLe S S')
    (hne : S ≠ Sock.void) : StatOK T S' σ where
  stat := fun _ π b e hb =>
    let ⟨q, hq, h'⟩ := h.stat hne π b e hb
    ⟨q, hq, h'.trans (hg.part π)⟩
  shape := fun _ π e => (hg.part π).cellish (h.shape hne π e)

/-- **`+compose:pi` keeps the static condition**: the call's subject `[S σ]`
satisfies it in the caller on `T`, and the callee's product `[P m]`
satisfies it in the callee on `S`. -/
theorem statOK_compose {T S P : Sock} {σ m : Noun} (hS : S ≠ Sock.void) (hy : StatOK T S σ)
    (hp : StatOK S P m) : StatOK T P (Pi.compose m σ) := by
  rw [compose_eq]
  suffices H : ∀ m' π, springAt m π = m' → StatOK T (sockAt P π) (Pi.composeLoop σ m') by
    exact H m [] rfl
  intro m'
  induction m' with
  | atom b =>
    intro π e
    cases b with
    | zero => exact statOK_zero _ _
    | succ k =>
      by_cases hP : P = Sock.void
      · subst hP; rw [sockAt_void]; exact statOK_void _ _
      obtain ⟨q, hq, hg⟩ := hp.stat hP π (k + 1) e (by omega)
      exact (statOK_slot hy (by omega) hq).mono hg (sockAt_ne_void q hS)
  | cell h t ih1 ih2 =>
    intro π e
    apply statOK_cons_cellish
    · intro hne
      exact hp.shape (sockAt_void_inv hne) π (by rw [e]; rfl)
    · have := ih1 (π ++ [false]) (by rw [springAt_app, e]; rfl)
      rwa [sockAt_app] at this
    · have := ih2 (π ++ [true]) (by rw [springAt_app, e]; rfl)
      rwa [sockAt_app] at this

/-! ## `+double-int` -/

theorem statOK_doubleInt_left' {T : Sock} : ∀ (k : Nat) (a b : Anno),
    Sock.msr a.sock + Sock.msr b.sock < k → a.sock ≠ Sock.void → StatOK T a.sock a.src →
      StatOK T (doubleInt a b).sock (doubleInt a b).src := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hne hp
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact hp
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => exact absurd rfl hne
  | mk ca da =>
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact hp
  | mk cb db =>
    apply doubleInt_cases (fun r => StatOK T r.sock r.src) hab (statOK_dunno _ _)
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    exact statOK_knit (ih _ _ h1 (hed_ne_void hne) (hp.part [false]))
      (ih _ _ h2 (tel_ne_void hne) (hp.part [true]))

theorem statOK_doubleInt_right' {T : Sock} : ∀ (k : Nat) (a b : Anno),
    Sock.msr a.sock + Sock.msr b.sock < k → b.sock ≠ Sock.void → StatOK T b.sock b.src →
      StatOK T (doubleInt a b).sock (doubleInt a b).src := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hne hp
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact hp
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sb with
  | void => exact absurd rfl hne
  | mk cb db =>
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact hp
  | mk ca da =>
    apply doubleInt_cases (fun r => StatOK T r.sock r.src) hab (statOK_dunno _ _)
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    exact statOK_knit (ih _ _ h1 (hed_ne_void hne) (hp.part [false]))
      (ih _ _ h2 (tel_ne_void hne) (hp.part [true]))

/-- **`+double-int` keeps the static condition of a side that is not
`%void`**: an axis provenance survives only where both sides agree. -/
theorem statOK_doubleInt_left {T : Sock} (a b : Anno) (hne : a.sock ≠ Sock.void)
    (h : StatOK T a.sock a.src) : StatOK T (doubleInt a b).sock (doubleInt a b).src :=
  statOK_doubleInt_left' _ a b (Nat.lt_succ_self _) hne h

theorem statOK_doubleInt_right {T : Sock} (a b : Anno) (hne : b.sock ≠ Sock.void)
    (h : StatOK T b.sock b.src) : StatOK T (doubleInt a b).sock (doubleInt a b).src :=
  statOK_doubleInt_right' _ a b (Nat.lt_succ_self _) hne h

/-! ## Nock 10 -/

/-- The siblings left on the way down, each with the static condition. -/
inductive CtxStat (T : Sock) : List (Nat × Sock) → List (Nat × Noun) → Prop where
  | nil : CtxStat T [] []
  | cons {k : Nat} {s : Sock} {p : Noun} {acc tack} : StatOK T s p → CtxStat T acc tack →
      CtxStat T ((k, s) :: acc) ((k, p) :: tack)

theorem statOK_up {T : Sock} : ∀ {acc : List (Nat × Sock)} {tack : List (Nat × Noun)} {two : Sock}
    {don : Noun}, CtxStat T acc tack → StatOK T two don →
    StatOK T (So.darnUp two acc) (Pi.editUp don tack)
  | [], [], _, _, CtxStat.nil, h => h
  | (k, s) :: acc, (_, p) :: tack, two, don, CtxStat.cons hs hrest, h => by
    rw [darnUp_eq, editUp_eq]
    split
    · exact statOK_up hrest (statOK_knit h hs)
    · exact statOK_up hrest (statOK_knit hs h)

theorem statOK_darnDown {T : Sock} : ∀ (ax : Nat) (one two : Sock) (rec don : Noun)
    (acc : List (Nat × Sock)) (tack : List (Nat × Noun)) (s : Sock),
    StatOK T one rec → StatOK T two don → CtxStat T acc tack →
    So.darnDown one ax two acc = some s → StatOK T s (Pi.editDown rec ax don tack) := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro one two rec don acc tack s h1 h2 hc hd
  rw [So.darnDown.eq_def] at hd
  split at hd
  · rename_i hstop
    simp only [Option.some.injEq] at hd
    subst hd
    rcases Nat.lt_or_ge ax 1 with h0 | hax1
    · have : ax = 0 := by omega
      subst this
      rw [Pi.editDown.eq_def]; simp only [if_neg (by omega : (0 : Nat) ≠ 1), dif_pos (by omega : (0 : Nat) < 2)]
      exact statOK_zero _ _
    rw [editDown_eq _ _ _ _ hax1]
    apply statOK_up hc
    rcases hstop with rfl | ⟨_, hno⟩
    · rw [editAt.eq_def]; simpa using h2
    · cases two with
      | void => exact statOK_void _ _
      | mk c d =>
        cases c with
        | no => exact statOK_no _ _ _
        | yes => simp [Sock.isNo] at hno
        | cell _ _ => simp [Sock.isNo] at hno
  · rename_i hstop
    split at hd
    · simp at hd
    · rename_i h0
      have h2' : 2 ≤ ax := by omega
      have hlt := mas_lt ax h2'
      rw [Pi.editDown.eq_def, if_neg (by omega), dif_neg (by omega)]
      split at hd
      · rename_i hcap
        rw [if_pos hcap]
        exact ih _ hlt _ _ (Pi.hed rec) don _ ((2, Pi.tel rec) :: tack) s (h1.part [false]) h2
          (CtxStat.cons (h1.part [true]) hc) hd
      · rename_i hcap
        rw [if_neg hcap]
        exact ih _ hlt _ _ (Pi.tel rec) don _ ((3, Pi.hed rec) :: tack) s (h1.part [true]) h2
          (CtxStat.cons (h1.part [false]) hc) hd

/-- **Nock 10 keeps the static condition**: `+darn:so` with `+edit:pi`. -/
theorem statOK_darn {T one two s : Sock} {rec don : Noun} {ax : Nat}
    (h1 : StatOK T one rec) (h2 : StatOK T two don) (hd : So.darn one ax two = some s) :
    StatOK T s (Pi.edit rec ax don) := by
  unfold So.darn at hd
  unfold Pi.edit
  split at hd
  · rename_i hax
    subst hax
    simp only [Option.some.injEq] at hd
    subst hd
    simpa using h2
  · rename_i hax
    rw [if_neg hax]
    split at hd
    · simp only [Option.some.injEq] at hd; subst hd; exact statOK_void _ _
    · split at hd
      · simp only [Option.some.injEq] at hd; subst hd; exact statOK_dunno _ _
      · split
        · exact statOK_zero _ _
        · exact statOK_darnDown ax one two rec don [] [] s h1 h2 CtxStat.nil hd

/-! ## `+patch-prod` -/

/-- **`+patch-prod` makes a product that satisfies the static condition on
the subject sock it patches for**: a part with an axis provenance is what
that sock knows there. -/
theorem statOK_patchProd {new : Sock} : ∀ (σ : Noun) (S : Sock),
    StatOK new (patchProd S σ new).sock (patchProd S σ new).src := by
  intro σ
  induction σ with
  | atom a =>
    intro S
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; exact statOK_zero _ _
    by_cases hS : S = Sock.void
    · subst hS; rw [patchProd]; split <;> exact statOK_void _ _
    rw [patchProd_atom new ha hS]
    obtain ⟨q, hq⟩ := axisPath_pos a (by omega)
    rw [pull_eq_sockAt (by omega) hq]
    exact statOK_axis new ha hq
  | cell h t ih1 ih2 =>
    intro S
    by_cases hS : S = Sock.void
    · subst hS; rw [patchProd]; simp; exact statOK_void _ _
    rw [patchProd_cell new hS]
    exact statOK_knit (ih1 _) (ih2 _)

end SkaModel
end Formalization
