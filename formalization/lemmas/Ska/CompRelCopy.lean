import lemmas.Ska.CompRelSix

/-!
# The copy block keeps the merged need

README Gaps 12.2, a step toward `binaryN_ok` with the relaxed `sem`.  With
the relaxed hypothesis the input registers may lie in the merged need of
`+copy` (in `[5 [0 2] [0 3]]` the whole's sure need is `pair rp rq`), and
`copy_ok` keeps only the registers outside both needs it fills.  The ops of
the copy write only registers of the two needs outside the merged need
(`wr_copyNeed`), and a run of ops changes no register they do not write
(`runs_read`, for a register that holds a value after the ops), so the copy
block keeps every register of the merged need (`copy_okR`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem holdsN_some : ∀ (n : Need) {R : Map (Option Noun)} {s : Noun} {y : Nat}, HoldsN n R s → NMem n y →
    SkaModel.read y R ≠ none
  | Need.none, _, _, _, _, hm => hm.elim
  | Need.this r, _, _, _, h, hm => by
    simp only [NMem] at hm; subst hm; simp only [HoldsN] at h; rw [h]; simp
  | Need.pair p q, _, Noun.cell a b, _, h, hm => by
    simp only [HoldsN] at h
    rcases hm with hm | hm
    · exact holdsN_some p h.1 hm
    · exact holdsN_some q h.2 hm
  | Need.pair _ _, _, Noun.atom _, _, h, _ => h.elim
  | Need.both r p q, _, Noun.cell a b, _, h, hm => by
    simp only [HoldsN] at h
    rcases hm with hm | hm | hm
    · subst hm; rw [h.1]; simp
    · exact holdsN_some p h.2.1 hm
    · exact holdsN_some q h.2.2 hm
  | Need.both _ _ _, _, Noun.atom _, _, h, _ => h.elim

section Ops
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- Ops that do not write `y`, ending in `%don y` with a product, return
the value `y` held before them. -/
theorem execOps_don_zero {Q : Nat → Prop} {y : Nat} (hy : ¬ Q y) :
    ∀ (A : List Pole) (st : σ) (R : Map (Option Noun)) (t : Trace) (w : Noun) (st' : σ), OpsWr Q A →
      execBlob lib O c gul st R t ⟨[], A, Termin.don y⟩ [] = some (Tone.zero w, st') →
      SkaModel.read y R = some w
  | [], st, R, t, w, st', _, h => by
    rw [execBlob_don'] at h
    cases e : SkaModel.read y R with
    | none => rw [e] at h; cases h
    | some v =>
      rw [e] at h
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Tone.zero.injEq] at h
      rw [h.1]
  | p :: A, st, R, t, w, st', hA, h => by
    rw [execBlob_cons] at h
    cases e : execPole lib O gul st p R t with
    | none => rw [e] at h; cases h
    | some x =>
      obtain ⟨ton, R1, t1, st1⟩ := x
      rw [e, Option.bind_some] at h
      cases ton with
      | zero v =>
        have ih := execOps_don_zero hy A st1 R1 t1 w st' (fun q hq => hA q (List.mem_cons_of_mem _ hq)) h
        have fr := execPole_frame lib O gul e y (fun hm => hy (hA p List.mem_cons_self y hm))
        simp only [SkaModel.read, fr] at ih ⊢
        exact ih
      | one v => simp at h
      | two v => simp at h

/-- **A run of ops keeps a register it does not write**, when the register
holds a value after the ops. -/
theorem runs_read {Q : Nat → Prop} {A : List Pole} {st : σ} {t : Trace} {R R' : Map (Option Noun)} {y : Nat}
    (hA : OpsWr Q A) (hy : ¬ Q y) (h : Runs lib O c gul st t A R R') (hs : SkaModel.read y R' ≠ none) :
    SkaModel.read y R' = SkaModel.read y R := by
  have e := h [] (Termin.don y)
  rw [List.append_nil, execBlob_don'] at e
  cases e' : SkaModel.read y R' with
  | none => exact absurd e' hs
  | some w =>
    rw [e', Option.bind_some] at e
    exact (execOps_don_zero hy A st R t w st hA e).symm

end Ops

/-- **`copy_ok` with the merged need kept**: the copy block changes no
register of the merged need. -/
theorem copy_okR {first : Next S} {second : Sure S} {g g' : Gen Map} {nex : Next S}
    (h : copy first second g = some (nex, g')) (P : CopyPre first.laz.ned second.ned g.re)
    (hd : g.drop = false) (c : Straight Map) (hc : Agree c g g') (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ)
    (R : Map (Option Noun)) (t : Trace) (gul : Noun) (s : Noun) (hs : HoldsS nex.laz R s) :
    ∃ R', HoldsS first.laz R' s ∧ HoldsS second R' s ∧
      (∀ y, ¬ NMem first.laz.ned y → ¬ NMem second.ned y → SkaModel.read y R' = SkaModel.read y R) ∧
      (∀ y, NMem nex.laz.ned y → SkaModel.read y R' = SkaModel.read y R) ∧
      goJ lib O c gul st R t nex.th = goJ lib O c gul st R' t first.th := by
  have h0 := h
  simp only [copy] at h
  obtain ⟨o, g0, h0', h⟩ := bind_some h
  rw [emit_apply] at h0'
  simp only [Option.some.injEq, Prod.mk.injEq] at h0'
  obtain ⟨rfl, rfl⟩ := h0'
  obtain ⟨laz, g1, h1', h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [copyLazy] at h1'
  obtain ⟨⟨n1, o1⟩, g2, h2, h1'⟩ := bind_some h1'
  obtain ⟨_, g3, h3, h1'⟩ := bind_some h1'
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl⟩ := h1'
  obtain ⟨Aops, eA, O1⟩ := copyNeed_spec _ _ _ _ _ _ h2
  obtain ⟨Bops, eB, W⟩ := wr_copyNeed _ _ _ _ _ _ h2 P.d (fun y hy => P.lo y (Or.inl hy))
    (fun y hy => P.lo y (Or.inr hy))
  simp only [List.append_nil] at eA eB
  rw [eA] at eB
  subst eB
  subst eA
  simp only at O1 W
  obtain ⟨-, -, bo3, -, -⟩ := copy_ok h0
  have hd2 : g2.drop = false := by rw [O1.gen]; exact hd
  have F3 := front_addOps h3 hd2
  have hb2 : HoonMap.get g2.blocks g.bo = some ⟨[], [], Termin.hop first.th⟩ := by
    rw [O1.gen]; exact emitted_get g _ hd
  have hb := (hc g.bo (Nat.le_refl _) (by rw [bo3]; omega)).trans (F3.blk _ _ hb2)
  obtain ⟨_, _, _, CS⟩ := O1.sem P
  obtain ⟨R', r1, hl, hr, u⟩ := CS lib σ O c gul st t R s hs.1
  have lk := (looks_uni _ _ s).mp hs.2
  refine ⟨R', ⟨hl, lk.1⟩, ⟨hr, lk.2⟩, fun y n1 n2 => u y (fun hm => hm.elim n1 n2), fun y hy => ?_, ?_⟩
  · by_cases hm : NMem first.laz.ned y ∨ NMem second.ned y
    · have hne : SkaModel.read y R' ≠ none := by
        rcases hm with hm | hm
        · exact holdsN_some _ hl hm
        · exact holdsN_some _ hr hm
      exact runs_read W (fun hq => hq.2 hy) r1 hne
    · exact u y hm
  · rw [goJ_jmp0 _ _ _ _ hb, r1, execBlob_hop]

end Comp
end SkaModel
end Formalization
