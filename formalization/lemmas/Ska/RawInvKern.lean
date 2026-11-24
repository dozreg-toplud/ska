import lemmas.Ska.RawInvOutMain

/-!
# Raw `+comp` output: the prologue of the final pass

README Gaps 14.  The ops that the final pass puts in front of the run's
entry: `+kern-need` (`kernLoop_raw`, through `kernBoth_raw`) takes the noun
in one register apart into the registers of a need, defining each of them
once and fresh ones, and reads first only that register; `+sure-loop`
(`raw_sureLoop`) does it from the input need's registers into the target
need's, and reads first only input registers.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- What the ops `A` of `+kern-need` from register `r` into `tgt` are. -/
structure KR (tgt : Need) (r : Nat) (g g' : Comp.Gen Map) (A : List Pole) : Prop where
  gen : g' = { g with re := g'.re }
  le : g.re ≤ g'.re
  nd : (defsOf A).Nodup
  defs : ∀ y ∈ defsOf A, NMem tgt y ∨ (g.re ≤ y ∧ y < g'.re)
  cov : ∀ y, NMem tgt y → y ∈ defsOf A
  rf : ∀ y, OpsRF A y → y = r
  tr : ∀ op ∈ A, trOp op = false
  regs : RegsIn (· < g'.re) A
  nsrc : r ∉ defsOf A

theorem opsRF_mov_cons {s d y : Nat} {A : List Pole} (h : OpsRF (Pole.mov s d :: A) y) :
    y = s ∨ (y ≠ d ∧ OpsRF A y) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (reads_mov.mp h)
  · exact Or.inr ⟨fun e => h1 (by simp [aliasDst, e]), h2⟩

/-- A part behind its `%hed` or `%tal`: reads first only the source `d` of
the step, which the ops before wrote. -/
theorem opsRF_part {d x y : Nat} {B : List Pole} {mk : Nat → Nat → Pole} (hmk : ∀ z, z ∈ aliasReads (mk d x) ↔ z = d)
    (hdst : aliasDst (mk d x) = some x) (hB : ∀ z, OpsRF B z → z = x)
    (h : OpsRF (if B = [] then [] else mk d x :: B) y) : y = d := by
  split at h
  · exact h.elim
  · rcases h with h | ⟨h1, h2⟩
    · exact (hmk y).mp h
    · exact absurd (hB y h2) (fun e => h1 (by rw [hdst, e]))

theorem defsOf_part {d x : Nat} {B : List Pole} {mk : Nat → Nat → Pole} (hdst : aliasDst (mk d x) = some x) {y : Nat} :
    y ∈ defsOf (if B = [] then [] else mk d x :: B) ↔ B ≠ [] ∧ (y = x ∨ y ∈ defsOf B) := by
  split
  · rename_i hb; simp [defsOf, hb]
  · rename_i hb; simp [defsOf_cons, hdst, hb, eq_comm]

/-- **The case `%both` of the loop of `+kern-need`.** -/
theorem kernBoth_raw {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)} {h t : Need}
    {acc ops : List Pole} {g g' : Comp.Gen Map}
    (Kh : ∀ x acc g g' ops, kh x acc g = some (ops, g') → x < g.re → ¬ NMem h x → NB g.re h →
      ∃ A, ops = A ++ acc ∧ KR h x g g' A)
    (Kt : ∀ x acc g g' ops, kt x acc g = some (ops, g') → x < g.re → ¬ NMem t x → NB g.re t →
      ∃ A, ops = A ++ acc ∧ KR t x g g' A)
    (ap : ∀ y, NMem h y → ¬ NMem t y) (ndh : ¬ NMem h d) (ndt : ¬ NMem t d) (bh : NB g.re h) (bt : NB g.re t)
    (hd : d < g.re) (hr : r < g.re) (hrh : ¬ NMem h r) (hrt : ¬ NMem t r)
    (hk : kernBoth r d kh kt acc g = some (ops, g')) :
    ∃ A, ops = A ++ acc ∧ KR (Need.both d h t) r g g' A := by
  simp only [kernBoth] at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨ops1, g2, h2, hk⟩ := bind_some hk
  obtain ⟨At, eAt, Kt'⟩ := Kt _ _ _ _ _ h2 (by simp) (fun e => by have := bt _ e; simp at this) (bt.mono (by simp))
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  rw [re_apply] at h3; simp only [Option.some.injEq, Prod.mk.injEq] at h3; obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨ops3, g4, h4, hk⟩ := bind_some hk
  have l2 := Kt'.le
  simp only at l2
  have hrt' : ¬ NMem h g2.re := fun e => by have := bh _ e; omega
  obtain ⟨Ah, eAh, Kh'⟩ := Kh _ _ _ _ _ h4 (by simp) hrt' (bh.mono (by simp; omega))
  have l4 := Kh'.le
  simp only at l4
  by_cases hrd : r = d
  · simp [hrd] at hk; cases hk
  simp only [hrd, if_false, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  -- the shape
  have eT : (if ops1 ≠ acc then Pole.tal d g.re :: ops1 else ops1) =
      (if At = [] then [] else Pole.tal d g.re :: At) ++ acc := by
    rw [eAt]; by_cases e : At = [] <;> simp [e, app_eq_self]
  rw [eT] at eAh
  have eH : (if ops3 ≠ (if At = [] then [] else Pole.tal d g.re :: At) ++ acc then Pole.hed d g2.re :: ops3 else ops3) =
      (if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++ ((if At = [] then [] else Pole.tal d g.re :: At) ++ acc) := by
    rw [eAh]; by_cases e : Ah = [] <;> simp [e, app_eq_self]
  rw [eT, eH]
  refine ⟨Pole.mov r d :: Pole.cel d :: ((if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++
    (if At = [] then [] else Pole.tal d g.re :: At)), by simp, ?_⟩
  have g4e : g4 = { g with re := g4.re } := by
    rw [Kh'.gen, Kt'.gen]
  have dT : ∀ y, y ∈ defsOf (if At = [] then [] else Pole.tal d g.re :: At) →
      NMem t y ∨ (g.re ≤ y ∧ y < g2.re) := fun y hy => by
    rcases (defsOf_part (mk := Pole.tal) rfl).mp hy with ⟨-, e | e⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · rcases Kt'.defs y e with e' | e'
      · exact Or.inl e'
      · exact Or.inr ⟨by simp at e'; omega, e'.2⟩
  have dH : ∀ y, y ∈ defsOf (if Ah = [] then [] else Pole.hed d g2.re :: Ah) →
      NMem h y ∨ (g2.re ≤ y ∧ y < g4.re) := fun y hy => by
    rcases (defsOf_part (mk := Pole.hed) rfl).mp hy with ⟨-, e | e⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · rcases Kh'.defs y e with e' | e'
      · exact Or.inl e'
      · exact Or.inr ⟨by simp at e'; omega, e'.2⟩
  have ndT : (defsOf (if At = [] then [] else Pole.tal d g.re :: At)).Nodup := by
    split
    · simp [defsOf]
    · rw [defsOf_cons]; simp only [aliasDst, Option.toList_some, List.singleton_append]
      exact List.nodup_cons.mpr ⟨Kt'.nsrc, Kt'.nd⟩
  have ndH : (defsOf (if Ah = [] then [] else Pole.hed d g2.re :: Ah)).Nodup := by
    split
    · simp [defsOf]
    · rw [defsOf_cons]; simp only [aliasDst, Option.toList_some, List.singleton_append]
      exact List.nodup_cons.mpr ⟨Kh'.nsrc, Kh'.nd⟩
  refine ⟨g4e, by omega, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun op hop => ?_, ?_, ?_⟩
  · simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_append,
      List.singleton_append]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, List.nodup_append.mpr ⟨ndH, ndT, fun a ha c hc e => ?_⟩⟩
    · rcases List.mem_append.mp hm with hm | hm
      · rcases dH d hm with e | e
        · exact ndh e
        · omega
      · rcases dT d hm with e | e
        · exact ndt e
        · omega
    · subst e
      rcases dH a ha with e1 | e1 <;> rcases dT a hc with e2 | e2
      · exact ap a e1 e2
      · have := bh a e1; omega
      · have := bt a e2; omega
      · omega
  · simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_append,
      List.singleton_append, List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · exact Or.inl (Or.inl rfl)
    · rcases dH y hy with e | e
      · exact Or.inl (Or.inr (Or.inl e))
      · exact Or.inr ⟨by omega, e.2⟩
    · rcases dT y hy with e | e
      · exact Or.inl (Or.inr (Or.inr e))
      · exact Or.inr ⟨e.1, by omega⟩
  · simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_append,
      List.singleton_append, List.mem_cons, List.mem_append]
    rcases hy with rfl | hy | hy
    · exact Or.inl rfl
    · have := Kh'.cov y hy
      right; left
      have hne : Ah ≠ [] := fun e => by rw [e] at this; simp [defsOf] at this
      exact (defsOf_part (mk := Pole.hed) rfl).mpr ⟨hne, Or.inr this⟩
    · have := Kt'.cov y hy
      right; right
      have hne : At ≠ [] := fun e => by rw [e] at this; simp [defsOf] at this
      exact (defsOf_part (mk := Pole.tal) rfl).mpr ⟨hne, Or.inr this⟩
  · rcases opsRF_mov_cons hy with e | ⟨hyd, hy⟩
    · exact e
    · exfalso
      rcases hy with hy | ⟨-, hy⟩
      · exact hyd (reads_cel.mp hy)
      · rcases opsRF_append.mp hy with e | ⟨-, e⟩
        · exact hyd (opsRF_part (mk := Pole.hed) (fun z => reads_hed) rfl Kh'.rf e)
        · exact hyd (opsRF_part (mk := Pole.tal) (fun z => reads_tal) rfl Kt'.rf e)
  · simp only [List.mem_cons, List.mem_append] at hop
    rcases hop with rfl | rfl | hop | hop
    · rfl
    · rfl
    · split at hop
      · exact absurd hop List.not_mem_nil
      · rcases List.mem_cons.mp hop with rfl | hop
        · rfl
        · exact Kh'.tr op hop
    · split at hop
      · exact absurd hop List.not_mem_nil
      · rcases List.mem_cons.mp hop with rfl | hop
        · rfl
        · exact Kt'.tr op hop
  · refine RegsIn.cons (fun y hy => by simp [Comp.poleRegs] at hy; omega) (RegsIn.cons
      (fun y hy => by simp [Comp.poleRegs] at hy; omega) (RegsIn.append ?_ ?_))
    · split
      · exact RegsIn.nil _
      · exact RegsIn.cons (fun y hy => by simp [Comp.poleRegs] at hy; omega) Kh'.regs
    · split
      · exact RegsIn.nil _
      · exact RegsIn.cons (fun y hy => by simp [Comp.poleRegs] at hy; omega) (Kt'.regs.mono fun y hy => by omega)
  · simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_append,
      List.singleton_append, List.mem_cons, List.mem_append, not_or]
    refine ⟨hrd, fun hm => ?_, fun hm => ?_⟩
    · rcases dH r hm with e | e
      · exact hrh e
      · omega
    · rcases dT r hm with e | e
      · exact hrt e
      · omega

/-- **The loop of `+kern-need`.** -/
theorem kernLoop_raw : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Comp.Gen Map) (ops : List Pole),
    kernLoop r tgt acc g = some (ops, g') → r < g.re → ¬ NMem tgt r → NB g.re tgt → Distinct tgt →
    ∃ A, ops = A ++ acc ∧ KR tgt r g g' A := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h _ _ _ _
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, ⟨rfl, Nat.le_refl _, by simp [defsOf], fun y hy => by simp [defsOf] at hy, fun y hy => hy.elim,
      fun y hy => hy.elim, fun _ h => absurd h List.not_mem_nil, RegsIn.nil _, by simp [defsOf]⟩⟩
  | this d =>
    intro r acc g g' ops h hr hn nb _
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hd := nb d rfl
    refine ⟨[Pole.mov r d], rfl, ⟨rfl, Nat.le_refl _, by simp [defsOf_mov], fun y hy => ?_, fun y hy => ?_,
      fun y hy => ?_, fun op hop => ?_, regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), ?_⟩⟩
    · simp [defsOf_mov] at hy; exact Or.inl hy
    · simp only [NMem] at hy; simp [defsOf_mov, hy]
    · rcases opsRF_mov_cons hy with e' | ⟨-, e'⟩
      · exact e'
      · exact e'.elim
    · simp at hop; subst hop; rfl
    · simp [defsOf_mov]; exact e
  | pair p q ihp ihq =>
    intro r acc g g' ops h hr hn nb dn
    obtain ⟨dp, dq, ap⟩ := dn
    simp only [kernLoop] at h
    obtain ⟨rn, g1, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨A, eA, K⟩ := kernBoth_raw (h := p) (t := q)
      (fun x acc g g' ops hk hx hnx bh => ihp x acc g g' ops hk hx hnx bh dp)
      (fun x acc g g' ops hk hx hnx bt => ihq x acc g g' ops hk hx hnx bt dq) ap
      (fun e => by have := nb _ (Or.inl e); simp at this) (fun e => by have := nb _ (Or.inr e); simp at this)
      (fun y hy => by have := nb y (Or.inl hy); simp; omega) (fun y hy => by have := nb y (Or.inr hy); simp; omega)
      (by simp) (by simp; omega) (fun e => hn (Or.inl e)) (fun e => hn (Or.inr e)) h
    refine ⟨A, eA, ⟨by rw [K.gen], by have := K.le; simp at this; omega, K.nd, fun y hy => ?_,
      fun y hy => K.cov y (Or.inr hy), K.rf, K.tr, K.regs, K.nsrc⟩⟩
    rcases K.defs y hy with e | e
    · rcases e with e | e
      · subst e; exact Or.inr ⟨Nat.le_refl _, by have := K.le; simp at this; omega⟩
      · exact Or.inl e
    · exact Or.inr ⟨by simp at e; omega, e.2⟩
  | both d h t ihh iht =>
    intro r acc g g' ops hk hr hn nb dn
    obtain ⟨dh, dt, ap, ndh, ndt⟩ := dn
    simp only [kernLoop] at hk
    exact kernBoth_raw (h := h) (t := t)
      (fun x acc g g' ops hk hx hnx bh => ihh x acc g g' ops hk hx hnx bh dh)
      (fun x acc g g' ops hk hx hnx bt => iht x acc g g' ops hk hx hnx bt dt) ap ndh ndt
      (fun y hy => nb y (Or.inr (Or.inl hy))) (fun y hy => nb y (Or.inr (Or.inr hy))) (nb d (Or.inl rfl)) hr
      (fun e => hn (Or.inr (Or.inl e))) (fun e => hn (Or.inr (Or.inr e))) hk

/-! ## `+sure-loop` -/

/-- What `+sure-loop` leaves in front of block `o`. -/
def SureR (ned tgt : Need) (g g' : Comp.Gen Map) (o : Nat) (b : Blob) : Prop :=
  SI g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
    (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
    (∀ y, OpsRF A y → NMem ned y) ∧ (∀ y, NMem tgt y → y ∈ defsOf A) ∧
    (∀ y ∈ defsOf A, NMem tgt y ∨ (g.re ≤ y ∧ y < g'.re))

theorem sureR_nil {ned tgt : Need} {g : Comp.Gen Map} {o : Nat} {b : Blob} (h : SI g)
    (hb : HoonMap.get g.blocks o = some b) (ht : ∀ y, ¬ NMem tgt y) : SureR ned tgt g g o b := by
  refine ⟨h, rfl, Nat.le_refl _, [], fun k => ?_, fun y hy => hy.elim, fun y hy => absurd hy (ht y),
    fun y hy => by simp [defsOf] at hy⟩
  by_cases e : k = o
  · subst e; simp [hb, pre_nil]
  · simp [e]

/-- One move into `d` from `r`. -/
theorem sureR_mov {r d : Nat} {ned : Need} {g g' : Comp.Gen Map} {o : Nat} {b : Blob} {u : Unit} (h : SI g)
    (hb : HoonMap.get g.blocks o = some b) (hr : r < g.re) (hd : d < g.re) (hnd : ¬ Defd g.blocks d)
    (hrn : NMem ned r) (ha : addOps o [Pole.mov r d] g = some (u, g')) :
    SI g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧
      (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre [Pole.mov r d] b) else HoonMap.get g.blocks k) := by
  have P : OpsOK g [Pole.mov r d] :=
    ⟨regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), by simp [defsOf_mov],
      fun y hy => by simp [defsOf_mov] at hy; subst hy; exact hnd, fun op hop => by simp at hop; subst hop; rfl⟩
  obtain ⟨S', b', hb', e', q', o'⟩ := si_addOps h P ha
  rw [hb] at hb'; cases hb'
  refine ⟨S', o', by omega, fun k => ?_⟩
  rw [e']; by_cases e : k = o
  · subst e; simp [get_put_self]
  · simp [get_put_ne e, e]

theorem defd_of_ifget {g g1 : Comp.Gen Map} {o : Nat} {b : Blob} {A : List Pole}
    (hb : HoonMap.get g.blocks o = some b)
    (hg : ∀ k, HoonMap.get g1.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) {y : Nat} :
    Defd g1.blocks y ↔ Defd g.blocks y ∨ y ∈ defsOf A := by
  have e : ∀ k, HoonMap.get g1.blocks k = HoonMap.get (HoonMap.put g.blocks o (pre A b)) k := fun k => by
    rw [hg k]; by_cases e : k = o
    · subst e; simp [get_put_self]
    · simp [e, get_put_ne e]
  rw [← defd_prepend hb]
  simp only [defd_iff, e]

/-- **Two loops one after the other at the same block.** -/
theorem sureR_seq {n2 t2 ned tgt : Need} {g g1 g2 : Comp.Gen Map} {o : Nat} {b : Blob} {A1 : List Pole}
    (l1 : g.re ≤ g1.re) (bo1 : g1.bo = g.bo)
    (get1 : ∀ k, HoonMap.get g1.blocks k = if k = o then some (pre A1 b) else HoonMap.get g.blocks k)
    (rf1 : ∀ y, OpsRF A1 y → NMem ned y) (df1 : ∀ y ∈ defsOf A1, NMem tgt y ∨ (g.re ≤ y ∧ y < g1.re))
    (R2 : SureR n2 t2 g1 g2 o (pre A1 b)) (s2 : ∀ y, NMem n2 y → NMem ned y) (u2 : ∀ y, NMem t2 y → NMem tgt y)
    (cov : ∀ y, NMem tgt y → y ∈ defsOf A1 ∨ NMem t2 y) : SureR ned tgt g g2 o b := by
  obtain ⟨S2, bo2, l2, A2, get2, rf2, cv2, df2⟩ := R2
  refine ⟨S2, by omega, by omega, A2 ++ A1, fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [get2, get1]; by_cases e : k = o
    · subst e; simp [pre_pre]
    · simp [e]
  · rcases opsRF_append.mp hy with e | ⟨-, e⟩
    · exact s2 y (rf2 y e)
    · exact rf1 y e
  · rw [defsOf_append, List.mem_append]
    rcases cov y hy with e | e
    · exact Or.inr e
    · exact Or.inl (cv2 y e)
  · rw [defsOf_append, List.mem_append] at hy
    rcases hy with e | e
    · rcases df2 y e with e' | e'
      · exact Or.inl (u2 y e')
      · exact Or.inr ⟨by omega, e'.2⟩
    · rcases df1 y e with e' | e'
      · exact Or.inl e'
      · exact Or.inr ⟨e'.1, by omega⟩

/-- **`+sure-loop`.** -/
theorem raw_sureLoop {o : Nat} : ∀ (ned tgt : Need) (g g' : Comp.Gen Map) (b : Blob) (u : Unit),
    SI g → HoonMap.get g.blocks o = some b → Distinct tgt → NB g.re tgt → NB g.re ned →
    (∀ y, NMem ned y → ¬ NMem tgt y) → (∀ y, NMem tgt y → ¬ Defd g.blocks y) →
    sureLoop o ned tgt g = some (u, g') → SureR ned tgt g g' o b := by
  intro ned
  induction ned with
  | none =>
    intro tgt g g' b u h hb _ _ _ _ _ hs
    simp only [sureLoop] at hs
    by_cases e : tgt = Need.none
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      subst e; exact sureR_nil h hb (fun y hy => hy)
    · rw [if_neg e] at hs; cases hs
  | this r =>
    intro tgt g g' b u h hb dt nt nn ap hf hs
    simp only [sureLoop] at hs
    obtain ⟨ops, g1, h1, hs⟩ := bind_some hs
    obtain ⟨B, eB, K⟩ := kernLoop_raw tgt r [] g g1 ops h1 (nn r rfl) (fun e => ap r rfl e) nt dt
    simp only [List.append_nil] at eB
    rw [eB] at hs
    have S1 : SI g1 := by rw [K.gen]; exact si_reg h K.le
    have b1 : g1.blocks = g.blocks := by rw [K.gen]
    have P : OpsOK g1 B := ⟨K.regs, K.nd, fun y hy d => by
        rw [b1] at d
        rcases K.defs y hy with e | e
        · exact hf y e d
        · have := h.defd_lt d; omega, K.tr⟩
    obtain ⟨S2, b', hb', e2, q2, o2⟩ := si_addOps S1 P hs
    rw [b1, hb] at hb'; cases hb'
    refine ⟨S2, by rw [o2, K.gen], by have := K.le; omega, B, fun k => ?_, fun y hy => ?_, K.cov,
      fun y hy => ?_⟩
    · rw [e2, b1]; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [e, get_put_ne e]
    · rw [K.rf y hy]; rfl
    · rcases K.defs y hy with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e.1, by omega⟩
  | pair p q ihp ihq =>
    intro tgt g g' b u h hb dt nt nn ap hf hs
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      exact sureR_nil h hb (fun y hy => hy)
    | pair tp tq =>
      simp only [sureLoop] at hs
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dp, dq, apq⟩ := dt
      obtain ⟨S1, bo1, l1, A1, get1, rf1, cv1, df1⟩ := ihp tp g g1 b u1 h hb dp (fun y hy => nt y (Or.inl hy))
        (fun y hy => nn y (Or.inl hy)) (fun y hy e => ap y (Or.inl hy) (Or.inl e)) (fun y hy => hf y (Or.inl hy)) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 b) := by rw [get1, if_pos rfl]
      have R2 := ihq tq g1 g' (pre A1 b) u S1 hb1 dq (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr hy)) l1) (fun y hy e => ap y (Or.inr hy) (Or.inr e))
        (fun y hy d => by
          rcases (defd_of_ifget hb get1).mp d with d | d
          · exact hf y (Or.inr hy) d
          · rcases df1 y d with e | e
            · exact apq y e hy
            · have := nt y (Or.inr hy); omega) hs
      exact sureR_seq l1 bo1 get1 (fun y hy => Or.inl (rf1 y hy))
        (fun y hy => (df1 y hy).imp Or.inl id) R2 (fun y hy => Or.inr hy) (fun y hy => Or.inr hy)
        (fun y hy => hy.elim (fun e => Or.inl (cv1 y e)) Or.inr)
    | this d => simp [sureLoop, crashM] at hs
    | both d th tt => simp [sureLoop, crashM] at hs
  | both r hh tt ihh iht =>
    intro tgt g g' b u h hb dt nt nn ap hf hs
    have hr := nn r (Or.inl rfl)
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      exact sureR_nil h hb (fun y hy => hy)
    | this d =>
      simp only [sureLoop] at hs
      by_cases e : r = d
      · rw [if_pos e] at hs; cases hs
      rw [if_neg e] at hs
      obtain ⟨S1, bo1, l1, get1⟩ := sureR_mov (ned := Need.both r hh tt) h hb hr (nt d rfl) (hf d rfl) (Or.inl rfl) hs
      refine ⟨S1, bo1, l1, [Pole.mov r d], get1, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
      · rcases opsRF_mov_cons hy with e' | ⟨-, e'⟩
        · rw [e']; exact Or.inl rfl
        · exact e'.elim
      · simp only [NMem] at hy; simp [defsOf_mov, hy]
      · simp [defsOf_mov] at hy; exact Or.inl hy
    | pair tp tq =>
      simp only [sureLoop] at hs
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dp, dq, apq⟩ := dt
      obtain ⟨S1, bo1, l1, A1, get1, rf1, cv1, df1⟩ := ihh tp g g1 b u1 h hb dp (fun y hy => nt y (Or.inl hy))
        (fun y hy => nn y (Or.inr (Or.inl hy))) (fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inl e))
        (fun y hy => hf y (Or.inl hy)) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 b) := by rw [get1, if_pos rfl]
      have R2 := iht tq g1 g' (pre A1 b) u S1 hb1 dq (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr (Or.inr hy))) l1)
        (fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr e))
        (fun y hy d => by
          rcases (defd_of_ifget hb get1).mp d with d | d
          · exact hf y (Or.inr hy) d
          · rcases df1 y d with e | e
            · exact apq y e hy
            · have := nt y (Or.inr hy); omega) hs
      exact sureR_seq l1 bo1 get1 (fun y hy => Or.inr (Or.inl (rf1 y hy)))
        (fun y hy => (df1 y hy).imp Or.inl id) R2 (fun y hy => Or.inr (Or.inr hy)) (fun y hy => Or.inr hy)
        (fun y hy => hy.elim (fun e => Or.inl (cv1 y e)) Or.inr)
    | both d th tt' =>
      simp only [sureLoop] at hs
      by_cases e : r = d
      · rw [if_pos e] at hs; cases hs
      rw [if_neg e] at hs
      obtain ⟨u0, g0, h0, hs⟩ := bind_some hs
      obtain ⟨dth, dtt, aptt, ndh, ndt⟩ := dt
      have hd := nt d (Or.inl rfl)
      obtain ⟨S0, bo0, l0, get0⟩ := sureR_mov (ned := Need.both r hh tt) h hb hr hd (hf d (Or.inl rfl))
        (Or.inl rfl) h0
      have hb0 : HoonMap.get g0.blocks o = some (pre [Pole.mov r d] b) := by rw [get0, if_pos rfl]
      have dd0 : ∀ y, Defd g0.blocks y → Defd g.blocks y ∨ y = d := fun y dy => by
        rcases (defd_of_ifget hb get0).mp dy with e | e
        · exact Or.inl e
        · simp [defsOf_mov] at e; exact Or.inr e
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨S1, bo1, l1, A1, get1, rf1, cv1, df1⟩ := ihh th g0 g1 _ u1 S0 hb0 dth
        (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr (Or.inl hy))) l0)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr (Or.inl hy))) l0)
        (fun y hy e' => ap y (Or.inr (Or.inl hy)) (Or.inr (Or.inl e')))
        (fun y hy dy => by
          rcases dd0 y dy with dy | rfl
          · exact hf y (Or.inr (Or.inl hy)) dy
          · exact ndh hy) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 (pre [Pole.mov r d] b)) := by rw [get1, if_pos rfl]
      obtain ⟨S2, bo2, l2, A2, get2, rf2, cv2, df2⟩ := iht tt' g1 g' _ u S1 hb1 dtt
        (fun y hy => by have := nt y (Or.inr (Or.inr hy)); omega)
        (fun y hy => by have := nn y (Or.inr (Or.inr hy)); omega)
        (fun y hy e' => ap y (Or.inr (Or.inr hy)) (Or.inr (Or.inr e')))
        (fun y hy dy => by
          rcases (defd_of_ifget hb0 get1).mp dy with dy | dy
          · rcases dd0 y dy with dy | rfl
            · exact hf y (Or.inr (Or.inr hy)) dy
            · exact ndt hy
          · rcases df1 y dy with e' | e'
            · exact aptt y e' hy
            · have := nt y (Or.inr (Or.inr hy)); omega) hs
      refine ⟨S2, by omega, by omega, A2 ++ A1 ++ [Pole.mov r d], fun k => ?_, fun y hy => ?_, fun y hy => ?_,
        fun y hy => ?_⟩
      · rw [get2, get1, get0]; by_cases e' : k = o
        · subst e'; simp [pre_pre]
        · simp [e']
      · rcases opsRF_append.mp hy with e' | ⟨-, e'⟩
        · rcases opsRF_append.mp e' with e' | ⟨-, e'⟩
          · exact Or.inr (Or.inr (rf2 y e'))
          · exact Or.inr (Or.inl (rf1 y e'))
        · rcases opsRF_mov_cons e' with e' | ⟨-, e'⟩
          · rw [e']; exact Or.inl rfl
          · exact e'.elim
      · simp only [defsOf_append, List.mem_append]
        rcases hy with e' | e' | e'
        · right; simp [defsOf_mov, e']
        · exact Or.inl (Or.inr (cv1 y e'))
        · exact Or.inl (Or.inl (cv2 y e'))
      · simp only [defsOf_append, List.mem_append] at hy
        rcases hy with (e' | e') | e'
        · rcases df2 y e' with e'' | e''
          · exact Or.inl (Or.inr (Or.inr e''))
          · exact Or.inr ⟨by omega, e''.2⟩
        · rcases df1 y e' with e'' | e''
          · exact Or.inl (Or.inr (Or.inl e''))
          · exact Or.inr ⟨by omega, by omega⟩
        · simp [defsOf_mov] at e'; exact Or.inl (Or.inl e')

end Raw
end SkaModel
end Formalization
