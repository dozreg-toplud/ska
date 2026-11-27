import lemmas.Ska.RawInvSplit

/-!
# Raw `+comp` output: `+crash-need`, `+mede`, `+collapse-lazy-atom`

README Gaps 14.

* `lookPath_keeps`, `sureRequireLook_keeps`: `+sure-require-look` keeps the
  registers of the need it is given (it only adds fresh ones for the looks).
* `raw_crashNeed`: the fill of `+crash-need` reads only the register it
  tests (`%|`) or nothing (`%&`, which writes the atom first), and writes the
  need's other registers and fresh ones, each once (since af5cc39 the fill
  skips the tested register).
* `raw_medeLoop`, `raw_mede`: the constant into the need's registers; the
  block reads nothing first.
* `raw_collapse`: `+collapse-lazy-atom` returns a register `r` (the goal's or
  a fresh one) that it does not define and a block `there` (the goal's
  continuation or a new `%bom` block) where only `r` and what the
  continuation needed beyond the goal can be live.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]
variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}
variable {K : Nat → Nat → Prop} [KVan K lo]

/-! ## `+sure-require-look` keeps registers -/

theorem lookPath_keeps : ∀ (axe : Nat), 1 ≤ axe → ∀ (ned ned' : Need) (g0 g1 : Comp.Gen Map),
    lookPath ned axe g0 = some (ned', g1) → ∀ y, NMem ned y → NMem ned' y := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ha ned ned' g0 g1 h y hy
  by_cases h1 : axe ≤ 1
  · rw [lookPath.eq_def] at h
    simp only [h1, dif_pos] at h
    cases ned with
    | none => exact hy.elim
    | this r => simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hy
    | pair p q => simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hy
    | both r p q => simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hy
  · rw [lookPath_step ned (by omega)] at h
    have ihm := ih (mas axe) (mas_lt axe (by omega)) (mas_pos axe (by omega))
    have hs := (split3_mem ned y).mp hy
    split at h
    · obtain ⟨x, g, h5, h6⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
      rw [← h6.1, consNeed_pair (Or.inl (lookPath_ne_none _ (mas_pos axe (by omega)) _ _ _ _ h5))]
      rw [wrap_mem _ ⟨_, _, rfl⟩]
      rcases hs with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (ihm _ _ _ _ h5 y e))
      · exact Or.inr (Or.inr e)
    · obtain ⟨x, g, h5, h6⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
      rw [← h6.1, consNeed_pair (Or.inr (lookPath_ne_none _ (mas_pos axe (by omega)) _ _ _ _ h5))]
      rw [wrap_mem _ ⟨_, _, rfl⟩]
      rcases hs with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (ihm _ _ _ _ h5 y e))

theorem foldLook_keeps : ∀ (xs : List Nat) (ned0 ned' : Need) (g0 g1 : Comp.Gen Map),
    (xs.foldl (fun acc axe => acc >>= lookStep axe) (pure ned0) : CM Map Need) g0 = some (ned', g1) →
    ∀ y, NMem ned0 y → NMem ned' y := by
  intro xs
  induction xs with
  | nil =>
    intro ned0 ned' g0 g1 h y hy
    simp only [List.foldl_nil, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hy
  | cons x xs ih =>
    intro ned0 ned' g0 g1 h y hy
    rw [List.foldl_cons, foldl_look] at h
    obtain ⟨n1, g', h1, h2⟩ := bind_some h
    rw [pure_bind] at h1
    refine ih n1 ned' g' g1 h2 y ?_
    unfold lookStep at h1
    split at h1
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1; rw [← h1.1]; exact hy
    · split at h1
      · cases h1
      · exact lookPath_keeps x (by omega) _ _ _ _ h1 y hy

theorem sureRequireLook_keeps {sur : Sure S} {ned' : Need} {g0 g1 : Comp.Gen Map}
    (h : sureRequireLook sur g0 = some (ned', g1)) {y : Nat} (hy : NMem sur.ned y) : NMem ned' y :=
  foldLook_keeps (Map := Map) _ _ _ g0 g1 (by rw [← sureRequireLook_eq]; exact h) y hy

theorem flatten_nodup : ∀ {ned : Need}, Distinct ned → (flattenNeed ned).Nodup
  | Need.none, _ => List.nodup_nil
  | Need.this _, _ => by simp [flattenNeed]
  | Need.pair p q, ⟨dp, dq, ap⟩ => by
    simp only [flattenNeed]
    refine List.nodup_append.mpr ⟨flatten_nodup dp, flatten_nodup dq, ?_⟩
    rintro x hx _ hy rfl; exact ap x ((mem_flatten p x).mp hx) ((mem_flatten q x).mp hy)
  | Need.both r p q, ⟨dp, dq, ap, np, nq⟩ => by
    simp only [flattenNeed]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, List.nodup_append.mpr ⟨flatten_nodup dp, flatten_nodup dq, ?_⟩⟩
    · rcases List.mem_append.mp hm with hm | hm
      · exact np ((mem_flatten p r).mp hm)
      · exact nq ((mem_flatten q r).mp hm)
    · rintro x hx _ hy rfl; exact ap x ((mem_flatten p x).mp hx) ((mem_flatten q x).mp hy)

/-! ## The fills -/

theorem defsOf_fill (l : List Nat) : defsOf (l.map fun x => Pole.imm (A 0) x) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, defsOf_cons, aliasDst, Option.toList_some, ih]; rfl

theorem opsRF_fill (l : List Nat) {y : Nat} : ¬ OpsRF (l.map fun x => Pole.imm (A 0) x) y := by
  induction l with
  | nil => exact id
  | cons x l ih => simp only [List.map_cons, OpsRF, reads_imm, false_or, not_and]; exact fun _ => ih

theorem tr_fill (l : List Nat) : ∀ op ∈ l.map (fun x => Pole.imm (A 0) x), trOp op = false := by
  intro op hop; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hop; rfl

theorem regs_fill {P : Nat → Prop} (l : List Nat) (h : ∀ x ∈ l, P x) : RegsIn P (l.map fun x => Pole.imm (A 0) x) := by
  intro op hop y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hop
  simp [Comp.poleRegs] at hy; rw [hy]; exact h x hx

/-- **`+crash-need`.** -/
theorem raw_crashNeed {o : Nat} {atom : Sum Nat Nat} {ned : Need} {g g' : Comp.Gen Map} {b : Blob} {u : Unit}
    (h : SIP X ρ lo g) (hb : HoonMap.get g.blocks o = some b) (dn : Distinct ned) (hn : NB g.re ned)
    (hp : ∀ p, atom = Sum.inr p → p < g.re)
    (hf : ∀ y, NMem ned y → (∀ p, atom = Sum.inr p → y ≠ p) → ¬ Defd g.blocks y)
    (hc : crashNeed o atom ned g = some (u, g')) :
    SIP X ρ lo g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
      (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
      (∀ y, OpsRF A y → atom = Sum.inr y) ∧
      (∀ y ∈ defsOf A, (NMem ned y ∧ ∀ p, atom = Sum.inr p → y ≠ p) ∨ (g.re ≤ y ∧ y < g'.re)) ∧
      (∀ y, Defd g'.blocks y ↔ Defd g.blocks y ∨ y ∈ defsOf A) ∧
      (∀ y, NMem ned y → (∀ p, atom = Sum.inr p → y ≠ p) → y ∈ defsOf A) := by
  have hnd := flatten_nodup dn
  cases atom with
  | inr p =>
    simp only [crashNeed] at hc
    have hpl := hp p rfl
    have P : OpsOK g (Pole.cel p :: ((flattenNeed ned).filter (· != p)).map fun x => Pole.imm (A 0) x) :=
      ⟨RegsIn.cons (fun y hy => by simp [Comp.poleRegs] at hy; omega)
          (regs_fill _ fun x hx => hn x ((mem_flatten ned x).mp (List.mem_filter.mp hx).1)),
        by simp only [defsOf_cons, aliasDst, Option.toList_none, List.nil_append, defsOf_fill]; exact hnd.filter _,
        fun y hy => by
          simp only [defsOf_cons, aliasDst, Option.toList_none, List.nil_append, defsOf_fill, List.mem_filter] at hy
          refine hf y ((mem_flatten ned y).mp hy.1) fun p' e => ?_
          cases e; simpa using hy.2,
        fun op hop => by
          rcases List.mem_cons.mp hop with rfl | hop
          · rfl
          · exact tr_fill _ op hop⟩
    obtain ⟨S', b', hb', e', q', o'⟩ := sip_addOps h P hc
    rw [hb] at hb'; cases hb'
    refine ⟨S', o', by omega, Pole.cel p :: ((flattenNeed ned).filter (· != p)).map fun x => Pole.imm (A 0) x,
      fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun y => ?_, ?_⟩
    · rw [e']; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [get_put_ne e, e]
    · rcases hy with hy | ⟨-, hy⟩
      · rw [reads_cel] at hy; rw [hy]
      · exact absurd hy (opsRF_fill _)
    · simp only [defsOf_cons, aliasDst, Option.toList_none, List.nil_append, defsOf_fill, List.mem_filter] at hy
      refine Or.inl ⟨(mem_flatten ned y).mp hy.1, fun p' e => ?_⟩
      cases e; simpa using hy.2
    · rw [e', defd_prepend hb]
    · intro y hy hne
      simp only [defsOf_cons, aliasDst, Option.toList_none, List.nil_append, defsOf_fill, List.mem_filter]
      exact ⟨(mem_flatten ned y).mpr hy, by simpa using hne p rfl⟩
  | inl n =>
    simp only [crashNeed] at hc
    obtain ⟨r, g1, h1, hc⟩ := bind_some hc
    obtain ⟨S1, rfl, q1, b1, o1⟩ := sip_re h h1
    have nd : ¬ Defd g1.blocks g.re := fun d => by rw [b1] at d; have := h.defd_lt d; omega
    have P : OpsOK g1 (Pole.imm (A n) g.re :: Pole.cel g.re :: (flattenNeed ned).map fun x => Pole.imm (A 0) x) :=
      ⟨RegsIn.cons (fun y hy => by simp [Comp.poleRegs] at hy; omega) (RegsIn.cons
          (fun y hy => by simp [Comp.poleRegs] at hy; omega)
          (regs_fill _ fun x hx => by have := hn x ((mem_flatten ned x).mp hx); omega)),
        by
          simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_fill,
            List.singleton_append]
          exact List.nodup_cons.mpr ⟨fun hm => by have := hn _ ((mem_flatten ned _).mp hm); omega, hnd⟩,
        fun y hy => by
          simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_fill,
            List.singleton_append, List.mem_cons] at hy
          rcases hy with e | hy
          · rw [e]; exact nd
          · rw [b1]; exact hf y ((mem_flatten ned y).mp hy) fun p e => by simp at e,
        fun op hop => by
          rcases List.mem_cons.mp hop with rfl | hop
          · rfl
          · rcases List.mem_cons.mp hop with rfl | hop
            · rfl
            · exact tr_fill _ op hop⟩
    obtain ⟨S', b', hb', e', q', o'⟩ := sip_addOps S1 P hc
    rw [b1, hb] at hb'; cases hb'
    refine ⟨S', by omega, by omega, Pole.imm (A n) g.re :: Pole.cel g.re :: (flattenNeed ned).map fun x => Pole.imm (A 0) x,
      fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun y => ?_, ?_⟩
    · rw [e', b1]; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [get_put_ne e, e]
    · exfalso
      simp only [OpsRF, reads_imm, reads_cel, aliasDst, ne_eq, Option.some.injEq, false_or] at hy
      obtain ⟨hne, hy | ⟨-, hy⟩⟩ := hy
      · exact hne hy.symm
      · exact opsRF_fill _ hy
    · simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_fill,
        List.singleton_append, List.mem_cons] at hy
      rcases hy with e | hy
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inl ⟨(mem_flatten ned y).mp hy, fun p e => by simp at e⟩
    · rw [e', defd_prepend (by rw [b1]; exact hb), b1]
    · intro y hy _
      simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_fill,
        List.singleton_append, List.mem_cons]
      exact Or.inr ((mem_flatten ned y).mpr hy)

/-! ## `+collapse-lazy-atom` -/

theorem lt_or_eq_of_mem_this {r y : Nat} {lo hi : Nat} {ned' : Need}
    (hm : ∀ y, NMem ned' y → NMem (Need.this r) y ∨ (lo ≤ y ∧ y < hi)) (hy : NMem ned' y) :
    y = r ∨ (lo ≤ y ∧ y < hi) := by
  rcases hm y hy with e | e
  · exact Or.inl e
  · exact Or.inr e

/-- **`+collapse-lazy-atom`** on a fork-free goal. -/
theorem raw_collapse [HoonMapKeys Map] {laz : Sure S} {th : Jmp} {g g' : Comp.Gen Map} {a : Option (Nat × Nat)}
    (h : SIP X ρ lo g) (hn : NB g.re laz.ned) (hj : th.there < g.bo)
    (hf : ∀ y, NMem laz.ned y → ¬ Defd g.blocks y)
    (hc : collapseLazyAtom ⟨laz, th⟩ g = some (a, g')) :
    SIP X ρ lo g' ∧ g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ th.args = [] ∧
      (∀ k, k < g.bo → k ≠ th.there → HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧
      (a = Option.none → laz.ned = Need.none ∧ g' = g) ∧
      (∀ r there, a = some (r, there) →
        (NMem laz.ned r ∨ (g.re ≤ r ∧ r < g'.re)) ∧ r < g'.re ∧ ¬ Defd g'.blocks r ∧ there < g'.bo ∧
        (∀ y, Defd g'.blocks y → Defd g.blocks y ∨ (g.re ≤ y ∧ y < g'.re ∧ y ≠ r)) ∧
        (∀ y, LiveK g'.blocks K there y → y = r ∨ (LiveK g.blocks K th.there y ∧ ¬ NMem laz.ned y))) := by
  unfold collapseLazyAtom at hc
  by_cases ha : th.args ≠ []
  · rw [if_pos ha] at hc; cases hc
  rw [if_neg ha] at hc
  have ha' : th.args = [] := Classical.byContradiction ha
  by_cases hne : noneEquivalent laz = true
  · rw [if_pos hne] at hc
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨h, Nat.le_refl _, Nat.le_refl _, ha', fun _ _ _ => rfl, fun _ => ⟨?_, rfl⟩, fun r t e => by cases e⟩
    simp only [noneEquivalent, Bool.and_eq_true, decide_eq_true_eq] at hne
    exact hne.1
  rw [if_neg hne] at hc
  obtain ⟨ns, g1, h1, hc⟩ := bind_some hc
  have L1 := sureRequireLook_spec h1
  obtain ⟨k1, e1⟩ := L1.gen
  have S1 : SIP X ρ lo g1 := by rw [e1]; exact sip_reg h (by have := L1.le; rw [e1] at this; exact this)
  have b1 : g1.blocks = g.blocks := by rw [e1]
  have bo1 : g1.bo = g.bo := by rw [e1]
  have keep1 : ∀ y, NMem laz.ned y → NMem ns y := fun y hy => sureRequireLook_keeps h1 hy
  have l1 := L1.le
  obtain ⟨⟨r, there⟩, g2, h2, hc⟩ := bind_some hc
  have hr : SIP X ρ lo g2 ∧ g1.re ≤ g2.re ∧ (∀ k, k < g1.bo → HoonMap.get g2.blocks k = HoonMap.get g1.blocks k) ∧
      r < g2.re ∧ (NMem laz.ned r ∨ (g.re ≤ r ∧ r < g2.re)) ∧ ¬ Defd g2.blocks r ∧
      (∀ y, Defd g2.blocks y ↔ Defd g.blocks y) ∧
      ((there = th.there ∧ g2.blocks = g.blocks ∧ g2.bo = g.bo ∧ ∀ y, NMem laz.ned y → y = r) ∨
       (there = g1.bo ∧ g2.bo = g1.bo + 1 ∧ HoonMap.get g2.blocks there = some ⟨[], [], Termin.bom Option.none⟩)) := by
    cases ns with
    | this r0 =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      have hm : NMem laz.ned r0 ∨ (g.re ≤ r0 ∧ r0 < g1.re) := L1.mem r0 rfl
      refine ⟨S1, Nat.le_refl _, fun _ _ => rfl, ?_, hm, ?_, fun y => by rw [b1],
        Or.inl ⟨rfl, b1, bo1, fun y hy => keep1 y hy⟩⟩
      · rcases hm with e | e
        · have := hn _ e; omega
        · exact e.2
      · rw [b1]; rcases hm with e | e
        · exact hf _ e
        · exact fun d => by have := h.defd_lt d; omega
    | none =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S1 h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      refine ⟨S3, by omega, fun k _ => by rw [b3], by omega, Or.inr ⟨by omega, by omega⟩, ?_,
        fun y => by rw [b3, b1], Or.inl ⟨rfl, by rw [b3, b1], by rw [o3, bo1], fun y hy => (keep1 y hy).elim⟩⟩
      exact fun d => by rw [b3, b1] at d; have := h.defd_lt d; omega
    | pair p q =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S1 h3
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 (emitOK_bom Option.none) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      have dd : ∀ y, Defd g4.blocks y ↔ Defd g.blocks y := fun y => by
        rw [e4, defd_put (S3.none (Nat.le_refl _)), b3, b1]; simp [blockDefs, defsOf]
      refine ⟨S4, by omega, fun k hk => by rw [e4, get_put_ne (by omega), b3], by omega,
        Or.inr ⟨by omega, by omega⟩, fun d => by rw [dd] at d; have := h.defd_lt d; omega, dd,
        Or.inr ⟨by omega, by omega, by rw [e4]; exact get_put_self⟩⟩
    | both r0 p q =>
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S1 (emitOK_bom Option.none) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      have dd : ∀ y, Defd g4.blocks y ↔ Defd g.blocks y := fun y => by
        rw [e4, defd_put (S1.none (Nat.le_refl _)), b1]; simp [blockDefs, defsOf]
      have hm : NMem laz.ned r0 ∨ (g.re ≤ r0 ∧ r0 < g1.re) := L1.mem r0 (Or.inl rfl)
      refine ⟨S4, by omega, fun k hk => by rw [e4, get_put_ne (by omega)], ?_, ?_, ?_, dd,
        Or.inr ⟨rfl, by omega, by rw [e4]; exact get_put_self⟩⟩
      · rcases hm with e | e
        · have := hn _ e; omega
        · omega
      · rcases hm with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e.1, by omega⟩
      · rw [dd]; rcases hm with e | e
        · exact hf _ e
        · exact fun d => by have := h.defd_lt d; omega
  obtain ⟨S2, l2, fr2, rlt, rm, rnd, dd2, case2⟩ := hr
  obtain ⟨g3, g3', h3, hc⟩ := bind_some hc
  rw [get_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  rw [S2.drop] at hc
  simp only [Bool.false_eq_true, if_false] at hc
  obtain ⟨ned', g4, h4, hc⟩ := bind_some hc
  have L4 := sureRequireLook_spec h4
  obtain ⟨k4, e4⟩ := L4.gen
  have l4 := L4.le
  have S4 : SIP X ρ lo g4 := by rw [e4]; exact sip_reg S2 (by rw [e4] at l4; exact l4)
  have b4 : g4.blocks = g2.blocks := by rw [e4]
  have bo4 : g4.bo = g2.bo := by rw [e4]
  have m4 : ∀ y, NMem ned' y → y = r ∨ (g2.re ≤ y ∧ y < g4.re) := fun y hy => lt_or_eq_of_mem_this L4.mem hy
  have d4 : Distinct ned' := L4.dist trivial (fun y hy => by simp [NMem] at hy; omega)
  have hthere : there < g2.bo := by
    rcases case2 with ⟨rfl, -, e, -⟩ | ⟨rfl, e, -⟩
    · omega
    · omega
  have dd4 : ∀ y, Defd g4.blocks y ↔ Defd g.blocks y := fun y => by rw [b4, dd2]
  have close : ∀ (g5 : Comp.Gen Map) (A : List Pole), SIP X ρ lo g5 → g4.re ≤ g5.re → g5.bo = g4.bo →
      (∀ k, k ≠ there → HoonMap.get g5.blocks k = HoonMap.get g4.blocks k) →
      (∀ y, LiveK g5.blocks K there y → OpsRF A y ∨ (y ∉ defsOf A ∧ LiveK g4.blocks K there y)) →
      (∀ y, OpsRF A y → y = r) →
      (∀ y, Defd g5.blocks y ↔ Defd g4.blocks y ∨ y ∈ defsOf A) →
      (∀ y ∈ defsOf A, g2.re ≤ y ∧ y < g5.re ∧ y ≠ r) →
      (pure (some (r, there)) : CM Map (Option (Nat × Nat))) g5 = some (a, g') →
      SIP X ρ lo g' ∧ g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ th.args = [] ∧
      (∀ k, k < g.bo → k ≠ th.there → HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧
      (a = Option.none → laz.ned = Need.none ∧ g' = g) ∧
      (∀ r there', a = some (r, there') →
        (NMem laz.ned r ∨ (g.re ≤ r ∧ r < g'.re)) ∧ r < g'.re ∧ ¬ Defd g'.blocks r ∧ there' < g'.bo ∧
        (∀ y, Defd g'.blocks y → Defd g.blocks y ∨ (g.re ≤ y ∧ y < g'.re ∧ y ≠ r)) ∧
        (∀ y, LiveK g'.blocks K there' y → y = r ∨ (LiveK g.blocks K th.there y ∧ ¬ NMem laz.ned y))) := by
    intro g5 A S5 l5 bo5 fr5 lv5 rf5 dd5 df5 e5
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e5
    obtain ⟨rfl, rfl⟩ := e5
    have ndr : ¬ Defd g5.blocks r := fun d => by
      rcases (dd5 r).mp d with d | d
      · exact rnd ((dd2 r).mpr ((dd4 r).mp d))
      · exact (df5 r d).2.2 rfl
    refine ⟨S5, by omega, by omega, ha', fun k hk hne => ?_, fun e => (by cases e), fun r' t e => ?_⟩
    · have hkt : k ≠ there := by
        rcases case2 with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -⟩
        · exact hne
        · omega
      rw [fr5 k hkt, b4, fr2 k (by omega), b1]
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨rm.imp id fun e => ⟨e.1, by omega⟩, by omega, ndr, by omega, fun y d => ?_, fun y hl => ?_⟩
      · rcases (dd5 y).mp d with d | d
        · exact Or.inl ((dd4 y).mp d)
        · have := df5 y d; exact Or.inr ⟨by omega, this.2.1, this.2.2⟩
      · rcases lv5 y hl with e | ⟨-, hl⟩
        · exact Or.inl (rf5 y e)
        · rw [b4] at hl
          rcases case2 with ⟨rfl, eb, -, hr'⟩ | ⟨rfl, -, eb⟩
          · rw [eb] at hl
            by_cases e : NMem laz.ned y
            · exact Or.inl (hr' y e)
            · exact Or.inr ⟨hl, e⟩
          · exact absurd hl (not_liveK_bom eb)
  cases ned' with
  | none =>
    exact close g4 [] S4 (Nat.le_refl _) rfl (fun _ _ => rfl) (fun y hl => Or.inr ⟨by simp [defsOf], hl⟩)
      (fun y e => e.elim) (fun y => by simp [defsOf]) (fun y hy => by simp [defsOf] at hy) hc
  | this r' =>
    simp only at hc
    by_cases e : r = r'
    · rw [if_pos e] at hc
      exact close g4 [] S4 (Nat.le_refl _) rfl (fun _ _ => rfl) (fun y hl => Or.inr ⟨by simp [defsOf], hl⟩)
        (fun y e => e.elim) (fun y => by simp [defsOf]) (fun y hy => by simp [defsOf] at hy) hc
    · rw [if_neg e] at hc
      obtain ⟨u, g5, h5, hc⟩ := bind_some hc
      have fr' : g2.re ≤ r' ∧ r' < g4.re := by
        rcases m4 r' rfl with e' | e'
        · exact absurd e'.symm e
        · exact e'
      have P : OpsOK g4 [Pole.mov r r'] :=
        ⟨regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), by simp [defsOf_mov],
          fun y hy d => by
            simp [defsOf_mov] at hy; subst hy
            have := h.defd_lt ((dd4 _).mp d); omega,
          fun op hop => by simp at hop; subst hop; rfl⟩
      obtain ⟨S5, b5, hb5, e5, q5, o5⟩ := sip_addOps S4 P h5
      have below : ∀ k, k ≠ there → HoonMap.get g5.blocks k = HoonMap.get g4.blocks k := fun k hk => by
        rw [e5, get_put_ne hk]
      refine close g5 [Pole.mov r r'] S5 (by omega) o5 below (fun y hl => ?_) (fun y hy => ?_) (fun y => ?_)
        (fun y hy => ?_) hc
      · rw [e5] at hl
        rcases liveK_prependRk hb5 S4.jr hl with ⟨-, h'⟩ | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · simp only [OpsRF, reads_mov] at hy
        rcases hy with hy | ⟨-, hy⟩
        · exact hy
        · exact hy.elim
      · rw [e5, defd_prepend hb5]
      · simp [defsOf_mov] at hy; subst hy; exact ⟨fr'.1, by omega, fun e' => e e'.symm⟩
  | pair p q =>
    simp only at hc
    obtain ⟨u, g5, h5, hc⟩ := bind_some hc
    obtain ⟨b5, hb5⟩ : ∃ b, HoonMap.get g4.blocks there = some b := by
      simp only [crashNeed] at h5
      obtain ⟨b, hb, -⟩ := addOps_spec h5 S4.drop
      exact ⟨b, hb⟩
    obtain ⟨S5, bo5, l5, A, hget, hrf, hdefs, hdd, -⟩ := raw_crashNeed S4 hb5 d4
      (fun y hy => by rcases m4 y hy with e | e <;> omega) (fun p e => by cases e; omega)
      (fun y hy hne d => by
        have := h.defd_lt ((dd4 _).mp d)
        rcases m4 y hy with e | e
        · exact hne r rfl e
        · omega) h5
    refine close g5 A S5 l5 bo5 (fun k hk => by rw [hget, if_neg hk]) (fun y hl => ?_) (fun y hy => ?_) hdd
      (fun y hy => ?_) hc
    · have hk : HoonMap.get g5.blocks there = some (pre A b5) := by rw [hget, if_pos rfl]
      have he : ∀ x, ρ x < ρ there → HoonMap.get g5.blocks x = HoonMap.get g4.blocks x := fun x hx => by
        rw [hget, if_neg (fun e => by subst e; omega)]
      have hl' : LiveK (HoonMap.put g4.blocks there (pre A b5)) K there y := by
        rcases liveK_cases hl with ⟨b', hb', hr'⟩
        rw [hk] at hb'; cases hb'
        refine (liveK_iff hl.nk).mpr ⟨_, get_put_self, ?_⟩
        rcases hr' with hr' | ⟨j, hj, hlj, hn⟩
        · exact Or.inl hr'
        · refine Or.inr ⟨j, hj, ?_, hn⟩
          have hjt : ρ j.there < ρ there := S4.jr there b5 hb5 j hj
          exact (liveK_frameRk S4.jr (fun x hx => get_put_ne (fun e => by subst e; omega)) hjt).mpr
            ((liveK_frameRk S4.jr he hjt).mp hlj)
      rcases liveK_prependRk hb5 S4.jr hl' with ⟨-, h'⟩ | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · have := hrf y hy; cases this; rfl
    · rcases hdefs y hy with ⟨hm, hne⟩ | e
      · rcases m4 y hm with e | e
        · exact absurd e (hne r rfl)
        · exact ⟨by omega, by omega, hne r rfl⟩
      · exact ⟨by omega, e.2, by omega⟩
  | both r0 p q =>
    simp only at hc
    obtain ⟨u, g5, h5, hc⟩ := bind_some hc
    obtain ⟨b5, hb5⟩ : ∃ b, HoonMap.get g4.blocks there = some b := by
      simp only [crashNeed] at h5
      obtain ⟨b, hb, -⟩ := addOps_spec h5 S4.drop
      exact ⟨b, hb⟩
    obtain ⟨S5, bo5, l5, A, hget, hrf, hdefs, hdd, -⟩ := raw_crashNeed S4 hb5 d4
      (fun y hy => by rcases m4 y hy with e | e <;> omega) (fun p e => by cases e; omega)
      (fun y hy hne d => by
        have := h.defd_lt ((dd4 _).mp d)
        rcases m4 y hy with e | e
        · exact hne r rfl e
        · omega) h5
    refine close g5 A S5 l5 bo5 (fun k hk => by rw [hget, if_neg hk]) (fun y hl => ?_) (fun y hy => ?_) hdd
      (fun y hy => ?_) hc
    · have hk : HoonMap.get g5.blocks there = some (pre A b5) := by rw [hget, if_pos rfl]
      have he : ∀ x, ρ x < ρ there → HoonMap.get g5.blocks x = HoonMap.get g4.blocks x := fun x hx => by
        rw [hget, if_neg (fun e => by subst e; omega)]
      have hl' : LiveK (HoonMap.put g4.blocks there (pre A b5)) K there y := by
        rcases liveK_cases hl with ⟨b', hb', hr'⟩
        rw [hk] at hb'; cases hb'
        refine (liveK_iff hl.nk).mpr ⟨_, get_put_self, ?_⟩
        rcases hr' with hr' | ⟨j, hj, hlj, hn⟩
        · exact Or.inl hr'
        · refine Or.inr ⟨j, hj, ?_, hn⟩
          have hjt : ρ j.there < ρ there := S4.jr there b5 hb5 j hj
          exact (liveK_frameRk S4.jr (fun x hx => get_put_ne (fun e => by subst e; omega)) hjt).mpr
            ((liveK_frameRk S4.jr he hjt).mp hlj)
      rcases liveK_prependRk hb5 S4.jr hl' with ⟨-, h'⟩ | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · have := hrf y hy; cases this; rfl
    · rcases hdefs y hy with ⟨hm, hne⟩ | e
      · rcases m4 y hm with e | e
        · exact absurd e (hne r rfl)
        · exact ⟨by omega, by omega, hne r rfl⟩
      · exact ⟨by omega, e.2, by omega⟩

end Raw
end SkaModel
end Formalization
