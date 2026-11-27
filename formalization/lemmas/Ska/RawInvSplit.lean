import lemmas.Ska.RawInvArms

/-!
# Raw `+comp` output: `+split` and `+copy`

README Gaps 14.  `raw_split`: the block of `+split` with its `%con` defines
the register of the goal's need that the halves do not name, and reads only
the halves' top registers.  `copyNeed_raw` (`CopyR`): the moves of
`+copy-need-make-ops` define each register of the two needs that the merged
need does not keep, once, and read only registers of the merged need;
`raw_copy`: the block of `+copy`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]
variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}

/-! ## `+must` and `+split-need` -/

theorem must_top {ned n : Need} {r : Nat} {g g' : Comp.Gen Map} (h : must ned g = some ((r, n), g')) : NMem n r := by
  cases ned <;> simp [must, bind_apply, re_apply, pure_apply] at h <;> obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h <;> simp [NMem]

theorem must_keep {ned n : Need} {r : Nat} {g g' : Comp.Gen Map} (h : must ned g = some ((r, n), g')) {y : Nat}
    (hy : NMem ned y) : NMem n y := by
  cases ned <;> simp [must, bind_apply, re_apply, pure_apply] at h <;> obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h <;>
    simp_all [NMem]

theorem opsRF_con {a c d y : Nat} : OpsRF [Pole.con a c d] y ↔ y = a ∨ y = c := by
  simp [OpsRF, reads_con]

theorem defsOf_con {a c d : Nat} : defsOf [Pole.con a c d] = [d] := by simp [defsOf, aliasDst]

/-- **`+split-need`**: the ops `A` in front of block `o` (none, or one
`%con` into the need's top register from the halves' top registers). -/
theorem raw_splitNeed {ned : Need} {o : Nat} {g g' : Comp.Gen Map} {x : Need × Need} {b : Blob} (h : SIP X ρ lo g)
    (hb : HoonMap.get g.blocks o = some b) (dn : Distinct ned) (hn : NB g.re ned)
    (hf : ∀ y, NMem ned y → ¬ Defd g.blocks y) (hs : splitNeed ned o g = some (x, g')) :
    SIP X ρ lo g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
      (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
      (∀ y, OpsRF A y → NMem x.1 y ∨ NMem x.2 y) ∧
      (∀ y, NMem ned y → y ∈ defsOf A ∨ NMem x.1 y ∨ NMem x.2 y) ∧
      (∀ y ∈ defsOf A, NMem ned y ∧ ¬ NMem x.1 y ∧ ¬ NMem x.2 y) ∧
      (∀ y, Defd g'.blocks y ↔ Defd g.blocks y ∨ y ∈ defsOf A) := by
  have same : ∀ k, HoonMap.get g.blocks k = if k = o then some (pre [] b) else HoonMap.get g.blocks k := by
    intro k; by_cases e : k = o
    · subst e; simp [hb, pre_nil]
    · simp [e]
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨h, rfl, Nat.le_refl _, [], same, fun y hy => hy.elim, fun y hy => Or.inr hy,
      fun y hy => by simp [defsOf] at hy, fun y => by simp [defsOf]⟩
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨h, rfl, Nat.le_refl _, [], same, fun y hy => hy.elim, fun y hy => hy.elim,
      fun y hy => by simp [defsOf] at hy, fun y => by simp [defsOf]⟩
  | this r =>
    simp only [splitNeed] at hs
    obtain ⟨hh, g1, h1, hs⟩ := bind_some hs
    obtain ⟨S1, rfl, q1, b1, o1⟩ := sip_re h h1
    obtain ⟨tt, g2, h2, hs⟩ := bind_some hs
    obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re S1 h2
    obtain ⟨u, g3, h3, hs⟩ := bind_some hs
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hr : r < g.re := hn r rfl
    have P : OpsOK g2 [Pole.con g.re g1.re r] :=
      ⟨regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), by simp [defsOf_con],
        fun y hy => by simp [defsOf_con] at hy; subst hy; rw [b2, b1]; exact hf y rfl,
        fun op hop => by simp at hop; subst hop; rfl⟩
    obtain ⟨S3, b', hb', e3, q3, o3⟩ := sip_addOps S2 P h3
    rw [b2, b1, hb] at hb'; cases hb'
    refine ⟨S3, by omega, by omega, [Pole.con g.re g1.re r], fun k => ?_, fun y hy => ?_, fun y hy => ?_,
      fun y hy => ?_, fun y => ?_⟩
    · rw [e3, b2, b1]; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [get_put_ne e, e]
    · rw [opsRF_con] at hy; simp only [NMem]; exact hy
    · simp only [NMem] at hy; subst hy; simp [defsOf_con]
    · simp only [defsOf_con, List.mem_singleton] at hy; subst hy
      simp only [NMem]; refine ⟨by trivial, ?_, ?_⟩ <;> omega
    · rw [e3, defd_prepend (by rw [b2, b1]; exact hb), b2, b1]
  | both r hh tt =>
    simp only [splitNeed] at hs
    obtain ⟨⟨hr, hn'⟩, g1, h1, hs⟩ := bind_some hs
    obtain ⟨e1, l1, m1, -⟩ := must_spec h1
    obtain ⟨⟨tr, tn'⟩, g2, h2, hs⟩ := bind_some hs
    obtain ⟨e2, l2, m2, -⟩ := must_spec h2
    obtain ⟨u, g3, h3, hs⟩ := bind_some hs
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hrr : r < g.re := hn r (Or.inl rfl)
    have t1 := must_top h1
    have t2 := must_top h2
    obtain ⟨dh, dt, ap, nrh, nrt⟩ := dn
    have S1 : SIP X ρ lo g1 := by rw [e1]; exact sip_reg h l1
    have S2 : SIP X ρ lo g2 := by rw [e2]; exact sip_reg S1 l2
    have bl2 : g2.blocks = g.blocks := by rw [e2, e1]
    have mlt1 : ∀ y, NMem hn' y → y < g1.re := fun y hy => by
      rcases m1 y hy with e | e
      · have := hn y (Or.inr (Or.inl e)); omega
      · omega
    have mlt2 : ∀ y, NMem tn' y → y < g2.re := fun y hy => by
      rcases m2 y hy with e | e
      · have := hn y (Or.inr (Or.inr e)); omega
      · omega
    have P : OpsOK g2 [Pole.con hr tr r] :=
      ⟨regsIn_one (fun y hy => by
          simp [Comp.poleRegs] at hy
          rcases hy with rfl | rfl | rfl
          · have := mlt1 _ t1; omega
          · exact mlt2 _ t2
          · omega), by simp [defsOf_con],
        fun y hy => by simp [defsOf_con] at hy; subst hy; rw [bl2]; exact hf y (Or.inl rfl),
        fun op hop => by simp at hop; subst hop; rfl⟩
    obtain ⟨S3, b', hb', e3, q3, o3⟩ := sip_addOps S2 P h3
    rw [bl2, hb] at hb'; cases hb'
    have o2 : g2.bo = g.bo := by rw [e2, e1]
    refine ⟨S3, by rw [o3, o2], by omega, [Pole.con hr tr r], fun k => ?_, fun y hy => ?_, fun y hy => ?_,
      fun y hy => ?_, fun y => ?_⟩
    · rw [e3, bl2]; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [get_put_ne e, e]
    · rw [opsRF_con] at hy
      rcases hy with rfl | rfl
      · exact Or.inl t1
      · exact Or.inr t2
    · rcases hy with rfl | hy | hy
      · simp [defsOf_con]
      · exact Or.inr (Or.inl (must_keep h1 hy))
      · exact Or.inr (Or.inr (must_keep h2 hy))
    · simp only [defsOf_con, List.mem_singleton] at hy; subst hy
      refine ⟨Or.inl rfl, fun e => ?_, fun e => ?_⟩
      · rcases m1 _ e with e | e
        · exact nrh e
        · omega
      · rcases m2 _ e with e | e
        · exact nrt e
        · omega
    · rw [e3, defd_prepend (by rw [bl2]; exact hb), bl2]

/-- **`+split`**: a new block that hops to the goal's continuation, with the
`%con` of `+split-need` in front. -/
theorem raw_split {laz : Sure S} {th : Jmp} {g g' : Comp.Gen Map} {x : Sure S × Sure S × Nat}
    (h : SIP X ρ lo g) (dn : Distinct laz.ned) (hn : NB g.re laz.ned) (ha : th.args = []) (hj : th.there < g.bo)
    (hf : ∀ y, NMem laz.ned y → ¬ Defd g.blocks y)
    (hs : Comp.split ⟨laz, th⟩ g = some (x, g')) :
    SIP X ρ lo g' ∧ x.2.2 = g.bo ∧ g'.bo = g.bo + 1 ∧ g.re ≤ g'.re ∧
      (∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧
      (∀ y, Live g'.blocks g.bo y → NMem x.1.ned y ∨ NMem x.2.1.ned y ∨
        (Live g.blocks th.there y ∧ ¬ NMem laz.ned y)) ∧
      (∀ y, Defd g'.blocks y → Defd g.blocks y ∨ (NMem laz.ned y ∧ ¬ NMem x.1.ned y ∧ ¬ NMem x.2.1.ned y)) := by
  simp only [Comp.split] at hs
  obtain ⟨o, g1, h1, hs⟩ := bind_some hs
  obtain ⟨S1, rfl, e1, q1, bo1⟩ := sip_emit h (emitOK_hop ha hj) h1
  obtain ⟨⟨sh, st⟩, g2, h2, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g3⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have hb1 : HoonMap.get g1.blocks g.bo = some ⟨[], [], Termin.hop th⟩ := by rw [e1]; exact get_put_self
  have hf1 : ∀ y, NMem laz.ned y → ¬ Defd g1.blocks y := fun y hy d => by
    rw [e1, defd_put (h.none (Nat.le_refl _))] at d
    rcases d with d | d
    · exact hf y hy d
    · simp [blockDefs, defsOf] at d
  obtain ⟨S3, bo3, l3, A, hget, hrf, hcov, hdefs, hdefd⟩ :=
    raw_splitNeed S1 hb1 dn (by rw [q1]; exact hn) hf1 h3
  have below : ∀ k, k < g.bo → HoonMap.get g3.blocks k = HoonMap.get g.blocks k := fun k hk => by
    rw [hget k, if_neg (by omega), e1, get_put_ne (by omega)]
  refine ⟨S3, rfl, by omega, by omega, below, fun y hy => ?_, fun y hy => ?_⟩
  · have hk : HoonMap.get g3.blocks g.bo = some ⟨[], A ++ [], Termin.hop th⟩ := by rw [hget, if_pos rfl]
    rcases live_unfoldP hk (h.below g.bo) below (fun j hj' => by simp [getJmps] at hj'; subst hj'; exact hj) hy with
      ⟨-, hr⟩ | ⟨j, hj', hl, hn'⟩
    · simp only [List.append_nil] at hr
      rcases hr with hr | ⟨-, hr⟩
      · rcases hrf y hr with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · simp [finRegs, jmpRegs_nil ha] at hr
    · simp [getJmps] at hj'; subst hj'
      have hnA : y ∉ defsOf A := fun e => hn' (by simp [blockDefs]; exact mem_defsOf.mp e)
      by_cases e : NMem laz.ned y
      · rcases hcov y e with e' | e' | e'
        · exact absurd e' hnA
        · exact Or.inl e'
        · exact Or.inr (Or.inl e')
      · exact Or.inr (Or.inr ⟨hl, e⟩)
  · rcases (hdefd y).mp hy with d | d
    · rw [e1, defd_put (h.none (Nat.le_refl _))] at d
      rcases d with d | d
      · exact Or.inl d
      · simp [blockDefs, defsOf] at d
    · exact Or.inr (hdefs y d)

/-! ## `+copy-need-make-ops` -/

/-- What the moves `A` of `+copy-need-make-ops` of `a` and `b` into `res`
are: distinct destinations; each a `%mov` from a register of `res` into a
register of `a` or `b` that `res` does not keep; every register of `a` and
`b` defined by them or kept in `res`. -/
def CopyR (a b res : Need) (A : List Pole) : Prop :=
  (defsOf A).Nodup ∧
  (∀ op ∈ A, ∃ s d, op = Pole.mov s d ∧ NMem res s ∧ (NMem a d ∨ NMem b d) ∧ ¬ NMem res d) ∧
  (∀ y, NMem a y ∨ NMem b y → y ∈ defsOf A ∨ NMem res y)

theorem defsOf_mov {s d : Nat} : defsOf [Pole.mov s d] = [d] := by simp [defsOf, aliasDst]

/-- One move into `d` from the top register `t` of `res`. -/
theorem copyR_one {a b res : Need} {t d : Nat} (ht : NMem res t) (hd : NMem a d ∨ NMem b d) (hn : ¬ NMem res d)
    (hcov : ∀ y, NMem a y ∨ NMem b y → y = d ∨ NMem res y) : CopyR a b res [Pole.mov t d] :=
  ⟨by simp [defsOf_mov], fun op hop => by simp at hop; subst hop; exact ⟨t, d, rfl, ht, hd, hn⟩,
    fun y hy => by rcases hcov y hy with e | e
                   · left; simp [defsOf_mov, e]
                   · exact Or.inr e⟩

theorem copyR_nil {a b res : Need} (hcov : ∀ y, NMem a y ∨ NMem b y → NMem res y) : CopyR a b res [] :=
  ⟨by simp [defsOf], fun _ h => absurd h List.not_mem_nil, fun y hy => Or.inr (hcov y hy)⟩

/-- Two copies side by side, and a move `M` of the top. -/
theorem copyR_join {a1 b1 a2 b2 a b a' b' res : Need} {A1 A2 M : List Pole} {U1 U2 T : Nat → Prop}
    (C1 : CopyR a1 b1 a' A1) (C2 : CopyR a2 b2 b' A2)
    (u1 : ∀ y, NMem a1 y ∨ NMem b1 y ∨ NMem a' y → U1 y) (u2 : ∀ y, NMem a2 y ∨ NMem b2 y ∨ NMem b' y → U2 y)
    (d12 : ∀ y, U1 y → ¬ U2 y) (t1 : ∀ y, T y → ¬ U1 y) (t2 : ∀ y, T y → ¬ U2 y)
    (hres : ∀ y, NMem res y ↔ T y ∨ NMem a' y ∨ NMem b' y)
    (hab : ∀ y, NMem a y ∨ NMem b y → (NMem a1 y ∨ NMem b1 y) ∨ (NMem a2 y ∨ NMem b2 y) ∨ T y ∨ y ∈ defsOf M)
    (s1 : ∀ y, NMem a1 y ∨ NMem b1 y → NMem a y ∨ NMem b y) (s2 : ∀ y, NMem a2 y ∨ NMem b2 y → NMem a y ∨ NMem b y)
    (hM : ∀ op ∈ M, ∃ s d, op = Pole.mov s d ∧ T s ∧ (NMem a d ∨ NMem b d) ∧ ¬ U1 d ∧ ¬ U2 d ∧ ¬ T d)
    (hMn : (defsOf M).Nodup) : CopyR a b res (A2 ++ A1 ++ M) := by
  obtain ⟨n1, m1, c1⟩ := C1
  obtain ⟨n2, m2, c2⟩ := C2
  have d1 : ∀ y ∈ defsOf A1, U1 y := fun y hy => by
    obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hy
    obtain ⟨s, d, rfl, -, hd', -⟩ := m1 op hop
    simp [aliasDst] at hd; subst hd
    exact u1 _ (hd'.elim Or.inl (fun e => Or.inr (Or.inl e)))
  have d2 : ∀ y ∈ defsOf A2, U2 y := fun y hy => by
    obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hy
    obtain ⟨s, d, rfl, -, hd', -⟩ := m2 op hop
    simp [aliasDst] at hd; subst hd
    exact u2 _ (hd'.elim Or.inl (fun e => Or.inr (Or.inl e)))
  have dM : ∀ y ∈ defsOf M, ¬ U1 y ∧ ¬ U2 y ∧ ¬ T y := fun y hy => by
    obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hy
    obtain ⟨s, d, rfl, -, -, h1, h2, h3⟩ := hM op hop
    simp [aliasDst] at hd; subst hd; exact ⟨h1, h2, h3⟩
  refine ⟨?_, fun op hop => ?_, fun y hy => ?_⟩
  · rw [defsOf_append, defsOf_append]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨n2, n1, ?_⟩, hMn, ?_⟩
    · intro x hx y hy e; subst e; exact d12 x (d1 x hy) (d2 x hx)
    · intro x hx y hy e; subst e
      rcases List.mem_append.mp hx with hx | hx
      · exact (dM x hy).2.1 (d2 x hx)
      · exact (dM x hy).1 (d1 x hx)
  · rcases List.mem_append.mp hop with hop | hop
    · rcases List.mem_append.mp hop with hop | hop
      · obtain ⟨s, d, rfl, hs, hd, hn⟩ := m2 op hop
        refine ⟨s, d, rfl, (hres s).mpr (Or.inr (Or.inr hs)), s2 d hd, fun e => ?_⟩
        have hU : U2 d := u2 d (hd.elim Or.inl (fun e => Or.inr (Or.inl e)))
        rcases (hres d).mp e with e | e | e
        · exact t2 d e hU
        · exact d12 d (u1 d (Or.inr (Or.inr e))) hU
        · exact hn e
      · obtain ⟨s, d, rfl, hs, hd, hn⟩ := m1 op hop
        refine ⟨s, d, rfl, (hres s).mpr (Or.inr (Or.inl hs)), s1 d hd, fun e => ?_⟩
        have hU : U1 d := u1 d (hd.elim Or.inl (fun e => Or.inr (Or.inl e)))
        rcases (hres d).mp e with e | e | e
        · exact t1 d e hU
        · exact hn e
        · exact d12 d hU (u2 d (Or.inr (Or.inr e)))
    · obtain ⟨s, d, rfl, hs, hd, h1, h2, h3⟩ := hM op hop
      refine ⟨s, d, rfl, (hres s).mpr (Or.inl hs), hd, fun e => ?_⟩
      rcases (hres d).mp e with e | e | e
      · exact h3 e
      · exact h1 (u1 d (Or.inr (Or.inr e)))
      · exact h2 (u2 d (Or.inr (Or.inr e)))
  · rw [defsOf_append, defsOf_append]
    simp only [List.mem_append]
    rcases hab y hy with e | e | e | e
    · rcases c1 y e with e' | e'
      · exact Or.inl (Or.inl (Or.inr e'))
      · exact Or.inr ((hres y).mpr (Or.inr (Or.inl e')))
    · rcases c2 y e with e' | e'
      · exact Or.inl (Or.inl (Or.inl e'))
      · exact Or.inr ((hres y).mpr (Or.inr (Or.inr e')))
    · exact Or.inr ((hres y).mpr (Or.inl e))
    · exact Or.inl (Or.inr e)

theorem nmem_consNeed_iff {a b : Need} {y : Nat} : NMem (consNeed a b) y ↔ NMem a y ∨ NMem b y := by
  unfold consNeed
  split
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; simp [NMem]
  · simp [NMem]

/-- **The moves of `+copy-need-make-ops`.** -/
theorem copyNeed_raw [HoonMapKeys Map] : ∀ (a b : Need) (ops : List Pole) (g g' : Comp.Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → Distinct (Need.pair a b) → NB g.re a → NB g.re b →
    ∃ A, x.2 = A ++ ops ∧ CopyR a b x.1 A := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h _ _ _
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, copyR_nil fun y hy => hy.elim (fun e => e.elim) id⟩
  | this rl =>
    intro b ops g g' x h dab na nb
    obtain ⟨_, _, ap⟩ := dab
    have arl : ¬ NMem b rl := ap rl rfl
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, copyR_nil fun y hy => hy.elim id (fun e => e.elim)⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov rl rr], rfl, copyR_one rfl (Or.inr rfl) (fun e => arl (by simp [NMem] at e ⊢; omega)) ?_⟩
      intro y hy; simp only [NMem] at hy ⊢; omega
    | both x' hh tt =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov x' rl], rfl, copyR_one (Or.inl rfl) (Or.inl rfl) arl ?_⟩
      intro y hy; rcases hy with e | e
      · exact Or.inl e
      · exact Or.inr e
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlt := na rl rfl
      refine ⟨[Pole.mov g.re rl], rfl, copyR_one (Or.inl rfl) (Or.inl rfl) ?_ ?_⟩
      · rintro (e | e | e)
        · omega
        · exact arl (Or.inl e)
        · exact arl (Or.inr e)
      · intro y hy; rcases hy with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inr e)
  | both rl hl tl ihh iht =>
    intro b ops g g' x h dab na nb
    obtain ⟨⟨dhl, dtl, aphtl, nrh, nrt⟩, db, ap⟩ := dab
    have arl : ¬ NMem b rl := ap rl (Or.inl rfl)
    have hlt := na rl (Or.inl rfl)
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, copyR_nil fun y hy => hy.elim id (fun e => e.elim)⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov rl rr], rfl, copyR_one (Or.inl rfl) (Or.inr rfl) (fun e => ap rr e rfl) ?_⟩
      intro y hy; rcases hy with e | e
      · exact Or.inr e
      · exact Or.inl e
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
      obtain ⟨A1, e1, C1⟩ := ihh hr _ g g1 _ h1 ⟨dhl, dhr, fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inr (Or.inl e))⟩
        (fun y hy => na y (Or.inr (Or.inl hy))) (fun y hy => nb y (Or.inr (Or.inl hy)))
      obtain ⟨A2, e2, C2⟩ := iht tr _ g1 g2 _ h2 ⟨dtl, dtr, fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr (Or.inr e))⟩
        (fun y hy => Nat.lt_of_lt_of_le (na y (Or.inr (Or.inr hy))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nb y (Or.inr (Or.inr hy))) l1)
      simp only at e1 e2
      refine ⟨A2 ++ A1 ++ [Pole.mov x' rl], by rw [e2, e1]; simp, ?_⟩
      have nal : ∀ y, NMem hl y → y < g.re := fun y hy => na y (Or.inr (Or.inl hy))
      have nat : ∀ y, NMem tl y → y < g.re := fun y hy => na y (Or.inr (Or.inr hy))
      have nbl : ∀ y, NMem hr y → y < g.re := fun y hy => nb y (Or.inr (Or.inl hy))
      have nbt : ∀ y, NMem tr y → y < g.re := fun y hy => nb y (Or.inr (Or.inr hy))
      refine copyR_join (U1 := fun y => NMem hl y ∨ NMem hr y ∨ (g.re ≤ y ∧ y < g1.re))
        (U2 := fun y => NMem tl y ∨ NMem tr y ∨ (g1.re ≤ y ∧ y < g2.re)) (T := (· = x')) C1 C2 ?_ ?_ ?_ ?_ ?_
        (fun y => Iff.rfl) ?_ ?_ ?_ ?_ (by simp [defsOf_mov])
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m1 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m2 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e) (e' | e' | e')
        · exact aphtl y e e'
        · exact ap y (Or.inr (Or.inl e)) (Or.inr (Or.inr e'))
        · have := nal y e; omega
        · exact ap y (Or.inr (Or.inr e')) (Or.inr (Or.inl e))
        · exact aphtr y e e'
        · have := nbl y e; omega
        · have := nat y e'; omega
        · have := nbt y e'; omega
        · omega
      · rintro y rfl (e | e | e)
        · exact ap y (Or.inr (Or.inl e)) (Or.inl rfl)
        · exact nxh e
        · omega
      · rintro y rfl (e | e | e)
        · exact ap y (Or.inr (Or.inr e)) (Or.inl rfl)
        · exact nxt e
        · omega
      · rintro y ((e | e | e) | (e | e | e))
        · right; right; right; simp [defsOf_mov, e]
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inl (Or.inl e))
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inl (Or.inr e))
      · rintro y (e | e)
        · exact Or.inl (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inl e))
      · rintro y (e | e)
        · exact Or.inl (Or.inr (Or.inr e))
        · exact Or.inr (Or.inr (Or.inr e))
      · intro op hop; simp at hop; subst hop
        refine ⟨x', rl, rfl, rfl, Or.inl (Or.inl rfl), ?_, ?_, fun e => arl (by rw [e]; exact Or.inl rfl)⟩
        · rintro (e | e | e)
          · exact nrh e
          · exact arl (Or.inr (Or.inl e))
          · omega
        · rintro (e | e | e)
          · exact nrt e
          · exact arl (Or.inr (Or.inr e))
          · omega
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
      obtain ⟨A1, e1, C1⟩ := ihh p _ _ g1 _ h1 ⟨dhl, dp, fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inl e)⟩
        (fun y hy => Nat.lt_succ_of_lt (na y (Or.inr (Or.inl hy)))) (fun y hy => Nat.lt_succ_of_lt (nb y (Or.inl hy)))
      obtain ⟨A2, e2, C2⟩ := iht q _ g1 g2 _ h2 ⟨dtl, dq, fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr e)⟩
        (fun y hy => by have := na y (Or.inr (Or.inr hy)); omega)
        (fun y hy => by have := nb y (Or.inr hy); omega)
      simp only at e1 e2
      refine ⟨A2 ++ A1 ++ [Pole.mov g.re rl], by rw [e2, e1]; simp, ?_⟩
      have nal : ∀ y, NMem hl y → y < g.re := fun y hy => na y (Or.inr (Or.inl hy))
      have nat : ∀ y, NMem tl y → y < g.re := fun y hy => na y (Or.inr (Or.inr hy))
      have nbl : ∀ y, NMem p y → y < g.re := fun y hy => nb y (Or.inl hy)
      have nbt : ∀ y, NMem q y → y < g.re := fun y hy => nb y (Or.inr hy)
      refine copyR_join (U1 := fun y => NMem hl y ∨ NMem p y ∨ (g.re + 1 ≤ y ∧ y < g1.re))
        (U2 := fun y => NMem tl y ∨ NMem q y ∨ (g1.re ≤ y ∧ y < g2.re)) (T := (· = g.re)) C1 C2 ?_ ?_ ?_ ?_ ?_
        (fun y => Iff.rfl) ?_ ?_ ?_ ?_ (by simp [defsOf_mov])
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m1 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m2 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e) (e' | e' | e')
        · exact aphtl y e e'
        · exact ap y (Or.inr (Or.inl e)) (Or.inr e')
        · have := nal y e; omega
        · exact ap y (Or.inr (Or.inr e')) (Or.inl e)
        · exact apq y e e'
        · have := nbl y e; omega
        · have := nat y e'; omega
        · have := nbt y e'; omega
        · omega
      · rintro y rfl (e | e | e)
        · have := nal _ e; omega
        · have := nbl _ e; omega
        · omega
      · rintro y rfl (e | e | e)
        · have := nat _ e; omega
        · have := nbt _ e; omega
        · omega
      · rintro y ((e | e | e) | (e | e))
        · right; right; right; simp [defsOf_mov, e]
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inl (Or.inl e))
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inl (Or.inr e))
      · rintro y (e | e)
        · exact Or.inl (Or.inr (Or.inl e))
        · exact Or.inr (Or.inl e)
      · rintro y (e | e)
        · exact Or.inl (Or.inr (Or.inr e))
        · exact Or.inr (Or.inr e)
      · intro op hop; simp at hop; subst hop
        refine ⟨g.re, rl, rfl, rfl, Or.inl (Or.inl rfl), ?_, ?_, fun e => by omega⟩
        · rintro (e | e | e)
          · exact nrh e
          · exact arl (Or.inl e)
          · omega
        · rintro (e | e | e)
          · exact nrt e
          · exact arl (Or.inr e)
          · omega
  | pair pl ql ihp ihq =>
    intro b ops g g' x h dab na nb
    obtain ⟨⟨dpl, dql, apl⟩, db, ap⟩ := dab
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, copyR_nil fun y hy => hy.elim id (fun e => e.elim)⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlt := nb rr rfl
      refine ⟨[Pole.mov g.re rr], rfl, copyR_one (Or.inl rfl) (Or.inr rfl) ?_ ?_⟩
      · rintro (e | e | e)
        · omega
        · exact ap rr (Or.inl e) rfl
        · exact ap rr (Or.inr e) rfl
      · intro y hy; rcases hy with e | e
        · exact Or.inr (Or.inr e)
        · exact Or.inl e
    | pair pr qr =>
      obtain ⟨dpr, dqr, apr⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨l2, m2⟩ := copy_mem h2
      obtain ⟨A1, e1, C1⟩ := ihp pr _ g g1 _ h1 ⟨dpl, dpr, fun y hy e => ap y (Or.inl hy) (Or.inl e)⟩
        (fun y hy => na y (Or.inl hy)) (fun y hy => nb y (Or.inl hy))
      obtain ⟨A2, e2, C2⟩ := ihq qr _ g1 g2 _ h2 ⟨dql, dqr, fun y hy e => ap y (Or.inr hy) (Or.inr e)⟩
        (fun y hy => Nat.lt_of_lt_of_le (na y (Or.inr hy)) l1) (fun y hy => Nat.lt_of_lt_of_le (nb y (Or.inr hy)) l1)
      simp only at e1 e2
      refine ⟨A2 ++ A1 ++ [], by rw [e2, e1]; simp, ?_⟩
      refine copyR_join (U1 := fun y => NMem pl y ∨ NMem pr y ∨ (g.re ≤ y ∧ y < g1.re))
        (U2 := fun y => NMem ql y ∨ NMem qr y ∨ (g1.re ≤ y ∧ y < g2.re)) (T := fun _ => False) C1 C2 ?_ ?_ ?_
        (fun _ e => e.elim) (fun _ e => e.elim) (fun y => by rw [nmem_consNeed_iff]; simp) ?_ ?_ ?_
        (fun _ h => absurd h List.not_mem_nil) (by simp [defsOf])
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m1 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m2 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e) (e' | e' | e')
        · exact apl y e e'
        · exact ap y (Or.inl e) (Or.inr e')
        · have := na y (Or.inl e); omega
        · exact ap y (Or.inr e') (Or.inl e)
        · exact apr y e e'
        · have := nb y (Or.inl e); omega
        · have := na y (Or.inr e'); omega
        · have := nb y (Or.inr e'); omega
        · omega
      · rintro y ((e | e) | (e | e))
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inl (Or.inl e))
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inl (Or.inr e))
      · rintro y (e | e)
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inl e)
      · rintro y (e | e)
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inr e)
    | both x' hh tt =>
      obtain ⟨dhh, dtt, aph, nxh, nxt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨l2, m2⟩ := copy_mem h2
      have xlt := nb x' (Or.inl rfl)
      obtain ⟨A1, e1, C1⟩ := ihp hh _ g g1 _ h1 ⟨dpl, dhh, fun y hy e => ap y (Or.inl hy) (Or.inr (Or.inl e))⟩
        (fun y hy => na y (Or.inl hy)) (fun y hy => nb y (Or.inr (Or.inl hy)))
      obtain ⟨A2, e2, C2⟩ := ihq tt _ g1 g2 _ h2 ⟨dql, dtt, fun y hy e => ap y (Or.inr hy) (Or.inr (Or.inr e))⟩
        (fun y hy => Nat.lt_of_lt_of_le (na y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nb y (Or.inr (Or.inr hy))) l1)
      simp only at e1 e2
      refine ⟨A2 ++ A1 ++ [], by rw [e2, e1]; simp, ?_⟩
      refine copyR_join (U1 := fun y => NMem pl y ∨ NMem hh y ∨ (g.re ≤ y ∧ y < g1.re))
        (U2 := fun y => NMem ql y ∨ NMem tt y ∨ (g1.re ≤ y ∧ y < g2.re)) (T := (· = x')) C1 C2 ?_ ?_ ?_ ?_ ?_
        (fun y => Iff.rfl) ?_ ?_ ?_ (fun _ h => absurd h List.not_mem_nil) (by simp [defsOf])
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m1 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases m2 y e with (e | e) | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      · rintro y (e | e | e) (e' | e' | e')
        · exact apl y e e'
        · exact ap y (Or.inl e) (Or.inr (Or.inr e'))
        · have := na y (Or.inl e); omega
        · exact ap y (Or.inr e') (Or.inr (Or.inl e))
        · exact aph y e e'
        · have := nb y (Or.inr (Or.inl e)); omega
        · have := na y (Or.inr e'); omega
        · have := nb y (Or.inr (Or.inr e')); omega
        · omega
      · rintro y rfl (e | e | e)
        · exact ap y (Or.inl e) (Or.inl rfl)
        · exact nxh e
        · omega
      · rintro y rfl (e | e | e)
        · exact ap y (Or.inr e) (Or.inl rfl)
        · exact nxt e
        · omega
      · rintro y ((e | e) | (e | e | e))
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inl (Or.inl e))
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inl (Or.inr e))
      · rintro y (e | e)
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
      · rintro y (e | e)
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inr (Or.inr e))

/-! ## `+copy` -/

theorem copyR_reads {a b res : Need} {A : List Pole} (C : CopyR a b res A) {y : Nat} (h : OpsRF A y) : NMem res y := by
  obtain ⟨op, hop, hr⟩ := opsRF_mem h
  obtain ⟨s, d, rfl, hs, -, -⟩ := C.2.1 op hop
  rw [reads_mov] at hr; subst hr; exact hs

theorem copyR_dsts {a b res : Need} {A : List Pole} (C : CopyR a b res A) {y : Nat} (h : y ∈ defsOf A) :
    (NMem a y ∨ NMem b y) ∧ ¬ NMem res y := by
  obtain ⟨op, hop, hd⟩ := mem_defsOf.mp h
  obtain ⟨s, d, rfl, -, h1, h2⟩ := C.2.1 op hop
  simp [aliasDst] at hd; subst hd; exact ⟨h1, h2⟩

theorem copyR_tr {a b res : Need} {A : List Pole} (C : CopyR a b res A) : ∀ op ∈ A, trOp op = false := by
  intro op hop
  obtain ⟨s, d, rfl, -⟩ := C.2.1 op hop
  rfl

/-- **`+copy`**: a new block that hops to the first code, with the moves in
front; it defines registers of the two needs that the merged need does not
keep. -/
theorem raw_copy [HoonMapKeys Map] {first : Next S} {second : Sure S} {g g' : Comp.Gen Map} {nex : Next S}
    (h : SIP X ρ lo g) (ha : first.th.args = []) (hj : first.th.there < g.bo)
    (dab : Distinct (Need.pair first.laz.ned second.ned)) (n1 : NB g.re first.laz.ned) (n2 : NB g.re second.ned)
    (hf : ∀ y, NMem first.laz.ned y ∨ NMem second.ned y → ¬ Defd g.blocks y)
    (hc : copy first second g = some (nex, g')) :
    SIP X ρ lo g' ∧ nex.th = jmp0 g.bo ∧ g'.bo = g.bo + 1 ∧ g.re ≤ g'.re ∧
      (∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧
      (∀ y, Live g'.blocks g.bo y → NMem nex.laz.ned y ∨
        (Live g.blocks first.th.there y ∧ ¬ NMem first.laz.ned y ∧ ¬ NMem second.ned y)) ∧
      (∀ y, Defd g'.blocks y → Defd g.blocks y ∨
        ((NMem first.laz.ned y ∨ NMem second.ned y) ∧ ¬ NMem nex.laz.ned y)) := by
  simp only [copy] at hc
  obtain ⟨o, g1, h1, hc⟩ := bind_some hc
  obtain ⟨S1, rfl, e1, q1, bo1⟩ := sip_emit h (emitOK_hop ha hj) h1
  obtain ⟨laz, g2, h2, hc⟩ := bind_some hc
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [copyLazy] at h2
  obtain ⟨⟨ned, ops⟩, g3, h3, h2⟩ := bind_some h2
  obtain ⟨u, g4, h4, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨_, _, c3⟩ := copyNeed_spec _ _ _ _ _ _ h3
  have n1' : NB g1.re first.laz.ned := by rw [q1]; exact n1
  have n2' : NB g1.re second.ned := by rw [q1]; exact n2
  obtain ⟨-, -, rg⟩ := keeps_copyNeed h3 n1' n2'
  obtain ⟨B, eB, C⟩ := copyNeed_raw _ _ _ _ _ _ h3 dab n1' n2'
  simp only [List.append_nil] at eB
  simp only at h4
  rw [eB] at h4
  have S3 : SIP X ρ lo g3 := by rw [c3.gen]; exact sip_reg S1 c3.le
  have b3 : g3.blocks = g1.blocks := by rw [c3.gen]
  have bo3 : g3.bo = g1.bo := by rw [c3.gen]
  have dd : ∀ y, Defd g1.blocks y ↔ Defd g.blocks y := fun y => by
    rw [e1, defd_put (h.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have P : OpsOK g3 B :=
    ⟨by simp only at rg; rw [eB] at rg; exact rg, C.1, fun y hy d => by
      rw [b3, dd] at d
      exact hf y (copyR_dsts C hy).1 d, copyR_tr C⟩
  obtain ⟨S4, b', hb', e4, q4, o4⟩ := sip_addOps S3 P h4
  rw [b3, e1, get_put_self] at hb'; cases hb'
  have below : ∀ k, k < g.bo → HoonMap.get g4.blocks k = HoonMap.get g.blocks k := fun k hk => by
    rw [e4, get_put_ne (by omega), b3, e1, get_put_ne (by omega)]
  refine ⟨S4, rfl, by rw [o4, bo3, bo1], by rw [q4]; have := c3.le; omega, below, fun y hy => ?_, fun y hy => ?_⟩
  · have hk : HoonMap.get g4.blocks g.bo = some ⟨[], B ++ [], Termin.hop first.th⟩ := by
      rw [e4]; exact get_put_self
    rcases live_unfoldP hk (h.below g.bo) below (fun j hj' => by simp [getJmps] at hj'; subst hj'; exact hj) hy with
      ⟨-, hr⟩ | ⟨j, hj', hl, hn'⟩
    · simp only [List.append_nil] at hr
      rcases hr with hr | ⟨-, hr⟩
      · exact Or.inl (copyR_reads C hr)
      · simp [finRegs, jmpRegs_nil ha] at hr
    · simp [getJmps] at hj'; subst hj'
      have hnA : y ∉ defsOf B := fun e => hn' (by simp [blockDefs]; exact mem_defsOf.mp e)
      by_cases e : NMem first.laz.ned y ∨ NMem second.ned y
      · rcases C.2.2 y e with e' | e'
        · exact absurd e' hnA
        · exact Or.inl e'
      · exact Or.inr ⟨hl, fun e' => e (Or.inl e'), fun e' => e (Or.inr e')⟩
  · rw [e4, defd_prepend (by rw [b3, e1]; exact get_put_self), b3, dd] at hy
    rcases hy with d | d
    · exact Or.inl d
    · exact Or.inr (copyR_dsts C d)

end Raw
end SkaModel
end Formalization
