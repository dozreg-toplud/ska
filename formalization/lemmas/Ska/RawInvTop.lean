import lemmas.Ska.RawInvKern
import lemmas.Ska.CompWhole

/-!
# Raw `+comp` output meets the optimizer's invariant, on the first fragment

README Gaps 14.  The main theorems of track D:

* **`optIn_finish`**: the raw blocks of `finish` (the final pass of
  `+compile-scc-in` with `run`, `+need-ord-alloc-regs`, `+coerce-lazy` and
  the renaming path of `+to-straight`) meet `OptIn`, when nothing is baked.
* **`optIn_finishLF`**: the same for `finishLF` (the whole of
  `+to-straight`), on the first fragment (`Frag nm CGoal.done`: no call,
  no `%6`, no hint).
* **`optIn_finishLU`**: the whole-subject version `finishLU`
  (`+compile-unary`: `+kerf` and `+kern`), on the first fragment.
* `rawDInv_finishLF`, `rawDInv_finishLU`: the form the field `rawDInv` of
  `CompHypOf.lean` asks (`Opt.DInvS` of the blocks), and `DInvR`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem si_gen0 : SI (gen0 : Comp.Gen Map) :=
  ⟨rfl, by simp [gen0], fun k b hb => by simp [gen0, HoonMap.get_empty] at hb,
    fun k b hb => by simp [gen0, HoonMap.get_empty] at hb, fun k b hb => by simp [gen0, HoonMap.get_empty] at hb,
    fun k b hb => by simp [gen0, HoonMap.get_empty] at hb,
    fun k k' b b' r hb => by simp [gen0, HoonMap.get_empty] at hb,
    fun k b hb => by simp [gen0, HoonMap.get_empty] at hb, fun k b hb => by simp [gen0, HoonMap.get_empty] at hb,
    fun z bz y b j r x hz => by simp [gen0, HoonMap.get_empty] at hz⟩

theorem live_congr {bl bl' : Map Blob} (he : ∀ k, HoonMap.get bl k = HoonMap.get bl' k) {k r : Nat}
    (h : Live bl k r) : Live bl' k r := by
  induction h with
  | here hb hr => exact Live.here (by rw [← he]; exact hb) hr
  | next hb hj _ hd ih => exact Live.next (by rw [← he]; exact hb) hj ih hd

/-- What the top-level run gives. -/
theorem top_run {nm : Nomm} {nex : Next S} {g1 : Comp.Gen Map}
    (h1 : run nm (CGoal.done : CGoal S) (gen0 : Comp.Gen Map) = some (nex, g1)) :
    SI g1 ∧ (∀ r, Live g1.blocks nex.th.there r → NMem nex.laz.ned r) ∧ NB g1.re nex.laz.ned ∧
      Distinct nex.laz.ned ∧ (∀ x, Defd g1.blocks x → ¬ NMem nex.laz.ned x) ∧ nex.th.args = [] ∧
      1 ≤ nex.th.there ∧ nex.th.there < g1.bo ∧ Down g1.blocks ∧
      ∃ B fin, HoonMap.get g1.blocks nex.th.there = some ⟨[], B, fin⟩ := by
  have S0 : SI (gen0 : Comp.Gen Map) := si_gen0
  have nd0 : ∀ r, Defd (gen0 : Comp.Gen Map).blocks r → ¬ GMem (CGoal.done : CGoal S) r := fun r _ e => e
  obtain ⟨S1, L1⟩ := run_raw nm CGoal.done gen0 g1 nex S0 trivial trivial trivial trivial nd0 h1
  obtain ⟨-, -, nb1, d1, s1, dd1, a1, lo1, hi1⟩ := sub_facts (goal := (CGoal.done : CGoal S)) S0 trivial trivial
    trivial trivial h1
  obtain ⟨D1, B, fin, hB⟩ := runDown (S := S) (Map := Map) nm nex g1 h1
  refine ⟨S1, fun r hl => (L1 r hl).elim id (fun e => e.elim), nb1, d1, defd_next S0 nd0 s1 dd1, a1, lo1, hi1, D1,
    B, fin, hB⟩

/-- **The final pass of `member`, with nothing baked, meets `OptIn`.** -/
theorem optIn_finish [MapKeys Map] {nm : Nomm} {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finish (S := S) (Map := Map) nm ord less bake = some c') : OptIn c'.blocks := by
  unfold finish at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  split at h
  · cases h
  obtain ⟨⟨nedF, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hbake] at h
  simp only [List.map_nil] at h
  obtain ⟨⟨u3, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u4, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨S1, L1, nb1, d1, nd1, a1, lo1, hi1, D1, B, fin, hB⟩ := top_run h1
  generalize hE : nex.th.there = E at *
  obtain ⟨⟨k2, e2⟩, l2, dF, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  -- `+coerce-lazy`
  simp only [coerceLazy] at h3
  obtain ⟨lok, g2', hl, h3⟩ := bind_some h3
  obtain ⟨lk, -, el⟩ := Option.map_eq_some_iff.mp hl
  simp only [Prod.mk.injEq] at el
  obtain ⟨rfl, rfl⟩ := el
  obtain ⟨tgt, g2a, ht, h3⟩ := bind_some h3
  have L := sureRequireLook_spec ht
  obtain ⟨ka, ea⟩ := L.gen
  have la := L.le
  have keepT : ∀ y, NMem nex.laz.ned y → NMem tgt y := fun y hy => sureRequireLook_keeps ht hy
  have S2a : SI g2a := by rw [ea, e2]; exact si_reg (si_reg S1 l2) (by rw [ea] at la; simpa [e2] using la)
  have b2a : g2a.blocks = g1.blocks := by rw [ea, e2]
  have dT : Distinct tgt := L.dist d1 (fun y hy => by have := nb1 y hy; simp [e2] at l2 ⊢; omega)
  have mT : ∀ y, NMem tgt y → NMem nex.laz.ned y ∨ (g2.re ≤ y ∧ y < g2a.re) := L.mem
  have hb2a : HoonMap.get g2a.blocks E = some ⟨[], B, fin⟩ := by rw [b2a]; exact hB
  obtain ⟨S3, bo3, l3, A, get3, rf3, cv3, df3⟩ := raw_sureLoop nedF tgt g2a g3 _ u3 S2a hb2a dT
    (fun y hy => by rcases mT y hy with e | e
                    · have := nb1 y e; omega
                    · exact e.2)
    (fun y hy => by have := (mF y hy).2; omega)
    (fun y hy ht' => by
      have := mF y hy
      rcases mT y ht' with e | e
      · have := nb1 y e; omega
      · omega)
    (fun y hy d => by
      rw [b2a] at d
      rcases mT y hy with e | e
      · exact nd1 y d e
      · have := S1.defd_lt d; omega) h3
  obtain ⟨S4, b3', hb3', e4, -, -⟩ := si_addOps S3 (opsOK_nil g3) h4
  rw [get3, if_pos rfl] at hb3'
  cases hb3'
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get (HoonMap.put g1.blocks E (pre A ⟨[], B, fin⟩)) k := by
    intro k
    rw [e4]
    by_cases e : k = E
    · subst e; simp [get_put_self, pre_nil]
    · rw [get_put_ne e, get3, if_neg e, b2a, get_put_ne e]
  have D4 : Down g4.blocks := by
    refine downRk_of_fins D1.rank fun k b' hk => ?_
    rw [get4] at hk
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact ⟨_, hB, rfl⟩
    · exact ⟨b', hk, rfl⟩
  have dd4 : ∀ y, Defd g4.blocks y ↔ Defd g1.blocks y ∨ y ∈ defsOf A := fun y => by
    rw [← defd_prepend hB]; simp only [defd_iff, get4]
  exact optIn_toStraight h D4 S4.nd S4.cr S4.tr (downPar_of_args S4.aa S4.jd)
    (fun r hl => by
      have hl' := live_congr get4 hl
      rcases live_prepend hB (S1.below E) (fun j hj => S1.jd E _ hB j hj) hl' with ⟨-, e⟩ | ⟨hn, e⟩
      · exact rf3 r e
      · exact absurd (cv3 r (keepT r (L1 r e))) hn)
    (fun r hr d => by
      have := mF r hr
      rcases (dd4 r).mp d with d | d
      · have := S1.defd_lt d; omega
      · rcases df3 r d with e | e
        · rcases mT r e with e' | e'
          · have := nb1 r e'; omega
          · omega
        · omega)

/-- On the first fragment the run of `runL` makes no proxy. -/
theorem runL_cond_frag {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {nex : NextL S} {g1 : Comp.Gen Map}
    (h : runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1)) :
    g1.cond = (gen0 : Comp.Gen Map).cond := by
  rw [show (CGoalL.done : CGoalL S) = CGoal.toL CGoal.done from rfl, runL_frag hf] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  rw [← e.2]
  exact (kc_run nm CGoal.done).keep _ n g hr

/-- **The n-ary final pass meets `OptIn` on the first fragment.** -/
theorem optIn_finishLF [MapKeys Map] {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {ord : NeedOrd}
    {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : OptIn c'.blocks := by
  rw [finishLF_eq hbake (fun _ _ h1 => runL_cond_frag hf h1)] at h
  rw [finishL_eq (frag_pure_noSix nm _ hf).1 (frag_pure_noSix nm _ hf).2] at h
  exact optIn_finish hbake h

/-- **The whole-subject version meets `OptIn` on the first fragment.** -/
theorem optIn_finishLU [MapKeys Map] {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {c' : Straight Map}
    (h : finishLU (S := S) (Map := Map) nm = some c') : OptIn c'.blocks := by
  unfold finishLU at h
  obtain ⟨⟨nexL, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  rw [show (CGoalL.done : CGoalL S) = CGoal.toL CGoal.done from rfl, runL_frag hf] at h1
  obtain ⟨⟨nex, g1'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, e1⟩ := e
  subst g1'
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  obtain ⟨S1, L1, nb1, d1, nd1, a1, lo1, hi1, D1, B, fin, hB⟩ := top_run hr
  have cond1 : g1.cond = (gen0 : Comp.Gen Map).cond := (kc_run nm CGoal.done).keep _ nex g1 hr
  -- `+kerf`
  simp only [kerf] at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  simp only [Next.toL_th] at he
  obtain ⟨Se, rfl, ee, qe, boe⟩ := si_emit S1 (emitOK_hop a1 hi1) he
  obtain ⟨r, g3, h3, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
  simp only [Next.toL_laz, kern] at h3
  obtain ⟨r0, g5, h5, h3⟩ := bind_some h3
  obtain ⟨S5, rfl, q5, b5, o5⟩ := si_re Se h5
  obtain ⟨g6, g6', h6, h3⟩ := bind_some h3
  rw [get_apply] at h6
  simp only [Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rw [S5.drop] at h3
  simp only [Bool.false_eq_true, if_false, walkLazy_ofSure] at h3
  obtain ⟨u7, g7, h7, h3⟩ := bind_some h3
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  -- the gate of `+kern` at the new block
  have hbo : HoonMap.get g5.blocks g1.bo = some ⟨[], [], Termin.hop nex.th⟩ := by rw [b5, ee]; exact get_put_self
  have below5 : ∀ k, k < g1.bo → HoonMap.get g5.blocks k = HoonMap.get g1.blocks k := fun k hk => by
    rw [b5, ee, get_put_ne (by omega)]
  have dd5 : ∀ y, Defd g5.blocks y ↔ Defd g1.blocks y := fun y => by
    rw [b5, ee, defd_put (S1.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have G : SI g7 ∧ g7.cond = g5.cond ∧ ∃ A, (∀ k, HoonMap.get g7.blocks k =
      if k = g1.bo then some ⟨[], A, Termin.hop nex.th⟩ else HoonMap.get g5.blocks k) ∧
      (∀ y, OpsRF A y → y = ge.re) ∧ (∀ y, NMem nex.laz.ned y → y ∈ defsOf A) ∧
      (∀ y, Defd g7.blocks y ↔ Defd g1.blocks y ∨ y ∈ defsOf A) ∧ ge.re ∉ defsOf A := by
    obtain ⟨u8, g8, h8, h7'⟩ := bind_some h7
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h7'
    obtain ⟨-, e78⟩ := h7'
    subst g8
    obtain ⟨ned, g9, h9, h7⟩ := bind_some h8
    have L := sureRequireLook_spec h9
    obtain ⟨k9, e9⟩ := L.gen
    have l9 := L.le
    have S9 : SI g9 := by rw [e9]; exact si_reg S5 (by rw [e9] at l9; exact l9)
    have b9 : g9.blocks = g5.blocks := by rw [e9]
    have keep : ∀ y, NMem nex.laz.ned y → NMem ned y := fun y hy => sureRequireLook_keeps h9 hy
    by_cases hn : ned = Need.none
    · rw [if_pos hn] at h7
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h7
      obtain ⟨-, rfl⟩ := h7
      refine ⟨S9, by rw [e9], [], fun k => ?_, fun y hy => hy.elim, fun y hy => by
        have := keep y hy; rw [hn] at this; exact this.elim, fun y => by rw [b9, dd5]; simp [defsOf],
        by simp [defsOf]⟩
      rw [b9]; by_cases e : k = g1.bo
      · subst e; rw [if_pos rfl, hbo]
      · rw [if_neg e]
    rw [if_neg hn] at h7
    obtain ⟨src, g10, h10, h7⟩ := bind_some h7
    simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h10
    obtain ⟨rfl, rfl⟩ := h10
    simp only [noSoft, Bool.false_eq_true, if_false] at h7
    obtain ⟨ops, g11, h11, h7⟩ := bind_some h7
    have mN : ∀ y, NMem ned y → NMem nex.laz.ned y ∨ (g5.re ≤ y ∧ y < g9.re) := L.mem
    obtain ⟨A, eA, K⟩ := kernLoop_raw ned ge.re [] g9 g11 ops h11 (by omega)
      (fun e => by rcases mN _ e with e' | e'
                   · have := nb1 _ e'; omega
                   · omega)
      (fun y hy => by rcases mN y hy with e' | e'
                      · have := nb1 y e'; omega
                      · exact e'.2)
      (L.dist d1 (fun y hy => by have := nb1 y hy; omega))
    simp only [List.append_nil] at eA
    rw [eA] at h7
    have S11 : SI g11 := by rw [K.gen]; exact si_reg S9 K.le
    have b11 : g11.blocks = g5.blocks := by rw [K.gen, b9]
    have P : OpsOK g11 A := ⟨K.regs, K.nd, fun y hy d => by
        rw [b11, dd5] at d
        rcases K.defs y hy with e' | e'
        · rcases mN y e' with e'' | e''
          · exact nd1 y d e''
          · have := S1.defd_lt d; omega
        · have := S1.defd_lt d; omega, K.tr⟩
    obtain ⟨S7, b', hb', e7, q7, o7⟩ := si_addOps S11 P h7
    rw [b11, hbo] at hb'; cases hb'
    have c7 : g7.cond = g5.cond := by
      obtain ⟨b, -, e⟩ := addOps_spec h7 S11.drop
      rw [e]; simp only; rw [K.gen, e9]
    refine ⟨S7, c7, A, fun k => ?_, K.rf, fun y hy => K.cov y (keep y hy), fun y => ?_, K.nsrc⟩
    · rw [e7, b11]; by_cases e : k = g1.bo
      · subst e; simp [get_put_self]
      · simp [e, get_put_ne e]
    · rw [e7, defd_prepend (by rw [b11]; exact hbo), b11, dd5]
  obtain ⟨S7, c7, A, get7, rf7, cv7, dd7, ns7⟩ := G
  have c5 : g5.cond = ge.cond := by rw [re_apply] at h5; simp only [Option.some.injEq, Prod.mk.injEq] at h5; rw [← h5.2]
  have ce : ge.cond = g1.cond := by rw [emit_apply] at he; simp only [Option.some.injEq, Prod.mk.injEq] at he; rw [← he.2]; rfl
  have hc : ∀ k, HoonMap.get g7.cond k = Option.none := fun k => by
    rw [c7, c5, ce, cond1]; simp [gen0, HoonMap.get_empty]
  rw [toStraightF_eq hc (by simp [isRun, flattenNeed])] at h
  have g7lo : ∀ x, x < g1.bo → HoonMap.get g7.blocks x = HoonMap.get g1.blocks x := fun x hx => by
    rw [get7, if_neg (by omega), below5 x hx]
  have hk7 : HoonMap.get g7.blocks g1.bo = some ⟨[], A, Termin.hop nex.th⟩ := by rw [get7, if_pos rfl]
  have D7 : Down g7.blocks := by
    intro k b hk
    by_cases e : k = g1.bo
    · subst e; rw [hk7] at hk; cases hk
      refine ⟨S1.bo1, fun j hj => ?_⟩
      simp [finJumps] at hj; subst hj; exact ⟨lo1, hi1⟩
    · rw [get7, if_neg e, b5, ee, get_put_ne e] at hk
      exact D1 k b hk
  refine optIn_toStraight h D7 S7.nd S7.cr S7.tr (downPar_of_args S7.aa S7.jd) (fun y hl => ?_) (fun y hy d => ?_)
  · rcases live_unfold hk7 (S1.below g1.bo) g7lo (fun j hj => by simp [getJmps] at hj; subst hj; exact hi1) hl with
      ⟨-, hr⟩ | ⟨j, hj, hl', hn'⟩
    · rcases hr with hr | ⟨-, hr⟩
      · simp only [NMem]; exact rf7 y hr
      · simp [finRegs, jmpRegs_nil a1] at hr
    · simp [getJmps] at hj; subst hj
      exact absurd (by simp only [blockDefs, List.nil_append]; exact cv7 y (L1 y hl')) hn'
  · simp only [NMem] at hy; subst hy
    rcases (dd7 _).mp d with d | d
    · have := S1.defd_lt d; omega
    · exact ns7 d

/-! ## The forms the rest of the project asks -/

/-- The n-ary raw blocks meet `DInvR`, the driver's block invariant. -/
theorem dInvR_finishLF [MapKeys Map] {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {ord : NeedOrd}
    {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : DInvR c'.blocks :=
  optIn_iff.mp (optIn_finishLF hf hbake h)

/-- **The field `rawDInv` of `CompHypOf.lean`, n-ary, on the first fragment.** -/
theorem rawDInv_finishLF [MapKeys Map] {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {ord : NeedOrd}
    {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : DInvS c'.blocks :=
  dInvR_dInvS (dInvR_finishLF hf hbake h)

theorem dInvR_finishLU [MapKeys Map] {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {c' : Straight Map}
    (h : finishLU (S := S) (Map := Map) nm = some c') : DInvR c'.blocks :=
  optIn_iff.mp (optIn_finishLU hf h)

/-- **The field `rawDInv` of `CompHypOf.lean`, whole subject, on the first
fragment.** -/
theorem rawDInv_finishLU [MapKeys Map] {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {c' : Straight Map}
    (h : finishLU (S := S) (Map := Map) nm = some c') : DInvS c'.blocks :=
  dInvR_dInvS (dInvR_finishLU hf h)

/-- **`+optimize` keeps the n-ary code of the first fragment** (with the
passes of the Hoon: the model of `+alias` with `pickR`, the real
`+trim-trace-hints`, the model of `+switch-chains`). -/
theorem optimize_keeps_finishLF [MapKeys Map] (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' s' : Straight Map}
    (h : finishLF (S := S) (Map := Map) nm ord less bake = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') : Opt.Keeps c' s' :=
  optimize_keeps_optIn M (optIn_finishLF hf hbake h) ho

/-- **`+optimize` keeps the whole-subject code of the first fragment.** -/
theorem optimize_keeps_finishLU [MapKeys Map] (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {c' s' : Straight Map}
    (h : finishLU (S := S) (Map := Map) nm = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') : Opt.Keeps c' s' :=
  optimize_keeps_optIn M (optIn_finishLU hf h) ho

end Raw
end SkaModel
end Formalization
