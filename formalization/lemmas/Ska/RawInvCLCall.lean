import lemmas.Ska.RawInvCLFive
import lemmas.Ska.RawInvKern

/-!
# The run-level liveness with calls: the arm `%2` (the indirect call)

README Gaps 14 (b), track D.  The field `n2` of `ArmsL`.  `callL` on an
indirect call: `+simple-next`, `+kerf` (a fresh hop block `out` to the
goal, then `+kern` from a fresh register `pro`), `re` (`rSub`), `re`
(`rFol`), the block `[nok rSub rFol pro]` hopping to `out`, then the chain
of `five_tail` (`q` for "`rFol` at the `%nok` block", `+past`, `p` for
"`rSub` at the continuation", `+copy`).

* `walkList_prepE`, `walkLazy_prepE`: `walkLazy_prepD` with a state
  invariant `W` and the gate's hypothesis at the entries walked only.
* **`kernGate_stepW`**: the gate of `+kern` keeps `CW` (the invariant of
  `RawInvCLColSpec.lean`), only puts ops in front, reads first `r` or a
  proxy of it, and defines the entry's whole need (`kernLoop_raw`).
* **`kerfSpecL`** (`KerfSpecL`, checked first at every `+kerf` of the 2,856
  `PlainN` runs under the seven goals, 0 failures): the goal "`pro` at
  `out`" holds `IL`, and a register live at `out` with `pro` killed there is
  one the goal `nex.goal` may leave live.
* `oph_nok`: the `%nok` block, as `oph_eqq` of `RawInvCLFive.lean`.
* **`liveRun_n2`**, **`armsL_n2`**: `LR` of `[2 p q]` from `LR` of its
  parts.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Walks with a state invariant, the gate's hypothesis at the entries -/

theorem walkList_prepE {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {D : Nat → Prop} {W : Comp.Gen Map → Prop} :
    ∀ (es : List (Nat × Lazy S)),
    (∀ e ∈ es, ∀ g g', W g → f e.1 e.2.sure g = some ((), g') → St g g' ∧ W g' ∧ GStepD R D e.1 e.2.sure g g') →
    ∀ (g g' : Comp.Gen Map), W g → walkList f es g = some ((), g') → St g g' ∧ W g' ∧ WalkPD R D es g g'
  | [], _, g, g', hW, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hrf g, hW, fun _ => [], prep_nil _, fun e he => absurd he List.not_mem_nil, fun _ _ h => h.elim,
      fun _ h => absurd rfl h⟩
  | (x, l) :: rest, hf, g, g', hW, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨s1, W1, A, pA, kA, rA⟩ := hf (x, l) List.mem_cons_self g g1 hW h1
    obtain ⟨s2, W2, Q, pQ, kQ, rQ, eQ⟩ :=
      walkList_prepE hrf htr hR rest (fun e he => hf e (List.mem_cons_of_mem _ he)) g1 g' W1 h2
    refine ⟨htr _ _ _ s1 s2, W2, _, prep_trans pA pQ, fun e he r hr => ?_, fun k y hy => ?_, fun k hk => ?_⟩
    · rw [defsOf_append, List.mem_append]
      rcases List.mem_cons.mp he with rfl | he
      · rcases kA r hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (by simp only [if_pos rfl]; exact h))
      · rcases kQ e he r hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · rcases opsRF_append.mp hy with h | ⟨-, h⟩
      · exact rQ k y h
      · by_cases e : k = x
        · rw [if_pos e] at h
          exact hR _ _ _ s2 (rA y h)
        · rw [if_neg e] at h; exact h.elim
    · by_cases e : k = x
      · exact ⟨(x, l), List.mem_cons_self, e.symm⟩
      · have : Q k ≠ [] := by
          intro hq; apply hk; simp [hq, e]
        obtain ⟨e', he', ee⟩ := eQ k this
        exact ⟨e', List.mem_cons_of_mem _ he', ee⟩

theorem walkLazy_prepE {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {D : Nat → Prop} {W : Comp.Gen Map → Prop} {o : Nat} {l : Lazy S}
    (hf : ∀ e ∈ (o, l) :: entries l, ∀ g g', W g → f e.1 e.2.sure g = some ((), g') →
      St g g' ∧ W g' ∧ GStepD R D e.1 e.2.sure g g')
    {g0 g' : Comp.Gen Map} (hW : W g0) (h : walkLazy f o l g0 = some ((), g')) :
    St g0 g' ∧ W g' ∧ WalkPD R D ((o, l) :: entries l) g0 g' := by
  have e : (walkLazy f o l : CM Map Unit) = walkList f ((o, l) :: wentries l) := by
    rw [walkLazy_flat]; rfl
  rw [e] at h
  have hm : ∀ e, e ∈ (o, l) :: entries l ↔ e ∈ (o, l) :: wentries l := fun e =>
    ((wentries_perm l).cons (o, l)).mem_iff.symm
  obtain ⟨s, W', P, pP, kP, rP, eP⟩ :=
    walkList_prepE hrf htr hR _ (fun e he => hf e ((hm e).mpr he)) g0 g' hW h
  refine ⟨s, W', P, pP, fun e he => kP e ((hm e).mp he), rP, fun k hk => ?_⟩
  obtain ⟨e, he, ee⟩ := eP k hk
  exact ⟨e, (hm e).mpr he, ee⟩

/-! ## The gate of `+kern` -/

/-- **The gate of `+kern`** at an entry whose need is distinct, below `r`
and names no key of `C0`: it keeps `CW`, only puts ops in front, reads
first `r` or a proxy of it and defines the whole need. -/
theorem kernGate_stepW {r o B x : Nat} {C0 : Map (Nat × List Nat)} {s : Sure S}
    (hs : ∀ y, NMem s.ned y → y < r ∧ HoonMap.get C0 y = Option.none) (hds : Distinct s.ned)
    {g g' : Comp.Gen Map} (hW : CW r B C0 g) (h : kernGate r o x s g = some ((), g')) :
    CSt g g' ∧ CW r B C0 g' ∧ GStepD (RCol r) (fun _ => False) x s g g' := by
  have hrB := hW.rlt
  have hBg := hW.le
  unfold kernGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨k, rfl⟩ := L.gen
  have hgk : g.re ≤ k := L.le
  have W1 := cw_re hW hgk
  have S1 : CSt g ({ g with re := k } : Comp.Gen Map) :=
    ⟨⟨rfl, rfl, rfl, hgk, fun _ _ h => h, fun _ _ h => Or.inl h⟩, fun hc k' v hk => Nat.lt_of_lt_of_le (hc k' v hk) hgk⟩
  have hkeep : ∀ y, NMem s.ned y → NMem ned y := fun y hy => sureRequireLook_keeps h1 hy
  have hmem : ∀ y, NMem ned y → (y < r ∧ HoonMap.get g.cond y = Option.none) ∨ (g.re ≤ y ∧ y < k) := by
    intro y hy
    rcases L.mem y hy with h | h
    · obtain ⟨a, b⟩ := hs y h
      exact Or.inl ⟨a, hW.old (by omega) b⟩
    · exact Or.inr h
  by_cases en : ned = Need.none
  · rw [if_pos en] at h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    refine ⟨S1, W1, [], prep_same, fun y hy => ?_, fun y hy => hy.elim⟩
    have := hkeep y hy; rw [en] at this; exact this.elim
  rw [if_neg en] at h2
  obtain ⟨src, g2, h3, h4⟩ := bind_some h2
  obtain ⟨W2, -, hsrc, hre2, hc2, -⟩ := cw_src W1 h3
  obtain ⟨S2, R2, F2, B2⟩ := srcStep W1.drop W1.clt h3
  simp only [noSoft, Bool.false_eq_true] at h4
  obtain ⟨ops, g3, h5, h6⟩ := bind_some h4
  have hk2 : k ≤ g2.re := hre2
  have F2' : src = r ∨ k ≤ src := F2
  have nsrc : ¬ NMem ned src := by
    intro hm
    rcases hmem src hm with ⟨a, -⟩ | ⟨a, b⟩ <;> rcases F2' with e | e <;> omega
  have nb : NB g2.re ned := fun y hy => by
    rcases hmem y hy with ⟨a, -⟩ | ⟨-, b⟩
    · omega
    · omega
  have dn : Distinct ned := L.dist hds (fun y hy => by have := (hs y hy).1; omega)
  obtain ⟨A, hA, KRA⟩ := kernLoop_raw ned src [] g2 g3 ops h5 hsrc nsrc nb dn
  rw [List.append_nil] at hA
  subst hA
  have eg3 := KRA.gen
  have W3 : CW r B C0 g3 := by rw [eg3]; exact cw_re W2 KRA.le
  have hc3 : g3.cond = g2.cond := by rw [eg3]
  have hb3 : g3.blocks = g2.blocks := by rw [eg3]
  have hd3 : g3.drop = false := by rw [eg3]; exact W2.drop
  have W' : CW r B C0 g' := by
    refine cw_addOps W3 KRA.regs (fun y hy => ?_) h6
    rcases KRA.defs y hy with hm | ⟨a, -⟩
    · rcases hmem y hm with ⟨a, b⟩ | ⟨a, b⟩
      · refine ⟨by rw [hc3, hc2 y (show y < k by omega)]; exact b, by omega⟩
      · have hgy : HoonMap.get g.cond y = Option.none := by
          cases e : HoonMap.get g.cond y with
          | none => rfl
          | some v => have := hW.clt y v e; omega
        refine ⟨by rw [hc3, hc2 y (show y < k from b)]; exact hgy, by omega⟩
    · refine ⟨?_, by omega⟩
      rw [hc3]
      cases e : HoonMap.get g2.cond y with
      | none => rfl
      | some v => have := W2.clt y v e; omega
  obtain ⟨A3, c3, P3⟩ := addOps_step hd3 h6
  have S3 : CSt g2 g3 :=
    ⟨⟨by rw [eg3], by rw [eg3], by rw [eg3], KRA.le, fun k' v hk => by rw [hc3]; exact hk,
      fun k' v hk => Or.inl (by rw [← hc3]; exact hk)⟩,
     fun hc k' v hk => by rw [hc3] at hk; exact Nat.lt_of_lt_of_le (hc k' v hk) KRA.le⟩
  have S4 : CSt g3 g' := ⟨A3, fun hc k' v hk => by rw [c3] at hk; exact Nat.lt_of_lt_of_le (hc k' v hk) A3.2.2.2.1⟩
  refine ⟨S1.trans (S2.trans (S3.trans S4)), W', ops, ?_, fun y hy => Or.inr (KRA.cov y (hkeep y hy)), fun y hy => ?_⟩
  · have hb : g3.blocks = g.blocks := hb3.trans B2
    rw [← hb]; exact P3
  · rw [KRA.rf y hy]
    exact rCol_mono (S3.trans S4) R2

/-! ## `+kerf` -/

/-- **What `+kerf` must give** (checked at every `+kerf` of the `PlainN`
runs): the goal "`pro` at `out`" holds `IL`, and a register live at `out`
with `pro` killed there is one the goal `nex.goal` may leave live. -/
def KerfSpecL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (nex : NextL S) (g0 g1 : Comp.Gen Map) (out pro : Nat),
    IL K nex.goal g0 → (kerf nex : CM Map (Nat × Nat)) g0 = some ((out, pro), g1) →
    IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) g1 ∧
      LiveC K nex.goal g0 g1 ⟨ofSure (lazyReg (S := S) pro), jmp0 out⟩

/-- **The spec of `+kerf`.** -/
theorem kerfSpecL : KerfSpecL S Map := by
  intro K nex g0 g1 out pro hI0 h
  rcases nex with ⟨laz, th⟩
  have hI : IL K (CGoalL.next laz th) g0 := hI0
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hth, hap, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  obtain ⟨A1, KP1, hfr⟩ := (ht_kerf (⟨laz, th⟩ : NextL S)).run g0 _ g1 hI.ats ⟨bt, hbt, hpt, targs⟩ h
  have hER := hI.entry_regs (o := g0.bo)
  have hthere : th.there < g0.bo := hI.lab hbt
  simp only [kerf] at h
  obtain ⟨o, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, gk, hk, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rw [kern_eq] at hk
  obtain ⟨r', gr, hr, hk⟩ := bind_some hk
  rw [re_apply] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨hr1, hr2⟩ := hr
  have e1 : r' = g0.re := hr1.symm
  have e2 : gr = ({ g0.emitted (⟨[], [], Termin.hop th⟩ : Blob) with re := g0.re + 1 } : Comp.Gen Map) := hr2.symm
  subst e1 e2
  obtain ⟨g', gc, hc, hk⟩ := bind_some hk
  simp only [get_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  split at hk
  · rename_i hdd
    have : g0.drop = true := hdd
    rw [hd] at this; cases this
  obtain ⟨u, gw, hw, hk⟩ := bind_some hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨hk1, rfl⟩ := hk
  subst hk1
  -- the state after the hop block and `re`
  have hbD : blockDefs (⟨[], [], Termin.hop th⟩ : Blob) = [] := by simp [blockDefs]
  have W0 : CW g0.re (g0.re + 1) g0.cond
      ({ g0.emitted (⟨[], [], Termin.hop th⟩ : Blob) with re := g0.re + 1 } : Comp.Gen Map) := by
    refine ⟨hd, Nat.le_refl _, Nat.lt_succ_self _, fun k v hk => Nat.lt_succ_of_lt (hI.cond_lt k v hk),
      fun k b hb => ?_, fun y hy => ?_, fun hy => ?_, hI.cond_ge (Nat.le_refl _), fun k v hk => Or.inl hk⟩
    · change HoonMap.get (g0.emitted (⟨[], [], Termin.hop th⟩ : Blob)).blocks k = some b at hb
      rw [em_get hd] at hb
      split at hb
      · cases hb; exact blobIn_nil_fin (jmpIn_nil targs)
      · exact (hI.regs k b hb).mono fun _ hx => Nat.lt_succ_of_lt hx
    · have hy' : Defd g0.blocks y := (defd_emitted_nil hI.ats hbD).mp hy
      show HoonMap.get g0.cond y = Option.none
      cases e : HoonMap.get g0.cond y with
      | none => rfl
      | some v => exact absurd hy' (hI.cond y v e).2.1
    · have hy' : Defd g0.blocks g0.re := (defd_emitted_nil hI.ats hbD).mp hy
      have := defd_lt hI.regs hy'; omega
  obtain ⟨St, W1, P, hP, hkill, hread, -⟩ := walkLazy_prepE (St := CSt) (R := RCol g0.re) (D := fun _ => False)
    (W := CW g0.re (g0.re + 1) g0.cond) CSt.refl (fun _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ h hy => rCol_mono h hy)
    (fun e he g g' hW hg => kernGate_stepW (fun y hy => hER e he y hy) (by
      rcases List.mem_cons.mp he with rfl | he'
      · exact (hent _ List.mem_cons_self).2.1
      · exact (hent e (List.mem_cons_of_mem _ he')).2.1) hW hg) W0 hw
  have hre1 : g0.re + 1 ≤ gw.re := W1.le
  refine ⟨⟨A1, W1.regs, fun k v hk => ?_, hI.kvan.mono KP1.2.1, hfr, ?_, fun e he => ?_⟩, ?_⟩
  · refine ⟨W1.clt k v hk, fun hdk => ?_, fun hg => ?_, ?_, ?_⟩
    · rw [W1.nokey k hdk] at hk; cases hk
    · have e : k = g0.re := gregL_ofSure.mp hg
      subst e; rw [W1.rkey] at hk; cases hk
    · rcases W1.keys k v hk with h | ⟨h, -⟩
      · have := (hI.cond k v h).2.2.2.1; omega
      · rw [h]; omega
    · rcases W1.keys k v hk with h | ⟨h, -⟩
      · obtain ⟨-, -, -, k4, k5⟩ := hI.cond k v h
        exact W1.old (by omega) k5
      · rw [h]; exact W1.rkey
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hfr
    refine ⟨⟨b, hb, hp⟩, trivial, fun y hy => ?_⟩
    have e : y = g0.re := hy
    subst e
    exact ⟨by omega, W1.rdef⟩
  -- the liveness
  intro y hl
  have hyr : y ≠ g0.re := fun e => hl.nk (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩))
  have hc : ∀ x, x < g0.re + 1 → HoonMap.get gw.cond x = HoonMap.get g0.cond x := fun x hx => St.1.cond_below hx
  have hl2 := liveK_walkR (R0 := g0.re) hP hc W0.regs (fun k x hx => rCol_unproxy W1.rkey (hread k x hx)) hyr hl
  have hold : ∀ z, z < g0.re → HoonMap.get g0.cond z = Option.none → unproxy gw.cond z = z :=
    fun z hz hn => unproxy_none (W1.old (by omega) hn)
  have hget : HoonMap.get (unpM ({ g0.emitted (⟨[], [], Termin.hop th⟩ : Blob) with re := g0.re + 1 } :
      Comp.Gen Map)) g0.bo = some ⟨[], [], Termin.hop th⟩ := by
    have := unpM_emitted_self (g := g0) hd (⟨[], [], Termin.hop th⟩ : Blob)
    simp only [renBlob, renFin, renJmp_nil _ targs, List.map_nil] at this
    exact this
  show LiveK (unpM g0) (fun x z => K x z ∨ lazK th.there laz x z) th.there y
  cases hl2 with
  | here hb' hr _ =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨-, hr⟩ := hr
    rcases hr with hr | ⟨-, hr⟩
    · exact absurd hr (by simp [OpsRF])
    · simp [finRegs, jmpRegs, targs] at hr
  | next hb' hj hl3 _ hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    rw [getJmps_hop, List.mem_singleton] at hj
    subst hj
    have hroot : ¬ NMem laz.sure.ned y := by
      intro hm
      rcases hkill _ List.mem_cons_self y hm with h | h
      · exact h
      · apply hk'
        refine Or.inr ?_
        rw [defsOf_ren]
        obtain ⟨a, b⟩ := hER _ List.mem_cons_self y hm
        exact List.mem_map.mpr ⟨y, h, hold y a b⟩
    have hl4 := (liveK_frameP hI.downU (fun x hx => (unpM_emitted_lt (g := g0) hd _ hx).trans rfl) hthere).mp hl3
    refine hl4.mono_r fun x hx => ?_
    rcases hx with hk | ⟨e, he, ex, hm⟩
    · exact Or.inl (Or.inl hk)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hroot hm).elim
      · refine Or.inr ?_
        rcases hkill e (List.mem_cons_of_mem _ he) y hm with h | h
        · exact h.elim
        · rw [defsOf_ren]
          obtain ⟨a, b⟩ := hER e (List.mem_cons_of_mem _ he) y hm
          exact List.mem_map.mpr ⟨y, ex ▸ h, hold y a b⟩

/-! ## The `%nok` block -/

/-- The goal "`rq` at the block just emitted", `rq` old, undefined, no key,
not written by the block (whose writes are no keys). -/
theorem il_old_atD {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {b : Blob}
    (hp : b.par = []) (hbat : BATC g.blocks b) (hin : BlobIn (· < g.re) b)
    (hdef : ∀ r ∈ blockDefs b, HoonMap.get g.cond r = Option.none)
    {rq : Nat} (hq : rq < g.re) (hdq : ¬ Defd g.blocks rq) (hkq : HoonMap.get g.cond rq = Option.none)
    (hqd : rq ∉ blockDefs b) :
    IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 g.bo)) (g.emitted b) := by
  have I0 : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g.bo)) (g.emitted b) :=
    il_emitGoal' (R := g.re) hI (Nat.le_refl _) hp hbat hin hdef (fun r hr => hr.elim) trivial
  have hd : g.drop = false := hI.ats.1
  have hD : ¬ Defd (g.emitted b).blocks rq := by
    intro h
    have e := (defd_put (b := b) hI.ats.free (r := rq)).mp (by simpa [Gen.emitted, hd] using h)
    rcases e with e | e
    · exact hdq e
    · exact hqd e
  exact il_lazyReg_after (goal := CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g.bo)) I0
    (frL_iff.mpr (DF.refl _ _)) hq hD hkq (fun h => (gregL_ofSure.mp h).elim) I0.goal.1

/-- **The `%nok` block of the indirect call** after `+kerf`: from the goal
"`pro` at `out`", with old registers `rp` (the subject) and `rq` (the
formula). -/
theorem oph_nok {K : Nat → Nat → Prop} {pro out : Nat} {g g' : Comp.Gen Map} {rp rq o' : Nat}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) g) (hp : rp < g.re) (hq : rq < g.re)
    (hne : rp ≠ rq) (hpp : rp ≠ pro) (hqp : rq ≠ pro)
    (hdp : ¬ Defd g.blocks rp) (hdq : ¬ Defd g.blocks rq) (hkp : HoonMap.get g.cond rp = Option.none)
    (hkq : HoonMap.get g.cond rq = Option.none)
    (h : (emit ⟨[], [Pole.nok rp rq pro], Termin.hop (jmp0 out)⟩ : CM Map Nat) g = some (o', g')) :
    OPh K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) g g' rp rq o' := by
  rw [emit_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hF, -, -⟩ := (hI.goal : GoalL g (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)))
  obtain ⟨bt, hbt, -, -⟩ := hF
  obtain ⟨hpl, hkpro⟩ := hI.entry_regs (o := out) _ List.mem_cons_self pro rfl
  have hdefs : blockDefs (⟨[], [Pole.nok rp rq pro], Termin.hop (jmp0 out)⟩ : Blob) = [pro] := by
    simp [blockDefs, aliasDst]
  have up : unproxy g.cond rp = rp := Raw.unproxy_none hkp
  have uq : unproxy g.cond rq = rq := Raw.unproxy_none hkq
  have upro : unproxy g.cond pro = pro := Raw.unproxy_none hkpro
  have hin : BlobIn (· < g.re) (⟨[], [Pole.nok rp rq pro], Termin.hop (jmp0 out)⟩ : Blob) := by
    refine ⟨fun x hx => by simp at hx, ?_, fun x hx => by simp [jmp0] at hx⟩
    intro q hq' x hx
    simp only [List.mem_singleton] at hq'
    subst hq'
    simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hpl
  refine ⟨il_old_atD hI rfl (batc_fresh fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj
      subst hj; exact hI.goal.1) hin (fun r hr => by rw [hdefs, List.mem_singleton] at hr; subst hr; exact hkpro)
      hq hdq hkq (by rw [hdefs, List.mem_singleton]; exact hqp),
    fun r hr hl => ?_, hp, fun h => ?_, hkp⟩
  · refine liveC_emitX hI _ _ (· = rp) (fun y hy hn' hx => ?_) (fun j hj => ?_) r hr hl
    · obtain ⟨-, hy | ⟨-, hy⟩⟩ := hy
      · have e : y = rp ∨ y = rq := by
          have hpp' : pro ≠ rp := fun e => hpp e.symm
          have hqp' : pro ≠ rq := fun e => hqp e.symm
          simp [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, up, uq, upro, List.erase_cons,
            hpp, hqp, hpp', hqp'] at hy
          exact hy
        rcases e with e | e
        · exact (hx e).elim
        · exact (hn' e).elim
      · simp [renBlob, renFin, finRegs, jmpRegs, jmp0, renJmp] at hy
    · simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
      subst hj
      refine ⟨hI.lab hbt, fun y hl hdf _ _ => ?_⟩
      have hyp : y ≠ pro := by
        intro e; apply hdf
        simp [blockDefs, renBlob, renPole, aliasDst, upro, e]
      exact hl.mono_r fun x hx => hx.elim id fun hz => (hyp (lazK_ofSure.mp hz).2).elim
  · have e := (defd_put (b := (⟨[], [Pole.nok rp rq pro], Termin.hop (jmp0 out)⟩ : Blob)) hI.ats.free (r := rp)).mp
      (by simpa [Gen.emitted, hI.ats.1] using h)
    rcases e with e | e
    · exact hdp e
    · rw [hdefs, List.mem_singleton] at e; exact hpp e

/-! ## The arm -/

/-- `+simple-next`, the liveness half, on every goal. -/
theorem liveC_simpleNextL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K goal g0) (h : (simpleNextL goal : CM Map (NextL S)) g0 = some (nex, g1)) :
    LiveC K goal g0 g1 nex := by
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact liveC_refl
  | done => exact liveC_simpleNextL_done hI.ats.1 (hI.cond_ge (Nat.le_refl _)) h
  | pick z o => exact liveC_simpleNextL_pick hI h

/-- **The arm `%2` (the indirect call), both halves**, from `LR` of its
parts. -/
theorem liveRun_n2 (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LR S Map env sup p) (ihq : LR S Map env sup q) : LR S Map env sup (Nomm.n2 p q Option.none) := by
  intro K goal region g0 g1 nex hI h
  simp only [runLC, callL] at h
  obtain ⟨ns, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, gb, hb, h⟩ := bind_some h
  obtain ⟨rSub, gc, hc, h⟩ := bind_some h
  obtain ⟨erS, cr, cbl, ccd, cbo, cdr⟩ := re_state hc
  obtain ⟨rFol, gd, hd, h⟩ := bind_some h
  obtain ⟨erF, dr, dbl, dcd, dbo, ddr⟩ := re_state hd
  obtain ⟨o, ge, he, h⟩ := bind_some h
  obtain ⟨nq, gf, h1, h⟩ := bind_some h
  obtain ⟨nq', gg, h2, h⟩ := bind_some h
  obtain ⟨np, gh, h3, h4⟩ := bind_some h
  subst erS erF
  have Ia : IL K ns.goal ga := il_simpleNextL hI ha
  have La : LiveC K goal g0 ga ns := liveC_simpleNextL hI ha
  obtain ⟨Ib, Lb⟩ := kerfSpecL K ns ga gb out pro Ia hb
  have Id : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) gd :=
    il_re_up Ib (by omega) (dbl.trans cbl) (dcd.trans ccd) (dbo.trans cbo) (ddr.trans cdr)
  have hU : unpM gd = unpM gb := by simp only [unpM, dbl, cbl, dcd, ccd]
  have hpro : pro < gb.re := (Ib.entry_regs (o := out) _ List.mem_cons_self pro rfl).1
  have hpl : gb.re < gd.re := by omega
  have hql : gc.re < gd.re := by omega
  have hne : gb.re ≠ gc.re := by omega
  have hdp : ¬ Defd gd.blocks gb.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hdq : ¬ Defd gd.blocks gc.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hkp : HoonMap.get gd.cond gb.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gd.cond gc.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (by omega)
  obtain ⟨O1, O2, O3, O4, O5⟩ := oph_nok Id hpl hql hne (by omega) (by omega) hdp hdq hkp hkq he
  obtain ⟨J, L⟩ := five_tail env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have h5 := O2 r hr hg
  rw [hU] at h5
  exact La r (Lb r h5)

/-- `ArmsL` with the field `n2` filled. -/
theorem armsL_n2 (env : CallEnv) :
    ∀ sup p q, PlainN p → PlainN q → LR S Map env sup p → LR S Map env sup q →
      LR S Map env sup (Nomm.n2 p q Option.none) :=
  fun sup _ _ hp hq ihp ihq => liveRun_n2 env sup hp hq ihp ihq

end Raw
end SkaModel
end Formalization
