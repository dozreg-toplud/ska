import lemmas.Ska.RawInvCLSABase

/-!
# Single assignment of the raw blocks with calls: `+kerf`

README Gaps 14 (b), track D.  **`kerfSAB : KerfSAB S Map`**: under `IL` of
the goal, `+kerf` keeps `SAB` (`RawInvCLTopU.lean`).  `+kerf` emits a hop
block `out` to the goal's `Fresh` jump (no argument, no definition), then
`+kern` from the fresh register `pro`: its gate puts ops in front of each
lazy entry's block (`kernLoop_raw`: distinct definitions, no trace op) that
define registers of the entry's need or fresh ones, and adds proxies to
`cond` only.  Under `IL` the entries' needs are `Distinct`, pairwise apart
and defined by no block, so the walk never defines a register twice, also
at a repeated label.

* `ksa_args_prepend`, `ksa_emit`: the jump-argument clause of `SAB` through
  ops in front of a block, and `SAB` through the hop block.
* **`ksa_gate`**: one gate of `+kern` keeps `SAB`; what it defines is old,
  of the entry's need, or fresh.
* **`ksa_walk`**: the walk over a list of entries with needs apart.
* **`kerfSAB`**.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The jump-argument clause of `SAB` through ops in front of a block. -/
theorem ksa_args_prepend {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole}
    (h : ∀ k b j a, HoonMap.get bl k = some b → j ∈ getJmps b.fin → some a ∈ j.args → a ∈ blockDefs b)
    (hb : HoonMap.get bl o = some b) :
    ∀ k b' j a, HoonMap.get (HoonMap.put bl o (pre A b)) k = some b' → j ∈ getJmps b'.fin → some a ∈ j.args →
      a ∈ blockDefs b' := by
  intro k b' j a hb' hj ha
  rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h'⟩
  · exact mem_blockDefs_pre.mpr (Or.inl (h k b j a hb hj ha))
  · exact h k b' j a h' hj ha

/-- `SAB` through ops in front of a block that define distinct registers
defined nowhere, none a trace op. -/
theorem ksa_prepend {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole} (hS : SAB bl)
    (hb : HoonMap.get bl o = some b) (hA : (defsOf A).Nodup) (hf : ∀ r ∈ defsOf A, ¬ Defd bl r)
    (ht : ∀ op ∈ A, trOp op = false) : SAB (HoonMap.put bl o (pre A b)) :=
  ⟨blkNodup_prepend hS.nd hb hA hf, cross_prepend hS.cr hb hf, noTr_prepend hS.tr hb ht,
    ksa_args_prepend hS.args hb⟩

/-- **`SAB` through the hop block** of `+kerf` (no definition, no argument). -/
theorem ksa_emit {g : Comp.Gen Map} {th : Jmp} (hd : g.drop = false)
    (hfree : HoonMap.get g.blocks g.bo = Option.none) (ht : th.args = []) (hS : SAB g.blocks) :
    SAB (g.emitted (⟨[], [], Termin.hop th⟩ : Blob)).blocks := by
  show SAB (if g.drop then g.blocks else HoonMap.put g.blocks g.bo (⟨[], [], Termin.hop th⟩ : Blob))
  simp only [hd, Bool.false_eq_true, if_false]
  refine ⟨blkNodup_put hS.nd (by simp [blockDefs]), cross_put hS.cr hfree (by simp [blockDefs]),
    noTr_put hS.tr (by simp), ?_⟩
  intro k b j a hb hj ha
  rcases get_put_cases hb with ⟨rfl, rfl⟩ | ⟨_, hb⟩
  · rw [getJmps_hop, List.mem_singleton] at hj
    subst hj
    rw [ht] at ha
    exact absurd ha List.not_mem_nil
  · exact hS.args k b j a hb hj ha

/-- **One gate of `+kern` keeps `SAB`**, at an entry whose need is distinct,
below `r`, names no key of `C0` and is defined by no block; what the new
blocks define is old, of the entry's need, or fresh. -/
theorem ksa_gate {r o B x : Nat} {C0 : Map (Nat × List Nat)} {s : Sure S}
    (hs : ∀ y, NMem s.ned y → y < r ∧ HoonMap.get C0 y = Option.none) (hds : Distinct s.ned)
    {g g' : Comp.Gen Map} (hW : CW r B C0 g) (hSA : SAB g.blocks) (hU : ∀ y, NMem s.ned y → ¬ Defd g.blocks y)
    (h : kernGate r o x s g = some ((), g')) :
    SAB g'.blocks ∧ ∀ y, Defd g'.blocks y → Defd g.blocks y ∨ NMem s.ned y ∨ g.re ≤ y := by
  have hrB := hW.rlt
  have hBg := hW.le
  unfold kernGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨k, rfl⟩ := L.gen
  have hgk : g.re ≤ k := L.le
  have W1 := cw_re hW hgk
  have hmem : ∀ y, NMem ned y → NMem s.ned y ∨ (g.re ≤ y ∧ y < k) := by
    intro y hy
    rcases L.mem y hy with h | h
    · exact Or.inl h
    · exact Or.inr h
  by_cases en : ned = Need.none
  · rw [if_pos en] at h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    exact ⟨hSA, fun y hy => Or.inl hy⟩
  rw [if_neg en] at h2
  obtain ⟨src, g2, h3, h4⟩ := bind_some h2
  obtain ⟨W2, -, hsrc, hre2, -, -⟩ := cw_src W1 h3
  obtain ⟨-, -, F2, B2⟩ := srcStep W1.drop W1.clt h3
  simp only [noSoft, Bool.false_eq_true] at h4
  obtain ⟨ops, g3, h5, h6⟩ := bind_some h4
  have hk2 : k ≤ g2.re := hre2
  have F2' : src = r ∨ k ≤ src := F2
  have nsrc : ¬ NMem ned src := by
    intro hm
    rcases hmem src hm with a | ⟨a, b⟩
    · have := (hs src a).1
      rcases F2' with e | e <;> omega
    · rcases F2' with e | e <;> omega
  have nb : NB g2.re ned := fun y hy => by
    rcases hmem y hy with a | ⟨-, b⟩
    · have := (hs y a).1; omega
    · omega
  have dn : Distinct ned := L.dist hds (fun y hy => by have := (hs y hy).1; omega)
  obtain ⟨A, hA, KRA⟩ := kernLoop_raw ned src [] g2 g3 ops h5 hsrc nsrc nb dn
  rw [List.append_nil] at hA
  subst hA
  have eg3 := KRA.gen
  have hb3 : g3.blocks = g2.blocks := by rw [eg3]
  have hd3 : g3.drop = false := by rw [eg3]; exact W2.drop
  have hbl : g3.blocks = g.blocks := hb3.trans B2
  simp only [addOps, hd3, Bool.false_eq_true, if_false] at h6
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h6
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  rw [hbl] at hb
  have hdlt : ∀ y, Defd g.blocks y → y < g.re := fun y d => defd_lt hW.regs d
  have hdA : ∀ y ∈ defsOf ops, NMem s.ned y ∨ g.re ≤ y := by
    intro y hy
    rcases KRA.defs y hy with hm | ⟨a, -⟩
    · rcases hmem y hm with hm | ⟨a, -⟩
      · exact Or.inl hm
      · exact Or.inr a
    · exact Or.inr (by omega)
  have hf : ∀ y ∈ defsOf ops, ¬ Defd g.blocks y := by
    intro y hy d
    rcases hdA y hy with hm | a
    · exact hU y hm d
    · have := hdlt y d; omega
  show SAB (HoonMap.put g3.blocks x (pre ops b)) ∧
    ∀ y, Defd (HoonMap.put g3.blocks x (pre ops b)) y → Defd g.blocks y ∨ NMem s.ned y ∨ g.re ≤ y
  rw [hbl]
  refine ⟨ksa_prepend hSA hb KRA.nd hf KRA.tr, fun y d => ?_⟩
  rcases (defd_prepend hb).mp d with d | d
  · exact Or.inl d
  · exact Or.inr (hdA y d)

/-- **The walk of `+kern` over entries with needs apart keeps `SAB`.** -/
theorem ksa_walk {r o B : Nat} {C0 : Map (Nat × List Nat)} :
    ∀ (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map), CW r B C0 g → SAB g.blocks → NeedsApart es →
    (∀ e ∈ es, Distinct e.2.sure.ned ∧
      ∀ y, NMem e.2.sure.ned y → (y < r ∧ HoonMap.get C0 y = Option.none) ∧ ¬ Defd g.blocks y) →
    walkList (kernGate r o) es g = some ((), g') → SAB g'.blocks
  | [], g, g', _, hS, _, _, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact hS
  | (x, l) :: rest, g, g', hW, hS, hap, he, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨hd, hn⟩ := he (x, l) List.mem_cons_self
    obtain ⟨-, W1, -⟩ := kernGate_stepW (fun y hy => (hn y hy).1) hd hW h1
    obtain ⟨S1, D1⟩ := ksa_gate (fun y hy => (hn y hy).1) hd hW hS (fun y hy => (hn y hy).2) h1
    have hap' := List.pairwise_cons.mp hap
    refine ksa_walk rest g1 g' W1 S1 hap'.2 (fun e hm => ⟨(he e (List.mem_cons_of_mem _ hm)).1,
      fun y hy => ⟨((he e (List.mem_cons_of_mem _ hm)).2 y hy).1, fun d => ?_⟩⟩) h2
    have hy' := (he e (List.mem_cons_of_mem _ hm)).2 y hy
    have hrB := hW.rlt
    have hBg := hW.le
    rcases D1 y d with d | d | d
    · exact hy'.2 d
    · exact hap'.1 e hm y d hy
    · have := hy'.1.1; omega

/-- **`+kerf` keeps single assignment** under `IL` of the goal. -/
theorem kerfSAB : KerfSAB S Map := by
  intro K nex g0 g1 out pro hI0 hS0 h
  rcases nex with ⟨laz, th⟩
  have hI : IL K (CGoalL.next laz th) g0 := hI0
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hth, hap, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  have hER := hI.entry_regs (o := g0.bo)
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
  have S0 : SAB ({ g0.emitted (⟨[], [], Termin.hop th⟩ : Blob) with re := g0.re + 1 } : Comp.Gen Map).blocks :=
    ksa_emit hd hI.ats.free targs hS0
  -- the walk as a list
  have ew : (walkLazy (kernGate g0.re g0.bo) g0.bo laz : CM Map Unit) =
      walkList (kernGate g0.re g0.bo) ((g0.bo, laz) :: wentries laz) := by
    rw [walkLazy_flat]; rfl
  rw [ew] at hw
  have hperm : ((g0.bo, laz) :: wentries laz).Perm ((g0.bo, laz) :: entries laz) :=
    (wentries_perm laz).cons (g0.bo, laz)
  have hap0 : NeedsApart ((g0.bo, laz) :: entries laz) :=
    List.pairwise_cons.mpr ⟨fun e he => (List.pairwise_cons.mp hap).1 e he, (List.pairwise_cons.mp hap).2⟩
  have hapW : NeedsApart ((g0.bo, laz) :: wentries laz) :=
    (hperm.pairwise_iff (fun {a b} hab r hb ha => hab r ha hb)).mpr hap0
  refine ksa_walk _ _ gw W0 S0 hapW (fun e he => ?_) hw
  have he' : e ∈ (g0.bo, laz) :: entries laz := hperm.mem_iff.mp he
  have hE : Distinct e.2.sure.ned ∧ ∀ y, NMem e.2.sure.ned y → y < g0.re ∧ ¬ Defd g0.blocks y := by
    rcases List.mem_cons.mp he' with rfl | he''
    · exact (hent _ List.mem_cons_self).2
    · exact (hent e (List.mem_cons_of_mem _ he'')).2
  refine ⟨hE.1, fun y hy => ⟨hER e he' y hy, fun d => ?_⟩⟩
  exact (hE.2 y hy).2 ((defd_emitted_nil hI.ats hbD).mp d)

end Raw
end SkaModel
end Formalization
