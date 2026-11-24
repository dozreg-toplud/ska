import lemmas.Ska.CompUnproxyTop

/-!
# Fact (i5): the blocks of a run mention only registers below its end

Fact (i5) of README Gaps 12.2 (tested on the real compiler,
`tools/hoon/selfkeep.py`): every register that a new or changed block of a
run mentions (parameters, ops, the terminator with its jump arguments) is
below `re` at the end of the run.  This file states it and draws its
consequence for `RunOKU`, and gives the steps for the separate induction that
is to prove it.

* `JmpIn`, `FinIn`, `BlobIn`: every register of a jump, a terminator, a block
  satisfies `P`.  A renaming that agrees on those registers renames the block
  the same way (`renJmp_congr`, `renFin_congr`, `renBlob_congr`).
* `BelowIn lo g`: every block of `g` at a label in `[lo, g.bo)` mentions only
  registers below `g.re`.  Fact (i5) of a run from `g0` to `g1` is
  `BelowIn g0.bo g1`.
* `agreeU_transfer`: on blocks that meet (i5), `AgreeU` by one `cond` is
  `AgreeU` by any `cond` that agrees with it below `g1.re`.
* `RunOKU.semW`: the `sem` of `RunOKU` widened to a later `cond` that agrees
  with the run's own below `g1.re`, given (i5); `RunOKU.semF` takes the `cond`
  of a later state reached by `CondFresh`, which is what composed runs have.
* The steps of the induction: `belowIn_start`, `BelowIn.mono`,
  `belowIn_emitted`, `belowIn_emit`, `belowIn_re`, `belowIn_addOps`,
  `belowIn_proxy`, `BelowIn.ext` (a sub-run that keeps the old blocks),
  `BelowIn.front` (a sub-run that puts ops in front of one old block).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The registers of a block -/

/-- Every register argument of a jump satisfies `P`. -/
def JmpIn (P : Nat → Prop) (j : Jmp) : Prop := ∀ x, some x ∈ j.args → P x

/-- Every register a terminator mentions satisfies `P`. -/
def FinIn (P : Nat → Prop) : Termin → Prop
  | Termin.clq s z o => P s ∧ JmpIn P z ∧ JmpIn P o
  | Termin.eqq l r z o => P l ∧ P r ∧ JmpIn P z ∧ JmpIn P o
  | Termin.brn s z o => P s ∧ JmpIn P z ∧ JmpIn P o
  | Termin.brz s z o => P s ∧ JmpIn P z ∧ JmpIn P o
  | Termin.hop t => JmpIn P t
  | Termin.jmp _ v => ∀ x ∈ v, P x
  | Termin.jmf _ v _ => ∀ x ∈ v, P x
  | Termin.jsp _ s => P s
  | Termin.jsf _ s _ => P s
  | Termin.don s => P s
  | Termin.bom _ => True
  | Termin.lti _ s z o => P s ∧ JmpIn P z ∧ JmpIn P o

/-- Every register a block mentions satisfies `P`. -/
def BlobIn (P : Nat → Prop) (b : Blob) : Prop := (∀ x ∈ b.par, P x) ∧ RegsIn P b.body ∧ FinIn P b.fin

theorem JmpIn.mono {P Q : Nat → Prop} (h : ∀ x, P x → Q x) {j : Jmp} (hj : JmpIn P j) : JmpIn Q j :=
  fun x hx => h x (hj x hx)

theorem jmpIn_jmp0 (P : Nat → Prop) (o : Nat) : JmpIn P (jmp0 o) := fun _ hx => by simp [jmp0] at hx

theorem FinIn.mono {P Q : Nat → Prop} (h : ∀ x, P x → Q x) {f : Termin} (hf : FinIn P f) : FinIn Q f := by
  cases f <;> simp only [FinIn] at hf ⊢
  case clq | brn | brz | lti => exact ⟨h _ hf.1, hf.2.1.mono h, hf.2.2.mono h⟩
  case eqq => exact ⟨h _ hf.1, h _ hf.2.1, hf.2.2.1.mono h, hf.2.2.2.mono h⟩
  case hop => exact hf.mono h
  case jmp | jmf => exact fun x hx => h x (hf x hx)
  case jsp | jsf | don => exact h _ hf

theorem BlobIn.mono {P Q : Nat → Prop} (h : ∀ x, P x → Q x) {b : Blob} (hb : BlobIn P b) : BlobIn Q b :=
  ⟨fun x hx => h x (hb.1 x hx), hb.2.1.mono h, hb.2.2.mono h⟩

section Congr
variable {u v : Nat → Nat} {P : Nat → Prop}

theorem renJmp_congr (h : ∀ x, P x → u x = v x) {j : Jmp} (hj : JmpIn P j) : renJmp u j = renJmp v j := by
  rcases j with ⟨args, there⟩
  simp only [renJmp, Jmp.mk.injEq, and_true]
  apply List.map_congr_left
  intro a ha
  cases a with
  | none => rfl
  | some x => simp only [Option.map_some, h x (hj x ha)]

theorem map_congr_in (h : ∀ x, P x → u x = v x) {l : List Nat} (hl : ∀ x ∈ l, P x) : l.map u = l.map v :=
  List.map_congr_left fun x hx => h x (hl x hx)

theorem renPole_congr (h : ∀ x, P x → u x = v x) {p : Pole} (hp : ∀ x ∈ poleRegs p, P x) :
    renPole u p = renPole v p := by
  have hl : ∀ x ∈ poleRegs p, u x = v x := fun x hx => h x (hp x hx)
  cases p <;> simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hl <;>
    simp only [renPole, hl]
  all_goals first
    | rw [List.map_congr_left hl]
    | rw [List.map_congr_left hl.2]

theorem renFin_congr (h : ∀ x, P x → u x = v x) {f : Termin} (hf : FinIn P f) : renFin u f = renFin v f := by
  cases f <;> simp only [FinIn] at hf <;> simp only [renFin]
  case clq | brn | brz | lti =>
    rw [h _ hf.1, renJmp_congr h hf.2.1, renJmp_congr h hf.2.2]
  case eqq => rw [h _ hf.1, h _ hf.2.1, renJmp_congr h hf.2.2.1, renJmp_congr h hf.2.2.2]
  case hop => rw [renJmp_congr h hf]
  case jmp | jmf => rw [map_congr_in h hf]
  case jsp | jsf | don => rw [h _ hf]

theorem renBlob_congr (h : ∀ x, P x → u x = v x) {b : Blob} (hb : BlobIn P b) : renBlob u b = renBlob v b := by
  rcases b with ⟨par, body, fin⟩
  obtain ⟨hp, hbody, hf⟩ := hb
  simp only [renBlob, Blob.mk.injEq]
  exact ⟨map_congr_in h hp, List.map_congr_left fun p hp' => renPole_congr h (hbody p hp'), renFin_congr h hf⟩

end Congr

/-- Two `cond`s that agree below `n` unproxy the registers below `n` alike. -/
theorem unproxy_agree {cond cond' : Map (Nat × List Nat)} {n : Nat}
    (hc : ∀ k, k < n → HoonMap.get cond k = HoonMap.get cond' k) : ∀ x, x < n → unproxy cond x = unproxy cond' x :=
  fun x hx => by simp only [unproxy, hc x hx]

/-! ## Fact (i5) -/

/-- **Every block of `g` at a label in `[lo, g.bo)` mentions only registers
below `g.re`.**  Fact (i5) of a run from `g0` to `g1` is `BelowIn g0.bo g1`. -/
def BelowIn (lo : Nat) (g : Gen Map) : Prop :=
  ∀ o b, lo ≤ o → o < g.bo → HoonMap.get g.blocks o = some b → BlobIn (· < g.re) b

/-- **On blocks that meet (i5), `AgreeU` does not depend on `cond` above the
run's end.** -/
theorem agreeU_transfer {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond cond' : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (hb : BelowIn g0.bo g1) (hc : ∀ k, k < g1.re → HoonMap.get cond k = HoonMap.get cond' k)
    (hl : ∀ e ∈ entries laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo)
    (ag : AgreeU lib O c gul st t cond ned g0 g1 laz s0 s) : AgreeU lib O c gul st t cond' ned g0 g1 laz s0 s := by
  obtain ⟨ag1, ag2⟩ := ag
  have hu := unproxy_agree hc
  refine ⟨fun o l u hn => ?_, fun e he => ?_⟩
  · rw [ag1 o l u hn]
    cases hg : HoonMap.get g1.blocks o with
    | none => rfl
    | some b =>
      simp only [Option.map_some, unproxyBlob]
      rw [renBlob_congr hu (hb o b l u hg)]
  · obtain ⟨A, th, h1, h2, h3⟩ := ag2 e he
    refine ⟨A, th, h1, ?_, h3⟩
    rw [h2]
    have hf := (hb e.1 _ (hl e he).1 (hl e he).2 h1).2.2
    simp only [FinIn] at hf
    rw [renJmp_congr hu hf]

/-- **The `sem` of `RunOKU` at a later `cond`** that agrees with the run's own
below `g1.re`, given fact (i5) of the run. -/
theorem RunOKU.semW {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKU lib nm goal g0 g1 nex) (hb : BelowIn g0.bo g1) {cond : Map (Nat × List Nat)}
    (hc : ∀ k, k < g1.re → HoonMap.get cond k = HoonMap.get g1.cond k)
    (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun)
    (ag : AgreeU lib O c gul st t cond ned g0 g1 nex.laz s0 s) (hn : ∀ r, NMem ned r → g1.re ≤ r)
    (regs : Map (Option Noun)) (hs : HoldsS nex.laz.sure regs s) (h0 : HoldsN ned regs s0) :
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s) :=
  R.sem c ned σ O st t gul s0 s
    (agreeU_transfer hb hc (fun e he => ⟨(R.labs e he).1, Nat.lt_trans (R.labs e he).2.1 R.hi⟩) ag) hn regs hs h0

/-- **The `sem` of `RunOKU` at the `cond` of any later state** that `cond`
reached by fresh proxies only (`CondFresh`), given fact (i5) of the run. -/
theorem RunOKU.semF {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 g2 : Gen Map} {nex : NextL S}
    (R : RunOKU lib nm goal g0 g1 nex) (hb : BelowIn g0.bo g1) (hf : CondFresh g1 g2)
    (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun)
    (ag : AgreeU lib O c gul st t g2.cond ned g0 g1 nex.laz s0 s) (hn : ∀ r, NMem ned r → g1.re ≤ r)
    (regs : Map (Option Noun)) (hs : HoldsS nex.laz.sure regs s) (h0 : HoldsN ned regs s0) :
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s) :=
  R.semW hb (fun _ hk => hf.get_lt hk) c ned σ O st t gul s0 s ag hn regs hs h0

/-! ## The steps of the induction for (i5) -/

/-- At the start of a run nothing is allocated from its `bo` on. -/
theorem belowIn_start (g : Gen Map) : BelowIn g.bo g := fun _ _ l u _ => absurd u (Nat.not_lt.mpr l)

theorem BelowIn.mono {lo lo' : Nat} {g g' : Gen Map} (h : BelowIn lo g) (hl : lo ≤ lo') (hbo : g'.bo ≤ g.bo)
    (hre : g.re ≤ g'.re) (hblk : ∀ o, lo' ≤ o → o < g'.bo → HoonMap.get g'.blocks o = HoonMap.get g.blocks o) :
    BelowIn lo' g' := fun o b l u hb => by
  rw [hblk o l u] at hb
  exact (h o b (Nat.le_trans hl l) (Nat.lt_of_lt_of_le u hbo) hb).mono fun x hx => Nat.lt_of_lt_of_le hx hre

/-- Allocating registers keeps (i5). -/
theorem belowIn_re {lo : Nat} {g : Gen Map} (h : BelowIn lo g) (k : Nat) (hk : g.re ≤ k) :
    BelowIn lo { g with re := k } :=
  h.mono (Nat.le_refl _) (Nat.le_refl _) hk fun _ _ _ => rfl

/-- **Emitting a block of registers below `re` keeps (i5)**, when the run
does not drop. -/
theorem belowIn_emitted {lo : Nat} {g : Gen Map} {b : Blob} (h : BelowIn lo g) (hd : g.drop = false)
    (hb : BlobIn (· < g.re) b) : BelowIn lo (g.emitted b) := by
  intro o b' l u hb'
  simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put] at u hb' ⊢
  by_cases e : o = g.bo
  · rw [if_pos e] at hb'; cases hb'; exact hb
  · rw [if_neg e] at hb'
    exact h o b' l (by omega) hb'

theorem belowIn_emit {lo : Nat} {g g' : Gen Map} {b : Blob} {o : Nat} (h : BelowIn lo g) (hd : g.drop = false)
    (hb : BlobIn (· < g.re) b) (he : (emit b : CM Map Nat) g = some (o, g')) : BelowIn lo g' := by
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  rw [← he.2]; exact belowIn_emitted h hd hb

/-- **Putting ops of registers below `re` in front of a block keeps (i5).** -/
theorem belowIn_addOps {lo o : Nat} {ops : List Pole} {g g' : Gen Map} (h : BelowIn lo g)
    (hA : o < lo ∨ RegsIn (· < g.re) ops) (ha : addOps o ops g = some ((), g')) : BelowIn lo g' := by
  unfold addOps at ha
  by_cases hd : g.drop = true
  · rw [if_pos hd] at ha; cases ha; exact h
  · rw [if_neg hd] at ha
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp ha
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    intro o' b' l u hb'
    simp only [HoonMap.get_put] at u hb' ⊢
    by_cases e' : o' = o
    · rw [if_pos e'] at hb'; cases hb'
      subst e'
      have hb0 := h o' b l u hb
      rcases hA with hA | hA
      · omega
      · exact ⟨hb0.1, hA.append hb0.2.1, hb0.2.2⟩
    · rw [if_neg e'] at hb'
      exact h o' b' l u hb'

/-- **`+proxy` keeps (i5)**: it allocates a register and changes no block. -/
theorem belowIn_proxy {lo r o p : Nat} {g g' : Gen Map} (h : BelowIn lo g) (hp : proxy r o g = some (p, g')) :
    BelowIn lo g' := by
  obtain ⟨_, hre, hbl, _, _, _⟩ := proxy_condFresh hp
  have hbo : g'.bo = g.bo := by
    unfold proxy at hp
    simp only at hp
    by_cases hd : g.drop = true
    · rw [if_pos hd] at hp; simp only [Option.some.injEq, Prod.mk.injEq] at hp; rw [← hp.2]
    · rw [if_neg hd] at hp
      obtain ⟨_, _, ht⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at ht; rw [← ht.2]
  exact h.mono (Nat.le_refl _) (Nat.le_of_eq hbo) (by rw [hre]; exact Nat.le_succ _) fun o' _ _ => by rw [hbl]

/-- **A sub-run that keeps the old blocks (`Ext`) and meets (i5) itself keeps
(i5) of the whole.** -/
theorem BelowIn.ext {lo : Nat} {g1 g2 : Gen Map} (a : BelowIn lo g1) (e : Ext g1 g2) (b : BelowIn g1.bo g2) :
    BelowIn lo g2 := by
  intro o bl l u h
  by_cases ho : o < g1.bo
  · rw [e.2.2.2 o ho] at h
    exact (a o bl l ho h).mono fun x hx => Nat.lt_of_lt_of_le hx e.1
  · exact b o bl (Nat.le_of_not_lt ho) u h

/-- **Ops `A` put in front of one old block keep (i5)**, when the block is
below `lo` or the ops' registers are below the end. -/
theorem BelowIn.front {lo o : Nat} {A : List Pole} {g1 g2 : Gen Map} (a : BelowIn lo g1) (F : Front o g1 g2 A)
    (hA : o < lo ∨ (RegsIn (· < g2.re) A ∧ ∃ B fin, HoonMap.get g1.blocks o = some ⟨[], B, fin⟩)) :
    BelowIn lo g2 := by
  intro o' bl l u h
  rw [F.bo] at u
  by_cases e : o' = o
  · subst e
    rcases hA with hA | ⟨hA, B, fin, hB⟩
    · omega
    · rw [F.blk B fin hB] at h; cases h
      have hb0 := (a o' _ l u hB).mono fun x hx => Nat.lt_of_lt_of_le hx F.le
      exact ⟨fun x hx => absurd hx (List.not_mem_nil), hA.append hb0.2.1, hb0.2.2⟩
  · rw [F.other o' e] at h
    exact (a o' bl l u h).mono fun x hx => Nat.lt_of_lt_of_le hx F.le

end Comp
end SkaModel
end Formalization
