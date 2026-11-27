import lemmas.Ska.CompSixLSWrap

/-!
# `[6 c a b]` at the top: calling tests, nested `%6` in the branches

README Gaps 12.34, steps 2 and 4.

* `entries_pure_any`, `pickTree_noEnt`: under `%pick`, a test of `PickTree`
  whose parts' needs have no entries (`NoEntF`) returns a need without
  entries (the indirect call and `[0 axe]` begin with the block of
  `+simple-next` and run under `%next`, where `NoEnt` holds).
* `pickD_of_pickTree`: such a test meets `PickD` with the bound `0`
  (`pickTree_pick`).
* `SixTest`: the tests of the class (call-free in `FragX` and `CallTreeA`,
  or calling in `PickTree` with `NoEntF`), `sixTest_pickD`.
* `Six0`: `[6 c a b]` with a test of `SixTest` and branches in `CallTreeA`
  with `NoEntF` or again in `Six0`, with the bound of the entries;
  `six0_done` (every nomm of `Six0` meets `SixDW` under `%done`),
  `finishLUC_contractSix0` (both halves of the contract at the top).
* Instances: a calling test, a calling test with a calling branch, a `%6`
  nested in a branch, each with a `#guard` that the code exists and agrees
  with `+mink` on the 24 subjects of `CompSixLSCheck.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Calling tests -/

/-- A call-free nomm without `%6` returns a need without entries for every
goal (`noEnt_pure` without its premise `NoPick`). -/
theorem entries_pure_any (env : CallEnv) {nm : Nomm} (hp : nm.pure = true) (h6 : noSix nm = true)
    {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runLC env sup nm (CGoal.toL goal) region g0 = some (nex, g1)) : entries nex.laz = [] := by
  rw [runLC_eq env nm (Nomm.noCall_of_pure nm hp), runL_toL nm hp h6 goal region, map_apply] at h
  obtain ⟨⟨n, g'⟩, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact entries_ofSure _

/-- **A test of `PickTree` with `NoEntF` returns a need without entries
under `%pick`.** -/
theorem pickTree_noEnt (env : CallEnv) {f : Noun} {nm : Nomm} (h : PickTree f nm) (hn : NoEntF nm) :
    ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {z o : Jmp},
    runLC env sup nm (CGoalL.pick z o) region g0 = some (nex, g1) → entries nex.laz = [] := by
  induction h with
  | ind hp hq =>
    intro sup region g0 g1 nex z o hr
    rw [runLC_pick_next env sup (Or.inl ⟨_, _, rfl⟩) z o region g0] at hr
    exact noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial hr
  | n0 hax =>
    intro sup region g0 g1 nex z o hr
    rw [runLC_pick_next env sup (Or.inr ⟨_, hax, rfl⟩) z o region g0] at hr
    exact noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial hr
  | @seven b c p q hp hq ihq =>
    intro sup region g0 g2 nex z o hr
    cases hn with
    | pure hpu h6 => exact entries_pure_any env hpu h6 (goal := CGoal.pick z o) hr
    | seven np nq =>
      rw [runLC_n7] at hr
      obtain ⟨nx, g1, h1, h2⟩ := bind_some hr
      have ex := eq_ofSure_of_entries (ihq nq h1)
      have h2' : runLC env sup p (CGoal.toL (CGoal.next nx.laz.sure nx.th)) region g1 = some (nex, g2) := by
        simp only [CGoal.toL]; rw [← ex]; exact h2
      exact noEnt_of_noEntF (S := S) (Map := Map) env np (goal := CGoal.next nx.laz.sure nx.th) trivial h2'

/-- **A test of `PickTree` with `NoEntF` meets `PickD`** with the bound `0`. -/
theorem pickD_of_pickTree (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : PickTree f nm) (hn : NoEntF nm) : PickD (S := S) (Map := Map) lib N env P f nm 0 := by
  intro sup region g0 g1 nex z o hz ho hj b0 d0 hu hcl hcb hr
  refine ⟨(pickTree_pick lib env h P hj ⟨hz, ho⟩ b0 d0 hu hcl hcb hr).run, ?_⟩
  rw [pickTree_noEnt (S := S) (Map := Map) env h hn hr]
  exact Nat.le_refl _

/-! ## `[3 p]` as a test -/

/-- **`[3 p]` under `%pick z o`** (step 3): the block `[clq r z o]`, then
`p` under `%next (lazy-from-reg r)` into it, composed by `unaryGTB_ok` (the
text of `three_doneB` with the block of `%pick` in place of `+done-blocks`). -/
theorem three_pickB (lib : Lib) {N : Needs} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fb p) (M : MinkC3 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {z o : Jmp} (hcount : sixCount p ≤ 255)
    (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (ha : z.args = [] ∧ o.args = []) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n3 p) (CGoalL.pick z o) region g0 = some (nex, g1)) :
    PickOK lib N P f z o g0 g1 nex := by
  have e3 : (runLC env sup (Nomm.n3 p) (CGoalL.pick z o : CGoalL S) region : CM Map (NextL S)) = (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runLC
  rw [e3] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have JB : JumpsBelow (Termin.clq g0.re z o) g0.bo := jumpsBelow_two rfl hj.1 hj.2
  have G1 : GrowU g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.clq g0.re z o⟩) :=
    ((grow_re g0).trans (grow_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.clq g0.re z o⟩) JB)).toU hu
  obtain ⟨⟨Qp, Rp⟩, pne, -, pfl, pec⟩ := Sp.run (L := ofSure (lazyReg g0.re)) (th := jmp0 g0.bo) (Or.inr e0) hcount
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu) (hcl0.growU G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    b0 (by simp only [jmp0, Gen.emitted]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h
  have RG := Rp.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted]; omega)
  refine ⟨?_, pne, pfl, Sp.clean (L := ofSure (lazyReg g0.re)) trivial h, pec⟩
  refine unaryGTB_ok (T := fun _ => wutTone) wutTone_keep M.fwd M.bwd ((ext_re _).trans (ext_emit _ _)) G1
    (by simp only [Gen.emitted]) ⟨Nat.le_refl _, by simp only [Gen.emitted]; omega⟩
    (by simp only [Gen.emitted]; omega) (fresh_emitted (g := { g0 with re := g0.re + 1 }) d0 rfl rfl) RG ?_ ?_
  · intro cf hcf k h0 h1
    have ek : k = g0.bo := by simp only [Gen.emitted] at h1; omega
    subst ek
    have c0 : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by simp only [Gen.emitted]; omega)]; exact condBelow_none hcb (Nat.le_refl _)
    rw [emitted_get ({ g0 with re := g0.re + 1 } : Gen Map) _ d0]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0,
      renJmp_nil _ ha.1, renJmp_nil _ ha.2]
  · intro c hc σ Inv ν O gul st regs t tm x hI htr hx
    have hb := emitted_get' (g := { g0 with re := g0.re + 1 }) d0
      (hc _ (Nat.le_refl _) (by simp only [Gen.emitted]; omega))
    have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_clq, hx, Option.bind_some] at hj'
    cases x with
    | atom n =>
      exact ⟨(fun e => by cases e), fun _ => ⟨st, regs, hI, Needs.le_refl _, trivial, fun _ _ => rfl, hj'⟩,
        fun _ h1 => absurd rfl h1⟩
    | cell u v =>
      exact ⟨fun _ => ⟨st, regs, hI, Needs.le_refl _, trivial, fun _ _ => rfl, hj'⟩, (fun e => by cases e),
        fun h0 _ => absurd rfl h0⟩

/-- **`[3 p]` with `p` in `CallTreeA` with `NoEntF` meets `PickD`** with the
bound `0`. -/
theorem pickD_three (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {b : Bool} {fb : Noun} {p : Nomm}
    (hp : CallTreeA b fb p) (hn : NoEntF p) : PickD (S := S) (Map := Map) lib N env P (n2 (A 3) fb) (Nomm.n3 p) 0 := by
  intro sup region g0 g1 nex z o hz ho hj b0 d0 hu hcl hcb hr
  refine ⟨(three_pickB lib (lokS_callTreeA lib env hp P).1.1 (minkC3_three lib P fb) (by rw [hp.sixCount]; omega)
    hj ⟨hz, ho⟩ b0 d0 hu hcl hcb hr).run, ?_⟩
  have e3 : (runLC env sup (Nomm.n3 p) (CGoalL.pick z o : CGoalL S) region : CM Map (NextL S)) = (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runLC
  rw [e3] at hr
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at hr
  rw [noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial hr]
  exact Nat.le_refl _

/-! ## The class -/

/-- **The tests of the class**: call-free (in `FragX`, which gives `UOK`,
and in `CallTreeA`, which gives the formula), or calling (in `PickTree`,
with needs without entries). -/
inductive SixTest : Noun → Nomm → Prop
  | pure {b : Bool} {f : Noun} {c : Nomm} : FragX (S := S) c → CallTreeA b f c → c.pure = true → SixTest f c
  | call {f : Noun} {c : Nomm} : PickTree f c → NoEntF c → SixTest f c
  | three {b : Bool} {f : Noun} {p : Nomm} : CallTreeA b f p → NoEntF p → SixTest (n2 (A 3) f) (Nomm.n3 p)

theorem sixTest_pickD (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) {f : Noun} {c : Nomm}
    (h : SixTest (S := S) f c) : PickD (S := S) (Map := Map) lib N env P f c 0 := by
  cases h with
  | pure hx ht hp =>
    have H : PickD (S := S) (Map := Map) lib N env P f c (2 * sixCount c) :=
      pickD_of_uok (S := S) (Map := Map) lib (N := N) env (uok_x lib hx)
        (fun s hs gul tm r => mink_pure (codeOK_none lib) hp (ht.annot P) hs gul tm r)
        (by rw [ht.sixCount]; omega)
    rwa [ht.sixCount] at H
  | call ht hn => exact pickD_of_pickTree lib env ht hn
  | three hp hn => exact pickD_three lib env hp hn

/-- **`[6 c a b]` at the top, nested in the branches**: a leaf of
`CallTreeA` whose need has no entries, or a `%6` whose test is in `SixTest`
and whose branches are again in `Six0`, the bounds of their entries small
enough that the fork is not big. -/
inductive Six0 : Noun → Nomm → Nat → Prop
  | leaf {b : Bool} {f : Noun} {nm : Nomm} : CallTreeA b f nm → NoEntF nm → Six0 f nm 0
  | six {fc fa fb : Noun} {c a b : Nomm} {ka kb : Nat} : SixTest (S := S) fc c → Six0 fa a ka → Six0 fb b kb →
      ka + kb + 5 ≤ lazyMax → Six0 (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (ka + kb + 4)

/-- **Every nomm of `Six0` meets `SixDW` under `%done`.** -/
theorem six0_done (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) {f : Noun} {nm : Nomm} {k : Nat}
    (h : Six0 (S := S) f nm k) : SixDW (S := S) (Map := Map) lib N env P f nm k := by
  induction h with
  | leaf ht hn => exact SixD.toW (sixD_of_callTreeA lib env ht hn P)
  | @six fc fa fb c a b ka kb hc _ _ hk iha ihb =>
    have H : SixDW (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (0 + ka + kb + 4) :=
      six_doneGBW lib env (sixTest_pickD lib env P hc) iha ihb hk
    rwa [Nat.zero_add] at H

/-- **The contract of `Six0` at the top**: the whole-subject code of every
nomm of the class meets both halves of the contract for its formula, on
every subject, with no hypothesis about the run. -/
theorem finishLUC_contractSix0 (lib : Lib) (env : CallEnv) (P : Noun → Prop) {f : Noun} {nm : Nomm} {k : Nat}
    (h : Six0 (S := S) f nm k) {c : Straight Map} (hc : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractSixDW lib env (six0_done (S := S) (Map := Map) lib (N := N) env P h) hc

/-! ## Instances -/

/-- The indirect call `[2 [0 3] [0 2]]` as a test. -/
theorem sixTest_ind : SixTest (S := S) (n3 (A 2) (slot 3) (slot 2)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) :=
  SixTest.call (PickTree.ind (CallTreeA.n0 3) (CallTreeA.n0 2)) (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl))

/-- `[0 axe]` as a branch. -/
theorem six0_n0 (axe : Nat) : Six0 (S := S) (slot axe) (Nomm.n0 axe) 0 :=
  Six0.leaf (CallTreeA.n0 axe) (NoEntF.pure rfl rfl)

/-- `[2 [0 x] [0 y]]` as a branch. -/
theorem six0_ind (x y : Nat) :
    Six0 (S := S) (n3 (A 2) (slot x) (slot y)) (Nomm.n2 (Nomm.n0 x) (Nomm.n0 y) Option.none) 0 :=
  Six0.leaf (CallTreeA.ind (CallTreeA.n0 x) (CallTreeA.n0 y)) (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl))

/-- `[6 [2 [0 3] [0 2]] [0 3] [0 2]]`: a calling test. -/
theorem sixCallTest_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n0 2)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (slot 2)) [s] c ∧
      ContractBwd lib N s (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (slot 2)) [s] c :=
  have H := finishLUC_contractSix0 lib env (fun _ => True)
    (Six0.six sixTest_ind (six0_n0 3) (six0_n0 2) (by decide)) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[6 [2 [0 3] [0 2]] [2 [0 6] [0 7]] [0 3]]`: a calling test and a calling
branch. -/
theorem sixCallBoth_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none)
        (Nomm.n0 3)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3)) [s] c ∧
      ContractBwd lib N s (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3)) [s] c :=
  have H := finishLUC_contractSix0 lib env (fun _ => True)
    (Six0.six sixTest_ind (six0_ind 6 7) (six0_n0 3) (by decide)) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[6 [3 [0 2]] [6 [2 [0 3] [0 2]] [0 2] [0 3]] [0 3]]`: a `%6` with a
calling test nested in the yes branch of a `%6` with a call-free test. -/
theorem sixNested_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n6 (Nomm.n3 (Nomm.n0 2))
        (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 3)) (Nomm.n0 3)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n4 (A 6) (n2 (A 3) (slot 2))
        (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 3)) (slot 3)) [s] c ∧
      ContractBwd lib N s (n4 (A 6) (n2 (A 3) (slot 2))
        (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 3)) (slot 3)) [s] c :=
  have H := finishLUC_contractSix0 lib env (fun _ => True)
    (Six0.six (SixTest.pure (FragX.three (FragX.frag (nm := Nomm.n0 2) fun _ => trivial))
        (CallTreeA.three (CallTreeA.n0 2)) rfl)
      (Six0.six sixTest_ind (six0_n0 2) (six0_n0 3) (by decide)) (six0_n0 3) (by decide)) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[6 [3 [2 [0 3] [0 2]]] [0 2] [0 3]]`: the cell test of a call as the
test. -/
theorem sixThreeCall_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n6 (Nomm.n3 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) (Nomm.n0 2) (Nomm.n0 3)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n4 (A 6) (n2 (A 3) (n3 (A 2) (slot 3) (slot 2))) (slot 2) (slot 3)) [s] c ∧
      ContractBwd lib N s (n4 (A 6) (n2 (A 3) (n3 (A 2) (slot 3) (slot 2))) (slot 2) (slot 3)) [s] c :=
  have H := finishLUC_contractSix0 lib env (fun _ => True)
    (Six0.six (SixTest.three (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2))
        (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)))
      (six0_n0 2) (six0_n0 3) (by decide)) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

#guard SixCheck.sem [Nomm.n6 (Nomm.n3 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) (Nomm.n0 2) (Nomm.n0 3)] ==
  (1, 1, 24, 24)

-- The whole-subject code of each instance exists and agrees with `+mink` on
-- the 24 subjects of `CompSixLSCheck.lean`.
#guard SixCheck.sem [Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n0 2)] == (1, 1, 24, 24)
#guard SixCheck.sem [Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
  (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3)] == (1, 1, 24, 24)
#guard SixCheck.sem [Nomm.n6 (Nomm.n3 (Nomm.n0 2))
  (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 3)) (Nomm.n0 3)] == (1, 1, 24, 24)

end Comp
end SkaModel
end Formalization
