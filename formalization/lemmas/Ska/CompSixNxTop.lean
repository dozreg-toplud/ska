import lemmas.Ska.CompSixNxRun

/-!
# A `%6` under `%next` inside a parent, and the top

README Gaps 12.36, steps 3 and 4.  Written by `tools/gen/sixnxt.py` (with
`sixnxt_head.lean`, `sixnxt_tail.lean`); do not edit by hand.

* `RunTE` (every run under `%next sur th`, a goal with no entry, from a
  state with the premises of `LOKSE.run`, meets `RunOKLT`), `six_nextT`
  (phase S: the `%6` meets `RunTE`, from `six_nextGB`).
* `four_doneT`, `three_doneT` (generated from `four_doneB`, `three_doneB`):
  `[4 p]` and `[3 p]` under `%done` run their operand under `%next
  (lazy-from-reg r)`, a goal with no entry; from `RunTE` of the operand they
  meet `RunOKGB` of the operand's unwrapped need, with `WalkEq` to the real
  one, which `finishLUC_contractGBW` reads at the top.
* `fourSix_contract`, `threeSix_contract`: the whole-subject code of
  `[4 [6 [3 [0 2]] [0 3] [1 0]]]` and `[3 [6 [3 [0 2]] [0 3] [1 0]]]` meets
  both halves of the contract, with `#guard`s that the code exists and
  agrees with `+mink` on the 24 subjects of `CompSixLSCheck.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

/-- **Every run at a goal with no entry meets `RunOKLT`**, from a state
with the premises of `LOKSE.run`. -/
abbrev RunTE (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct sur.ned →
    (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) → Clean sur.ned →
    runLC env sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    ∃ Q, RunOKLT (Map := Map) lib N P f (ofSure sur) th Q false g0 g1 nex

/-- **Phase S: `[6 c a b]` meets `RunTE`** (`six_nextGB`, `RunOKGB.toLS`). -/
theorem six_nextT (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fc fa fb : Noun} {c a b : Nomm}
    {kc ka kb : Nat} (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc) (Fc : PickF (S := S) (Map := Map) env c)
    (Ha : SixN (S := S) (Map := Map) lib N env P fa a ka) (Hb : SixN (S := S) (Map := Map) lib N env P fb b kb)
    (hk : 5 + ka + kb ≤ lazyMax) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) := by
  intro sup sur th region g0 g1 nex hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hr
  obtain ⟨nexU, eth, unw, t1, R⟩ := six_nextGB lib env Hc Fc Ha Hb hk hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl
    hcs hr
  exact ⟨noWit, nexU, eth, unw, t1, R.toLS⟩

/-- (Generated from `four_doneB`.) **`[4 p]` under `%done` with an operand of `RunTE`**: the operand's
`RunOKLT` read on its unwrapped need, `RunOKLB.toGB`, `unaryGB_ok`. -/
theorem four_doneT (lib : Lib) {N : Needs} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Sp : RunTE (S := S) (Map := Map) lib N env P fb p) (M : MinkC4 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n4 p) CGoalL.done region g0 = some (nex, g1)) :
    ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEq (Map := Map) nex.laz nexU.laz ∧
      RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nexU := by
  have e4 : (runLC env sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runLC
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have e0 : ∀ a : Nat, entries (ofSure (lazyReg a : Sure S)) = [] := fun a => entries_ofSure _
  have GU := ((grow_reg g0 (g0.re + 1 + 1)).trans (grow_emit (g := { g0 with re := g0.re + 1 + 1 })
    (b := ⟨[], [Pole.inc (g0.re + 1) g0.re], Termin.don g0.re⟩) (jumpsBelow_nil rfl _))).toU hu
  obtain ⟨Qp, nexU, eth, unw, -, Rp⟩ := Sp (sur := lazyReg _) (th := jmp0 _) hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) (GU.up hu) (hcl0.growU GU)
    (CondFresh.below (condFresh_of_eq (g0 := g0) (by romega) rfl) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl trivial
    (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr
      exact ⟨by simp [emitted_re], condBelow_none hcb (by romega)⟩)
    trivial h
  have RG := Rp.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp [emitted_re])
  refine ⟨nexU, eth, unw.walkEq, ?_⟩
  refine unaryGB_ok M ((ext_re _).trans ((ext_re _).trans (ext_emit _ _)))
    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu) rfl
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl) RG
    (fix_of_keeps (gs := g0) rfl ((keepsA_reg _ g0 _ (by romega)).trans (keepsA_emitted d0 (blobIn_one
      (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        <;> exact condBelow_none hcb (by romega)) (condBelow_none hcb (by romega)))))
      ((keeps_reg g0 _ (by romega)).trans (keeps_emitted d0 (blobIn_one
      (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        <;> romega) (by simp only [FinIn]; romega)))))
    ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx] at hj
    refine ⟨Tone.zero (A (n + 1)), st, hI, Needs.le_refl _, ?_, ToneRel.zero _⟩
    rw [hj]; simp [execBlob_don', read_store_eq]
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx] at hj
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, hj, ToneRel.two htr⟩

/-- (Generated from `three_doneB`.) **`[3 p]` under `%done` with an operand of `RunTE`**. -/
theorem three_doneT (lib : Lib) {N : Needs} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Sp : RunTE (S := S) (Map := Map) lib N env P fb p) (M : MinkC3 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n3 p) CGoalL.done region g0 = some (nex, g1)) :
    ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEq (Map := Map) nex.laz nexU.laz ∧
      RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nexU := by
  have e3 : (runLC env sup (Nomm.n3 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let (o0, o1) ← doneBlocks
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runLC
  rw [e3] at h
  obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
  have B := doneBlocks_down h2 b0
  obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h2
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d2 : g2.drop = false := D.2.2.1.trans d0
  have G : Grow g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 g0.bo) (jmp0 (g0.bo + 1))⟩) :=
    B.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl B.2.1 B.2.2)))
  have e0 : ∀ a : Nat, entries (ofSure (lazyReg a : Sure S)) = [] := fun a => entries_ofSure _
  obtain ⟨Qp, nexU, eth, unw, -, Rp⟩ := Sp (sur := lazyReg _) (th := jmp0 _) hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu))
    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans D.1 (Nat.le_succ _))
      ((kc_doneBlocks.keep g0 _ g2 h2))) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl trivial
    (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr
      refine ⟨by simp [emitted_re], ?_⟩
      show HoonMap.get g2.cond _ = _
      rw [kc_doneBlocks.keep g0 _ g2 h2]; exact condBelow_none hcb D.1)
    trivial h
  have RG := Rp.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp [emitted_re])
  refine ⟨nexU, eth, unw.walkEq, ?_⟩
  refine unaryGTB_ok (T := fun _ => wutTone) wutTone_keep M.fwd M.bwd (D.trans ((ext_re _).trans (ext_emit _ _)))
    (G.toU hu) (kc_doneBlocks.keep g0 _ g2 h2)
    ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d2) rfl rfl) RG
    (fix_of_keeps (gs := g0) rfl ((keepsA_doneBlocks d0 (fun r hr => condBelow_none hcb hr) h2).trans
      ((keepsA_reg _ g2 _ (Nat.le_succ _)).trans (keepsA_emitted d2
        (blobIn_fin ⟨condBelow_none hcb D.1, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩))))
      ((keeps_doneBlocks d0 h2).trans ((keeps_reg g2 _ (Nat.le_succ _)).trans (keeps_emitted d2
        (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))))
    ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d2) (hc _ (by show g0.bo ≤ g2.bo; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  have DB' := DB c d0 (hc.left D ((ext_re _).trans (ext_emit _ _))) lib σ O st regs t gul
  cases x with
  | atom n => exact ⟨Tone.zero (A 1), st, hI, Needs.le_refl _, hj.trans DB'.2, ToneRel.zero _⟩
  | cell u v => exact ⟨Tone.zero (A 0), st, hI, Needs.le_refl _, hj.trans DB'.1, ToneRel.zero _⟩

/-! ## The top -/

/-- `[6 [3 [0 2]] [0 3] [1 0]]` meets `RunTE`: the test `pickD_three2`,
`pickF_pure`, the branches `sixN_of_uok`. -/
theorem six3N_runTE (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))
      (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0))) :=
  six_nextT lib env (pickD_three2 lib env P) (pickF_pure env rfl rfl)
    (sixN_of_uok lib env (uok_x lib (fragX_n0 (by decide)))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 3).annot P) hs gul tm r) rfl)
    (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 0)).annot P) hs gul tm r) rfl)
    (by decide)

/-- **`[4 [6 [3 [0 2]] [0 3] [1 0]]]` meets both halves of the contract**:
a `%6` under `%next`, the operand of `%4`. -/
theorem fourSix_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n4 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0)))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 4) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => four_doneT lib (six3N_runTE lib env _) (minkC4_four lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

/-- **`[3 [6 [3 [0 2]] [0 3] [1 0]]]` meets both halves of the contract**:
a `%6` under `%next`, the operand of `%3`. -/
theorem threeSix_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n3 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0)))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 3) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c ∧
      ContractBwd lib N s (n2 (A 3) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => three_doneT lib (six3N_runTE lib env _) (minkC3_three lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

/-- **A test that begins under `%pick` with the block `[brn re z o]`** (the
indirect call, `[0 axe]`) and whose need has no entries meets `PickF`
(`runLC_pick_next`, `noEnt_of_noEntF`). -/
theorem pickF_of_next (env : CallEnv) {nm : Nomm}
    (hs : (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax)) (hn : NoEntF nm) :
    PickF (S := S) (Map := Map) env nm := by
  intro sup z o region g0 g1 nex h
  rw [runLC_pick_next env sup hs z o region g0] at h
  exact entries_nil_flat (noEnt_of_noEntF (S := S) (Map := Map) env hn
    (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial h)

/-- `[6 [2 [0 3] [0 2]] [0 3] [1 0]]`, a calling test, meets `RunTE`: the
test `pickD_of_pickTree`, `pickF_of_next`. -/
theorem six2N_runTE (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (quote (A 0)))
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n1 (A 0))) :=
  six_nextT lib env
    (pickD_of_pickTree lib env (PickTree.ind (CallTreeA.n0 3) (CallTreeA.n0 2))
      (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)))
    (pickF_of_next env (Or.inl ⟨_, _, rfl⟩) (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)))
    (sixN_of_uok lib env (uok_x lib (fragX_n0 (by decide)))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 3).annot P) hs gul tm r) rfl)
    (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 0)).annot P) hs gul tm r) rfl)
    (by decide)

/-- **`[4 [6 [2 [0 3] [0 2]] [0 3] [1 0]]]` meets both halves of the
contract**: a `%6` with a calling test under `%next`, the operand of `%4`. -/
theorem fourSixCall_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n4 (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n1 (A 0)))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 4) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => four_doneT lib (six2N_runTE lib env _) (minkC4_four lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

-- The code of `fourSixCall_contract`'s nomm exists and agrees with `+mink`.
#guard SixCheck.sem [Nomm.n4 (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n1 (A 0)))] ==
  (1, 1, 24, 24)

-- The whole-subject code of both nomms exists and agrees with `+mink` on
-- the 24 subjects of `CompSixLSCheck.lean`.
#guard SixCheck.sem [Nomm.n4 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0))),
  Nomm.n3 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0)))] == (2, 2, 48, 48)

end Comp
end SkaModel
end Formalization
