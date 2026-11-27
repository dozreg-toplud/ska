import lemmas.Ska.CompDirectMCal
import lemmas.Ska.CompDirectMTailEx

/-!
# A direct call under `%4` at the top, with `mono` `&`

README Gaps 18.13 (track J, 2026-11-27).  The first contract theorem with a
direct call under `%next` (the `%cal` form of `callLBM`):

* `four_doneBM`: `four_doneB` (`CompFourTop.lean`, unchanged) for the
  whole-subject run (`runLCM env true`), the operand meeting `LOKSM false`.
* `finishLUCM_contractFourDirect`: both halves of the contract of
  `[4 [2 p [1 k] b]]` on the real whole-subject code, `p` meeting `LOKS
  false` with no direct call (track C's class), hypotheses only on the needs
  and `Annot.direct`; `finishLUCM_bellContractFourDirect` the `BellContract`
  form for `p = [0 1]`.
* The instance `[4 callR]` (`R`'s call under `%4`): a `#guard` of its code
  (the blocks of `%dn` of `CompDirectMCheck.lean` from the `%4` on), and
  `fourCallR_bellContract`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `omega` after reducing the projections of the states (as in `CompFourTop.lean`). -/
local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`four_doneB` for the whole-subject run**: `[4 p]` under `%done` meets
`DoneOK` when `p` meets `LOKSM false`.  The text of `four_doneB`. -/
theorem four_doneBM (lib : Lib) {N : Needs} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Sp : LOKSM (S := S) (Map := Map) false lib N env P fb p) (M : MinkC4 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLCM env true sup (Nomm.n4 p) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P f g0 g1 nex := by
  have e4 : (runLCM env true sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runLCM env true sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runLCM
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have e0 : ∀ a : Nat, entries (ofSure (lazyReg a : Sure S)) = [] := fun a => entries_ofSure _
  have GU := ((grow_reg g0 (g0.re + 1 + 1)).trans (grow_emit (g := { g0 with re := g0.re + 1 + 1 })
    (b := ⟨[], [Pole.inc (g0.re + 1) g0.re], Termin.don g0.re⟩) (jumpsBelow_nil rfl _))).toU hu
  obtain ⟨⟨Qp, Rp⟩, pne, -, pfl, pec⟩ := Sp.run (L := ofSure (lazyReg _)) (th := jmp0 _) hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) (GU.up hu) (hcl0.growU GU)
    (CondFresh.below (condFresh_of_eq (g0 := g0) (by romega) rfl) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl (by rw [e0]; simp) trivial
    (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr
      exact ⟨by simp [emitted_re], condBelow_none hcb (by romega)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h
  have RG := Rp.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp [emitted_re])
  refine ⟨?_, pne, pfl, Sp.clean (L := ofSure (lazyReg _)) trivial h, pec⟩
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

/-- **`[4 [2 p [1 k] b]]` at the top meets both halves of the contract** on
the real whole-subject code (`finishLUCM`): the direct call under `%next`
(`lokSM_direct`), `p` meeting `LOKS false` with no direct call, the callee
not pure, the needs as in `tail_done`, the products of `p` fitting the
bell. -/
theorem finishLUCM_contractFourDirect (lib : Lib) {env : CallEnv} {P : Noun → Prop} {p : Nomm} {fb k : Noun}
    {b : Bell} {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true) (hcount : sixCount p ≤ 255)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y) (hk : k = b.fol)
    {c : Straight Map}
    (hc : finishLUCM (S := S) env (Nomm.n4 (Nomm.n2 p (Nomm.n1 k) (some (b, Option.none)))) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s (n2 (A 4) (n3 (A 2) fb (C (A 1) k))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n3 (A 2) fb (C (A 1) k))) [s] c := by
  subst hk
  have Sc := lokSM_direct (S := S) (Map := Map) lib env (q := Nomm.n1 b.fol) (fq := C (A 1) b.fol) hring hned hNf hNt
    hpure Sp hpd rfl hAp (fun _ h => quote_hq1 h) (fun _ => quote_hq2)
  exact finishLUCM_contractGB lib N (fun hr => (four_doneBM lib Sc (minkC4_four lib P _)
    (by simp only [sixCount]; omega) (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

end

/-! ## The instance: `R`'s call under `%4` -/

/-- The caller's bell for `[4 callR]`: the subject fits `R-bell`. -/
def bellF : Bell := ⟨bellR.less, n2 (A 4) (tailFol nounR)⟩

/- The whole-subject code of `[4 callR]`, registers and labels as the
Hoon's: the blocks of `%dn` (`CompDirectMCheck.lean`) from the `%4` on
(`inc`, `+kerf`'s `out`, the merge block with `par [v5]`, `cal R-bell [v3]
v7` and `csl R-bell v6 v8` hopping with their product, the tree); `%dn`'s
`[[1 R] [0 1]]` in front is the `%1` no class has yet. -/
#guard monoOutM (Nomm.n4 callR) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6] (hp 8)), (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 4 2] (hp 1)), (3, bkp [5] [Pole.mov 5 4] (hp 2)),
    (4, bk [Pole.cal bellR [3] 7] (hpa 7 3)), (5, bk [Pole.csl bellR 6 8] (hpa 8 3)),
    (6, bk [Pole.mov 9 3] (hp 4)), (7, bk [Pole.hed 6 10, Pole.tal 6 9] (hp 6)),
    (8, bk [] (Termin.clq 6 (jmp0 7) (jmp0 5))), (9, Option.none)])

/-- **The bell contract of `R`'s call under `%4` at the top**, on the real
whole-subject code, for every needs table with `R-bell`'s n-ary need
`[~ this]` and a need for its call by subject. -/
theorem fourCallR_bellContract {lib : Lib} {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {cd : Straight FM} (hc : finishLUCM (S := LS) envD (Nomm.n4 callR) = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bellF true cd := by
  have H := finishLUCM_contractFourDirect (S := LS) lib (P := SkaModel.Fits bellF.less) (env := envD) rfl
    (by simp [envD]) hNf hNt rfl (lokS_callTree (S := LS) (Map := FM) lib envD _ (CallTree.n0 1)).1 rfl
    (by simp [sixCount]) (fun x gul y hx hm => by
      have := Mink.det hm ⟨1, minkStep_axis1 _ _ _ _ _⟩
      cases this; exact hx) rfl hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
