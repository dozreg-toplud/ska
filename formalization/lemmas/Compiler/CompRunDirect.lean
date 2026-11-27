import lemmas.Compiler.CompRunDirectN
import lemmas.Compiler.CompRunFiveL
import lemmas.Compiler.CompRunResAll
import lemmas.Compiler.Safe

/-!
# The direct call of the case `%2` of `+run`: the dropped call

README Gaps 19.  The parts of `cr2Dir` (cut in `CompRunDirectN.lean`) that
the dropped call runs, each against the model `callL` of `Ska/CompCall.lean`
with `info = some (b, key)`:

* `crd_pure`: the push of `callee-pure`, `pure:(~(got by code.long-ska)
  b-callee)`, given the entry of `b` in `code` (`hgot`, `hv`).
* `crd_test`: the test `&(callee-pure ?=(%next -.goal) (none-equivalent
  laz.goal))` on a `%next` goal (`ne_all`).
* `crd_drop`: the dropped call (`+safe-fol-fol`, the run of `q`, `+past`,
  the run of `p`, `+copy`), as `cr2_tailL` for the indirect call.
* `comp_run_n2_drop`: the case `%2` with a callee whose code entry is
  `pure` on a `%next` goal whose need asks nothing, on every goal with
  `GInv`, against `runLC env msup`; `res_n2_drop`: what it returns
  (`GRes`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The noun of a direct call. -/
theorem crd_noun (p q : Nomm) (b : Bell) (key : Option Noun) :
    (Nomm.n2 p q (some (b, key))).toNoun
      = C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id key))))) := rfl

/-- **The push of `callee-pure`**: the field `pure` (axis `6`) of the entry
of `b` in `code.long-ska` (axis `52` of the context). -/
theorem crd_pure (hc : CompIn ctx) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (P Q B K V PV mono goal region sup : Noun) (g : Gen (TreapMap mugF)) (x : GenRest)
    (hgot : getF mugF B cod = some (C (A 0) V)) (hv : slot? 6 V = some PV) :
    nock (crSubj mono (C (A 2) (C P (C Q (C (A 0) (C B K))))) goal region sup (compCore g x ctx)) crDPure
      = some PV := by
  have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B cod V hgot
  unfold crDPure
  simp [nock_exec, crSubj, compCore, hc, hcode, by.arm_at, by_arm, by.got.arm_at, got_arm, hgt, hv]

/-- **The test of the drop** on a `%next` goal, the callee pure: `+none-equivalent`
of the goal's need (`ne_all`). -/
theorem crd_test (h7 : slot? 7 ctx = some compK) (N mono region sup : Noun) (laz : Lazy CSet) (th : Jmp)
    (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C (A 0) (crSubj mono N (CGoalL.next laz th).toNoun region sup (compCore g x ctx))) crDTest
      = some (loob (Lazy.noneEquivalentL laz)) := by
  have hD0 := compK_ne
  have hn := ne_all laz
  rw [cgl_next_noun]
  unfold crDTest
  generalize compK = KC at h7 hD0 hn
  cases e : Lazy.noneEquivalentL laz <;>
    simp [nock_exec, crSubj, compCore, h7, hD0, ne_arm, hn, e, loob]

/-- `ana` is at axis `63` of the context. -/
theorem crd_ctx63 (h7 : slot? 7 ctx = some compK) : slot? 63 ctx = some ana := by
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have := slot_spine (by omega) (by omega) h1 3
  simp only [show 2 ^ 3 * (7 + 1) - 1 = 63 from rfl, show 2 ^ 3 * (1 + 1) - 1 = 15 from rfl] at this
  rw [this]; rfl

/-- The model of the dropped call. -/
noncomputable def crdDropM (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (th : Jmp) (region : List Nat) :
    CM (TreapMap mugF) (NextL CSet) := do
  let nexFol ← (if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
    else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region : CM (TreapMap mugF) (NextL CSet))
  let nexFol ← pastL noCode nexFol p region
  let nexSub ← runLC env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexFol.th) region
  copyL nexSub nexFol.laz

/-- **The model of the case on a dropped call**: a callee whose code entry is
`pure`, a `%next` goal whose need asks nothing. -/
theorem crd_model (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (key : Option Noun)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (hpc : hinted env.cod p = hinted noCode p) :
    (runLC env msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = crdDropM env msup p q th region := by
  simp only [runLC, callL, hpu, hne, Bool.and_self, if_true, crdDropM, pastL_cod hpc]

/-- The first push of the dropped call: `+safe-fol-fol` of `q` (arm `767` of
`ana`), else the run of `q` for `[%next *need-lazy then.goal]`. -/
theorem crd_nf (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono I sup : Noun) (laz : Lazy CSet) (th : Jmp)
    (g : Gen (TreapMap mugF))
    (hq : CompRunAtR (runLC env msup) ctx q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g) :
    nock (C (A 0) (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) (CGoalL.next laz th).toNoun
      (listNoun A region) sup (compCore g x ctx))) crDNf
      = ((if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
          else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region : CM (TreapMap mugF) (NextL CSet))
          g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  have hq1 := hq x mono sup hx
  rw [cgl_next_noun, cr_bunt_noun] at hq1
  rw [cgl_next_noun]
  unfold crDNf
  simp only [crSubj, compCore] at hq1 ⊢
  generalize comp.door = Dr at hq1 ⊢
  cases hs : safeFolFol q with
  | true =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, cr_next_nounL, cr_bunt_noun]
  | false =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, cr_bat_dol, hq1]

/-- **The dropped call** after the test: the first push (`crd_nf`), `+past`
over `p` (`comp_past`), the run of `p` for `[%next *need-lazy then.nex-fol]`,
`+copy` (`comp_copy_all`). -/
theorem crd_drop (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono I sup : Noun) (laz : Lazy CSet) (th : Jmp)
    (g : Gen (TreapMap mugF))
    (hq : CompRunAtR (runLC env msup) ctx q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ nexF g2 nexF' g3, (if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
          else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region : CM (TreapMap mugF) (NextL CSet))
          g = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      CompRunAtR (runLC env msup) ctx p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, (if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
          else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region : CM (TreapMap mugF) (NextL CSet))
          g = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      runLC env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (C (A 0) (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) (CGoalL.next laz th).toNoun
      (listNoun A region) sup (compCore g x ctx))) crDDrop
      = (crdDropM env msup p q th region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hnf := crd_nf h7 env msup p q region x hx mono I sup laz th g hq
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  unfold crdDropM
  generalize hF : (if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
    else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region : CM (TreapMap mugF) (NextL CSet)) = F
    at hnf hp hcp
  simp only [crSubj, compCore] at hnf ⊢
  cases eq : F g with
  | none =>
    rw [eq] at hnf
    generalize comp.door = Dr at hnf hD1 hD2 ⊢
    unfold crDDrop
    simp [nock_exec, hnf, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hnf
    simp only [Option.map_some, cr_next_nounL] at hnf
    have hpa := comp_past h7 hcode x g2 nexF p region hpn
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode nexF p region g2 with
    | none =>
      rw [e3] at hpa
      generalize comp.door = Dr at hnf hD1 hD2 hpa ⊢
      unfold crDDrop crDD1 crDD2 crDD3
      simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      have hp1 := hp nexF g2 nexF' g3 eq e3 x mono sup hx
      rw [cgl_next_noun, cr_bunt_noun] at hp1
      simp only [crSubj, compCore] at hp1
      cases eq2 : runLC (S := CSet) (Map := TreapMap mugF) env msup p
          (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 ⊢
        unfold crDDrop crDD1 crDD2 crDD3
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 hcpy ⊢
        unfold crDDrop crDD1 crDD2 crDD3
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2, hD2, cr_cp_arm, hcpy, cr_next_nounL, Function.comp_def]

end Compiler
end Formalization
