import lemmas.Compiler.CompRunHintMeanNo
import lemmas.Compiler.CompRunHintKP

/-!
# The case `%mean` of `+run` on every goal, as a part (README Gaps 25)

* `runLCH_mean_konst`: on a constant `n` (and `snd p [%none ~]`) the model
  at `mono` `&` is `+simple-next`, then `cmFrom`.
* **`comp_run_mean_no`**: the case on a constant, on every goal, from
  `SoundAt` of `p` and `q`, `snd p [%none ~]`, the code entry of `b`, and
  what the part from the run of `q` takes (`CmRest`).
* `cm_steps`: the goals of `q` and `p` meet `GInv` and the `+copy` meets
  `CopyH` (the proof of `cd_steps` with no `+re`, the trap's goal
  `[%next [[%none ~] ~] ~ prol]`).
* **`partH_mean_no`**, **`partH_mean`**: `PartH` of `p` and `q`, `SoundAt`
  of both, `snd p [%none ~]` on a constant, the code entry of `b` when `k`
  is `some`: `PartH` of `[%mean p b q body k]`, constant or not.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {ctx : Noun}

theorem cmGoal_bunt (prol : Nat) : cmGoal Need.none prol = CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 prol) := rfl

/-- On a constant the model at `mono` `&` is `+simple-next`, then `cmFrom`. -/
theorem runLCH_mean_konst (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) {p q : Nomm} {b : Bell}
    {body : Noun} {k : Option Noun} {n : Noun} (hk : meanKonst env b k = some n) (hsp : snd p NeedOrd.none = true)
    (goal : CGoalL CSet) (region : List Nat) :
    (runLCH env snd true msup (Nomm.mean p b q body k) goal region : CM (TreapMap mugF) (NextL CSet)) =
      simpleNextL goal >>= cmFrom (runLCH env snd true msup) snd p q n body Need.none region := by
  simp only [runLCH, hk, hsp, needOrdAllocRegs, Bool.not_true, Bool.false_eq_true, if_false, cmFrom, cmTail7,
    cmTail11, cmEpil, cmProl, cmGoal]
  rfl

/-- **The case `%mean` on a constant**, on every goal, at `mono` `&`. -/
theorem comp_run_mean_no (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) {E : GenRest → Prop}
    (p q : Nomm) (b : Bell) (body : Noun) (k : Option Noun) (n : Noun) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hk : meanKonst env b k = some n) (hcd : CodePure cod env b)
    (hsq : SoundAt ctx snd q) (hs : SoundAt ctx snd p) (hsp : snd p NeedOrd.none = true)
    (hR : ∀ nex4 g1 nex5 g2, simpleNextL goal g = some (nex4, g1) → pastIfL snd nex4 q region g1 = some (nex5, g2) →
      CmRest (runLCH env snd true msup) ctx (XM E msup) p q n body region Need.none nex5.laz g2.bo
        (cfEmitG (cmEpil n body nex5.th) g2)) :
    CompRunAtX (runLCH env snd true msup) ctx (XM E msup) (Nomm.mean p b q body k) goal region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  intro x mono sup hx hX
  have hX' := hX
  obtain ⟨hE, rfl, rfl⟩ := hX
  rw [runLCH_mean_konst env snd msup hk hsp]
  have hno := cm_no h7 p q b body k n goal region x hx (A 0) (unitNoun Nomm.toNoun msup) g hsq hs hsp hR hX'
  rw [← hno]
  have hmk : nock (C mkBat (C (C b.toNoun (unitNoun id k)) (compCore g x ctx))) mkBat = some (C (A 0) n) := by
    rw [comp_mean_konst hc hcode env b k g x (fun _ => hcd), hk]; rfl
  simp only [Nomm.toNoun]
  rw [cr_disp_mean, cm_eq]
  have hD1 := mk_at
  simp only [crSubj, compCore] at hmk hno ⊢
  generalize comp.door = Dr at hmk hD1 hno ⊢
  unfold cmHead cmKonst cmTest
  simp [nock_exec, hD1, mk_arm, hmk, Tag.mean]

/-- **The steps of the constant case** from a goal with `GInv`. -/
theorem cm_steps {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)} {snd : Nomm → NeedOrd → Bool}
    {p q : Nomm} {n body : Noun} {region : List Nat}
    (Qr : ResForR R q region) (Pr : ResForR R p region) {goal : CGoalL CSet}
    {g g1 g2 : Gen (TreapMap mugF)} {nex0 nex1 : NextL CSet} (hi : GInv g goal)
    (e0 : simpleNextL goal g = some (nex0, g1)) (e1 : pastIfL snd nex0 q region g1 = some (nex1, g2)) :
    GInv (cfEmitG (cmEpil n body nex1.th) g2) (CGoalL.next nex1.laz (jmp0 g2.bo)) ∧
    ∀ n1 g5 n2 g6, R q (CGoalL.next nex1.laz (jmp0 g2.bo)) region (cfEmitG (cmEpil n body nex1.th) g2)
        = some (n1, g5) →
      lazyBound n1 region g5 = some (n2, g6) →
      GInv (cfEmitG (cmProl n body n2.th) g6) (cmGoal Need.none g6.bo) ∧
      ∀ n3 g8, R p (cmGoal Need.none g6.bo) region (cfEmitG (cmProl n body n2.th) g6) = some (n3, g8) →
        CopyH g8.re n3.laz n2.laz ∧ LInv g8.re g8.bo n3.laz ∧ LInv g8.re g8.bo n2.laz ∧
        (lregs n3.laz ++ lregs n2.laz).Nodup ∧ g8.drop = false ∧ g.re ≤ g8.re ∧ g.bo ≤ g8.bo ∧
        ∀ r ∈ lregs n3.laz ++ lregs n2.laz, g.re ≤ r ∨ r ∈ gregs goal := by
  obtain ⟨l0, b0, ⟨i0, d0, j0⟩, s0⟩ := simpleNextL_res hi e0
  obtain ⟨r1, b1, d1, i1, j1, m1⟩ := pastIfL_inv i0 j0 e1
  have rr : (cfEmitG (cmEpil n body nex1.th) g2).re = g2.re := cf_emitG_re _ _
  have bb : (cfEmitG (cmEpil n body nex1.th) g2).bo = g2.bo + 1 := cf_emitG_bo _ _
  have dd : (cfEmitG (cmEpil n body nex1.th) g2).drop = g2.drop := cf_emitG_drop _ _
  have iq : GInv (cfEmitG (cmEpil n body nex1.th) g2) (CGoalL.next nex1.laz (jmp0 g2.bo)) :=
    ⟨linv_mono i1 (by omega) (by omega), by rw [dd, d1, d0], jmpIn_jmp0 _ _⟩
  refine ⟨iq, fun n1 g5 n2 g6 e3 e4 => ?_⟩
  obtain ⟨l3, b3, i3, s3⟩ := Qr _ _ _ _ iq e3
  obtain ⟨rfl, r4, b4, d4⟩ := lazyBound_eq e4
  obtain ⟨i3l, d3, -⟩ := i3
  obtain ⟨L4, M4⟩ := linv_bound i3l
  have ih : GInv (cfEmitG (cmProl n body (jmp0 g5.bo)) g6) (cmGoal Need.none g6.bo) := by
    rw [cmGoal_bunt]
    exact ginv_bunt_j (by rw [cf_emitG_drop, d4, d3]) (jmpIn_jmp0 _ _)
  refine ⟨ih, fun n3 g8 e5 => ?_⟩
  obtain ⟨l5, b5, ⟨i5, d5, -⟩, s5⟩ := Pr _ _ _ _ ih e5
  rw [cf_emitG_re] at l5
  rw [cf_emitG_bo] at b5
  simp only at M4 L4 ⊢
  have hn2 : ∀ r ∈ lregs n1.laz, r < g5.re := lnb_regs i3l.1
  have hn3 : ∀ r ∈ lregs n3.laz, g6.re ≤ r := fun r hr => by
    rcases s5 r hr with e | e
    · rw [cf_emitG_re] at e; exact e
    · rw [cmGoal_bunt] at e
      simp only [gregs, lregs_bunt] at e
      exact absurd e (List.not_mem_nil)
  have apart : ∀ r ∈ lregs n3.laz, r ∉ lregs n1.laz := fun r h3 h2 => by
    have := hn2 r h2
    have := hn3 r h3
    omega
  refine ⟨copyH_of_regs (lnb_regs i5.1) (fun r hr => by rw [M4] at hr; have := hn2 r hr; omega)
      (fun r hr hr' => apart r hr (M4 ▸ hr')), i5, linv_mono L4 (by omega) (by omega),
    ?_, d5, by omega, by omega, fun r hr => ?_⟩
  · rw [List.nodup_append, M4]
    exact ⟨i5.2.1, M4 ▸ L4.2.1, fun a ha b hb e => apart a ha (e ▸ hb)⟩
  · rcases List.mem_append.1 hr with hr | hr
    · have := hn3 r hr; left; omega
    · rw [M4] at hr
      rcases s3 r hr with e' | e'
      · left; rw [rr] at e'; omega
      · simp only [gregs] at e'
        rcases s0 r ((m1 r).1 e') with e'' | e''
        · left; exact e''
        · right; exact e''

/-! ## As a part -/

/-- **No constant, as a part**: through `partH_n11d_kept`. -/
theorem partH_mean_yes (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {msup : Option Nomm} {E : GenRest → Prop} {p q : Nomm}
    (b : Bell) (body : Noun) (k : Option Noun) {region : List Nat} (hk : meanKonst env b k = Option.none)
    (hcd : k.isSome = true → CodePure cod env b)
    (P : PartH env snd msup ctx (XM E msup) p region) (Q : PartH env snd msup ctx (XM E msup) q region)
    (hsq : SoundAt ctx snd q) (hcp : CallCode cod env p) (hcq : CallCode cod env q) :
    PartH env snd msup ctx (XM E msup) (Nomm.mean p b q body k) region := by
  have hdy : hintDynamic Tag.mean = true := by decide
  have K := partH_n11d_kept h7 hdy body Q P hsq (pastAt_code h7 hcode env ⟨hcp, hcq⟩)
  refine ⟨fun goal g hi => comp_run_mean_yes h7 hcode env snd msup p q b body k goal region g hk hcd (K.link goal g hi),
    fun goal g g' nex hi he => K.res goal g g' nex hi (by rwa [runLCH_mean_none env snd msup hk] at he),
    pastAt_code h7 hcode env trivial⟩

/-- **A constant, as a part.** -/
theorem partH_mean_no (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {msup : Option Nomm} {E : GenRest → Prop} {p q : Nomm}
    (b : Bell) (body : Noun) (k : Option Noun) (n : Noun) {region : List Nat} (hk : meanKonst env b k = some n)
    (hcd : CodePure cod env b)
    (P : PartH env snd msup ctx (XM E msup) p region) (Q : PartH env snd msup ctx (XM E msup) q region)
    (hsq : SoundAt ctx snd q) (hs : SoundAt ctx snd p) (hsp : snd p NeedOrd.none = true) :
    PartH env snd msup ctx (XM E msup) (Nomm.mean p b q body k) region := by
  refine ⟨fun goal g hi => ?_, fun goal g g' nex hi he => ?_, pastAt_code h7 hcode env trivial⟩
  · refine comp_run_mean_no h7 hcode env snd msup p q b body k n goal region g hk hcd hsq hs hsp
      (fun nex4 g1 nex5 g2 e0 e1 => ?_)
    obtain ⟨iq, K⟩ := cm_steps (n := n) (body := body) Q.res P.res hi e0 e1
    exact ⟨Q.link _ _ iq, fun n1 g5 n2 g6 e3 e4 => P.link _ _ (K n1 g5 n2 g6 e3 e4).1,
      fun n1 g5 n2 g6 n3 g8 e3 e4 e5 => ((K n1 g5 n2 g6 e3 e4).2 n3 g8 e5).1⟩
  · rw [runLCH_mean_konst env snd msup hk hsp] at he
    obtain ⟨nex0, g1, e0, he⟩ := bind_some he
    simp only [cmFrom] at he
    obtain ⟨nex1, g2, e1, he⟩ := bind_some he
    obtain ⟨epil, g4, e3, he⟩ := bind_some he
    rw [cf_emit_g] at e3
    simp only [Option.some.injEq, Prod.mk.injEq] at e3
    obtain ⟨rfl, rfl⟩ := e3
    simp only [cmTail7] at he
    obtain ⟨n1, g5, e4, he⟩ := bind_some he
    obtain ⟨n2, g6, e5, he⟩ := bind_some he
    obtain ⟨prol, g7, e6, he⟩ := bind_some he
    rw [cf_emit_g] at e6
    simp only [Option.some.injEq, Prod.mk.injEq] at e6
    obtain ⟨rfl, rfl⟩ := e6
    simp only [cmTail11] at he
    obtain ⟨n3, g8, e7, e8⟩ := bind_some he
    obtain ⟨-, K⟩ := cm_steps (n := n) (body := body) Q.res P.res hi e0 e1
    have K2 := (K n1 g5 n2 g6 e4 e5).2 n3 g8 e7
    obtain ⟨-, i3, i2, nd, d8, l8, b8, rg⟩ := K2
    obtain ⟨l, b, gi, rs⟩ := copyL_inv i3 i2 nd d8 e8
    exact ⟨by omega, by omega, gi, fun r hr => by
      rcases rs r hr with e | e
      · exact rg r e
      · left; omega⟩

/-- **The case `%mean` as a part**, constant or not, at `mono` `&`:
`PartH` of `p` and `q`, `SoundAt` of both, `snd p [%none ~]` on a constant,
the code entry of `b` when `k` is `some`, the code of the calls in `p`, `q`. -/
theorem partH_mean (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {msup : Option Nomm} {E : GenRest → Prop} {p q : Nomm}
    (b : Bell) (body : Noun) (k : Option Noun) {region : List Nat}
    (hcd : k.isSome = true → CodePure cod env b)
    (P : PartH env snd msup ctx (XM E msup) p region) (Q : PartH env snd msup ctx (XM E msup) q region)
    (hsq : SoundAt ctx snd q) (hs : SoundAt ctx snd p)
    (hsp : (meanKonst env b k).isSome = true → snd p NeedOrd.none = true)
    (hcp : CallCode cod env p) (hcq : CallCode cod env q) :
    PartH env snd msup ctx (XM E msup) (Nomm.mean p b q body k) region := by
  cases hk : meanKonst env b k with
  | none => exact partH_mean_yes h7 hcode b body k hk hcd P Q hsq hcp hcq
  | some n =>
    have hks : k.isSome = true := by
      cases k with
      | none => simp [meanKonst] at hk
      | some _ => rfl
    exact partH_mean_no h7 hcode b body k n hk (hcd hks) P Q hsq hs (hsp (by rw [hk]; rfl))

end Compiler
end Formalization
