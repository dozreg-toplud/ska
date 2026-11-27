import lemmas.Compiler.CompRunSoftCall
import lemmas.Compiler.CompSofPush
import lemmas.Compiler.CompRunTNClass

/-! # The corpus's soft tail call with its three side conditions discharged (README Gaps 19 (g))

`comp_run_n2_softTail` (`CompRunSoftCall.lean`) took three hypotheses.  Here:

* **`sof_push_val`**: the push of `sof` at any `mono` is `loob (!s && (t || hp || hq))` from the
  values `s` of `+sound-far` and `t` of `+need-soft` (`sof_push` with the value kept);
  `SofRetS`: the push gives `&` at `mono` `|`; **`sofRetS_of`** from `+sound-far` giving `|` and
  `+need-soft` giving `&`; `callNounS_of_read` (`CallNounM` at `SOF = A 0`, the copy of
  `callNounN_of_read`);
* **`softBond_spec`**: `+soft-bond` keeps `re` and returns the lazy need
  `[bunt ~ [[o (lazy-from-sure sure.laz)] ~]]` (one bond at the middle block);
* `walkP_softBond`: the lock walk of that need (`WalkP lok0`), from `lok` empty in the call's
  `[sub-ned ~]`;
* `copyH_softTail`: `CopyH` of the corpus call (`p = [0 1]` returns its goal, `q` a quote
  skipped), from the registers of `sub-ned` below `re` (`needOrdAllocRegs_spec`);
* **`comp_run_n2_softTailR`**: the corpus call `[2 [0 1] [1 f] [~ b ~]]` under `%done` with only
  the facts of the callee: its `call.cole` entry, `jets-hot`, the need read (`NeedRead`), the
  `sure.cache` entry (`SureNoun`), `SofRetS`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **The push of `sof` with its value**, at any `mono`: `sof_push` with the loobeans of
`+sound-far` (`s`) and `+need-soft` (`t`) given. -/
theorem sof_push_val (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd) (x : GenRest) (mono : Noun)
    (hcp : CallCode cod env p) (hcq : CallCode cod env q) (s t : Bool)
    (hs : nock (C sfBat (C (C (made p msup).toNoun (C nb.toNoun (C cod (A 3)))) compK)) sfBat = some (loob s))
    (ht : nock (C nsBat (C (C nb.toNoun (C (env.sure b).toNoun b.less.toNoun)) compK)) nsBat = some (loob t)) :
    ∃ hp hq : Bool, ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
      nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj mono (crdN p q b) goalN regionN
        (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some (loob (!s && (t || hp || hq))) := by
  obtain ⟨hp, ehp⟩ := hinted_code p hcp
  obtain ⟨hq, ehq⟩ := hinted_code q hcq
  have hdp := hd_gateR cod env p hp hcp ehp
  have hdq := hd_gateR cod env q hq hcq ehq
  have hK := compK_hd
  have hN := compK_ns
  have hM := comp_made_at
  have hS := comp_sound_at
  refine ⟨hp, hq, fun g SV SN PV goalN regionN => ?_⟩
  have hsnd := snd_gate h7 hcode g x (made p msup).toNoun nb.toNoun
  have hmd := made_gate (compCore g x ctx) p msup
  rw [hs] at hsnd
  simp only [compCore] at hsnd hmd
  unfold crDKc6
  simp only [compCore]
  generalize comp.door = Dr at hM hS hsnd hmd ⊢
  cases s <;> cases t <;> cases hp <;> cases hq <;>
    simp [nock_exec, crSubj, Bell.toNoun, h7, hcode, hK, hN, hM, hS, hd_arm, ns_arm, snd_arm, madArm, hsnd,
      hmd, hdp, hdq, ht, loob]

/-- **The push of `sof` gives `&`** at the rest `x` (`mono` `|`): what the soft call asks of the
pill's `sof` (line 3975). -/
def SofRetS (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (x : GenRest) : Prop :=
  ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj (A 1) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some (A 0)

/-- **`SofRetS` from the two arms**: `+sound-far` gives `|` on `(made p sup)` and the callee's
need, `+need-soft` gives `&` on the need, `b-sur` and `less` of the callee, and the callees of
`p` and `q` have their code entries.  It holds at every rest. -/
theorem sofRetS_of (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (hcp : CallCode cod env p) (hcq : CallCode cod env q)
    (hs : nock (C sfBat (C (C (made p msup).toNoun (C nb.toNoun (C cod (A 3)))) compK)) sfBat = some (loob false))
    (ht : nock (C nsBat (C (C nb.toNoun (C (env.sure b).toNoun b.less.toNoun)) compK)) nsBat = some (loob true))
    (x : GenRest) : SofRetS env msup ctx p q b nb x := by
  obtain ⟨hp, hq, h⟩ := sof_push_val h7 hcode env msup p q b nb x (A 1) hcp hcq false true hs ht
  intro g SV SN PV goalN regionN
  rw [h g SV SN PV goalN regionN]
  simp [loob]

/-- **`CallNounM` at `SOF = A 0` of a callee read at the rest** (the copy of
`callNounN_of_read` with `SofRetS`). -/
theorem callNounS_of_read (h7 : slot? 7 ctx = some compK) {env : CallEnv} {msup : Option Nomm} {p q : Nomm}
    {b : Bell} {nb : NeedOrd} {x : GenRest}
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hr : NeedRead ctx x b nb) (hs : SureNoun env b x)
    (hso : SofRetS env msup ctx p q b nb x) :
    CallNounM msup ctx p q b nb (env.sure b).toNoun x (A 1) (A 0) :=
  ⟨hcole, hhot, cne_read h7 b nb x hcole hhot hr, csu_gate (comp_ctx_pill ctx h7).1 env b x hs, hso⟩

/-- **What `+soft-bond` returns**: `re` kept, the lazy need one bond at a block `o`, holding
`(lazy-from-sure sure.laz.nex)`. -/
theorem softBond_spec {nex : NextL CSet} {region : List Nat} {s s' : GenSf (TreapMap mugF)} {r : NextL CSet}
    (h : softBond nex region s = some (r, s')) :
    s'.g.re = s.g.re ∧ ∃ o, r.laz = Lazy.mk Sure.bunt [] [(o, Lazy.ofSure nex.laz.sure)] := by
  unfold softBond at h
  simp only [bind, StateT.bind, liftS, cf_emit_g, Option.map_some, Option.bind_some, setTag] at h
  cases e : HoonMap.get s.soft nex.th.there with
  | none => simp [e] at h
  | some c =>
    simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, _, rfl⟩
    simp only [cfEmitG]
    repeat (first | rfl | split)

/-- The lock walk of the lazy need `+soft-bond` returns for a call: every sure need it visits
looks at no axis `0` (the bunt and `[sub-ned ~]` have no lock). -/
theorem walkP_softBond (subNed : Need) (cb : Nat) {region : List Nat} {s s' : GenSf (TreapMap mugF)}
    {r : NextL CSet} (h : softBond (crdArg subNed cb) region s = some (r, s')) : WalkP lok0 0 r.laz := by
  obtain ⟨-, o, hl⟩ := softBond_spec h
  rw [hl]
  simp only [crdArg, Lazy.ofSure, WalkP, WalkPF, WalkPB, lok0, Sure.bunt]
  refine ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial,
    ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, trivial⟩, trivial⟩

/-- **`CopyH` of the corpus's soft tail call**: `q = [1 f]` is skipped, `+past` over `[0 1]` keeps
the bunt, `[0 1]` returns its goal, so `+copy` is of the bond need `+soft-bond` returns (the
registers of `sub-ned`, below `re`) with the bunt. -/
theorem copyH_softTail (env : CallEnv) (msup : Option Nomm) (f : Noun) (b : Bell) (nb : NeedOrd)
    (gs : GenSf (TreapMap mugF)) (region : List Nat) :
    ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed (env.sure b)) = some (nexB, gs2) →
      ∀ nexF g2 nexF' g3 nexS g4, crdFqR (runLC env msup) (Nomm.n1 f) nexB.th region gs2.g = some (nexF, g2) →
      pastL env.cod nexF (Nomm.n0 1) region g2 = some (nexF', g3) →
      runLC env msup (Nomm.n0 1) (CGoalL.next nexB.laz nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz := by
  intro subNed g1 nexB gs2 e1 e2 nexF g2 nexF' g3 nexS g4 e3 e4 e5
  obtain ⟨-, -, -, hmem⟩ := needOrdAllocRegs_spec nb gs.g g1 subNed e1
  obtain ⟨hre, o, hl⟩ := softBond_spec e2
  have hsq : safeFolFol (Nomm.n1 f) = true := rfl
  simp only [crdFqR, hsq, if_true, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl⟩ := e3
  have hpb : (pastL env.cod (⟨Lazy.ofSure Sure.bunt, nexB.th⟩ : NextL CSet) (Nomm.n0 1) region :
      CM (TreapMap mugF) (NextL CSet)) = pure ⟨Lazy.ofSure Sure.bunt, nexB.th⟩ := by
    unfold pastL
    rw [if_pos ⟨rfl, small_empty, rfl⟩]
  rw [hpb] at e4
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  rw [runLC_n0] at e5
  simp only [runL, simpleNextL, pure, StateT.pure, bind, StateT.bind, Option.bind_some, if_true,
    Option.some.injEq, Prod.mk.injEq] at e5
  obtain ⟨rfl, rfl⟩ := e5
  have hre1 : gs2.g.re = g1.re := by
    rw [hre]; simp only [softGs1, cfEmitG]; repeat (first | rfl | split)
  apply copyH_of_regs
  · intro r hr
    simp only [hl, lregs, fregs, bregs, crdArg, Lazy.ofSure, Sure.bunt, flattenNeed, List.nil_append,
      List.append_nil] at hr
    rw [hre1]
    exact ((hmem r ((mem_flat subNed r).1 hr))).2
  · intro r hr
    simp [Lazy.ofSure, lregs, fregs, bregs, Sure.bunt, flattenNeed] at hr
  · intro r _ hr
    simp [Lazy.ofSure, lregs, fregs, bregs, Sure.bunt, flattenNeed] at hr

/-- **The soft tail call of the corpus, side conditions discharged** (`[2 [0 1] [1 f] [~ b ~]]`
under `%done`, `sof` `&`): `comp_run_n2_softTail` with `CallNounM` from the callee's facts at the
rest (`callNounS_of_read`), the lock walk from `walkP_softBond`, and `CopyH` from
`copyH_softTail`. -/
theorem comp_run_n2_softTailR (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) (f : Noun)
    (hpn : PastAt ctx env.cod (Nomm.n0 1)) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd)
    (region : List Nat) (gs : GenSf (TreapMap mugF))
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (hsof : env.sof (made (Nomm.n0 1) msup) (Nomm.n0 1) (Nomm.n1 f) b nb = true)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hsY : ∀ {x y : GenRest} (s : Noun), Y x y → Y x { y with soft := s })
    (x : GenRest) (hx : x.soft = softMapNoun gs.soft)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hrd : NeedRead ctx x b nb) (hsu : SureNoun env b x)
    (hso : SofRetS env msup ctx (Nomm.n0 1) (Nomm.n1 f) b nb x) :
    ∃ x', Y x x' ∧
      nock (crSubj (A 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))).toNoun
        (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore gs.g x ctx)) crDol
      = (runLCS (S := CSet) env snd msup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))) CGoalL.done
          region gs).map
          fun r => C r.1.goal.toNoun (genNoun r.2.g { x' with soft := softMapNoun r.2.soft }) :=
  comp_run_n2_softTail h7 hcode env snd msup f hpn b hcd nb region gs hri hnb hsof hr ht hsY x hx
    (callNounS_of_read h7 hcole hhot hrd hsu hso)
    (fun subNed g1 nexB gs2 _ e2 => walkP_softBond subNed g1.bo e2)
    (copyH_softTail env msup f b nb gs region)

end Compiler
end Formalization
