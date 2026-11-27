import lemmas.Compiler.CompRunDirectMonoB
import lemmas.Compiler.CompRunDirectP
import lemmas.Ska.CompRunLCM

/-!
# The direct call of `%2` under `mono` `&`: the parts, the case, the result

README Gaps 19.  `crd_callM` (`CompRunDirectMonoB.lean`) linked the call
`crDCall` at `mono` `A 0` against `callDM` with the runs of `p` and `q` and
the `CopyH` of their results as hypotheses.  Here, as `CompRunDirectP.lean`
does for `mono` `|`:

* `km_monoTryLoop`, `km_crdBlockMM`, `km_monoBlocks`: `+mono-try-call` and
  the blocks of step `7` keep the counters' order, `drop` and the tags;
  `crdBlockMM_sub`, `monoBlocks_sub`: the register `sub-pes` is fresh (at or
  above the counter before, below the counter after).
* `crd_goalsM`: the goals of `q` (`[%next *need-lazy ~ call-block]`) and of
  `p` (`ofSure (lazyReg sub-pes)`) after the blocks meet `GInv` / `LInv`.
* `runLCM_n2_direct`, `crd_model_n2M`: the model of the case at `mono` `&`.
* `comp_run_n2_callMono`: the case `%2` from `cr2Dir` at `mono` `A 0`
  against `runLCM env true msup`, one instance (`RunAtR`), with the runs as
  hypotheses (the shape of `comp_run_n2_call`).
* `PartLM`, `crd_hpqM`, `comp_run_n2_callMM`: the runs from what the call
  takes of a part at `mono` `A 0` (the shape of `comp_run_n2_callM`).
* `res_n2_callMono`: what the call returns meets `GRes` (the shape of
  `res_n2_call`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## What the blocks and `+mono-try-call` keep -/

/-- **`+mono-try-call`** keeps the counters' order, `drop` and the tags. -/
theorem km_monoTryLoop (fail : Nat) :
    ∀ (ned : Need) (r o : Nat), KM (monoTryLoop fail ned r o : CM (TreapMap mugF) Nat)
  | Need.none, _, o => by unfold monoTryLoop; exact KM.pure' _
  | Need.this rn, r, o => by
      unfold monoTryLoop; exact KM.ite' _ KM.fail (KM.emit' _)
  | Need.pair h t, r, o => by
      unfold monoTryLoop
      exact KM.bind' KM.re' fun rt => KM.bind' KM.re' fun rh =>
        KM.bind' (km_monoTryLoop fail t rt o) fun ot => KM.bind' (km_monoTryLoop fail h rh ot) fun _ =>
          KM.bind' (KM.emit' _) fun _ => KM.emit' _
  | Need.both rn h t, r, o => by
      unfold monoTryLoop
      exact KM.bind' KM.re' fun rt => KM.bind' KM.re' fun rh =>
        KM.bind' (km_monoTryLoop fail t rt o) fun ot => KM.bind' (km_monoTryLoop fail h rh ot) fun _ =>
          KM.ite' _ KM.fail (KM.bind' (KM.emit' _) fun _ => KM.emit' _)

/-- **The blocks of step `7` under `mono` `&`** keep the counters' order,
`drop` and the tags. -/
theorem km_crdBlockMM (b : Bell) (subV : List Nat) (goal : CGoalL CSet) :
    KM (crdBlockMM b subV goal : CM (TreapMap mugF) (Nat × Nat × Nat)) := by
  cases goal with
  | done =>
    exact KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => KM.bind' (KM.emit' _) fun _ => KM.pure' _
  | next laz th =>
    exact KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf nex) fun r => by
      obtain ⟨out, pro⟩ := r
      exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ =>
        KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ =>
          KM.bind' (KM.emit' _) fun _ => KM.pure' _
  | pick z o =>
    exact KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf nex) fun r => by
      obtain ⟨out, pro⟩ := r
      exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ =>
        KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ =>
          KM.bind' (KM.emit' _) fun _ => KM.pure' _

/-- **`monoBlocks`** keeps the counters' order, `drop` and the tags. -/
theorem km_monoBlocks (b : Bell) (subNed : Need) (goal : CGoalL CSet) :
    KM (monoBlocks b subNed goal : CM (TreapMap mugF) (Nat × Nat)) := by
  rw [monoBlocks_eq]
  exact KM.bind' (km_crdBlockMM _ _ _) fun r => by
    obtain ⟨opt, s, pes⟩ := r
    exact KM.bind' (km_monoTryLoop _ _ _ _) fun _ => KM.pure' _

/-- **`sub-pes` is fresh** in the blocks of step `7`. -/
theorem crdBlockMM_sub {b : Bell} {subV : List Nat} {goal : CGoalL CSet} {g g' : Gen (TreapMap mugF)}
    {opt s pes : Nat} (h : crdBlockMM b subV goal g = some ((opt, s, pes), g')) : g.re ≤ s ∧ s < g'.re := by
  cases goal with
  | done =>
    simp only [crdBlockMM, bind_apply, re_apply, Option.bind_some, cf_emit_g, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl, -⟩, rfl⟩ := h
    simp [cf_emitG_re]
  | next laz th =>
    simp only [crdBlockMM] at h
    obtain ⟨nex, g1, e1, h⟩ := bind_some h
    obtain ⟨⟨out, pro⟩, g2, e2, h⟩ := bind_some h
    simp only [bind_apply, re_apply, Option.bind_some, cf_emit_g, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl, -⟩, rfl⟩ := h
    have k1 := (km_simpleNextL _).keep _ _ _ e1
    have k2 := (km_kerf _).keep _ _ _ e2
    simp only [cf_emitG_re]
    omega
  | pick z o =>
    simp only [crdBlockMM] at h
    obtain ⟨nex, g1, e1, h⟩ := bind_some h
    obtain ⟨⟨out, pro⟩, g2, e2, h⟩ := bind_some h
    simp only [bind_apply, re_apply, Option.bind_some, cf_emit_g, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl, -⟩, rfl⟩ := h
    have k1 := (km_simpleNextL _).keep _ _ _ e1
    have k2 := (km_kerf _).keep _ _ _ e2
    simp only [cf_emitG_re]
    omega

/-- **`sub-pes` is fresh** in `monoBlocks`. -/
theorem monoBlocks_sub {b : Bell} {subNed : Need} {goal : CGoalL CSet} {g g' : Gen (TreapMap mugF)} {s o : Nat}
    (h : monoBlocks b subNed goal g = some ((s, o), g')) : g.re ≤ s ∧ s < g'.re := by
  rw [monoBlocks_eq] at h
  obtain ⟨⟨opt, s', pes⟩, g1, e1, h⟩ := bind_some h
  obtain ⟨o', g2, e2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have k1 := crdBlockMM_sub e1
  have k2 := (km_monoTryLoop _ _ _ _).keep _ _ _ e2
  omega

/-! ## The goals of the two runs -/

/-- The goal of the call's blocks after `+need-ord-alloc-regs` meets `GInv`. -/
theorem ginv_noar {nb : NeedOrd} {goal : CGoalL CSet} {g g1 : Gen (TreapMap mugF)} {subNed : Need}
    (hinv : GInv g goal) (e : needOrdAllocRegs nb g = some (subNed, g1)) : GInv g1 goal := by
  obtain ⟨⟨k, hk⟩, hre, -, -⟩ := needOrdAllocRegs_spec nb g g1 subNed e
  exact ginv_mono hinv hre (by rw [hk]; exact Nat.le_refl _) (by rw [hk])

/-- **The goals of the call's two runs under `mono` `&`**, at the state after
`monoBlocks`: `q`'s `[%next *need-lazy ~ call-block]` meets `GInv`, `p`'s
need `(lazy-from-need [%this sub-pes])` meets `LInv`, the counters moved up,
and `sub-pes` is at or above the counter before the call. -/
theorem crd_goalsM {nb : NeedOrd} {b : Bell} {goal : CGoalL CSet} {g g1 g2 : Gen (TreapMap mugF)} {subNed : Need}
    {s o : Nat} (hinv : GInv g goal) (e : needOrdAllocRegs nb g = some (subNed, g1))
    (eb : monoBlocks b subNed goal g1 = some ((s, o), g2)) :
    GInv g2 (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) ∧
      LInv g2.re g2.bo (Lazy.ofSure (lazyReg s : Sure CSet)) ∧
      g.re ≤ g2.re ∧ g.bo ≤ g2.bo ∧ g.re ≤ s := by
  obtain ⟨⟨k, hk⟩, hre, -, -⟩ := needOrdAllocRegs_spec nb g g1 subNed e
  have hd0 : g.drop = false := ginv_drop hinv
  have hd1 : g1.drop = false := by rw [hk]; exact hd0
  have hb1 : g1.bo = g.bo := by rw [hk]
  obtain ⟨l2, b2, d2⟩ := km_drop (km_monoBlocks _ _ _) eb hd1
  obtain ⟨s1, s2⟩ := monoBlocks_sub eb
  exact ⟨ginv_bunt_j d2 (jmpIn_jmp0 _ _), linv_reg s2, by omega, by omega, by omega⟩

/-! ## The model of the case at `mono` `&` -/

/-- The case `%2` of `runLCM env true` on a direct call is `callDM`. -/
theorem runLCM_n2_direct (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (key : Option Noun)
    (goal : CGoalL CSet) (region : List Nat) :
    (runLCM env true msup (Nomm.n2 p q (some (b, key))) goal region : CM (TreapMap mugF) (NextL CSet))
      = callDM env (runLCM env true msup p) (runLCM env true msup q) p q b key goal region := by
  rw [runLCM]; rfl

/-- **The model of the case at `mono` `&`** on a direct call with no key, not
dropped, no ring, `env.need b = some nb`: `+need-ord-alloc-regs`, then
`crdCallMM` with the runs `runLCM env true msup`. -/
theorem crd_model_n2M (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (goal : CGoalL CSet) (region : List Nat) (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hpc : hinted env.cod p = hinted noCode p) :
    (runLCM env true msup (Nomm.n2 p q (some (b, Option.none))) goal region : CM (TreapMap mugF) (NextL CSet))
      = needOrdAllocRegs nb >>= fun subNed => crdCallMM (runLCM env true msup) p q b subNed goal region := by
  rw [runLCM_n2_direct]
  exact crd_model_callM env (runLCM env true msup) p q b nb goal region hdr hri hnb hpc

/-! ## The case `%2` at `mono` `A 0`, one instance -/

/-- **The case `%2` on a direct call under `mono` `&`** (README Gaps 19), one
instance (`RunAtR`) at `mono` `A 0` and `sup` the noun of `msup`, against
`runLCM env true msup`, from `cr2Dir`: a callee `b` with no memo key whose
code entry has `pure` `env.pure b` (`CodePure`), the call not dropped
(`crdDrop`), no ring, `env.need b = some nb`, the rest `x` of the state with
`NoSoft` and `CallNounM` (any value `SOF` of the push of `sof`, which `mono`
`&` does not read), every goal with `GInv`; the runs of `q` and `p` for the
goals of the call and the `CopyH` of their results (`hq`, `hp`, `hcp`). -/
theorem comp_run_n2_callMono (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpc : hinted env.cod p = hinted noCode p)
    (hpn : hinted noCode p ≠ Option.none) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd) (sur SOF : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : GInv g goal)
    (hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (x : GenRest) (hx : x.NoSoft) (hn : CallNounM msup ctx p q b nb sur x (A 0) SOF)
    (hq : ∀ subNed g1 s o g2, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      RunAtR (runLCM env true msup) ctx x (A 0) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g2)
    (hp : ∀ subNed g1 s o g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL noCode nexF p region g3 = some (nexF', g4) →
      RunAtR (runLCM env true msup) ctx x (A 0) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4)
    (hcp : ∀ subNed g1 s o g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL noCode nexF p region g3 = some (nexF', g4) →
      runLCM env true msup p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    RunAtR (runLCM env true msup) ctx x (A 0) (unitNoun Nomm.toNoun msup) (Nomm.n2 p q (some (b, Option.none)))
      goal region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  unfold RunAtR
  rw [crd_model_n2M env msup p q b nb goal region hdr hri hnb hpc, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id Option.none) V _ (A 0)
    goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) g x hgot hv
  have ht := crd_test_all h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id Option.none))))))
    (A 0) (listNoun A region) (unitNoun Nomm.toNoun msup) (env.pure b) goal g x
  rw [hdr] at ht
  have hcall := crd_callM h7 hcode (runLCM env true msup) msup p q hpn b nb sur SOF x hx hn (loob (env.pure b))
    goal region g (fun _ _ e => ginv_noar hinv e) hq hp hcp
  simp only [crdN] at hcall
  have hu : unitNoun (id : Noun → Noun) Option.none = A 0 := rfl
  rw [hu] at hpure ht ⊢
  have hl : loob false = A 1 := rfl
  rw [hl] at ht
  unfold crDHead
  simp [nock_exec, hpure, ht, hcall]

/-! ## The runs from the parts -/

/-- What a run of `n` against `R` returns, on every goal with the invariant. -/
def ResForR (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (n : Nomm)
    (region : List Nat) : Prop :=
  ∀ (goal : CGoalL CSet) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), GInv g goal →
    R n goal region g = some (nex, g') → GRes g goal g' nex

/-- **The run link at `mono` `&`** (`A 0`, the whole-subject versions of
`+compile-scc-in`) against `runLCM env true msup`, with the Hoon's `sup` the
noun of `msup`, for every rest `x` of the state with an empty `soft` that
meets `E`. -/
def CompRunAtMM (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (E : GenRest → Prop) (n : Nomm)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  ∀ x : GenRest, x.NoSoft → E x →
    RunAtR (runLCM env true msup) ctx x (A 0) (unitNoun Nomm.toNoun msup) n goal region g

/-- What the call under `mono` `&` takes of a part: the link at `mono` `A 0`
on every goal with the invariant, and what the run returns. -/
structure PartLM (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (E : GenRest → Prop) (n : Nomm)
    (region : List Nat) : Prop where
  link : ∀ (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal → CompRunAtMM env msup ctx E n goal region g
  res : ResForR (runLCM env true msup) n region

/-- What the first push of the tail returns, against `R`. -/
theorem crd_fq_resR {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)} {q : Nomm}
    {region : List Nat} (ihq : ResForR R q region) {th : Jmp} {g g2 : Gen (TreapMap mugF)} {nexF : NextL CSet}
    (hd : g.drop = false) (hj : JmpIn (· < g.re) th) (e : crdFqR R q th region g = some (nexF, g2)) :
    GRes g (CGoalL.next (Lazy.ofSure Sure.bunt) th) g2 nexF := by
  unfold crdFqR at e
  cases hs : safeFolFol q with
  | true =>
    simp only [hs, if_true, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact gres_bunt (Nat.le_refl _) (Nat.le_refl _) hd hj
  | false =>
    simp only [hs, Bool.false_eq_true, if_false] at e
    exact ihq _ _ _ _ (ginv_bunt_j hd hj) e

/-- **The runs of `p` and `q` of the call under `mono` `&` from `PartLM`**
(the hypotheses `hq`, `hp`, `hcp` of `comp_run_n2_callMono`), for a rest `x`
with `NoSoft` and `E`. -/
theorem crd_hpqM {E : GenRest → Prop} (env : CallEnv) (msup : Option Nomm) (p q : Nomm) {region : List Nat}
    (P : PartLM env msup ctx E p region) (Q : PartLM env msup ctx E q region) (b : Bell) (nb : NeedOrd)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (x : GenRest) (hx : x.NoSoft) (hE : E x) :
    (∀ subNed g1 s o g2, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      RunAtR (runLCM env true msup) ctx x (A 0) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g2) ∧
    (∀ subNed g1 s o g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL noCode nexF p region g3 = some (nexF', g4) →
      RunAtR (runLCM env true msup) ctx x (A 0) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4) ∧
    (∀ subNed g1 s o g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL noCode nexF p region g3 = some (nexF', g4) →
      runLCM env true msup p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) := by
  refine ⟨fun subNed g1 s o g2 e eb => Q.link _ g2 (crd_goalsM hinv e eb).1 x hx hE,
    fun subNed g1 s o g2 nexF g3 nexF' g4 e eb ef e3 => ?_,
    fun subNed g1 s o g2 nexF g3 nexF' g4 nexS g5 e eb ef e3 e4 => ?_⟩
  · obtain ⟨hq2, hp2, -⟩ := crd_goalsM hinv e eb
    exact P.link _ _ (tail_pgoal hq2 hp2 (crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef) e3).1 x hx hE
  · obtain ⟨hq2, hp2, -⟩ := crd_goalsM hinv e eb
    have R2 := crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef
    have ap : (lregs (Lazy.ofSure (lazyReg s : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
      rw [lregs_bunt, List.append_nil]; exact hp2.2.1
    exact (tail_copyH hq2 hp2 ap R2 e3 (P.res _ _ _ _ (tail_pgoal hq2 hp2 R2 e3).1 e4)).1

/-- **What the call under `mono` `&` returns** (`GRes`): a direct call with
no key, not dropped, no ring, `env.need b = some nb`, on every goal with
`GInv`.  A register of the result is one of the goal's or at or above the
counter (`sub-pes` and the fresh registers of the runs). -/
theorem res_n2_callMono {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCM env true msup) p region) (ihq : ResForR (runLCM env true msup) q region)
    (hpc : hinted env.cod p = hinted noCode p) {b : Bell} {nb : NeedOrd} {goal : CGoalL CSet}
    (hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    {g g' : Gen (TreapMap mugF)} {nex : NextL CSet} (hi : GInv g goal)
    (h : runLCM env true msup (Nomm.n2 p q (some (b, Option.none))) goal region g = some (nex, g')) :
    GRes g goal g' nex := by
  rw [crd_model_n2M env msup p q b nb goal region hdr hri hnb hpc] at h
  obtain ⟨subNed, g1, e, h⟩ := bind_some h
  unfold crdCallMM at h
  obtain ⟨⟨s, o⟩, g2, eb, h⟩ := bind_some h
  unfold crdTailMR at h
  obtain ⟨nexF, g3, ef, h⟩ := bind_some h
  obtain ⟨nexF', g4, e3, h⟩ := bind_some h
  obtain ⟨nexS, g5, e4, e5⟩ := bind_some h
  obtain ⟨hq2, hp2, l2, b2, hs⟩ := crd_goalsM hi e eb
  have R2 := crd_fq_resR ihq hq2.2.1 hq2.2.2 ef
  have P3 := tail_pgoal hq2 hp2 R2 e3
  have ap : (lregs (Lazy.ofSure (lazyReg s : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
    rw [lregs_bunt, List.append_nil]; exact hp2.2.1
  obtain ⟨l, bb, i, s'⟩ := tail_res hq2 hp2 ap R2 e3 (ihp _ _ _ _ P3.1 e4) e5
  refine ⟨Nat.le_trans l2 l, Nat.le_trans b2 bb, i, fun r hr => ?_⟩
  rcases s' r hr with e' | e'
  · rw [lregs_bunt, List.append_nil, lregs_reg, List.mem_singleton] at e'
    subst e'
    exact Or.inl hs
  · exact Or.inl (Nat.le_trans l2 e')

/-- **The case `%2` on a direct call under `mono` `&`, as `CompRunAtMM`**
(README Gaps 19): at `mono` `A 0` and `sup` the noun of `msup`, against
`runLCM env true msup`, for every rest `x` of the state with `NoSoft` and
`E`, on every goal with `GInv`; `p` and `q` as `PartLM` with the same `E`,
and `E` gives the call's `CallNounM` (for some `sur` and `SOF`).  The callee
`b` has no memo key, its code entry has `pure` `env.pure b` (`CodePure`),
the call is not dropped, no ring, `env.need b = some nb`; `hpc`, `hpn` are
what `hinted_plain` (or `hinted_nd`) gives of `p`. -/
theorem comp_run_n2_callMM {E : GenRest → Prop} (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : CallEnv) (msup : Option Nomm) (p q : Nomm) {region : List Nat}
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none)
    (P : PartLM env msup ctx E p region) (Q : PartLM env msup ctx E q region) (b : Bell) (hcd : CodePure cod env b)
    (nb : NeedOrd) (hE : ∀ x, E x → ∃ sur SOF, CallNounM msup ctx p q b nb sur x (A 0) SOF)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) :
    CompRunAtMM env msup ctx E (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  intro x hx hEx
  obtain ⟨sur, SOF, hn⟩ := hE x hEx
  obtain ⟨hq, hp, hcp⟩ := crd_hpqM env msup p q P Q b nb goal g hinv x hx hEx
  exact comp_run_n2_callMono h7 hcode env msup p q hpc hpn b hcd nb sur SOF goal region g hinv hdr hri hnb x hx hn
    hq hp hcp

/-! ## The dropped call against any run model

`crd_nf` and `crd_drop` (`CompRunDirect.lean`) with the runs of `p` and `q`
against any model `R`, at one rest `x`, `mono` and `sup` (the same proofs);
the model of the dropped call is the tail `crdTailMR` with `nex-arg`
`[*need-lazy then.goal]`. -/

/-- The first push of the dropped call against `R`. -/
theorem crd_nfR (h7 : slot? 7 ctx = some compK) (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (p q : Nomm) (region : List Nat) (x : GenRest) (mono I sup : Noun) (laz : Lazy CSet) (th : Jmp)
    (g : Gen (TreapMap mugF)) (hq : RunAtR R ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g) :
    nock (C (A 0) (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) (CGoalL.next laz th).toNoun
      (listNoun A region) sup (compCore g x ctx))) crDNf
      = (crdFqR R q th region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  have hq1 := hq
  unfold RunAtR at hq1
  rw [cgl_next_noun, cr_bunt_noun] at hq1
  rw [cgl_next_noun]
  unfold crDNf crdFqR
  simp only [crSubj, compCore] at hq1 ⊢
  generalize comp.door = Dr at hq1 ⊢
  cases hs : safeFolFol q with
  | true =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, cr_next_nounL, cr_bunt_noun]
  | false =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, cr_bat_dol, hq1]

/-- **The dropped call against `R`** after the test: `crd_nfR`, `+past`,
the run of `p` for `[%next *need-lazy then.nex-fol]`, `+copy`. -/
theorem crd_dropR (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm)
    (hpn : hinted noCode p ≠ Option.none) (region : List Nat) (x : GenRest) (mono I sup : Noun) (laz : Lazy CSet)
    (th : Jmp) (g : Gen (TreapMap mugF))
    (hq : RunAtR R ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ nexF g2 nexF' g3, crdFqR R q th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      RunAtR R ctx x mono sup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (C (A 0) (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) (CGoalL.next laz th).toNoun
      (listNoun A region) sup (compCore g x ctx))) crDDrop
      = (crdTailMR R p q ⟨Lazy.ofSure Sure.bunt, th⟩ region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hnf := crd_nfR h7 R p q region x mono I sup laz th g hq
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  unfold crdTailMR
  simp only []
  generalize hF : crdFqR R q th region = F at hnf hp hcp
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
      have hp1 := hp nexF g2 nexF' g3 eq e3
      unfold RunAtR at hp1
      rw [cgl_next_noun, cr_bunt_noun] at hp1
      simp only [crSubj, compCore] at hp1
      cases eq2 : R p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 with
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

/-- **The model of the dropped call at `mono` `&`**: a pure callee on a
`%next` goal whose need asks nothing, any memo key; the tail with
`[*need-lazy then.goal]`. -/
theorem crd_model_dropM (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (key : Option Noun)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (hpc : hinted env.cod p = hinted noCode p) :
    (runLCM env true msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region
        : CM (TreapMap mugF) (NextL CSet))
      = crdTailMR (runLCM env true msup) p q ⟨Lazy.ofSure Sure.bunt, th⟩ region := by
  rw [runLCM_n2_direct]
  simp only [callDM, hpu, hne, Bool.and_self, if_true, pastL_cod hpc]
  unfold crdTailMR crdFqR
  rfl

/-- **The case `%2` on a dropped call at `mono` `&`**, one instance
(`RunAtR`) at any `mono` and `sup` against `runLCM env true msup`: a callee
whose code entry is `pure` (`CodePure`, `hpu`), a `%next` goal whose need
asks nothing (`hne`), any memo key; the runs of `q` and `p` for
`[%next *need-lazy _]` and the `CopyH` of their results. -/
theorem comp_run_n2_dropMono (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpc : hinted env.cod p = hinted noCode p)
    (hpn : hinted noCode p ≠ Option.none) (b : Bell) (key : Option Noun) (hcd : CodePure cod env b)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (g : Gen (TreapMap mugF)) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (x : GenRest) (mono sup : Noun)
    (hq : RunAtR (runLCM env true msup) ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ nexF g2 nexF' g3, crdFqR (runLCM env true msup) q th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      RunAtR (runLCM env true msup) ctx x mono sup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR (runLCM env true msup) q th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      runLCM env true msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    RunAtR (runLCM env true msup) ctx x mono sup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  unfold RunAtR
  rw [crd_model_dropM env msup p q b key laz th region hpu hne hpc, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id key) V _ mono
    (CGoalL.next laz th).toNoun (listNoun A region) sup g x hgot hv
  rw [hpu] at hpure
  have ht := crd_test h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id key)))))) mono
    (listNoun A region) sup laz th g x
  rw [hne] at ht
  have hdr := crd_dropR h7 hcode (runLCM env true msup) p q hpn region x mono
    (C (A 0) (C b.toNoun (unitNoun id key))) sup laz th g hq hp hcp
  unfold crDHead
  simp [nock_exec, hpure, ht, loob, hdr]

/-- **What the dropped call at `mono` `&` returns** (`GRes`). -/
theorem res_n2_dropMono {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCM env true msup) p region) (ihq : ResForR (runLCM env true msup) q region)
    (hpc : hinted env.cod p = hinted noCode p) {b : Bell} {key : Option Noun} {laz : Lazy CSet} {th : Jmp}
    (hpu : env.pure b = true) (hne : Lazy.noneEquivalentL laz = true) {g g' : Gen (TreapMap mugF)}
    {nex : NextL CSet} (hi : GInv g (CGoalL.next laz th))
    (h : runLCM env true msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  have hd : g.drop = false := hi.2.1
  have hj : JmpIn (· < g.re) th := hi.2.2
  rw [crd_model_dropM env msup p q b key laz th region hpu hne hpc] at h
  unfold crdTailMR at h
  obtain ⟨n2, g2, e1, h⟩ := bind_some h
  obtain ⟨n2', g3, e2, h⟩ := bind_some h
  obtain ⟨n1, g4, e3, e4⟩ := bind_some h
  have R2 := crd_fq_resR ihq hd hj e1
  have P3 := tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e2
  obtain ⟨l, bb, i, s⟩ := tail_res (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e2
    (ihp _ _ _ _ P3.1 e3) e4
  refine ⟨l, bb, i, fun r hr => ?_⟩
  rcases s r hr with e | e
  · simp [lregs_bunt] at e
  · exact Or.inl e

/-! ## The case `%2` on a direct call with no memo key at `mono` `&` -/

/-- **The case `%2` on a direct call with no memo key under `mono` `&`, as
`CompRunAtMM`** (README Gaps 19): dropped (`comp_run_n2_dropMono`) or not
(`comp_run_n2_callMono`), on every goal with `GInv`, against `runLCM env
true msup` at `mono` `A 0` and `sup` the noun of `msup`, for every rest `x`
with `NoSoft` and `E`; `p` and `q` as `PartLM` with the same `E`, and `E`
gives the call's `CallNounM`.  No ring and `env.need b = some nb` (read only
when the call is not dropped). -/
theorem comp_run_n2_directMM {E : GenRest → Prop} (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : CallEnv) (msup : Option Nomm) (p q : Nomm) {region : List Nat}
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none)
    (P : PartLM env msup ctx E p region) (Q : PartLM env msup ctx E q region) (b : Bell) (hcd : CodePure cod env b)
    (nb : NeedOrd) (hE : ∀ x, E x → ∃ sur SOF, CallNounM msup ctx p q b nb sur x (A 0) SOF)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtMM env msup ctx E (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  cases hdr : crdDrop (env.pure b) goal with
  | false => exact comp_run_n2_callMM h7 hcode env msup p q hpc hpn P Q b hcd nb hE goal g hinv hdr hri hnb
  | true =>
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      obtain ⟨hpu, hne⟩ := hdr
      have hd : g.drop = false := hinv.2.1
      have hj : JmpIn (· < g.re) th := hinv.2.2
      intro x hx hEx
      exact comp_run_n2_dropMono h7 hcode env msup p q hpc hpn b Option.none hcd laz th region g hpu hne x _ _
        (Q.link _ g (ginv_bunt_j hd hj) x hx hEx)
        (fun nexF g2 nexF' g3 e e3 =>
          P.link _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) (crd_fq_resR Q.res hd hj e) e3).1 x hx hEx)
        (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => by
          have R2 := crd_fq_resR Q.res hd hj e
          exact (tail_copyH (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e3
            (P.res _ _ _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e3).1 e4)).1)

/-- **What the case `%2` on a direct call with no memo key under `mono` `&`
returns** (`GRes`), dropped or not, on every goal with `GInv`. -/
theorem res_n2_directMono {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCM env true msup) p region) (ihq : ResForR (runLCM env true msup) q region)
    (hpc : hinted env.cod p = hinted noCode p) {b : Bell} {nb : NeedOrd} (hri : env.ring b = Option.none)
    (hnb : env.need b = some nb) :
    ResForR (runLCM env true msup) (Nomm.n2 p q (some (b, Option.none))) region := by
  intro goal g g' nex hi h
  cases hdr : crdDrop (env.pure b) goal with
  | false => exact res_n2_callMono ihp ihq hpc hdr hri hnb hi h
  | true =>
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      exact res_n2_dropMono ihp ihq hpc hdr.1 hdr.2 hi h

end Compiler
end Formalization
