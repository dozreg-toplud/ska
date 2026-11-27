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

end Compiler
end Formalization
