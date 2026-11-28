import lemmas.Compiler.CompUnaryDirE
import lemmas.Compiler.CompRunTGClass
import lemmas.Compiler.CompRingNeedStep

/-!
# The gate of `+compile-unary` through rings, against `finishLUCMR` (track K, README Gaps 19 (h))

`cu_gate_dirT`, `cu_gate_dirExt`, `cu_gate_dirE`, `cu_gate_dirE_csi` (`CompUnaryDirT.lean`,
`CompUnaryDirE.lean`) link `+compile-unary` to `finishLUCM env n` on a nomm whose direct callees
have no `call.cole` entry (`CodeNoRing`).  Here a callee may have a ring with no hot driver,
and the gate is `finishLUCMR env n` (`Ska/CompRingRunEq.lean`), through the run link
`comp_run_dirXTG` (`CompRunTGClass.lean`):

* `cu_trap_dirTG`, `cu_gate_dirTG`, `cu_gate_dirExtG`: the copies on `DirCallsTG`.
* `SofRetG`, `sof_pushG`, `SofAllG`, `sofAllG_of_arms`: the push of `sof` on the subject with
  `rin` the noun `RIN` (`sof` does not read `rin`; the proofs are the old ones).
* **`callOkTG_of_E`**: `CallOkTG` of one call from `CallAt`, the code entry, `RinOk` and
  `RinAt` of `env.ring b` (in place of "no ring"), the push of `sof`; by `callNounMTG_of`.
* `RingAtG COLE JH b`: the entry of `b` in `call.cole` is the unit `ringOf COLE b`, a ring is
  a `RingNoun` with no `jets-hot` entry (P: `reach_ringVals`, `reach_hotEmpty`); `ringAtG_none`
  (a `~` entry); `BellEG`, `bellEG_of_E` (the old `BellE` is the case `~`), `envOf_ring`.
* **`dirCallsTG_of_E`**, **`cu_gate_dirEG`**, **`cu_gate_dirE_csiG`**: the gate with the
  per-call facts down to the cache, against `finishLUCMR env n`, rings included.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## The trap and the gate on `DirCallsTG` -/

/-- **The trap of `+compile-unary` on `DirOk` through rings, threaded** (`cu_trap_dirT`). -/
theorem cu_trap_dirTG (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y) (hE0 : E (cuRest CA))
    (hd : DirCallsTG env CODE (cuCtx FUNC SCC CODE LSR JH NM) E Y Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    ∃ x', Y (cuRest CA) x' ∧ nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = (finishLUCMR (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) x'.cache := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have hcode : slot? 52 (cuCtx FUNC SCC CODE LSR JH NM) = some CODE := by simp [cuCtx, nock_exec]
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill _ h7
  obtain ⟨x', hy, hrun⟩ := comp_run_dirXTG h7 hcode env E Y hY n hn Option.none [] hd (CGoal.toL CGoal.done) genEntry
    (show genEntry.drop = false from rfl) (cuRest CA) (A 0) (unitNoun Nomm.toNoun Option.none) (cu_entry_nosoft CA)
    ⟨hE0, rfl, rfl⟩
  have hx' : x'.NoSoft := (hY Option.none).soft (cu_entry_nosoft CA) hy
  refine ⟨x', hy, ?_⟩
  simp only [unitNoun] at hrun
  have hres := res_dirTG h7 hcode env E Y hY n hn Option.none [] hd
  rw [cu_trap_entry FUNC SCC CODE LSR JH CACHE NM CA hcsi,
    cu_trap_run FUNC SCC CODE LSR JH CACHE NM CA V n hgot hv, hrun]
  have hf : finishLUCMR (S := CSet) (Map := TreapMap mugF) env n
      = ((runLCMR env true Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind
          fun p => kerf p.1 p.2).bind
          fun q => toStraightF q.2.cond q.2.blocks (Need.this q.1.2) q.1.1 := by
    rw [Option.bind_assoc]; rfl
  rw [hf]
  cases e : runLCMR (S := CSet) (Map := TreapMap mugF) env true Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) []
      genEntry with
  | none => simp
  | some p =>
    obtain ⟨nex, g1⟩ := p
    obtain ⟨-, -, hG, -⟩ := hres CGoalL.done genEntry g1 nex rfl e
    simp only [NextL.goal, GInv] at hG
    have hlok : LAll CrLok nex.laz := lall_mono (fun s h => h.1) hG.1.1
    have hk := comp_kerf_all hc hl hm x' g1 nex (walk_mdP hx' g1.bo hlok)
    simp only [compCore] at hk
    simp only [Option.bind_some, Option.map_some, NextL.goal, CGoalL.toNoun]
    rw [cu_trap_kerf, hk]
    cases e2 : kerf nex g1 with
    | none => simp
    | some q =>
      obtain ⟨⟨o, sub⟩, g2⟩ := q
      have h : nock (C tsBat (C (tsSampleN (A o) (C (A 0x73696874) (A sub)))
            (C comp.door (C (genNoun g2 x') (cuCtx FUNC SCC CODE LSR JH NM))))) tsBat
          = (toStraightF g2.cond g2.blocks (Need.this sub) o).map Straight.toNoun :=
        ts_at_all h7 g2 x' o (Need.this sub) (by simp [flattenNeed, isRun])
      simp only [Option.map_some, Option.bind_some]
      unfold cuS4
      rw [cu_trap_end, tsSample_eq, h, cu_gen_cache]
      cases toStraightF g2.cond g2.blocks (Need.this sub) o <;> rfl

/-- **The gate of `+compile-unary` on `DirOk` through rings, threaded** (`cu_gate_dirT`). -/
theorem cu_gate_dirTG (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y) (hE0 : E (cuRest CA))
    (hd : DirCallsTG env CODE (cuCtx FUNC SCC CODE LSR JH NM) E Y Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    ∃ x', Y (cuRest CA) x' ∧ nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCMR (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) x'.cache := by
  obtain ⟨x', hy, ht⟩ := cu_trap_dirTG FUNC SCC CODE LSR JH CACHE NM CA V env n hn E Y hY hE0 hd hcsi hgot hv
  refine ⟨x', hy, ?_⟩
  rw [cu_gate_rp, ← ht]
  apply Option.ext
  intro y
  rw [cu_rp_iff]
  have hk : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) rpK
      = nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap := by
    unfold cuTC
    simp [rpK, nock_exec]
  rw [hk]

/-- **The gate through rings with the final cache** (`cu_gate_dirExt`). -/
theorem cu_gate_dirExtG (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (E : GenRest → Prop) (hE0 : E (cuRest CA))
    (hd : DirCallsTG env CODE (cuCtx FUNC SCC CODE LSR JH NM) E (ExtE E) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ E (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
        = (finishLUCMR (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  obtain ⟨x', ⟨he, hEE⟩, h⟩ :=
    cu_gate_dirTG FUNC SCC CODE LSR JH CACHE NM CA V env n hn E (ExtE E) (yOk_extE E) hE0 hd hcsi hgot hv
  have hx := ext_cuRest he
  refine ⟨x'.cache, hx ▸ he, hx ▸ hEE hE0, h⟩

/-! ## The push of `sof` with `rin` any noun -/

section
variable {ctx : Noun}

/-- `SofRet` on the subject with `rin` the noun `RIN`. -/
def SofRetG (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (x : GenRest) (RIN : Noun) : Prop :=
  ∃ SOF, ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C RIN (C PV (crSubj (A 0) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some SOF

/-- **`sof_push` with `rin` any noun** (the push never reads `rin`). -/
theorem sof_pushG (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd) (x : GenRest) (RIN : Noun)
    (hcp : CallCode cod env p) (hcq : CallCode cod env q)
    (hsf : SoundFarRet (made p msup) nb cod) (hns : NeedSoftRet nb (env.sure b) b.less) :
    SofRetG env msup ctx p q b nb x RIN := by
  obtain ⟨s, hs⟩ := hsf
  obtain ⟨t, ht⟩ := hns
  obtain ⟨hp, ehp⟩ := hinted_code p hcp
  obtain ⟨hq, ehq⟩ := hinted_code q hcq
  have hdp := hd_gateR cod env p hp hcp ehp
  have hdq := hd_gateR cod env q hq hcq ehq
  have hK := compK_hd
  have hN := compK_ns
  have hM := comp_made_at
  have hS := comp_sound_at
  refine ⟨loob (!s && (t || hp || hq)), fun g SV SN PV goalN regionN => ?_⟩
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

/-- `SofAll` with the push of `sof` on the subject with the callee's ring. -/
def SofAllG (env : CallEnv) (ctx : Noun) (x : GenRest) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => SofAllG env ctx x ms p ∧ SofAllG env ctx x ms q
  | ms, Nomm.n2 p q Option.none => SofAllG env ctx x ms p ∧ SofAllG env ctx x ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      (∀ nb, env.need b = some nb → SofRetG env ms ctx p q b nb x (unitNoun id (env.ring b))) ∧
        SofAllG env ctx x ms p ∧ SofAllG env ctx x ms q
  | ms, Nomm.n3 p => SofAllG env ctx x ms p
  | ms, Nomm.n4 p => SofAllG env ctx x ms p
  | ms, Nomm.n5 p q => SofAllG env ctx x ms p ∧ SofAllG env ctx x ms q
  | ms, Nomm.n6 p q r => SofAllG env ctx x ms p ∧ SofAllG env ctx x ms q ∧ SofAllG env ctx x ms r
  | ms, Nomm.n7 p q => SofAllG env ctx x ms p ∧ SofAllG env ctx x (some p) q
  | ms, Nomm.n10 _ v q => SofAllG env ctx x ms v ∧ SofAllG env ctx x ms q
  | _, _ => True

/-- **`sofAll_of_arms` with the ring in the subject.** -/
theorem sofAllG_of_arms (h7 : slot? 7 ctx = some compK) {CODE COLE : Noun} (hcode : slot? 52 ctx = some CODE)
    {env : CallEnv} (he : EnvFrom env CODE COLE) (x : GenRest) :
    ∀ (ms : Option Nomm) (n : Nomm), DirOk n = true → (∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c) →
      SofArms env CODE ms n → SofAllG env ctx x ms n
  | ms, Nomm.cons p q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAllG_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAllG_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | _, Nomm.n0 _, _, _, _ => trivial
  | _, Nomm.n1 _, _, _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAllG_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAllG_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | ms, Nomm.n2 p q (some (b0, Option.none)), h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_cons, List.mem_append] at hb
    have hbp : ∀ b ∈ dirBells p, ∃ c, codeOf CODE b = some c := fun b m => hb b (Or.inr (Or.inl m))
    have hbq : ∀ b ∈ dirBells q, ∃ c, codeOf CODE b = some c := fun b m => hb b (Or.inr (Or.inr m))
    exact ⟨fun nb hnb => sof_pushG h7 hcode env ms p q b0 nb x _ (callCode_of_bells he p h.1 hbp)
        (callCode_of_bells he q h.2 hbq) (hs.1 nb hnb).1 (hs.1 nb hnb).2,
      sofAllG_of_arms h7 hcode he x ms p h.1 hbp hs.2.1, sofAllG_of_arms h7 hcode he x ms q h.2 hbq hs.2.2⟩
  | _, Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [DirOk] at h
  | ms, Nomm.n3 p, h, hb, hs => by simp only [DirOk] at h; exact sofAllG_of_arms h7 hcode he x ms p h hb hs
  | ms, Nomm.n4 p, h, hb, hs => by simp only [DirOk] at h; exact sofAllG_of_arms h7 hcode he x ms p h hb hs
  | ms, Nomm.n5 p q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAllG_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAllG_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | ms, Nomm.n6 p q r, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAllG_of_arms h7 hcode he x ms p h.1.1 (fun b m => hb b (Or.inl (Or.inl m))) hs.1,
      sofAllG_of_arms h7 hcode he x ms q h.1.2 (fun b m => hb b (Or.inl (Or.inr m))) hs.2.1,
      sofAllG_of_arms h7 hcode he x ms r h.2 (fun b m => hb b (Or.inr m)) hs.2.2⟩
  | ms, Nomm.n7 p q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAllG_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAllG_of_arms h7 hcode he x (some p) q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | ms, Nomm.n10 _ v q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAllG_of_arms h7 hcode he x ms v h.1.2 (fun b m => hb b (Or.inl m)) hs.1,
      sofAllG_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | _, Nomm.n11s _ _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.n11d _ _ _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.n12 _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.mean _ _ _ _ _, h, _, _ => by simp [DirOk] at h

/-! ## One call through a ring, discharged from the cache -/

/-- **`CallOkTG` of one call, discharged** at `E = EnvE env x0` and `Y = ExtE E`: the code
entry, `RinOk` and `RinAt` of the callee's ring (no ring, or a ring with no hot driver), the need
`nb`, `CallAt`, and the push of `sof` at every rest. -/
theorem callOkTG_of_E (h7 : slot? 7 ctx = some compK) {env : CallEnv} {cod : Noun} {x0 : GenRest}
    {R : GenRest → Prop} {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd}
    (hcd : CodePure cod env b) (hc : env.cod b = some (env.pure b)) (hro : RinOk (env.ring b))
    (hnb : env.need b = some nb) (hra : RinAt ctx b (env.ring b))
    (hsof : ∀ x, SofRetG env msup ctx p q b nb x (unitNoun id (env.ring b)))
    (hca : CallAt env R ctx x0 b nb) :
    CallOkTG env cod ctx (EnvE env R x0) (ExtE (EnvE env R x0)) msup p q b := by
  refine ⟨hcd, hc, hro, nb, hnb, fun x _ hE => ?_⟩
  rcases hca with ⟨hr, hs⟩ | ⟨S, hS, hin, hcc⟩
  · obtain ⟨SOF, hso⟩ := hsof x
    exact ⟨x, _, SOF, ⟨ext_refl x, id⟩, callNounMTG_of h7 hra (NeedStep.read (needRead_ext hr hE.2.1))
      (sureNoun_ext hs hE.2.1 hE.1) hso⟩
  · obtain ⟨_, NR, MO, SC, INL, SU, hcx, hnm, -⟩ := hE.1
    have hNR : slot? 2 x.cache = some NR := by rw [hcx]; simp [cacheN, nock_exec]
    rcases getF_cases (k := b.toNoun) hnm with h0 | ⟨u, hu⟩
    · obtain ⟨CA', hmiss, hext, hA', hR', N', u', hN', hu'⟩ := hcc x NR MO SC (C INL SU) hE.1 hE.2.2 hcx h0
      obtain ⟨-, hs'⟩ := hit_of_agree hS hin hnb hA' hN' hu'
      obtain ⟨SOF, hso⟩ := hsof ⟨CA', x.soft, x.sofs⟩
      exact ⟨_, _, SOF, agreeE_ext hext hA' hR',
        callNounMTG_of h7 hra (NeedStep.miss hS hin hcx h0 hmiss) hs' hso⟩
    · obtain ⟨hr, hs⟩ := hit_of_agree hS hin hnb hE.1 hNR hu
      obtain ⟨SOF, hso⟩ := hsof x
      exact ⟨x, _, SOF, ⟨ext_refl x, id⟩, callNounMTG_of h7 hra (NeedStep.read hr) hs hso⟩

end

/-! ## The callees' facts through rings -/

/-- **The ring facts of a callee**: its `call.cole` entry (in `COLE`) is the unit `ringOf COLE b`
(P: every value of `call.cole` is a ring, `reach_ringVals`), a ring is a `RingNoun`, and a ring
has no entry in `jets-hot` (`JH`; P: `reach_hotEmpty`). -/
def RingAtG (COLE JH : Noun) (b : Bell) : Prop :=
  getF mugF b.toNoun COLE = some (unitNoun id (ringOf COLE b)) ∧ RinOk (ringOf COLE b) ∧
    ∀ u, ringOf COLE b = some u → getF mugF u JH = some (A 0)

/-- A `~` entry has the ring facts. -/
theorem ringAtG_none {COLE JH : Noun} {b : Bell} (h : getF mugF b.toNoun COLE = some (A 0)) : RingAtG COLE JH b := by
  have hr : ringOf COLE b = Option.none := by simp [ringOf, h]
  refine ⟨by rw [hr, h]; rfl, by rw [hr]; trivial, fun u hu => by rw [hr] at hu; cases hu⟩

/-- `RinAt` of the callee's ring from its ring facts. -/
theorem rinAt_of_ringAtG {ctx COLE JH : Noun} {b : Bell} (hcl : slot? 6846 ctx = some COLE)
    (hjh : slot? 54 ctx = some JH) (h : RingAtG COLE JH b) : RinAt ctx b (ringOf COLE b) :=
  ⟨COLE, JH, hcl, hjh, h.1, h.2.2⟩

/-- The environment of the samples reads its rings from `call.cole`. -/
theorem envOf_ring (CODE COLE : Noun) (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
    (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool) (b : Bell) :
    (envOf CODE COLE need sure sof).ring b = ringOf COLE b := rfl

/-- What a callee of `n` takes in the gate through rings: a code entry, the ring facts, its need,
and `CallAt` at the start. -/
def BellEG (env : CallEnv) (R : GenRest → Prop) (CODE COLE JH ctx : Noun) (x0 : GenRest) (b : Bell) : Prop :=
  (∃ c, codeOf CODE b = some c) ∧ RingAtG COLE JH b ∧ ∃ nb, env.need b = some nb ∧ CallAt env R ctx x0 b nb

/-- **The old `BellE` (no ring) is `BellEG`.** -/
theorem bellEG_of_E {env : CallEnv} {R : GenRest → Prop} {CODE COLE JH ctx : Noun} {x0 : GenRest} {b : Bell}
    (h : BellE env R CODE COLE ctx x0 b) : BellEG env R CODE COLE JH ctx x0 b :=
  ⟨h.1, ringAtG_none h.2.1, h.2.2⟩

/-- **`DirCallsTG` at `EnvE` from the callees' facts through rings** and the push of `sof` at
every rest (`dirCallsT_of_E`). -/
theorem dirCallsTG_of_E {ctx : Noun} (h7 : slot? 7 ctx = some compK) {env : CallEnv} {CODE COLE JH : Noun}
    (he : EnvFrom env CODE COLE) (hring : ∀ b, env.ring b = ringOf COLE b) (hcl : slot? 6846 ctx = some COLE)
    (hjh : slot? 54 ctx = some JH) {R : GenRest → Prop} {x0 : GenRest} : ∀ (ms : Option Nomm) (n : Nomm),
      (∀ b ∈ dirBells n, BellEG env R CODE COLE JH ctx x0 b) →
      (∀ x, SofAllG env ctx x ms n) → DirCallsTG env CODE ctx (EnvE env R x0) (ExtE (EnvE env R x0)) ms n
  | ms, Nomm.cons p q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAllG] at hs
    exact ⟨dirCallsTG_of_E h7 he hring hcl hjh ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsTG_of_E h7 he hring hcl hjh ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | _, Nomm.n0 _, _, _ => trivial
  | _, Nomm.n1 _, _, _ => trivial
  | ms, Nomm.n2 p q Option.none, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAllG] at hs
    exact ⟨dirCallsTG_of_E h7 he hring hcl hjh ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsTG_of_E h7 he hring hcl hjh ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | ms, Nomm.n2 p q (some (b0, k)), hb, hs => by
    simp only [dirBells, List.mem_cons, List.mem_append] at hb; simp only [SofAllG] at hs
    obtain ⟨⟨c, hc⟩, hrg, nb, hnb, hca⟩ := hb b0 (Or.inl rfl)
    obtain ⟨hcd, hcod⟩ := codePure_of he hc
    have hra := rinAt_of_ringAtG hcl hjh hrg
    rw [← hring b0] at hra
    have hro : RinOk (env.ring b0) := by rw [hring b0]; exact hrg.2.1
    exact ⟨callOkTG_of_E h7 hcd hcod hro hnb hra (fun x => (hs x).1 nb hnb) hca,
      dirCallsTG_of_E h7 he hring hcl hjh ms p (fun b h => hb b (Or.inr (Or.inl h))) fun x => (hs x).2.1,
      dirCallsTG_of_E h7 he hring hcl hjh ms q (fun b h => hb b (Or.inr (Or.inr h))) fun x => (hs x).2.2⟩
  | ms, Nomm.n3 p, hb, hs => dirCallsTG_of_E h7 he hring hcl hjh ms p hb hs
  | ms, Nomm.n4 p, hb, hs => dirCallsTG_of_E h7 he hring hcl hjh ms p hb hs
  | ms, Nomm.n5 p q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAllG] at hs
    exact ⟨dirCallsTG_of_E h7 he hring hcl hjh ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsTG_of_E h7 he hring hcl hjh ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | ms, Nomm.n6 p q r, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAllG] at hs
    exact ⟨dirCallsTG_of_E h7 he hring hcl hjh ms p (fun b h => hb b (Or.inl (Or.inl h))) fun x => (hs x).1,
      dirCallsTG_of_E h7 he hring hcl hjh ms q (fun b h => hb b (Or.inl (Or.inr h))) fun x => (hs x).2.1,
      dirCallsTG_of_E h7 he hring hcl hjh ms r (fun b h => hb b (Or.inr h)) fun x => (hs x).2.2⟩
  | ms, Nomm.n7 p q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAllG] at hs
    exact ⟨dirCallsTG_of_E h7 he hring hcl hjh ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsTG_of_E h7 he hring hcl hjh (some p) q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | ms, Nomm.n10 _ v q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAllG] at hs
    exact ⟨dirCallsTG_of_E h7 he hring hcl hjh ms v (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsTG_of_E h7 he hring hcl hjh ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | _, Nomm.n11s _ _ _, _, _ => trivial
  | _, Nomm.n11d _ _ _ _, _, _ => trivial
  | _, Nomm.n12 _ _, _, _ => trivial
  | _, Nomm.mean _ _ _ _ _, _, _ => trivial

/-! ## The gate through rings -/

/-- **The gate of `+compile-unary` on `DirOk` through rings, the per-call facts discharged from
the cache** (`cu_gate_dirE` with `finishLUCMR`).  In place of `CodeNoRing`: every direct callee
has a code entry (`hck`) and the ring facts (`hrg`: its entry is `~` or a ring with no hot
driver), and the environment reads its rings from `call.cole` (`hring`; `envOf_ring`). -/
theorem cu_gate_dirEG (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (R : GenRest → Prop) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : R (cuRest CA))
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hring : ∀ b, env.ring b = ringOf COLE b)
    (hck : ∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c) (hrg : ∀ b ∈ dirBells n, RingAtG COLE JH b)
    (hana : CodeAna CODE)
    (hcall : ∀ b ∈ dirBells n, ∃ nb, env.need b = some nb ∧
      CallAt env R (cuCtx FUNC SCC CODE LSR JH NM) (cuRest CA) b nb) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ R (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
        = (finishLUCMR (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have harm : SofArms env CODE Option.none n :=
    sofArms_code (sfTable_code hana) Option.none n hn (fun b mem => by
      obtain ⟨c, hc⟩ := hck b mem
      obtain ⟨V', hg⟩ := entry_of_codeOf hc
      exact sofBell_code hana hg) (fun _ e => by cases e)
  have hsof : ∀ x, SofAllG env (cuCtx FUNC SCC CODE LSR JH NM) x Option.none n := fun x =>
    sofAllG_of_arms rfl (by simp [cuCtx, nock_exec]) he x Option.none n hn hck harm
  have hd := dirCallsTG_of_E h7 he hring (cuCtx_cole hcl) (cuCtx_hot FUNC SCC CODE LSR JH NM) Option.none n
    (fun b hb => by
      obtain ⟨nb, hnb, hca⟩ := hcall b hb
      exact ⟨hck b hb, hrg b hb, nb, hnb, hca⟩) hsof
  obtain ⟨CA', hx, hE, h⟩ := cu_gate_dirExtG FUNC SCC CODE LSR JH CACHE NM CA V env n hn (EnvE env R (cuRest CA))
    ⟨hE0, ext_refl _, hR0⟩ hd hcsi hgot hv
  exact ⟨CA', hx, hE.1, hE.2.2, h⟩

/-- **The gate through rings with every callee readable at the start** (`cu_gate_dirE_csi`:
`CsiNeeds`, `CsiSures`). -/
theorem cu_gate_dirE_csiG (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hring : ∀ b, env.ring b = ringOf COLE b)
    (hck : ∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c) (hrg : ∀ b ∈ dirBells n, RingAtG COLE JH b)
    (hana : CodeAna CODE)
    (hneed : CsiNeeds env SCC NM CA n) (hsure : CsiSures env CA n) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
        = (finishLUCMR (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  obtain ⟨CA', hx, hA, -, h⟩ := cu_gate_dirEG FUNC SCC CODE LSR JH CACHE NM CA V COLE env (fun _ => True) n hgot hv
    hcl hcsi hE0 trivial hn he hring hck hrg hana fun b hb => by
    obtain ⟨nb, hnb, hs⟩ := hneed b hb
    exact ⟨nb, hnb, callAt_of_scc hs (hsure b hb)⟩
  exact ⟨CA', hx, hA, h⟩

/-- **The old hypotheses feed the gate through rings**: `CodeNoRing` gives the code entries and
the ring facts (every entry `~`). -/
theorem ringAtG_of_noRing {CODE COLE JH : Noun} {n : Nomm} (hcr : CodeNoRing CODE COLE n) :
    (∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c) ∧ ∀ b ∈ dirBells n, RingAtG COLE JH b :=
  ⟨fun b hb => (hcr b hb).1, fun b hb => ringAtG_none (hcr b hb).2⟩

end Compiler
end Formalization
