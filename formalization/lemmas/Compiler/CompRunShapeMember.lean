import lemmas.Compiler.CompRunShapeAll
import lemmas.Compiler.CompRunShapeColl
import lemmas.Compiler.CompRunShapeMay
import lemmas.Compiler.CompRunShapeBno
import lemmas.Compiler.CompShapeColSur
import lemmas.Compiler.CompRunAll
import lemmas.Ska.SccLoopReal

/-!
# The branch of the sweeps of `member` (`%must`, `%may`) in the pill (track A, 2026-11-28)

Off `%done` the gate `member` runs `memShape` (`CompSccLoopMemShape.lean`, `memShape_cut`):

    =^  l=laze  gen  (~(run-shape comp gen) nomm [%done ~] ~)
    =/  collapsed  ?:(?=(%must mode) (laze-collapse l cape.less.b) (laze-may l cape.less.b))
    [(bake-need-ord collapsed less.b) *need-lazy *need *baked 0 (sure-of sure.l cape.less.b)]

**`memShape_branchA`** links it: the run is `rs_doneE` (on nomms of `RsTailE`, at the one rest
`memY CA1` of the bunt `gen` with the cache `CA1`), `collapsed` is `lco_call` (`%must`) or
`lmy_call` (`%may`), the shape `bno_call`, `sur` `so_gate`.  The statement is track I's
`MemShapeBranch` (`CompSccLoopSweepBase.lean` of the integration branch, not on this base): its
definitions are restated here word for word with the suffix `A`, with `ShapeX` given as its two
fields `jet` and `cod` (`shapeEnvOfA jet xcod env` is `shapeEnvOf ⟨jet, xcod⟩ env`).  At the merge:
`MemShapeBranch x .. ↔ MemShapeBranchA x.jet x.cod ..` should hold by `Iff.rfl`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Track I's statement, restated (`CompSccLoopSweepBase.lean`, `Ska/SccLoopShape.lean`) -/

/-- `memS0X`: the subject after the push of `done` (`DN`), for the mode `MODE`. -/
def memS0XA (DN MODE B KEEP ML TOP CACHE CTX : Noun) : Noun :=
  C DN (C memBody (C (memSam B MODE KEEP ML TOP CACHE) CTX))

/-- `modeN`: the noun of a sweep's mode. -/
def modeNA : Mode → Noun
  | Mode.must => A 0x7473756d
  | Mode.may => A 0x79616d
  | Mode.done => A 0x656e6f64

/-- `shapeResN`: `[shape *need-lazy *need *baked 0 sur]`. -/
def shapeResNA (SH SUR : Noun) : Noun :=
  C SH (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))
    (C (C (A 0x656e6f6e) (A 0)) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) SUR))))

/-- `memShapeSubj`: the subject at the branch. -/
def memShapeSubjA (MODE : Noun) (keep : Bool) (NM SCC LONG JH ML TOP B CA1 CTX : Noun) : Noun :=
  C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA1))
    (memS3 NM (memDCtx SCC LONG JH ML TOP B) (memS0XA (A 1) MODE B (loob keep) ML TOP CA1 CTX))

/-- `shapeEnvOf ⟨jet, xcod⟩ env`. -/
def shapeEnvOfA (jet : Bell → Bool) (xcod : Bell → Option Nomm) (env : CallEnv) : ShapeEnv :=
  ⟨env.need, env.sure, jet, env.cod, xcod⟩

/-- `collapseOf`. -/
noncomputable def collapseOfA (mode : Mode) (fuel : Nat) (l : Laze CSet) (cape : Cape) : Option NeedOrd :=
  match mode with
  | Mode.must => lazeCollapse fuel l cape
  | _ => lazeMay l cape

/-- `lazeReal ⟨jet, xcod⟩` (`lazeRealG` over `CSet` from `rsSt0`). -/
noncomputable def lazeRealA (jet : Bell → Bool) (xcod : Bell → Option Nomm) (mode : Mode) (env : CallEnv)
    (m : MemInfo) : Option (NeedOrd × NeedOrd) :=
  (runShape (S := CSet) (shapeEnvOfA jet xcod env) Option.none m.nm GoalS.done ⟨0, HoonSet.empty⟩).bind fun p =>
    (collapseOfA mode m.fuel p.1 m.cape).bind fun col =>
      (sureOfS p.1.sure.ned p.1.sure.lok m.cape).map fun sur => (col, sur)

/-- **`MemShapeBranch`**, restated. -/
def MemShapeBranchA (jet : Bell → Bool) (xcod : Bell → Option Nomm) (mode : Mode) (env : CallEnv) (cape : Cape)
    (DATA FOL : Noun) (nm : Nomm) (fuel : Nat) (keep : Bool) (SCC LONG JH ML TOP CA1 CTX : Noun)
    (col sur : NeedOrd) (G2 : Noun) : Prop :=
  lazeRealA jet xcod mode env ⟨nm, cape, DATA, fuel⟩ = some (col, sur) ∧
  nock (memShapeSubjA (modeNA mode) keep nm.toNoun SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL) CA1 CTX) memShape
    = some (C (shapeResNA (bakeNeedOrd col (Sock.mk cape DATA)).toNoun sur.toNoun) G2)

/-! ## The pieces -/

/-- The rest of the bunt `gen` with the cache `CA1` (its `id-gen` is `0` and `sofs` `~`). -/
def memY (CA1 : Noun) : RsRest :=
  ⟨A 0, A 1, cgModeNoun false, HoonMap.toNoun Blob.toNoun (HoonMap.empty : TreapMap mugF _),
    HoonMap.toNoun (listNoun A) (HoonMap.empty : TreapMap mugF _),
    HoonMap.toNoun condValNoun (HoonMap.empty : TreapMap mugF _), CA1, A 0⟩

theorem memY_gen (CA1 : Noun) :
    genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA1) = rsGenNoun ⟨0, HoonSet.empty⟩ (memY CA1) := by
  simp [genNoun, rsGenNoun, genEntry, cuRest, memY, HoonSet.toNoun_empty]

/-- The cache of `gen` after the run is `CA1`. -/
theorem memY_cache (st : RSt CSet) (CA1 : Noun) : slot? 510 (rsGenNoun st (memY CA1)) = some CA1 := by
  simp [rsGenNoun, memY, nock_exec]

theorem rs_arm_at'' (y : Noun) : slot? 0xabee (C comp.door y) = some rsArm := by kernel_rfl

/-- `(~(run-shape comp gen) nomm [%done ~] ~)` of the branch is the gate on its core. -/
theorem ms_run (GN NM DCTX S0 : Noun) :
    nock (C GN (memS3 NM DCTX S0)) msRun
      = nock (rsCoreG NM (C (A 0x656e6f64) (A 0)) (A 0) (C comp.door (C GN DCTX))) rsGate := by
  have ha := rs_arm_at'' (C GN DCTX)
  unfold msRun
  simp [nock_exec, memS3, ha, rsArm, rsCoreG]

/-- `memShape`: the run, then `msR1` on its product. -/
theorem ms_split (S : Noun) : nock S memShape = (nock S msRun).bind fun P => nock (C P S) msR1 := by
  rw [memShape_cut]
  generalize msRun = RN
  generalize msR1 = R1
  simp [nock_exec]

theorem sock_mk_noun (c : Cape) (d : Noun) : (Sock.mk c d).toNoun = C c.toNoun d := rfl

/-- The subject after the `=^` of the run: `[l [gen' [nomm [door S0]]]]`. -/
def msS1 (L G NM DCTX S0 : Noun) : Noun := C L (C G (C NM (C (C comp.door (C cuBunt DCTX)) S0)))

/-! ## The branch -/

/-- **The branch of the sweeps is the model** (`MemShapeBranch` of track I, restated): on `%must`
and `%may`, on a member `[[cape DATA] FOL]` whose nomm is in `RsTailE`, whose direct calls are in the
code table (`CallCode`, `CodeNomms`) and read the door as `ShapeCall` says at the rest `memY CA1` of
the bunt `gen` (`ShapeOK`), with `K` at axis `63` of the gate's context `CTX` and the code table at
axis `2` of `long-ska`, the model's `(col, sur)` is what the pill returns, and `gen'` is the noun of
`gen` after the run (its cache still `CA1`, `memY_cache`). -/
theorem memShape_branchA (mode : Mode) (hm : mode = Mode.must ∨ mode = Mode.may)
    (jet : Bell → Bool) (xcod : Bell → Option Nomm) (env : CallEnv) (cape : Cape) (DATA FOL : Noun)
    (nm : Nomm) (fuel : Nat) (keep : Bool) (SCC LONG JH ML TOP CA1 CTX : Noun)
    (hK : slot? 63 CTX = some compK) {cod : Noun} (hcode : slot? 2 LONG = some cod)
    (hcn : CodeNomms xcod cod) (hn : RsTailE nm)
    (hcc : CallCode cod (shapeCE (shapeEnvOfA jet xcod env)) nm)
    (hs : ShapeOK (memDCtx SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL)) (shapeEnvOfA jet xcod env)
      (· = memY CA1) Option.none nm)
    (col sur : NeedOrd) (hlr : lazeRealA jet xcod mode env ⟨nm, cape, DATA, fuel⟩ = some (col, sur)) :
    ∃ st1 : RSt CSet, MemShapeBranchA jet xcod mode env cape DATA FOL nm fuel keep SCC LONG JH ML TOP CA1 CTX
      col sur (rsGenNoun st1 (memY CA1)) := by
  -- the model's pieces
  unfold lazeRealA at hlr
  cases e1 : runShape (S := CSet) (shapeEnvOfA jet xcod env) Option.none nm GoalS.done ⟨0, HoonSet.empty⟩ with
  | none => rw [e1] at hlr; cases hlr
  | some r1 =>
  obtain ⟨⟨sr, fk, bd⟩, st1⟩ := r1
  rw [e1] at hlr
  simp only [Option.bind_some] at hlr
  cases e2 : collapseOfA mode fuel (Laze.mk sr fk bd) cape with
  | none => rw [e2] at hlr; cases hlr
  | some col' =>
  rw [e2] at hlr
  simp only [Option.bind_some, Laze.sure] at hlr
  cases e3 : sureOfS sr.ned sr.lok cape with
  | none => rw [e3] at hlr; cases hlr
  | some sur' =>
  rw [e3] at hlr
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlr
  obtain ⟨rfl, rfl⟩ := hlr
  refine ⟨st1, ?_, ?_⟩
  · simp [lazeRealA, e1, e2, e3, Laze.sure]
  -- the pill
  have h7 : slot? 7 (memDCtx SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := by
    simp [memDCtx, nock_exec]
  have hc52 : slot? 52 (memDCtx SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL)) = some cod := by
    simp [memDCtx, nock_exec, hcode]
  have hci := (comp_ctx_pill _ h7).1
  have hrun := rs_doneE hci h7 hc52 (shapeEnvOfA jet xcod env) hcn (· = memY CA1) nm hn hcc hs
    ⟨0, HoonSet.empty⟩ (memY CA1) rfl
  rw [e1] at hrun
  simp only [Option.map_some, rsDoor, GoalS.toNoun] at hrun
  unfold memShapeSubjA
  rw [ms_split, ms_run, memY_gen, hrun]
  simp only [Option.bind_some]
  -- the subject after the `=^`
  generalize hS1 : msS1 (Laze.mk sr fk bd).toNoun (rsGenNoun st1 (memY CA1)) nm.toNoun
    (memDCtx SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL))
    (memS0XA (A 1) (modeNA mode) (C (C cape.toNoun DATA) FOL) (loob keep) ML TOP CA1 CTX) = S1
  have hr1 : nock (C (C (Laze.mk sr fk bd).toNoun (rsGenNoun st1 (memY CA1)))
      (C (rsGenNoun ⟨0, HoonSet.empty⟩ (memY CA1)) (memS3 nm.toNoun
        (memDCtx SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL))
        (memS0XA (A 1) (modeNA mode) (C (C cape.toNoun DATA) FOL) (loob keep) ML TOP CA1 CTX)))) msR1
      = nock S1 msR3 := by
    rw [← hS1]
    unfold msR1 msR2
    generalize msR3 = R3
    simp [nock_exec, memS3, msS1]
  rw [hr1]
  have hk1 : slot? 8191 S1 = some compK := by rw [← hS1]; simp [msS1, memS0XA, memSam, nock_exec, hK]
  have hl1 : slot? 2 S1 = some (Laze.mk sr fk bd).toNoun := by rw [← hS1]; simp [msS1, nock_exec]
  have hc1 : slot? 2032 S1 = some cape.toNoun := by rw [← hS1]; simp [msS1, memS0XA, memSam, nock_exec]
  have hb1 : slot? 1016 S1 = some (C cape.toNoun DATA) := by rw [← hS1]; simp [msS1, memS0XA, memSam, nock_exec]
  have hm1 : slot? 1018 S1 = some (modeNA mode) := by rw [← hS1]; simp [msS1, memS0XA, memSam, nock_exec]
  have hg1 : slot? 6 S1 = some (rsGenNoun st1 (memY CA1)) := by rw [← hS1]; simp [msS1, nock_exec]
  have hs1 : slot? 4 S1 = some sr.toNoun := by rw [← hS1]; simp [msS1, nock_exec, Laze.toNoun]
  clear hS1
  have hcol : nock S1 msColl = some col'.toNoun := by
    rcases hm with rfl | rfl
    · have := lco_call S1 (Laze.mk sr fk bd) cape fuel col' e2 hk1 hl1 hc1
      unfold msColl msTest
      generalize msMust = MM at this
      generalize msMay = MY
      simp [nock_exec, hm1, modeNA, this]
    · have := lmy_call S1 (Laze.mk sr fk bd) cape hk1 hl1 hc1
      simp only [collapseOfA] at e2
      rw [e2] at this
      unfold msColl msTest
      generalize msMust = MM
      generalize msMay = MY at this
      simp [nock_exec, hm1, modeNA, this]
  have hk2 : slot? 0x3fff (C col'.toNoun S1) = some compK := by simp [nock_exec, hk1]
  have hl2 : slot? 2040 (C col'.toNoun S1) = some (Sock.mk cape DATA).toNoun := by
    simp [nock_exec, hb1, sock_mk_noun]
  have hbno := bno_call (C col'.toNoun S1) col' (Sock.mk cape DATA) hk2 (by simp [nock_exec]) hl2
  have hshape : nock S1 msShape = some (bakeNeedOrd col' (Sock.mk cape DATA)).toNoun := by
    unfold msShape
    generalize msColl = MC at hcol
    generalize msBno = MB at hbno
    simp [nock_exec, hcol, hbno]
  -- `sur`: `+sure-of` of `sure.l`
  obtain ⟨ned, lok⟩ := sr
  have hso := so_gate ned lok cape
  rw [← sureOfS_eq, e3] at hso
  have hsat := so_at
  simp only [SureO.toNoun] at hs1
  have hsur : nock (C (bakeNeedOrd col' (Sock.mk cape DATA)).toNoun S1) msSur = some sur'.toNoun := by
    unfold msSur
    generalize compK = KC at hsat hso hk1
    simp [nock_exec, hk1, hs1, hc1, hsat, so_arm, hso]
  unfold msR3 msTuple
  generalize msShape = MS at hshape
  generalize msSur = MU at hsur
  simp [nock_exec, hshape, hsur, shapeResNA, hg1]

end Compiler
end Formalization
