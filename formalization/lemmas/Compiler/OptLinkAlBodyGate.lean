import lemmas.Compiler.OptLinkAlBodyImm
import lemmas.Compiler.OptLinkAlPrelude
import lemmas.Compiler.OptLinkMiddle
import lemmas.Compiler.OptLinkAlState

/-!
# `+alias`: the gate of the body and its `+roll` (phase 13, README Gaps 13)

* `alCase op`: the case of the `?-` that runs on `op` (the four hints
  `%hsp`, `%hse`, `%hcp`, `%hce` share the noun `alOpHce`, `%csm` is the last
  case `alOpLast`, run with no test).
* `opOK_all`: **every case links** (`OpOK` for `pick = Ana.pickR FinMap`).
* `al_bodyG_case`: the gate `alBodyG` sets `gen` to its sample's `gen-init`
  and runs `alCase op`; `al_bodyG`: so it links.
* `body_fold`: the `+roll` is the model's `aliasBody` (the kept ops consed in
  front of the accumulator, reversed at the end by the `+flop`).
* `al_body`: **the phase**: `alBody` (the `=^  body-new  gen` with its
  `=-  [(flop -<) ->]`) on a related state returns the noun of the model's
  ops and a related state; `gen` keeps every field but `old`, `info-local`,
  `imms-local`.  The roll starts from the bunt of its gate's sample, `[*pole
  ~ gen]` (`poleBunt`, `list_mb`).
* `al_body_gen`: `al_body` stated with `GenRelL` (`OptLinkAlState.lean`) on
  the walk's subject `alWS`: the body of the block `b` runs on the model's
  state `{ old := g.old, loc, imml }` and leaves `gen` related to
  `{ g with old := st'.old }` with `st'.loc`, `st'.imml`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local instance] SkaModel.Ana.tkeyNat

/-- The case of the `?-` over the op that runs on `op`. -/
def alCase : Pole → Noun
  | Pole.imm .. => alOpImm
  | Pole.mov .. => alOpMov
  | Pole.inc .. => alOpInc
  | Pole.con .. => alOpCon
  | Pole.hed .. => alOpHed
  | Pole.tal .. => alOpTal
  | Pole.cel .. => alOpCel
  | Pole.lob .. => alOpLob
  | Pole.equ .. => alOpEqu
  | Pole.hsp .. => alOpHce
  | Pole.hse .. => alOpHce
  | Pole.hdp .. => alOpHdp
  | Pole.hde .. => alOpHde
  | Pole.hmp .. => alOpHmp
  | Pole.hme .. => alOpHme
  | Pole.hcp .. => alOpHce
  | Pole.hce .. => alOpHce
  | Pole.spy .. => alOpSpy
  | Pole.nok .. => alOpNok
  | Pole.cal .. => alOpCal
  | Pole.caf .. => alOpCaf
  | Pole.cam .. => alOpCam
  | Pole.csl .. => alOpCsl
  | Pole.csf .. => alOpCsf
  | Pole.csm .. => alOpLast

/-- **Every case of the `?-` links.** -/
theorem opOK_all (op : Pole) : OpOK (Ana.pickR FinMap) (alCase op) op := by
  cases op with
  | imm n d => exact opOK_imm n d
  | mov s d => exact opOK_mov _ s d
  | inc s d => exact opOK_inc _ s d
  | con h t d => exact opOK_con h t d
  | hed s d => exact opOK_hed _ s d
  | tal s d => exact opOK_tal _ s d
  | cel p => exact opOK_cel _ p
  | lob p => exact opOK_lob _ p
  | equ l r => exact opOK_equ _ l r
  | hsp n f => exact opOK_hsp _ n f
  | hse n f => exact opOK_hse _ n f
  | hdp n p f => exact opOK_hdp _ n p f
  | hde n p f => exact opOK_hde _ n p f
  | hmp a v f => exact opOK_hmp _ a v f
  | hme a v f => exact opOK_hme _ a v f
  | hcp n f => exact opOK_hcp _ n f
  | hce n f => exact opOK_hce _ n f
  | spy e p d => exact opOK_spy _ e p d
  | nok u f d => exact opOK_nok _ u f d
  | cal a v d => exact opOK_cal _ a v d
  | caf a v d n => exact opOK_caf _ a v d n
  | cam a v d k => exact opOK_cam _ a v d k
  | csl a s d => exact opOK_csl _ a s d
  | csf a s d n => exact opOK_csf _ a s d n
  | csm a s d k => exact opOK_csm _ a s d k

/-- The gate `alBodyG`: `=.  gen  gen-init`, then the case of the op. -/
theorem al_bodyG_case (op : Pole) (BN GI P1 P2 P3 P4 P5 GEN0 Y Z : Noun) :
    nock (C alBodyG (C (C op.toNoun (C BN GI)) (C P1 (C P2 (C P3 (C P4 (C P5 (C alBat (C GEN0 (C Y (C Z optC)))))))))))
      alBodyG = nock (alOS alBodyG op.toNoun BN GI P1 P2 P3 P4 P5 GI Y Z) (alCase op) := by
  unfold alOS
  generalize optC = OC
  generalize alBat = B
  conv => lhs; arg 2; unfold alBodyG
  cases op <;>
    simp [nock_exec, Pole.toNoun, alCase, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel,
      Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy,
      Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

/-- **The gate of the `+roll` links**, on any `gen` of its context. -/
theorem al_bodyG (op : Pole) (BN P1 P2 P3 P4 P5 GEN0 Y Z NEW INFO IMMS REST OLD LOC IML : Noun)
    (st : Opt.ABody) (hR : BodyRel OLD LOC IML st) (res : Option Pole) (st' : Opt.ABody)
    (hm : Opt.aliasOp (Ana.pickR FinMap) st op = some (res, st')) :
    ∃ OLD' LOC' IML', nock (C alBodyG (C (C op.toNoun (C BN (alGenB NEW OLD INFO IMMS LOC IML REST)))
        (C P1 (C P2 (C P3 (C P4 (C P5 (C alBat (C GEN0 (C Y (C Z optC))))))))))) alBodyG
      = some (C (optCons res BN) (alGenB NEW OLD' INFO IMMS LOC' IML' REST)) ∧ BodyRel OLD' LOC' IML' st' := by
  rw [al_bodyG_case]
  exact opOK_all op alBodyG BN _ P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm

/-! ## The `+roll` against `aliasBody` -/

/-- The step of the `+roll`: the kept op consed in front of the accumulator. -/
def bodyStep (pick : List Nat → Nat) (op : Pole) (s : List Pole × Opt.ABody) : Option (List Pole × Opt.ABody) :=
  (Opt.aliasOp pick s.2 op).map fun r => (r.1.toList ++ s.1, r.2)

theorem body_fold (pick : List Nat → Nat) : ∀ (body : List Pole) (acc : List Pole) (st : Opt.ABody),
    body.foldlM (fun s p => bodyStep pick p s) (acc, st)
      = (Opt.aliasBody pick body st).map fun r => (r.1.reverse ++ acc, r.2)
  | [], acc, st => by simp [Opt.aliasBody]
  | op :: l, acc, st => by
    rw [List.foldlM_cons]
    simp only [Opt.aliasBody]
    cases h : Opt.aliasOp pick st op with
    | none => simp [bodyStep, h]
    | some r =>
      obtain ⟨o, s⟩ := r
      have e : bodyStep pick op (acc, st) = some (o.toList ++ acc, s) := by simp [bodyStep, h]
      rw [e]
      show List.foldlM (fun s p => bodyStep pick p s) (o.toList ++ acc, s) l = _
      rw [body_fold pick l]
      cases h2 : Opt.aliasBody pick l s with
      | none => simp [h2]
      | some r2 => cases o <;> simp [h2]

/-- The accumulator of the `+roll`: `[body-new gen]`. -/
def BodyAcc (NEW INFO IMMS REST : Noun) (N : Noun) (s : List Pole × Opt.ABody) : Prop :=
  ∃ OLD LOC IML, N = C (listNoun Pole.toNoun s.1) (alGenB NEW OLD INFO IMMS LOC IML REST) ∧
    BodyRel OLD LOC IML s.2

theorem optCons_listNoun (res : Option Pole) (acc : List Pole) :
    optCons res (listNoun Pole.toNoun acc) = listNoun Pole.toNoun (res.toList ++ acc) := by
  cases res <;> rfl

/-- **The body of a block** (phase 13). -/
theorem al_body (P1 PAR FIN P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML : Noun) (body : List Pole)
    (st : Opt.ABody) (hR : BodyRel OLD LOC IML st) (ops : List Pole) (st' : Opt.ABody)
    (hb : Opt.aliasBody (Ana.pickR FinMap) body st = some (ops, st')) :
    ∃ OLD' LOC' IML', nock (C P1 (C (C PAR (C (listNoun Pole.toNoun body) FIN)) (C P3 (C P4 (C P5
        (C alBat (C (alGenB NEW OLD INFO IMMS LOC IML REST) (C Y (C Z optC))))))))) alBody
      = some (C (listNoun Pole.toNoun ops) (alGenB NEW OLD' INFO IMMS LOC' IML' REST)) ∧
      BodyRel OLD' LOC' IML' st' := by
  have hfold : body.foldlM (fun s p => bodyStep (Ana.pickR FinMap) p s) (([] : List Pole), st)
      = some (ops.reverse, st') := by
    rw [body_fold, hb]; simp
  obtain ⟨N', hN', OLD', LOC', IML', e, hR'⟩ := roll_gate_rel Pole.toNoun (BodyAcc NEW INFO IMMS REST)
    (bodyStep (Ana.pickR FinMap)) layer2 alBodyG poleBunt
    (C P1 (C (C PAR (C (listNoun Pole.toNoun body) FIN)) (C P3 (C P4 (C P5
      (C alBat (C (alGenB NEW OLD INFO IMMS LOC IML REST) (C Y (C Z optC)))))))))
    body ([], st) (C (A 0) (alGenB NEW OLD INFO IMMS LOC IML REST)) (ops.reverse, st')
    (fun op _ s N s' hs hf => by
      obtain ⟨OLD0, LOC0, IML0, rfl, hR0⟩ := hs
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hf
      obtain ⟨OLD1, LOC1, IML1, h1, h2⟩ := al_bodyG op _ P1 _ P3 P4 P5 _ Y Z NEW INFO IMMS REST OLD0 LOC0 IML0
        s.2 hR0 r.1 r.2 hr
      exact ⟨_, h1, OLD1, LOC1, IML1, by rw [optCons_listNoun], h2⟩)
    ⟨OLD, LOC, IML, rfl, hR⟩ hfold
  subst e
  refine ⟨OLD', LOC', IML', ?_, hR'⟩
  rw [← listNoun_map_listN] at hN'
  have hfl := flop_gate layer2 homoIn_layer2 (ops.reverse.map Pole.toNoun)
  rw [← List.map_reverse, List.reverse_reverse, ← listNoun_map_listN, ← listNoun_map_listN] at hfl
  have hL := optC_layer2
  have hL1 := optC_layer1
  have hT := optC_types
  have hpm := pole_mold_at
  have hpg := pole_gate
  have hps := pole_gate_bat
  have hpb := pole_bunt'
  have hl1 := layer2_layer1
  have hla := list_at
  generalize optC = OC at hL hL1 hT hN'
  generalize compTypes = CT at hT hpm hpg
  generalize poleGateBat = PB at hps hpb
  generalize poleGate = PG at hpg hps hpb
  unfold alBody
  generalize alBodyG = G at hN' ⊢
  simp [nock_exec, alBodyGBunt, hL, hL1, hT, hpm, hpg, hps, hpb, hl1, hla, list_arm, list_b, list_mb, roll.arm_at, roll_arm,
    flop.arm_at, flop_arm, hN', hfl]

/-- **The body of a block, on the state of the walk** (phase 13 with `GenRelL`). -/
theorem al_body_gen {g : Opt.AGen (TreapMap mugF)} {loc : Opt.AInfo} {imml : Opt.AImms} {GEN : Noun}
    (hg : GenRelL g loc imml GEN) (PN IM IN PRE NA BL REV TOPO : Noun) (b : Blob) (ops : List Pole)
    (st' : Opt.ABody) (hb : Opt.aliasBody (Ana.pickR FinMap) b.body { old := g.old, loc := loc, imml := imml }
      = some (ops, st')) :
    ∃ GEN', nock (C PN (C b.toNoun (C IM (C IN (C PRE (alWS GEN NA BL REV TOPO)))))) alBody
      = some (C (listNoun Pole.toNoun ops) GEN') ∧ GenRelL { g with old := st'.old } st'.loc st'.imml GEN' := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, REV', rfl, h1, h2, h3, h4, h5, h6⟩ := hg
  obtain ⟨OLD', LOC', IML', e, hR'⟩ := al_body PN (listNoun A b.par) b.fin.toNoun IM IN PRE
    (HoonMap.toNoun Blob.toNoun g.new) INFO IMMS (C REV' (flag g.folded)) alBodyCut (C NA (C BL (C REV TOPO)))
    OLD LOC IMML b.body _ ⟨h1, h5, h6⟩ ops st' hb
  exact ⟨_, e, OLD', INFO, IMMS, LOC', IML', REV', rfl, hR'.1, h2, h3, h4, hR'.2.1, hR'.2.2⟩

end Compiler
end Formalization
