import lemmas.Compiler.OptLinkAlJImms
import lemmas.Ska.OptAliasPickRoot

/-!
# `+alias`: the body of a block, the small cases (phase 13 of the plan, README Gaps 13)

```hoon
  =^  body-new=(list pole)  gen
    =-  [(flop -<) ->]
    ^-  [(list pole) _gen]
    %+  roll  body.bob
    |=  [op=pole body-new=(list pole) gen-init=_gen]
    ^+  [body-new gen]
    =.  gen  gen-init
    ?-    -.op
      ...
```

The gate `alBodyG` of the `+roll` first sets `gen` (axis `1022` of its
subject) to its sample's `gen-init`, then runs one case of the `?-` over the
op (`alOpImm` to `alOpLast`).  A case runs in the subject `alOS`: the gate
`K`, the sample `[op body-new gen-init]`, and the subject of the body phase:
`par-new`, `bob`, `imms`, `info`, `pre`, then the `|^` core of `+alias` with
`gen` (`alGenB`: `new`, `old`, `info`, `imms`, `info-local`, `imms-local` and
the rest).  Each case returns `[body-new gen]`, the op (renamed) consed on
`body-new` or not.

* `al_op_mov`: `%mov` renames `d` to `(rn s)`, drops the op.
* `al_op_equ`: `%equ` drops the op when the renamed registers are equal,
  else keeps it renamed.
* `al_op_hsp` (also `%hse`, `%hcp`, `%hce`: the four cases are one noun),
  `al_op_hdp`, `al_op_hde`, `al_op_hmp`, `al_op_hme`: the hints, kept, their
  registers renamed.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of `gen` with the fields the body reads and writes named. -/
def alGenB (NEW OLD INFO IMMS LOC IML REST : Noun) : Noun :=
  C NEW (C OLD (C INFO (C IMMS (C LOC (C IML REST)))))

/-- The subject of a case of the `?-` over the op: the gate `K`, its sample
`[op body-new gen-init]`, `par-new`, `bob`, `imms`, `info`, `pre`, then the
`|^` core of `+alias` with `gen` = `GEN`. -/
def alOS (K OP BN GI P1 P2 P3 P4 P5 GEN Y Z : Noun) : Noun :=
  C K (C (C OP (C BN GI)) (C P1 (C P2 (C P3 (C P4 (C P5 (C alBat (C GEN (C Y (C Z optC))))))))))

/-- The arm `rn` of the battery `alBat` (axis `6`). -/
def alRnArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alRnB) (C (A 0) (A 1))))

theorem alBat_rn : ∃ X R, alBat = C X (C alRnArm R) := ⟨_, _, rfl⟩

/-- The list noun of the ops kept so far, with the op of a case put in front
when it is kept. -/
def optCons : Option Pole → Noun → Noun
  | none, BN => BN
  | some p, BN => C p.toNoun BN

/-- `rn` in the core with `alBat` cut at its arm `rn`. -/
theorem al_rn' (X R NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f) (r : Nat) :
    nock (C alRnB (C (A r) (C (C X (C alRnArm R)) (C (C NEW (C OLD REST)) (C Y (C Z optC)))))) alRnB
      = some (A (f r)) :=
  al_rn (C X (C alRnArm R)) Y Z NEW OLD REST f h r

/-- **`%mov`**: `old.gen` gets `d ↦ (rn s)`, the op is dropped. -/
theorem al_op_mov (K BN GI P1 P2 P3 P4 P5 NEW OLD INFO IMMS LOC IML REST Y Z : Noun) (f : Nat → Nat)
    (h : OldRel OLD f) (s d : Nat) :
    ∃ OLD', nock (alOS K (Pole.mov s d).toNoun BN GI P1 P2 P3 P4 P5
        (alGenB NEW OLD INFO IMMS LOC IML REST) Y Z) alOpMov
      = some (C BN (alGenB NEW OLD' INFO IMMS LOC IML REST)) ∧ OldRel OLD' (Opt.updA f d (f s)) := by
  obtain ⟨N', hp, hr⟩ := old_put h d (f s)
  refine ⟨N', ?_, hr⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z f h
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  simp [nock_exec, alOpMov, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hrn, hp]

/-! ## The relation of the state of the body, and the statement of a case -/

/-- `old.gen`, `info-local.gen` and `imms-local.gen` hold the state of the
model's body. -/
def BodyRel (OLD LOC IML : Noun) (st : Opt.ABody) : Prop :=
  OldRel OLD st.old ∧ InfoMapRel LOC st.loc ∧ ImmsRel IML st.imml

/-- **The case `F` of the op `op` links**: where the model's step returns
`(res, st')` on a related state, the case returns `[body-new gen]` with the
op `res` consed on `body-new` when kept and `gen` related to `st'`, the other
fields of `gen` as they were. -/
def OpOK (pick : List Nat → Nat) (F : Noun) (op : Pole) : Prop :=
  ∀ (K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML : Noun) (st : Opt.ABody),
    BodyRel OLD LOC IML st → ∀ res st', Opt.aliasOp pick st op = some (res, st') →
    ∃ OLD' LOC' IML', nock (alOS K op.toNoun BN GI P1 P2 P3 P4 P5
        (alGenB NEW OLD INFO IMMS LOC IML REST) Y Z) F
      = some (C (optCons res BN) (alGenB NEW OLD' INFO IMMS LOC' IML' REST)) ∧ BodyRel OLD' LOC' IML' st'

theorem opOK_mov (pick : List Nat → Nat) (s d : Nat) : OpOK pick alOpMov (Pole.mov s d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨OLD', h1, h2⟩ := al_op_mov K BN GI P1 P2 P3 P4 P5 NEW OLD INFO IMMS LOC IML REST Y Z st.old hR.1 s d
  exact ⟨OLD', LOC, IML, h1, h2, hR.2.1, hR.2.2⟩

/-- **`%equ`**: dropped when the renamed registers are equal. -/
theorem opOK_equ (pick : List Nat → Nat) (l r : Nat) : OpOK pick alOpEqu (Pole.equ l r) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  refine ⟨OLD, LOC, IML, ?_, ?_⟩
  · obtain ⟨X, R, hX⟩ := alBat_rn
    have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
    have hL := optC_layer2
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    by_cases e : st.old l = st.old r
    · simp only [Opt.aliasOp, e, if_true, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [nock_exec, alOpEqu, alRnArm, Pole.toNoun, hrn, e, eqCode, optCons]
    · simp only [Opt.aliasOp, e, if_false, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have e' : ¬ A (st.old l) = A (st.old r) := fun h => e (Noun.atom.inj h)
      simp [nock_exec, alOpEqu, alRnArm, Pole.toNoun, hrn, e, e', eqCode, optCons, Tag.equ]
  · by_cases e : st.old l = st.old r <;>
      simp only [Opt.aliasOp, e, if_true, if_false, Option.some.injEq, Prod.mk.injEq] at hm <;>
      obtain ⟨rfl, rfl⟩ := hm <;> exact hR

/-! ## The hints: kept, their registers renamed -/

/-- `(turn v rn)`: the list of the renamed registers. -/
theorem al_turn_rn (CORE : Noun) (f : Nat → Nat)
    (hrn : ∀ r, nock (C alRnB (C (A r) CORE)) alRnB = some (A (f r))) (v : List Nat) :
    nock (C turn.battery (C (C (listNoun A v) (C alRnB (C (A 0) CORE))) layer2)) turn.battery
      = some (listNoun A (v.map f)) := by
  rw [listNoun_map_listN, listNoun_map_listN,
    turn_gate layer2 homoIn_layer2 alRnB (A 0) CORE (fun x => match x with | Noun.atom r => A (f r) | x => x)
      (v.map A) (fun x hx => by obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx; exact hrn r)]
  simp [List.map_map]
  rfl

theorem opOK_hsp (pick : List Nat → Nat) (n : Nat) (f : Noun) : OpOK pick alOpHce (Pole.hsp n f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  unfold alOS alGenB alOpHce alOpHcp alOpHse alOpHsp
  simp [nock_exec, Pole.toNoun, optCons]

theorem opOK_hse (pick : List Nat → Nat) (n : Nat) (f : Noun) : OpOK pick alOpHce (Pole.hse n f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  unfold alOS alGenB alOpHce alOpHcp alOpHse alOpHsp
  simp [nock_exec, Pole.toNoun, optCons]

theorem opOK_hcp (pick : List Nat → Nat) (n f : Noun) : OpOK pick alOpHce (Pole.hcp n f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  unfold alOS alGenB alOpHce alOpHcp alOpHse alOpHsp
  simp [nock_exec, Pole.toNoun, optCons]

theorem opOK_hce (pick : List Nat → Nat) (n f : Noun) : OpOK pick alOpHce (Pole.hce n f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  unfold alOS alGenB alOpHce alOpHcp alOpHse alOpHsp
  simp [nock_exec, Pole.toNoun, optCons]

theorem opOK_hdp (pick : List Nat → Nat) (n p : Nat) (f : Noun) : OpOK pick alOpHdp (Pole.hdp n p f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpHdp, Tag.hdp]

theorem opOK_hde (pick : List Nat → Nat) (n p : Nat) (f : Noun) : OpOK pick alOpHde (Pole.hde n p f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpHde, Tag.hde]

theorem opOK_hmp (pick : List Nat → Nat) (a : Bell) (v : List Nat) (f : Noun) :
    OpOK pick alOpHmp (Pole.hmp a v f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  have ht := al_turn_rn _ _ hrn v
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpHmp, Tag.hmp, ht]

theorem opOK_hme (pick : List Nat → Nat) (a : Bell) (v : List Nat) (f : Noun) :
    OpOK pick alOpHme (Pole.hme a v f) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  refine ⟨OLD, LOC, IML, ?_, hR⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  have ht := al_turn_rn _ _ hrn v
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpHme, Tag.hme, ht]

/-! ## The ops that define a fresh register: `*info-reg` at `d` -/

/-- `*info-reg`. -/
def alInfoBunt : Noun := C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))

theorem infoRel_bunt : InfoRel alInfoBunt {} := ⟨false, A 0, A 0, rfl, sawRel_nil, sawRel_nil, rfl⟩

/-- `(~(put by info-local.gen) d N)` with `N` related to `x`. -/
theorem loc_put {LOC : Noun} {m : Opt.AInfo} (h : InfoMapRel LOC m) (d : Nat) {N : Noun} {x : Opt.InfoReg}
    (hN : InfoRel N x) :
    ∃ LOC', nock (C by.put.battery (C (C (A d) N) (C by.battery (C LOC layer2)))) by.put.battery = some LOC' ∧
      InfoMapRel LOC' (Opt.updA m d (some x)) := by
  obtain ⟨out, hp, ho, hg⟩ := putF_spec mugF LOC (A d) N h.1
  refine ⟨out, put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, ?_, ?_⟩
  · intro k v hv
    rcases (hg k v).1 hv with ⟨rfl, rfl⟩ | ⟨ne, hv'⟩
    · exact ⟨d, x, rfl, by simp [Opt.updA], hN⟩
    · obtain ⟨r, y, rfl, hy, hr⟩ := h.2.1 _ _ hv'
      have : r ≠ d := fun e => ne (by rw [e])
      exact ⟨r, y, rfl, by simp [Opt.updA, this, hy], hr⟩
  · intro r y hy
    by_cases e : r = d
    · subst e; exact ⟨N, (hg _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · simp only [Opt.updA, e, if_false] at hy
      obtain ⟨w, hw⟩ := h.2.2 r y hy
      exact ⟨w, (hg _ _).2 (Or.inr ⟨fun h' => e (Noun.atom.inj h'), hw⟩)⟩

theorem opOK_spy (pick : List Nat → Nat) (e p d : Nat) : OpOK pick alOpSpy (Pole.spy e p d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpSpy, Tag.spy, hp]

theorem opOK_nok (pick : List Nat → Nat) (u f d : Nat) : OpOK pick alOpNok (Pole.nok u f d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpNok, Tag.nok, hp]

theorem opOK_cal (pick : List Nat → Nat) (a : Bell) (v : List Nat) (d : Nat) : OpOK pick alOpCal (Pole.cal a v d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  have ht := al_turn_rn _ _ hrn v
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpCal, Tag.cal, hp, ht]

theorem opOK_caf (pick : List Nat → Nat) (a : Bell) (v : List Nat) (d : Nat) (n : Ring) : OpOK pick alOpCaf (Pole.caf a v d n) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  have ht := al_turn_rn _ _ hrn v
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpCaf, Tag.caf, hp, ht]

theorem opOK_cam (pick : List Nat → Nat) (a : Bell) (v : List Nat) (d : Nat) (k : Noun) : OpOK pick alOpCam (Pole.cam a v d k) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  have ht := al_turn_rn _ _ hrn v
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpCam, Tag.cam, hp, ht]

theorem opOK_csl (pick : List Nat → Nat) (a : Bell) (s d : Nat) : OpOK pick alOpCsl (Pole.csl a s d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpCsl, Tag.csl, hp]

theorem opOK_csf (pick : List Nat → Nat) (a : Bell) (s d : Nat) (n : Ring) : OpOK pick alOpCsf (Pole.csf a s d n) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpCsf, Tag.csf, hp]

theorem opOK_csm (pick : List Nat → Nat) (a : Bell) (s d : Nat) (k : Noun) : OpOK pick alOpLast (Pole.csm a s d k) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d infoRel_bunt
  refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  unfold alOS alGenB
  rw [hX]
  generalize optC = OC at hL hrn
  unfold alRnArm at hrn
  unfold alInfoBunt at hp
  simp [nock_exec, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, turn.arm_at, turn_arm, hrn, optCons, alOpLast, Tag.csm, hp]

end Compiler
end Formalization
