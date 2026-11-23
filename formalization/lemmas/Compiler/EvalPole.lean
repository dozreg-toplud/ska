import lemmas.Compiler.EvalPass
import lemmas.Pill.Arm.Eval_pole

/-!
`+eval-pole` of the interpreter core against `localPole` of
`lemmas/Ska/Interp.lean`: the ops that change only the registers and the
trace.  The gate's context is the interpreter core with the compiler's core
`cor` as its tail (`=*  cor  ..poke`); the product is `[tone regs trace cor]`.

The ops that leave the function (`%nok` and the calls, which poke the
compiler and run `+eval-top` or `+eval-blob`) and `%spy` (which slams the scry
gate) are not done here.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- `+read` on a map of `TreapMap mugF`, in any context that holds what it
reads. -/
theorem read_model (c : Noun) (hc : RegsIn mugF c) (r : Nat) (regs : TreapMap mugF Noun) :
    nock (C read.battery (C (C (A r) (HoonMap.toNoun id regs)) c)) read.battery
      = SkaModel.read r regs := by
  have h := getF_hoonMap id regs r
  unfold SkaModel.read
  cases e : HoonMap.get regs r with
  | none => rw [e] at h; exact read_gate_nil _ hc r _ h
  | some v => rw [e] at h; exact read_gate _ hc r _ v h

/-- `+store` on a map of `TreapMap mugF`. -/
theorem store_model (c : Noun) (hc : RegsIn mugF c) (r : Nat) (v : Noun)
    (regs : TreapMap mugF Noun) :
    nock (C store.battery (C (C (A r) (C v (HoonMap.toNoun id regs))) c)) store.battery
      = some (HoonMap.toNoun id (SkaModel.store r v regs)) :=
  store_gate _ hc r v _ _ (putF_hoonMap id regs r v)

/-- What `+eval-pole` reads from its context for the local ops: `+read`,
`+store`, `+move` and what they read. -/
abbrev EvalPoleIn (c : Noun) : Prop := slot? move.axis c = some move.arm ∧ MoveIn mugF c

/-- The product of `+eval-pole` as a noun. -/
def poleOut (cor : Noun) (r : Tone × TreapMap mugF Noun × Trace) : Noun :=
  C r.1.toNoun (C (HoonMap.toNoun id r.2.1) (C (listNoun Frame.toNoun r.2.2) cor))

/-- The ops that `localPole` runs, other than `%spy` and `%hmp`. -/
def PlainLocal : Pole → Prop
  | Pole.imm _ _ | Pole.mov _ _ | Pole.inc _ _ | Pole.con _ _ _ | Pole.hed _ _ | Pole.tal _ _
  | Pole.cel _ | Pole.lob _ | Pole.equ _ _ | Pole.hsp _ _ | Pole.hse _ _ | Pole.hdp _ _ _
  | Pole.hde _ _ _ | Pole.hme _ _ _ | Pole.hcp _ _ | Pole.hce _ _ => True
  | _ => False

/-- The tags of the frames that `+mink` keeps: either one of the five, or
none of them. -/
theorem stopTag_cases (tag : Nat) :
    (stopTag tag = true ∧
      (tag = 0x6b6e7568 ∨ tag = 0x646e6168 ∨ tag = 0x65736f6c ∨ tag = 0x6e61656d ∨
        tag = 0x746f7073)) ∨
    (stopTag tag = false ∧ ¬ (0x6b6e7568 = tag) ∧ ¬ (0x646e6168 = tag) ∧
      ¬ (0x65736f6c = tag) ∧ ¬ (0x6e61656d = tag) ∧ ¬ (0x746f7073 = tag)) := by
  cases h : stopTag tag <;> simp [stopTag] at h <;>
    simp only [Tag.hunk, Tag.hand, Tag.mean, Tag.lose, Tag.spot] at h <;> simp <;> omega

/-- One case of `+eval-pole`: run the dispatch and the op. -/
macro "pole_simp" : tactic => `(tactic|
  (nock_open eval_pole.battery
   simp [nock_exec, nock_ite, Pole.toNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal,
     Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp,
     Tag.hce, Tag.meac, store_arm, read_arm, move_arm, localPole, poleOut, Tone.toNoun, listNoun,
     Frame.toNoun, popTrace, *]))

set_option maxHeartbeats 2000000 in
/-- `+eval-pole` on an op that changes only the registers and the trace. -/
theorem eval_pole_local (ctx cor : Noun) (hcor : slot? 3 ctx = some cor) (hc : EvalPoleIn ctx)
    (lib : Lib) (scry : Noun) (pole : Pole) (hp : PlainLocal pole) (regs : TreapMap mugF Noun)
    (trace : Trace) :
    nock (C eval_pole.battery (C (C pole.toNoun
        (C (C (HoonMap.toNoun id regs) (listNoun Frame.toNoun trace)) scry)) ctx)) eval_pole.battery
      = (localPole lib scry pole regs trace).map (poleOut cor) := by
  obtain ⟨hmv, hmc⟩ := hc
  have hrc : RegsIn mugF ctx := hmc.2.2
  obtain ⟨hrd, hst, _⟩ := hmc
  have hsm := store_model ctx hrc
  have hrm := read_model ctx hrc
  have hmm := move_model ctx ⟨hrd, hst, hrc⟩
  cases pole with
  | imm n d => pole_simp
  | mov s d => cases e : SkaModel.move s d regs <;> pole_simp
  | inc s d =>
    cases e : SkaModel.read s regs with
    | none => pole_simp
    | some v => cases v <;> pole_simp
  | con h t d =>
    cases e : SkaModel.read h regs <;> cases e' : SkaModel.read t regs <;> pole_simp
  | hed s d =>
    cases e : SkaModel.read s regs with
    | none => pole_simp
    | some v => cases v <;> pole_simp
  | tal s d =>
    cases e : SkaModel.read s regs with
    | none => pole_simp
    | some v => cases v <;> pole_simp
  | cel p =>
    cases e : SkaModel.read p regs with
    | none => pole_simp
    | some v => cases v <;> pole_simp
  | lob p =>
    cases e : SkaModel.read p regs with
    | none => pole_simp
    | some v =>
      rcases v with a | ⟨_, _⟩
      · rcases a with _ | _ | a <;> pole_simp
      · pole_simp
  | equ l r => cases e : SkaModel.read l regs <;> cases e' : SkaModel.read r regs <;> pole_simp
  | hsp n f => pole_simp
  | hse n f => pole_simp
  | hdp n p f =>
    rcases stopTag_cases n with ⟨h, rfl | rfl | rfl | rfl | rfl⟩ | ⟨h, h1, h2, h3, h4, h5⟩
    all_goals first
      | (cases e : SkaModel.read p regs <;> pole_simp; done)
      | pole_simp
  | hde n p f =>
    rcases stopTag_cases n with ⟨h, rfl | rfl | rfl | rfl | rfl⟩ | ⟨h, h1, h2, h3, h4, h5⟩
    all_goals first
      | (cases trace <;> pole_simp; done)
      | pole_simp
  | hme a v f => cases trace <;> pole_simp
  | hcp n f => pole_simp
  | hce n f => cases trace <;> pole_simp
  | _ => simp [PlainLocal] at hp

end Compiler
end Formalization
