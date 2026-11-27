import lemmas.Compiler.CompStraightRun

/-!
# `+to-straight` with `run` `|`: the jumps, `rewrite-op` and `rewrite-fin`

Written by `tools/gen/tsrops.py` (README Gaps 20).  In a core
`[tsCoreBat [(rmN st) R]]` whose `rer` is the model's stateful `rr`
(`MapCoreM`: `RerM`, `layer2`, the bunt of the units of `rewrite-args`, the
blocks `bs`), every gate returns the noun of the model's `RM` step on `st`
and the state it leaves: `rewrite-jump` and `rewrite-hop` (`tsr_jmp`,
`tsr_hop`: `+chase`, then `tsr_args`), `rewrite-op` on each of the 25 tags
(`tsr_op_<tag>`, `tsr_op`: `rewriteOp rr`) and `rewrite-fin` on each
terminator (`tsr_fin_<tag>`, `tsr_fin`: `rewriteFin rr bs`), each `=^` one
step in the Hoon's order.  The stateless copies are track I's
`CompStraightMapOps.lean` (`tools/gen/tsmops.py`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The hypotheses on a core `[tsCoreBat [(rmN st) R]]` of the map path with
the state, for every `st`: the stateful `rer` `rr`, `layer2`, the bunt of the
units of `rewrite-args`, the blocks `bs`. -/
structure MapCoreM (bs : TreapMap mugF Blob) (rr : Nat → RM (TreapMap mugF) Nat) (R : Noun) : Prop where
  hrer : RerM rr R
  hL : slot? 0x7fffffff R = some layer2
  hU : ∀ J G, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G)
  hB : ∀ G, slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)

theorem rewriteJump_eq (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    rewriteJump rr bs j st = (chase bs true j).bind fun j' => rewriteArgs rr j' st := by
  unfold rewriteJump
  simp only [liftR, bind, StateT.bind]
  cases chase bs true j <;> rfl

theorem rewriteHop_eq (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    rewriteHop rr bs j st = (chase bs false j).bind fun j' => rewriteArgs rr j' st := by
  unfold rewriteHop
  simp only [liftR, bind, StateT.bind]
  cases chase bs false j <;> rfl

/-- **`rewrite-jump` with the state**: `(rewrite-args (chase & j))`. -/
theorem tsr_jmp {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (bs : TreapMap mugF Blob) (hrer : RerM rr R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J G, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G))
    (hB : ∀ G, slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    nock (C tsmJmpBody (C (Jmp.toNoun j) (C tsCoreBat (C (rmN st) R)))) tsmJmpBody
      = (rewriteJump rr bs j st).map fun p => C (Jmp.toNoun p.1) (rmN p.2) := by
  have hL' : slot? 0x1ffffffff (C tsCoreBat (C (rmN st) R)) = some layer2 := by simp [nock_exec, hL]
  have hY := (tsm_core_l2 (G := rmN st) hL).2
  have hch := ch_gate bs true (C tsCoreBat (C (rmN st) R)) (hB _) hL' hY j
  rw [show loob true = A 0 from rfl] at hch
  obtain ⟨h1519, h21⟩ := tsm_core_arms (rmN st) R
  rw [rewriteJump_eq]
  cases e : chase bs true j with
  | none =>
    rw [e] at hch
    generalize tsCoreBat = K at hch h1519 h21 ⊢
    conv => { lhs; arg 2; unfold tsmJmpBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, loob]
  | some j' =>
    rw [e] at hch
    have ha := tsr_args hrer hL hU j' st
    generalize tsCoreBat = K at hch h1519 h21 ha ⊢
    conv => { lhs; arg 2; unfold tsmJmpBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, ha, loob]

/-- **`rewrite-hop` with the state**: `(rewrite-args (chase | j))`. -/
theorem tsr_hop {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (bs : TreapMap mugF Blob) (hrer : RerM rr R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J G, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G))
    (hB : ∀ G, slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    nock (C tsmHopBody (C (Jmp.toNoun j) (C tsCoreBat (C (rmN st) R)))) tsmHopBody
      = (rewriteHop rr bs j st).map fun p => C (Jmp.toNoun p.1) (rmN p.2) := by
  have hL' : slot? 0x1ffffffff (C tsCoreBat (C (rmN st) R)) = some layer2 := by simp [nock_exec, hL]
  have hY := (tsm_core_l2 (G := rmN st) hL).2
  have hch := ch_gate bs false (C tsCoreBat (C (rmN st) R)) (hB _) hL' hY j
  rw [show loob false = A 1 from rfl] at hch
  obtain ⟨h1519, h21⟩ := tsm_core_arms (rmN st) R
  rw [rewriteHop_eq]
  cases e : chase bs false j with
  | none =>
    rw [e] at hch
    generalize tsCoreBat = K at hch h1519 h21 ⊢
    conv => { lhs; arg 2; unfold tsmHopBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, loob]
  | some j' =>
    rw [e] at hch
    have ha := tsr_args hrer hL hU j' st
    generalize tsCoreBat = K at hch h1519 h21 ha ⊢
    conv => { lhs; arg 2; unfold tsmHopBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, ha, loob]

theorem tsr_op_imm {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n : Noun) (d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.imm n d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.imm n d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr d st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.imm, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.imm, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_mov {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.mov s d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.mov s d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.mov, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.mov, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.mov, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_inc {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.inc s d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.inc s d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.inc, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.inc, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.inc, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_con {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (h t d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.con h t d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.con h t d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr h st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.con, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr t st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.con, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rr d st2 with
      | none =>
        simp [nock_exec, Pole.toNoun, Tag.con, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        simp [nock_exec, Pole.toNoun, Tag.con, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
theorem tsr_op_hed {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hed s d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hed s d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.hed, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.hed, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.hed, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_tal {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.tal s d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.tal s d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.tal, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.tal, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.tal, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_cel {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (p : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.cel p)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.cel p) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr p st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.cel, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.cel, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_lob {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (p : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.lob p)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.lob p) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr p st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.lob, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.lob, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_equ {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (l r : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.equ l r)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.equ l r) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr l st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.equ, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr r st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.equ, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.equ, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_hsp {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n : Nat) (f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hsp n f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hsp n f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, Tag.hsp, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure]
theorem tsr_op_hse {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n : Nat) (f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hse n f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hse n f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, Tag.hse, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure]
theorem tsr_op_hdp {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n p : Nat) (f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hdp n p f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hdp n p f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr p st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.hdp, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.hdp, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_hde {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n p : Nat) (f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hde n p f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hde n p f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr p st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.hde, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.hde, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_hmp {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hmp a v f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hmp a v f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.hmp, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.hmp, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_hme {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hme a v f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hme a v f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.hme, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Pole.toNoun, Tag.hme, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_op_hcp {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hcp n f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hcp n f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, Tag.hcp, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure]
theorem tsr_op_hce {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n f : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hce n f)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.hce n f) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, Tag.hce, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure]
theorem tsr_op_spy {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (e p d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.spy e p d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.spy e p d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr e st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.spy, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr p st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.spy, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rr d st2 with
      | none =>
        simp [nock_exec, Pole.toNoun, Tag.spy, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        simp [nock_exec, Pole.toNoun, Tag.spy, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
theorem tsr_op_nok {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (u f d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.nok u f d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.nok u f d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr u st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.nok, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr f st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.nok, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rr d st2 with
      | none =>
        simp [nock_exec, Pole.toNoun, Tag.nok, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        simp [nock_exec, Pole.toNoun, Tag.nok, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
theorem tsr_op_cal {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.cal a v d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.cal a v d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.cal, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.cal, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.cal, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_caf {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (d : Nat) (n : Ring) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.caf a v d n)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.caf a v d n) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.caf, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.caf, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.caf, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_cam {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (d : Nat) (k : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.cam a v d k)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.cam a v d k) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.cam, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.cam, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.cam, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_csl {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (s d : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.csl a s d)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.csl a s d) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.csl, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.csl, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.csl, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_csf {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (s d : Nat) (n : Ring) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.csf a s d n)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.csf a s d n) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.csf, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.csf, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.csf, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
theorem tsr_op_csm {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (s d : Nat) (k : Noun) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.csm a s d k)) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.csm a s d k) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Pole.toNoun, Tag.csm, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr d st1 with
    | none =>
      simp [nock_exec, Pole.toNoun, Tag.csm, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      simp [nock_exec, Pole.toNoun, Tag.csm, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, StateT.pure, e1, e2]
/-- **`rewrite-op` with the state** on any op: the model's `rewriteOp rr`. -/
theorem tsr_op {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hc : MapCoreM bs rr R)
    (op : Pole) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun op) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr op st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  cases op with
  | imm n d => exact tsr_op_imm hc n d st
  | mov s d => exact tsr_op_mov hc s d st
  | inc s d => exact tsr_op_inc hc s d st
  | con h t d => exact tsr_op_con hc h t d st
  | hed s d => exact tsr_op_hed hc s d st
  | tal s d => exact tsr_op_tal hc s d st
  | cel p => exact tsr_op_cel hc p st
  | lob p => exact tsr_op_lob hc p st
  | equ l r => exact tsr_op_equ hc l r st
  | hsp n f => exact tsr_op_hsp hc n f st
  | hse n f => exact tsr_op_hse hc n f st
  | hdp n p f => exact tsr_op_hdp hc n p f st
  | hde n p f => exact tsr_op_hde hc n p f st
  | hmp a v f => exact tsr_op_hmp hc a v f st
  | hme a v f => exact tsr_op_hme hc a v f st
  | hcp n f => exact tsr_op_hcp hc n f st
  | hce n f => exact tsr_op_hce hc n f st
  | spy e p d => exact tsr_op_spy hc e p d st
  | nok u f d => exact tsr_op_nok hc u f d st
  | cal a v d => exact tsr_op_cal hc a v d st
  | caf a v d n => exact tsr_op_caf hc a v d n st
  | cam a v d k => exact tsr_op_cam hc a v d k st
  | csl a s d => exact tsr_op_csl hc a s d st
  | csf a s d n => exact tsr_op_csf hc a s d n st
  | csm a s d k => exact tsr_op_csm hc a s d k st

theorem tsr_fin_clq {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s : Nat) (z o : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.clq s z o)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.clq s z o) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rewriteJump rr bs z st1 with
    | none =>
      simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rewriteJump rr bs o st2 with
      | none =>
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
theorem tsr_fin_eqq {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (l r : Nat) (z o : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.eqq l r z o)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.eqq l r z o) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr l st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rr r st1 with
    | none =>
      simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rewriteJump rr bs z st2 with
      | none =>
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        cases e4 : rewriteJump rr bs o st3 with
        | none =>
          simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3, e4]
        | some p4 =>
          obtain ⟨_, st4⟩ := p4
          simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3, e4]
theorem tsr_fin_brn {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s : Nat) (z o : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.brn s z o)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.brn s z o) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rewriteJump rr bs z st1 with
    | none =>
      simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rewriteJump rr bs o st2 with
      | none =>
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
theorem tsr_fin_brz {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s : Nat) (z o : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.brz s z o)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.brz s z o) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    cases e2 : rewriteJump rr bs z st1 with
    | none =>
      simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2]
    | some p2 =>
      obtain ⟨_, st2⟩ := p2
      cases e3 : rewriteJump rr bs o st2 with
      | none =>
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
      | some p3 =>
        obtain ⟨_, st3⟩ := p3
        simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]
theorem tsr_fin_hop {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (t : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.hop t)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.hop t) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rewriteHop rr bs t st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_fin_jmp {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jmp a v)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.jmp a v) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_fin_jmf {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (v : List Nat) (n : Ring) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jmf a v n)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.jmf a v n) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rewritePar rr v st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_fin_jsp {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (s : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jsp a s)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.jsp a s) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_fin_jsf {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (a : Bell) (s : Nat) (n : Ring) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jsf a s n)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.jsf a s n) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_fin_don {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (s : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.don s)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.don s) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  cases e1 : rr s st with
  | none =>
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
  | some p1 =>
    obtain ⟨_, st1⟩ := p1
    simp [nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, StateT.bind, pure, StateT.pure, e1]
theorem tsr_fin_bom_none {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.bom Option.none)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.bom Option.none) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K
  simp [nock_exec, Termin.toNoun, unitNoun, rewriteFin, pure, StateT.pure, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

theorem tsr_fin_bom_some {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (x : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.bom (some x))) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.bom (some x)) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  obtain ⟨hL', hY⟩ := tsm_core_l2 (G := rmN st) hc.hL
  have ht := ch_gate bs true (C tsCoreBat (C (rmN st) R)) (hc.hB _) hL' hY ⟨[], x⟩
  rw [show loob true = A 0 from rfl] at ht
  simp only [Jmp.toNoun, listNoun] at ht
  have h21 := (tsm_core_arms (rmN st) R).2
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at ht h21 ⊢
  cases et : chase bs true ⟨[], x⟩ <;> rw [et] at ht <;>
    simp [nock_exec, Termin.toNoun, Jmp.toNoun, listNoun, unitNoun, rewriteFin, liftR, bind, StateT.bind, pure,
      StateT.pure, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, h21, tsChaseArm, ht, et]

theorem tsr_fin_lti {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun}
    (hc : MapCoreM bs rr R) (n s : Nat) (z o : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.lti n s z o)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.lti n s z o) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hx := tsm_chase_cell (hc.hB (rmN st)) hc.hL (A 0) (A s) (C (Jmp.toNoun z) (Jmp.toNoun o))
  have h21 := (tsm_core_arms (rmN st) R).2
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hx h21 ⊢
  simp [nock_exec, Termin.toNoun, rewriteFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, h21, tsChaseArm, hx]

/-- **`rewrite-fin` with the state** on any terminator: the model's
`rewriteFin rr bs`, a crash where it is `none`. -/
theorem tsr_fin {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hc : MapCoreM bs rr R)
    (fin : Termin) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun fin) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs fin st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  cases fin with
  | clq s z o => exact tsr_fin_clq hc s z o st
  | eqq l r z o => exact tsr_fin_eqq hc l r z o st
  | brn s z o => exact tsr_fin_brn hc s z o st
  | brz s z o => exact tsr_fin_brz hc s z o st
  | hop t => exact tsr_fin_hop hc t st
  | jmp a v => exact tsr_fin_jmp hc a v st
  | jmf a v n => exact tsr_fin_jmf hc a v n st
  | jsp a s => exact tsr_fin_jsp hc a s st
  | jsf a s n => exact tsr_fin_jsf hc a s n st
  | don s => exact tsr_fin_don hc s st
  | bom o =>
    cases o with
    | none => exact tsr_fin_bom_none hc st
    | some x => exact tsr_fin_bom_some hc x st
  | lti n s z o => exact tsr_fin_lti hc n s z o st

end Compiler
end Formalization
