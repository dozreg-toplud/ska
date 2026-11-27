import lemmas.Compiler.CompStraightMap

/-!
# The map path of `+to-straight`: `rewrite-op` and `rewrite-fin`

Written by `tools/gen/tsmops.py` (README Gaps 20).  In a core whose `rer`
renames by `f` and keeps `gen` (`MapCoreS`), `rewrite-op` on each of the 25
op tags is `renPole f` with `gen` kept (`tsm_op_<tag>`, `tsm_op`), as
`rewriteOp_stateless` of the model; `rewrite-fin` on each terminator is
`chaseFin bs f` (`tsm_fin_<tag>`, `tsm_fin`), as `rewriteFin_stateless`:
the registers through `rer`, the branch jumps through `rewrite-jump`, the
hop through `rewrite-hop`, `%bom` through `+chase`.  `%lti` falls into the
last case (`%bom`, under `%toss`) and crashes, as the model's `none`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The hypotheses on a core `[tsCoreBat [G R]]` of the map path: the
stateless `rer`, `layer2`, the bunt of the units of `rewrite-args`, the
blocks `bs`. -/
structure MapCoreS (bs : TreapMap mugF Blob) (f : Nat → Nat) (G R : Noun) : Prop where
  hrer : RerS f G R
  hL : slot? 0x7fffffff R = some layer2
  hU : ∀ J, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (A 0)
  hB : slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)


theorem tsm_op_imm {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n : Noun) (d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.imm n d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.imm n d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.imm, hra, hrer, hpa, hp]

theorem tsm_op_mov {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.mov s d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.mov s d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.mov, hra, hrer, hpa, hp]

theorem tsm_op_inc {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.inc s d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.inc s d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.inc, hra, hrer, hpa, hp]

theorem tsm_op_con {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (h t d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.con h t d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.con h t d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.con, hra, hrer, hpa, hp]

theorem tsm_op_hed {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hed s d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hed s d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hed, hra, hrer, hpa, hp]

theorem tsm_op_tal {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.tal s d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.tal s d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.tal, hra, hrer, hpa, hp]

theorem tsm_op_cel {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (p : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.cel p)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.cel p))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.cel, hra, hrer, hpa, hp]

theorem tsm_op_lob {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (p : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.lob p)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.lob p))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.lob, hra, hrer, hpa, hp]

theorem tsm_op_equ {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (l r : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.equ l r)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.equ l r))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.equ, hra, hrer, hpa, hp]

theorem tsm_op_hsp {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n : Nat) (f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hsp n f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hsp n f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hsp, hra, hrer, hpa, hp]

theorem tsm_op_hse {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n : Nat) (f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hse n f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hse n f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hse, hra, hrer, hpa, hp]

theorem tsm_op_hdp {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n p : Nat) (f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hdp n p f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hdp n p f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hdp, hra, hrer, hpa, hp]

theorem tsm_op_hde {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n p : Nat) (f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hde n p f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hde n p f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hde, hra, hrer, hpa, hp]

theorem tsm_op_hmp {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) (f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hmp a v f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hmp a v f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hmp, hra, hrer, hpa, hp]

theorem tsm_op_hme {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) (f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hme a v f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hme a v f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hme, hra, hrer, hpa, hp]

theorem tsm_op_hcp {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hcp n f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hcp n f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hcp, hra, hrer, hpa, hp]

theorem tsm_op_hce {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n f : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.hce n f)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.hce n f))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.hce, hra, hrer, hpa, hp]

theorem tsm_op_spy {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (e p d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.spy e p d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.spy e p d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.spy, hra, hrer, hpa, hp]

theorem tsm_op_nok {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (u f d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.nok u f d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.nok u f d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.nok, hra, hrer, hpa, hp]

theorem tsm_op_cal {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) (d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.cal a v d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.cal a v d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.cal, hra, hrer, hpa, hp]

theorem tsm_op_caf {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) (d : Nat) (n : Ring) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.caf a v d n)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.caf a v d n))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.caf, hra, hrer, hpa, hp]

theorem tsm_op_cam {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) (d : Nat) (k : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.cam a v d k)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.cam a v d k))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.cam, hra, hrer, hpa, hp]

theorem tsm_op_csl {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (s d : Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.csl a s d)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.csl a s d))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.csl, hra, hrer, hpa, hp]

theorem tsm_op_csf {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (s d : Nat) (n : Ring) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.csf a s d n)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.csf a s d n))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.csf, hra, hrer, hpa, hp]

theorem tsm_op_csm {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (s d : Nat) (k : Noun) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.csm a s d k)) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.csm a s d k))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.csm, hra, hrer, hpa, hp]

/-- **`rewrite-op`** on any op: `renPole rn op`, `gen` kept. -/
theorem tsm_op {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R) (op : Pole) :
    nock (C tsmOpBody (C (Pole.toNoun op) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn op)) G) := by
  cases op with
  | imm n d => exact tsm_op_imm hc n d
  | mov s d => exact tsm_op_mov hc s d
  | inc s d => exact tsm_op_inc hc s d
  | con h t d => exact tsm_op_con hc h t d
  | hed s d => exact tsm_op_hed hc s d
  | tal s d => exact tsm_op_tal hc s d
  | cel p => exact tsm_op_cel hc p
  | lob p => exact tsm_op_lob hc p
  | equ l r => exact tsm_op_equ hc l r
  | hsp n f => exact tsm_op_hsp hc n f
  | hse n f => exact tsm_op_hse hc n f
  | hdp n p f => exact tsm_op_hdp hc n p f
  | hde n p f => exact tsm_op_hde hc n p f
  | hmp a v f => exact tsm_op_hmp hc a v f
  | hme a v f => exact tsm_op_hme hc a v f
  | hcp n f => exact tsm_op_hcp hc n f
  | hce n f => exact tsm_op_hce hc n f
  | spy e p d => exact tsm_op_spy hc e p d
  | nok u f d => exact tsm_op_nok hc u f d
  | cal a v d => exact tsm_op_cal hc a v d
  | caf a v d n => exact tsm_op_caf hc a v d n
  | cam a v d k => exact tsm_op_cam hc a v d k
  | csl a s d => exact tsm_op_csl hc a s d
  | csf a s d n => exact tsm_op_csf hc a s d n
  | csm a s d k => exact tsm_op_csm hc a s d k

theorem tsm_fin_clq {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s : Nat) (z o : Jmp) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.clq s z o)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.clq s z o)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := And.intro (hj z) (hj o)
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha HX ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja HX ⊢
  generalize tsmHopBody = HB at hh hha HX ⊢
  obtain ⟨hz, ho⟩ := HX
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, hz, ho, ez, eo]

theorem tsm_fin_eqq {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (l r : Nat) (z o : Jmp) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.eqq l r z o)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.eqq l r z o)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := And.intro (hj z) (hj o)
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha HX ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja HX ⊢
  generalize tsmHopBody = HB at hh hha HX ⊢
  obtain ⟨hz, ho⟩ := HX
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, hz, ho, ez, eo]

theorem tsm_fin_brn {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s : Nat) (z o : Jmp) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.brn s z o)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.brn s z o)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := And.intro (hj z) (hj o)
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha HX ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja HX ⊢
  generalize tsmHopBody = HB at hh hha HX ⊢
  obtain ⟨hz, ho⟩ := HX
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, hz, ho, ez, eo]

theorem tsm_fin_brz {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s : Nat) (z o : Jmp) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.brz s z o)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.brz s z o)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := And.intro (hj z) (hj o)
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha HX ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja HX ⊢
  generalize tsmHopBody = HB at hh hha HX ⊢
  obtain ⟨hz, ho⟩ := HX
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, hz, ho, ez, eo]

theorem tsm_fin_hop {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (t : Jmp) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.hop t)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.hop t)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := hh t
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha HX ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja HX ⊢
  generalize tsmHopBody = HB at hh hha HX ⊢
  cases et : chase bs false t <;> rw [et] at HX <;>
    simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh, HX, et]

theorem tsm_fin_jmp {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jmp a v)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.jmp a v)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := True.intro
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh]

theorem tsm_fin_jmf {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (v : List Nat) (n : Ring) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jmf a v n)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.jmf a v n)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := True.intro
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh]

theorem tsm_fin_jsp {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (s : Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jsp a s)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.jsp a s)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := True.intro
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh]

theorem tsm_fin_jsf {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (a : Bell) (s : Nat) (n : Ring) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.jsf a s n)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.jsf a s n)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := True.intro
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh]

theorem tsm_fin_don {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (s : Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.don s)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.don s)).map fun t => C (Termin.toNoun t) G := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  have HX := True.intro
  have HY := True.intro
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
  simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hra, hrer, hpa, hp, hja, hj, hha, hh]

end Compiler
end Formalization
