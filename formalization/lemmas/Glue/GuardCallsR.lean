import lemmas.Glue.GuardCallsK
import lemmas.Glue.GuardCallsL

/-!
# `RunG` of every arm of `runLCM env true` with no `%6` (track G, tenth pass)

LEDGER 2.c, toward `GuardMonoC`.  Over `KPA` (`Glue/GuardCallsA.lean`)
with the `DN` goals of `Glue/GuardCallsB.lean`: every run of
`runLCM env true sup nm` on a nomm with no `%6` (`NoSixC`), for a goal
whose jumps are `FL` and pass no `~` and whose lazy has `DN` entries, keeps
`InvA` and returns a `RN` result (`runG_lcm`), under the mid-run fact
`KIMid` (the `DN` of the sub-runs' results and of `+split`'s and `+into`'s
halves; `+kerf` itself is `kerfG`, proved).

* `rs_run`, `rs_split`, `rs_into`: `KIMid` as `RS` facts, for `KPA.andR`.
* The arms: `runG_cons`, `runG_n0`, `runG_n1`, `runG_n3`, `runG_n4`,
  `runG_n5`, `runG_n7`, `runG_n10`, `runG_n2` (the direct call
  `kpa_callDMG` and the indirect call `kpa_callLI`), the rest fail.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## The mid-run fact as `RS` -/

/-- **A run keeps `DN`** (from `KIMid`). -/
def RunR (run : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (r0 : Nat) (goal : CGoalL S) region, GD r0 goal → RS (Map := Map) r0 (fun r (n : NextL S) => LzS (DN r) n.laz) (run goal region)

theorem rs_run {env : CallEnv} (hD : KIMid S Map env) {nm : Nomm} (hn : NoSixC nm) (sup : Option Nomm) :
    RunR (runLCM (S := S) (Map := Map) env true sup nm) :=
  fun r0 goal region hd g x g' hr e => hD.run nm sup hn goal region g g' x (hd.up hr) e

theorem rs_split {env : CallEnv} (hD : KIMid S Map env) {r0 : Nat} {nex : NextL S} (h : LzS (DN r0) nex.laz) :
    RS (Map := Map) r0 (fun r (x : Lazy S × Lazy S × Nat) => LzS (DN r) x.1 ∧ LzS (DN r) x.2.1) (splitL nex) :=
  fun g x g' hr e => hD.split nex g g' x (h.upD hr) e

theorem rs_into {env : CallEnv} (hD : KIMid S Map env) {r0 : Nat} {nex : NextL S} (h : LzS (DN r0) nex.laz)
    (axe : Nat) :
    RS (Map := Map) r0 (fun r (x : Lazy S × Lazy S × Nat) => LzS (DN r) x.1 ∧ LzS (DN r) x.2.1) (intoL nex axe) :=
  fun g x g' hr e => hD.into nex axe g g' x (h.upD hr) e

/-! ## Small pieces -/

theorem fl_two {K : Nat → Nat → Prop} {b : Nat} {z o : Jmp} {fin : Termin} (hf : getJmps fin = [z, o])
    (hz : FL K b z.there) (ho : FL K b o.there) : ∀ j ∈ getJmps fin, FL K b j.there := by
  intro j hj; rw [hf] at hj
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact hz
  · exact ho

theorem jok_two {z o : Jmp} {fin : Termin} (hf : getJmps fin = [z, o]) (hz : JOK z) (ho : JOK o) :
    ∀ j ∈ getJmps fin, JOK j := by
  intro j hj; rw [hf] at hj
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact hz
  · exact ho

theorem fl_one {K : Nat → Nat → Prop} {b : Nat} {z : Jmp} (hz : FL K b z.there) :
    ∀ j ∈ getJmps (Termin.hop z), FL K b j.there := by
  intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact hz

theorem fl_none {K : Nat → Nat → Prop} {b : Nat} {fin : Termin} (hf : getJmps fin = []) :
    ∀ j ∈ getJmps fin, FL K b j.there := by
  intro j hj; rw [hf] at hj; exact absurd hj List.not_mem_nil

theorem jok_none {fin : Termin} (hf : getJmps fin = []) : ∀ j ∈ getJmps fin, JOK j := by
  intro j hj; rw [hf] at hj; exact absurd hj List.not_mem_nil

/-! ## The arms -/

section arms

variable (env : CallEnv) (sup : Option Nomm)

theorem runG_n0 (ax : Nat) : RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n0 ax)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.ite' _ (fun _ => kpa_bombL _) fun _ => ?_
  refine KPA.bind' (kpa_simpleNextL hg) fun nex K1 b1 r1 X1 hn => ?_
  refine KPA.ite' _ (fun _ => KPA.pure' fun K b r X => ⟨hn.1.up X, hn.2.1, hn.2.2.up X⟩) fun _ => ?_
  split
  · rename_i laz e
    exact KPA.pure' fun K b r X => ⟨hn.1.up X, hn.2.1, lzL_fromL e (hn.2.2.up X)⟩
  · exact KPA.fail

theorem runG_n1 (k : Noun) : RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n1 k)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases goal with
  | done =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 _ => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (jok_none rfl)) (fl_none rfl)) fun o K2 b2 r2 X2 ho => ?_
    exact KPA.pure' fun K b r X => ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _⟩
  | pick z o =>
    refine KPA.ite' _ (fun _ => KPA.pure' fun K b r X => ⟨hg.1.up X, hg.2.1, lzL_ofSure _ _⟩) fun _ => ?_
    refine KPA.ite' _ (fun _ => KPA.pure' fun K b r X => ⟨hg.2.2.1.up X, hg.2.2.2, lzL_ofSure _ _⟩) fun _ => ?_
    exact kpa_bombL _
  | next laz th =>
    refine KPA.bind' (kpa_medeL hg.1 hg.2.1 k hg.2.2) fun o K1 b1 r1 X1 ho => ?_
    exact KPA.pure' fun K b r X => ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _⟩

theorem runG_n3 {p : Nomm} (ih : RunG (runLCM (S := S) (Map := Map) env true sup p)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n3 p)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases goal with
  | next laz th =>
    refine KPA.ite' _ (fun _ => ih _ _ _ _ _ hg hd) fun _ => ?_
    refine KPA.bind' (kpa_collapseLazyAtomL (nex := ⟨laz, th⟩) hg) fun a K1 b1 r1 X1 ha => ?_
    split
    · exact KPA.fail
    · rename_i r o
      refine KPA.bind' (kpa_forl r o (ha (r, o) rfl)) fun x K2 b2 r2 X2 hx => ?_
      obtain ⟨z, o'⟩ := x
      refine KPA.bind' KPA.re' fun r' K3 b3 r3 X3 hr' => ?_
      refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _)))
        (fl_two rfl (hx.1.up X3) (hx.2.up X3))) fun oc K4 b4 r4 X4 hoc => ?_
      exact ih _ _ _ _ _ (gfl_next hoc (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up hr'.2 X4))
  | pick z o =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_two rfl hg.2.1 hg.2.2.2))
      (fl_two rfl (hg.1.up X1) (hg.2.2.1.up X1))) fun oc K2 b2 r2 X2 hoc => ?_
    exact ih _ _ _ _ _ (gfl_next hoc (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up hr.2 X2))
  | done =>
    refine KPA.bind' kpa_doneBlocks fun x K1 b1 r1 X1 hx => ?_
    obtain ⟨o0, o1⟩ := x
    refine KPA.bind' KPA.re' fun r K2 b2 r2 X2 hr => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _)))
      (fl_two rfl (hx.1.up X2) (hx.2.up X2))) fun oc K3 b3 r3 X3 hoc => ?_
    exact ih _ _ _ _ _ (gfl_next hoc (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up hr.2 X3))

theorem runG_n4 {p : Nomm} (ih : RunG (runLCM (S := S) (Map := Map) env true sup p)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n4 p)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases goal with
  | done =>
    refine KPA.bind' KPA.re' fun pro K1 b1 r1 X1 _ => ?_
    refine KPA.bind' KPA.re' fun arg K2 b2 r2 X2 harg => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (jok_none rfl)) (fl_none rfl)) fun o K3 b3 r3 X3 ho => ?_
    exact ih _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up harg.2 X3))
  | pick z o =>
    refine KPA.bind' KPA.re' fun pro K1 b1 r1 X1 _ => ?_
    refine KPA.bind' KPA.re' fun arg K2 b2 r2 X2 harg => ?_
    have X12 := X1.trans X2
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (jok_two rfl hg.2.1 hg.2.2.2))
      (fl_two rfl (hg.1.up X12) (hg.2.2.1.up X12))) fun o K3 b3 r3 X3 ho => ?_
    exact ih _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up harg.2 X3))
  | next laz th =>
    refine KPA.bind' (kpa_collapseLazyAtomL (nex := ⟨laz, th⟩) hg) fun a K1 b1 r1 X1 ha => ?_
    refine KPA.bind' (P := fun K b _ (x : Nat × Nat) => FL K b x.2) ?_ fun x K2 b2 r2 X2 hx => ?_
    · split
      · rename_i x
        exact KPA.pure' fun K b r X => (ha x rfl).up X
      · refine KPA.bind' KPA.re' fun r K2 b2 r2 X2 _ => ?_
        exact KPA.ite' _ (fun _ => KPA.pure' fun K b r' X => (hg.1.up (X1.trans X2)).up X) fun _ => KPA.fail
    · obtain ⟨pro, th'⟩ := x
      refine KPA.bind' KPA.re' fun arg K3 b3 r3 X3 harg => ?_
      refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0]))
        (fl_one (hx.up X3))) fun o K4 b4 r4 X4 ho => ?_
      exact ih _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up harg.2 X4))

/-- The two runs, `+past` and `+copy` of `%5` and of the indirect tail. -/
theorem kpa_twoRegs {p q : Nomm} (ihp : RunG (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunG (runLCM (S := S) (Map := Map) env true sup q)) {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    {rp rq o : Nat} (hrp : rp < r0) (hrq : rq < r0) (ho : FL K0 b0 o) (region : List Nat) :
    KPA K0 b0 r0 RN (do
      let nexq ← runLCM env true sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCM env true sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz : CM Map (NextL S)) := by
  refine KPA.bind' (ihq _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg hrq))
    fun n1 K1 b1 r1 X1 h1 => ?_
  refine KPA.bind' (kpa_pastL env.cod h1 p region) fun n2 K2 b2 r2 X2 h2 => ?_
  refine KPA.bind' (ihp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (lzL_ofSure _ _)) (lzS_reg (lt_up (lt_up hrp X1) X2)))
    fun n3 K3 b3 r3 X3 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X3)

theorem runG_n5 {p q : Nomm} (ihp : RunG (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunG (runLCM (S := S) (Map := Map) env true sup q)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n5 p q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' KPA.re' fun rp K1 b1 r1 X1 hrp => ?_
  refine KPA.bind' KPA.re' fun rq K2 b2 r2 X2 hrq => ?_
  have X12 := X1.trans X2
  refine KPA.bind' (P := fun K b _ (o : Nat) => FL K b o) ?_ fun o K3 b3 r3 X3 ho =>
    kpa_twoRegs env sup ihp ihq (lt_up (lt_up hrp.2 X2) X3) (lt_up hrq.2 X3) ho region
  cases goal with
  | pick z o =>
    exact KPA.emit' (blockOK_nil _ _ (jok_two rfl hg.2.1 hg.2.2.2)) (fl_two rfl (hg.1.up X12) (hg.2.2.1.up X12))
  | done =>
    refine KPA.bind' kpa_doneBlocks fun x K3 b3 r3 X3 hx => ?_
    obtain ⟨o0, o1⟩ := x
    exact KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _))) (fl_two rfl hx.1 hx.2)
  | next laz th =>
    refine KPA.bind' (kpa_collapseLazyAtomL (nex := ⟨laz, th⟩) (RN.up (rr := r0) (n := ⟨laz, th⟩) hg X12 r2)) fun a K3 b3 r3 X3 ha => ?_
    split
    · refine KPA.ite' _ (fun _ => ?_) fun _ => KPA.fail
      exact KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) (fl_one ((hg.1.up X12).up X3))
    · rename_i r o
      refine KPA.bind' (kpa_forl r o (ha (r, o) rfl)) fun x K4 b4 r4 X4 hx => ?_
      obtain ⟨z, o'⟩ := x
      exact KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _))) (fl_two rfl hx.1 hx.2)

theorem runG_n7 {p q : Nomm} (ihp : RunG (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunG (runLCM (S := S) (Map := Map) env true (some p) q))
    (dq : RunR (runLCM (S := S) (Map := Map) env true (some p) q)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n7 p q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' (KPA.andR (ihq _ _ _ _ _ hg hd) (dq _ _ _ hd)) fun nex K1 b1 r1 X1 hn => ?_
  exact ihp _ _ _ _ _ (gfl_next hn.1.1 hn.1.2.1 hn.1.2.2) hn.2

theorem runG_cons (hD : KIMid S Map env) {p q : Nomm} (ihp : RunG (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunG (runLCM (S := S) (Map := Map) env true sup q)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.cons p q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' (P := fun K b r (goal' : CGoalL S) => GFL K b goal' ∧ GD r goal') ?_ fun goal' K1 b1 r1 X1 hg1 => ?_
  · cases goal with
    | done =>
      refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => ?_
      refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_none rfl)) (fl_none rfl)) fun o K2 b2 r2 X2 ho => ?_
      exact KPA.pure' fun K b r' X => ⟨gfl_next (ho.up X) (jok_jmp0 _) (lzL_ofSure _ _),
        lzS_reg (lt_up (lt_up hr.2 X2) X)⟩
    | pick z o => exact KPA.pure' fun K b r X => ⟨hg.up X, trivial⟩
    | next laz th => exact KPA.pure' fun K b r X => ⟨hg.up X, GD.up (goal := CGoalL.next laz th) hd X.2.1⟩
  obtain ⟨hg1, hd1⟩ := hg1
  cases goal' with
  | pick z o =>
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_none rfl)) (fl_none rfl)) fun o K2 b2 r2 X2 ho => ?_
    refine KPA.bind' (ihq _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_bunt _))
      fun n1 K3 b3 r3 X3 h1 => ?_
    refine KPA.bind' (kpa_pastL env.cod h1 p region) fun n2 K4 b4 r4 X4 h2 => ?_
    refine KPA.bind' (ihp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (lzL_ofSure _ _)) (lzS_bunt _))
      fun n3 K5 b5 r5 X5 h3 => ?_
    exact kpa_copyL h3 (h2.2.2.up X5)
  | next laz th =>
    refine KPA.bind' (KPA.andR (kpa_splitL (nex := ⟨laz, th⟩) hg1) (rs_split hD (nex := ⟨laz, th⟩) hd1))
      fun x K2 b2 r2 X2 hx => ?_
    obtain ⟨hed, tel, o⟩ := x
    obtain ⟨⟨lh, lt, lo⟩, dh, dt⟩ := hx
    refine KPA.bind' (KPA.andR (kpa_pastL (nex := ⟨hed, jmp0 o⟩) env.cod ⟨lo, jok_jmp0 _, lh⟩ q region)
      (rs_pastL env.cod (nex := ⟨hed, jmp0 o⟩) dh q region)) fun nh K3 b3 r3 X3 hh => ?_
    refine KPA.bind' (ihq _ _ _ _ _ (gfl_next hh.1.1 hh.1.2.1 (lt.up X3)) (dt.upD X3.2.1))
      fun n2 K4 b4 r4 X4 h2 => ?_
    refine KPA.bind' (kpa_pastL env.cod h2 p region) fun n2' K5 b5 r5 X5 h2' => ?_
    have X45 := X4.trans X5
    refine KPA.bind' (ihp _ _ _ _ _ (gfl_next h2'.1 h2'.2.1 (hh.1.2.2.up X45)) (hh.2.upD X45.2.1))
      fun n1 K6 b6 r6 X6 h1 => ?_
    exact kpa_copyL h1 (h2'.2.2.up X6)
  | done => exact KPA.fail

theorem runG_n10 (hD : KIMid S Map env) {a : Nat} {v q : Nomm} (ihv : RunG (runLCM (S := S) (Map := Map) env true sup v))
    (ihq : RunG (runLCM (S := S) (Map := Map) env true sup q)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n10 a v q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' (kpa_simpleNextLG hg hd) fun nex K1 b1 r1 X1 hn => ?_
  refine KPA.bind' (KPA.andR (kpa_intoL (nex := nex) ⟨hn.1, hn.2.1, hn.2.2.1⟩ a) (rs_into hD hn.2.2.2 a))
    fun x K2 b2 r2 X2 hx => ?_
  obtain ⟨don, rec, o⟩ := x
  obtain ⟨⟨ld, lr, lo⟩, dd, dr⟩ := hx
  refine KPA.bind' (KPA.andR (kpa_pastL (nex := ⟨rec, jmp0 o⟩) env.cod ⟨lo, jok_jmp0 _, lr⟩ v region)
    (rs_pastL env.cod (nex := ⟨rec, jmp0 o⟩) dr v region)) fun nr K3 b3 r3 X3 hr => ?_
  refine KPA.bind' (ihv _ _ _ _ _ (gfl_next hr.1.1 hr.1.2.1 (ld.up X3)) (dd.upD X3.2.1))
    fun n2 K4 b4 r4 X4 h2 => ?_
  refine KPA.bind' (kpa_pastL env.cod h2 q region) fun n2' K5 b5 r5 X5 h2' => ?_
  have X45 := X4.trans X5
  refine KPA.bind' (ihq _ _ _ _ _ (gfl_next h2'.1 h2'.2.1 (hr.1.2.2.up X45)) (hr.2.upD X45.2.1))
    fun n1 K6 b6 r6 X6 h1 => ?_
  exact kpa_copyL h1 (h2'.2.2.up X6)

theorem runG_n2 {p q : Nomm} (info : Option (Bell × Option Noun))
    (ihp : RunG (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunG (runLCM (S := S) (Map := Map) env true sup q)) :
    RunG (runLCM (S := S) (Map := Map) env true sup (Nomm.n2 p q info)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases info with
  | none => exact kpa_callLI kerfG env ihp ihq p q sup hg hd region
  | some bk =>
    obtain ⟨b, key⟩ := bk
    exact kpa_callDMG kerfG env ihp ihq p q b key hg hd region

end arms

/-! ## The induction -/

/-- **Every run of `runLCM env true` on a nomm with no `%6` keeps `InvA`**,
for a goal with `FL` jumps and `DN` entries, and returns a `RN` result,
under the mid-run fact `KIMid`. -/
theorem runG_lcm {env : CallEnv} (hD : KIMid S Map env) :
    ∀ (nm : Nomm), NoSixC nm → ∀ sup, RunG (runLCM (S := S) (Map := Map) env true sup nm)
  | Nomm.cons p q, h, sup => runG_cons env sup hD (runG_lcm hD p h.1 sup) (runG_lcm hD q h.2 sup)
  | Nomm.n0 ax, _, sup => runG_n0 env sup ax
  | Nomm.n1 k, _, sup => runG_n1 env sup k
  | Nomm.n2 p q info, h, sup => runG_n2 env sup info (runG_lcm hD p h.1 sup) (runG_lcm hD q h.2 sup)
  | Nomm.n3 p, h, sup => runG_n3 env sup (runG_lcm hD p h sup)
  | Nomm.n4 p, h, sup => runG_n4 env sup (runG_lcm hD p h sup)
  | Nomm.n5 p q, h, sup => runG_n5 env sup (runG_lcm hD p h.1 sup) (runG_lcm hD q h.2 sup)
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n7 p q, h, sup => runG_n7 env sup (runG_lcm hD p h.1 sup) (runG_lcm hD q h.2 (some p))
      (rs_run hD h.2 (some p))
  | Nomm.n10 a v q, h, sup => runG_n10 env sup hD (runG_lcm hD v h.1 sup) (runG_lcm hD q h.2 sup)
  | Nomm.n11s _ _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail
  | Nomm.n11d _ _ _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail
  | Nomm.n12 _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail
  | Nomm.mean _ _ _ _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail

end Glue
end SkaModel
end Formalization
