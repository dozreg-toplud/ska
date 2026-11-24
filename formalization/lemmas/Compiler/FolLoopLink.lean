import lemmas.Compiler.RecCall
import lemmas.Pill.Arm.Fol_loop
import lemmas.Pill.Arm.Ska_analyze
import lemmas.Pill.Arm.Ska_cg
import lemmas.Iter

/-!
The trap `fol-loop` of `+run` against `Ana.folStep` of `Ska/Analysis.lean`,
case by case of its `?+`, with the calls of the trap to itself as the
parameter `go` (and `resolve` as `res`).

The trap is the core `[fol_loop.battery payload]`, whose payload holds the
variables of `+run` that the trap reads and changes, pushed in this order
(`folSubj`): `defer` at axis `6`, `bare-call` at `14`, `memo-key` at `30`,
`seat` at `62`, `gen` at `126`, `sub` at `254`, `fol` at `510`, and the rest of
the subject of `+run` (`rest`) at `511`.  A call of the trap to itself edits
some of these and kicks the battery: `go` says what such a run returns, as the
noun of `FolOut` and `GenS` (`folOutNoun`).

The cases that read the library core or `ana` assume `ana` at axis `511` of
`rest` (`hana`); `%spot` assumes `SoftSpotIs` and `%fast` `RegisterFastIs`.
`fol_loop_step` puts every case but `%2` together.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-- A noun cut at depth `n`, cheap to compare where a battery is not. -/
def ftrunc : Nat → Noun → Noun
  | 0, _ => A 0
  | _ + 1, Noun.atom a => A a
  | n + 1, Noun.cell x y => C (ftrunc n x) (ftrunc n y)

/-- A formula that is none of those whose calls the induction on the depth
of calls follows: the trap's battery, the traps `nock-2-direct-non-inlined`
and `resolve`, the gate `+analyze`, and (for the induction that will
discharge `AnaIs`) the gate `+run`, the pass and member loops of `+analyze`,
the loop of `+sweep` and the loop `live` of `+cull`.  The case theorems are
stated for `nockW c` with `c` equal to `nock` on every such formula. -/
def FFar (f : Noun) : Prop :=
  ftrunc 8 f ≠ ftrunc 8 fol_loop.battery ∧ ftrunc 8 f ≠ ftrunc 8 fol_loop.resolve ∧
    ftrunc 8 f ≠ ftrunc 8 fol_loop.direct ∧ ftrunc 8 f ≠ ftrunc 8 ska_analyze.battery ∧
    ftrunc 8 f ≠ ftrunc 8 ska_run.battery ∧ ftrunc 8 f ≠ ftrunc 8 ska_analyze.loop0 ∧
    ftrunc 8 f ≠ ftrunc 8 ska_analyze.loop1 ∧ ftrunc 8 f ≠ ftrunc 8 ska_cg.sweep.loop ∧
    ftrunc 8 f ≠ ftrunc 8 ska_cg.cull.loop

instance : DecidablePred FFar := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Open the formula of a goal `nockW c subject formula = _`. -/
syntax "nockW_open " ident : tactic

macro_rules
  | `(tactic| nockW_open $name:ident) =>
    `(tactic| conv => { lhs; arg 3; unfold $name:ident })

/-- The side conditions `FFar f` of `hcf` in a `simp` run of a battery: the
kernel compares the cuts of `f` and of the four formulas. -/
macro "ffar_disch" : tactic => `(tactic| (show FFar _; decide))

set_option linter.unusedSimpArgs false

/-- The subject of the trap `fol-loop`. -/
noncomputable def folSubj (regsNoun : R → Noun) (rest fol : Noun) (sub : Anno) (seat mk : Option Noun)
    (bc df : Bool) (gen : GenS FinMap R) : Noun :=
  C fol_loop.battery (C (flag df) (C (flag bc) (C (unitNoun id mk) (C (unitNoun id seat)
    (C (gen.toNoun regsNoun) (C sub.toNoun (C fol rest)))))))

/-- The noun of a result of `fol-loop`: `[[nomm prod saf] gen]`. -/
noncomputable def folOutNoun (regsNoun : R → Noun) (r : FolOut × GenS FinMap R) : Noun :=
  C r.1.toNoun (r.2.toNoun regsNoun)

/-- `[%1 p=*]`: a constant. -/
theorem fol_loop_op1 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest p : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 1) p) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 1) p) sub seat mk bc df gen).map (folOutNoun regsNoun) := by
  unfold folSubj
  nockW_open fol_loop.battery
  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
    Sock.toNoun, Cape.toNoun, flag]
  done

/-- The calls of the trap to itself, made by `c`, compute `go`. -/
def GoIsW (c : Noun → Noun → Option Noun) (regsNoun : R → Noun) (rest : Noun) (go : FolGoS FinMap R) :
    Prop :=
  ∀ fol sub seat mk bc df gen,
    c (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (go fol sub seat mk bc df gen).map (folOutNoun regsNoun)

/-- The calls of the trap to itself compute `go`. -/
abbrev GoIs (regsNoun : R → Noun) (rest : Noun) (go : FolGoS FinMap R) : Prop :=
  GoIsW nock regsNoun rest go

/-- `[%3 p=^]`: a cell test. -/
theorem fol_loop_op3 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (a b : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 3) (C a b)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 3) (C a b)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h ⊢
    generalize flag bc = n2 at h ⊢
    generalize unitNoun id mk = n3 at h ⊢
    generalize unitNoun id seat = n4 at h ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h ⊢
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
    simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
      Sock.toNoun, Cape.toNoun, flag]

/-- `[%4 p=^]`: an increment. -/
theorem fol_loop_op4 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (a b : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 4) (C a b)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 4) (C a b)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h ⊢
    generalize flag bc = n2 at h ⊢
    generalize unitNoun id mk = n3 at h ⊢
    generalize unitNoun id seat = n4 at h ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h ⊢
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
    simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
      Sock.toNoun, Cape.toNoun, flag]

/-- `[%7 p=^ q=*]`: a composition, the second call on the product of the
first. -/
theorem fol_loop_op7 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 7) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 7) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have h2 := hgo q o.prod seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h h2 ⊢
    generalize flag bc = n2 at h h2 ⊢
    generalize unitNoun id mk = n3 at h h2 ⊢
    generalize unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h ⊢
    generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
    generalize o.prod.toNoun = n8 at h h2 ⊢
    cases e2 : go q o.prod seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-- `[%5 p=^ q=*]`: an equality test. -/
theorem fol_loop_op5 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 5) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 5) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have h2 := hgo q sub seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h h2 ⊢
    generalize flag bc = n2 at h h2 ⊢
    generalize unitNoun id mk = n3 at h h2 ⊢
    generalize unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h h2 ⊢
    generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
    generalize o.prod.toNoun = n8 at h h2 ⊢
    cases e2 : go q sub seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
        Sock.toNoun, Cape.toNoun, flag]

/-- `[%12 p=^ q=*]`: a scry. -/
theorem fol_loop_op12 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 12) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 12) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have h2 := hgo q sub seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h h2 ⊢
    generalize flag bc = n2 at h h2 ⊢
    generalize unitNoun id mk = n3 at h h2 ⊢
    generalize unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h h2 ⊢
    generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
    generalize o.prod.toNoun = n8 at h h2 ⊢
    cases e2 : go q sub seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
        Sock.toNoun, Cape.toNoun, flag]

/-- `[%8 p=^ q=*]`: the same as `[%7 [p 0+1] q]`. -/
theorem fol_loop_op8 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 8) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 8) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (Nock.n3 (A 7) (C (C a b) (Nock.slot 1)) q) sub seat mk bc df gen
  unfold folSubj at h ⊢
  simp only [Nock.n3, Nock.slot] at h
  generalize flag df = n1 at h ⊢
  generalize flag bc = n2 at h ⊢
  generalize unitNoun id mk = n3 at h ⊢
  generalize unitNoun id seat = n4 at h ⊢
  generalize GenS.toNoun regsNoun gen = n5 at h ⊢
  generalize sub.toNoun = n6 at h ⊢
  nockW_open fol_loop.battery
  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, h]

/-- `[%9 p=@ q=^]`: the same as `[%7 q %2 [%0 1] %0 p]`. -/
theorem fol_loop_op9 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (p : Nat) (a b : Noun)
    (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 9) (C (A p) (C a b))) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 9) (C (A p) (C a b))) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (Nock.n3 (A 7) (C a b) (Nock.n3 (A 2) (Nock.slot 1) (Nock.slot p))) sub seat mk
    bc df gen
  unfold folSubj at h ⊢
  simp only [Nock.n3, Nock.slot] at h
  generalize flag df = n1 at h ⊢
  generalize flag bc = n2 at h ⊢
  generalize unitNoun id mk = n3 at h ⊢
  generalize unitNoun id seat = n4 at h ⊢
  generalize GenS.toNoun regsNoun gen = n5 at h ⊢
  generalize sub.toNoun = n6 at h ⊢
  nockW_open fol_loop.battery
  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, h]

/-! ## The cases that read the library core

The rest of the subject of `+run` is `[bus [data run-gate]]`, by its `=/`s.
The gate of `+run` is built in the core of `+ska-callgraph` (`|%`), whose
context is the gate of `+ska-callgraph`, whose context is `ana`: so `ana` is at
axis `511` of the rest, and the library core `lib` at `2047` (axis `7` of
`ana`).  The battery reads `+so`, `+pi` and `+double-int` there, at
`[9 11 0 0x7ffff]` and so on, the axis depending on what the case has pushed. -/

/-- `lib` is at axis `2047` of a rest that has `ana` at `511`. -/
theorem rest_lib {rest : Noun} (h : slot? 511 rest = some ana) : slot? 2047 rest = some lib := by
  have h' : slot? 511 rest = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 2
  simp only [show 2 ^ 2 * (511 + 1) - 1 = 2047 from rfl,
    show 2 ^ 2 * (1 + 1) - 1 = 7 from rfl] at this
  rw [this, show (7 : Nat) = knit_anno.lib.axis from rfl, knit_anno.lib.arm_at]

set_option maxHeartbeats 1000000 in
/-- `[p=^ q=*]`: a cons, the knit of the two products, or a constant when both
sides are safe. -/
theorem fol_loop_cons (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (C a b) q) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (C a b) q) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have h2 := hgo q sub seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h h2 ⊢
    generalize flag bc = n2 at h h2 ⊢
    generalize unitNoun id mk = n3 at h h2 ⊢
    generalize unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h h2 ⊢
    generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
    cases e2 : go q sub seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
      obtain ⟨m2, ⟨s2, src2⟩, f2⟩ := o2
      simp only [Anno.toNoun] at h h2
      have hk := so_knit_pill s1 s2
      rcases s1 with _ | ⟨c1, d1⟩ <;> rcases s2 with _ | ⟨c2, d2⟩ <;> cases f1 <;> cases f2 <;>
      simp only [sock_mk_toNoun, sock_void_toNoun] at hk h h2 <;>
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2, rest_lib hana, so.lib.arm_at, so_lib_arm,
        so.knit.arm_at, so_knit_arm, hk, pi.lib.arm_at, pi_lib_arm, pi.cons.arm_at,
        pi_cons_arm, pi_cons_gate, consProd, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
        sock_mk_toNoun, cape_yes_toNoun, flag, Sock.data]

/-- `[%0 p=@]`: a fragment of the subject, through `+pull:so` and `+slot:pi`. -/
theorem fol_loop_op0 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun)
    (hana : slot? 511 rest = some ana) (p : Nat) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 0) (A p)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 0) (A p)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  unfold folSubj
  obtain ⟨s, src⟩ := sub
  have hp := so_pull_pill s p
  rcases Nat.lt_or_ge p 2 with hlt | hge
  · have : p = 0 ∨ p = 1 := by omega
    rcases this with rfl | rfl
    · nockW_open fol_loop.battery
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
        Anno.dunno, Sock.dunno, Sock.toNoun, Cape.toNoun, flag]
    · nockW_open fol_loop.battery
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]
  · have hs := pi_slot_pill src p (by omega)
    have h0 : p ≠ 0 := by omega
    have h1 : p ≠ 1 := by omega
    have h0' : ¬ (0 = p) := by omega
    have h1' : ¬ (1 = p) := by omega
    generalize hsn : s.toNoun = ns at hp
    nockW_open fol_loop.battery
    cases e : So.pull s p with
    | none =>
      rw [e] at hp
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Anno.toNoun, hsn, rest_lib hana, h0, h1, h0', h1', e, hp, so.lib.arm_at,
        so_lib_arm, so.pull.arm_at, so_pull_arm, flag]
    | some x =>
      rw [e] at hp
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Anno.toNoun, hsn, rest_lib hana, h0, h1, h0', h1', e, hp, hs,
        so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, pi.lib.arm_at, pi_lib_arm,
        pi.slot.arm_at, pi_slot_arm, folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-- `[%6 p=^ q=* r=*]`: a branch, with `+double-int` of the two products. -/
theorem fol_loop_op6 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (a b q r : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 6) (C (C a b) (C q r))) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 6) (C (C a b) (C q r))) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h]
  | some r1 =>
    rw [e] at h
    obtain ⟨o, g⟩ := r1
    have h2 := hgo q sub seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize hn1 : flag df = n1 at h h2 ⊢
    generalize hn2 : flag bc = n2 at h h2 ⊢
    generalize hn3 : unitNoun id mk = n3 at h h2 ⊢
    generalize hn4 : unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize hn6 : sub.toNoun = n6 at h h2 ⊢
    generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
    generalize o.prod.toNoun = n8 at h h2 ⊢
    cases e2 : go q sub seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      have h3 := hgo r sub seat mk bc df g2
      unfold folSubj at h3
      rw [hn1, hn2, hn3, hn4, hn6] at h3
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      generalize GenS.toNoun regsNoun g2 = n9 at h2 h3 ⊢
      cases e3 : go r sub seat mk bc df g2 with
      | none =>
        rw [e3] at h3
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2, e3, h3]
      | some r3 =>
        rw [e3] at h3
        obtain ⟨o3, g3⟩ := r3
        simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h3
        have hd := double_int_pill o2.prod o3.prod
        generalize o2.prod.toNoun = n10 at h2 hd ⊢
        generalize o3.prod.toNoun = n11 at h3 hd ⊢
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2, e3, h3, rest_lib hana, double_int.arm_at,
          double_int_arm, hd]
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-- `[%10 [a=@ don=*] rec=^]`: an edit, through `+darn:so` and `+edit:pi`; the
axis `0` is the default. -/
theorem fol_loop_op10 (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (ax : Nat) (don r1 r2 : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 10) (C (C (A ax) don) (C r1 r2))) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 10) (C (C (A ax) don) (C r1 r2))) sub seat mk bc df
          gen).map (folOutNoun regsNoun) := by
  unfold folSubj
  rcases Nat.eq_zero_or_pos ax with rfl | hax
  · nockW_open fol_loop.battery
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
      Anno.dunno, Sock.dunno, Sock.toNoun, Cape.toNoun, flag]
  have hax0 : ax ≠ 0 := by omega
  have hax0' : ¬ (0 = ax) := by omega
  have h := hgo don sub seat mk bc df gen
  unfold folSubj at h
  nockW_open fol_loop.battery
  cases e : go don sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, hax0, hax0']
  | some x =>
    rw [e] at h
    obtain ⟨o, g⟩ := x
    have h2 := hgo (C r1 r2) sub seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize hn1 : flag df = n1 at h h2 ⊢
    generalize hn2 : flag bc = n2 at h h2 ⊢
    generalize hn3 : unitNoun id mk = n3 at h h2 ⊢
    generalize hn4 : unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize hn6 : sub.toNoun = n6 at h h2 ⊢
    generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
    obtain ⟨m1, ⟨sd, srcd⟩, f1⟩ := o
    simp only [Anno.toNoun] at h
    cases e2 : go (C r1 r2) sub seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2, hax0, hax0']
    | some y =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := y
      obtain ⟨m2, ⟨sr, srcr⟩, f2⟩ := o2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun, Anno.toNoun] at h2
      have hd := so_darn_pill sr ax sd
      have hp := pi_edit_pill srcr ax hax srcd
      generalize hnd : sd.toNoun = nd at h hd
      generalize hnr : sr.toNoun = nr at h2 hd
      cases e3 : So.darn sr ax sd with
      | none =>
        rw [e3] at hd
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2, e3, hd, hax0, hax0', rest_lib hana,
          so.lib.arm_at, so_lib_arm, so.darn.arm_at, so_darn_arm]
      | some s =>
        rw [e3] at hd
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, e2, h2, e3, hd, hp, hax0, hax0', rest_lib hana,
          so.lib.arm_at, so_lib_arm, so.darn.arm_at, so_darn_arm, pi.lib.arm_at, pi_lib_arm,
          pi.edit.arm_at, pi_edit_arm]
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]

/-! ## The default and the static hint -/

/-- The default of the `?+`: a formula of no case (`shape` says `other`) is
`[0 0]` with no knowledge. -/
theorem fol_loop_other (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest fol : Noun) (hs : shape fol = Shape.other) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go fol sub seat mk bc df gen).map (folOutNoun regsNoun) := by
  have hstep : Ana.folStep env res go fol sub seat mk bc df gen
      = some (⟨Nomm.n0 0, Anno.dunno, false⟩, gen) := by
    simp [Ana.folStep, hs]
  rw [hstep]
  simp only [Option.map_some, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno,
    Sock.dunno, Sock.toNoun, Cape.toNoun, flag, folSubj]
  generalize flag df = n1
  generalize flag bc = n2
  generalize unitNoun id mk = n3
  generalize unitNoun id seat = n4
  generalize GenS.toNoun regsNoun gen = n5
  generalize sub.toNoun = n6
  nockW_open fol_loop.battery
  match fol, hs with
  | .atom _, _ => simp [nock_exec]
  | .cell (.cell _ _) _, hs => simp [shape] at hs
  | .cell (.atom 0) (.atom _), hs => simp [shape] at hs
  | .cell (.atom 0) (.cell _ _), _ => simp [nock_exec]
  | .cell (.atom 1) _, hs => simp [shape] at hs
  | .cell (.atom 2) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 2) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 2) (.cell (.cell _ _) _), hs => simp [shape] at hs
  | .cell (.atom 5) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 5) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 5) (.cell (.cell _ _) _), hs => simp [shape] at hs
  | .cell (.atom 7) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 7) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 7) (.cell (.cell _ _) _), hs => simp [shape] at hs
  | .cell (.atom 8) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 8) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 8) (.cell (.cell _ _) _), hs => simp [shape] at hs
  | .cell (.atom 12) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 12) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 12) (.cell (.cell _ _) _), hs => simp [shape] at hs
  | .cell (.atom 3) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 3) (.cell _ _), hs => simp [shape] at hs
  | .cell (.atom 4) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 4) (.cell _ _), hs => simp [shape] at hs
  | .cell (.atom 6) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 6) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 6) (.cell (.cell _ _) (.atom _)), _ => simp [nock_exec]
  | .cell (.atom 6) (.cell (.cell _ _) (.cell _ _)), hs => simp [shape] at hs
  | .cell (.atom 9) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 9) (.cell (.cell _ _) _), _ => simp [nock_exec]
  | .cell (.atom 9) (.cell (.atom _) (.atom _)), _ => simp [nock_exec]
  | .cell (.atom 9) (.cell (.atom _) (.cell _ _)), hs => simp [shape] at hs
  | .cell (.atom 10) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 10) (.cell (.atom _) _), _ => simp [nock_exec]
  | .cell (.atom 10) (.cell (.cell (.cell _ _) _) _), _ => simp [nock_exec]
  | .cell (.atom 10) (.cell (.cell (.atom _) _) (.atom _)), _ => simp [nock_exec]
  | .cell (.atom 10) (.cell (.cell (.atom _) _) (.cell _ _)), hs => simp [shape] at hs
  | .cell (.atom 11) (.atom _), _ => simp [nock_exec]
  | .cell (.atom 11) (.cell (.atom _) (.atom _)), _ => simp [nock_exec]
  | .cell (.atom 11) (.cell (.atom _) (.cell _ _)), hs => simp [shape] at hs
  | .cell (.atom 11) (.cell (.cell (.cell _ _) _) _), _ => simp [nock_exec]
  | .cell (.atom 11) (.cell (.cell (.atom _) (.atom _)) _), _ => simp [nock_exec]
  | .cell (.atom 11) (.cell (.cell (.atom _) (.cell _ _)) _), hs => simp [shape] at hs
  | .cell (.atom (_ + 13)) _, _ => simp [nock_exec]

/-- `[%11 p=@ q=^]`: a static hint; `%bare` is analysed as the indirect call
`[%2 [%0 1] %1 fol]` with `bare-call` set. -/
theorem fol_loop_op11s (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (p : Nat) (a b : Noun)
    (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (A p) (C a b))) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (A p) (C a b))) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  by_cases hp : p = Tag.bare
  · obtain rfl : p = 0x65726162 := hp
    have h := hgo (Nock.n3 (A 2) (Nock.slot 1) (Nock.quote (C (A 11) (C (A 0x65726162) (C a b)))))
      sub seat mk true df gen
    unfold folSubj at h ⊢
    simp only [Nock.n3, Nock.n2, Nock.slot, Nock.quote] at h
    rw [show flag true = A 0 from rfl] at h
    generalize flag df = n1 at h ⊢
    generalize unitNoun id mk = n3 at h ⊢
    generalize unitNoun id seat = n4 at h ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h ⊢
    nockW_open fol_loop.battery
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, h, Tag.bare, Nock.n3, Nock.n2, Nock.slot, Nock.quote]
  · have hp' : ¬ (0x65726162 = p) := fun e => hp (by rw [← e]; rfl)
    have h := hgo (C a b) sub seat mk bc df gen
    unfold folSubj at h ⊢
    nockW_open fol_loop.battery
    cases e : go (C a b) sub seat mk bc df gen with
    | none =>
      rw [e] at h
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, hp, hp']
    | some r =>
      rw [e] at h
      obtain ⟨o, g⟩ := r
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
      generalize flag df = n1 at h ⊢
      generalize flag bc = n2 at h ⊢
      generalize unitNoun id mk = n3 at h ⊢
      generalize unitNoun id seat = n4 at h ⊢
      generalize GenS.toNoun regsNoun gen = n5 at h ⊢
      generalize sub.toNoun = n6 at h ⊢
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, e, h, hp, hp']
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-! ## The dynamic hint -/

/-- `+soft-spot` of `ana` computes `env.softSpot`, as a unit. -/
def SoftSpotIs (env : Env R) : Prop :=
  ∀ n, nock (C soft_spot.battery (C n ana)) soft_spot.battery = some (unitNoun id (env.softSpot n))

theorem soft_spot_arm : nock ana soft_spot.arm = some (C soft_spot.battery (C (A 0) ana)) := by
  unfold soft_spot.arm; simp only [nock_exec]

/-- The trap `nock-11-soft` sets `seat`, and `area` if not set yet, as
`spotHint` says. -/
theorem fol_loop_soft (regsNoun : R → Noun) (env : Env R) (rest : Noun)
    (hana : slot? 511 rest = some ana) (hsoft : SoftSpotIs env) (tag : Nat) (h1 h2 f : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (C fol_loop.soft (folSubj regsNoun rest (C (A 11) (C (C (A tag) (C h1 h2)) f)) sub seat mk
        bc df gen)) fol_loop.soft
      = some (folSubj regsNoun rest (C (A 11) (C (C (A tag) (C h1 h2)) f)) sub (spotHint env Tag.spot (A 1) h2 seat gen).1 mk bc df
          (spotHint env Tag.spot (A 1) h2 seat gen).2) := by
  have hs := hsoft h2
  unfold folSubj
  nock_open fol_loop.soft
  cases e : env.softSpot h2 with
  | none =>
    rw [e] at hs
    simp [nock_exec, spotHint, e, hs, hana, soft_spot.arm_at, soft_spot_arm,
      unitNoun]
  | some pot =>
    rw [e] at hs
    cases ea : gen.area with
    | none =>
      simp [nock_exec, spotHint, e, hs, ea, hana, soft_spot.arm_at, soft_spot_arm, unitNoun,
        GenS.toNoun]
    | some ar =>
      simp [nock_exec, spotHint, e, hs, ea, hana, soft_spot.arm_at, soft_spot_arm, unitNoun,
        GenS.toNoun]

set_option linter.unusedSimpArgs false in
/-- `[%11 [a=@ h=^] f=*]` with a tag that is none of `%spot`, `%memo`, `%mean`,
`%fast`: the hint, then the formula. -/
theorem fol_loop_op11d_plain (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go) (tag : Nat)
    (hsp : tag ≠ Tag.spot) (hme : tag ≠ Tag.memo) (hmn : tag ≠ Tag.mean) (hfa : tag ≠ Tag.fast)
    (h1 h2 f : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (C (A tag) (C h1 h2)) f)) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (C (A tag) (C h1 h2)) f)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have hsp' : ¬ (0x746f7073 = tag) := fun e => hsp (e ▸ rfl)
  have hme' : ¬ (0x6f6d656d = tag) := fun e => hme (e ▸ rfl)
  have hmn' : ¬ (0x6e61656d = tag) := fun e => hmn (e ▸ rfl)
  have hfa' : ¬ (0x74736166 = tag) := fun e => hfa (e ▸ rfl)
  have hsp'' : ¬ (tag = 0x746f7073) := fun e => hsp (e ▸ rfl)
  have hme'' : ¬ (tag = 0x6f6d656d) := fun e => hme (e ▸ rfl)
  have hmn'' : ¬ (tag = 0x6e61656d) := fun e => hmn (e ▸ rfl)
  have hfa'' : ¬ (tag = 0x74736166) := fun e => hfa (e ▸ rfl)
  have h := hgo (C h1 h2) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C h1 h2) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, e, h, hsp, hsp', hsp'']
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have hf := hgo f sub seat mk bc df g
    unfold folSubj at hf
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h hf ⊢
    generalize flag bc = n2 at h hf ⊢
    generalize unitNoun id mk = n3 at h hf ⊢
    generalize unitNoun id seat = n4 at h hf ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h hf ⊢
    generalize GenS.toNoun regsNoun g = n7 at h hf ⊢
    obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
    simp only [Anno.toNoun] at h
    generalize hs1 : s1.toNoun = ns1 at h
    cases e2 : go f sub seat mk bc df g with
    | none =>
      rw [e2] at hf
      cases f1 <;>
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, e, h, e2, hf, hsp, hsp', hsp'', hme,
        hme', hme'', hmn, hmn', hmn'']
    | some r2 =>
      rw [e2] at hf
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
      cases f1 <;>
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, e2, hf, hsp, hsp',
        hsp'', hme, hme', hme'', hmn, hmn', hmn'', hfa, hfa', hfa''] <;>
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag, hsp, hmn]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `[%11 [%memo h=^] f=*]`: a safe hint with a known product makes the formula a
call `[%2 [%0 1] %1 f]` with `memo-key` set, else a plain hint. -/
theorem fol_loop_op11d_memo (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (h1 h2 f : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (C (A Tag.memo) (C h1 h2)) f)) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (C (A Tag.memo) (C h1 h2)) f)) sub seat mk bc df
          gen).map (folOutNoun regsNoun) := by
  have h := hgo (C h1 h2) sub seat mk bc df gen
  unfold folSubj at h ⊢
  simp only [Tag.memo] at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C h1 h2) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, e, h, Tag.spot]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have hf := hgo f sub seat mk bc df g
    have hm := hgo (C (A 2) (C (C (A 0) (A 1)) (C (A 1) f))) sub seat (some o.prod.sock.data) bc df g
    unfold folSubj at hf hm
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h hf hm ⊢
    generalize flag bc = n2 at h hf hm ⊢
    generalize unitNoun id mk = n3 at h hf ⊢
    generalize unitNoun id seat = n4 at h hf hm ⊢
    simp only [unitNoun, id] at hm
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h hf hm ⊢
    generalize GenS.toNoun regsNoun g = n7 at h hf hm ⊢
    obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
    simp only [Anno.toNoun] at h
    rcases s1 with _ | ⟨c1, d1⟩
    · simp only [sock_void_toNoun] at h
      cases e2 : go f sub seat mk bc df g with
      | none =>
        rw [e2] at hf
        cases f1 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, e, h, e2, hf, Tag.spot,
          Tag.mean, Tag.memo, flag]
      | some r2 =>
        rw [e2] at hf
        obtain ⟨o2, g2⟩ := r2
        simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
        cases f1 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, e2, hf,
          Tag.spot, Tag.mean, Tag.memo, Tag.fast, flag] <;>
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]
    · simp only [sock_mk_toNoun, Sock.data] at h hm
      generalize c1.toNoun = nc at h
      cases f1
      · cases e2 : go f sub seat mk bc df g with
        | none =>
          rw [e2] at hf
          simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, e, h, e2, hf, Tag.spot,
            Tag.mean, Tag.memo, flag]
        | some r2 =>
          rw [e2] at hf
          obtain ⟨o2, g2⟩ := r2
          simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
          simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, e2,
            hf, Tag.spot, Tag.mean, Tag.memo, Tag.fast, flag]
          simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]
      · simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, e, h, hm, Tag.spot, Tag.memo, Nock.n3,
          Nock.n2, Nock.slot, Nock.quote, flag, Sock.data]

/-- The arm `+register-fast` of `ana` builds its gate. -/
theorem register_fast_arm : nock ana register_fast.arm
    = some (C register_fast.battery
        (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))
          ana)) := by
  unfold register_fast.arm; simp only [nock_exec]

/-- The gate `+register-fast` of `ana` computes `env.registerFast`: the flag
`miss` and the new registrations. -/
def RegisterFastIs (regsNoun : R → Noun) (env : Env R) : Prop :=
  ∀ h f r, nock (C register_fast.battery (C (C h.toNoun (C f.toNoun (regsNoun r))) ana))
      register_fast.battery = (env.registerFast h f r).map fun p => C (flag p.1) (regsNoun p.2)

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `[%11 [%fast h=^] f=*]`: the hint, the formula, then `+register-fast` on
their products. -/
theorem fol_loop_op11d_fast (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hreg : RegisterFastIs regsNoun env)
    (h1 h2 f : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (C (A Tag.fast) (C h1 h2)) f)) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (C (A Tag.fast) (C h1 h2)) f)) sub seat mk bc df
          gen).map (folOutNoun regsNoun) := by
  have h := hgo (C h1 h2) sub seat mk bc df gen
  unfold folSubj at h ⊢
  simp only [Tag.fast] at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C h1 h2) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, e, h, Tag.spot]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have hf := hgo f sub seat mk bc df g
    unfold folSubj at hf
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize flag df = n1 at h hf ⊢
    generalize flag bc = n2 at h hf ⊢
    generalize unitNoun id mk = n3 at h hf ⊢
    generalize unitNoun id seat = n4 at h hf ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize sub.toNoun = n6 at h hf ⊢
    generalize GenS.toNoun regsNoun g = n7 at h hf ⊢
    obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
    simp only [Anno.toNoun] at h
    cases e2 : go f sub seat mk bc df g with
    | none =>
      rw [e2] at hf
      generalize s1.toNoun = ns1 at h
      cases f1 <;>
      simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, e, h, e2, hf, Tag.spot,
        Tag.mean, Tag.memo, flag]
    | some r2 =>
      rw [e2] at hf
      obtain ⟨o2, g2⟩ := r2
      obtain ⟨m2, ⟨s2, src2⟩, f2⟩ := o2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun, Anno.toNoun] at hf
      have hr := hreg s1 s2 g2.st.regs
      generalize s1.toNoun = ns1 at h hr
      simp only [GenS.toNoun, SkaState.toNoun, Stats.toNoun] at hf
      cases e3 : env.registerFast s1 s2 g2.st.regs with
      | none =>
        rw [e3] at hr
        cases f1 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, e2,
          hf, e3, hr, hana, fol_loop.register_fast.arm_at, register_fast_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag]
      | some p =>
        rw [e3] at hr
        obtain ⟨miss, r'⟩ := p
        cases f1 <;> cases miss <;>
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, e2,
          hf, e3, hr, hana, fol_loop.register_fast.arm_at, register_fast_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag] <;>
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag, GenS.toNoun,
          SkaState.toNoun, Stats.toNoun]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `[%11 [%spot h=^] f=*]`: with a constant spot (`h` is `[1 pot]`), the trap
`nock-11-soft` sets `seat` and `area` first; then the hint and the formula. -/
theorem fol_loop_op11d_spot (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hsoft : SoftSpotIs env)
    (h1 h2 f : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (C (A Tag.spot) (C h1 h2)) f)) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (C (A Tag.spot) (C h1 h2)) f)) sub seat mk bc df
          gen).map (folOutNoun regsNoun) := by
  have hs := fol_loop_soft regsNoun env rest hana hsoft Tag.spot h1 h2 f sub seat mk bc df gen
  obtain ⟨seat', gen', hsg⟩ : ∃ seat' gen', spotHint env Tag.spot h1 h2 seat gen = (seat', gen') :=
    ⟨_, _, rfl⟩
  have hstep : Ana.folStep env res go (C (A 11) (C (C (A Tag.spot) (C h1 h2)) f)) sub seat mk bc df
      gen = (go (C h1 h2) sub seat' mk bc df gen').bind fun h =>
        (go f sub seat' mk bc df h.2).bind fun fr =>
        some (⟨Nomm.n11d Tag.spot h.1.nomm fr.1.nomm f, fr.1.prod,
          decide (h.1.saf = true ∧ fr.1.saf = true)⟩, fr.2) := by
    have hsg' : spotHint env 0x746f7073 h1 h2 seat gen = (seat', gen') := hsg
    simp [Ana.folStep, shape, hsg', Ana.meanArm, Ana.fastHint, Tag.spot, Tag.memo, Tag.mean,
      Tag.fast]
  rw [hstep]
  have hm1 : ∀ fol seat gen, folSubj regsNoun rest fol sub seat mk bc df gen
      = C fol_loop.battery (C (flag df) (C (flag bc) (C (unitNoun id mk) (C (unitNoun id seat)
          (C (gen.toNoun regsNoun) (C sub.toNoun (C fol rest))))))) := fun _ _ _ => rfl
  have h := hgo (C h1 h2) sub seat' mk bc df gen'
  by_cases hh1 : h1 = A 1
  · subst hh1
    rw [hsg] at hs
    simp only [hm1] at hs h ⊢
    simp only [Tag.spot] at hs ⊢
    nockW_open fol_loop.battery
    generalize hn1 : flag df = n1 at h hs ⊢
    generalize hn2 : flag bc = n2 at h hs ⊢
    generalize hn3 : unitNoun id mk = n3 at h hs ⊢
    generalize unitNoun id seat = n4 at hs ⊢
    generalize GenS.toNoun regsNoun gen = n5 at hs ⊢
    generalize hn6 : sub.toNoun = n6 at h hs ⊢
    generalize hn4 : unitNoun id seat' = m4 at h hs ⊢
    generalize GenS.toNoun regsNoun gen' = m5 at h hs ⊢
    cases e : go (C (A 1) h2) sub seat' mk bc df gen' with
    | none =>
      rw [e] at h
      simp (disch := ffar_disch) [nock_exec, hcf, e, h, hs, Tag.spot]
    | some r =>
      rw [e] at h
      obtain ⟨o, g⟩ := r
      have hf := hgo f sub seat' mk bc df g
      simp only [hm1] at hf
      rw [hn1, hn2, hn3, hn4, hn6] at hf
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
      generalize GenS.toNoun regsNoun g = n7 at h hf ⊢
      obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
      simp only [Anno.toNoun] at h
      generalize s1.toNoun = ns1 at h
      cases e2 : go f sub seat' mk bc df g with
      | none =>
        rw [e2] at hf
        cases f1 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, e, h, hs, e2, hf, Tag.spot, Tag.memo, Tag.mean, Tag.fast, flag]
      | some r2 =>
        rw [e2] at hf
        obtain ⟨⟨m2, p2, f2⟩, g2⟩ := r2
        simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
        cases f1 <;> cases f2 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, e, h, hs, e2, hf, Tag.spot, Tag.memo, Tag.mean, Tag.fast, flag] <;>
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag, Tag.spot]
  · have hh1' : ¬ (A 1 = h1) := fun e => hh1 e.symm
    simp [spotHint, hh1] at hsg
    obtain ⟨rfl, rfl⟩ := hsg
    simp only [hm1] at h ⊢
    nockW_open fol_loop.battery
    cases e : go (C h1 h2) sub seat mk bc df gen with
    | none =>
      rw [e] at h
      simp (disch := ffar_disch) [nock_exec, hcf, e, h, hh1', Tag.spot]
    | some r =>
      rw [e] at h
      obtain ⟨o, g⟩ := r
      have hf := hgo f sub seat mk bc df g
      simp only [hm1] at hf
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
      generalize flag df = n1 at h hf ⊢
      generalize flag bc = n2 at h hf ⊢
      generalize unitNoun id mk = n3 at h hf ⊢
      generalize unitNoun id seat = n4 at h hf ⊢
      generalize GenS.toNoun regsNoun gen = n5 at h ⊢
      generalize sub.toNoun = n6 at h hf ⊢
      generalize GenS.toNoun regsNoun g = n7 at h hf ⊢
      obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
      simp only [Anno.toNoun] at h
      generalize s1.toNoun = ns1 at h
      cases e2 : go f sub seat mk bc df g with
      | none =>
        rw [e2] at hf
        cases f1 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, e, h, e2, hf, hh1', Tag.spot, Tag.memo, Tag.mean, Tag.fast, flag]
      | some r2 =>
        rw [e2] at hf
        obtain ⟨⟨m2, p2, f2⟩, g2⟩ := r2
        simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
        cases f1 <;> cases f2 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, e, h, e2, hf, hh1', Tag.spot, Tag.memo, Tag.mean, Tag.fast, flag] <;>
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag, Tag.spot]


theorem nomm_toNoun_ne_two (n : Nomm) : (A 2 = n.toNoun) = False := by
  cases n <;> simp [Nomm.toNoun]

theorem wut_nomm (n : Nomm) : wut n.toNoun = A 0 := by
  cases n <;> rfl

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- `[%11 [%mean h=^] f=*]`: when the hint is not safe and its product is a core
with a known battery, the call `[%2 [%0 1] %0 2]` on it, with `defer`, gives
the bell of the `%mean` nomm. -/
theorem fol_loop_op11d_mean (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana)
    (h1 h2 f : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (C (A Tag.mean) (C h1 h2)) f)) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (C (A Tag.mean) (C h1 h2)) f)) sub seat mk bc df
          gen).map (folOutNoun regsNoun) := by
  have h := hgo (C h1 h2) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nockW_open fol_loop.battery
  cases e : go (C h1 h2) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, e, h, Tag.spot, Tag.mean]
  | some r =>
    rw [e] at h
    obtain ⟨⟨m1, ⟨s1, src1⟩, f1⟩, g⟩ := r
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    have hf := hgo f sub seat mk bc df g
    unfold folSubj at hf
    generalize hn1 : flag df = n1 at h hf ⊢
    generalize hn2 : flag bc = n2 at h hf ⊢
    generalize hn3 : unitNoun id mk = n3 at h hf ⊢
    generalize hn4 : unitNoun id seat = n4 at h hf ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize hn6 : sub.toNoun = n6 at h hf ⊢
    simp only [Anno.toNoun] at h
    by_cases hgood : f1 = false ∧ s1 ≠ Sock.void
    · obtain ⟨rfl, hs1⟩ := hgood
      obtain ⟨c1, d1, rfl⟩ : ∃ c1 d1, s1 = Sock.mk c1 d1 := by
        cases s1 with
        | void => exact absurd rfl hs1
        | mk c d => exact ⟨c, d, rfl⟩
      simp only [sock_mk_toNoun] at h
      have hp := so_pull_pill (Sock.mk c1 d1) 2
      simp only [sock_mk_toNoun] at hp
      generalize hnc1 : c1.toNoun = nc1 at h hp
      cases ep : So.pull (Sock.mk c1 d1) 2 with
      | none =>
        rw [ep] at hp
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot]
      | some bat =>
        rw [ep] at hp
        by_cases hb : ∃ da db, bat = Sock.mk Cape.yes (C da db)
        · obtain ⟨da, db, rfl⟩ := hb
          simp only [Option.map_some, sock_mk_toNoun, cape_yes_toNoun] at hp
          have hc := hgo (C (A 2) (C (C (A 0) (A 1)) (C (A 0) (A 2)))) ⟨Sock.mk c1 d1, src1⟩ seat mk
            bc true g
          unfold folSubj at hc
          rw [hn2, hn3, hn4, show flag true = A 0 from rfl] at hc
          simp only [Anno.toNoun, sock_mk_toNoun, hnc1] at hc
          generalize GenS.toNoun regsNoun g = n7 at h hf hc ⊢
          cases ec : go (C (A 2) (C (C (A 0) (A 1)) (C (A 0) (A 2)))) ⟨Sock.mk c1 d1, src1⟩ seat mk
            bc true g with
          | none =>
            rw [ec] at hc
            simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec]
          | some rc =>
            rw [ec] at hc
            obtain ⟨⟨mc, ⟨sc, srcc⟩, fc⟩, gc⟩ := rc
            simp only [Option.map_some, folOutNoun, FolOut.toNoun, Anno.toNoun] at hc
            have hf2 := hgo f sub seat mk bc df gc
            unfold folSubj at hf2
            rw [hn1, hn2, hn3, hn4, hn6] at hf2
            generalize GenS.toNoun regsNoun gc = n8 at hc hf2 ⊢
            by_cases hn : ∃ p q b k, mc = Nomm.n2 p q (some (b, k))
            · obtain ⟨p, q, b, k, rfl⟩ := hn
              simp only [Nomm.toNoun, unitNoun, id] at hc
              have hca : ∀ c : Cape, nock (C ca.all.battery (C c.toNoun (C ca.battery lib)))
                  ca.all.battery = some (Hoon.loob (Ca.all c)) := ca_all_gate _
              cases e3 : go f sub seat mk bc df gc with
              | none =>
                rw [e3] at hf2
                rcases sc with _ | ⟨cc, dc⟩
                · simp only [sock_void_toNoun] at hc
                  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec, hf2, e3]
                · simp only [sock_mk_toNoun] at hc
                  have ha := hca cc
                  cases hall : Ca.all cc <;> rw [hall] at ha <;>
                  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec, hf2, e3, hall, ha, ca.lib.arm_at, ca_lib_arm,
                    ca.all.arm_at, ca_all_arm, Hoon.loob]
              | some r3 =>
                rw [e3] at hf2
                obtain ⟨⟨m2, p2, f2⟩, g2⟩ := r3
                simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf2
                rcases sc with _ | ⟨cc, dc⟩
                · simp only [sock_void_toNoun] at hc
                  cases f2 <;> simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec, hf2, e3] <;>
                  simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag, unitNoun,
                    Tag.mean]
                · simp only [sock_mk_toNoun] at hc
                  have ha := hca cc
                  cases hall : Ca.all cc <;> rw [hall] at ha <;> cases f2 <;>
                  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec, hf2, e3, hall, ha, ca.lib.arm_at, ca_lib_arm,
                    ca.all.arm_at, ca_all_arm, Hoon.loob] <;>
                  simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag, unitNoun,
                    Tag.mean]
            · cases mc
              case n2 p q info =>
                cases info with
                | none =>
                  simp only [Nomm.toNoun, unitNoun] at hc
                  simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec]
                | some bk => exact absurd ⟨p, q, bk.1, bk.2, rfl⟩ hn
              case cons p q =>
                simp only [Nomm.toNoun] at hc
                simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec, nomm_toNoun_ne_two]
              all_goals
                simp only [Nomm.toNoun] at hc
                simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hc, ec]
        · have hb' : ∀ da db, bat ≠ Sock.mk Cape.yes (C da db) := fun da db e => hb ⟨da, db, e⟩
          generalize GenS.toNoun regsNoun g = n7 at h hf ⊢
          cases e2 : go f sub seat mk bc df g with
          | none =>
            rw [e2] at hf
            rcases bat with _ | ⟨_ | _ | ⟨cp, cq⟩, _ | ⟨da, db⟩⟩ <;>
            (try exact absurd rfl (hb' _ _)) <;>
            simp only [Option.map_some, sock_mk_toNoun, sock_void_toNoun, Cape.toNoun] at hp <;>
            simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hf, e2]
          | some r2 =>
            rw [e2] at hf
            obtain ⟨⟨m2, p2, f2⟩, g2⟩ := r2
            simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
            rcases bat with _ | ⟨_ | _ | ⟨cp, cq⟩, _ | ⟨da, db⟩⟩ <;>
            (try exact absurd rfl (hb' _ _)) <;>
            simp only [Option.map_some, sock_mk_toNoun, sock_void_toNoun, Cape.toNoun] at hp <;>
            cases f2 <;>
            simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, hp, ep,
          rest_lib hana, so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, Tag.spot, Tag.mean,
          Tag.memo, Tag.fast, flag, Nock.n3, Nock.n2, Nock.slot, hf, e2] <;>
            simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]
    · have hbad : f1 = true ∨ s1 = Sock.void := by
        cases f1 <;> simp_all
      generalize GenS.toNoun regsNoun g = n7 at h hf ⊢
      cases e2 : go f sub seat mk bc df g with
      | none =>
        rw [e2] at hf
        rcases s1 with _ | ⟨c1, d1⟩ <;> cases f1 <;> simp at hbad <;>
        simp only [sock_mk_toNoun, sock_void_toNoun] at h <;>
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, e, h, e2, hf, Tag.spot,
          Tag.mean, Tag.memo, flag]
      | some r2 =>
        rw [e2] at hf
        obtain ⟨⟨m2, p2, f2⟩, g2⟩ := r2
        simp only [Option.map_some, folOutNoun, FolOut.toNoun] at hf
        rcases s1 with _ | ⟨c1, d1⟩ <;> cases f1 <;> simp at hbad <;>
        simp only [sock_mk_toNoun, sock_void_toNoun] at h <;> cases f2 <;>
        simp (disch := ffar_disch) [nock_exec, hcf, Ana.folStep, shape, Ana.spotHint, Ana.meanArm, Ana.fastHint, e, h, e2,
          hf, Tag.spot, Tag.mean, Tag.memo, Tag.fast, flag] <;>
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]

/-- `[%11 [a=@ h=^] f=*]`, every tag. -/
theorem fol_loop_op11d (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hsoft : SoftSpotIs env) (hreg : RegisterFastIs regsNoun env)
    (tag : Nat) (h1 h2 f : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest (C (A 11) (C (C (A tag) (C h1 h2)) f)) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 11) (C (C (A tag) (C h1 h2)) f)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  by_cases hsp : tag = Tag.spot
  · subst hsp; exact fol_loop_op11d_spot c hcf regsNoun env res go rest hgo hana hsoft h1 h2 f sub seat mk
      bc df gen
  by_cases hme : tag = Tag.memo
  · subst hme; exact fol_loop_op11d_memo c hcf regsNoun env res go rest hgo h1 h2 f sub seat mk bc df gen
  by_cases hmn : tag = Tag.mean
  · subst hmn; exact fol_loop_op11d_mean c hcf regsNoun env res go rest hgo hana h1 h2 f sub seat mk bc df
      gen
  by_cases hfa : tag = Tag.fast
  · subst hfa; exact fol_loop_op11d_fast c hcf regsNoun env res go rest hgo hana hreg h1 h2 f sub seat mk
      bc df gen
  exact fol_loop_op11d_plain c hcf regsNoun env res go rest hgo tag hsp hme hmn hfa h1 h2 f sub seat mk bc
    df gen

/-! ## Every case but `%2` -/

/-- One level of the trap is `Ana.folStep` on every formula but a `%2`, given
its calls to itself (`GoIs`), `ana` at axis `511` of the rest of `+run`'s
subject, and `+soft-spot` and `+register-fast` as `env` says. -/
theorem fol_loop_step (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hsoft : SoftSpotIs env) (hreg : RegisterFastIs regsNoun env)
    (fol : Noun) (h2 : ∀ a b q, shape fol ≠ Shape.op2 a b q) (sub : Anno) (seat mk : Option Noun)
    (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go fol sub seat mk bc df gen).map (folOutNoun regsNoun) := by
  rcases shape_fol fol with hs | hs
  · exact fol_loop_other c hcf regsNoun env res go rest fol hs sub seat mk bc df gen
  · generalize hsh : shape fol = sh at hs h2
    subst hs
    cases sh with
    | cons a b q => exact fol_loop_cons c hcf regsNoun env res go rest hgo hana a b q sub seat mk bc df gen
    | op0 p => exact fol_loop_op0 c hcf regsNoun env res go rest hana p sub seat mk bc df gen
    | op1 p => exact fol_loop_op1 c hcf regsNoun env res go rest p sub seat mk bc df gen
    | op2 a b q => exact absurd rfl (h2 a b q)
    | op3 a b => exact fol_loop_op3 c hcf regsNoun env res go rest hgo a b sub seat mk bc df gen
    | op4 a b => exact fol_loop_op4 c hcf regsNoun env res go rest hgo a b sub seat mk bc df gen
    | op5 a b q => exact fol_loop_op5 c hcf regsNoun env res go rest hgo a b q sub seat mk bc df gen
    | op6 a b q r => exact fol_loop_op6 c hcf regsNoun env res go rest hgo hana a b q r sub seat mk bc df gen
    | op7 a b q => exact fol_loop_op7 c hcf regsNoun env res go rest hgo a b q sub seat mk bc df gen
    | op8 a b q => exact fol_loop_op8 c hcf regsNoun env res go rest hgo a b q sub seat mk bc df gen
    | op9 p a b => exact fol_loop_op9 c hcf regsNoun env res go rest hgo p a b sub seat mk bc df gen
    | op10 ax don r1 r2 =>
      exact fol_loop_op10 c hcf regsNoun env res go rest hgo hana ax don r1 r2 sub seat mk bc df gen
    | op11s p a b => exact fol_loop_op11s c hcf regsNoun env res go rest hgo p a b sub seat mk bc df gen
    | op11d tag h1 h2' f =>
      exact fol_loop_op11d c hcf regsNoun env res go rest hgo hana hsoft hreg tag h1 h2' f sub seat mk bc df
        gen
    | op12 a b q => exact fol_loop_op12 c hcf regsNoun env res go rest hgo a b q sub seat mk bc df gen
    | other => exact fol_loop_other c hcf regsNoun env res go rest _ hsh sub seat mk bc df gen

end Compiler
end Formalization
