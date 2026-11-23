import lemmas.Compiler.RecCall
import lemmas.Pill.Arm.Fol_loop

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
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-- The subject of the trap `fol-loop`. -/
noncomputable def folSubj (regsNoun : R → Noun) (rest fol : Noun) (sub : Anno) (seat mk : Option Noun)
    (bc df : Bool) (gen : GenS FinMap R) : Noun :=
  C fol_loop.battery (C (flag df) (C (flag bc) (C (unitNoun id mk) (C (unitNoun id seat)
    (C (gen.toNoun regsNoun) (C sub.toNoun (C fol rest)))))))

/-- The noun of a result of `fol-loop`: `[[nomm prod saf] gen]`. -/
noncomputable def folOutNoun (regsNoun : R → Noun) (r : FolOut × GenS FinMap R) : Noun :=
  C r.1.toNoun (r.2.toNoun regsNoun)

/-- `[%1 p=*]`: a constant. -/
theorem fol_loop_op1 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest p : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 1) p) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 1) p) sub seat mk bc df gen).map (folOutNoun regsNoun) := by
  unfold folSubj
  nock_open fol_loop.battery
  simp [nock_exec, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
    Sock.toNoun, Cape.toNoun, flag]
  done

/-- The calls of the trap to itself compute `go`. -/
def GoIs (regsNoun : R → Noun) (rest : Noun) (go : FolGoS FinMap R) : Prop :=
  ∀ fol sub seat mk bc df gen,
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (go fol sub seat mk bc df gen).map (folOutNoun regsNoun)

/-- `[%3 p=^]`: a cell test. -/
theorem fol_loop_op3 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (a b : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 3) (C a b)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 3) (C a b)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
    simp [nock_exec, Ana.folStep, shape, e, h]
    simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
      Sock.toNoun, Cape.toNoun, flag]

/-- `[%4 p=^]`: an increment. -/
theorem fol_loop_op4 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (a b : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 4) (C a b)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 4) (C a b)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
    simp [nock_exec, Ana.folStep, shape, e, h]
    simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
      Sock.toNoun, Cape.toNoun, flag]

/-- `[%7 p=^ q=*]`: a composition, the second call on the product of the
first. -/
theorem fol_loop_op7 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 7) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 7) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-- `[%5 p=^ q=*]`: an equality test. -/
theorem fol_loop_op5 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 5) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 5) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
        Sock.toNoun, Cape.toNoun, flag]

/-- `[%12 p=^ q=*]`: a scry. -/
theorem fol_loop_op12 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 12) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 12) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
        Sock.toNoun, Cape.toNoun, flag]

/-- `[%8 p=^ q=*]`: the same as `[%7 [p 0+1] q]`. -/
theorem fol_loop_op8 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 8) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
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
  nock_open fol_loop.battery
  simp [nock_exec, Ana.folStep, shape, h]

/-- `[%9 p=@ q=^]`: the same as `[%7 q %2 [%0 1] %0 p]`. -/
theorem fol_loop_op9 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (p : Nat) (a b : Noun)
    (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 9) (C (A p) (C a b))) sub seat mk bc df gen) fol_loop.battery
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
  nock_open fol_loop.battery
  simp [nock_exec, Ana.folStep, shape, h]

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

/-- `[p=^ q=*]`: a cons, the knit of the two products, or a constant when both
sides are safe. -/
theorem fol_loop_cons (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go)
    (hana : slot? 511 rest = some ana) (a b q : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (C a b) q) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (C a b) q) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2, rest_lib hana, so.lib.arm_at, so_lib_arm,
        so.knit.arm_at, so_knit_arm, hk, pi.lib.arm_at, pi_lib_arm, pi.cons.arm_at,
        pi_cons_arm, pi_cons_gate, consProd, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
        sock_mk_toNoun, cape_yes_toNoun, flag, Sock.data]

/-- `[%0 p=@]`: a fragment of the subject, through `+pull:so` and `+slot:pi`. -/
theorem fol_loop_op0 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun)
    (hana : slot? 511 rest = some ana) (p : Nat) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 0) (A p)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 0) (A p)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  unfold folSubj
  obtain ⟨s, src⟩ := sub
  have hp := so_pull_pill s p
  rcases Nat.lt_or_ge p 2 with hlt | hge
  · have : p = 0 ∨ p = 1 := by omega
    rcases this with rfl | rfl
    · nock_open fol_loop.battery
      simp [nock_exec, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
        Anno.dunno, Sock.dunno, Sock.toNoun, Cape.toNoun, flag]
    · nock_open fol_loop.battery
      simp [nock_exec, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]
  · have hs := pi_slot_pill src p (by omega)
    have h0 : p ≠ 0 := by omega
    have h1 : p ≠ 1 := by omega
    have h0' : ¬ (0 = p) := by omega
    have h1' : ¬ (1 = p) := by omega
    generalize hsn : s.toNoun = ns at hp
    nock_open fol_loop.battery
    cases e : So.pull s p with
    | none =>
      rw [e] at hp
      simp [nock_exec, Ana.folStep, shape, Anno.toNoun, hsn, rest_lib hana, h0, h1, h0', h1', e, hp, so.lib.arm_at,
        so_lib_arm, so.pull.arm_at, so_pull_arm, flag]
    | some x =>
      rw [e] at hp
      simp [nock_exec, Ana.folStep, shape, Anno.toNoun, hsn, rest_lib hana, h0, h1, h0', h1', e, hp, hs,
        so.lib.arm_at, so_lib_arm, so.pull.arm_at, so_pull_arm, pi.lib.arm_at, pi_lib_arm,
        pi.slot.arm_at, pi_slot_arm, folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-- `[%6 p=^ q=* r=*]`: a branch, with `+double-int` of the two products. -/
theorem fol_loop_op6 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go)
    (hana : slot? 511 rest = some ana) (a b q r : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 6) (C (C a b) (C q r))) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 6) (C (C a b) (C q r))) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
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
        simp [nock_exec, Ana.folStep, shape, e, h, e2, h2, e3, h3]
      | some r3 =>
        rw [e3] at h3
        obtain ⟨o3, g3⟩ := r3
        simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h3
        have hd := double_int_pill o2.prod o3.prod
        generalize o2.prod.toNoun = n10 at h2 hd ⊢
        generalize o3.prod.toNoun = n11 at h3 hd ⊢
        simp [nock_exec, Ana.folStep, shape, e, h, e2, h2, e3, h3, rest_lib hana, double_int.arm_at,
          double_int_arm, hd]
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

/-- `[%10 [a=@ don=*] rec=^]`: an edit, through `+darn:so` and `+edit:pi`; the
axis `0` is the default. -/
theorem fol_loop_op10 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go)
    (hana : slot? 511 rest = some ana) (ax : Nat) (don r1 r2 : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 10) (C (C (A ax) don) (C r1 r2))) sub seat mk bc df gen)
        fol_loop.battery
      = (Ana.folStep env res go (C (A 10) (C (C (A ax) don) (C r1 r2))) sub seat mk bc df
          gen).map (folOutNoun regsNoun) := by
  unfold folSubj
  rcases Nat.eq_zero_or_pos ax with rfl | hax
  · nock_open fol_loop.battery
    simp [nock_exec, Ana.folStep, shape, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun,
      Anno.dunno, Sock.dunno, Sock.toNoun, Cape.toNoun, flag]
  have hax0 : ax ≠ 0 := by omega
  have hax0' : ¬ (0 = ax) := by omega
  have h := hgo don sub seat mk bc df gen
  unfold folSubj at h
  nock_open fol_loop.battery
  cases e : go don sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h, hax0, hax0']
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
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2, hax0, hax0']
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
        simp [nock_exec, Ana.folStep, shape, e, h, e2, h2, e3, hd, hax0, hax0', rest_lib hana,
          so.lib.arm_at, so_lib_arm, so.darn.arm_at, so_darn_arm]
      | some s =>
        rw [e3] at hd
        simp [nock_exec, Ana.folStep, shape, e, h, e2, h2, e3, hd, hp, hax0, hax0', rest_lib hana,
          so.lib.arm_at, so_lib_arm, so.darn.arm_at, so_darn_arm, pi.lib.arm_at, pi_lib_arm,
          pi.edit.arm_at, pi_edit_arm]
        simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, flag]

/-! ## The default and the static hint -/

/-- The default of the `?+`: a formula of no case (`shape` says `other`) is
`[0 0]` with no knowledge. -/
theorem fol_loop_other (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest fol : Noun) (hs : shape fol = Shape.other) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
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
  nock_open fol_loop.battery
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
theorem fol_loop_op11s (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go) (p : Nat) (a b : Noun)
    (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 11) (C (A p) (C a b))) sub seat mk bc df gen)
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
    nock_open fol_loop.battery
    simp [nock_exec, Ana.folStep, shape, h, Tag.bare, Nock.n3, Nock.n2, Nock.slot, Nock.quote]
  · have hp' : ¬ (0x65726162 = p) := fun e => hp (by rw [← e]; rfl)
    have h := hgo (C a b) sub seat mk bc df gen
    unfold folSubj at h ⊢
    nock_open fol_loop.battery
    cases e : go (C a b) sub seat mk bc df gen with
    | none =>
      rw [e] at h
      simp [nock_exec, Ana.folStep, shape, e, h, hp, hp']
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
      simp [nock_exec, Ana.folStep, shape, e, h, hp, hp']
      simp [folOutNoun, FolOut.toNoun, Nomm.toNoun, flag]

end Compiler
end Formalization
