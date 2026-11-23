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

end Compiler
end Formalization
