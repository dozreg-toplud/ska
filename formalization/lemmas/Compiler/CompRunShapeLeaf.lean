import lemmas.Compiler.CompRunShapeCut
import lemmas.Ska.RunShape

/-!
# The link of `+run-shape`: the frame, `[1 k]`, `[0 a]`, `[7 p q]` (track A, 2026-11-27)

The gate of `+run-shape` (`rsGate`, `CompRunShapeCut.lean`) runs on its core

    [rsGate [[nomm goal sup] [comp.door [gen ctx]]]]

and a recursive `$(..)` is `[9 2 10 [..] ..]` on that core, so the statement of a case,
`RsAt`, is on this core: the gate on the noun of a nomm, a goal and `sup` gives the model
`runShape env sup` with the noun of its `laze` and the new `gen`.  `+run-shape` reads and
changes only `id-gen` and `sofs` of `gen` (`RSt`); the other eight fields are the nouns of
`RsRest`, kept as they are.  `sup` is the noun of the model's `Option Nomm`.

* `rs_push`: the three pushes (`none`, `this`, `simple`) on any goal.
* `rs_disp_n0`, `rs_disp_n1`, `rs_disp_n7`: the `?-` takes the case.
* **`rs_n1`**: the case `[1 k]` on every goal and state.
* **`rs_n0`**: the case `[0 a]`, given `LazeFromAt` (the link of `+laze-from`, door arm
  `0x1576a`, not linked yet) at the door.
* **`rs_n7`**: the case `[7 p q]` from `RsAt` of its two recursive calls.
* **`rs_cls`**: by induction, `RsAt` on every nomm of `RsCls` (built of `[0 a]`, `[1 k]`,
  `[7 p q]`), every `sup`, goal and state, given `LazeFromAt` at the door.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The fields of `gen` that `+run-shape` neither reads nor writes, but `cache` (read by
`+callee-need` and `+callee-sure`; the model has their answers in `ShapeEnv`). -/
structure RsRest where
  re : Noun
  bo : Noun
  mode : Noun
  blocks : Noun
  tags : Noun
  cond : Noun
  cache : Noun
  soft : Noun

/-- The noun of `gen`: `id-gen` and `sofs` from the model's state. -/
noncomputable def rsGenNoun (st : RSt CSet) (y : RsRest) : Noun :=
  C y.re (C y.bo (C (A st.idg) (C y.mode (C y.blocks (C y.tags (C y.cond (C y.cache
    (C y.soft (HoonSet.toNoun st.sofs)))))))))

/-- The door's core. -/
noncomputable def rsDoor (st : RSt CSet) (y : RsRest) (ctx : Noun) : Noun := C comp.door (C (rsGenNoun st y) ctx)

/-- The gate's core on the sample `[nomm goal sup]`. -/
def rsCoreG (nomm goal sup D : Noun) : Noun := C rsGate (C (C nomm (C goal sup)) D)

/-- The noun of a goal. -/
def _root_.Formalization.SkaModel.Comp.GoalS.toNoun {S : Type} [HoonSet S] : GoalS S → Noun
  | GoalS.pick => C (A 0x6b636970) (A 0)
  | GoalS.done => C (A 0x656e6f64) (A 0)
  | GoalS.next l => C (A 0x7478656e) l.toNoun

/-- The noun of `sup`. -/
def supNoun (sup : Option Nomm) : Noun := unitNoun Nomm.toNoun sup

/-- **The gate of `+run-shape` is the model** on the nomm `n`, the goal and `sup`, from the
state `st`, for every rest `y` of `gen`. -/
def RsAt (ctx : Noun) (env : ShapeEnv) (n : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) : Prop :=
  ∀ y : RsRest, nock (rsCoreG n.toNoun goal.toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
    = (runShape env sup n goal st).map fun p => C p.1.toNoun (rsGenNoun p.2 y)

/-- The noun of `none`. -/
theorem noneL_noun : (noneL : Laze CSet).toNoun = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)) := by
  simp [noneL, Laze.toNoun, SureO.bunt, SureO.toNoun, NeedOrd.toNoun, Tag.none, Laze.forksNoun,
    Laze.bondsNoun, HoonSet.toNoun_empty]

/-- The noun of `this`. -/
theorem thisL_noun : (thisL : Laze CSet).toNoun = C (C (C (A 0x73696874) (A 0)) (A 0)) (C (A 0) (A 0)) := by
  simp [thisL, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, Tag.this, Laze.forksNoun,
    Laze.bondsNoun, HoonSet.toNoun_empty]

/-- The noun `simple`: the goal itself when it is `%next`, else `[%next this]`. -/
noncomputable def rsSimpleN (goal : GoalS CSet) : Noun := (GoalS.next (simpleS goal)).toNoun

/-- The subject of the cases. -/
def rsS (simple nomm goal sup D : Noun) : Noun :=
  C simple (C (C (C (C (A 0x73696874) (A 0)) (A 0)) (C (A 0) (A 0)))
    (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (rsCoreG nomm goal sup D)))

/-- **The three pushes** of the gate, on any goal. -/
theorem rs_push (goal : GoalS CSet) (nomm sup D : Noun) :
    nock (rsCoreG nomm goal.toNoun sup D) rsGate
      = nock (rsS (rsSimpleN goal) nomm goal.toNoun sup D) rsDol := by
  cases goal <;>
  simp [rsGate, rsNoneF, rsThisF, rsSimpleF, rsCoreG, rsS, rsSimpleN, GoalS.toNoun, simpleS,
    thisL_noun, nock_exec]

theorem rs_disp_n1 (k s goal sup D : Noun) :
    nock (rsS s (C (A 1) k) goal sup D) rsDol = nock (rsS s (C (A 1) k) goal sup D) rsK1 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

theorem rs_disp_n0 (a : Nat) (s goal sup D : Noun) :
    nock (rsS s (C (A 0) (A a)) goal sup D) rsDol = nock (rsS s (C (A 0) (A a)) goal sup D) rsK0 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

theorem rs_disp_n7 (t s goal sup D : Noun) :
    nock (rsS s (C (A 7) t) goal sup D) rsDol = nock (rsS s (C (A 7) t) goal sup D) rsK7 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

variable {ctx : Noun}

/-- **The case `[1 k]`**: `[none gen]`, on every goal. -/
theorem rs_n1 (env : ShapeEnv) (k : Noun) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet) :
    RsAt ctx env (Nomm.n1 k) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n1]
  simp [rsK1, rsS, rsCoreG, rsDoor, nock_exec, runShape, pure, StateT.pure, noneL_noun]

/-- **The case `[7 p q]`** from the runs of `q` (with `sup` `p`) and of `p` (on the goal
`[%next l]` of the product `l` of `q`, from the state `q` left). -/
theorem rs_n7 (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hq : RsAt ctx env q (some p) goal st)
    (hp : ∀ l st1, RsAt ctx env p sup (GoalS.next l) st1) :
    RsAt ctx env (Nomm.n7 p q) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n7]
  have hq' := hq y
  simp only [rsCoreG, supNoun, unitNoun, rsDoor] at hq'
  nock_open rsK7
  cases e : runShape env (some p) q goal st with
  | none =>
    rw [e] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e, bind, StateT.bind]
  | some r =>
    obtain ⟨l, st1⟩ := r
    rw [e] at hq'
    have hp' := hp l st1 y
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e, bind, StateT.bind]
    exact hp'

/-- **The link of `+laze-from`** (door arm `0x1576a`) at the door `D`, not proved yet: the
arm makes a gate whose slam on `[a laz]` is the model `lazeFrom`. -/
def LazeFromAt (D : Noun) : Prop :=
  ∃ bat sam c, nock D (C (A 9) (C (A 0x1576a) (C (A 0) (A 1)))) = some (C bat (C sam c)) ∧
    ∀ (a : Nat) (laz : Laze CSet), nock (C bat (C (C (A a) laz.toNoun) c)) bat = (lazeFrom a laz).map Laze.toNoun

/-- **The case `[0 a]`**: `none` at `0`, the goal's need at `1`, `+laze-from` of it
elsewhere, given the link of `+laze-from`. -/
theorem rs_n0 (env : ShapeEnv) (a : Nat) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hf : ∀ y, LazeFromAt (rsDoor st y ctx)) :
    RsAt ctx env (Nomm.n0 a) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n0]
  obtain ⟨bat, sam, c, h9, hg⟩ := hf y
  have hg' := hg a (simpleS goal)
  simp only [nock_exec, rsDoor] at h9
  nock_open rsK0
  by_cases h0 : a = 0
  · subst h0
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, pure, StateT.pure, noneL_noun]
  · by_cases h1 : a = 1
    · subst h1
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, pure, StateT.pure, rsSimpleN, GoalS.toNoun]
    · have h0' : ¬ (0 = a) := fun h => h0 h.symm
      have h1' : ¬ (1 = a) := fun h => h1 h.symm
      cases e : lazeFrom a (simpleS goal) with
      | none =>
        rw [e] at hg'
        simp [nock_exec, rsS, rsCoreG, rsDoor, h0, h1, h0', h1', h9, hg', runShape, liftS, e, rsSimpleN, GoalS.toNoun]
      | some l =>
        rw [e] at hg'
        simp [nock_exec, rsS, rsCoreG, rsDoor, h0, h1, h0', h1', h9, hg', runShape, liftS, e, rsSimpleN, GoalS.toNoun]

/-- The nomms built of the cases linked so far: `[0 a]`, `[1 k]`, `[7 p q]`. -/
def RsCls : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n7 p q => RsCls p ∧ RsCls q
  | _ => False

/-- **The induction over the cases linked so far**: on every nomm of `RsCls`, every `sup`,
goal and state, the gate of `+run-shape` is `runShape`, given the link of `+laze-from` at
every state of the door. -/
theorem rs_cls (env : ShapeEnv) (hf : ∀ st y, LazeFromAt (rsDoor st y ctx)) :
    ∀ (n : Nomm), RsCls n → ∀ sup goal st, RsAt ctx env n sup goal st
  | Nomm.n0 a, _, sup, goal, st => rs_n0 env a sup goal st (hf st)
  | Nomm.n1 k, _, sup, goal, st => rs_n1 env k sup goal st
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st =>
    rs_n7 env p q sup goal st (rs_cls env hf q hq (some p) goal st)
      (fun l st1 => rs_cls env hf p hp sup (GoalS.next l) st1)

end Compiler
end Formalization
