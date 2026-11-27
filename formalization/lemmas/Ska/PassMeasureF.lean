import lemmas.Ska.PassMeasureW
import lemmas.Ska.AnaFuel

/-!
# The pass loop returns at some fuel (track F, Gaps 16)

`passOn_wf_W` says that the passes of a component that go on are finitely
many.  Here that becomes a statement about fuel: **the pass loop returns at
some fuel whenever each of its passes does**, that is, at every state the
passes reach, the pass either stops on its own (with a continuation that
always fails it still returns: `+sweep`, the member loop, `+cull` and `+pop`
returned) or goes on with a change (`PassOn`, its `+sweep` and member loop
returned), at some fuel, and `next` stays below a bound `B`
(`passLoop_returns`).  Since dab8478 a pass can also go on with no change
(a member that `id` reaches is dirty at the end): such a quiet pass is neither,
so `passLoop_returns` asks that none is reached; that the quiet passes are
finitely many is not proved.

The argument: no infinite chain of passes (`passOn_wf_W`) gives `Acc` of the
pass relation by dependent choice (`acc_of_no_chain`); by induction on it, a
pass that stops returns at its fuel plus two (`passStep_le`), and a pass that
goes on at fuel `m` goes on at every fuel above (`passOn_mono`), so the pass
loop at `max m n' + 1` is the pass loop of the next pass at `max m n'`
(`passLoop_of_on`), which returns by the fuel monotonicity of `AnaFuel.lean`.

Left for the parts: `+sweep` and `+cull` are loops over the members and their
callee sets (each step either consumes one callee of a frame or inserts a new
member into `seen`/`live`), so a fuel of `(|members| + 1) * (K + 1) + 1`, `K`
the largest callee set, is enough; not proved here.  The member loop is
structural over its list, but each step is a `+run`, which is the whole
recursion (`fol-loop`, and `+analyze` of the callees inside it); its fuel is
the open part of `CgHalts`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **No infinite descending chain gives `Acc`**, by dependent choice. -/
theorem acc_of_no_chain {α : Type} {r : α → α → Prop} (h : ∀ f : Nat → α, ¬ ∀ k, r (f (k + 1)) (f k))
    (x : α) : Acc r x := by
  refine Classical.byContradiction fun hx => ?_
  have step : ∀ y : {y // ¬ Acc r y}, ∃ z : {z // ¬ Acc r z}, r z.1 y.1 := by
    intro y
    refine Classical.byContradiction fun hn => y.2 ⟨_, fun z hz => Classical.byContradiction fun hz' => ?_⟩
    exact hn ⟨⟨z, hz'⟩, hz⟩
  let g : Nat → {y // ¬ Acc r y} := fun k =>
    Nat.rec (motive := fun _ => {y // ¬ Acc r y}) ⟨x, hx⟩ (fun _ y => Classical.choose (step y)) k
  exact h (fun k => (g k).1) (fun k => Classical.choose_spec (step (g k)))

/-- **A pass that goes on at fuel `m` goes on at every fuel above.** -/
theorem passOn_mono {env : Env R} {memoF : Memo M} {m m' : Nat} (h : m ≤ m') {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hp : PassOn env memoF m id index pass st st') :
    PassOn env memoF m' id index pass st st' := by
  obtain ⟨ab, members, r, h1, h2, h3, h4, h6⟩ := hp
  exact ⟨ab, members, r, h1,
    fuel_chain (f := fun k => sweep k id (Treap.silt ab) st) (fun k => sweep_fuel k id _ st) h _ h2,
    memberLoop_fuel_le env memoF h _ _ _ _ _ h3, h4, h6⟩

/-- The states that the passes of the component of `id` reach from `x`
(the pass number and the state), each pass going on at some fuel. -/
inductive PassReach (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R) :
    Nat × SkaState M R → Prop
  | refl : PassReach env memoF id index x x
  | step {y : Nat × SkaState M R} {st' : SkaState M R} {m : Nat} :
      PassReach env memoF id index x y → PassOn env memoF m id index y.1 y.2 st' →
      PassReach env memoF id index x (y.1 + 1, st')

theorem passReach_inv (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) {id : Ident} {index : Nat} {x y : Nat × SkaState M R}
    (h : PassReach env memoF id index x y) (hi : SInv x.2) (ht : TInv x.2) (hw : WInv x.2) :
    SInv y.2 ∧ TInv y.2 ∧ WInv y.2 := by
  induction h with
  | refl => exact ⟨hi, ht, hw⟩
  | step _ hp ih =>
    obtain ⟨a, b, c, _, _⟩ := passOn_inv env memoF hmF hmT (run_winv env memoF hmF hmT hmN)
      ih.1 ih.2.1 ih.2.2 hp
    exact ⟨a, b, c⟩

/-- One pass that goes on, among the states reached from `x`: from `b` to `a`. -/
def PassNext (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R)
    (a b : Nat × SkaState M R) : Prop :=
  PassReach env memoF id index x b ∧ ∃ m, a.1 = b.1 + 1 ∧ PassOn env memoF m id index b.1 b.2 a.2

/-- **The passes reached from `x` are well founded**, with `next` bounded
along them. -/
theorem passNext_acc (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) {id : Ident} {index B : Nat} (x : Nat × SkaState M R)
    (hi : SInv x.2) (ht : TInv x.2) (hw : WInv x.2)
    (hB : ∀ y, PassReach env memoF id index x y → y.2.next ≤ B) :
    Acc (PassNext env memoF id index x) x := by
  refine acc_of_no_chain (fun f hf => ?_) x
  have hreach : ∀ k, PassReach env memoF id index x (f k) := fun k => (hf k).1
  have hidx : ∀ k, (f k).1 = (f 0).1 + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      obtain ⟨_, m, e, _⟩ := hf k
      rw [e, ih]; rfl
  obtain ⟨i0, t0, w0⟩ := passReach_inv env memoF hmF hmT hmN (hreach 0) hi ht hw
  exact passOn_wf_W env memoF hmF hmT hmN id index (f 0).1 B (fun k => (f k).2) i0 t0 w0
    (fun k => by obtain ⟨_, m, _, hp⟩ := hf k; exact ⟨m, by rw [← hidx k]; exact hp⟩)
    (fun k => hB _ (hreach k))

/-- **The pass loop returns at some fuel whenever each of its passes does**:
from a state with `SInv`, `TInv` and `WInv`, if at every state the passes
reach the pass stops on its own at some fuel (it returns with a continuation
that always fails) or goes on at some fuel, and `next` stays at most `B`,
then the pass loop returns. -/
theorem passLoop_returns (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) (id : Ident) (index B : Nat) (x : Nat × SkaState M R)
    (hi : SInv x.2) (ht : TInv x.2) (hw : WInv x.2)
    (hB : ∀ y, PassReach env memoF id index x y → y.2.next ≤ B)
    (hparts : ∀ y, PassReach env memoF id index x y → ∃ m,
      (∃ r, passStep m (memberLoop env memoF m) (fun _ _ _ _ => none) id index y.1 y.2 = some r) ∨
      ∃ st', PassOn env memoF m id index y.1 y.2 st') :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r := by
  suffices H : ∀ y, Acc (PassNext env memoF id index x) y → PassReach env memoF id index x y →
      ∃ n r, passLoop env memoF n id index y.1 y.2 = some r from
    H x (passNext_acc env memoF hmF hmT hmN x hi ht hw hB) PassReach.refl
  intro y hacc
  induction hacc with
  | intro y _ ih =>
    intro hy
    obtain ⟨m, hstop | ⟨st', hon⟩⟩ := hparts y hy
    · obtain ⟨r, hr⟩ := hstop
      refine ⟨m + 2, r, ?_⟩
      rw [passLoop_succ]
      exact passStep_le m (fun index pass ms st => (fuelStep env memoF m).mem index pass ms st)
        (fun _ _ _ _ _ h => by cases h) id index y.1 y.2 r hr
    · obtain ⟨n', r', hr'⟩ := ih (y.1 + 1, st') ⟨hy, m, rfl, hon⟩ (PassReach.step hy hon)
      refine ⟨max m n' + 1, r', ?_⟩
      rw [passLoop_of_on (passOn_mono (Nat.le_max_left m n') hon)]
      exact passLoop_fuel_le env memoF (Nat.le_max_right m n') id index (y.1 + 1) st' r' hr'

end Ana
end SkaModel
end Formalization
