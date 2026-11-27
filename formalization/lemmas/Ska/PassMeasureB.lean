import lemmas.Ska.PassMeasureF

/-!
# The bound on `next`, restated (track F, Gaps 16)

`passOn_wf_W` and `passLoop_returns` name one hypothesis: a bound `B` on
`next` along the passes.  It was meant to follow from (i) finitely many
identities and (b) "an identity that a pass's `+cull` drops is never pushed
again".  **(b) is false on the real compiler**
(`formalization/tools/hoon/repush.hoon`): an identity `(s, f)` that `+cull`
dropped is analysed afresh in a later pass of the same component, by another
call site whose subject reaches `s` later, or by the same call site, whose
subject goes back up to `s` when a callee upstream is replaced by a fresh
entry whose first product knows more.  On the witnesses the pass loop still
returns: one identity is pushed up to five times (one per call site whose
subject passes through it), or twice by one site.

What the two theorems use is only that `next` is bounded along each chain of
passes.  `next` grows by one at every push (every fresh `+analyze`), so this
is: **every chain of passes pushes finitely often**, which, with the finite
set of identities of (i), is "every identity is pushed finitely often along
it".  `FinPushes` states it per chain, without a bound fixed in advance; the
old hypothesis implies it (`finPushes_of_bound`), and the two theorems go
through with it (`passOn_wf_fin`, `passNext_acc_fin`, `passLoop_returns_fin`).

What `FinPushes` needs, not proved: every entry present at two consecutive
passes falls or stays (the merge of `+run`: `runDatum_prod_step`, the code
requirement united with the old one), so an identity present from some pass
on changes finitely often; the root is never culled.  The rest is an eventual
stabilisation along the evaluation order of each run: a call site whose
subject is eventually constant has an eventually constant callee, once the
entries `+hit-test` reads (`less-code`, `indi` of the members of the stack
with its formula) stop changing, and that callee is then never culled.  The
point that is open is the dependence of the resolution on the stack: a fresh
push of another identity of the same formula, higher on the stack, can take
over a site that resolved by `%rec`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **Finitely many pushes along every chain of passes from `x`**: along each
infinite sequence of passes of the component that go on, `next` (one more at
every push) stays below some bound, which may depend on the chain. -/
def FinPushes (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R) : Prop :=
  ∀ f : Nat → Nat × SkaState M R, (∀ k, PassNext env memoF id index x (f (k + 1)) (f k)) →
    ∃ B, ∀ k, (f k).2.next ≤ B

/-- The bound of `passLoop_returns` gives `FinPushes`. -/
theorem finPushes_of_bound {env : Env R} {memoF : Memo M} {id : Ident} {index B : Nat}
    {x : Nat × SkaState M R} (hB : ∀ y, PassReach env memoF id index x y → y.2.next ≤ B) :
    FinPushes env memoF id index x :=
  fun f hf => ⟨B, fun k => hB _ (hf k).1⟩

/-- **`passOn_wf_W` with finitely many pushes**: no infinite sequence of passes
that go on and push only finitely often. -/
theorem passOn_wf_fin (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) (id : Ident) (index p : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : WInv (f 0))
    (hon : ∀ k, ∃ n, PassOn env memoF n id index (p + k) (f k) (f (k + 1)))
    (hB : ∃ B, ∀ k, (f k).next ≤ B) : False := by
  obtain ⟨B, hB⟩ := hB
  exact passOn_wf_W env memoF hmF hmT hmN id index p B f h0i h0t h0w hon hB

/-- **The passes reached from `x` are well founded** when every chain of them
pushes finitely often. -/
theorem passNext_acc_fin (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) {id : Ident} {index : Nat} (x : Nat × SkaState M R)
    (hi : SInv x.2) (ht : TInv x.2) (hw : WInv x.2) (hB : FinPushes env memoF id index x) :
    Acc (PassNext env memoF id index x) x := by
  refine acc_of_no_chain (fun f hf => ?_) x
  obtain ⟨B, hB'⟩ := hB f hf
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
    (fun k => by obtain ⟨_, m, _, hp⟩ := hf k; exact ⟨m, by rw [← hidx k]; exact hp⟩) hB'

/-- **The pass loop returns at some fuel whenever each of its passes does and
every chain of passes pushes finitely often** (`passLoop_returns` with
`FinPushes` in place of the bound `B`). -/
theorem passLoop_returns_fin (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) (id : Ident) (index : Nat) (x : Nat × SkaState M R)
    (hi : SInv x.2) (ht : TInv x.2) (hw : WInv x.2)
    (hB : FinPushes env memoF id index x)
    (hparts : ∀ y, PassReach env memoF id index x y → ∃ m,
      (∃ r, passStep m (memberLoop env memoF m) (fun _ _ _ _ => none) id index y.1 y.2 = some r) ∨
      ∃ st', PassOn env memoF m id index y.1 y.2 st') :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r := by
  suffices H : ∀ y, Acc (PassNext env memoF id index x) y → PassReach env memoF id index x y →
      ∃ n r, passLoop env memoF n id index y.1 y.2 = some r from
    H x (passNext_acc_fin env memoF hmF hmT hmN x hi ht hw hB) PassReach.refl
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
