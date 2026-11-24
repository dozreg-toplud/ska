import lemmas.Ska.Types

/-!
# `+mink`, `+mook` and `+mock` of `hoon.hoon`, as Lean models

`+mink` may not halt, so its model is fuelled: `minkF lib gul n trace s f`
runs it with `n` levels of recursion, and `none` is a crash of the Nock that
runs it, a run that needs more fuel, or one that never ends.  `Mink` is the
relation: some fuel is enough.  The trace is the one that `+mink` keeps in
its subject (`=| trace`); `+mink` itself starts it empty.

The arms of `hoon.hoon` that the models call and that do not matter to the
proofs are parameters, in `Lib`: slamming the scry gate, `(soft tank)`, the
branches of `+rend:mook` other than a `%mean` of a cell, and the cord that
`+mook` puts in place of skipped frames.  The same `Lib` serves `+mook` and
the interpreter's `+eval-mook`, which run the same arms.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The arms of `hoon.hoon` that the models take as given. -/
structure Lib where
  /-- `(gate sample)`: the product of slamming a gate, `none` on a crash. -/
  slam : Noun → Noun → Option Noun
  /-- `((soft tank) n)`: `none` is `~`. -/
  softTank : Noun → Option Noun
  /-- `+rend:mook` on a frame other than `[%mean ^]`. -/
  rendBase : Nat → Noun → Option Noun
  /-- `(crip "[skipped {(scow %ud n)} frames]")`. -/
  skipMsg : Nat → Noun

/-! ## Options ordered by definedness -/

/-- `x` is below `y`: whatever `x` returns, `y` returns. -/
def OptLe {α : Type} (x y : Option α) : Prop := ∀ a, x = some a → y = some a

theorem OptLe.refl {α : Type} (x : Option α) : OptLe x x := fun _ h => h

theorem OptLe.bind {α β : Type} {x x' : Option α} {f f' : α → Option β}
    (hx : OptLe x x') (hf : ∀ a, OptLe (f a) (f' a)) : OptLe (x.bind f) (x'.bind f') := by
  intro b h
  cases x with
  | none => simp at h
  | some a =>
    rw [hx a rfl]
    exact hf a b h

/-! ## `+mink` -/

/-- `?.  ?=(%0 -.x)  x`: go on with the product if the tone is `%0`, else
return the tone. -/
def tbind (x : Option Tone) (k : Noun → Option Tone) : Option Tone :=
  match x with
  | none => none
  | some (Tone.zero p) => k p
  | some t => some t

@[simp] theorem tbind_none (k : Noun → Option Tone) : tbind none k = none := rfl
@[simp] theorem tbind_zero (p : Noun) (k : Noun → Option Tone) :
    tbind (some (Tone.zero p)) k = k p := rfl
@[simp] theorem tbind_one (p : Noun) (k : Noun → Option Tone) :
    tbind (some (Tone.one p)) k = some (Tone.one p) := rfl
@[simp] theorem tbind_two (t : Trace) (k : Noun → Option Tone) :
    tbind (some (Tone.two t)) k = some (Tone.two t) := rfl

theorem OptLe.tbind {x x' : Option Tone} {k k' : Noun → Option Tone}
    (hx : OptLe x x') (hk : ∀ p, OptLe (k p) (k' p)) : OptLe (tbind x k) (tbind x' k') := by
  intro r h
  match x, h with
  | some (Tone.zero p), h => rw [hx _ rfl]; exact hk p r h
  | some (Tone.one p), h => rw [hx _ rfl]; exact h
  | some (Tone.two t), h => rw [hx _ rfl]; exact h

theorem tbind_eq_some {x : Option Tone} {k : Noun → Option Tone} {r : Tone}
    (h : tbind x k = some r) :
    (∃ p, x = some (Tone.zero p) ∧ k p = some r) ∨
      (x = some r ∧ ∀ p, r ≠ Tone.zero p) := by
  match x, h with
  | some (Tone.zero p), h => exact Or.inl ⟨p, rfl, h⟩
  | some (Tone.one p), h => cases h; exact Or.inr ⟨rfl, fun _ h => Tone.noConfusion h⟩
  | some (Tone.two t), h => cases h; exact Or.inr ⟨rfl, fun _ h => Tone.noConfusion h⟩

/-- One level of `+mink`: `go` runs the subformulas, with the trace it is
given.  The cases are those of the `?+` in `+mink`, in its order; anything
else is `[%2 trace]`.  The `.*` at the end of the two cases of `%11` is the
product of the hinted formula. -/
def minkStep (lib : Lib) (gul : Noun) (go : Trace → Noun → Noun → Option Tone)
    (trace : Trace) (s f : Noun) : Option Tone :=
  match f with
  | Noun.cell (Noun.cell a b) c =>
      tbind (go trace s (C a b)) fun ph =>
        tbind (go trace s c) fun pt => some (Tone.zero (C ph pt))
  | Noun.cell (Noun.atom 0) (Noun.atom axis) =>
      match slot? axis s with
      | none => some (Tone.two trace)
      | some p => some (Tone.zero p)
  | Noun.cell (Noun.atom 1) k => some (Tone.zero k)
  | Noun.cell (Noun.atom 2) (Noun.cell b c) =>
      tbind (go trace s b) fun s' =>
        tbind (go trace s c) fun f' => go trace s' f'
  | Noun.cell (Noun.atom 3) b =>
      tbind (go trace s b) fun p => some (Tone.zero (wut p))
  | Noun.cell (Noun.atom 4) b =>
      tbind (go trace s b) fun p =>
        match p with
        | Noun.cell _ _ => some (Tone.two trace)
        | Noun.atom a => some (Tone.zero (A (a + 1)))
  | Noun.cell (Noun.atom 5) (Noun.cell b c) =>
      tbind (go trace s b) fun x =>
        tbind (go trace s c) fun y => some (Tone.zero (eqCode x y))
  | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) =>
      tbind (go trace s b) fun t =>
        match t with
        | Noun.atom 0 => go trace s c
        | Noun.atom 1 => go trace s d
        | _ => some (Tone.two trace)
  | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
      tbind (go trace s b) fun s' => go trace s' c
  | Noun.cell (Noun.atom 8) (Noun.cell b c) =>
      tbind (go trace s b) fun h => go trace (C h s) c
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom axis) c) =>
      tbind (go trace s c) fun core =>
        match slot? axis core with
        | none => some (Tone.two trace)
        | some arm => go trace core arm
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom axis) v) tgt) =>
      if axis = 0 then some (Tone.two trace) else
      tbind (go trace s tgt) fun t =>
        tbind (go trace s v) fun x =>
          match edit? axis x t with
          | none => some (Tone.two trace)
          | some r => some (Tone.zero r)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) nx) =>
      tbind (go trace s nx) fun p => some (Tone.zero p)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) clue) nx) =>
      tbind (go trace s clue) fun c =>
        tbind (go (if stopTag tag then (tag, c) :: trace else trace) s nx) fun p =>
          some (Tone.zero p)
  | Noun.cell (Noun.atom 12) (Noun.cell ref path) =>
      tbind (go trace s ref) fun r =>
        tbind (go trace s path) fun p =>
          if gul = A 0 then some (Tone.two trace) else
          (lib.slam gul (C r p)).bind fun res =>
            (scryDecode res).bind fun d =>
              match d with
              | ScryRes.block => some (Tone.one p)
              | ScryRes.hunk => some (Tone.two ((Tag.hunk, C r p) :: trace))
              | ScryRes.val v => some (Tone.zero v)
  | _ => some (Tone.two trace)

/-- `+mink` with fuel: `minkF lib gul n trace s f` is the inner loop of
`(mink [s f] gul)` with the trace `trace`, given `n` levels of recursion. -/
def minkF (lib : Lib) (gul : Noun) : Nat → Trace → Noun → Noun → Option Tone
  | 0 => fun _ _ _ => none
  | n + 1 => minkStep lib gul (minkF lib gul n)

/-- `+mink` returns `r` on `[s f]`, from the trace `trace`. -/
def Mink (lib : Lib) (gul : Noun) (trace : Trace) (s f : Noun) (r : Tone) : Prop :=
  ∃ n, minkF lib gul n trace s f = some r

theorem minkStep_mono (lib : Lib) (gul : Noun) {go go' : Trace → Noun → Noun → Option Tone}
    (h : ∀ t s f, OptLe (go t s f) (go' t s f)) (trace : Trace) (s f : Noun) :
    OptLe (minkStep lib gul go trace s f) (minkStep lib gul go' trace s f) := by
  unfold minkStep
  split
  all_goals first
    | exact OptLe.refl _
    | skip
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.tbind (h _ _ _) fun _ => h _ _ _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · refine OptLe.tbind (h _ _ _) fun t => ?_
    split
    · exact h _ _ _
    · exact h _ _ _
    · exact OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => h _ _ _
  · exact OptLe.tbind (h _ _ _) fun _ => h _ _ _
  · refine OptLe.tbind (h _ _ _) fun core => ?_
    split
    · exact OptLe.refl _
    · exact h _ _ _
  · split
    · exact OptLe.refl _
    · exact OptLe.tbind (h _ _ _) fun _ => OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.tbind (h _ _ _) fun _ => OptLe.refl _
  · exact OptLe.tbind (h _ _ _) fun _ => OptLe.tbind (h _ _ _) fun _ => OptLe.refl _

theorem minkF_succ (lib : Lib) (gul : Noun) :
    ∀ (n : Nat) (t : Trace) (s f : Noun), OptLe (minkF lib gul n t s f) (minkF lib gul (n + 1) t s f)
  | 0, _, _, _ => fun _ h => by simp [minkF] at h
  | n + 1, t, s, f => minkStep_mono lib gul (fun t s f => minkF_succ lib gul n t s f) t s f

theorem minkF_le (lib : Lib) (gul : Noun) {n m : Nat} (hle : n ≤ m) (t : Trace) (s f : Noun) :
    OptLe (minkF lib gul n t s f) (minkF lib gul m t s f) := by
  induction hle with
  | refl => exact OptLe.refl _
  | step _ ih => exact fun r h => minkF_succ lib gul _ t s f r (ih r h)

theorem minkF_det (lib : Lib) (gul : Noun) {n m : Nat} {t : Trace} {s f : Noun} {r r' : Tone}
    (h : minkF lib gul n t s f = some r) (h' : minkF lib gul m t s f = some r') : r = r' := by
  have h1 := minkF_le lib gul (Nat.le_max_left n m) t s f r h
  have h2 := minkF_le lib gul (Nat.le_max_right n m) t s f r' h'
  rw [h1] at h2
  exact Option.some.inj h2

theorem Mink.det {lib : Lib} {gul : Noun} {t : Trace} {s f : Noun} {r r' : Tone}
    (h : Mink lib gul t s f r) (h' : Mink lib gul t s f r') : r = r' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  exact minkF_det lib gul hn hm

/-! ## Nock's products are `+mink`'s `%0`

`+mink` takes the tag of a dynamic hint `[11 [b c] d]` to be an atom and
returns `[%2 trace]` when `b` is a cell, while the Nock specification (and
`Eval`) reduces it like any other hint.  `EvalH` is `Eval` with that one
difference, and with opcode 9 stated by its arm; `EvalH.toEval` shows that it
is a part of `Eval`, and `eval_cell_tag` below shows that the difference is
real.
-/

/-- `Eval` where the tag of a dynamic hint is an atom. -/
inductive EvalH : Noun → Noun → Noun → Prop where
  | cell {s b c d l r} : EvalH s (C b c) l → EvalH s d r → EvalH s (C (C b c) d) (C l r)
  | op0 {s axis out} : Slot axis s out → EvalH s (slot axis) out
  | op1 {s k} : EvalH s (quote k) k
  | op2 {s b c s' f' out} : EvalH s b s' → EvalH s c f' → EvalH s' f' out → EvalH s (n3 (A 2) b c) out
  | op3 {s b x} : EvalH s b x → EvalH s (n2 (A 3) b) (wut x)
  | op4 {s b a} : EvalH s b (A a) → EvalH s (n2 (A 4) b) (A (a + 1))
  | op5 {s b c x y} : EvalH s b x → EvalH s c y → EvalH s (n3 (A 5) b c) (eqCode x y)
  | op6_zero {s b c d out} : EvalH s b (A 0) → EvalH s c out → EvalH s (n4 (A 6) b c d) out
  | op6_one {s b c d out} : EvalH s b (A 1) → EvalH s d out → EvalH s (n4 (A 6) b c d) out
  | op7 {s b c s' out} : EvalH s b s' → EvalH s' c out → EvalH s (n3 (A 7) b c) out
  | op8 {s b c x out} : EvalH s b x → EvalH (C x s) c out → EvalH s (n3 (A 8) b c) out
  | op9 {s axis c core arm out} :
      EvalH s c core → Slot axis core arm → EvalH core arm out → EvalH s (n3 (A 9) (A axis) c) out
  | op10 {s axis c d rep base out} :
      EvalH s c rep → EvalH s d base → Edit axis rep base out →
      EvalH s (n3 (A 10) (n2 (A axis) c) d) out
  | op11_cell {s tag c d hint out} :
      EvalH s c hint → EvalH s d out → EvalH s (n3 (A 11) (C (A tag) c) d) out
  | op11_atom {s tag c out} : EvalH s c out → EvalH s (n3 (A 11) (A tag) c) out

theorem EvalH.toEval {s f p : Noun} (h : EvalH s f p) : Eval s f p := by
  induction h with
  | cell _ _ ih1 ih2 => exact Eval.cell ih1 ih2
  | op0 hs => exact Eval.op0 hs
  | op1 => exact Eval.op1
  | op2 _ _ _ ih1 ih2 ih3 => exact Eval.op2 ih1 ih2 ih3
  | op3 _ ih => exact Eval.op3 ih
  | op4 _ ih => exact Eval.op4 ih
  | op5 _ _ ih1 ih2 => exact Eval.op5 ih1 ih2
  | op6_zero _ _ ih1 ih2 => exact Eval.op6_zero ih1 ih2
  | op6_one _ _ ih1 ih2 => exact Eval.op6_one ih1 ih2
  | op7 _ _ ih1 ih2 => exact Eval.op7 ih1 ih2
  | op8 _ _ ih1 ih2 => exact Eval.op8 ih1 ih2
  | op9 _ hs _ ih1 ih2 =>
    exact Eval.op9 ih1 (Eval.op2 (Eval.op0 Slot.one) (Eval.op0 hs) ih2)
  | op10 _ _ he ih1 ih2 => exact Eval.op10 ih1 ih2 he
  | op11_cell _ _ ih1 ih2 => exact Eval.op11_cell ih1 ih2 (Eval.op0 (Slot.right Slot.one))
  | op11_atom _ ih => exact Eval.op11_atom ih

/-- `EvalH` is `EvalA` of `core/Nock.lean`, with opcode 9 stated by its arm. -/
theorem EvalH.toEvalA {s f p : Noun} (h : EvalH s f p) : EvalA s f p := by
  induction h with
  | cell _ _ ih1 ih2 => exact EvalA.cell ih1 ih2
  | op0 hs => exact EvalA.op0 hs
  | op1 => exact EvalA.op1
  | op2 _ _ _ ih1 ih2 ih3 => exact EvalA.op2 ih1 ih2 ih3
  | op3 _ ih => exact EvalA.op3 ih
  | op4 _ ih => exact EvalA.op4 ih
  | op5 _ _ ih1 ih2 => exact EvalA.op5 ih1 ih2
  | op6_zero _ _ ih1 ih2 => exact EvalA.op6_zero ih1 ih2
  | op6_one _ _ ih1 ih2 => exact EvalA.op6_one ih1 ih2
  | op7 _ _ ih1 ih2 => exact EvalA.op7 ih1 ih2
  | op8 _ _ ih1 ih2 => exact EvalA.op8 ih1 ih2
  | op9 _ hs _ ih1 ih2 =>
    exact EvalA.op9 ih1 (EvalA.op2 (EvalA.op0 Slot.one) (EvalA.op0 hs) ih2)
  | op10 _ _ he ih1 ih2 => exact EvalA.op10 ih1 ih2 he
  | op11_cell _ _ ih1 ih2 => exact EvalA.op11_cell ih1 ih2 (EvalA.op0 (Slot.right Slot.one))
  | op11_atom _ ih => exact EvalA.op11_atom ih

theorem minkF_succ_eq (lib : Lib) (gul : Noun) (n : Nat) (t : Trace) (s f : Noun) :
    minkF lib gul (n + 1) t s f = minkStep lib gul (minkF lib gul n) t s f := rfl

/-- `EvalA` of `core/Nock.lean` (Nock with atom hint tags) is `EvalH`, which
states opcode 9 by its arm for the inductions here. -/
theorem EvalA.toEvalH {s f p : Noun} (h : EvalA s f p) : EvalH s f p := by
  induction h with
  | cell _ _ ih1 ih2 => exact EvalH.cell ih1 ih2
  | op0 hs => exact EvalH.op0 hs
  | op1 => exact EvalH.op1
  | op2 _ _ _ ih1 ih2 ih3 => exact EvalH.op2 ih1 ih2 ih3
  | op3 _ ih => exact EvalH.op3 ih
  | op4 _ ih => exact EvalH.op4 ih
  | op5 _ _ ih1 ih2 => exact EvalH.op5 ih1 ih2
  | op6_zero _ _ ih1 ih2 => exact EvalH.op6_zero ih1 ih2
  | op6_one _ _ ih1 ih2 => exact EvalH.op6_one ih1 ih2
  | op7 _ _ ih1 ih2 => exact EvalH.op7 ih1 ih2
  | op8 _ _ ih1 ih2 => exact EvalH.op8 ih1 ih2
  | op9 _ _ ih1 ih2 =>
    cases ih2 with
    | op2 h1 h2 h3 =>
      cases h1 with
      | op0 hs1 =>
        cases h2 with
        | op0 hs2 =>
          cases Slot.deterministic hs1 Slot.one
          exact EvalH.op9 ih1 hs2 h3
  | op10 _ _ he ih1 ih2 => exact EvalH.op10 ih1 ih2 he
  | op11_cell _ _ _ ih1 ih2 ih3 =>
    cases ih3 with
    | op0 hs =>
      have := slot?_complete hs
      simp [slot?_step 3 (by omega), child] at this
      subst this
      exact EvalH.op11_cell ih1 ih2
  | op11_atom _ ih => exact EvalH.op11_atom ih

/-- If Nock computes `p` from `s` and `f` with atom hint tags, then `+mink`
returns `[%0 p]`, from any trace and with any scry gate. -/
theorem mink_of_evalH (lib : Lib) (gul : Noun) {s f p : Noun} (h : EvalH s f p) :
    ∃ n, ∀ t, minkF lib gul n t s f = some (Tone.zero p) := by
  have L := fun {n m : Nat} (hle : n ≤ m) {t s f r} (h : minkF lib gul n t s f = some r) =>
    minkF_le lib gul hle t s f r h
  induction h with
  | @cell s b c d l r _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero, L (Nat.le_max_right n1 n2) (h2 t), tbind_zero]
  | @op0 s axis out hs =>
    refine ⟨1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep, slot?_complete hs]
  | op1 => exact ⟨1, fun t => rfl⟩
  | @op2 s b c s' f' out _ _ _ ih1 ih2 ih3 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    obtain ⟨n3, h3⟩ := ih3
    refine ⟨max n1 (max n2 n3) + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (by omega) (h1 t), tbind_zero, L (by omega) (h2 t), tbind_zero, L (by omega) (h3 t)]
  | @op3 s b x _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep, h1, tbind_zero]
  | @op4 s b a _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep, h1, tbind_zero]
  | @op5 s b c l r _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero, L (Nat.le_max_right n1 n2) (h2 t), tbind_zero]
  | @op6_zero s b c d out _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero]
    exact L (Nat.le_max_right n1 n2) (h2 t)
  | @op6_one s b c d out _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero]
    exact L (Nat.le_max_right n1 n2) (h2 t)
  | @op7 s b c s' out _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero]
    exact L (Nat.le_max_right n1 n2) (h2 t)
  | @op8 s b c x out _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero]
    exact L (Nat.le_max_right n1 n2) (h2 t)
  | @op9 s axis c core arm out _ hs _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero, slot?_complete hs]
    exact L (Nat.le_max_right n1 n2) (h2 t)
  | @op10 s axis c d rep base out _ _ hed ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    have hpos : axis ≠ 0 := Nat.pos_iff_ne_zero.mp (Edit.pos hed)
    rw [if_neg hpos, L (Nat.le_max_right n1 n2) (h2 t), tbind_zero,
      L (Nat.le_max_left n1 n2) (h1 t), tbind_zero, edit?_complete hed]
  | @op11_cell s tag c d hint out _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [L (Nat.le_max_left n1 n2) (h1 t), tbind_zero, L (Nat.le_max_right n1 n2) (h2 _), tbind_zero]
  | @op11_atom s tag c out _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, fun t => ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep, h1, tbind_zero]

/-- The difference: a dynamic hint whose tag is a cell.  Nock reduces
`[11 [[1 0] 1 0] 1 42]` to `42`; `+mink` returns `[%2 trace]` on it. -/
theorem eval_cell_tag (lib : Lib) (gul : Noun) (s : Noun) (t : Trace) (n : Nat) :
    Eval s (n3 (A 11) (C (C (A 1) (A 0)) (C (A 1) (A 0))) (C (A 1) (A 42))) (A 42) ∧
      minkF lib gul (n + 1) t s (n3 (A 11) (C (C (A 1) (A 0)) (C (A 1) (A 0))) (C (A 1) (A 42))) =
        some (Tone.two t) :=
  ⟨Eval.op11_cell Eval.op1 Eval.op1 (Eval.op0 (Slot.right Slot.one)), rfl⟩

/-! ## `+mook` and `+mock`

    ++  mook
      |=  ton=tone
      ^-  toon
      ?.  ?=([%2 *] ton)  ton
      |^  [%2 (turn skip rend)]
      ...

`+rend` of a `[%mean dat]` frame with a cell `dat` runs the trap,
`(mack dat -.dat)`, which is `+mink` without a scry gate; the other frames are
`Lib.rendBase`.
-/

/-- A tape from its bytes. -/
def tape (bytes : List Nat) : Noun := listNoun A bytes

/-- `leaf+"####"`. -/
def leafHash : Noun := C (A Tag.leaf) (tape [35, 35, 35, 35])

/-- `leaf+"mook.mean"`. -/
def leafMookMean : Noun := C (A Tag.leaf) (tape [109, 111, 111, 107, 46, 109, 101, 97, 110])

/-- What `+rend` makes of the product of a trap: `(soft tank)` of it, and
`leaf+"mook.mean"` if it is no tank. -/
def rendProduct (lib : Lib) (p : Noun) : Noun := (lib.softTank p).getD leafMookMean

/-- `+rend:mook` with fuel for the `+mack` of a `%mean` trap. -/
def rendF (lib : Lib) (k : Nat) (fr : Frame) : Option Noun :=
  match fr with
  | (tag, Noun.cell h t) =>
    if tag = Tag.mean then
      match minkF lib (A 0) k [] (C h t) h with
      | none => none
      | some (Tone.zero v) => some (rendProduct lib v)
      | some _ => some leafHash
    else lib.rendBase tag (C h t)
  | (tag, Noun.atom a) => lib.rendBase tag (A a)

/-- `+skip:mook`: a trace of more than 1024 frames keeps its first 512 and
its last 512, with a `%lose` frame between them. -/
def skip (lib : Lib) {α : Type} (lose : Noun → α) (tr : List α) : List α :=
  if tr.length > 1024 then
    tr.take 512 ++ lose (lib.skipMsg (tr.length - 1024)) :: tr.drop (tr.length - 512)
  else tr

/-- `+mook` with fuel. -/
def mookF (lib : Lib) (k : Nat) : Tone → Option Toon
  | Tone.zero p => some (Toon.zero p)
  | Tone.one p => some (Toon.one p)
  | Tone.two tr => ((skip lib (fun m => (Tag.lose, m)) tr).mapM (rendF lib k)).map Toon.two

/-- `(mock [s f] gul)` returns `toon`. -/
def Mock (lib : Lib) (s f gul : Noun) (toon : Toon) : Prop :=
  ∃ k, ((minkF lib gul k [] s f).bind (mookF lib k)) = some toon

theorem rendF_le (lib : Lib) {k k' : Nat} (hk : k ≤ k') (fr : Frame) :
    OptLe (rendF lib k fr) (rendF lib k' fr) := by
  intro x h
  match fr, h with
  | (tag, Noun.atom a), h => exact h
  | (tag, Noun.cell hd tl), h =>
    by_cases htag : tag = Tag.mean
    · simp only [rendF, htag, if_true] at h ⊢
      cases hm : minkF lib (A 0) k [] (C hd tl) hd with
      | none => rw [hm] at h; simp at h
      | some r =>
        rw [hm] at h
        rw [minkF_le lib (A 0) hk _ _ _ _ hm]
        exact h
    · simp only [rendF, htag, if_false] at h ⊢
      exact h

theorem mapM_le {α β : Type} {f g : α → Option β} (hfg : ∀ a, OptLe (f a) (g a)) :
    ∀ (l : List α), OptLe (l.mapM f) (l.mapM g)
  | [] => OptLe.refl _
  | a :: l => by
    intro r h
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact ⟨b, hfg a b hb, bs, mapM_le hfg l bs hbs, rfl⟩

theorem mookF_le (lib : Lib) {k k' : Nat} (hk : k ≤ k') (ton : Tone) :
    OptLe (mookF lib k ton) (mookF lib k' ton) := by
  intro x h
  cases ton with
  | zero p => exact h
  | one p => exact h
  | two tr =>
    simp only [mookF, Option.map_eq_some_iff] at h ⊢
    obtain ⟨l, hl, rfl⟩ := h
    exact ⟨l, mapM_le (rendF_le lib hk) _ l hl, rfl⟩

end SkaModel
end Formalization
