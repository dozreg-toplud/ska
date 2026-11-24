import lemmas.Ska.Analysis

/-!
# The fuel of the analysis: more fuel returns the same

The arms of `Analysis.lean` that recurse (`folLoop`, `resolve`, `analyze`,
`run`, `passLoop`, `memberLoop`, and the loops `+sweep`, `+cull`,
`+prune-callgraph` that take the fuel of the arm they run in) return `none`
when the fuel runs out.  Here: whatever one of them returns at fuel `n`, it
returns at every fuel `m ≥ n` (`folLoop_fuel_le`, `resolve_fuel_le`,
`analyze_fuel_le`, `run_fuel_le`, `passLoop_fuel_le`, `memberLoop_fuel_le`,
and `skaCallgraph_fuel_le`, `skaPoke_fuel_le` for the poke).  For example,
if `folLoop env memoF 5` returns `r` on `[4 0 1]`, so does
`folLoop env memoF 9`.

The order `OLe x y` ("whatever `x` returns, `y` returns") is `Below?` of
`Iter.lean`, unfolded, so that this file does not import the executor: a
statement here is the statement with `Below?` by `id`.  The proof is one
step (`fuelStep`: fuel `n` below fuel `n + 1`, for the six arms at once, by
induction on `n`, each step being monotone in the arms it calls:
`folStep_le`, `resolveStep_le`, `analyzeStep_le`, `runStep_le`,
`passStep_le`, `memberStep_le`), then a chain.  `allP` of `AnaInv.lean` does
not give it: it carries a property of each result, not a comparison of two
fuels.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

/-- `x` below `y`: whatever `x` returns, `y` returns (`Below?` of
`Iter.lean`). -/
def OLe {α : Type} (x y : Option α) : Prop := ∀ a, x = some a → y = some a

theorem OLe.refl {α : Type} (x : Option α) : OLe x x := fun _ h => h

theorem OLe.trans {α : Type} {x y z : Option α} (h1 : OLe x y) (h2 : OLe y z) : OLe x z :=
  fun a h => h2 a (h1 a h)

theorem OLe.bind {α β : Type} {x x' : Option α} {f f' : α → Option β}
    (hx : OLe x x') (hf : ∀ a, OLe (f a) (f' a)) : OLe (x.bind f) (x'.bind f') := by
  intro b h
  simp only [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, hx a ha, hf a b hb⟩

theorem OLe.map {α β : Type} {x x' : Option α} (f : α → β) (hx : OLe x x') :
    OLe (x.map f) (x'.map f) := by
  intro b h
  simp only [Option.map_eq_some_iff] at h ⊢
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, hx a ha, hb⟩

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## The loops with their own fuel -/

theorem sweepLoop_fuel (st : SkaState M R) (was : M Ident Unit) :
    ∀ (n : Nat) (seen : M Ident Unit) (l : List (Ident × List Ident)) (out : List Ident),
      OLe (sweepLoop st was n seen l out) (sweepLoop st was (n + 1) seen l out)
  | 0, _, _, _ => fun _ h => by simp [sweepLoop] at h
  | n + 1, seen, [], out => fun a h => by simpa [sweepLoop] using h
  | n + 1, seen, (i, []) :: rest, out => fun a h => by
    simp only [sweepLoop] at h ⊢
    exact sweepLoop_fuel st was n _ _ _ a h
  | n + 1, seen, (i, k :: ks) :: rest, out => fun a h => by
    simp only [sweepLoop] at h ⊢
    by_cases hc : Treap.has seen k = true ∨ Treap.has was k = false
    · rw [if_pos hc] at h ⊢
      exact sweepLoop_fuel st was n _ _ _ a h
    · rw [if_neg hc] at h ⊢
      exact sweepLoop_fuel st was n _ _ _ a h

theorem liveLoop_fuel (st : SkaState M R) (members : M Ident Unit) :
    ∀ (n : Nat) (q : List Ident) (live : M Ident Unit),
      OLe (liveLoop st members n q live) (liveLoop st members (n + 1) q live)
  | 0, _, _ => fun _ h => by simp [liveLoop] at h
  | n + 1, [], live => fun a h => by simpa [liveLoop] using h
  | n + 1, i :: q, live => fun a h => by
    simp only [liveLoop] at h ⊢
    by_cases hc : Treap.has live i = true ∨ Treap.has members i = false
    · rw [if_pos hc] at h ⊢
      exact liveLoop_fuel st members n _ _ a h
    · rw [if_neg hc] at h ⊢
      exact liveLoop_fuel st members n _ _ a h

theorem sweep_fuel (n : Nat) (id : Ident) (was : M Ident Unit) (st : SkaState M R) :
    OLe (sweep n id was st) (sweep (n + 1) id was st) :=
  sweepLoop_fuel st was n _ _ _

theorem cull_fuel (n : Nat) (id : Ident) (st : SkaState M R) : OLe (cull n id st) (cull (n + 1) id st) := by
  unfold cull
  refine OLe.bind (OLe.refl _) fun ab => ?_
  exact OLe.map _ (liveLoop_fuel st _ n _ _)

theorem pruneLoop_fuel (g : Callgraph M) :
    ∀ (n : Nat) (q : List Ident) (out : Callgraph M), OLe (pruneLoop g n q out) (pruneLoop g (n + 1) q out)
  | 0, _, _ => fun _ h => by simp [pruneLoop] at h
  | n + 1, [], out => fun a h => by simpa [pruneLoop] using h
  | n + 1, i :: q, out => fun a h => by
    simp only [pruneLoop] at h ⊢
    by_cases hc : Treap.has out i = true
    · rw [if_pos hc] at h ⊢
      exact pruneLoop_fuel g n _ _ a h
    · rw [if_neg hc] at h ⊢
      exact OLe.bind (OLe.refl _) (fun d => pruneLoop_fuel g n _ _) a h

/-! ## Each step is monotone in the arms it calls -/

/-- `go` below `go'` on every argument. -/
def GoLe (go go' : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gen, OLe (go fol sub seat mk bc df gen) (go' fol sub seat mk bc df gen)

/-- `res` below `res'` on every argument. -/
def ResLe (res res' : ResGo M R) : Prop := ∀ i gen, OLe (res i gen) (res' i gen)

theorem callStep_le {res res' : ResGo M R} {go go' : FolGoS M R} (hres : ResLe res res')
    (hgo : GoLe go go') (seat mk : Option Noun) (bc df : Bool) (s f : FolOut) (gen : GenS M R) :
    OLe (callStep res go seat mk bc df s f gen) (callStep res' go' seat mk bc df s f gen) := by
  unfold callStep
  split
  · exact OLe.refl _
  · split
    · split
      · exact OLe.bind (hgo _ _ _ _ _ _ _) fun _ => OLe.refl _
      · exact OLe.bind (hres _ _) fun _ => OLe.refl _
    · exact OLe.refl _

omit [Treap M] in
theorem meanArm_le {go go' : FolGoS M R} (hgo : GoLe go go') (tag : Nat) (h : FolOut)
    (seat mk : Option Noun) (bc : Bool) (gen : GenS M R) :
    OLe (meanArm go tag h seat mk bc gen) (meanArm go' tag h seat mk bc gen) := by
  unfold meanArm
  split
  · exact OLe.refl _
  · refine OLe.bind (OLe.refl _) fun bat => ?_
    split
    · exact OLe.bind (hgo _ _ _ _ _ _ _) fun _ => OLe.refl _
    · exact OLe.refl _

/-- One level of `fol-loop` is monotone in `go` and `res`. -/
theorem folStep_le (env : Env R) {res res' : ResGo M R} {go go' : FolGoS M R}
    (hres : ResLe res res') (hgo : GoLe go go') (fol : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS M R) :
    OLe (folStep env res go fol sub seat mk bc df gen) (folStep env res' go' fol sub seat mk bc df gen) := by
  unfold folStep
  split <;> (try dsimp only) <;>
    repeat (first
      | exact OLe.refl _
      | exact hgo _ _ _ _ _ _ _
      | exact callStep_le hres hgo _ _ _ _ _ _ _
      | (refine OLe.bind (meanArm_le hgo _ _ _ _ _ _) fun _ => ?_)
      | (refine OLe.bind (hgo _ _ _ _ _ _ _) fun _ => ?_)
      | (refine OLe.bind (OLe.refl _) fun _ => ?_)
      | split)

/-- One turn of the `resolve` loop is monotone in the loop and in `+analyze`. -/
theorem resolveStep_le (env : Env R) {rs rs' : ResGo M R} {an an' : AnaGo M R} (hr : ResLe rs rs')
    (ha : ∀ i st, OLe (an i st) (an' i st)) (orig idT : Ident) (gen : GenS M R) :
    OLe (resolveStep env rs an orig idT gen) (resolveStep env rs' an' orig idT gen) := by
  unfold resolveStep
  repeat (first
    | exact OLe.refl _
    | exact hr _ _
    | exact OLe.map _ (ha _ _)
    | split)

theorem runStep_le {fol fol' : FolGoS M R} (hf : GoLe fol fol') (id : Ident) (index : Nat) (st : SkaState M R) :
    OLe (runStep fol id index st) (runStep fol' id index st) := by
  unfold runStep
  exact OLe.map _ (hf _ _ _ _ _ _ _)

theorem memberStep_le {run run' : RunGo M R} {ml ml' : MemGo M R}
    (hrun : ∀ i index st, OLe (run i index st) (run' i index st))
    (hml : ∀ index pass ms st, OLe (ml index pass ms st) (ml' index pass ms st)) (index pass : Nat) :
    ∀ (ms : List Ident) (st : SkaState M R),
      OLe (memberStep run ml index pass ms st) (memberStep run' ml' index pass ms st)
  | [], _ => OLe.refl _
  | m :: ms, st => by
    simp only [memberStep]
    split
    · exact hml _ _ _ _
    · refine OLe.bind (OLe.refl _) fun o => OLe.bind (hrun _ _ _) fun r => ?_
      split
      · exact OLe.refl _
      · exact OLe.map _ (hml _ _ _ _)

theorem passStep_le (n : Nat) {ml ml' : MemGo M R} {pl pl' : PassGo M R}
    (hml : ∀ index pass ms st, OLe (ml index pass ms st) (ml' index pass ms st))
    (hpl : ∀ id index pass st, OLe (pl id index pass st) (pl' id index pass st))
    (id : Ident) (index pass : Nat) (st : SkaState M R) :
    OLe (passStep n ml pl id index pass st) (passStep (n + 1) ml' pl' id index pass st) := by
  unfold passStep
  refine OLe.bind (OLe.refl _) fun ab => OLe.bind (sweep_fuel _ _ _ _) fun members => ?_
  refine OLe.bind (hml _ _ _ _) fun r => ?_
  split
  · exact OLe.refl _
  · refine OLe.bind (cull_fuel _ _ _) fun st' => ?_
    split
    · exact OLe.refl _
    · exact hpl _ _ _ _

theorem cullPass_le (n : Nat) {pl pl' : PassGo M R}
    (hpl : ∀ id index pass st, OLe (pl id index pass st) (pl' id index pass st))
    (id : Ident) (index : Nat) (st : SkaState M R) :
    OLe (cullPass n pl id index st) (cullPass (n + 1) pl' id index st) :=
  OLe.bind (cull_fuel _ _ _) fun _ => hpl _ _ _ _

theorem analyzeStep_le (n : Nat) (memoF : Memo M) {run run' : RunGo M R} {pl pl' : PassGo M R}
    (hrun : ∀ i index st, OLe (run i index st) (run' i index st))
    (hpl : ∀ id index pass st, OLe (pl id index pass st) (pl' id index pass st))
    (id : Ident) (st : SkaState M R) :
    OLe (analyzeStep n memoF run pl id st) (analyzeStep (n + 1) memoF run' pl' id st) := by
  unfold analyzeStep
  split
  · exact OLe.refl _
  · exact OLe.refl _
  · refine OLe.bind (hrun _ _ _) fun r => ?_
    split
    · exact OLe.refl _
    · split
      · exact cullPass_le n hpl _ _ _
      · refine OLe.bind (OLe.refl _) fun ab => ?_
        split
        · exact cullPass_le n hpl _ _ _
        · exact OLe.refl _

/-! ## The recursion -/

section Rec

variable (env : Env R) (memoF : Memo M)

theorem folLoop_unfold (n : Nat) :
    folLoop env memoF (n + 1) = folStep env (fun i => resolve env memoF n i i) (folLoop env memoF n) := by
  simp only [folLoop]

theorem resolve_unfold (n : Nat) (orig : Ident) :
    resolve env memoF (n + 1) orig = resolveStep env (resolve env memoF n orig) (analyze env memoF n) orig := by
  simp only [resolve]

theorem analyze_unfold (n : Nat) :
    analyze env memoF (n + 1) = analyzeStep n memoF (run env memoF n) (passLoop env memoF n) := by
  simp only [analyze]

theorem run_unfold (n : Nat) : run env memoF (n + 1) = runStep (folLoop env memoF n) := by
  simp only [run]

theorem passLoop_unfold (n : Nat) :
    passLoop env memoF (n + 1) = passStep n (memberLoop env memoF n) (passLoop env memoF n) := by
  simp only [passLoop]

theorem memberLoop_unfold (n : Nat) :
    memberLoop env memoF (n + 1) = memberStep (run env memoF n) (memberLoop env memoF n) := by
  simp only [memberLoop]

/-- The six arms at fuel `n` are below themselves at fuel `n + 1`. -/
structure FuelStep (n : Nat) : Prop where
  fol : GoLe (folLoop env memoF n) (folLoop env memoF (n + 1))
  res : ∀ orig, ResLe (resolve env memoF n orig) (resolve env memoF (n + 1) orig)
  ana : ∀ i st, OLe (analyze env memoF n i st) (analyze env memoF (n + 1) i st)
  run : ∀ i index st, OLe (run env memoF n i index st) (run env memoF (n + 1) i index st)
  pass : ∀ id index pass st, OLe (passLoop env memoF n id index pass st) (passLoop env memoF (n + 1) id index pass st)
  mem : ∀ index pass ms st,
    OLe (memberLoop env memoF n index pass ms st) (memberLoop env memoF (n + 1) index pass ms st)

/-- **One more unit of fuel returns the same**, for the six arms at once. -/
theorem fuelStep : ∀ n, FuelStep env memoF n
  | 0 => {
      fol := fun _ _ _ _ _ _ _ _ h => by simp [folLoop] at h
      res := fun _ _ _ _ h => by simp [resolve] at h
      ana := fun _ _ _ h => by simp [analyze] at h
      run := fun _ _ _ _ h => by simp [run] at h
      pass := fun _ _ _ _ _ h => by simp [passLoop] at h
      mem := fun _ _ _ _ _ h => by simp [memberLoop] at h }
  | n + 1 =>
    have ih := fuelStep n
    { fol := by
        intro fol sub seat mk bc df gen
        rw [folLoop_unfold env memoF n, folLoop_unfold env memoF (n + 1)]
        exact folStep_le env (fun i gen => ih.res i i gen) ih.fol _ _ _ _ _ _ _
      res := by
        intro orig i gen
        rw [resolve_unfold env memoF n, resolve_unfold env memoF (n + 1)]
        exact resolveStep_le env (ih.res orig) ih.ana _ _ _
      ana := by
        intro i st
        rw [analyze_unfold env memoF n, analyze_unfold env memoF (n + 1)]
        exact analyzeStep_le n memoF ih.run ih.pass _ _
      run := by
        intro i index st
        rw [run_unfold env memoF n, run_unfold env memoF (n + 1)]
        exact runStep_le ih.fol _ _ _
      pass := by
        intro id index pass st
        rw [passLoop_unfold env memoF n, passLoop_unfold env memoF (n + 1)]
        exact passStep_le n ih.mem ih.pass _ _ _ _
      mem := by
        intro index pass ms st
        rw [memberLoop_unfold env memoF n, memberLoop_unfold env memoF (n + 1)]
        exact memberStep_le ih.run ih.mem _ _ _ _ }

/-- A chain of one-step comparisons gives every larger fuel. -/
theorem fuel_chain {α : Type} {f : Nat → Option α} (h : ∀ n, OLe (f n) (f (n + 1))) :
    ∀ {n m : Nat}, n ≤ m → OLe (f n) (f m) := by
  intro n m hnm
  induction hnm with
  | refl => exact OLe.refl _
  | step _ ih => exact ih.trans (h _)

theorem folLoop_fuel_le {n m : Nat} (h : n ≤ m) (fol : Noun) (sub : Anno) (seat mk : Option Noun)
    (bc df : Bool) (gen : GenS M R) :
    OLe (folLoop env memoF n fol sub seat mk bc df gen) (folLoop env memoF m fol sub seat mk bc df gen) :=
  fuel_chain (f := fun k => folLoop env memoF k fol sub seat mk bc df gen)
    (fun k => (fuelStep env memoF k).fol _ _ _ _ _ _ _) h

theorem resolve_fuel_le {n m : Nat} (h : n ≤ m) (orig i : Ident) (gen : GenS M R) :
    OLe (resolve env memoF n orig i gen) (resolve env memoF m orig i gen) :=
  fuel_chain (f := fun k => resolve env memoF k orig i gen) (fun k => (fuelStep env memoF k).res _ _ _) h

theorem resolveR_fuel_le {n m : Nat} (h : n ≤ m) (i : Ident) (gen : GenS M R) :
    OLe (resolveR env memoF n i gen) (resolveR env memoF m i gen) :=
  resolve_fuel_le env memoF h i i gen

theorem analyze_fuel_le {n m : Nat} (h : n ≤ m) (i : Ident) (st : SkaState M R) :
    OLe (analyze env memoF n i st) (analyze env memoF m i st) :=
  fuel_chain (f := fun k => analyze env memoF k i st) (fun k => (fuelStep env memoF k).ana _ _) h

theorem run_fuel_le {n m : Nat} (h : n ≤ m) (i : Ident) (index : Nat) (st : SkaState M R) :
    OLe (run env memoF n i index st) (run env memoF m i index st) :=
  fuel_chain (f := fun k => run env memoF k i index st) (fun k => (fuelStep env memoF k).run _ _ _) h

theorem passLoop_fuel_le {n m : Nat} (h : n ≤ m) (id : Ident) (index pass : Nat) (st : SkaState M R) :
    OLe (passLoop env memoF n id index pass st) (passLoop env memoF m id index pass st) :=
  fuel_chain (f := fun k => passLoop env memoF k id index pass st)
    (fun k => (fuelStep env memoF k).pass _ _ _ _) h

theorem memberLoop_fuel_le {n m : Nat} (h : n ≤ m) (index pass : Nat) (ms : List Ident) (st : SkaState M R) :
    OLe (memberLoop env memoF n index pass ms st) (memberLoop env memoF m index pass ms st) :=
  fuel_chain (f := fun k => memberLoop env memoF k index pass ms st)
    (fun k => (fuelStep env memoF k).mem _ _ _ _) h

end Rec

/-! ## The poke -/

theorem skaCallgraph_fuel_le (env : Env R) {n m : Nat} (h : n ≤ m) (root : Ident) (memoF : Memo M) (reg : R) :
    OLe (skaCallgraph env n root memoF reg) (skaCallgraph env m root memoF reg) := by
  unfold skaCallgraph
  exact OLe.map _ (analyze_fuel_le env memoF h _ _)

theorem pruneCallgraph_fuel_le {n m : Nat} (h : n ≤ m) (g : Callgraph M) (root : Ident) :
    OLe (pruneCallgraph n g root) (pruneCallgraph m g root) :=
  fuel_chain (f := fun k => pruneCallgraph k g root) (fun k => pruneLoop_fuel g k _ _) h

/-- **The analysis part of `+ska-poke` returns the same at every larger
fuel.** -/
theorem skaPoke_fuel_le (env : Env R) {n m : Nat} (h : n ≤ m) (root : Ident) (memo : Memo M) (reg : R) :
    OLe (skaPoke env n root memo reg) (skaPoke env m root memo reg) := by
  unfold skaPoke
  exact OLe.bind (skaCallgraph_fuel_le env h _ _ _) fun gr =>
    OLe.bind (pruneCallgraph_fuel_le h _ _) fun _ => OLe.refl _

end Ana
end SkaModel
end Formalization
