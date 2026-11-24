import lemmas.Ska.Interp

/-!
# Executions of `execBlob` as paths of configurations

The proxies of `+comp` need a statement about the paths of a run: a register
that a join was passed `~` for (poisoned) is defined, may be moved, and is
read for real only on the paths where it holds a value.  This file gives
`execBlob` a small-step form that keeps the labels of the blocks.

* `Cfg`: a block being run (its label, what is left of it, the arguments not
  yet passed), the registers, the trace and the state.
* `Step lib O c gul x es y`: one step of `execBlob` from `x` to `y`, which
  passes the arguments, runs one op that returns `%0`, or follows the jump of
  the terminator to the block at its label; `es` is `[(x.lab, y.lab)]` for
  a jump and `[]` otherwise.  `Steps` is its closure, with the edges in order.
* `endOf`: what a configuration returns when its next action leaves the
  function or ends it (an op that does not return `%0`, `%don`, `%bom`, a
  tail call, a `%brn` on a non-loobean).

`run_iff_path`: `execBlob` returns `r` exactly when some path of steps from
the configuration reaches one whose `endOf` is `r`.  Steps are deterministic
(`step_det`) and keep what the run returns (`step_run`, `steps_run`); a
jump through `%hop`, `%brn`, `%brz` is a step (`step_hop`, `step_brn0`,
`step_brn1`, `step_brz`).

The guard half of the threading invariant is stated with it
(`Guarded`): every path from the entry that reaches a real read of a
register (`ReadsAt`, with `poleReads` and `finReads`; a `%mov` and a hop
argument are no real reads) passes a given edge.  A real read of a poisoned
register crashes (`run_poison_pole`, `run_poison_fin`), so the run of a
function can succeed only where the guard holds; with the register half in
the form `HeldAfter` (past the edge the register holds a value),
`guarded_reads` gives that every real read reads a value.

What `+comp` emits.  On the real compiler, with a subject sock that knows
nothing (`tools/hoon/proxy-dump.hoon`), the smallest formula seen whose code
before `+optimize` passes `~` to a join is
`[7 [6 [0 2] [1 0] [6 [0 6] [0 7] [0 1]]] [6 [0 2] [0 3] [0 1]]]`: the outer
`%6` of `p` tests register `0v4` at `0wE` (the branch `[1 0]` at `0wB`,
the inner `%6` at `0wD`); the inner one tests `0vd` at `0wz` and joins at
`0wm`; the outer join `0w9` has the parameters `[0vo 0v3]`, to which `0wm`
passes `[0vd 0v6]` and `0wB` passes `[~ 0v5]`, so `0vo` (the threaded proxy
of the inner test) is poisoned on the path through `0wB`.  The lazy blocks of
`q` (`0wi`, `0wj`) branch again on `0v4` (`%brz`, the proxy of the outer test
that `+fork` makes), and only their `o` side reaches the real reads of
`0vo` (`%brz 0vo` at `0wv` and `0ww`).  So the guard is a property of
executions, not of the graph: the graph has a path `0wB → 0w9 → 0w5 → 0wi →
0wv`, but no execution follows it, because `0v4` is `0` on it and the `%brz`
at `0wi` then takes its `z` side.  Every execution that reaches `0wv` passed
the edge `(0wE, 0wD)`.  On `[1 0 0 5]` the run takes that path, reads `0vo`
(`0`) at `0wv` and returns `5`, as `+mink` does.  In `[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]`
the proxy that `+collapse-lazy-atom` makes for the yes branch's block is
read only by a `%mov`, and `+to-straight` replaces it by its definition, the
register of the `%4` (`%mov 0v3 0v2` at `0w3`), which every path to that
block defines.
-/

namespace Formalization
namespace SkaModel
namespace Path

open Nock

section
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

/-- A configuration of `execBlob`: the label of the block being run, what is
left of it, the arguments not yet passed, the registers, the trace and the
state. -/
structure Cfg (σ : Type) (Map : Type → Type) where
  lab : Nat
  b : Blob
  params : List (Option Nat)
  regs : Map (Option Noun)
  t : Trace
  st : σ

/-- The jump a terminator takes on the registers, when it stays in the
function; `none` for an end, a crash, a call, a non-loobean `%brn`. -/
def taken (regs : Map (Option Noun)) : Termin → Option Jmp
  | Termin.lti n r z o => (read r regs).map fun v =>
      if (match v with | Noun.atom a => decide (a < n) | _ => false) then z else o
  | Termin.clq r z o => (read r regs).map fun v => match v with | Noun.cell _ _ => z | Noun.atom _ => o
  | Termin.eqq l r z o => (read l regs).bind fun x => (read r regs).map fun y => if x = y then z else o
  | Termin.brn r z o => (read r regs).bind fun v =>
      if v = A 0 then some z else if v = A 1 then some o else none
  | Termin.brz r z o => (read r regs).map fun v => if v = A 0 then z else o
  | Termin.hop t => some t
  | _ => none

variable (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun)

/-- What a configuration runs to. -/
def run (x : Cfg σ Map) : Option (Tone × σ) := execBlob lib O c gul x.st x.regs x.t x.b x.params

/-- **One step of `execBlob`**, with the edge it takes. -/
inductive Step : Cfg σ Map → List (Nat × Nat) → Cfg σ Map → Prop
  | pass {x : Cfg σ Map} {R : Map (Option Noun)} :
      (x.params ≠ [] ∨ x.b.par ≠ []) → evalPass x.params x.b.par x.regs = some R →
      Step x [] { x with b := { x.b with par := [] }, params := [], regs := R }
  | op {x : Cfg σ Map} {p : Pole} {rest : List Pole} {n : Noun} {R : Map (Option Noun)} {t' : Trace} {st' : σ} :
      x.params = [] → x.b.par = [] → x.b.body = p :: rest →
      execPole lib O gul x.st p x.regs x.t = some (Tone.zero n, R, t', st') →
      Step x [] { x with b := { x.b with body := rest }, regs := R, t := t', st := st' }
  | jump {x : Cfg σ Map} {j : Jmp} {b' : Blob} :
      x.params = [] → x.b.par = [] → x.b.body = [] → taken x.regs x.b.fin = some j →
      HoonMap.get c.blocks j.there = some b' →
      Step x [(x.lab, j.there)] ⟨j.there, b', j.args, x.regs, x.t, x.st⟩

/-- Paths of steps, with their edges in order. -/
inductive Steps : Cfg σ Map → List (Nat × Nat) → Cfg σ Map → Prop
  | refl (x : Cfg σ Map) : Steps x [] x
  | step {x y z : Cfg σ Map} {e es : List (Nat × Nat)} : Step lib O c gul x e y → Steps y es z → Steps x (e ++ es) z

/-- What a configuration returns when its next action leaves the function or
ends it, and `none` when it steps (or crashes). -/
def endOf (x : Cfg σ Map) : Option (Tone × σ) :=
  if x.params ≠ [] ∨ x.b.par ≠ [] then none else
  match x.b.body with
  | p :: _ =>
      match execPole lib O gul x.st p x.regs x.t with
      | some (Tone.zero _, _, _, _) => none
      | some (ton, _, _, st') => some (ton, st')
      | none => none
  | [] =>
    match x.b.fin with
    | Termin.brn r _ _ => (read r x.regs).bind fun v =>
        if v = A 0 ∨ v = A 1 then none else some (Tone.two x.t, x.st)
    | Termin.jmp a v => (v.mapM (read · x.regs)).bind fun vs => O.call x.st a false vs x.t gul
    | Termin.jmf a v _ => (v.mapM (read · x.regs)).bind fun vs => O.call x.st a false vs x.t gul
    | Termin.jsp a r => (read r x.regs).bind fun v => O.call x.st a true [v] x.t gul
    | Termin.jsf a r _ => (read r x.regs).bind fun v => O.call x.st a true [v] x.t gul
    | Termin.don r => (read r x.regs).bind fun v => some (Tone.zero v, x.st)
    | Termin.bom _ => some (Tone.two x.t, x.st)
    | _ => none

/-! ## Steps keep the run -/

variable {lib O c gul}

theorem step_run {x y : Cfg σ Map} {e : List (Nat × Nat)} (h : Step lib O c gul x e y) :
    run lib O c gul x = run lib O c gul y := by
  cases h with
  | pass hne hR =>
    unfold run; rw [execBlob]; simp only [hne, if_true, hR, Option.bind_eq_bind, Option.bind_some]
  | op hp hq hb hpole =>
    unfold run; rw [execBlob]
    simp only [hp, hq, ne_eq, not_true, or_self, if_false, hb, Option.bind_eq_bind, hpole, Option.bind_some]
  | @jump j b' hp hq hb ht hb' =>
    obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
    simp only at hp hq hb ht ⊢
    subst hp hq hb
    unfold run; rw [execBlob]
    simp only [ne_eq, not_true, or_self, if_false, Option.bind_eq_bind]
    cases fin with
    | lti n r z o =>
      simp only [taken, Option.map_eq_some_iff] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      simp only [hv, Option.bind_some]; split <;> simp_all
    | clq r z o =>
      simp only [taken, Option.map_eq_some_iff] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      simp only [hv, Option.bind_some]; split <;> simp_all
    | eqq l r z o =>
      simp only [taken, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
      obtain ⟨x, hx, y, hy, rfl⟩ := ht
      simp only [hx, hy, Option.bind_some]; split <;> simp_all
    | brn r z o =>
      simp only [taken, Option.bind_eq_some_iff] at ht
      obtain ⟨v, hv, hj⟩ := ht
      simp only [hv, Option.bind_some]
      by_cases h0 : v = A 0
      · simp only [h0, if_true, Option.some.injEq] at hj ⊢; subst hj; simp [hb']
      · by_cases h1 : v = A 1
        · subst h1; simp at hj; subst hj; simp [hb']
        · simp [h0, h1] at hj
    | brz r z o =>
      simp only [taken, Option.map_eq_some_iff] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      simp only [hv, Option.bind_some]; split <;> simp_all
    | hop t =>
      simp only [taken, Option.some.injEq] at ht
      subst ht; simp [hb']
    | jmp => simp [taken] at ht
    | jmf => simp [taken] at ht
    | jsp => simp [taken] at ht
    | jsf => simp [taken] at ht
    | don => simp [taken] at ht
    | bom => simp [taken] at ht

theorem steps_run {x y : Cfg σ Map} {es : List (Nat × Nat)} (h : Steps lib O c gul x es y) :
    run lib O c gul x = run lib O c gul y := by
  induction h with
  | refl => rfl
  | step s _ ih => exact (step_run s).trans ih

/-- An end is what the run returns. -/
theorem endOf_run {x : Cfg σ Map} {r : Tone × σ} (h : endOf lib O gul x = some r) :
    run lib O c gul x = some r := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  unfold endOf at h; unfold run; rw [execBlob]
  simp only at h ⊢
  split at h
  · simp at h
  rename_i hne
  simp only [hne, if_false]
  cases body with
  | cons p rest =>
    simp only [Option.bind_eq_bind] at h ⊢
    cases hpole : execPole lib O gul st p regs t with
    | none => simp [hpole] at h
    | some res =>
      obtain ⟨ton, R, t', st'⟩ := res
      rw [hpole] at h
      cases ton <;> simp_all
  | nil =>
    simp only [Option.bind_eq_bind] at h ⊢
    cases fin with
    | brn r z o =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      simp only [hv, Option.bind_some]
      by_cases h0 : v = A 0
      · simp [h0] at h
      · by_cases h1 : v = A 1
        · simp [h1] at h
        · simp only [h0, h1, or_self, if_false, Option.some.injEq] at h; simp [h0, h1, h]
    | jmp => exact h
    | jmf => exact h
    | jsp => exact h
    | jsf => exact h
    | don => exact h
    | bom => exact h
    | _ => simp at h

/-! ## A successful run is a path -/

/-- **A run returns `r` exactly when a path of steps reaches an end that is
`r`.** -/
theorem run_iff_path (x : Cfg σ Map) (r : Tone × σ) :
    run lib O c gul x = some r ↔ ∃ es y, Steps lib O c gul x es y ∧ endOf lib O gul y = some r := by
  constructor
  · intro h
    obtain ⟨lab, b, params, regs, t, st⟩ := x
    unfold run at h
    simp only at h
    revert lab
    refine execBlob.partial_correctness lib O c gul
      (fun st regs t b params r => ∀ lab, ∃ es y, Steps lib O c gul ⟨lab, b, params, regs, t, st⟩ es y ∧
        endOf lib O gul y = some r) ?_ st regs t b params r h
    intro rec ih st regs t b params r h lab
    simp only [Option.bind_eq_bind] at h
    split at h
    · rename_i hne
      obtain ⟨R, hR, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨es, y, hs, he⟩ := ih _ _ _ _ _ _ h lab
      exact ⟨[] ++ es, y, Steps.step (Step.pass (x := ⟨lab, b, params, regs, t, st⟩) hne hR) hs, he⟩
    · rename_i hne
      simp only [not_or, ne_eq, Decidable.not_not] at hne
      obtain ⟨hp, hq⟩ := hne
      subst hp
      split at h
      · rename_i p rest hb
        obtain ⟨⟨ton, R, t', st'⟩, hpole, h⟩ := Option.bind_eq_some_iff.mp h
        cases ton with
        | zero n =>
          obtain ⟨es, y, hs, he⟩ := ih _ _ _ _ _ _ h lab
          exact ⟨[] ++ es, y, Steps.step (Step.op (x := ⟨lab, b, [], regs, t, st⟩) rfl hq hb hpole) hs, he⟩
        | one m =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨[], _, Steps.refl _, ?_⟩
          simp [endOf, hq, hb, hpole]
        | two m =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨[], _, Steps.refl _, ?_⟩
          simp [endOf, hq, hb, hpole]
      · rename_i hb
        have jump : ∀ j, taken regs b.fin = some j →
            ((HoonMap.get c.blocks j.there).bind fun b' => rec st regs t b' j.args) = some r →
            ∃ es y, Steps lib O c gul ⟨lab, b, [], regs, t, st⟩ es y ∧ endOf lib O gul y = some r := by
          intro j ht h
          obtain ⟨b', hb', h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨es, y, hs, he⟩ := ih _ _ _ _ _ _ h j.there
          exact ⟨_, y, Steps.step (Step.jump (x := ⟨lab, b, [], regs, t, st⟩) rfl hq hb ht hb') hs, he⟩
        have fin0 : endOf lib O gul ⟨lab, b, [], regs, t, st⟩ = some r →
            ∃ es y, Steps lib O c gul ⟨lab, b, [], regs, t, st⟩ es y ∧ endOf lib O gul y = some r :=
          fun he => ⟨[], _, Steps.refl _, he⟩
        obtain ⟨fin, hf⟩ : ∃ f, b.fin = f := ⟨_, rfl⟩
        rw [hf] at h
        match fin, h, hf with
        | Termin.lti n r0 z o, h, hf =>
          obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
          refine jump _ ?_ h; simp [taken, hf, hv] <;> cases v <;> rfl
        | Termin.clq r0 z o, h, hf =>
          obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
          refine jump _ ?_ h; simp [taken, hf, hv] <;> cases v <;> rfl
        | Termin.eqq l r0 z o, h, hf =>
          obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
          refine jump _ ?_ h; simp [taken, hf, hx, hy]
        | Termin.brn r0 z o, h, hf =>
          obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
          by_cases h0 : v = A 0
          · simp only [h0, if_true] at h; refine jump z ?_ h; simp [taken, hf, hv, h0]
          · by_cases h1 : v = A 1
            · simp only [h1] at h; simp at h; refine jump o ?_ h; simp [taken, hf, hv, h1]
            · simp only [h0, h1, if_false, Option.some.injEq] at h; subst h
              exact fin0 (by simp [endOf, hq, hb, hf, hv, h0, h1])
        | Termin.brz r0 z o, h, hf =>
          obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
          refine jump _ ?_ h; simp [taken, hf, hv]
        | Termin.hop j, h, hf =>
          refine jump j ?_ h; simp [taken, hf]
        | Termin.jmp a v, h, hf => exact fin0 (by simp only [endOf, hq, hb, hf]; simpa using h)
        | Termin.jmf a v n, h, hf => exact fin0 (by simp only [endOf, hq, hb, hf]; simpa using h)
        | Termin.jsp a r0, h, hf => exact fin0 (by simp only [endOf, hq, hb, hf]; simpa using h)
        | Termin.jsf a r0 n, h, hf => exact fin0 (by simp only [endOf, hq, hb, hf]; simpa using h)
        | Termin.don r0, h, hf => exact fin0 (by simp only [endOf, hq, hb, hf]; simpa using h)
        | Termin.bom o, h, hf => exact fin0 (by simp only [endOf, hq, hb, hf]; simpa using h)
  · rintro ⟨es, y, hs, he⟩
    exact (steps_run hs).trans (endOf_run he)

/-! ## Determinism and the jumps -/

/-- **Steps are deterministic.** -/
theorem step_det {x y y' : Cfg σ Map} {e e' : List (Nat × Nat)} (h : Step lib O c gul x e y)
    (h' : Step lib O c gul x e' y') : e = e' ∧ y = y' := by
  cases h <;> cases h' <;> simp_all

theorem step_hop {x : Cfg σ Map} {j : Jmp} {b' : Blob} (hp : x.params = []) (hq : x.b.par = [])
    (hb : x.b.body = []) (hf : x.b.fin = Termin.hop j) (hb' : HoonMap.get c.blocks j.there = some b') :
    Step lib O c gul x [(x.lab, j.there)] ⟨j.there, b', j.args, x.regs, x.t, x.st⟩ :=
  Step.jump hp hq hb (by simp [taken, hf]) hb'

/-- A `%brn` on a register that reads `0` goes to its yes side. -/
theorem step_brn0 {x : Cfg σ Map} {r : Nat} {z o : Jmp} {b' : Blob} (hp : x.params = []) (hq : x.b.par = [])
    (hb : x.b.body = []) (hf : x.b.fin = Termin.brn r z o) (hr : read r x.regs = some (A 0))
    (hb' : HoonMap.get c.blocks z.there = some b') :
    Step lib O c gul x [(x.lab, z.there)] ⟨z.there, b', z.args, x.regs, x.t, x.st⟩ :=
  Step.jump hp hq hb (by simp [taken, hf, hr]) hb'

/-- A `%brn` on a register that reads `1` goes to its no side. -/
theorem step_brn1 {x : Cfg σ Map} {r : Nat} {z o : Jmp} {b' : Blob} (hp : x.params = []) (hq : x.b.par = [])
    (hb : x.b.body = []) (hf : x.b.fin = Termin.brn r z o) (hr : read r x.regs = some (A 1))
    (hb' : HoonMap.get c.blocks o.there = some b') :
    Step lib O c gul x [(x.lab, o.there)] ⟨o.there, b', o.args, x.regs, x.t, x.st⟩ :=
  Step.jump hp hq hb (by simp [taken, hf, hr]) hb'

/-- A `%brz` goes to its `z` side on `0` and to its `o` side on anything else. -/
theorem step_brz {x : Cfg σ Map} {r : Nat} {z o : Jmp} {v : Noun} {b' : Blob} (hp : x.params = [])
    (hq : x.b.par = []) (hb : x.b.body = []) (hf : x.b.fin = Termin.brz r z o) (hr : read r x.regs = some v)
    (hb' : HoonMap.get c.blocks (if v = A 0 then z else o).there = some b') :
    Step lib O c gul x [(x.lab, (if v = A 0 then z else o).there)]
      ⟨(if v = A 0 then z else o).there, b', (if v = A 0 then z else o).args, x.regs, x.t, x.st⟩ :=
  Step.jump hp hq hb (by simp [taken, hf, hr]) hb'

/-- A jump step is the only kind that changes the label, and it records it. -/
theorem step_edge {x y : Cfg σ Map} {e : List (Nat × Nat)} (h : Step lib O c gul x e y) :
    (e = [] ∧ y.lab = x.lab) ∨ e = [(x.lab, y.lab)] := by
  cases h <;> simp

theorem steps_trans {x y z : Cfg σ Map} {es es' : List (Nat × Nat)} (h : Steps lib O c gul x es y)
    (h' : Steps lib O c gul y es' z) : Steps lib O c gul x (es ++ es') z := by
  induction h with
  | refl => exact h'
  | step s _ ih => rw [List.append_assoc]; exact Steps.step s (ih h')

/-! ## Runs from the entry -/

/-- The configuration `execEntry` starts from: block `0` with the values in
registers `0 ..`. -/
def FromEntry (st : σ) (vals : List Noun) (t : Trace) (es : List (Nat × Nat)) (y : Cfg σ Map) : Prop :=
  ∃ b0, HoonMap.get c.blocks 0 = some b0 ∧ Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y

/-- **`execEntry` returns `r` exactly when a path from the entry reaches an
end that is `r`.** -/
theorem execEntry_iff_path (st : σ) (vals : List Noun) (t : Trace) (r : Tone × σ) :
    execEntry lib O st c vals t gul = some r ↔
      ∃ es y, FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y ∧ endOf lib O gul y = some r := by
  unfold execEntry FromEntry
  constructor
  · intro h
    obtain ⟨b0, hb0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨es, y, hs, he⟩ := (run_iff_path (lib := lib) (O := O) (c := c) (gul := gul)
      ⟨0, b0, [], regsOf vals, t, st⟩ r).mp h
    exact ⟨es, y, ⟨b0, hb0, hs⟩, he⟩
  · rintro ⟨es, y, ⟨b0, hb0, hs⟩, he⟩
    rw [hb0, Option.bind_some]
    exact (run_iff_path (lib := lib) (O := O) (c := c) (gul := gul) ⟨0, b0, [], regsOf vals, t, st⟩ r).mpr
      ⟨es, y, hs, he⟩

/-! ## Real reads -/

variable (gul) in
/-- The registers an op reads for real (`+read`, which fails on poison).  A
`%mov` reads none (`+move` copies poison), nor do the ops without operands;
`%hdp` reads its register only under a tag that `stopTag` keeps, and `%spy`
only with a scry gate. -/
def poleReads : Pole → List Nat
  | Pole.inc s _ => [s]
  | Pole.con h t _ => [h, t]
  | Pole.hed s _ => [s]
  | Pole.tal s _ => [s]
  | Pole.cel p => [p]
  | Pole.lob p => [p]
  | Pole.equ l r => [l, r]
  | Pole.hdp n p _ => if stopTag n then [p] else []
  | Pole.hmp _ v _ => v
  | Pole.spy e p _ => if gul = A 0 then [] else [e, p]
  | Pole.nok u f _ => [u, f]
  | Pole.cal _ v _ => v
  | Pole.caf _ v _ _ => v
  | Pole.cam _ v _ _ => v
  | Pole.csl _ s _ => [s]
  | Pole.csf _ s _ _ => [s]
  | Pole.csm _ s _ _ => [s]
  | _ => []

/-- The registers a terminator reads for real.  A hop reads none: its
arguments are moves (`+eval-pass`). -/
def finReads : Termin → List Nat
  | Termin.clq s _ _ => [s]
  | Termin.eqq l r _ _ => [l, r]
  | Termin.brn s _ _ => [s]
  | Termin.brz s _ _ => [s]
  | Termin.lti _ s _ _ => [s]
  | Termin.jmp _ v => v
  | Termin.jmf _ v _ => v
  | Termin.jsp _ s => [s]
  | Termin.jsf _ s _ => [s]
  | Termin.don s => [s]
  | _ => []

variable (gul) in
/-- The next action of `x` reads `k` for real. -/
def ReadsAt (x : Cfg σ Map) (k : Nat) : Prop :=
  x.params = [] ∧ x.b.par = [] ∧
    ((∃ p rest, x.b.body = p :: rest ∧ k ∈ poleReads gul p) ∨ (x.b.body = [] ∧ k ∈ finReads x.b.fin))

theorem mapM_read_none {k : Nat} {regs : Map (Option Noun)} (hr : read k regs = none) :
    ∀ v : List Nat, k ∈ v → v.mapM (read · regs) = none
  | [], hk => absurd hk List.not_mem_nil
  | a :: v, hk => by
    rcases List.mem_cons.mp hk with rfl | hk
    · simp [List.mapM_cons, hr]
    · have := mapM_read_none hr v hk
      simp only [List.mapM_cons, this]
      cases read a regs <;> simp

theorem execPole_poison {k : Nat} {regs : Map (Option Noun)} {st : σ} {t : Trace} {p : Pole}
    (hk : k ∈ poleReads gul p) (hr : read k regs = none) : execPole lib O gul st p regs t = none := by
  cases p <;> simp only [poleReads, List.mem_cons, List.not_mem_nil, or_false] at hk
  case hdp n q f =>
    split at hk
    · rename_i hs; simp only [List.mem_singleton] at hk; subst hk; simp [execPole, localPole, hs, hr]
    · simp at hk
  case spy e q d =>
    split at hk
    · simp at hk
    · rename_i hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> simp [execPole, localPole, hg, hr] <;> cases read _ regs <;> simp
  all_goals first
    | (subst hk; simp [execPole, localPole, hr]; done)
    | (rcases hk with rfl | rfl <;> simp [execPole, localPole, hr] <;> cases read _ regs <;> simp; done)
    | (simp [execPole, localPole, mapM_read_none hr _ hk]; done)

/-- **A real read of a poisoned (or missing) register crashes the run.** -/
theorem run_poison {x : Cfg σ Map} {k : Nat} (hk : ReadsAt gul x k) (hr : read k x.regs = none) :
    run lib O c gul x = none := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  obtain ⟨hp, hq, hk⟩ := hk
  simp only at hp hq hk hr ⊢
  subst hp hq
  unfold run; rw [execBlob]
  simp only [ne_eq, not_true, or_self, if_false, Option.bind_eq_bind]
  rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, hk⟩
  · subst hb; simp [execPole_poison hk hr]
  · subst hb
    cases fin <;> simp only [finReads, List.mem_cons, List.not_mem_nil, or_false] at hk
    all_goals first
      | (subst hk; simp [hr]; done)
      | (rcases hk with rfl | rfl <;> simp [hr] <;> cases read _ regs <;> simp; done)
      | (simp [mapM_read_none hr _ hk]; done)

/-- **On a path of a run that succeeds, every real read reads a value.** -/
theorem steps_reads {x z : Cfg σ Map} {es : List (Nat × Nat)} {r : Tone × σ} (hs : Steps lib O c gul x es z)
    (hx : run lib O c gul x = some r) {k : Nat} (hk : ReadsAt gul z k) : ∃ v, read k z.regs = some v := by
  cases e : read k z.regs with
  | some v => exact ⟨v, rfl⟩
  | none => rw [steps_run hs, run_poison hk e] at hx; cases hx

/-! ## The guard half of the threading invariant -/

/-- **The guard half**: every path from the entry that reaches a real read
of `k` passed the edge `e` (for a proxy, the edge from the block of the `%6`'s
`%brn` to the side whose branch made it). -/
def Guarded (st : σ) (vals : List Noun) (t : Trace) (k : Nat) (e : Nat × Nat) : Prop :=
  ∀ es y, FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y → ReadsAt gul y k → e ∈ es

/-- **The register half, on paths**: past the edge `e`, a real read of `k`
reads a value (the proxy's definition, passed to it by the branch that made
it). -/
def HeldAfter (st : σ) (vals : List Noun) (t : Trace) (k : Nat) (e : Nat × Nat) : Prop :=
  ∀ es y, FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y → e ∈ es → ReadsAt gul y k →
    ∃ v, read k y.regs = some v

/-- **The two halves together**: every real read of `k` reads a value, on
every path from the entry, whatever the other paths pass to `k`. -/
theorem guarded_reads {st : σ} {vals : List Noun} {t : Trace} {k : Nat} {e : Nat × Nat}
    (hg : Guarded (lib := lib) (O := O) (c := c) (gul := gul) st vals t k e)
    (hh : HeldAfter (lib := lib) (O := O) (c := c) (gul := gul) st vals t k e) :
    ∀ es y, FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y → ReadsAt gul y k →
      ∃ v, read k y.regs = some v :=
  fun es y hy hk => hh es y hy (hg es y hy hk) hk

end

end Path
end SkaModel
end Formalization
