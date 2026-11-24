import lemmas.Ska.OptAliasStart
import lemmas.Ska.ExecPath

/-!
# The end of a block of `+alias` (`aliasFin`, `aliasFold`)

`aliasFin` renames the registers an end reads through `old`, and folds a
two-way end whose test the facts decide: a `%clq` on a register known to be a
cell (or an atom), an `%eqq` of two registers renamed to the same one, a
`%brn` or `%brz` on a known immediate, to a hop to the side the facts give;
a `%brn` on a register known to be a loobean becomes a `%brz`, and a `%brn` on
a known immediate that is no loobean becomes `[%bom ~]`.

On a register file `R` on which the facts at the end hold (`FactsOK`) and
every register the end reads reads through `old` what it holds, the end after
takes the jump the end before takes (`takenR`, the jump of `Path.taken` on
the values; `afn_taken`), to the same block, with the arguments renamed by
`old` (**`afn_jump`**), and the edge it takes stays listed in `rev`; the end
after then goes to that block in the sense of `GoesTo` (**`afn_goesTo`**),
which is what `ast_start` needs.  An end that leaves the function or ends it
(`endR`, the end of `Path.endOf` on the values) returns the same
(**`afn_end`**), given that the test of a `%brn` holds a value (a real read,
`ReadsOK`).

`%lti` is excluded: `aliasFin` keeps it as it is without renaming its
register, which is sound only because no `%lti` exists before
`+switch-chains`, which runs after the loop that calls `+alias`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- The jump an end takes on the values `R` (`Path.taken` on values). -/
def takenR (R : Nat → Option Noun) : Termin → Option Jmp
  | Termin.lti n r z o => (R r).map fun v =>
      if (match v with | Noun.atom a => decide (a < n) | _ => false) then z else o
  | Termin.clq r z o => (R r).map fun v => match v with | Noun.cell _ _ => z | Noun.atom _ => o
  | Termin.eqq l r z o => (R l).bind fun x => (R r).map fun y => if x = y then z else o
  | Termin.brn r z o => (R r).bind fun v => if v = A 0 then some z else if v = A 1 then some o else none
  | Termin.brz r z o => (R r).map fun v => if v = A 0 then z else o
  | Termin.hop t => some t
  | _ => none

theorem afn_taken (regs : Map (Option Noun)) (fin : Termin) :
    Path.taken regs fin = takenR (fun x => read x regs) fin := by
  cases fin <;> rfl

/-- `takenR` reads only the registers of `finReads`. -/
theorem afn_taken_congr {R R' : Nat → Option Noun} {fin : Termin} (h : ∀ x ∈ Path.finReads fin, R' x = R x) :
    takenR R' fin = takenR R fin := by
  cases fin <;> simp only [takenR, Path.finReads, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h ⊢
  all_goals first
    | rfl
    | (rw [h])
    | (rw [h.1, h.2])

/-- A two-way end folded to a hop to `go`. -/
theorem afn_fold_fin (rev : Nat → List Nat) (o go cut : Nat) :
    (aliasFold rev o go cut).1 = Termin.hop { args := [], there := go } := rfl

/-- A fold keeps the edge to the side it goes to. -/
theorem afn_fold_rev {rev : Nat → List Nat} {o go cut : Nat} (h : o ∈ rev go) :
    o ∈ (aliasFold rev o go cut).2.1 go := by
  by_cases e : go = cut
  · subst e; simpa [aliasFold] using h
  · simpa [aliasFold, delJu, updA, e] using h

/-- What a fold to `go` does, for a two-way end whose sides pass nothing and
whose side taken is `go`. -/
theorem afn_fold_jump {rev : Nat → List Nat} {o go cut : Nat} {old : Nat → Nat} {R : Nat → Option Noun} {j : Jmp}
    (hj : j.there = go) (ha : j.args = []) :
    ∃ j', takenR R (aliasFold rev o go cut).1 = some j' ∧ j'.there = j.there ∧
      j'.args = j.args.map (Option.map old) ∧ (o ∈ rev j.there → o ∈ (aliasFold rev o go cut).2.1 j.there) :=
  ⟨{ args := [], there := go }, rfl, hj.symm, by rw [ha]; rfl, fun h => by rw [hj] at h ⊢; exact afn_fold_rev h⟩

/-- **The end after takes the jump the end before takes**, to the same
block, with the arguments renamed by `old`, and the edge stays listed. -/
theorem afn_jump {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} {R : Nat → Option Noun} {j : Jmp}
    (h : aliasFin old loc rev f o fin = some r) (hf : FactsOK R loc)
    (hold : ∀ x ∈ Path.finReads fin, R (old x) = R x) (hnl : ∀ n s z o', fin ≠ Termin.lti n s z o')
    (ht : takenR R fin = some j) :
    ∃ j', takenR R r.1 = some j' ∧ j'.there = j.there ∧ j'.args = j.args.map (Option.map old) ∧
      (o ∈ rev j.there → o ∈ r.2.1 j.there) := by
  cases fin with
  | clq s z o' =>
    have hs := hold s (by simp [Path.finReads])
    simp only [aliasFin] at h
    split at h
    · cases h
    rename_i hargs
    simp only [not_or, Decidable.not_not] at hargs
    obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
    simp only [takenR] at ht
    obtain ⟨v, hv, hj⟩ := Option.map_eq_some_iff.mp ht
    have hI := hf _ ic v hic (by rw [hs, hv])
    have jz : j.args = [] := by rw [← hj]; cases v <;> simp [hargs.1, hargs.2]
    split at e
    · rename_i hc
      have hcell : ∃ a b, v = Noun.cell a b := by
        rcases Bool.or_eq_true_iff.mp hc with hc | hc
        · exact hI.1 hc
        · unfold InfoReg.cellImm at hc
          split at hc
          · rename_i a b hm; exact ⟨a, b, hI.2.2.1 _ hm⟩
          · cases hc
      obtain ⟨a, b, rfl⟩ := hcell
      subst e
      exact afn_fold_jump (by rw [← hj]) jz
    · split at e
      · rename_i _ hc
        have hat : ∃ a, v = Noun.atom a := by
          rcases Bool.or_eq_true_iff.mp hc with hc | hc
          · rcases hI.2.1 hc with e1 | e1 <;> exact ⟨_, e1⟩
          · unfold InfoReg.atomImm at hc
            split at hc
            · rename_i a hm; exact ⟨a, hI.2.2.1 _ hm⟩
            · cases hc
        obtain ⟨a, rfl⟩ := hat
        subst e
        exact afn_fold_jump (by rw [← hj]) jz
      · subst e
        refine ⟨j, ?_, rfl, by rw [jz]; rfl, fun h => h⟩
        simp only [takenR, hs, hv, Option.map_some]
        exact congrArg some hj
  | eqq l r0 z o' =>
    have hl := hold l (by simp [Path.finReads])
    have hr := hold r0 (by simp [Path.finReads])
    simp only [aliasFin] at h
    split at h
    · cases h
    rename_i hargs
    simp only [not_or, Decidable.not_not] at hargs
    simp only [takenR] at ht
    obtain ⟨x, hx, ht⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨y, hy, hj⟩ := Option.map_eq_some_iff.mp ht
    have jz : j.args = [] := by rw [← hj]; split <;> simp [hargs.1, hargs.2]
    split at h
    · simp only [Option.some.injEq] at h; subst h
      refine ⟨j, ?_, rfl, by rw [jz]; rfl, fun h => h⟩
      simp only [takenR, hl, hr, hx, hy, Option.bind_some, Option.map_some]
      exact congrArg some hj
    · rename_i he
      simp only [ne_eq, Decidable.not_not] at he
      have hxy : x = y := by
        have := hl.symm.trans ((congrArg R he).trans hr)
        rw [hx, hy] at this; cases this; rfl
      simp only [hxy, if_true] at hj
      simp only [Option.some.injEq] at h; subst h
      exact afn_fold_jump (by rw [← hj]) jz
  | brn s z o' =>
    have hs := hold s (by simp [Path.finReads])
    simp only [aliasFin] at h
    split at h
    · cases h
    rename_i hargs
    simp only [not_or, Decidable.not_not] at hargs
    obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
    simp only [takenR] at ht
    obtain ⟨v, hv, hj⟩ := Option.bind_eq_some_iff.mp ht
    have hI := hf _ ic v hic (by rw [hs, hv])
    have hv01 : (v = A 0 ∧ j = z) ∨ (v = A 1 ∧ j = o') := by
      by_cases h0 : v = A 0
      · simp only [h0, if_true, Option.some.injEq] at hj; exact Or.inl ⟨h0, hj.symm⟩
      · by_cases h1 : v = A 1
        · simp [h1, A] at hj; exact Or.inr ⟨h1, hj.symm⟩
        · simp [h0, h1] at hj
    have jz : j.args = [] := by rcases hv01 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [hargs.1, hargs.2]
    split at e
    · split at e
      · subst e
        refine ⟨j, ?_, rfl, by rw [jz]; rfl, fun h => h⟩
        simp only [takenR, hs, hv, Option.map_some]
        rcases hv01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp
        · simp [A]
      · subst e
        refine ⟨j, ?_, rfl, by rw [jz]; rfl, fun h => h⟩
        simp only [takenR, hs, hv, Option.bind_some]
        exact hj
    · rename_i hm
      have := hI.2.2.1 _ hm
      subst e
      rcases hv01 with ⟨e1, rfl⟩ | ⟨e1, rfl⟩
      · exact afn_fold_jump rfl jz
      · rw [this] at e1; cases e1
    · rename_i hm
      have := hI.2.2.1 _ hm
      subst e
      rcases hv01 with ⟨e1, rfl⟩ | ⟨e1, rfl⟩
      · rw [this] at e1; cases e1
      · exact afn_fold_jump rfl jz
    · rename_i n hn0 hn1 hm
      have := hI.2.2.1 _ hm
      subst this
      rcases hv01 with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact absurd e1 (fun e => hn0 e)
      · exact absurd e1 (fun e => hn1 e)
  | brz s z o' =>
    have hs := hold s (by simp [Path.finReads])
    simp only [aliasFin] at h
    split at h
    · cases h
    rename_i hargs
    simp only [not_or, Decidable.not_not] at hargs
    obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
    simp only [takenR] at ht
    obtain ⟨v, hv, hj⟩ := Option.map_eq_some_iff.mp ht
    have hI := hf _ ic v hic (by rw [hs, hv])
    have jz : j.args = [] := by rw [← hj]; split <;> simp [hargs.1, hargs.2]
    split at e
    · subst e
      refine ⟨j, ?_, rfl, by rw [jz]; rfl, fun h => h⟩
      simp only [takenR, hs, hv, Option.map_some]
      exact congrArg some hj
    · rename_i hz
      have hv0 : v = A 0 := by
        split at hz
        · rename_i w hw
          simp only [Option.some.injEq, decide_eq_true_eq] at hz
          rw [hI.2.2.1 _ hw, hz]
        · split at hz <;> cases hz
      subst e
      simp only [hv0, if_true] at hj
      exact afn_fold_jump (by rw [← hj]) jz
    · rename_i hz
      have hv0 : v ≠ A 0 := by
        split at hz
        · rename_i w hw
          simp only [Option.some.injEq, decide_eq_false_iff_not] at hz
          rw [hI.2.2.1 _ hw]; exact hz
        · split at hz
          · rename_i hc
            obtain ⟨a, b, rfl⟩ := hI.1 hc
            exact fun e => by cases e
          · cases hz
      subst e
      simp only [hv0, if_false] at hj
      exact afn_fold_jump (by rw [← hj]) jz
  | hop t =>
    simp only [aliasFin, Option.some.injEq] at h
    subst h
    simp only [takenR, Option.some.injEq] at ht
    subst ht
    exact ⟨_, rfl, rfl, rfl, fun h => h⟩
  | lti n s z o' => exact absurd rfl (hnl n s z o')
  | jmp => simp [takenR] at ht
  | jmf => simp [takenR] at ht
  | jsp => simp [takenR] at ht
  | jsf => simp [takenR] at ht
  | don => simp [takenR] at ht
  | bom => simp [takenR] at ht

/-- **An end that takes a jump to `o` goes to `o`** (`GoesTo`). -/
theorem afn_goesTo {R : Nat → Option Noun} {fin : Termin} {j : Jmp} (h : takenR R fin = some j) :
    GoesTo R j.there fin := by
  cases fin with
  | brn s z o' =>
    simp only [takenR] at h
    obtain ⟨v, hv, hj⟩ := Option.bind_eq_some_iff.mp h
    simp only [GoesTo]
    by_cases h0 : v = A 0
    · subst h0; simp only [if_true, Option.some.injEq] at hj; subst hj; exact Or.inl ⟨hv, rfl⟩
    · by_cases h1 : v = A 1
      · subst h1; simp [A] at hj; subst hj; exact Or.inr ⟨hv, rfl⟩
      · simp [h0, h1] at hj
  | brz s z o' =>
    simp only [takenR] at h
    obtain ⟨v, hv, hj⟩ := Option.map_eq_some_iff.mp h
    simp only [GoesTo]
    by_cases h0 : v = A 0
    · subst h0; simp only [if_true] at hj; subst hj; exact Or.inl ⟨hv, rfl⟩
    · simp only [h0, if_false] at hj; subst hj; exact Or.inr ⟨v, hv, h0, rfl⟩
  | clq s z o' =>
    simp only [takenR] at h
    obtain ⟨v, hv, hj⟩ := Option.map_eq_some_iff.mp h
    simp only [GoesTo]
    cases v with
    | cell a b => simp only at hj; subst hj; exact Or.inl ⟨a, b, hv, rfl⟩
    | atom a => simp only at hj; subst hj; exact Or.inr ⟨a, hv, rfl⟩
  | _ => trivial

/-! ## Ends that leave the function -/

section
variable {σ : Type}

/-- What an end that leaves the function or ends it returns, on the values
(`Path.endOf` at an end; `afn_endOf`). -/
def endR (O : Oracle σ) (gul : Noun) (R : Nat → Option Noun) (st : σ) (t : Trace) : Termin → Option (Tone × σ)
  | Termin.brn r _ _ => (R r).bind fun v => if v = A 0 ∨ v = A 1 then none else some (Tone.two t, st)
  | Termin.jmp a v => (v.mapM R).bind fun vs => O.call st a false vs t gul
  | Termin.jmf a v _ => (v.mapM R).bind fun vs => O.call st a false vs t gul
  | Termin.jsp a r => (R r).bind fun v => O.call st a true [v] t gul
  | Termin.jsf a r _ => (R r).bind fun v => O.call st a true [v] t gul
  | Termin.don r => (R r).bind fun v => some (Tone.zero v, st)
  | Termin.bom _ => some (Tone.two t, st)
  | _ => none

theorem afn_endOf {lib : Lib} {O : Oracle σ} {gul : Noun} {x : Path.Cfg σ Map} (hp : x.params = [])
    (hq : x.b.par = []) (hb : x.b.body = []) :
    Path.endOf lib O gul x = endR O gul (fun k => read k x.regs) x.st x.t x.b.fin := by
  unfold Path.endOf
  simp only [hp, hq, ne_eq, not_true_eq_false, or_self, if_false, hb]
  cases x.b.fin <;> rfl

theorem afn_mapM {old : Nat → Nat} {R : Nat → Option Noun} :
    ∀ v : List Nat, (∀ x ∈ v, R (old x) = R x) → (v.map old).mapM R = v.mapM R
  | [], _ => rfl
  | x :: v, h => by
    simp only [List.map_cons, List.mapM_cons, h x List.mem_cons_self,
      afn_mapM v fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **An end that leaves the function or ends it returns the same after**,
given that the test of a `%brn` holds a value. -/
theorem afn_end {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} {R : Nat → Option Noun} (O : Oracle σ) (gul : Noun) (st : σ)
    (t : Trace) (h : aliasFin old loc rev f o fin = some r) (hf : FactsOK R loc)
    (hold : ∀ x ∈ Path.finReads fin, R (old x) = R x) (hnl : ∀ n s z o', fin ≠ Termin.lti n s z o')
    (hval : ∀ s z o', fin = Termin.brn s z o' → (R s).isSome) :
    endR O gul R st t r.1 = endR O gul R st t fin := by
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
    split at e
    · subst e; rfl
    · split at e <;> (subst e; rfl)
  | eqq l r0 z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    split at h <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | brn s z o' =>
    have hs := hold s (by simp [Path.finReads])
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval s z o' rfl)
    simp only [aliasFin] at h
    split at h
    · cases h
    obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
    have hI := hf _ ic v hic (by rw [hs, hv])
    have rhs : endR O gul R st t (Termin.brn s z o') =
        if v = A 0 ∨ v = A 1 then none else some (Tone.two t, st) := by
      simp only [endR, hv, Option.bind_some]
    rw [rhs]
    split at e
    · split at e
      · rename_i hl
        subst e
        rcases hI.2.1 hl with e1 | e1 <;> simp [e1, endR]
      · subst e
        simp only [endR, hs, hv, Option.bind_some]
    · rename_i hm
      subst e
      rw [hI.2.2.1 _ hm]; simp [endR, aliasFold]
    · rename_i hm
      subst e
      rw [hI.2.2.1 _ hm]; simp [endR, aliasFold, A]
    · rename_i n hn0 hn1 hm
      subst e
      rw [hI.2.2.1 _ hm]
      have : ¬ (n = A 0 ∨ n = A 1) := fun e => e.elim (fun e => hn0 e) (fun e => hn1 e)
      simp only [this, if_false, endR]
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
    split at e <;> (subst e; rfl)
  | hop t0 =>
    simp only [aliasFin, Option.some.injEq] at h; subst h; rfl
  | jmp a v =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    simp only [endR, afn_mapM v (fun x hx => hold x hx)]
  | jmf a v n =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    simp only [endR, afn_mapM v (fun x hx => hold x hx)]
  | jsp a s =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    simp only [endR, hold s (by simp [Path.finReads])]
  | jsf a s n =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    simp only [endR, hold s (by simp [Path.finReads])]
  | don s =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    simp only [endR, hold s (by simp [Path.finReads])]
  | bom u =>
    simp only [aliasFin, Option.some.injEq] at h; subst h; rfl
  | lti n s z o' => exact absurd rfl (hnl n s z o')

end

end Opt
end SkaModel
end Formalization
