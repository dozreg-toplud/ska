import lemmas.Compiler.CompSccLoopMemStep
import lemmas.Compiler.CompSccLoopPrint

/-! # `map-local` holds straights, and the loop's `M` decoded (README Gaps 21.17)

`MlExact` (`CompSccLoopClose.lean`) says of `map-local` only that the head of each value is the
model's need.  Every `member` call writes a straight there: on `%done` the straight of `finish`
(`(finish ~)`, or `(finish `np)` after `+coerce-soft`), off `%done` the placeholder `[np 0 ~]`
(`placeholder_straight`).  So the loop can carry, beside `LoopR`, that every value is a straight's
noun:

* `MlStr`, `LoopRS` (`LoopR` and `MlStr`), `mlStr_nil`, `mlStr_put`, `loopRS_reset`;
* `placeholder_straight`: the `%may` / `%must` value `[np 0 ~]` is the noun of the straight
  `⟨np, 0, ~⟩`, so those gates keep `MlStr` by `mlStr_put` (the obligation of track A's side);
* **`ml_decode`**: a map that holds `ml` exactly (`MlExact`) and holds straights (`MlStr`), whose
  keys are bells, is `FinMap.toNoun` of a map of straights whose needs are `ml`'s (through
  `isMap_ext`).

The copies of the member step and of the loop's gate at `LoopRS` are generated
(`CompSccLoopStrGen.lean`, `tools/gen/mlstr.py`); the gate with its `M` decoded is in
`CompSccLoopStrDec.lean`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Every value of `map-local` is the noun of a straight. -/
def MlStr (ML : Noun) : Prop :=
  ∀ k v, Get ML k v → ∃ s : Straight (TreapMap mugF), v = s.toNoun

/-- **The relation of the loop with straights**: `LoopR` and `MlStr` of `map-local`. -/
def LoopRS (bs : List Noun) (outC : Noun → List Noun) (nout : Noun → NeedOrd) (Q : Noun → Prop)
    (ml sure : Noun → Option NeedOrd) (ML CA : Noun) : Prop :=
  LoopR bs outC nout Q ml sure ML CA ∧ MlStr ML

theorem mlStr_nil : MlStr (A 0) := fun k v h => absurd h (by simp [get_nil])

/-- The `+put:by` of a straight's noun keeps `MlStr`. -/
theorem mlStr_put {ML ML' b v : Noun} (h : MlStr ML) (hv : ∃ s : Straight (TreapMap mugF), v = s.toNoun)
    (hm : IsMap mugF ML) (hp : putF mugF b v ML = some ML') : MlStr ML' := by
  obtain ⟨out, hput, -, hget⟩ := putF_spec mugF ML b v hm
  rw [hp] at hput
  obtain rfl := Option.some.inj hput
  intro k w hw
  rcases (hget k w).1 hw with ⟨rfl, rfl⟩ | ⟨-, hw'⟩
  · exact hv
  · exact h k w hw'

theorem loopRS_reset (bs : List Noun) (outC : Noun → List Noun) (nout : Noun → NeedOrd)
    (Q : Noun → Prop) : ∀ ml sure ML CA, LoopRS bs outC nout Q ml sure ML CA →
      LoopRS bs outC nout Q (fun _ => none) sure (A 0) CA :=
  fun ml sure ML CA h => ⟨loopR_reset bs outC nout Q ml sure ML CA h.1, mlStr_nil⟩

/-- **The placeholder of `finish` off `%done`** (`[need 0 ~]`, the `?.  done` branch of
`member`) is the noun of a straight with no blocks. -/
theorem placeholder_straight (np : NeedOrd) :
    C np.toNoun (C (A 0) (A 0)) = (⟨np, 0, HoonMap.empty⟩ : Straight (TreapMap mugF)).toNoun := rfl

/-- `LoopRS` after the `+put:by` at `b` of a straight whose need is `n`, from `LoopR` after it
(the `%may` / `%must` step: `[np 0 ~]` is `placeholder_straight`). -/
theorem loopRS_put {bs : List Noun} {outC : Noun → List Noun} {nout : Noun → NeedOrd} {Q : Noun → Prop}
    {ml sure ml' sure' : Noun → Option NeedOrd} {ML ML' CA CA' b v : Noun}
    (h : LoopRS bs outC nout Q ml sure ML CA) (hv : ∃ s : Straight (TreapMap mugF), v = s.toNoun)
    (hp : putF mugF b v ML = some ML') (h' : LoopR bs outC nout Q ml' sure' ML' CA') :
    LoopRS bs outC nout Q ml' sure' ML' CA' :=
  ⟨h', mlStr_put h.2 hv h.1.1.1 hp⟩

/-- **The loop's `map-local` decoded**: a map holding `ml` exactly and holding straights, whose
keys with a need are bells, is the noun `FinMap.toNoun` of a map of straights `m` (the shape
`unaryImageAt_of_gate` asks of `NM`), and the needs of `m` are those of `ml`. -/
theorem ml_decode {ml : Noun → Option NeedOrd} {M : Noun} (hE : MlExact ml M) (hS : MlStr M)
    (hk : ∀ k, (ml k).isSome → ∃ b : Bell, b.toNoun = k) :
    ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun ∧
      ∀ b : Bell, (m.1 b).map Straight.need = ml b.toNoun := by
  classical
  have huniq : ∀ k v w, Get M k v → Get M k w → v = w := by
    intro k v w hv hw
    have h1 := getF_some hE.1 hv
    rw [getF_some hE.1 hw] at h1
    simp only [Option.some.injEq, Noun.cell.injEq] at h1
    exact h1.2.symm
  let f : Bell → Option (Straight (TreapMap mugF)) := fun b =>
    if h : ∃ s : Straight (TreapMap mugF), Get M b.toNoun s.toNoun then some (Classical.choose h) else none
  have hfin : ∃ l : List Bell, ∀ b, f b ≠ none → b ∈ l := by
    refine ⟨(tapList M).filterMap (fun x => match x with
      | Noun.cell kn _ => FinMap.decode? (κ := Bell) kn
      | Noun.atom _ => none), fun b hb => ?_⟩
    have h : ∃ s : Straight (TreapMap mugF), Get M b.toNoun s.toNoun :=
      Classical.byContradiction fun h => hb (by simp only [f, dif_neg h])
    obtain ⟨s, hs⟩ := h
    rw [List.mem_filterMap]
    exact ⟨C b.toNoun s.toNoun, (mem_tapList hE.1 _).2 ⟨_, _, rfl, hs⟩, FinMap.decode?_enc (κ := Bell) b⟩
  let m : FinMap Bell (Straight (TreapMap mugF)) := ⟨f, hfin⟩
  have hm : ∀ b s, m.1 b = some s ↔ Get M b.toNoun s.toNoun := by
    intro b s
    show f b = some s ↔ _
    constructor
    · intro e
      by_cases h : ∃ s : Straight (TreapMap mugF), Get M b.toNoun s.toNoun
      · simp only [f, dif_pos h, Option.some.injEq] at e
        rw [← e]; exact Classical.choose_spec h
      · simp only [f, dif_neg h] at e; cases e
    · intro hg
      have h : ∃ s : Straight (TreapMap mugF), Get M b.toNoun s.toNoun := ⟨s, hg⟩
      simp only [f, dif_pos h, Option.some.injEq]
      exact straight_toNoun_inj (huniq _ _ _ (Classical.choose_spec h) hg)
  refine ⟨m, isMap_ext hE.1 (FinMap.isMap_toNoun _ m) (fun kn vn => ?_), fun b => ?_⟩
  · rw [FinMap.get_toNoun]
    constructor
    · intro hg
      obtain ⟨n, t, hn, rfl⟩ := hE.2.1 kn vn hg
      obtain ⟨b, rfl⟩ := hk kn (by simp [hn])
      obtain ⟨s, hs⟩ := hS _ _ hg
      exact ⟨b, s, (hm b s).2 (hs ▸ hg), rfl, hs⟩
    · rintro ⟨b, s, h1, rfl, rfl⟩
      exact (hm b s).1 h1
  · cases e : m.1 b with
    | some s =>
      have hg := (hm b s).1 e
      obtain ⟨n, t, hn, he⟩ := hE.2.1 _ _ hg
      rw [hn]
      simp only [Option.map_some, Option.some.injEq]
      simp only [Straight.toNoun, Noun.cell.injEq] at he
      exact needOrd_toNoun_inj he.1
    | none =>
      cases e2 : ml b.toNoun with
      | none => rfl
      | some n =>
        obtain ⟨t, ht⟩ := hE.2.2 _ n e2
        obtain ⟨s, hs⟩ := hS _ _ ht
        rw [(hm b s).2 (hs ▸ ht)] at e; cases e

end Compiler
end Formalization
