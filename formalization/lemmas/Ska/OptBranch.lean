import lemmas.Ska.Opt

/-!
# `+remove-useless-branching`

The model follows the Hoon (line 8981): `rubTwo` is the shared part of the
four cases (`?>` that both sides pass nothing, `got` of both targets, the
test `=(nex-z nex-o)`), `rubFin` the `?+` over the terminator with the
epilogue (`[%equ l r]` for `%eqq`, `[%lob s]` for `%brn`), `rubStep` the gate
of the `+rep:by`, and `removeUselessBranching` the fold over the keys in the
order of `MapKeys.keys`.  The order does not matter: each key's new value
depends only on the old map, and the flag is an `|` (`rubFold_get`).

`rub_keepsR`: the pass keeps the code (`KeepsR` of `Opt.lean`), with no
hypothesis on the CFG (`rub_keeps` in `OptArgs.lean` adds `ArgsOK`).  The proof is a simulation on paths (`RubRel`): the
two runs hold the same registers, trace and state, the block of the code
after is that of the code before with the epilogue appended and the new
terminator, or the epilogue has run.  Forward (`rub_fwd`), each step of the
code before is matched by at most two steps after; backward (`rub_bwd`),
each step after by at most one before, using `ReadsOK` of the code before at
a `%clq` or `%brz` that became a hop, the only place the code after reads less.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-! ## The model -/

/-- The shared part of the four cases. -/
def rubTwo (bl : Map Blob) (fin : Termin) (z o : Jmp) (epi : List Pole) : Option (List Pole × Termin) :=
  if z.args = [] ∧ o.args = [] then
    (HoonMap.get bl z.there).bind fun nz => (HoonMap.get bl o.there).map fun no =>
      if nz = no then (epi, Termin.hop ⟨[], z.there⟩) else ([], fin)
  else none

/-- The epilogue and the new terminator of one block. -/
def rubFin (bl : Map Blob) (fin : Termin) : Option (List Pole × Termin) :=
  match fin with
  | Termin.clq _ z o => rubTwo bl fin z o []
  | Termin.eqq l r z o => rubTwo bl fin z o [Pole.equ l r]
  | Termin.brn s z o => rubTwo bl fin z o [Pole.lob s]
  | Termin.brz _ z o => rubTwo bl fin z o []
  | _ => some ([], fin)

/-- `b(body (weld body.b epilogue), fin new-fin)`. -/
def rubBlob (b : Blob) (e : List Pole × Termin) : Blob := { b with body := b.body ++ e.1, fin := e.2 }

/-- The gate of the `+rep:by`. -/
def rubStep (bl : Map Blob) (acc : Option (Bool × Map Blob)) (o : Nat) : Option (Bool × Map Blob) :=
  acc.bind fun r => (HoonMap.get bl o).bind fun b => (rubFin bl b.fin).map fun e =>
    (r.1 || decide (e.2 ≠ b.fin), HoonMap.put r.2 o (rubBlob b e))

/-- `+remove-useless-branching`. -/
def removeUselessBranching [MapKeys Map] (bl : Map Blob) : Option (Bool × Map Blob) :=
  (MapKeys.keys bl).foldl (rubStep bl) (some (false, HoonMap.empty))

/-! ## The blocks after the pass -/

theorem rubFold_none (bl : Map Blob) : ∀ ks : List Nat, ks.foldl (rubStep bl) none = none
  | [] => rfl
  | _ :: ks => by simp only [List.foldl_cons, rubStep, Option.bind_none]; exact rubFold_none bl ks

theorem rubFold_get (bl : Map Blob) : ∀ (ks : List Nat) (acc : Option (Bool × Map Blob)) (r : Bool × Map Blob),
    ks.foldl (rubStep bl) acc = some r → ∃ a, acc = some a ∧
      (∀ k b, k ∈ ks → HoonMap.get bl k = some b → ∃ e, rubFin bl b.fin = some e ∧
        HoonMap.get r.2 k = some (rubBlob b e)) ∧
      (∀ k, (k ∉ ks ∨ HoonMap.get bl k = none) → HoonMap.get r.2 k = HoonMap.get a.2 k)
  | [], acc, r, h => by
    simp only [List.foldl_nil] at h; subst h
    exact ⟨r, rfl, fun _ _ hk => absurd hk List.not_mem_nil, fun _ _ => rfl⟩
  | k0 :: ks, acc, r, h => by
    simp only [List.foldl_cons] at h
    cases hs : rubStep bl acc k0 with
    | none => rw [hs, rubFold_none] at h; cases h
    | some a' =>
      rw [hs] at h
      obtain ⟨a'', ha'', hin, hout⟩ := rubFold_get bl ks _ r h
      cases ha''
      unfold rubStep at hs
      obtain ⟨a, ha, hs1⟩ := Option.bind_eq_some_iff.mp hs
      subst ha
      obtain ⟨b0, hb0, hs2⟩ := Option.bind_eq_some_iff.mp hs1
      obtain ⟨e0, he0, hs3⟩ := Option.map_eq_some_iff.mp hs2
      subst hs3
      refine ⟨a, rfl, ?_, ?_⟩
      · intro k b hk hb
        by_cases hks : k ∈ ks
        · exact hin k b hks hb
        · have hk0 : k = k0 := by
            rcases List.mem_cons.mp hk with h | h
            · exact h
            · exact absurd h hks
          subst hk0
          rw [hb0] at hb; cases hb
          refine ⟨e0, he0, ?_⟩
          rw [hout k (Or.inl hks)]; simp [HoonMap.get_put]
      · intro k hk
        have hk' : k ∉ ks ∨ HoonMap.get bl k = none := by
          rcases hk with hk | hk
          · exact Or.inl (fun h => hk (List.mem_cons_of_mem _ h))
          · exact Or.inr hk
        rw [hout k hk']
        simp only [HoonMap.get_put]
        by_cases e : k = k0
        · subst e
          rcases hk with hk | hk
          · exact absurd (List.mem_cons_self) hk
          · rw [hk] at hb0; cases hb0
        · simp [e]

/-- The blocks after the pass, block by block. -/
def RubBlocks (bl bl' : Map Blob) : Prop :=
  ∀ k, (HoonMap.get bl k = none → HoonMap.get bl' k = none) ∧
    ∀ b, HoonMap.get bl k = some b → ∃ e, rubFin bl b.fin = some e ∧ HoonMap.get bl' k = some (rubBlob b e)

theorem rub_blocks [MapKeys Map] {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl')) :
    RubBlocks bl bl' := by
  obtain ⟨a, ha, hin, hout⟩ := rubFold_get bl _ _ _ h
  cases ha
  intro k
  refine ⟨fun hk => ?_, fun b hb => hin k b ((MapKeys.mem_keys bl k).mpr (by simp [hb])) hb⟩
  rw [hout k (Or.inr hk)]; exact HoonMap.get_empty k

theorem RubBlocks.back {bl bl' : Map Blob} (h : RubBlocks bl bl') {k : Nat} {b' : Blob}
    (hb : HoonMap.get bl' k = some b') : ∃ b e, HoonMap.get bl k = some b ∧ rubFin bl b.fin = some e ∧
      b' = rubBlob b e := by
  cases e : HoonMap.get bl k with
  | none => rw [(h k).1 e] at hb; cases hb
  | some b =>
    obtain ⟨en, hen, hb'⟩ := (h k).2 b e
    rw [hb'] at hb; cases hb
    exact ⟨b, en, rfl, hen, rfl⟩

/-! ## What a terminator becomes -/

theorem rubTwo_cases {bl : Map Blob} {fin : Termin} {z o : Jmp} {epi : List Pole} {e : List Pole × Termin}
    (h : rubTwo bl fin z o epi = some e) :
    e = ([], fin) ∨ ∃ nz, z.args = [] ∧ o.args = [] ∧ HoonMap.get bl z.there = some nz ∧
      HoonMap.get bl o.there = some nz ∧ e = (epi, Termin.hop ⟨[], z.there⟩) := by
  unfold rubTwo at h
  split at h
  · rename_i hc
    obtain ⟨nz, hz, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨no, ho, h⟩ := Option.map_eq_some_iff.mp h
    split at h
    · rename_i heq; subst heq; exact Or.inr ⟨nz, hc.1, hc.2, hz, ho, h.symm⟩
    · exact Or.inl h.symm
  · simp at h

/-- The new terminator is the old one, or a hop to `z` of a branch whose two
targets are one block. -/
theorem rubFin_cases {bl : Map Blob} {fin : Termin} {e : List Pole × Termin} (h : rubFin bl fin = some e) :
    e = ([], fin) ∨ ∃ z o nz, z.args = [] ∧ o.args = [] ∧ HoonMap.get bl z.there = some nz ∧
      HoonMap.get bl o.there = some nz ∧ e.2 = Termin.hop ⟨[], z.there⟩ ∧
      ((∃ s, fin = Termin.clq s z o ∧ e.1 = []) ∨ (∃ s, fin = Termin.brz s z o ∧ e.1 = []) ∨
       (∃ l r, fin = Termin.eqq l r z o ∧ e.1 = [Pole.equ l r]) ∨
       (∃ s, fin = Termin.brn s z o ∧ e.1 = [Pole.lob s])) := by
  unfold rubFin at h
  split at h
  all_goals first
    | (exact Or.inl (Option.some.inj h).symm)
    | (rcases rubTwo_cases h with h | ⟨nz, h1, h2, h3, h4, rfl⟩
       · exact Or.inl h
       · refine Or.inr ⟨_, _, nz, h1, h2, h3, h4, rfl, ?_⟩; simp)

/-- A branch that takes a jump takes one of its two. -/
theorem taken_two {regs : Map (Option Noun)} {fin : Termin} {z o j : Jmp}
    (hf : (∃ s, fin = Termin.clq s z o) ∨ (∃ s, fin = Termin.brz s z o) ∨ (∃ l r, fin = Termin.eqq l r z o) ∨
      (∃ s, fin = Termin.brn s z o)) (ht : taken regs fin = some j) : j = z ∨ j = o := by
  rcases hf with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨l, r, rfl⟩ | ⟨s, rfl⟩
  · simp only [taken, Option.map_eq_some_iff] at ht
    obtain ⟨v, -, rfl⟩ := ht; cases v <;> simp
  · simp only [taken, Option.map_eq_some_iff] at ht
    obtain ⟨v, -, rfl⟩ := ht; split <;> simp
  · simp only [taken, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
    obtain ⟨_, -, _, -, rfl⟩ := ht; split <;> simp
  · simp only [taken, Option.bind_eq_some_iff] at ht
    obtain ⟨v, -, ht⟩ := ht
    split at ht
    · exact Or.inl (Option.some.inj ht).symm
    · split at ht
      · exact Or.inr (Option.some.inj ht).symm
      · cases ht

/-! ## The simulation -/

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map}

/-- Same registers, trace, state and arguments; the block after is the block
before with the epilogue and the new end, or the epilogue has run. -/
def RubRel (bl : Map Blob) (x x' : Cfg σ Map) : Prop :=
  x'.params = x.params ∧ x'.regs = x.regs ∧ x'.t = x.t ∧ x'.st = x.st ∧ ∃ e, rubFin bl x.b.fin = some e ∧
    (x'.b = rubBlob x.b e ∨
     (x.params = [] ∧ x.b.par = [] ∧ x.b.body = [] ∧ (taken x.regs x.b.fin).isSome ∧ x'.b = { x.b with fin := e.2 }))

/-- The epilogue runs when the branch takes a jump. -/
theorem rub_epi {x : Cfg σ Map} {e : List Pole × Termin} (he : rubFin c.blocks x.b.fin = some e)
    (hp : x.params = []) (hq : x.b.par = []) (hb : x.b.body = []) (ht : (taken x.regs x.b.fin).isSome)
    (lab' : Nat) :
    Steps lib O c' gul ⟨lab', rubBlob x.b e, [], x.regs, x.t, x.st⟩ []
      ⟨lab', { x.b with fin := e.2 }, [], x.regs, x.t, x.st⟩ := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at he hp hq hb ht ⊢
  subst hq hb
  rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
  · exact Steps.refl _
  · obtain ⟨e1, e2⟩ := e
    simp only at h2 hf; subst h2
    rcases hf with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨l, r, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
    · exact Steps.refl _
    · exact Steps.refl _
    · simp only [taken, Option.isSome_iff_exists, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
      obtain ⟨_, vl, hl, vr, hr, -⟩ := ht
      have := Steps.step (Step.op (lib := lib) (O := O) (c := c') (gul := gul)
        (x := ⟨lab', rubBlob ⟨[], [], Termin.eqq l r z o⟩ ([Pole.equ l r], Termin.hop ⟨[], z.there⟩), [], regs, t, st⟩)
        (p := Pole.equ l r) (rest := []) (n := A 0) (R := regs) (t' := t) (st' := st)
        rfl rfl rfl (by simp [execPole, localPole, hl, hr])) (Steps.refl _)
      simpa [rubBlob] using this
    · simp only [taken, Option.isSome_iff_exists, Option.bind_eq_some_iff] at ht
      obtain ⟨_, v, hv, hj⟩ := ht
      have hl : v = A 0 ∨ v = A 1 := by
        by_cases h0 : v = A 0
        · exact Or.inl h0
        · by_cases h1 : v = A 1
          · exact Or.inr h1
          · simp [h0, h1] at hj
      have := Steps.step (Step.op (lib := lib) (O := O) (c := c') (gul := gul)
        (x := ⟨lab', rubBlob ⟨[], [], Termin.brn s z o⟩ ([Pole.lob s], Termin.hop ⟨[], z.there⟩), [], regs, t, st⟩)
        (p := Pole.lob s) (rest := []) (n := A 0) (R := regs) (t' := t) (st' := st)
        rfl rfl rfl (by simp [execPole, localPole, hv, hl])) (Steps.refl _)
      simpa [rubBlob] using this


/-- A branch that takes a jump does not end the function. -/
theorem endOf_taken {x : Cfg σ Map} (hp : x.params = []) (hq : x.b.par = []) (hb : x.b.body = [])
    (ht : (taken x.regs x.b.fin).isSome) : endOf lib O gul x = none := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at hp hq hb ht ⊢
  subst hp hq hb
  unfold endOf
  cases fin <;> simp only [taken, Option.isSome_iff_exists] at ht ⊢ <;> try rfl
  all_goals first
    | (obtain ⟨_, h⟩ := ht; simp at h; done)
    | skip
  rename_i r z o
  obtain ⟨j, hj⟩ := ht
  simp only [ne_eq, not_true_eq_false, or_self, if_false]
  simp only [Option.bind_eq_some_iff] at hj
  obtain ⟨v, hv, hj⟩ := hj
  simp only [hv, Option.bind_some]
  by_cases h0 : v = A 0
  · simp [h0]
  · by_cases h1 : v = A 1
    · simp [h1]
    · simp [h0, h1] at hj

/-- At the end of a block whose epilogue has run, a jump of the code before
is matched by one jump of the code after. -/
theorem rub_jump (hbl : RubBlocks c.blocks c'.blocks) {x : Cfg σ Map} {e : List Pole × Termin} {j : Jmp}
    {b2 : Blob} (he : rubFin c.blocks x.b.fin = some e) (hq : x.b.par = []) (hb : x.b.body = [])
    (ht : taken x.regs x.b.fin = some j) (hb2 : HoonMap.get c.blocks j.there = some b2) (lab' : Nat) :
    ∃ es y', Step lib O c' gul ⟨lab', { x.b with fin := e.2 }, [], x.regs, x.t, x.st⟩ es y' ∧
      RubRel c.blocks ⟨j.there, b2, j.args, x.regs, x.t, x.st⟩ y' := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at he hq hb ht hb2 ⊢
  subst hq hb
  rcases rubFin_cases he with rfl | ⟨z, o, nz, hz, ho, hgz, hgo, h2, hf⟩
  · obtain ⟨e2, he2, hg'⟩ := (hbl j.there).2 b2 hb2
    exact ⟨_, _, Step.jump rfl rfl rfl ht hg', rfl, rfl, rfl, rfl, e2, he2, Or.inl rfl⟩
  · have hf' : (∃ s, fin = Termin.clq s z o) ∨ (∃ s, fin = Termin.brz s z o) ∨
        (∃ l r, fin = Termin.eqq l r z o) ∨ (∃ s, fin = Termin.brn s z o) := by
      rcases hf with ⟨s, h, -⟩ | ⟨s, h, -⟩ | ⟨l, r, h, -⟩ | ⟨s, h, -⟩
      · exact Or.inl ⟨s, h⟩
      · exact Or.inr (Or.inl ⟨s, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨l, r, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨s, h⟩))
    have hjz : j.args = [] ∧ b2 = nz := by
      rcases taken_two hf' ht with rfl | rfl
      · rw [hgz] at hb2; exact ⟨hz, (Option.some.inj hb2).symm⟩
      · rw [hgo] at hb2; exact ⟨ho, (Option.some.inj hb2).symm⟩
    obtain ⟨hja, rfl⟩ := hjz
    obtain ⟨e2, he2, hg'⟩ := (hbl z.there).2 b2 hgz
    refine ⟨_, _, Step.jump (j := ⟨[], z.there⟩) rfl rfl rfl (by simp [taken, h2]) hg', ?_⟩
    exact ⟨hja.symm, rfl, rfl, rfl, e2, he2, Or.inl rfl⟩

theorem rubBlob_nil (b : Blob) : rubBlob b ([], b.fin) = b := by
  obtain ⟨par, body, fin⟩ := b; simp [rubBlob]

/-- **Forward**: a step of the code before is matched by steps after. -/
theorem rub_fwd_step (hbl : RubBlocks c.blocks c'.blocks) {x y x' : Cfg σ Map} {es : List (Nat × Nat)}
    (hs : Step lib O c gul x es y) (hr : RubRel c.blocks x x') :
    ∃ es' y', Steps lib O c' gul x' es' y' ∧ RubRel c.blocks y y' := by
  obtain ⟨hp', hr', ht', hst', e, he, hblk⟩ := hr
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  simp only at hp' hr' ht' hst' hblk
  subst hp' hr' ht' hst'
  cases hs with
  | pass hne hR =>
    rcases hblk with rfl | ⟨hp, hq, -⟩
    · exact ⟨_, _, Steps.step (Step.pass (x := ⟨lab', rubBlob _ e, _, _, _, _⟩) hne hR) (Steps.refl _),
        rfl, rfl, rfl, rfl, e, he, Or.inl rfl⟩
    · exact absurd (Or.elim hne (fun h => h hp) (fun h => h hq)) not_false
  | @op p rest n R t2 st2 hp hq hb hpole =>
    rcases hblk with rfl | ⟨-, -, hb', -⟩
    · refine ⟨_, _, Steps.step (Step.op (x := ⟨lab', rubBlob _ e, _, _, _, _⟩) (rest := rest ++ e.1) hp hq
        (by simp [rubBlob, hb]) hpole) (Steps.refl _), rfl, rfl, rfl, rfl, e, he, Or.inl ?_⟩
      simp [rubBlob]
    · rw [hb] at hb'; cases hb'
  | jump hp hq hb ht hb2 =>
    rcases hblk with rfl | ⟨-, -, -, -, rfl⟩
    · obtain ⟨es2, y', hs2, hr2⟩ := rub_jump (lib := lib) (O := O) (gul := gul) hbl he hq hb ht hb2 lab'
      have h1 := rub_epi (lib := lib) (O := O) (c' := c') (gul := gul) he hp hq hb (by simp [ht]) lab'
      rw [hp]
      exact ⟨_, y', steps_trans h1 (Steps.step hs2 (Steps.refl _)), hr2⟩
    · obtain ⟨es2, y', hs2, hr2⟩ := rub_jump (lib := lib) (O := O) (gul := gul) hbl he hq hb ht hb2 lab'
      rw [hp]
      exact ⟨_, y', Steps.step hs2 (Steps.refl _), hr2⟩

/-- **Forward, at an end.** -/
theorem rub_fwd_end {x x' : Cfg σ Map} {r : Tone × σ} (he : endOf lib O gul x = some r)
    (hr : RubRel c.blocks x x') : ∃ es' y', Steps lib O c' gul x' es' y' ∧ endOf lib O gul y' = some r := by
  obtain ⟨hp', hr', ht', hst', e, hef, hblk⟩ := hr
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at hp' hr' ht' hst' hblk hef
  subst params' regs' t' st'
  refine ⟨[], _, Steps.refl _, ?_⟩
  rcases hblk with rfl | ⟨hp, hq, hb, ht, rfl⟩
  · by_cases hpq : params ≠ [] ∨ par ≠ []
    · simp [endOf, hpq] at he
    · cases body with
      | cons p rest =>
        rw [← he]; rfl
      | nil =>
        rcases rubFin_cases hef with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
        · rw [← he]; rfl
        · obtain ⟨e1, e2⟩ := e
          simp only at h2 hf; subst h2
          simp only [not_or, ne_eq, Decidable.not_not] at hpq
          obtain ⟨rfl, rfl⟩ := hpq
          rcases hf with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨l, r0, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
          · simp [endOf] at he
          · simp [endOf] at he
          · simp [endOf] at he
          · simp only [endOf, ne_eq, not_true_eq_false, or_self, if_false, Option.bind_eq_some_iff] at he
            obtain ⟨v, hv, he⟩ := he
            split at he
            · cases he
            · rename_i hl
              cases he
              simp [endOf, rubBlob, execPole, localPole, hv, hl]
  · rw [endOf_taken (x := ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩) hp hq hb ht] at he; cases he


/-- **Backward**: a step of the code after is matched by steps before, given
that the real reads of the configuration before read values. -/
theorem rub_bwd_step (hbl : RubBlocks c.blocks c'.blocks) {x x' y' : Cfg σ Map} {es' : List (Nat × Nat)}
    (hs : Step lib O c' gul x' es' y') (hr : RubRel c.blocks x x')
    (hok : ∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v) :
    ∃ es y, Steps lib O c gul x es y ∧ RubRel c.blocks y y' := by
  obtain ⟨hp', hr', ht', hst', e, he, hblk⟩ := hr
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at hp' hr' ht' hst' hblk he hok
  subst params' regs' t' st'
  cases hs with
  | pass hne hR =>
    rcases hblk with rfl | ⟨hp, hq, -, -, rfl⟩
    · exact ⟨_, _, Steps.step (Step.pass (x := ⟨lab, ⟨par, body, fin⟩, _, _, _, _⟩) hne hR) (Steps.refl _),
        rfl, rfl, rfl, rfl, e, he, Or.inl rfl⟩
    · simp only [hp, hq] at hne; simp at hne
  | @op p rest' n R t2 st2 hp hq hb hpole =>
    rcases hblk with rfl | ⟨-, -, hb0, -, rfl⟩
    · simp only [rubBlob] at hb hq hp
      cases body with
      | cons p0 rest0 =>
        simp only [List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨_, ⟨lab, ⟨par, rest0, fin⟩, params, R, t2, st2⟩,
          Steps.step (Step.op (x := ⟨lab, ⟨par, p0 :: rest0, fin⟩, params, regs, t, st⟩) hp hq rfl hpole)
          (Steps.refl _), rfl, rfl, rfl, rfl, e, he, Or.inl rfl⟩
      | nil =>
        simp only [List.nil_append] at hb
        rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
        · simp at hb
        · obtain ⟨e1, e2⟩ := e
          simp only at h2 hf hb; subst h2
          rcases hf with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨l, r0, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
          · simp at hb
          · simp at hb
          · simp only [List.cons.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
            cases hl : read l regs with
            | none => simp [execPole, localPole, hl] at hpole
            | some vl =>
              cases hr : read r0 regs with
              | none => simp [execPole, localPole, hl, hr] at hpole
              | some vr =>
                simp [execPole, localPole, hl, hr] at hpole
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hpole
                refine ⟨[], ⟨lab, ⟨par, [], _⟩, params, regs, t, st⟩, Steps.refl _, rfl, rfl, rfl, rfl, _, he,
                  Or.inr ⟨hp, hq, rfl, ?_, rfl⟩⟩
                simp [taken, hl, hr]
          · simp only [List.cons.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
            cases hv : read s regs with
            | none => simp [execPole, localPole, hv] at hpole
            | some v =>
              by_cases hl : v = A 0 ∨ v = A 1
              · simp [execPole, localPole, hv, hl] at hpole
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hpole
                refine ⟨[], ⟨lab, ⟨par, [], _⟩, params, regs, t, st⟩, Steps.refl _, rfl, rfl, rfl, rfl, _, he,
                  Or.inr ⟨hp, hq, rfl, ?_, rfl⟩⟩
                rcases hl with rfl | rfl <;> simp [taken, hv]
              · simp [execPole, localPole, hv, hl] at hpole
    · simp only at hb; rw [hb0] at hb; cases hb
  | @jump j' b2' hp hq hb ht' hb2' =>
    simp only at hp hq hb
    subst hp
    have hq0 : par = [] := by
      rcases hblk with h | ⟨-, -, -, -, h⟩ <;> (rw [h] at hq; simpa [rubBlob] using hq)
    have hb0 : body = [] := by
      rcases hblk with h | ⟨-, -, hb0, -, -⟩
      · rw [h] at hb; simp only [rubBlob, List.append_eq_nil_iff] at hb; exact hb.1
      · exact hb0
    subst hq0 hb0
    have hb1 : b' = ⟨[], [], e.2⟩ := by
      rcases hblk with h | ⟨-, -, -, -, h⟩
      · rw [h] at hb ⊢; simp only [rubBlob, List.nil_append] at hb; simp [rubBlob, hb]
      · rw [h]
    subst hb1
    simp only at ht'
    -- the jump the code before takes
    obtain ⟨j, hj⟩ : ∃ j, taken regs fin = some j := by
      rcases hblk with h | ⟨-, -, -, ht, -⟩
      · rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
        · exact ⟨j', by simpa using ht'⟩
        · obtain ⟨e1, e2⟩ := e
          simp only at h2 hf; subst h2
          rcases hf with ⟨s, rfl, -⟩ | ⟨s, rfl, -⟩ | ⟨l, r0, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
          · obtain ⟨v, hv⟩ := hok s ⟨rfl, rfl, Or.inr ⟨rfl, by simp [finReads]⟩⟩
            cases v with
            | atom a => exact ⟨o, by simp [taken, hv]⟩
            | cell a b => exact ⟨z, by simp [taken, hv]⟩
          · obtain ⟨v, hv⟩ := hok s ⟨rfl, rfl, Or.inr ⟨rfl, by simp [finReads]⟩⟩
            exact ⟨if v = A 0 then z else o, by simp [taken, hv]⟩
          · simp [rubBlob] at h
          · simp [rubBlob] at h
      · exact Option.isSome_iff_exists.mp ht
    -- its target is a block
    obtain ⟨b2, hb2⟩ : ∃ b2, HoonMap.get c.blocks j.there = some b2 := by
      rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, hgz, hgo, h2, hf⟩
      · have ht2 : taken regs fin = some j' := by simpa using ht'
        rw [hj] at ht2; cases ht2
        obtain ⟨b2, -, hb2, -, -⟩ := hbl.back hb2'
        exact ⟨b2, hb2⟩
      · have hf' : (∃ s, fin = Termin.clq s z o) ∨ (∃ s, fin = Termin.brz s z o) ∨
            (∃ l r, fin = Termin.eqq l r z o) ∨ (∃ s, fin = Termin.brn s z o) := by
          rcases hf with ⟨s, h, -⟩ | ⟨s, h, -⟩ | ⟨l, r, h, -⟩ | ⟨s, h, -⟩
          · exact Or.inl ⟨s, h⟩
          · exact Or.inr (Or.inl ⟨s, h⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨l, r, h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨s, h⟩))
        rcases taken_two hf' hj with rfl | rfl
        · exact ⟨nz, hgz⟩
        · exact ⟨nz, hgo⟩
    obtain ⟨es2, y2, hs2, hr2⟩ := rub_jump (lib := lib) (O := O) (gul := gul)
      (x := ⟨lab, ⟨[], [], fin⟩, [], regs, t, st⟩) hbl he rfl rfl hj hb2 lab'
    have hstep := Step.jump (lib := lib) (O := O) (c := c') (gul := gul)
      (x := ⟨lab', ⟨[], [], e.2⟩, [], regs, t, st⟩) rfl rfl rfl ht' hb2'
    obtain ⟨-, rfl⟩ := step_det hs2 hstep
    exact ⟨_, ⟨j.there, b2, j.args, regs, t, st⟩,
      Steps.step (Step.jump (x := ⟨lab, ⟨[], [], fin⟩, [], regs, t, st⟩) rfl rfl rfl hj hb2) (Steps.refl _), hr2⟩

/-- **Backward, at an end**: the code before ends where the code after does. -/
theorem rub_bwd_end {x x' : Cfg σ Map} {r : Tone × σ} (he : endOf lib O gul x' = some r)
    (hr : RubRel c.blocks x x') : endOf lib O gul x = some r := by
  obtain ⟨hp', hr', ht', hst', e, hef, hblk⟩ := hr
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at hp' hr' ht' hst' hblk hef
  subst params' regs' t' st'
  rcases hblk with rfl | ⟨hp, hq, hb, ht, rfl⟩
  · by_cases hpq : params ≠ [] ∨ par ≠ []
    · simp [endOf, rubBlob, hpq] at he
    · cases body with
      | cons p rest => rw [← he]; rfl
      | nil =>
        rcases rubFin_cases hef with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
        · rw [← he]; rfl
        · obtain ⟨e1, e2⟩ := e
          simp only at h2 hf; subst h2
          simp only [not_or, ne_eq, Decidable.not_not] at hpq
          obtain ⟨rfl, rfl⟩ := hpq
          rcases hf with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨l, r0, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
          · simp [endOf, rubBlob] at he
          · simp [endOf, rubBlob] at he
          · simp only [endOf, rubBlob, ne_eq, not_true_eq_false, or_self, if_false, List.nil_append] at he
            simp only [execPole, localPole] at he
            cases hl : read l regs <;> cases hr : read r0 regs <;> simp [hl, hr] at he
          · simp only [endOf, rubBlob, ne_eq, not_true_eq_false, or_self, if_false, List.nil_append] at he
            simp only [execPole, localPole] at he
            cases hv : read s regs with
            | none => simp [hv] at he
            | some v =>
              simp only [hv, Option.bind_some] at he
              by_cases hl : v = A 0 ∨ v = A 1
              · simp [hl] at he
              · simp only [hl, if_false] at he
                simp only [Option.map_some, Option.some.injEq] at he
                subst he
                simp only [not_or] at hl
                simp [endOf, hv, hl.1, hl.2]
  · rcases rubFin_cases hef with rfl | ⟨z, o, nz, -, -, -, -, h2, -⟩
    · rw [← he]; rfl
    · subst hp hq hb; simp [endOf, h2] at he

/-- A real read after is a real read before. -/
theorem rub_reads {x x' : Cfg σ Map} {k : Nat} (hr : RubRel c.blocks x x') (hk : ReadsAt gul x' k) :
    ReadsAt gul x k := by
  obtain ⟨hp', hr', ht', hst', e, hef, hblk⟩ := hr
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at hp' hr' ht' hst' hblk hef
  subst params' regs' t' st'
  obtain ⟨hp, hq, hk⟩ := hk
  simp only at hp hq hk
  have hq0 : par = [] := by rcases hblk with rfl | ⟨-, -, -, -, rfl⟩ <;> simpa [rubBlob] using hq
  refine ⟨hp, hq0, ?_⟩
  simp only
  rcases hblk with rfl | ⟨-, -, rfl, -, rfl⟩
  · cases body with
    | cons p0 rest0 =>
      rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, -⟩
      · simp only [rubBlob, List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, -⟩ := hb
        exact Or.inl ⟨p0, rest0, rfl, hk⟩
      · simp [rubBlob] at hb
    | nil =>
      refine Or.inr ⟨rfl, ?_⟩
      rcases rubFin_cases hef with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
      · rcases hk with ⟨p, rest, hb, -⟩ | ⟨-, hk⟩
        · simp [rubBlob] at hb
        · exact hk
      · obtain ⟨e1, e2⟩ := e
        simp only at h2 hf; subst h2
        rcases hk with ⟨p, rest, hb, hk⟩ | ⟨-, hk⟩
        · rcases hf with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨l, r0, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
          · simp [rubBlob] at hb
          · simp [rubBlob] at hb
          · simp only [rubBlob, List.nil_append, List.cons.injEq] at hb
            obtain ⟨rfl, -⟩ := hb
            simpa [poleReads, finReads] using hk
          · simp only [rubBlob, List.nil_append, List.cons.injEq] at hb
            obtain ⟨rfl, -⟩ := hb
            simpa [poleReads, finReads] using hk
        · simp [rubBlob, finReads] at hk
  · rcases hk with ⟨p, rest, hb, -⟩ | ⟨-, hk⟩
    · simp at hb
    · refine Or.inr ⟨rfl, ?_⟩
      rcases rubFin_cases hef with rfl | ⟨z, o, nz, -, -, -, -, h2, -⟩
      · exact hk
      · simp [h2, finReads] at hk


/-- **Forward, on paths.** -/
theorem rub_fwd (hbl : RubBlocks c.blocks c'.blocks) {x y : Cfg σ Map} {es : List (Nat × Nat)}
    (hs : Steps lib O c gul x es y) {r : Tone × σ} (he : endOf lib O gul y = some r) :
    ∀ {x' : Cfg σ Map}, RubRel c.blocks x x' →
      ∃ es' y', Steps lib O c' gul x' es' y' ∧ endOf lib O gul y' = some r := by
  induction hs with
  | refl => intro x' hr; exact rub_fwd_end he hr
  | step s _ ih =>
    intro x' hr
    obtain ⟨es1, y1, hs1, hr1⟩ := rub_fwd_step (lib := lib) (O := O) (gul := gul) hbl s hr
    obtain ⟨es2, y2, hs2, he2⟩ := ih he hr1
    exact ⟨_, y2, steps_trans hs1 hs2, he2⟩

/-- **Backward, on paths**, from a configuration that a path of the code
before reaches, given that every real read on such paths reads a value. -/
theorem rub_bwd (hbl : RubBlocks c.blocks c'.blocks) {x0 : Cfg σ Map}
    (hok : ∀ es y k, Steps lib O c gul x0 es y → ReadsAt gul y k → ∃ v, read k y.regs = some v)
    {x' y' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Steps lib O c' gul x' es' y') :
    ∀ {x : Cfg σ Map} {es : List (Nat × Nat)}, Steps lib O c gul x0 es x → RubRel c.blocks x x' →
      ∃ es2 y, Steps lib O c gul x0 es2 y ∧ RubRel c.blocks y y' := by
  induction hs with
  | refl => intro x es h hr; exact ⟨es, x, h, hr⟩
  | step s _ ih =>
    intro x es h hr
    obtain ⟨es1, y1, hs1, hr1⟩ := rub_bwd_step (lib := lib) (O := O) (gul := gul) hbl s hr
      (fun k hk => hok es x k h hk)
    exact ih (steps_trans h hs1) hr1

end Sim

/-- **`+remove-useless-branching` keeps the code** (`ReadsOK` alone). -/
theorem rub_keepsR [MapKeys Map] (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeUselessBranching c.blocks = some (ch, bl')) : KeepsR c (withBlocks c bl') := by
  have hbl : RubBlocks c.blocks bl' := rub_blocks h
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [withBlocks]
    cases hb : HoonMap.get c.blocks 0 with
    | none => rw [(hbl 0).1 hb]
    | some b =>
      obtain ⟨e, -, hb'⟩ := (hbl 0).2 b hb
      rw [hb']; rfl
  intro lib σ O gul st vals t hok
  have hbl' : RubBlocks c.blocks (withBlocks c bl').blocks := hbl
  cases hb0 : HoonMap.get c.blocks 0 with
  | none =>
    have hn' : HoonMap.get (withBlocks c bl').blocks 0 = none := (hbl 0).1 hb0
    refine ⟨by simp [execEntry, hn', hb0], ?_⟩
    rintro es y k ⟨b0, hb0', -⟩ -
    rw [hn'] at hb0'; cases hb0'
  | some b0 =>
    obtain ⟨e0, he0, hb0'⟩ := (hbl 0).2 b0 hb0
    change HoonMap.get (withBlocks c bl').blocks 0 = some (rubBlob b0 e0) at hb0'
    let x0 : Path.Cfg σ Map := ⟨0, b0, [], regsOf vals, t, st⟩
    let x0' : Path.Cfg σ Map := ⟨0, rubBlob b0 e0, [], regsOf vals, t, st⟩
    have hr0 : RubRel c.blocks x0 x0' := ⟨rfl, rfl, rfl, rfl, e0, he0, Or.inl rfl⟩
    have hok' : ∀ es y k, Steps lib O c gul x0 es y → ReadsAt gul y k → ∃ v, read k y.regs = some v :=
      fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
    -- a path of the code after from its entry is related to a path before
    have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c bl') (gul := gul) st vals t es' y' →
        ∃ es y, Steps lib O c gul x0 es y ∧ RubRel c.blocks y y' := by
      rintro es' y' ⟨b0'', hb0'', hs'⟩
      rw [hb0'] at hb0''; cases hb0''
      exact rub_bwd (c' := withBlocks c bl') hbl' hok' hs' (Steps.refl x0) hr0
    refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, ?_⟩
    · obtain ⟨es', y', hy', he'⟩ := (execEntry_iff_path (c := withBlocks c bl') st vals t r).mp h'
      obtain ⟨es, y, hs, hr⟩ := back es' y' hy'
      exact (execEntry_iff_path (c := c) st vals t r).mpr ⟨es, y, ⟨b0, hb0, hs⟩, rub_bwd_end he' hr⟩
    · obtain ⟨es, y, ⟨b0'', hb0'', hs⟩, he⟩ := (execEntry_iff_path (c := c) st vals t r).mp h'
      rw [hb0] at hb0''; cases hb0''
      obtain ⟨es', y', hs', he'⟩ := rub_fwd (c' := withBlocks c bl') hbl' hs he hr0
      exact (execEntry_iff_path (c := withBlocks c bl') st vals t r).mpr ⟨es', y', ⟨_, hb0', hs'⟩, he'⟩
    · intro es' y' k hy' hk
      obtain ⟨es, y, hs, hr⟩ := back es' y' hy'
      obtain ⟨v, hv⟩ := hok' es y k hs (rub_reads hr hk)
      exact ⟨v, by rw [hr.2.1]; exact hv⟩

end Opt
end SkaModel
end Formalization
