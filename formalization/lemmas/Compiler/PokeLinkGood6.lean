import lemmas.Compiler.PokeLinkTop5
import lemmas.Compiler.PokeLinkCole
import lemmas.Compiler.CompSccOfMissSem

/-!
# `PGood6`: `PGood5` with `ColeDom` (track P, README Gaps 23)

The `ColeCoh` step of `+ska-cole-update` as `PGood5` asks it (`JetsOfCole`:
every jets noun with `ColeCoh` goes to one with `ColeCoh`) is false for the
Hoon: `+cole-put` of a bell that already has a ring leaves it in the old
ring's `back` set (`coleCohM_put_bad`).  The pill never puts such a bell:
`new-code` holds no key of `code`, and every key of `call.cole` is a key of
`code` (`ColeDom`; `%cdom` of `tools/hoon/invdump2.hoon` after each of its
32 mixed pokes).

* `ColeDom`, `PGood6`, `good6_empty`;
* `JetsOfCole6`: the step restated, with `ColeDom` and a table `L'` that
  keeps the keys of `L` (the bells `+ska-cole-update` matches are those of
  `L'` not in `L`), and `ColeDom` kept;
* `bakeGraph_root`, **`anaArmP_root`**: the root bell of a poke is a key of
  the new table (the worklist keeps the root's bake, the final pass gives it
  its variant), so `+scc-of` is called on a key;
* **`good6_full_step`**: the model's `%full` keeps `PGood6`; `good6_mid`;
  both with track Q's `SccOfIsK` (`SccOfIs` is false off a key or without
  `SccsGoodM`, `CompSccOfMissIs.lean`), its side conditions discharged;
* the noun form of `ColeCohM` and of the domain: `getF_toNoun_iff`,
  **`coleCoh_toNoun`**, `coleDom_toNoun` (the maps `call` and `back` laid
  out by `FinMap.toNoun`, a ring a noun).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- **Every key of `call.cole` is a key of `code`.** -/
def ColeDom (j : Noun) (code : FinMap Bell (VarEntry FinMap)) : Prop :=
  ∀ r1 r2 r3 r4 pd ca bk, j = C r1 (C r2 (C r3 (C r4 (C pd (C ca bk))))) →
    ∀ c r, getF mugF c ca = some (C (A 0) r) → ∃ b : Bell, c = TKey.enc b ∧ FinMap.get code b ≠ none

/-- **The invariant**: `PGood5` and `ColeDom`. -/
structure PGood6 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good5 : PGood5 Cls st
  coleDom : ColeDom st.jets st.long.code

theorem good6_empty (Cls : Straight (TreapMap mugF) → Prop) (lib : Lib) : PGood6 Cls emptySt where
  good5 := good5_empty Cls lib
  coleDom := fun r1 r2 r3 r4 pd ca bk h c r hc => by
    simp only [emptySt, jets0, Noun.cell.injEq] at h
    obtain ⟨-, -, -, -, -, rfl, rfl⟩ := h
    simp [getF] at hc

/-- **The `ColeCoh` step of `+ska-cole-update`, restated** (P): from a jets
noun with `ColeCoh` and `ColeDom` at `L`, and a table `L'` keeping the keys of
`L`, `jetsOf` gives one with `ColeCoh` and `ColeDom` at `L'`. -/
def JetsOfCole6 {R : Type} (jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun) : Prop :=
  ∀ hot j reg (L L' : LongB FinMap), ColeCoh j → ColeDom j L.code →
    (∀ b, FinMap.get L.code b ≠ none → FinMap.get L'.code b ≠ none) →
    ColeCoh (jetsOf hot j reg L L') ∧ ColeDom (jetsOf hot j reg L L') L'.code

/-- `addCode` keeps the keys. -/
theorem addCode_keys (code baked : FinMap Bell (VarEntry FinMap)) (b : Bell) (h : FinMap.get code b ≠ none) :
    FinMap.get (addCode code (newCode code baked)) b ≠ none := by
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 h
  rw [(addsTo_addCode code baked).1 b e he]; simp

/-- **The root's variant is baked**: the worklist keeps the root's bake
(`LoopInv.root`) and the final pass gives every bake its variant. -/
theorem bakeGraph_root {E : BEnv FinMap} {n : Nat} {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)}
    (h : bakeGraph E n = some bg) : (Treap.get bg.1 E.root).isSome := by
  unfold bakeGraph at h
  obtain ⟨st, hl, hf⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨qs', hI⟩ := bakeLoop_inv E n _ _ _ _ (loopInv_init E) hl
  obtain ⟨out, vars⟩ := bg
  exact (finalFold_spec E st _ Treap.empty out E.vars vars hf).2.2.1 (E.root, E.root.less)
    ((Treap.mem_rap _ _ _).2 hI.root)

/-- **The root bell of a poke is a key of the new table.** -/
theorem anaArmP_root {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    {s f j hot : Noun} {L : LongB FinMap} {r : Bell × LongB FinMap × Noun × Noun}
    (h : anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s f L j hot = some r) :
    ∃ e, FinMap.get r.2.1.code r.1 = some e := by
  unfold anaArmP at h
  split at h
  · cases h
  · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
    unfold skaPokeB at hr'
    obtain ⟨a, _, hr'⟩ := Option.bind_eq_some_iff.1 hr'
    obtain ⟨bg, hbg, rfl⟩ := Option.map_eq_some_iff.1 hr'
    have hroot := bakeGraph_root hbg
    dsimp only
    rw [← tget_fin, addCode_get]
    split
    · exact ⟨_, rfl⟩
    · exact Option.isSome_iff_exists.1 hroot

section Keep

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}

/-- The jets of a poke the model answers: `ColeCoh` and `ColeDom` at the new
table. -/
theorem cole_poke {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (hJC : JetsOfCole6 jetsOf)
    (st : PSt) (s f : Noun) (hg : PGood6 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r) :
    ColeCoh r.2.2.1 ∧ ColeDom r.2.2.1 r.2.1.code := by
  rw [hA] at e1
  obtain ⟨E, n, bg, reg', -, -, hcode, hjets⟩ := anaArmP_bake e1
  rw [hjets]
  refine hJC _ _ _ _ _ hg.good5.cole hg.coleDom fun b hb => ?_
  rw [hcode]; exact addCode_keys _ _ b hb

/-- **The model's `%full` keeps `PGood6`.** -/
theorem good6_full_step {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps Ar Cls)
    (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood6 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood6 Cls st' := by
  have hg3 := good3_full_step hK hU (skaCodeKeeps_of_armP Ar hA) hO hC st s f pr st' hg.good5.good4.good3 h
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hcole, hdom⟩ := cole_poke hA hJC st s f hg r e1
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, -⟩ := anaArmP_bake e1'
  obtain ⟨lib, hInv⟩ := hg.good5.invB
  have hInv' : InvB lib r.2.1 := ((anaHyp_of_armP (lib := lib) Ar hA).ana s f st.long st.jets st.hot r e1 hInv).1
  have hc := hg.good5.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good5.good4.good3.vars
  have hi := hg.good5.good4.info
  obtain ⟨F, hF, hFt⟩ := hg.good5.good4.flags
  obtain ⟨L, hL⟩ := hTE (newCode st.long.code bg.1)
  obtain ⟨G, hG⟩ := loopTotal_poke hc hv hi hbg hFt hInv' hcode L hL
  obtain ⟨hi', hG1, hG2⟩ := flags_poke hc hv hi hbg hL hF hFt hG
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.good5.sccsIs
    hg.good5.good4.good3.good2.cache.sccs
  rw [← hcode] at hi' hG1 hG2 hc' hsc
  have key : ∀ st'' : PSt, st''.long = r.2.1 → st''.jets = r.2.2.1 → SccsIs r.2.1.code st''.cache.sccs →
      PGood3 Cls st'' → PGood6 Cls st'' := fun st'' hl hj hs h3 =>
    ⟨⟨⟨h3, hl ▸ hi', ⟨G, hl ▸ hG1, hl ▸ hG2⟩⟩, ⟨lib, hl ▸ hInv'⟩, hl ▸ hs, hj ▸ hcole⟩, hj ▸ hl ▸ hdom⟩
  split at h
  · cases h
    exact key _ rfl rfl hsc hg3
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, e3, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    simp only [if_true] at hp'
    have hsq : SccsIs r.2.1.code q.2 :=
      hSI _ _ _ q hc' hsc hg.good5.good4.good3.good2.cache.sccs (anaArmP_root e1') e3
    refine key _ rfl rfl ?_ hg3
    unfold compiledMono at hp'
    split at hp'
    · cases hp'; exact hsq
    · obtain ⟨r', hr', e⟩ := Option.map_eq_some_iff.1 hp'
      cases e
      exact hUS { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 r'
        hc' hsq hr'

/-- **`PGood6` at the state `+compiled-mono` runs on.** -/
theorem good6_mid {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hO : SccOfKeeps Ar) (hSI : SccOfIsK Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (st : PSt) (s f : Noun) (hg : PGood6 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r)
    (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) (e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs = some q) :
    PGood6 Cls { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } := by
  have hg3 := good3_mid hK (skaCodeKeeps_of_armP Ar hA) hO st s f hg.good5.good4.good3 r e1 q e3
  obtain ⟨hcole, hdom⟩ := cole_poke hA hJC st s f hg r e1
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, -⟩ := anaArmP_bake e1'
  obtain ⟨lib, hInv⟩ := hg.good5.invB
  have hInv' : InvB lib r.2.1 := ((anaHyp_of_armP (lib := lib) Ar hA).ana s f st.long st.jets st.hot r e1 hInv).1
  have hc := hg.good5.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good5.good4.good3.vars
  have hi := hg.good5.good4.info
  obtain ⟨F, hF, hFt⟩ := hg.good5.good4.flags
  obtain ⟨L, hL⟩ := hTE (newCode st.long.code bg.1)
  obtain ⟨G, hG⟩ := loopTotal_poke hc hv hi hbg hFt hInv' hcode L hL
  obtain ⟨hi', hG1, hG2⟩ := flags_poke hc hv hi hbg hL hF hFt hG
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.good5.sccsIs
    hg.good5.good4.good3.good2.cache.sccs
  rw [← hcode] at hi' hG1 hG2 hc' hsc
  exact ⟨⟨⟨hg3, hi', ⟨G, hG1, hG2⟩⟩, ⟨lib, hInv'⟩,
    hSI _ _ _ q hc' hsc hg.good5.good4.good3.good2.cache.sccs (anaArmP_root e1') e3, hcole⟩, hdom⟩

end Keep

/-! ## The noun form of `ColeCohM` -/

section Noun

variable {κ ν : Type} [DecidableEq κ] [TKey κ]

/-- `+get:by` on the noun of a map. -/
theorem getF_toNoun_iff (f : ν → Noun) (m : FinMap κ ν) (k S : Noun) :
    getF mugF k (m.toNoun f) = some (C (A 0) S) ↔ ∃ b x, m.1 b = some x ∧ k = TKey.enc b ∧ S = f x := by
  constructor
  · intro h
    by_cases hg : ∃ v, Get (m.toNoun f) k v
    · obtain ⟨v, hv⟩ := hg
      rw [getF_some (isMap_toNoun f m) hv] at h
      simp only [Option.some.injEq, Noun.cell.injEq, true_and] at h
      subst h
      exact (get_toNoun f m k v).1 hv
    · rw [getF_none (isMap_toNoun f m) (fun v hv => hg ⟨v, hv⟩)] at h
      cases h
  · intro h
    exact getF_some (isMap_toNoun f m) ((get_toNoun f m k S).2 h)

/-- **`ColeCoh` of the jets noun whose `call` and `back` are the nouns of a
coherent `ColeM`** (a ring is a noun, `back` a jug: a map to sets). -/
theorem coleCoh_toNoun (c : ColeM Bell Noun) (h : ColeCohM c) (r1 r2 r3 r4 pd : Noun) :
    ColeCoh (C r1 (C r2 (C r3 (C r4 (C pd (C (c.call.toNoun fun x => x) (c.back.toNoun FinMap.setNoun))))))) := by
  intro a1 a2 a3 a4 apd ca bk he cn r
  simp only [Noun.cell.injEq] at he
  obtain ⟨-, -, -, -, -, rfl, rfl⟩ := he
  rw [getF_toNoun_iff]
  constructor
  · rintro ⟨b, x, hb, rfl, hx⟩
    rw [show r = x from hx]
    obtain ⟨S, hS, hSb⟩ := (h b x).1 hb
    exact ⟨_, (getF_toNoun_iff _ _ _ _).2 ⟨x, S, hS, rfl, rfl⟩, (has_setNoun S _).2 ⟨b, hSb, rfl⟩⟩
  · rintro ⟨Sn, hS, hh⟩
    obtain ⟨r', S, hS', hr', rfl⟩ := (getF_toNoun_iff _ _ _ _).1 hS
    rw [show r = r' from hr']
    obtain ⟨b, hb, rfl⟩ := (has_setNoun S _).1 hh
    exact ⟨b, r', (h b r').2 ⟨S, hS', hb⟩, rfl, rfl⟩

/-- **`ColeDom` of the jets noun whose `call` is the noun of a map with keys
in `code`.** -/
theorem coleDom_toNoun (call : FinMap Bell Noun) (code : FinMap Bell (VarEntry FinMap))
    (h : ∀ b r, call.get b = some r → FinMap.get code b ≠ none) (r1 r2 r3 r4 pd bk : Noun) :
    ColeDom (C r1 (C r2 (C r3 (C r4 (C pd (C (call.toNoun fun x => x) bk)))))) code := by
  intro a1 a2 a3 a4 apd ca bk' he cn r hc
  simp only [Noun.cell.injEq] at he
  obtain ⟨-, -, -, -, -, rfl, rfl⟩ := he
  obtain ⟨b, x, hb, rfl, -⟩ := (getF_toNoun_iff _ _ _ _).1 hc
  exact ⟨b, rfl, h b x hb⟩

end Noun

end Compiler
end Formalization
