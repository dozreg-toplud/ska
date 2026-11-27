import lemmas.Compiler.PokeLinkLoopTotal
import lemmas.Compiler.CompSccOfRank
import lemmas.Compiler.PokeLinkGoodK

/-!
# `PGood5`: the invariant other tracks ask for (track P, README Gaps 23)

`PGood5` = `PGood4` + `InvB` of `long` (the analysis invariant, kept by
`skaPokeB_sound` with no hypothesis; it gives `LoopTotal`) + `SccsIs` (every
`sccs.cache` entry of `b` is the SCC `sccSet code b`) + `ColeCoh` (`call.cole`
maps `c` to `r` iff `c` is in `back.cole` of `r`).  All three new clauses hold
after each of the 32 mixed pokes of `tools/hoon/invdump2.hoon` (`%sset`,
`%ccoh`; the `%flag` replay and `InvB` were checked before).

* `htRank_of`: track K's `HtRank` and `HtScc` (`CompSccOfRank.lean`) on the
  nouns of `sccs.cache` and `calls`, with the height `reachCnt` of the table,
  from `SccsIs` and `CodeClosed`.
* `good5_empty`.
* `sccsIs_addCode`: old entries stay SCCs of the grown table.
* **`good5_full_step`**: the model's `%full` keeps `PGood5`, from the
  hypotheses of `good3_full_step` and `SccOfIs` (P: `+scc-of`'s miss writes
  whole SCCs), `UnarySccsIs` (K: `+compile-unary`'s `+scc-of`s likewise),
  `TarjanExists` (P: a callees-first list of SCCs exists) and `JetsOfCole`
  (P: `+ska-cole-update` keeps `ColeCoh`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- **The height clause**: every entry of `sccs.cache` is its bell's SCC. -/
def SccsIs (code : FinMap Bell (VarEntry FinMap)) (sc : FinMap Bell (FinMap Bell Unit)) : Prop :=
  ∀ b S, FinMap.get sc b = some S → S = sccSet code b

/-- **`call.cole` and `back.cole` agree** (`+cole-put` writes both). -/
def ColeCoh (j : Noun) : Prop :=
  ∀ r1 r2 r3 r4 pd ca bk, j = C r1 (C r2 (C r3 (C r4 (C pd (C ca bk))))) →
    ∀ c r, getF mugF c ca = some (C (A 0) r) ↔ ∃ S, getF mugF r bk = some (C (A 0) S) ∧ Has S c

/-- **The invariant other tracks ask for.** -/
structure PGood5 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good4 : PGood4 Cls st
  invB : ∃ lib, InvB lib st.long
  sccsIs : SccsIs st.long.code st.cache.sccs
  cole : ColeCoh st.jets

/-! ## The height for track K -/

open Classical in
/-- The height of a bell noun: how many keys of `l` it reaches. -/
noncomputable def htOf (T : FinMap Bell (VarEntry FinMap)) (l : List Bell) : Noun → Nat := fun k =>
  if h : ∃ b : Bell, TKey.enc b = k then reachCnt T l (Classical.choose h) else 0

theorem htOf_enc (T : FinMap Bell (VarEntry FinMap)) (l : List Bell) (b : Bell) :
    htOf T l (TKey.enc b) = reachCnt T l b := by
  have h : ∃ b' : Bell, TKey.enc b' = TKey.enc b := ⟨b, rfl⟩
  unfold htOf
  rw [dif_pos h, TKey.enc_inj _ _ (Classical.choose_spec h)]

theorem sccSet_get {T : FinMap Bell (VarEntry FinMap)} {b c : Bell} :
    (sccSet T b).1 c = some () ↔ InScc T b c := by
  unfold sccSet
  by_cases h : InScc T b c <;> simp [h]

/-- **`HtRank` and `HtScc` of track K from `SccsIs`**: the height is
`reachCnt` over the keys, constant on an SCC and lower across an edge out of
it. -/
theorem htRank_of {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)}
    (hc : CodeClosed L.code) (hs : SccsIs L.code sc) :
    ∃ ht, HtRank (sccsNoun sc) (callsNoun L) ht ∧ HtScc (sccsNoun sc) ht := by
  generalize hcd : L.code = code at hc hs
  have hcn : callsNoun L = code.toNoun fun e => FinMap.setNoun e.calls := by rw [← hcd]; rfl
  rw [hcn]
  obtain ⟨l, hl⟩ := code.2
  refine ⟨htOf code l, ?_, ?_⟩
  · intro k k' S hk hcall hn
    obtain ⟨b, S', hb, rfl, rfl⟩ := getF_toNoun_some FinMap.setNoun sc k S hk
    obtain ⟨v, hv, hh⟩ := hcall
    obtain ⟨b2, e, he, hbe, rfl⟩ := (get_toNoun _ _ _ v).1 hv
    have hb2 : b2 = b := TKey.enc_inj _ _ hbe.symm
    subst hb2
    obtain ⟨c, hcc, rfl⟩ := (has_setNoun e.calls k').1 hh
    obtain ⟨ec, hec⟩ := (hc b2 e he).1 c hcc
    have hedge : Edge code b2 c := ⟨e, he, hcc, ec, hec⟩
    have hR : Reach code b2 c := Reach.step hedge (Reach.refl c)
    have hS := hs b2 S' hb
    subst hS
    have hnot : ¬ Reach code c b2 := by
      intro h'
      apply hn
      rw [mem_tapList_set (isSet_setNoun _)]
      exact (has_setNoun _ _).2 ⟨c, sccSet_get.2 ⟨⟨ec, hec⟩, hR, h'⟩, rfl⟩
    rw [htOf_enc, htOf_enc]
    exact reachCnt_lt l hR hnot (hl b2 (by rw [show code.1 b2 = some e from he]; simp))
  · intro k S hk k' hk'
    obtain ⟨b, S', hb, rfl, rfl⟩ := getF_toNoun_some FinMap.setNoun sc k S hk
    have hS := hs b S' hb
    subst hS
    obtain ⟨c, hcs, rfl⟩ := (has_setNoun _ _).1 ((mem_tapList_set (isSet_setNoun _) _).1 hk')
    obtain ⟨-, r1, r2⟩ := sccSet_get.1 hcs
    rw [htOf_enc, htOf_enc]
    exact Nat.le_antisymm (reachCnt_le l r1) (reachCnt_le l r2)

/-! ## The empty state -/

theorem good5_empty (Cls : Straight (TreapMap mugF) → Prop) (lib : Lib) : PGood5 Cls emptySt where
  good4 := good4_empty Cls
  invB := ⟨lib, InvB.init lib⟩
  sccsIs := fun b S h => by simp [emptySt, FinMap.get, Treap.empty, FinMap.empty] at h
  cole := fun r1 r2 r3 r4 pd ca bk h c r => by
    simp only [emptySt, jets0, Noun.cell.injEq] at h
    obtain ⟨-, -, -, -, -, rfl, rfl⟩ := h
    simp [getF]

/-! ## `%full` -/

/-- An entry of `sccs` that is its bell's SCC under `SccsGoodM` is at a key. -/
theorem sccsIs_key {code : FinMap Bell (VarEntry FinMap)} {sc : FinMap Bell (FinMap Bell Unit)}
    (hs : SccsIs code sc) (hg : SccsGoodM sc) {b : Bell} {S : FinMap Bell Unit} (hb : FinMap.get sc b = some S) :
    FinMap.get code b ≠ none := by
  have h1 := (hg b S hb).1
  rw [hs b S hb] at h1
  obtain ⟨⟨e, he⟩, -⟩ := sccSet_get.1 h1
  rw [he]; simp

/-- **Old `sccs` entries stay SCCs** of the table a bake grows. -/
theorem sccsIs_addCode {code nc T' : FinMap Bell (VarEntry FinMap)} {sc : FinMap Bell (FinMap Bell Unit)}
    (hA : AddsTo code nc T') (hc : CodeClosed code) (hs : SccsIs code sc) (hg : SccsGoodM sc) : SccsIs T' sc := by
  intro b S hb
  rw [hs b S hb]
  exact sccSet_congr fun x => (inScc_old hA hc (sccsIs_key hs hg hb) x).symm

section Keep

variable (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (Cls : Straight (TreapMap mugF) → Prop)

/-- **`+scc-of` writes whole SCCs** (P: a pill fact on `sccOfP`, the miss
puts `+tarjan`'s SCCs; `%sset` of `invdump2.hoon`). -/
def SccOfIs : Prop :=
  ∀ b L sc q, CodeClosed L.code → SccsIs L.code sc → Ar.sccOf b L sc = some q → SccsIs L.code q.2

/-- **`+compile-unary` keeps `SccsIs`** (K: its `+scc-of`s of callees). -/
def UnarySccsIs : Prop :=
  ∀ (st : PSt) b scc r, CodeClosed st.long.code → SccsIs st.long.code st.cache.sccs →
    Ar.compileUnary b scc st.long st.jets st.hot st.cache = some r → SccsIs st.long.code r.2.sccs

/-- **A callees-first list of the SCCs of a table exists** (P: graph theory;
`+tarjan` returns one, `SccsLeafAt` of track Q). -/
def TarjanExists : Prop := ∀ nc : FinMap Bell (VarEntry FinMap), ∃ L, TarjanSpec nc L

/-- **`+ska-cole-update` keeps `ColeCoh`** (P, with `JetsOfGood`). -/
def JetsOfCole (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) : Prop :=
  ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L')

variable {Ar Cls}

/-- What `anaArmP` returns: the bake and the grown table. -/
theorem anaArmP_bake {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    {s f j hot : Noun} {L : LongB FinMap} {r : Bell × LongB FinMap × Noun × Noun}
    (h : anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s f L j hot = some r) :
    ∃ (E : BEnv FinMap) (n : Nat) (bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)) (reg' : R),
      bakeGraph E n = some bg ∧ E.vars = L.vars ∧ r.2.1.code = addCode L.code (newCode L.code bg.1) ∧
      r.2.2.1 = jetsOf hot j reg' L r.2.1 := by
  unfold anaArmP at h
  split at h
  · cases h
  · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
    unfold skaPokeB at hr'
    obtain ⟨a, _, hr'⟩ := Option.bind_eq_some_iff.1 hr'
    obtain ⟨bg, hbg, rfl⟩ := Option.map_eq_some_iff.1 hr'
    exact ⟨_, _, bg, _, hbg, rfl, rfl, rfl⟩

/-- **The model's `%full` keeps `PGood5`.** -/
theorem good5_full_step {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps Ar Cls)
    (hSI : SccOfIs Ar) (hUS : UnarySccsIs Ar) (hTE : TarjanExists)
    (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood5 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood5 Cls st' := by
  have hg3 := good3_full_step hK hU (skaCodeKeeps_of_armP Ar hA) hO hC st s f pr st' hg.good4.good3 h
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, hjets⟩ := anaArmP_bake e1'
  obtain ⟨lib, hInv⟩ := hg.invB
  have hInv' : InvB lib r.2.1 := ((anaHyp_of_armP (lib := lib) Ar hA).ana s f st.long st.jets st.hot r e1 hInv).1
  have hc := hg.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good4.good3.vars
  have hi := hg.good4.info
  obtain ⟨F, hF, hFt⟩ := hg.good4.flags
  obtain ⟨L, hL⟩ := hTE (newCode st.long.code bg.1)
  obtain ⟨G, hG⟩ := loopTotal_poke hc hv hi hbg hFt hInv' hcode L hL
  obtain ⟨hi', hG1, hG2⟩ := flags_poke hc hv hi hbg hL hF hFt hG
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.sccsIs hg.good4.good3.good2.cache.sccs
  rw [← hcode] at hi' hG1 hG2 hc' hsc
  have hcole : ColeCoh r.2.2.1 := by rw [hjets]; exact hJC _ _ _ _ _ hg.cole
  -- the state after the poke: `long` and `jets` from `r`, the cache by branch
  have key : ∀ st'' : PSt, st''.long = r.2.1 → st''.jets = r.2.2.1 → SccsIs r.2.1.code st''.cache.sccs →
      PGood3 Cls st'' → PGood5 Cls st'' := fun st'' hl hj hs h3 =>
    ⟨⟨h3, hl ▸ hi', ⟨G, hl ▸ hG1, hl ▸ hG2⟩⟩, ⟨lib, hl ▸ hInv'⟩, hl ▸ hs, hj ▸ hcole⟩
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
    have hsq : SccsIs r.2.1.code q.2 := hSI _ _ _ q hc' hsc e3
    refine key _ rfl rfl ?_ hg3
    unfold compiledMono at hp'
    split at hp'
    · cases hp'; exact hsq
    · obtain ⟨r', hr', e⟩ := Option.map_eq_some_iff.1 hp'
      cases e
      exact hUS { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 r'
        hc' hsq hr'

end Keep

end Compiler
end Formalization
