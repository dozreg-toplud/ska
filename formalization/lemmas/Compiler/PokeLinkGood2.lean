import lemmas.Compiler.PokeLinkGood

/-!
# `PGood2`: `PGood` with the closure of the table and the cache clauses

P1 (README Gaps 23) needs the table closed (`CodeClosed`: every callee in
`calls` and every `%2` info bell of an entry is a key of `code`), so that
the replay of the SCC loop gives old bells the same flags when the table
grows.  Track K's bridge to `MonoLinkGood` (`PGoodK`, README Gaps 19 (g))
asks for the cache clauses: `sure.cache` and `inl.cache` are maps, `sure`
has the keys of `nary`, `inl` holds nomms of keys of `code`, `sccs` is
`SccsGood` and `nary` is closed under whole SCCs.  Track K's own names
(`SccsGood`, `NaryClosed`, `RInl`) are on its branch, on nouns; these are
the same clauses on the model's values, under new names.

*Checked* (`tools/hoon/invdump.hoon`, output `invdump.txt`): after each of
the 21 `%full` pokes of `sprestdump.hoon`, every clause holds, and
`inl.cache` holds exactly `+inlined` of its bell on the state with
`inl.cache` emptied (a function of the table: track K's `inl`).
*Proved*: `good2_empty` (all clauses at the start, so at `cor`).
*Open*: that `%full` keeps each clause (checked only), and that `%jets`
(`+del-bells`, `+hot-stale`) and `%fast` keep them (not checked).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- The bells of the `%2` infos of a nomm (the callees `+eval-finalized`
reads the flags of). -/
def nommInfos : Nomm → List Bell
  | .cons p q => nommInfos p ++ nommInfos q
  | .n0 _ => []
  | .n1 _ => []
  | .n2 p q info => nommInfos p ++ nommInfos q ++ (match info with | some i => [i.1] | none => [])
  | .n3 p => nommInfos p
  | .n4 p => nommInfos p
  | .n5 p q => nommInfos p ++ nommInfos q
  | .n6 p q r => nommInfos p ++ nommInfos q ++ nommInfos r
  | .n7 p q => nommInfos p ++ nommInfos q
  | .n10 _ v q => nommInfos v ++ nommInfos q
  | .n11s _ q _ => nommInfos q
  | .n11d _ h q _ => nommInfos h ++ nommInfos q
  | .n12 p q => nommInfos p ++ nommInfos q
  | .mean p _ q _ _ => nommInfos p ++ nommInfos q

/-- **The table is closed**: every callee in `calls` and every `%2` info
bell of an entry is a key. -/
def CodeClosed (code : FinMap Bell (VarEntry FinMap)) : Prop :=
  ∀ b e, FinMap.get code b = some e →
    (∀ c, FinMap.get e.calls c = some () → ∃ e', FinMap.get code c = some e') ∧
    (∀ c ∈ nommInfos e.nomm, ∃ e', FinMap.get code c = some e')

/-- `sccs.cache` is `SccsGood`: an SCC holds its bell, and each member has it. -/
def SccsGoodM (sccs : FinMap Bell (FinMap Bell Unit)) : Prop :=
  ∀ k S, FinMap.get sccs k = some S → FinMap.get S k = some () ∧
    ∀ k', FinMap.get S k' = some () → FinMap.get sccs k' = some S

/-- `nary.cache` is closed under whole SCCs of `sccs.cache`. -/
def NaryClosedM (nary : FinMap Bell (Straight (TreapMap mugF))) (sccs : FinMap Bell (FinMap Bell Unit)) : Prop :=
  ∀ k s, FinMap.get nary k = some s → ∃ S, FinMap.get sccs k = some S ∧
    ∀ k', FinMap.get S k' = some () → ∃ s', FinMap.get nary k' = some s'

/-- **The cache clauses**: `inl` and `sure` (raw nouns of the model) are
maps; the keys of `sure` are those of `nary`; `inl` holds nomms of keys of
`code`; `sccs` and `nary` as above. -/
structure CacheGood (code : FinMap Bell (VarEntry FinMap)) (c : Cache FinMap (TreapMap mugF) (Noun × Noun)) :
    Prop where
  sureMap : IsMap mugF c.rest.2
  sureKeys : ∀ kn, (∃ v, Get c.rest.2 kn v) ↔ ∃ (b : Bell) (s : Straight (TreapMap mugF)),
    kn = b.toNoun ∧ FinMap.get c.nary b = some s
  inlMap : IsMap mugF c.rest.1
  inlKeys : ∀ kn v, Get c.rest.1 kn v → ∃ (b : Bell) (e : VarEntry FinMap) (nm : Nomm),
    kn = b.toNoun ∧ FinMap.get code b = some e ∧ v = nm.toNoun
  sccs : SccsGoodM c.sccs
  nary : NaryClosedM c.nary c.sccs

/-- **`PGood2`**: `PGood`, the closed table, the cache clauses. -/
structure PGood2 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good : PGood Cls st
  closed : CodeClosed st.long.code
  cache : CacheGood st.long.code st.cache

/-- **`PGood2` at the start** (so at `cor`, `cor_enc`). -/
theorem good2_empty (Cls : Straight (TreapMap mugF) → Prop) : PGood2 Cls emptySt where
  good := good_empty Cls
  closed := fun b e h => by
    have : FinMap.get (Treap.empty : FinMap Bell (VarEntry FinMap)) b = none := rfl
    exact absurd (this.symm.trans h) (by simp)
  cache :=
    { sureMap := IsMap.nil
      sureKeys := fun kn => by
        constructor
        · rintro ⟨v, hv⟩; exact absurd hv Get_atom
        · rintro ⟨b, s, -, h⟩
          have : FinMap.get (Treap.empty : FinMap Bell (Straight (TreapMap mugF))) b = none := rfl
          exact absurd (this.symm.trans h) (by simp)
      inlMap := IsMap.nil
      inlKeys := fun kn v hv => absurd hv Get_atom
      sccs := fun k S h => by
        have : FinMap.get (Treap.empty : FinMap Bell (FinMap Bell Unit)) k = none := rfl
        exact absurd (this.symm.trans h) (by simp)
      nary := fun k s h => by
        have : FinMap.get (Treap.empty : FinMap Bell (Straight (TreapMap mugF))) k = none := rfl
        exact absurd (this.symm.trans h) (by simp) }

end Compiler
end Formalization
