import lemmas.Compiler.CompSccOfHeightS

/-!
# The "lower" of `MemCallOk` from a ranked condensation (README Gaps 19 (g))

`MemCallOk` (the static facts of one call of a member run) asks, of a call `b` outside the
member's SCC `S`, that `b` is in the domain `D` of the table and lower than the SCC in
progress.  Here both come from state facts:

* `HtRank SC0 CALLS ht`: **the height clause asked of tracks P/Q**, on the nouns of the state: a
  callee `k'` of `k` (`CalleeIn CALLS`) outside `k`'s SCC is lower;
* `InSccs SC0`: the domain, the bells with an entry in `sccs.cache`;
* **`memCall_side`**: a call of a member is inside `S` (`hasInF` `&`) or outside it, in `InSccs`,
  and lower than the member;
* **`memCallOk_of_rank`**: `MemCallOk` at `D := InSccs SC0` and `h := ht m` from `memCallOk_of`,
  `HtRank`, `CalleeIn CALLS m b` (the member's `calls` entry holds the call) and `InSccs SC0 b`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The height clause** (asked of tracks P/Q): a callee `k'` of `k` outside the SCC `S` of `k`
in `sccs.cache` is lower than `k`. -/
def HtRank (SC0 CALLS : Noun) (ht : Noun → Nat) : Prop :=
  ∀ k k' S, getF mugF k SC0 = some (C (A 0) S) → CalleeIn CALLS k k' → k' ∉ tapList S → ht k' < ht k

/-- **The domain of the table**: the bells with an entry in `sccs.cache`. -/
def InSccs (SC0 : Noun) (b : Bell) : Prop := ∃ S, getF mugF b.toNoun SC0 = some (C (A 0) S)

/-- **The side of a call of a member `m` of `S`**: inside `S`, or outside it, in the domain and
lower than `m`. -/
theorem memCall_side {SC0 CALLS S m : Noun} {ht : Noun → Nat} {b : Bell}
    (hsg : SccsGood SC0) (hr : HtRank SC0 CALLS ht)
    (hm : getF mugF m SC0 = some (C (A 0) S)) (hc : CalleeIn CALLS m b.toNoun) (hkey : InSccs SC0 b) :
    (hasInF mugF b.toNoun S = some true ∧ b.toNoun ∈ tapList S) ∨
      (hasInF mugF b.toNoun S = some false ∧ b.toNoun ∉ tapList S ∧ InSccs SC0 b ∧ ht b.toNoun < ht m) := by
  obtain ⟨hSs, -, -⟩ := hsg _ _ hm
  obtain ⟨t, ht', hiff⟩ := hasInF_spec mugF S b.toNoun hSs
  by_cases hb : b.toNoun ∈ tapList S
  · left
    have e : t = true := hiff.2 ((mem_tapList_set hSs _).1 hb)
    subst e
    exact ⟨ht', hb⟩
  · right
    have e : t = false := by
      cases t
      · rfl
      · exact absurd ((mem_tapList_set hSs _).2 (hiff.1 rfl)) hb
    subst e
    exact ⟨ht', hb, hkey, hr _ _ _ hm hc hb⟩

/-- **`MemCallOk` with the domain `InSccs` and the height of the member** (`memCallOk_of` with
`memCall_side`): the call `b` of the member `m` of the loop's SCC `S` is in `m`'s `calls` entry
and has an entry in `sccs.cache`; an outside callee has a need in the loop's `r.env`. -/
theorem memCallOk_of_rank {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd}
    {CODE JETS CALLS JH SC0 S ML TOP B COLE m : Noun} {ht : Noun → Nat}
    {ms : Option Nomm} {p q : Nomm} {b : Bell}
    (he : EnvFrom r.env CODE COLE) (hcl : slot? 190 (C JETS CALLS) = some COLE)
    {c : Bool} (hc : codeOf CODE b = some c) (hr : getF mugF b.toNoun COLE = some (A 0))
    (hs : ∀ nb, (envDone r order kids st).need b = some nb →
      (envDone r order kids st).sof (made p ms) p q b nb = false ∧
        ∀ x, SofRetN (envDone r order kids st) ms (memDCtx S (C CODE (C JETS CALLS)) JH ML TOP B) p q b nb x)
    (hrs : r.scc = tapList S) (hsg : SccsGood SC0) (hR : HtRank SC0 CALLS ht)
    (hm : getF mugF m SC0 = some (C (A 0) S)) (hcall : CalleeIn CALLS m b.toNoun) (hkey : InSccs SC0 b)
    (hneed : b.toNoun ∉ tapList S → ∃ nb, r.env.need b = some nb) :
    MemCallOk r order kids st CODE (memDCtx S (C CODE (C JETS CALLS)) JH ML TOP B) S ht (InSccs SC0) (ht m) ms p q b := by
  refine memCallOk_of he hcl hc hr hs ?_
  rcases memCall_side hsg hR hm hcall hkey with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, hrs ▸ h2⟩
  · exact Or.inr ⟨h1, hrs ▸ h2, h3, h4, hneed h2⟩

/-- **The height of the SCC in progress is the member's** (`HtScc`): what `MemDoneRestS` asks
at `h := ht b0` for a member `m` of the SCC of `b0`. -/
theorem ht_member {SC0 S k m : Noun} {ht : Noun → Nat} (hsg : SccsGood SC0) (hht : HtScc SC0 ht)
    (hk : getF mugF k SC0 = some (C (A 0) S)) (hmS : m ∈ tapList S) :
    getF mugF m SC0 = some (C (A 0) S) ∧ ht m = ht k :=
  ⟨((hsg _ _ hk).2.2 m hmS).1, hht _ _ hk m hmS⟩

end Compiler
end Formalization
