import lemmas.Ska.OptAliasBack
import lemmas.Ska.OptAliasPick

/-!
# `KeepsB` for the model of `+alias`

**`alias_keeps_of`**: under the driver's invariant (`DInvS` of the blocks,
`TopoInvR` of `topo` and `rev`) and a `pick` that picks a member of its list,
the blocks `g.new` of the walk of `+alias` over `topo` keep the code
(`Keeps c (withBlocks c g.new)`).  At the entry the two configurations are
related (`alias_entry`: the same register file, `old` the identity at the
start of the walk, so `AKept` and presence are trivial), in the live mode at
place `0` of block `0`, or in the pending mode when block `0` has parameters
(both stuck).  Then the forward simulation (`alias_fwd`) gives every end of
the code before to the code after, and the backward one (`alias_bwd`, to the
normal form, with `alias_bwd_end`) every end of the code after to the code
before; `alias_reads`, `alias_args`, `alias_local` give `EntryOK` of the code
after.

**`alias_keepsB`**: `KeepsB bl bl'` for `aliasM pick n bl rev topo = some (f, bl')`,
the first conjunct of `AliasFieldSSAB`; **`alias_keepsB_pickR`**: the same
with the choice of the Hoon (`pickR`, the first key of `rap` of the `+silt`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- **Block `0` of the walk**: it is walked from the initial state, not
dropped, and its block after is its parameters, the ops kept from its body
from the start state (whose `old` is the identity) and the end made. -/
theorem alias_zero {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    (ht : TopoOK bl topo) {g : AGen Map} (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) :
    ∃ l g2 b0 st0 rb rf, topo = [] ++ 0 :: l ∧ aliasBlock pick nargs bl (aliasInit rev) 0 = some g2 ∧
      HoonMap.get bl 0 = some b0 ∧ aStart nargs (aliasInit rev) 0 b0 = some st0 ∧ st0.old = id ∧
      aliasBody pick b0.body st0 = some rb ∧
      aliasFin rb.2.old rb.2.loc (aliasInit (Map := Map) rev).rev (aliasInit (Map := Map) rev).folded 0 b0.fin = some rf ∧
      HoonMap.get g.new 0 = some { par := b0.par, body := rb.1, fin := rf.1 } := by
  obtain ⟨hnd, h0, hin, -⟩ := ht
  cases topo with
  | nil => cases h0
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp (hin 0 List.mem_cons_self)
    simp only [aliasWalk] at h
    obtain ⟨g2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st0, rb, rf, hA, hold, hrb, hrf, hg2⟩ :=
      aStart_some (c := ⟨NeedOrd.none, 0, bl⟩) h2 (fun e => e.2 rfl) hb0
    have hl0 : (0 : Nat) ∉ l := (List.nodup_cons.mp hnd).1
    refine ⟨l, g2, b0, st0, rb, rf, rfl, h2, hb0, hA, hold, hrb, hrf, ?_⟩
    rw [((awk_walk l g2 g h3).2 0 hl0).2.2, hg2]
    simp only [HoonMap.get_put, if_true]

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun}

/-- **The two entries are related.** -/
theorem alias_entry {pick : List Nat → Nat} {nargs : Nat} {c : Straight Map} {topo : List Nat}
    {rev : Map (List Nat)} {l : List Nat} {g2 : AGen Map} {b0 : Blob} {st0 : ABody}
    {rb : List Pole × ABody} {rf : Termin × (Nat → List Nat) × Bool}
    (hto : topo = [] ++ 0 :: l) (h2 : aliasBlock pick nargs c.blocks (aliasInit rev) 0 = some g2)
    (hb0 : HoonMap.get c.blocks 0 = some b0) (hA : aStart nargs (aliasInit rev) 0 b0 = some st0)
    (hold : st0.old = id) (hrb : aliasBody pick b0.body st0 = some rb)
    (hrf : aliasFin rb.2.old rb.2.loc (aliasInit (Map := Map) rev).rev (aliasInit (Map := Map) rev).folded 0 b0.fin
      = some rf)
    (S0 : σ) (V0 : List Noun) (T0 : Trace) :
    AliasI pick nargs lib O c gul topo rev S0 V0 T0 ⟨0, b0, [], regsOf V0, T0, S0⟩
      ⟨0, { par := b0.par, body := rb.1, fin := rf.1 }, [], regsOf V0, T0, S0⟩ := by
  refine ⟨[], ⟨b0, hb0, Path.Steps.refl _⟩, rfl, rfl, rfl, ?_⟩
  by_cases hp0 : b0.par = []
  · right; left
    let s : ASplit Map := ⟨[], l, aliasInit rev, g2, b0, st0, 0, [], st0, rb.1, rb.2, rf⟩
    have hok : ASplitOK pick nargs c.blocks topo rev 0 s :=
      ⟨hto, rfl, h2, fun e => e.2 rfl, hb0, hA, Nat.zero_le _, by simp [s, aliasBody],
        by show aliasBody pick (b0.body.drop 0) st0 = some (rb.1, rb.2); rw [List.drop_zero]; exact hrb, hrf⟩
    refine ⟨s, ⟨hok, rfl, blob_par_nil hp0, rfl, ?_, fun i r hi => absurd hi (Nat.not_lt_zero _),
      ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, fun d _ hs => ?_⟩⟩
    · show ({ par := b0.par, body := rb.1, fin := rf.1 } : Blob) = { par := [], body := rb.1, fin := rf.1 }
      rw [hp0]
    · show (HoonMap.get (regsOf V0) (st0.old d)).isSome = true
      rw [hold]; exact hs
  · left
    refine ⟨Or.inr hp0, rfl, fun u hu => absurd hu List.not_mem_nil, id, rfl, fun u hu => absurd hu List.not_mem_nil,
      fun Rp hRp => ?_⟩
    exact absurd (awa_pass_nil hRp).1 hp0

end

/-- **The blocks of the walk of `+alias` keep the code**, under `DInvS`,
`TopoInvR` and a `pick` that picks a member of its list. -/
theorem alias_keeps_of (c : Straight Map) {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {nargs : Nat} (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g) :
    Keeps c (withBlocks c g.new) := by
  obtain ⟨l, g2, b0, st0, rb, rf, hto, h2, hb0, hA, hold, hrb, hrf, hg0⟩ := alias_zero hT.1.1 h
  have hc' : (withBlocks c g.new).blocks = g.new := rfl
  refine ⟨rfl, rfl, ?_, fun lib σ O gul st vals t hE => ?_⟩
  · show (HoonMap.get g.new 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par
    rw [hg0, hb0]; rfl
  have hr0 := alias_entry (lib := lib) (O := O) (gul := gul) hto h2 hb0 hA hold hrb hrf st vals t
  let x0' : Path.Cfg σ Map := ⟨0, { par := b0.par, body := rb.1, fin := rf.1 }, [], regsOf vals, t, st⟩
  have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c g.new) (gul := gul) st vals t es' y' →
      ∃ es y, Path.Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y ∧
        AliasN pick nargs lib O c gul topo rev st vals t y y' := by
    rintro es' y' ⟨b0'', hb0'', hs'⟩
    rw [hc', hg0] at hb0''
    cases hb0''
    exact alias_bwd hpick hD hT h hc' hE hs' hr0
  refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, fun es' y' k hy' hk => ?_,
    fun es' y' k hy' hk => ?_, fun es' y' p rest hy' hp hq hb hsa => ?_⟩
  · obtain ⟨es', y', hy', he'⟩ := (Path.execEntry_iff_path (c := withBlocks c g.new) st vals t r).mp h'
    obtain ⟨es, y, hs, hn⟩ := back es' y' hy'
    exact (Path.execEntry_iff_path (c := c) st vals t r).mpr
      ⟨es, y, ⟨b0, hb0, hs⟩, alias_bwd_end hpick hD hT hE hn he'⟩
  · obtain ⟨es, y, ⟨b0'', hb0'', hs⟩, he⟩ := (Path.execEntry_iff_path (c := c) st vals t r).mp h'
    rw [hb0] at hb0''
    cases hb0''
    obtain ⟨es', z', hs', he'⟩ := alias_fwd hpick hD hT h hc' hE hs he hr0
    exact (Path.execEntry_iff_path (c := withBlocks c g.new) st vals t r).mpr ⟨es', z', ⟨_, hg0, hs'⟩, he'⟩
  · obtain ⟨es, y, -, hn⟩ := back es' y' hy'
    exact alias_reads hpick hD hT hE hn hk
  · obtain ⟨es, y, -, hn⟩ := back es' y' hy'
    exact alias_args hE hn hk
  · obtain ⟨es, y, -, hn⟩ := back es' y' hy'
    exact alias_local hpick hD hT hE hn hp hq hb hsa

/-- **`KeepsB` for the model of `+alias`**: under `DInvS`, `TopoInvR` and a
`pick` that picks a member of its list, the blocks `aliasM` returns keep the
code. -/
theorem alias_keepsB {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    {bl : Map Blob} (hD : DInvS bl) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR bl topo rev)
    {f : Bool} {bl' : Map Blob} (h : aliasM pick nargs bl rev topo = some (f, bl')) : KeepsB bl bl' := by
  unfold aliasM at h
  obtain ⟨g, hg, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  intro c hc
  subst hc
  exact alias_keeps_of c hpick hD hT hg

/-- **`KeepsB` for `+alias` with the choice of the Hoon** (`pickR`, the first
key of `rap` of the `+silt` of the list, on any treap of the analysis). -/
theorem alias_keepsB_pickR (M : Type → Type → Type) [Ana.Treap M] {nargs : Nat} {bl : Map Blob} (hD : DInvS bl)
    {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR bl topo rev) {f : Bool} {bl' : Map Blob}
    (h : aliasM (Ana.pickR M) nargs bl rev topo = some (f, bl')) : KeepsB bl bl' :=
  alias_keepsB (fun l hl => Ana.pickR_mem l hl) hD hT h

end Opt
end SkaModel
end Formalization
