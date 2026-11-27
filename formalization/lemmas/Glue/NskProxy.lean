import lemmas.Glue.ProxCalls
import lemmas.Glue.SplitDefBase

/-!
# Toward `NskEndC`: the weaker body invariant and the step that adds keys (track G)

With a direct call `SDBody` fails (`+mono-try-call`'s split block splits a
register defined in another block, or nowhere).  The invariant to carry
through the run instead is `SDW`: in every block, every split register is
defined by an earlier op of its body, OR it is no key of `cond` and lies
below `re`.

* `nsk_of_sdw`: `SDW` and "no defined register is a key" (track D's
  `IL.cond`) give "no split op splits a key" at a state;
* `SDWEndC` (the frame target, a leaf) and **`nskEndC_of`**: `NskEndC` from
  `KeyUndefC` and `SDWEndC`; `entryMono_noSixW` (`entryMono_noSixN` with
  `SDWEndC` for `NskEndC`);
* `proxy_fresh` (the carry fact: `+proxy` allocates its key at `re` and
  adds no other key, blocks unchanged) and **`sdw_proxy`**: `+proxy` keeps
  `SDW`, because an undefined split register lies below the old `re`, which
  is the new key;
* `sdw_of_sds`: the old frame's invariant is the first disjunct.

Left for `SDWEndC`: the `KS` frame of `Glue/SplitDefBase.lean` and
`Glue/SplitDefRun.lean` re-run with `SDW` for `SDS` (every block step: a
block put with a body meeting `SDW`, `+add-ops` in front, `+re` growing
`re`, `+proxy` by `sdw_proxy`), then the direct-call arms (`+mono-try-call`:
its split registers come from `+re` before the split block, so they are below
`re` and, not being keys yet, meet the second disjunct; the keys a later
`+kerf` makes are fresh by `proxy_fresh`).
-/

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-- **The weaker body invariant**: every split register of every block is
defined by an earlier op of its body, or is no key and lies below `re`. -/
def SDW (g : Comp.Gen Map) : Prop :=
  ∀ o b, HoonMap.get g.blocks o = some b → ∀ i p s, b.body[i]? = some p → splitReg p = some s →
    (∃ j : Nat, j < i ∧ ∃ q, b.body[j]? = some q ∧ aliasDst q = some s) ∨
      (HoonMap.get g.cond s = Option.none ∧ s < g.re)

theorem sdw_of_sds {g : Comp.Gen Map} (h : SDS g) : SDW g :=
  fun o b hb i p s hp hs => Or.inl (h o b hb i p s hp hs)

/-- **No split op splits a key**, from `SDW` and "no defined register is a
key". -/
theorem nsk_of_sdw {g : Comp.Gen Map} (hW : SDW g)
    (hK : ∀ x, Defd g.blocks x → HoonMap.get g.cond x = Option.none) :
    ∀ k b, HoonMap.get g.blocks k = some b → ∀ p ∈ b.body, ∀ s, splitReg p = some s →
      HoonMap.get g.cond s = Option.none := by
  intro k b hb p hp s hs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rcases hW k b hb i p s hi hs with ⟨j, -, q, hq, hd⟩ | ⟨hc, -⟩
  · exact hK s ⟨(k, some j), b, q, hb, hq, hd⟩
  · exact hc

/-- **Leaf (track G), the frame target**: after the top run and its `+kerf`
on a nomm with no `%6`, `SDW` holds. -/
def SDWEndC (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop :=
  ∀ nm, NoSixC nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) →
    kerf nex g1 = some ((o, sub), g2) → SDW g2

/-- **`NskEndC` from `KeyUndefC` (D) and `SDWEndC` (G).** -/
theorem nskEndC_of {env : CallEnv} (hK : KeyUndefC S Map env) (hW : SDWEndC S Map env) : NskEndC S Map env :=
  fun nm hn nex g1 g2 o sub h1 h2 => nsk_of_sdw (hW nm hn nex g1 g2 o sub h1 h2) (hK nm hn nex g1 g2 o sub h1 h2)

/-- **`EntryMono` on `NoSixM`** with the frame target `SDWEndC` in place of
`NskEndC`. -/
theorem entryMono_noSixW (lib : Lib) (hO : OptInMono S Map NoSixM) (hR : ReadsInMono S Map NoSixM)
    (hD : ∀ env, KIMid S Map env) (hK : ∀ env, KeyUndefC S Map env) (hW : ∀ env, SDWEndC S Map env) :
    EntryMono S Map lib NoSixM :=
  entryMono_noSixN lib hO hR hD hK fun env => nskEndC_of (hK env) (hW env)

/-- **`+proxy` allocates its key at `re`** and adds no other key; the blocks
do not change. -/
theorem proxy_fresh {r o p : Nat} {g g' : Comp.Gen Map} (h : proxy r o g = some (p, g')) :
    p = g.re ∧ g'.re = g.re + 1 ∧ g'.blocks = g.blocks ∧
      ∀ k, HoonMap.get g'.cond k ≠ Option.none → HoonMap.get g.cond k ≠ Option.none ∨ k = g.re := by
  unfold proxy at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, fun k hk => Or.inl hk⟩
  · obtain ⟨tag, -, e⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨rfl, rfl, rfl, fun k hk => ?_⟩
    rw [HoonMap.get_put] at hk
    by_cases e : k = g.re
    · exact Or.inr e
    · rw [if_neg e] at hk
      exact Or.inl hk

/-- **`+proxy` keeps `SDW`.** -/
theorem sdw_proxy {r o p : Nat} {g g' : Comp.Gen Map} (hW : SDW g) (h : proxy r o g = some (p, g')) : SDW g' := by
  obtain ⟨-, hre, hbl, hc⟩ := proxy_fresh h
  intro k b hb i q s hq hs
  rw [hbl] at hb
  rcases hW k b hb i q s hq hs with hd | ⟨hn, hlt⟩
  · exact Or.inl hd
  · refine Or.inr ⟨?_, by rw [hre]; omega⟩
    cases e : HoonMap.get g'.cond s with
    | none => rfl
    | some v =>
      rcases hc s (by rw [e]; exact Option.some_ne_none v) with h' | h'
      · exact absurd hn h'
      · omega

end Glue
end SkaModel
end Formalization
