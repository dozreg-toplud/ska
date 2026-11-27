import lemmas.Glue.ProxPlain

/-!
# The proxy facts with direct calls: the two leaves left (track G, twelfth pass)

LEDGER 2.c.  On `PlainN` both facts of `ProxOKN` are theorems
(`Glue/ProxPlain.lean`, `Glue/SplitDefRun.lean`).  With direct calls
(`NoSixM`) they are two end-state leaves:

* `KeyUndefC` (track D): no key of `cond` has a definition at the state
  after the top `+kerf`: the `¬ Defd` clause of track D's `IL.cond` there,
  which D's run invariant gives on `PlainN` (`topU_of`) and which D's
  current pass extends to the direct call;
* `NskEndC` (track G): no split op splits a key.  `SDBody` FAILS with a
  direct call (the split block `[hed r rh, tal r rt]` of `+mono-try-call`
  splits a register defined elsewhere, or nowhere: 64 of the 7,920 `enumDX`
  states split a register with no definition), but no key is split on any
  checked state (`Glue/ProxPlainCheck.lean`).  The run invariant to carry
  is: every split register is defined by an earlier op of its body, or is
  no key and lies below `re` (keys are allocated at `re` by `+proxy`; the
  registers `+mono-try-call` splits are allocated by `re`).

* **`proxEndC_of`**: `ProxOKN` at the end from the two leaves;
* **`guardMonoC_noSixN`**, **`entryMono_noSixN`**: `GuardMonoC` / `EntryMono`
  on `NoSixM` from `KIMid` and the two leaves (no `src` clause: weaker than
  `ProxEnd`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-- **Leaf (track D)**: after the top run and its `+kerf` on a nomm with no
`%6`, no key of `cond` has a definition. -/
def KeyUndefC (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop :=
  ∀ nm, NoSixC nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) →
    kerf nex g1 = some ((o, sub), g2) → ∀ x, Defd g2.blocks x → HoonMap.get g2.cond x = Option.none

/-- **Leaf (track G)**: after the top run and its `+kerf` on a nomm with no
`%6`, no split op splits a key. -/
def NskEndC (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop :=
  ∀ nm, NoSixC nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) →
    kerf nex g1 = some ((o, sub), g2) →
    ∀ k b, HoonMap.get g2.blocks k = some b → ∀ p ∈ b.body, ∀ s, splitReg p = some s →
      HoonMap.get g2.cond s = Option.none

/-- **`ProxOKN` at the end on `NoSixC`** from the two leaves. -/
theorem proxEndC_of {env : CallEnv} (hK : KeyUndefC S Map env) (hN : NskEndC S Map env) {nm : Nomm}
    (hn : NoSixC nm) {nex : NextL S} {g1 g2 : Comp.Gen Map} {o sub : Nat}
    (h1 : runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1))
    (h2 : kerf nex g1 = some ((o, sub), g2)) : ProxOKN g2.blocks g2.cond := by
  refine ⟨fun k b hb x hx => hK nm hn nex g1 g2 o sub h1 h2 x ?_, hN nm hn nex g1 g2 o sub h1 h2⟩
  rcases hx with hx | ⟨q, hq, hx⟩
  · exact ⟨(k, Option.none), b, hb, hx⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    exact ⟨(k, some i), b, q, hb, hi, hx⟩

/-- **`GuardMonoC` on `NoSixM`** from `KIMid` and the two leaves. -/
theorem guardMonoC_noSixN (hD : ∀ env, KIMid S Map env) (hK : ∀ env, KeyUndefC S Map env)
    (hN : ∀ env, NskEndC S Map env) : GuardMonoC S Map NoSixM := by
  intro env N bl nm c hn hs
  unfold finishLUCM at hs
  obtain ⟨⟨nex, g1⟩, h1, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨K, hI, hfo⟩ := top_kerfA (hD env) hn h1 h2
  have P := proxEndC_of (hK env) (hN env) hn h1 h2
  dsimp only at hs
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at hs
  simp only [flattenNeed, List.headD, List.length] at hs
  obtain ⟨start, hst, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hs
  have P0 := proxOKN_start P hst
  have B1 := blocksOKA_npN (blocksOKA_start hI.ok hfo.2 hst) P0
  have R := celAnn_renameN B1 (renA_proxN P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`EntryMono` on `NoSixM`** from track D's `OptInMono`, `ReadsInMono`,
`KIMid`, `KeyUndefC` and track G's `NskEndC`. -/
theorem entryMono_noSixN (lib : Lib) (hO : OptInMono S Map NoSixM) (hR : ReadsInMono S Map NoSixM)
    (hD : ∀ env, KIMid S Map env) (hK : ∀ env, KeyUndefC S Map env) (hN : ∀ env, NskEndC S Map env) :
    EntryMono S Map lib NoSixM :=
  entryMono_of lib hO hR (guardMonoC_noSixN hD hK hN)

end Glue
end SkaModel
end Formalization
