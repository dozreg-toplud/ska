import lemmas.Compiler.CapeSize
import lemmas.Compiler.TreapKey
import lemmas.Hoon.Layer2
import lemmas.Ska.Analysis
import lemmas.Pill.Arm.Git_g

/-!
`+git-g` of the analysis core `ana` against `Ana.gitG` of
`lemmas/Ska/Analysis.lean`, on the treaps of `FinMap` (`TreapKey.lean`).

```hoon
++  git-g
  |=  [g=callgraph i=identity]
  ^-  datum
  (~(gut by g) i *datum)
```

The gate builds the door `+by` of the library's second layer, at axis `8191`
of its context, on `g`, and slams its `gut` on `[i *datum]`; the bunt of
`datum` is a constant of the formula, the noun of `FDatum.bunt`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-! ## The noun of the empty treap and of `*datum` -/

namespace FinMap

variable {κ ν : Type} [TKey κ]

theorem foldl_step_empty (f : ν → Noun) :
    ∀ (L : List κ) (a : Noun), L.foldl (step f (empty : FinMap κ ν)) a = a
  | [], _ => rfl
  | _ :: L, a => foldl_step_empty f L a

theorem toNoun_empty (f : ν → Noun) : (empty : FinMap κ ν).toNoun f = A 0 :=
  foldl_step_empty f _ _

theorem setNoun_empty : (empty : FinMap κ Unit).setNoun = A 0 := by
  unfold setNoun; rw [toNoun_empty]; rfl

end FinMap

/-- The noun of `*datum`, as the formula of `+git-g` quotes it. -/
theorem fdatum_bunt_toNoun :
    (FDatum.bunt : FDatum FinMap).toNoun =
      C (A 0) (C (C (A 0) (A 0)) (C (C (A 1) (A 0)) (C (A 1) (C (A 1)
        (C (C (A 0x64696f76) (A 0)) (A 0)))))) := by
  show C (Treap.setNoun (Treap.empty : FinMap CalleeEntry Unit)) _ = _
  show C (FinMap.setNoun (FinMap.empty : FinMap CalleeEntry Unit)) _ = _
  rw [FinMap.setNoun_empty]
  rfl

/-! ## The gate -/

/-- The axis of the library's second layer in the context of `+git-g`. -/
abbrev gitG.layer2.axis : Nat := 8191

/-- What `+git-g` reads from its context: the door `+by` and what its `gut`
reads. -/
abbrev GitGIn (c : Noun) : Prop :=
  ∃ l2, slot? gitG.layer2.axis c = some l2 ∧ slot? by.axis l2 = some by.arm ∧
    FallIn l2 ∧ SomeIn l2 ∧ GorIn mugF l2

@[nock_exec] theorem git_g_arm (c : Noun) :
    nock c git_g.arm
      = some (C git_g.battery (C (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) c)) := by
  nock_open git_g.arm; simp only [nock_exec]

/-- Slamming `+git-g` on a call graph of `FinMap` and an identity. -/
theorem git_g_gate (ctx : Noun) (hc : GitGIn ctx) (g : Callgraph FinMap) (i : Ident) :
    nock (C git_g.battery (C (C (Treap.toNoun FDatum.toNoun g) (identNoun i)) ctx))
        git_g.battery
      = some (Ana.gitG g i).toNoun := by
  obtain ⟨l2, hl2, hby, hfall, hsome, hgor⟩ := hc
  have hg : getF mugF (identNoun i) (Treap.toNoun FDatum.toNoun g)
      = some (unitNoun FDatum.toNoun (Treap.get g i)) :=
    FinMap.getF_toNoun FDatum.toNoun g i
  unfold Ana.gitG Treap.gut
  nock_open git_g.battery
  cases e : Treap.get g i with
  | none =>
    rw [e] at hg
    simp only [unitNoun] at hg
    simp [nock_exec, hl2, hby, by_arm, by.gut.arm_at, gut_arm,
      gut_gate l2 ⟨hfall, hsome, hgor⟩ _ _ _ _ hg (Or.inl rfl), fdatum_bunt_toNoun]
  | some d =>
    rw [e] at hg
    simp only [unitNoun] at hg
    simp [nock_exec, hl2, hby, by_arm, by.gut.arm_at, gut_arm,
      gut_gate l2 ⟨hfall, hsome, hgor⟩ _ _ _ _ hg (Or.inr ⟨_, rfl⟩)]

/-! ## On the pill's analysis core -/

/-- `ana` holds the library's second layer at axis `8191`: through `lib`. -/
theorem ana_layer2 : slot? gitG.layer2.axis ana = some layer2 := by
  have h : slot? 7 ana = slot? 1 lib := by
    rw [show (7 : Nat) = knit_anno.lib.axis from rfl, knit_anno.lib.arm_at]; rfl
  have := slot_spine (by omega) (by omega) h 10
  simp only [show 2 ^ 10 * (7 + 1) - 1 = 8191 from rfl,
    show 2 ^ 10 * (1 + 1) - 1 = 2047 from rfl] at this
  rw [this]
  exact ca.lib.layer2.arm_at

theorem gitGIn_ana : GitGIn ana :=
  ⟨layer2, ana_layer2, by.arm_at, fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩

theorem git_g_pill (g : Callgraph FinMap) (i : Ident) :
    nock (C git_g.battery (C (C (Treap.toNoun FDatum.toNoun g) (identNoun i)) ana))
        git_g.battery
      = some (Ana.gitG g i).toNoun :=
  git_g_gate ana gitGIn_ana g i

end Compiler
end Formalization
