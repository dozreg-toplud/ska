import lemmas.Glue.EntryPathD
import lemmas.Glue.EntryFragX
import lemmas.Glue.GuardFinalTop

/-!
# `EntryMono`, `EntryNary` on classes with calls, from named leaves

LEDGER 2.c (track G, eighth pass).  With `entryOK_ofK`
(`Glue/EntryPathD.lean`), `EntryOK` of raw code needs `DefFirst`, `ReadsIn`
at the argument count, `NoPoison` and a cell annotation `CelAnn`.  On a
class `FM` of `Glue/MonoCalls.lean` (with calls):

* `DefFirst`: a field of `OptIn`, the leaf `OptInMono` / `OptInNary` (track
  D, `ArmsL`);
* `ReadsIn`: the leaf `ReadsInMono` / `ReadsInNary` (track D:
  `optInput_finishLUX_at` is its `FragX` case);
* `NoPoison` and `CelAnn`: the leaf `GuardMonoC` / `GuardNaryC` (track G:
  the run-level induction with the path guard, below).

`entryMono_of`, `entryNary_of`: the leaves `EntryMono`, `EntryNary` from
them.  `guardMonoC_fragX`: on `FragX` the new guard leaf is the old one
(`CelGuard` gives `CelAnn` with `K` empty).

## The all-blocks form for the run-level induction

`BlocksOKA bl K`: every block passes no `~`, `K` names no parameter and
nothing at `0`, every edge of EVERY block into a label with `K _ s` is a
`ClqYes` or a `CellOut`, and every split is guarded by a `%cel` of the body
or by `K`.  `celAnn_of_blocksOKA`, `noPoison_of_blocksOKA`; `BlocksOK` is
the case `K` empty (`blocksOKA_of_blocksOK`).  What a run must carry beside
it with calls (not proved here; LEDGER 2.c): `K` is the set of the split
blocks of `+mono-try-call` with their register, a split block is emitted by
`+emit` at the fresh label `bo` and only the `%clq` block emitted right
after it jumps to it, so the run must also keep "every jump of every block
goes below `bo`" and "no goal or result jump goes to a label with `K`".
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map] [Opt.MapKeys Map]
variable {S : Type} [Comp.HoonSet S]

/-! ## The leaves -/

/-- **Leaf (track G): the raw whole-subject code of the class passes no `~`
and has a cell annotation.** -/
def GuardMonoC (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (FM : MonoClass) : Prop :=
  ∀ env N bl nm (c : Straight Map), FM env N bl nm → Comp.finishLUCM (S := S) env nm = some c →
    NoPoison c.blocks ∧ ∃ K, CelAnn c.blocks K

/-- **Leaf (track G): the same of the raw n-ary code of the class.** -/
def GuardNaryC (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (FN : NaryClass) : Prop :=
  ∀ env N bl cape bake nm ord (c : Straight Map), FN env N bl cape bake nm →
    Comp.finishLFC (S := S) env nm ord cape bake = some c → NoPoison c.blocks ∧ ∃ K, CelAnn c.blocks K

/-- **Leaf (track D): `ReadsIn` of the raw whole-subject code of the class.** -/
def ReadsInMono (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (FM : MonoClass) : Prop :=
  ∀ env N bl nm (c : Straight Map), FM env N bl nm → Comp.finishLUCM (S := S) env nm = some c →
    Compiler.ReadsIn c.nargs c.blocks

/-- **Leaf (track D): `ReadsIn` of the raw n-ary code of the class, and its
argument count is that of its need.** -/
def ReadsInNary (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (FN : NaryClass) : Prop :=
  ∀ env N bl cape bake nm ord (c : Straight Map), FN env N bl cape bake nm →
    Comp.finishLFC (S := S) env nm ord cape bake = some c →
      Compiler.ReadsIn c.nargs c.blocks ∧ c.nargs = Comp.countArgs c.need

theorem finishLUCM_nargs1 {env : Comp.CallEnv} {nm : Nomm} {c : Straight Map}
    (h : Comp.finishLUCM (S := S) (Map := Map) env nm = some c) : c.nargs = 1 := by
  unfold Comp.finishLUCM at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact (PokeM.toStraightF_this h).2

/-! ## `EntryMono`, `EntryNary` -/

/-- **The leaf `EntryMono` from `OptInMono`, `ReadsInMono` and
`GuardMonoC`.** -/
theorem entryMono_of (lib : Lib) {FM : MonoClass} (hO : OptInMono S Map FM) (hR : ReadsInMono S Map FM)
    (hG : GuardMonoC S Map FM) : EntryMono S Map lib FM := by
  intro env N bl nm s hf hs x _ σ O gul st t
  obtain ⟨hP, K, hK⟩ := hG env N bl nm s hf hs
  exact entryOK_ofK (hO env N bl nm s hf hs).defFirst (hR env N bl nm s hf hs) hP hK
    (by rw [finishLUCM_nargs1 hs]; simp) lib O gul st t

/-- **The leaf `EntryNary` from `OptInNary`, `ReadsInNary` and
`GuardNaryC`.** -/
theorem entryNary_of (lib : Lib) {FN : NaryClass} (hO : OptInNary S Map FN) (hR : ReadsInNary S Map FN)
    (hG : GuardNaryC S Map FN) : EntryNary S Map lib FN := by
  intro env N bl cape bake nm ord s hf hs x _ args hargs σ O gul st t
  obtain ⟨hP, K, hK⟩ := hG env N bl cape bake nm ord s hf hs
  obtain ⟨hR1, hn⟩ := hR env N bl cape bake nm ord s hf hs
  exact entryOK_ofK (hO env N bl cape bake nm ord s hf hs).defFirst hR1 hP hK
    (by rw [hn, split_length _ _ _ hargs]; exact Nat.le_refl _) lib O gul st t

/-! ## The all-blocks form -/

/-- **The all-blocks form with a cell annotation.** -/
structure BlocksOKA (bl : Map Blob) (K : Nat → Nat → Prop) : Prop where
  noNone : ∀ o b, HoonMap.get bl o = some b → ∀ j ∈ getJmps b.fin, Option.none ∉ j.args
  par : ∀ o b s, HoonMap.get bl o = some b → K o s → s ∉ b.par
  zero : ∀ s, ¬ K 0 s
  edge : ∀ o b j s, HoonMap.get bl o = some b → j ∈ getJmps b.fin → K j.there s →
    ClqYes b.fin s j.there ∨ CellOut K o b s
  split : ∀ o b, HoonMap.get bl o = some b → ∀ i p s, b.body[i]? = some p → splitReg p = some s →
    (∃ j : Nat, j < i ∧ b.body[j]? = some (Pole.cel s) ∧
      ∀ l, j < l → l < i → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s) ∨
    (K o s ∧ NoWriteBefore b.body i s)

theorem noPoison_of_blocksOKA {bl : Map Blob} {K : Nat → Nat → Prop} (h : BlocksOKA bl K) : NoPoison bl :=
  fun o b j _ hb hj => h.noNone o b hb j hj

theorem celAnn_of_blocksOKA {bl : Map Blob} {K : Nat → Nat → Prop} (h : BlocksOKA bl K) : CelAnn bl K where
  par := h.par
  zero := h.zero
  edge := fun o b j s _ hb hj hk => h.edge o b j s hb hj hk
  split := fun o b i p s _ hb hp hs => h.split o b hb i p s hp hs

/-- **`BlocksOK` is the all-blocks form with no annotation.** -/
theorem blocksOKA_of_blocksOK {bl : Map Blob} (h : BlocksOK bl) : BlocksOKA bl (fun _ _ => False) where
  noNone := fun o b hb => (h o b hb).1
  par := fun _ _ _ _ hk => hk.elim
  zero := fun _ hk => hk
  edge := fun _ _ _ _ _ _ hk => hk.elim
  split := fun o b hb i p s hp hs => Or.inl ((h o b hb).2 i p s hp hs)

/-- `CelGuard` is an annotation with `K` empty. -/
theorem celAnn_of_celGuard {bl : Map Blob} (h : CelGuard bl) : CelAnn bl (fun _ _ => False) where
  par := fun _ _ _ _ hk => hk.elim
  zero := fun _ hk => hk
  edge := fun _ _ _ _ _ _ _ hk => hk.elim
  split := fun o b i p s ho hb hp hs => Or.inl (h o b i p s ho hb hp hs)

/-- **On `FragX` the new guard leaf is the old one.** -/
theorem guardMonoC_fragX : GuardMonoC S Map (liftMC (FragXM S)) := by
  intro env N bl nm s hf hs
  rw [Comp.finishLUCM_eq _ (Comp.noDirect_of_fragX hf.1),
    Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  obtain ⟨hP, hG⟩ := guardMonoX nm s hf.1 hf.2 hs
  exact ⟨hP, _, celAnn_of_celGuard hG⟩

end Glue
end SkaModel
end Formalization
