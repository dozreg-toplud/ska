import lemmas.Glue.GuardCallsR

/-!
# `GuardMonoC` on code with calls and no `%6` (track G, tenth pass)

LEDGER 2.c.  `finishLUCM env nm` is the run `runLCM env true` under `%done`
from `gen0`, `+kerf` of its result, and `+to-straight`.  The run keeps
`InvA` (`runG_lcm`, under `KIMid`), so does the top `+kerf` (`kerfG`, its
lazy is `DN` by `KIMid.run`), and the start block it returns has no
annotation.  The last step is the named hypothesis `StraightA`: the final
pass (`+to-straight`: unproxying, renaming, `+chase`, the start block moved
to `0`) takes the annotated form of the state the top `+kerf` leaves to a
cell annotation of the finished code.  It is checked on 7 of 7 direct calls
and 990 of 990 sampled `enumDX` nomms (`Glue/GuardCallsCheck.lean`, the
third stage).  Why it is not the old `blocksOK_rename`: an inner `+kerf`
(a call) leaves proxies in `cond` for a register its `%nok` / `%cal`
writes, so `RenOK` (no written register is merged with another) does not
hold as such; the annotation must be renamed with the registers.

* `guardMonoC_noSix`: **`GuardMonoC` on `NoSixM` from `KIMid` and
  `StraightA`**; `guardMonoC_sub`: on every subclass.
* `entryMono_noSix`: `EntryMono` on `NoSixM` from track D's two leaves
  (`OptInMono`, `ReadsInMono`) and these two named hypotheses.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-- **The final pass keeps the annotation** (named hypothesis): on a nomm
with no `%6`, from the state the top `+kerf` leaves, with `InvA K` and the
start block without annotation, the finished code has a cell annotation
and passes no `~`. -/
def StraightA (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop :=
  ∀ nm, NoSixC nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat) (c : Straight Map)
    (K : Nat → Nat → Prop),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) →
    kerf nex g1 = some ((o, sub), g2) → InvA K g2 → FL K g2.bo o →
    toStraightF g2.cond g2.blocks (Need.this sub) o = some c → NoPoison c.blocks ∧ ∃ K', CelAnn c.blocks K'

/-- **The state the top `+kerf` leaves**: `InvA K` and a start block
without annotation. -/
theorem top_kerfA {env : CallEnv} (hD : KIMid S Map env) {nm : Nomm} (hn : NoSixC nm) {nex : NextL S}
    {g1 g2 : Comp.Gen Map} {o sub : Nat}
    (h1 : runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1))
    (h2 : kerf nex g1 = some ((o, sub), g2)) : ∃ K, InvA K g2 ∧ FL K g2.bo o := by
  obtain ⟨K1, hI1, X1, hR1⟩ := (runG_lcm hD nm hn Option.none (fun _ _ => False) 1 0 CGoalL.done [] trivial
    trivial).k _ gen0 nex g1 invA_gen0 (by simp [gen0]) (XB.refl _ _ _) h1
  have hdn : LzS (DN g1.re) nex.laz := hD.run nm Option.none hn CGoalL.done [] gen0 g1 nex trivial h1
  have h0 : 0 < g1.bo := Nat.lt_of_lt_of_le (by simp [gen0]) X1.1
  obtain ⟨K2, hI2, -, hfo, -⟩ := (kerfG K1 g1.bo g1.re nex hR1.1 hR1.2.1 hR1.2.2 hdn).k K1 g1 (o, sub) g2 hI1 h0
    (XB.refl _ _ _) h2
  exact ⟨K2, hI2, hfo⟩

/-- **`GuardMonoC` on code with calls and no `%6`**, from the mid-run fact
`KIMid` and the final pass `StraightA`. -/
theorem guardMonoC_noSix (hD : ∀ env, KIMid S Map env) (hT : ∀ env, StraightA S Map env) :
    GuardMonoC S Map NoSixM := by
  intro env N bl nm c hf hs
  unfold finishLUCM at hs
  obtain ⟨⟨nex, g1⟩, h1, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨K, hI, ho⟩ := top_kerfA (hD env) hf h1 h2
  exact hT env nm hf nex g1 g2 o sub c K h1 h2 hI ho hs

/-- `GuardMonoC` holds on every subclass. -/
theorem guardMonoC_sub {F G : MonoClass} (h : GuardMonoC S Map F) (hs : ∀ env N bl nm, G env N bl nm → F env N bl nm) :
    GuardMonoC S Map G :=
  fun env N bl nm c hg hc => h env N bl nm c (hs env N bl nm hg) hc

/-- **`EntryMono` on code with calls and no `%6`** from track D's two leaves
and the named hypotheses `KIMid`, `StraightA`. -/
theorem entryMono_noSix (lib : Lib) (hO : OptInMono S Map NoSixM) (hR : ReadsInMono S Map NoSixM)
    (hD : ∀ env, KIMid S Map env) (hT : ∀ env, StraightA S Map env) : EntryMono S Map lib NoSixM :=
  entryMono_of lib hO hR (guardMonoC_noSix hD hT)

end Glue
end SkaModel
end Formalization
