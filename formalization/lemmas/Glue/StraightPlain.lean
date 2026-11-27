import lemmas.Glue.StraightRen
import lemmas.Ska.RawInvCLLeaves

/-!
# `EntryMono` on track D's class `PlainM` (track G, eleventh pass)

LEDGER 2.c.  Track D proved its two whole-subject leaves on `PlainM`
(indirect calls, no `%6`, no direct call, no hint; `Ska/RawInvCLLeaves.lean`:
`optInMono_plain`, `readsInMono_plain`).  `PlainN` has no `%6`
(`noSix_of_plain`), so `PlainM` is inside `NoSixM` and `guardMonoC_noSixP`
applies there:

* `guardMonoC_plain`: `GuardMonoC` on `PlainM` from `KIMid` and `ProxEnd`;
* **`entryMono_plain`**: `EntryMono` on `PlainM` from `KIMid` (its run
  clause is D's; `kim_split`, `kim_into` are D's theorems) and `ProxEnd`
  alone.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-- **`PlainN` has no `%6`.** -/
theorem noSix_of_plain : ∀ nm : Nomm, Comp.PlainN nm → NoSixC nm
  | Nomm.cons p q, h => ⟨noSix_of_plain p h.1, noSix_of_plain q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q Option.none, h => ⟨noSix_of_plain p h.1, noSix_of_plain q h.2⟩
  | Nomm.n2 _ _ (some _), h => h.elim
  | Nomm.n3 p, h => noSix_of_plain p h
  | Nomm.n4 p, h => noSix_of_plain p h
  | Nomm.n5 p q, h => ⟨noSix_of_plain p h.1, noSix_of_plain q h.2⟩
  | Nomm.n6 _ _ _, h => h.elim
  | Nomm.n7 p q, h => ⟨noSix_of_plain p h.1, noSix_of_plain q h.2⟩
  | Nomm.n10 _ v q, h => ⟨noSix_of_plain v h.1, noSix_of_plain q h.2⟩
  | Nomm.n11s _ _ _, h => h.elim
  | Nomm.n11d _ _ _ _, h => h.elim
  | Nomm.n12 _ _, h => h.elim
  | Nomm.mean _ _ _ _ _, h => h.elim

/-- `GuardMonoC` on `PlainM` from `KIMid` and `ProxEnd`. -/
theorem guardMonoC_plain (hD : ∀ env, KIMid S Map env) (hP : ∀ env, ProxEnd S Map env) :
    GuardMonoC S Map PlainM :=
  guardMonoC_sub (guardMonoC_noSixP hD hP) fun _ _ _ nm h => noSix_of_plain nm h

/-- **`EntryMono` on `PlainM`** from `KIMid` and `ProxEnd` alone (track D's
`optInMono_plain`, `readsInMono_plain`). -/
theorem entryMono_plain (lib : Lib) (hD : ∀ env, KIMid S Map env) (hP : ∀ env, ProxEnd S Map env) :
    EntryMono S Map lib PlainM :=
  entryMono_of lib optInMono_plain readsInMono_plain (guardMonoC_plain hD hP)

end Glue
end SkaModel
end Formalization
