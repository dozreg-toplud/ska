import lemmas.Compiler.Inlineable
import lemmas.Pill.Arm.Safe_nomm
import lemmas.Pill.Arm.Safe_fol_fol

/-!
`+safe-nomm` and `+safe-fol-fol` of the analysis core against `safeNomm` and
`safeFolFol` of `lemmas/Ska/FolLoop.lean`, on the noun `Nomm.toNoun` of every
nomm.

```hoon
++  safe-nomm
  |=  =nomm
  ^-  ?
  =*  g  .
  ?+    nomm  |
      [p=^ q=^]  &((g p.nomm) (g q.nomm))
      [%1 *]     &
      [%11 @ *]  &(?=(?(hint-safe %memo) p.nomm) (g q.nomm))
      [%11 [@ *] *]
    &(?=(?(hint-safe %memo) p.p.nomm) (g q.p.nomm) (g q.nomm))
      [%mean *]  &((g p.nomm) (g q.nomm))
  ==
```

`+safe-nomm` reads nothing from its context; `+safe-fol-fol` reads
`+safe-nomm` (`SafeFolFolIn`).  Both recurse on themselves through `=*  g  .`,
on sub-nomms, so the proofs go by induction on the nomm.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-- Every nomm is laid out as a cell. -/
theorem wut_nomm_toNoun (n : Nomm) : wut n.toNoun = A 0 := by
  cases n <;> rfl

/-- The tags that the arms test for: either the tag is one of the six of
`?(hint-safe %memo)`, or it differs from all six. -/
theorem hintSafeMemo_cases (tag : Nat) :
    (hintSafeMemo tag = true ∧
      (tag = 0x6f6d656d ∨ tag = 0x6b6e7568 ∨ tag = 0x646e6168 ∨ tag = 0x6e61656d ∨
        tag = 0x65736f6c ∨ tag = 0x746f7073)) ∨
    (hintSafeMemo tag = false ∧ ¬ (0x6f6d656d = tag) ∧ ¬ (0x6b6e7568 = tag) ∧
      ¬ (0x646e6168 = tag) ∧ ¬ (0x6e61656d = tag) ∧ ¬ (0x65736f6c = tag) ∧
      ¬ (0x746f7073 = tag)) := by
  cases h : hintSafeMemo tag <;> simp [hintSafeMemo, hintSafe, stopTag] at h <;>
    simp only [Tag.memo, Tag.hunk, Tag.hand, Tag.mean, Tag.lose, Tag.spot] at h <;> simp <;> omega

@[nock_exec] theorem safe_nomm_arm (c : Noun) :
    nock c safe_nomm.arm = some (C safe_nomm.battery (C (C (A 0) (A 0)) c)) := by
  nock_open safe_nomm.arm; simp only [nock_exec]

/-- One case of `+safe-nomm` or `+safe-fol-fol`: run the tests, recurse by the
induction hypotheses, which are in the context with the facts about the tag. -/
macro "safe_simp" : tactic => `(tactic|
  (simp [nock_exec, nock_ite, Nomm.toNoun, safeNomm, safeFolFol, wut_nomm_toNoun, ite_some,
     loob_rev, loob_and', Bool.and_assoc, Tag.mean, *]
   try rfl))

/-- Slamming `+safe-nomm` on a nomm, in any context. -/
theorem safe_nomm_gate (ctx : Noun) : ∀ (n : Nomm),
    nock (C safe_nomm.battery (C n.toNoun ctx)) safe_nomm.battery
      = some (Hoon.loob (safeNomm n)) := by
  intro n
  induction n with
  | cons p q ihp ihq => nock_open safe_nomm.battery; safe_simp
  | n11s tag q body ihq =>
    nock_open safe_nomm.battery
    rcases hintSafeMemo_cases tag with ⟨h, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
        ⟨h, h1, h2, h3, h4, h5, h6⟩ <;>
      safe_simp
  | n11d tag hh q body ihh ihq =>
    nock_open safe_nomm.battery
    rcases hintSafeMemo_cases tag with ⟨h, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
        ⟨h, h1, h2, h3, h4, h5, h6⟩ <;>
      safe_simp
  | mean p b q body k ihp ihq => nock_open safe_nomm.battery; safe_simp
  | _ => nock_open safe_nomm.battery; safe_simp

/-! ## `+safe-fol-fol` -/

/-- What `+safe-fol-fol` reads from its context: the arm `+safe-nomm`. -/
abbrev SafeFolFolIn (c : Noun) : Prop := slot? safe_nomm.axis c = some safe_nomm.arm

@[nock_exec] theorem safe_fol_fol_arm (c : Noun) :
    nock c safe_fol_fol.arm = some (C safe_fol_fol.battery (C (C (A 0) (A 0)) c)) := by
  nock_open safe_fol_fol.arm; simp only [nock_exec]

/-- The cases of `+safe-fol-fol`, which slam `+safe-nomm` too. -/
macro "safe_simp'" : tactic => `(tactic|
  (simp [nock_exec, nock_ite, Nomm.toNoun, safeNomm, safeFolFol, wut_nomm_toNoun, ite_some,
     loob_rev, loob_and', Bool.and_assoc, Tag.mean, safe_nomm_arm, safe_nomm_gate, *]
   try rfl))

/-- Slamming `+safe-fol-fol` on a nomm, in a context that holds `+safe-nomm`. -/
theorem safe_fol_fol_gate (ctx : Noun) (hc : SafeFolFolIn ctx) : ∀ (n : Nomm),
    nock (C safe_fol_fol.battery (C n.toNoun ctx)) safe_fol_fol.battery
      = some (Hoon.loob (safeFolFol n)) := by
  intro n
  induction n with
  | cons p q ihp ihq => nock_open safe_fol_fol.battery; safe_simp'
  | n11s tag q body ihq =>
    nock_open safe_fol_fol.battery
    rcases hintSafeMemo_cases tag with ⟨h, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
        ⟨h, h1, h2, h3, h4, h5, h6⟩ <;>
      safe_simp'
  | n11d tag hh q body ihh ihq =>
    nock_open safe_fol_fol.battery
    rcases hintSafeMemo_cases tag with ⟨h, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
        ⟨h, h1, h2, h3, h4, h5, h6⟩ <;>
      safe_simp'
  | mean p b q body k ihp ihq => nock_open safe_fol_fol.battery; safe_simp'
  | _ => nock_open safe_fol_fol.battery; safe_simp'

/-! ## On the pill's analysis core, with no assumption -/

theorem safe_nomm_pill (n : Nomm) :
    nock (C safe_nomm.battery (C n.toNoun ana)) safe_nomm.battery
      = some (Hoon.loob (safeNomm n)) :=
  safe_nomm_gate ana n

theorem safe_fol_fol_pill (n : Nomm) :
    nock (C safe_fol_fol.battery (C n.toNoun ana)) safe_fol_fol.battery
      = some (Hoon.loob (safeFolFol n)) :=
  safe_fol_fol_gate ana safe_nomm.arm_at n

end Compiler
end Formalization
