import lemmas.Compiler.OptLinkTotalOnce
import lemmas.Compiler.OptLinkAlWalkGate

/-!
# The link of `+optimize` where the passes return

**`opt_gate_total_of`**: for the passes of the Hoon (`+alias` with
`Ana.pickR FinMap`, the real `+trim-trace-hints`, `+switch-chains` with any
fuel), on blocks with no `%lti`, `StInv ρ L` and a block invariant `J` for
which `PassTotal` holds, there are a fuel and a result `s'` with
`optimizeF fuel P s = some s'`, and the pill's `+optimize` returns the noun of
`s'` (`opt_gate_alias`).  The only condition left on the model is
`PassTotal` (what `+alias`, `+trim-trace-hints` and `+switch-chains` owe, and
`J` kept by the structural passes).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

theorem opt_gate_total_of (P : Opt.Passes (TreapMap mugF)) (hP : P.alias = Opt.aliasM (Ana.pickR FinMap))
    (hPt : ∀ bl topo rev, P.trim bl topo rev = Opt.trimTraceHints bl topo rev) (sfuel : Nat)
    (hPs : ∀ bl, P.switch bl = Opt.switchChains sfuel bl) {ρ : Nat → Nat} {L : List Nat}
    {J : TreapMap mugF Blob → Prop} (H : PassTotal P ρ L J) (s : Straight (TreapMap mugF))
    (hI : StInv ρ L s.blocks) (hJ : J s.blocks) (hl : NoLti s.blocks) :
    ∃ fuel s', Opt.optimizeF fuel P s = some s' ∧ nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun := by
  obtain ⟨F, s', hF⟩ := optimizeF_total H s hI hJ
  exact ⟨F, s', hF F (Nat.le_refl _), opt_gate_alias P hP hPt sfuel hPs F s s' hl (hF F (Nat.le_refl _))⟩

end Compiler
end Formalization
