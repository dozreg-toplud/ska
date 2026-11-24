#!/usr/bin/env python3
"""Generate kernBoth_lt and kernLoop_lt (the registers of +kern-need's ops,
with fresh registers bounded by the end state's re) from the text of
kernBoth_regs and kernLoop_regs in lemmas/Ska/CompUnproxyRegs.lean.
Prints the Lean text; each replacement asserts its match count."""
import re, sys
src = open(sys.argv[1]).read()
a = src.index('theorem kernBoth_regs')
b = src.index('/-- **The ops of the loop of `+kern-need` from `r` into `tgt` mention only')
c = src.index('theorem kernLoop_regs')
d = src.index('end Comp', c)
both, loop = src[a:b], src[c:d]
def rep(t, old, new, n):
    k = t.count(old)
    assert k == n, (old, k, n)
    return t.replace(old, new)
both = rep(both, 'kernBoth_regs', 'kernBoth_lt', 1)
both = rep(both, "(P r' → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops)",
           "(P r' → (∀ x, g.re ≤ x → x < g'.re → P x) → RegsIn P acc → RegsIn P ops)", 2)
both = rep(both, "(P r → P d → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops)",
           "(P r → P d → (∀ x, g.re ≤ x → x < g'.re → P x) → RegsIn P acc → RegsIn P ops)", 1)
both = rep(both, "have hg1 : ∀ x, g.re + 1 ≤ x → P x := fun x hx => hg x (by omega)",
           "have hg1 : ∀ x, g.re + 1 ≤ x → x < g2.re → P x := fun x hx hx' => hg x (by omega) (by omega)", 1)
both = rep(both, "have hg3 : ∀ x, g2.re + 1 ≤ x → P x := fun x hx => hg x (by omega)",
           "have hg3 : ∀ x, g2.re + 1 ≤ x → x < g4.re → P x := fun x hx hx' => hg x (by omega) hx'", 1)
both = rep(both, "R2 (hg g.re (Nat.le_refl _)) hg1 ha", "R2 (hg g.re (Nat.le_refl _) (by omega)) hg1 ha", 1)
both = rep(both, "exact hg _ (Nat.le_refl _)) A2", "exact hg _ (Nat.le_refl _) (by omega)) A2", 1)
both = rep(both, "R4 (hg g2.re (by omega)) hg3 A2'", "R4 (hg g2.re (by omega) (by omega)) hg3 A2'", 1)
both = rep(both, "exact hg _ (by omega)) A4", "exact hg _ (by omega) (by omega)) A4", 1)
loop = rep(loop, 'kernLoop_regs', 'kernLoop_lt', 1)
loop = rep(loop, "P r → (∀ x, NMem tgt x → P x) → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops",
           "P r → (∀ x, NMem tgt x → P x) → (∀ x, g.re ≤ x → x < g'.re → P x) → RegsIn P acc → RegsIn P ops", 1)
loop = rep(loop, "kernBoth_regs P", "kernBoth_lt P", 2)
loop = rep(loop, "      h).2 hr (hg _ (Nat.le_refl _)) (fun x hx => hg x (by simp only at hx; omega)) ha",
           "      h).2 hr (hg _ (Nat.le_refl _) (by\n        have := (kernBoth_lt P (fun r' acc g g' ops h => ⟨(kernLoop_spec p r' acc g g' ops h).choose_spec.2.le,\n          fun a b c => ihp r' acc g g' ops h a (fun x hx => ht x (Or.inl hx)) b c⟩)\n          (fun r' acc g g' ops h => ⟨(kernLoop_spec q r' acc g g' ops h).choose_spec.2.le,\n          fun a b c => ihq r' acc g g' ops h a (fun x hx => ht x (Or.inr hx)) b c⟩) h).1\n        simp only at this; omega))\n        (fun x hx hx' => hg x (by simp only at hx; omega) hx') ha", 1)
print(both + "/-- **`kernLoop_regs` with the fresh registers below the end's `re`.** -/\n" + loop, end='')
