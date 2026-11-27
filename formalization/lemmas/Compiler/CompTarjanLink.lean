import lemmas.Compiler.CompTarjanGate

/-!
# `TarjanLinkAt`: the leaf on `+tarjan` the miss of `+scc-of` takes (track Q)

`+scc-of` (`[9 2815 [0 255]]` in its miss) and `+ska-poke` slam the gate
`tjArm` of `ana`: the gate core is `[tjBat [g ana]]` and the slam runs
`tjBat` on it.  `TarjanLinkAt g`: whenever the model `tarjanM` of the
pre-order graph of `g` returns `L`, the pill returns a list of set nouns
with the members of the lists of `L`, in the same order (callers first).

`tarjanLinkAt_of` gives it from `tj_bat`'s three hypotheses on `g`: the
node shape, `TjGraphAt` (the `+get:ju` of `g` is `kidsOf`), and the bunt of
the outer gate's sample (`tjSamB`, the molds of `gen`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

/-- **The leaf on `+tarjan`.** -/
def TarjanLinkAt (G : Noun) : Prop :=
  ∀ L, tarjanM (tjGraph G) = some L → ∃ FIN, TjFinIs FIN L ∧ nock (C tjBat (C G ana)) tjBat = some FIN

/-- The gate core of the slam: `tjArm` on `ana` with the sample `g`. -/
theorem tjArm_gate : nock ana tjArm = some (C tjBat (C (A 0) ana)) := by
  rw [tjArm_eq]; simp [nock_exec]

/-- **`TarjanLinkAt` from the three hypotheses of `tj_bat`.** -/
theorem tarjanLinkAt_of {G E : Noun} (hG : Tree G) (hn : ∀ x ∈ preorder G, ∃ v KS, x = C v KS ∧ Tree KS)
    (hg : TjGraphAt (C tjBat (C G ana)) (tjGraph G))
    (hb : nock (C tjBat (C G ana)) tjSamB = some (C E (tjAccN (A 0) (A 0) (A 0) (A 0) (A 0)))) :
    TarjanLinkAt G :=
  fun _ h => tj_bat hG hn hg hb h

end Compiler
end Formalization
