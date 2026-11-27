import lemmas.Ska.CompHintTree

/-!
# The side conditions of a `%mean` (README Gaps 24.6, 24.12)

`Annot.mean` ties nothing of the bell `b` and the constant `k` to the trap
(`nomm_agree` needs nothing: `nommStep` pushes `(%mean, trap)`), but the
frames the code pushes stand for `(%mean, trap)` only through
`FrameRel.meaf` (`%hmp`, no constant) and `FrameRel.meac` (`%hcp`, a
constant).  `MeanOK lib P h b k` states what they need, for the trap's
formula `h` on the subjects `P`, as a premise a class constructor for
`mean` takes (as `CallTreeH.n11d` takes `ClueSafe`), and which the glue
takes from the analysis of `+fol-loop` (line 2700 on):

* `bell`: `b` is a bell `+poke` takes: `b` is made by `+fol-loop` from a
  sock, so its noun decodes to it (the facts of `Bell.ofNoun?` on the
  analysis's bells, as for `Annot.direct`);
* `head`: every trap is a cell whose head is `b.fol` and that fits
  `b.less`: `b` is the bell of the arm `[2 [0 1] 0 2]` on the clue's
  product sock, whose battery is known, so the soundness of the clue's
  product sock gives both;
* `konst`: with a constant `n`, `+mack` of every trap gives `n`: `k` is
  the arm's product sock when it is fully known, so the soundness of the
  arm's analysis gives it (`+mean-konst` keeps it only for a pure arm).

`MeanOK.meac`, `MeanOK.meaf`: the frames, from `MeanOK` (and, for `%meaf`,
the bell's need `N b false` and the split of the trap by it).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- **The side conditions of `%mean`** for the trap's formula `h`. -/
structure MeanOK (lib : Lib) (P : Noun → Prop) (h : Noun) (b : Bell) (k : Option Noun) : Prop where
  bell : Bell.ofNoun? b.toNoun = some b
  head : ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s → Mink lib gul tm s h (Tone.zero trap) →
    ∃ hd tl, trap = C hd tl ∧ b.fol = hd ∧ SkaModel.Fits b.less trap
  konst : ∀ {n : Noun}, k = some n → ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s →
    Mink lib gul tm s h (Tone.zero trap) → MackRel lib trap n

/-- **The frame of a constant `%mean`** (`%hcp`) stands for `+mink`'s. -/
theorem MeanOK.meac {lib : Lib} {P : Noun → Prop} {h : Noun} {b : Bell} {n : Noun} (M : MeanOK lib P h b (some n))
    (N : Needs) {s gul : Noun} {tm : Trace} {trap : Noun} (hs : P s) (hm : Mink lib gul tm s h (Tone.zero trap)) :
    FrameRel lib N (Tag.meac, n) (Tag.mean, trap) :=
  FrameRel.meac (M.konst rfl hs hm)

/-- **The frame of a deferred `%mean`** (`%hmp`) stands for `+mink`'s, with
the values the split of the trap by the bell's need. -/
theorem MeanOK.meaf {lib : Lib} {P : Noun → Prop} {h : Noun} {b : Bell} {k : Option Noun} (M : MeanOK lib P h b k)
    {N : Needs} {nd : NeedOrd} (hN : N b false = some nd) {s gul : Noun} {tm : Trace} {trap : Noun} (hs : P s)
    (hm : Mink lib gul tm s h (Tone.zero trap)) {vals : List Noun} (hv : SkaModel.split nd trap = some vals) :
    FrameRel lib N (Tag.meaf, C b.toNoun (listNoun id vals)) (Tag.mean, trap) := by
  obtain ⟨hd, tl, rfl, hf, hfit⟩ := M.head hs hm
  exact FrameRel.meaf M.bell hfit hf hN hv

end Comp
end SkaModel
end Formalization
