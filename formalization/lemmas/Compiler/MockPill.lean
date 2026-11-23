import lemmas.Compiler.Mook
import lemmas.Compiler.MinkPill
import lemmas.Hoon.Layer2

/-!
`+mook` and `+mock` in the pill's layer 4 of `hoon.hoon`: layer 4 satisfies
`MookIn` and `MockIn`, so the theorems keep only the hypotheses on the model's
`Lib`: the scry gate is slammed as Nock slams it (`SlamIsNock`), and the three
formatting fields are what the pill's gates compute (`RendBaseIs`,
`SoftTankIs`, `SkipMsgIs`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

theorem mookIn_layer4 : MookIn layer4 := by
  obtain ⟨_, hsub, _, _, _, _, hgth, _⟩ := Hoon.arith_layer1
  exact ⟨mack.arm_at, mackIn_layer4, soft.arm_at, layer2, mook.layer2.arm_at, turn.arm_at,
    homo.arm_at, lent.arm_at, weld.arm_at, scag.arm_at, slag.arm_at, tank.arm_at, ⟨hgth, hsub⟩⟩

theorem mockIn_layer4 : MockIn layer4 := ⟨mook.arm_at, mookIn_layer4⟩

theorem rendIn_layer4 : RendIn mugF layer4 layer2 := by
  obtain ⟨_, _, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := Hoon.arith_layer1
  have hbex : BexIn layer2 := ⟨bex.arm_at, hm⟩
  exact ⟨scow.arm_at, rip.arm_at, ⟨end.arm_at, hbex, hmd⟩, ⟨rsh.arm_at, hbex, hdv⟩,
    ⟨Pill.mug.arm_at, mug_layer2⟩⟩

/-- In layer 4, `RendBaseIs` holds of a `Lib` that takes the frames of
`rendLeaf` as the pill does, whose `%hand` frames are `+scow %p` of `mugF`,
and whose `%hunk` frames of a cell and `%spot` frames are the pill's. -/
theorem rendBaseIs_layer4 (lib : Lib) (hleaf : RendLeafIs lib) (hhand : HandIs lib mugF layer4)
    (hrest : RendRestIs lib layer4) : RendBaseIs lib layer4 :=
  rendBaseIs_of lib mugF layer4 mookIn_layer4
    (fun l2 h => by
      rw [mook.layer2.arm_at] at h
      cases h
      exact rendIn_layer4) hleaf hhand hrest

/-- The pill's `+mook` on the encoding of a tone. -/
theorem mook_pill_iff (lib : Lib) (hslam : SlamIsNock lib) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (ton : Tone) (x : Noun) :
    nock (C mook.battery (C ton.toNoun layer4)) mook.battery = some x ↔
      ∃ k toon, mookF lib k ton = some toon ∧ x = toon.toNoun :=
  mook_gate_iff lib layer4 mookIn_layer4 hslam hrb hst hm ton x

/-- The pill's `+mock`, the arm at `mock.axis` of layer 4, slammed on
`[[s f] gul]`, returns `x` exactly when the model's `Mock` returns a toon that
`x` encodes.  The assumptions on `Lib`: the scry gate is slammed as Nock slams
it; the frames that `rend` formats with constants and `+rip` are taken as the
pill takes them (`RendLeafIs`, on `Lib` alone); and five formatting facts are
what the pill computes, each a field of `Lib`: `+scow %p` for `%hand`, `rend`
on `%hunk` of a cell and on `%spot` (`+smyt`), `(soft tank)` and the cord of
`+skip` (`+scow %ud`, `+crip`). -/
theorem mock_pill_iff (lib : Lib) (hslam : SlamIsNock lib) (hleaf : RendLeafIs lib)
    (hhand : HandIs lib mugF layer4) (hrest : RendRestIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (s f gul x : Noun) :
    nock (C mock.battery (C (C (C s f) gul) layer4)) mock.battery = some x ↔
      ∃ toon, Mock lib s f gul toon ∧ x = toon.toNoun :=
  mock_gate_iff lib layer4 mockIn_layer4 hslam (rendBaseIs_layer4 lib hleaf hhand hrest) hst hm
    s f gul x

end Compiler
end Formalization
