import lemmas.Ska.RawInvCLFrameSplit
import lemmas.Ska.RawInvCLFrameCopy

/-!
# The frame of a run with calls: the indirect call `%2`

README Gaps 14 (b), track D.  **`frameRun_n2`**: the frame of `[2 p q]`
from the frames of `p` and `q`: `+simple-next`, `+kerf`, the two fresh
registers and the `%nok` block, then the chain `q`, `+past`, `p`, `+copy`
(`frame_chain`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The frame of an indirect call.** -/
theorem frameRun_n2 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLC (S := S) (Map := Map) env sup p)) (hq : FrameRun (runLC (S := S) (Map := Map) env sup q)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n2 p q Option.none)) := by
  intro goal region g0 g' nex h
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  obtain ⟨d1, gr1⟩ := frame_simpleNextL h1
  obtain ⟨d2, hpro⟩ := frame_kerf h2
  have r1 : g0.re ≤ g1.re := d1.1
  have r2 : g1.re ≤ g2.re := d2.1
  have hL : ∀ y, LReg nex0.laz y → FG g0 goal y := fun y hy => by
    rcases gr1 y (gregL_goal.mpr hy) with e | e
    · exact Or.inr e
    · exact Or.inl e
  have dR : DF (FG g0 goal) g2 { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } :=
    df_gen rfl (by show g2.re ≤ g2.re + 1 + 1; omega)
  have hQp : FG g0 goal pro := by
    rcases hpro with e | e
    · exact Or.inl (by omega)
    · exact hL pro e
  obtain ⟨d3, -, e3⟩ := df_emit (blobWr_one (Q := FG g0 goal) (p := Pole.nok g2.re (g2.re + 1) pro) (fun x hx => by
    simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact hQp) _) h3
  have e3' : g3.re = g2.re + 1 + 1 := e3
  obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) hq hp
    (fun y hy => Or.inl (by have := lReg_ofSure.mp hy; simp only [lazyReg, NMem] at this; omega))
    (fun y hy => Or.inl (by have := lReg_ofSure.mp hy; simp only [lazyReg, NMem] at this; omega))
    (fun y hy => Or.inl (by omega)) h4 h5 h6 h7
  refine ⟨(d1.mono fun _ h => h.elim).trans ((d2.mono fun y hy => ?_).trans (dR.trans (d3.trans dC))),
    fun y hy => ?_⟩
  · rcases hy with e | e
    · exact Or.inl (by omega)
    · exact hL y e
  · rcases lC y (gregL_goal.mp hy) with e | e
    · exact Or.inr e
    · exact Or.inl e

end Raw
end SkaModel
end Formalization
