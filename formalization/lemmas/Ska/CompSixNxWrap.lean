import lemmas.Ska.CompSixNxS

/-!
# `[6 c a b]` under `%next`: the result is the plain one, wrapped

README Gaps 12.36.  In phases S and F the result of `%6` is `+copy` of the
test's flat result with `+past-fork` of the fork of the branches.  The
wrapping of `+past-fork` only wraps fork sides (`pastFork_unwraps`), and
`+copy` of a flat need with a need without bonds takes that need's forks as
they are (`copyLazyL_flatFirst`), so the run with the wrapped fork and the
run with the plain fork reach the same state, the first result `Unwraps` to
the second (`copyL_unwraps`).  So `RunOKLT` of a `%6` is `RunOKLS` of the
run with the plain fork, which is the run a call-free test makes
(`sixNextSimpleC_plain` for phase S).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem forall2_wrap (F : List (ForkE S)) :
    Forall2 (fun (e e' : ForkE S) => WrapSide e.1 e'.1 ∧ WrapSide e.2 e'.2)
      (F.map fun e => ((e.1.1, mk Sure.bunt [] [(e.1.1, e.1.2)]), (e.2.1, mk Sure.bunt [] [(e.2.1, e.2.2)]))) F := by
  induction F with
  | nil => exact Forall2.nil
  | cons e F ih => exact Forall2.cons ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩ ih

/-- **`+past-fork` only wraps fork sides.** -/
theorem pastFork_unwraps {cod : Bell → Option Bool} {lz lw : Lazy S} {p : Nomm} (h : pastFork cod lz p = some lw) :
    Unwraps lw lz := by
  unfold pastFork at h
  split at h
  · cases h
  · cases h; exact unwraps_refl _
  · cases h; exact ⟨rfl, rfl, forall2_wrap _⟩

/-- **`+copy` of a fork-free need with a need without bonds** keeps the
second need's forks as they are. -/
theorem copyLazyL_flatFirst (o : Nat) (s1 : Sure S) (b1 : List (Nat × Lazy S)) {w : Lazy S} (hb : w.bond = []) :
    (copyLazyL o (mk s1 [] b1) w : CM Map (Lazy S)) = (do
      let (ned, ops) ← copyNeed s1.ned w.sure.ned []
      addOps o ops
      pure (mk ⟨ned, HoonSet.uni s1.lok w.sure.lok⟩ w.fork b1)) := by
  rcases w with ⟨s, F, B⟩
  simp only [bond_mk] at hb
  subst hb
  cases F <;> simp [copyLazyL]

/-- **`+copy` of the wrapped need and of the plain one**: the same state,
the same jump, the first result unwrapping to the second. -/
theorem copyL_unwraps {xc : NextL S} {w u : Lazy S} (hf : xc.laz.fork = []) (hw : Unwraps w u) (hb : u.bond = [])
    {g g' : Gen Map} {nex : NextL S} (h : copyL xc w g = some (nex, g')) :
    ∃ nexU : NextL S, copyL xc u g = some (nexU, g') ∧ nexU.th = nex.th ∧ Unwraps nex.laz nexU.laz := by
  obtain ⟨hs, hbw, hF⟩ := hw
  rcases xc with ⟨⟨s1, f1, b1⟩, th⟩
  simp only [fork_mk] at hf
  subst hf
  unfold copyL at h ⊢
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨laz, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [copyLazyL_flatFirst o s1 b1 (hbw.trans hb)] at h2
  obtain ⟨⟨ned, ops⟩, g3, h3, h2⟩ := bind_some h2
  obtain ⟨_, g4, h4, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  refine ⟨⟨mk ⟨ned, HoonSet.uni s1.lok u.sure.lok⟩ u.fork b1, jmp0 o⟩, ?_, rfl, ⟨by simp [hs], rfl, hF⟩⟩
  simp only [bind_apply, h1, Option.bind_some, copyLazyL_flatFirst o s1 b1 hb, ← hs, h3, h4, pure_apply]

/-- **Phase S with the plain fork**: the run taken apart as in
`sixNextSimpleC_apart`, and its result unwraps to `+copy` of the test's
result with the plain fork `lz` of `+sect`, in the same final state, when
the test's result has no fork and the plain fork no bond. -/
theorem sixNextSimpleC_plain {cod : Bell → Option Bool} {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)}
    {p : Nomm} {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (h : sixNextSimpleC cod rp rq rr p laz th region g0 = some (nex, g9)) :
    ∃ (s0 s1 : Sure S) (x1 x0 xc : NextL S) (lz lw : Lazy S) (yes nuh : Nat) (gF gR gQ gS gC : Gen Map),
      forkSure laz.sure th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 1 + 1 } = some ((s0, s1), gF) ∧
      rr (CGoalL.next (ofSure s1) (jmp0 (g0.bo + 1))) (gF.id :: region) { gF with id := gF.id + 1 } =
        some (x1, gR) ∧
      rq (CGoalL.next (ofSure s0) (jmp0 g0.bo)) (gF.id :: region) gR = some (x0, gQ) ∧
      sect x0 x1 g0.bo (g0.bo + 1) (gF.id :: region) gF.cond gR.cond gQ = some ((lz, yes, nuh), gS) ∧
      pastFork cod lz p = some lw ∧
      rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region gS = some (xc, gC) ∧
      (lazyBig lw = false → xc.laz.fork = [] → lz.bond = [] →
        ∃ nexU : NextL S, copyL xc lz gC = some (nexU, g9) ∧ nexU.th = nex.th ∧ Unwraps nex.laz nexU.laz) := by
  obtain ⟨s0, s1, x1, x0, xc, lz, lw, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hw, hC, hk⟩ :=
    sixNextSimpleC_apart h
  exact ⟨s0, s1, x1, x0, xc, lz, lw, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hw, hC,
    fun hb hf hlb => copyL_unwraps hf (pastFork_unwraps hw) hlb (hk hb)⟩

end Comp
end SkaModel
end Formalization
