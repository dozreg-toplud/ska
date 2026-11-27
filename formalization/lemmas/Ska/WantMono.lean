import lemmas.Ska.FolLoop
import lemmas.Ska.CapeFacts

/-!
# `want` only grows along a run of `fol-loop`

`folLoopF_want_mono`: every path that the code requirement `want` covers
before a run of the model of `fol-loop` it still covers after.  The relative
soundness of `fol-loop` needs this to pass from the `want` of a part of a
run to the `want` of the whole run, which is what the entry records.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- `want` covers no fewer paths in `g'` than in `g`. -/
def WantLe (g g' : Gen) : Prop := ∀ p, g.want.Has p → g'.want.Has p

theorem WantLe.refl (g : Gen) : WantLe g g := fun _ h => h

theorem WantLe.trans {g1 g2 g3 : Gen} (h1 : WantLe g1 g2) (h2 : WantLe g2 g3) : WantLe g1 g3 :=
  fun p h => h2 p (h1 p h)

theorem WantLe.uni {g g' : Gen} {c : Cape} (h : g'.want = Ca.uni g.want c) : WantLe g g' :=
  fun p hp => by rw [h, uni_has]; exact Or.inl hp

/-- Every run of the recursion keeps what `want` covers. -/
def GoMono (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') → WantLe gen gen'

theorem callStep_mono {tab : Tab} {go : FolGo} (IH : GoMono go) {mk : Option Noun} {bc df : Bool}
    {s f : FolOut} {gen gen' : Gen} {out : FolOut}
    (h : callStep tab go mk bc df s f gen = some (out, gen')) : WantLe gen gen' := by
  unfold callStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact WantLe.refl _
  · split at h
    · split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨i, g3⟩, hi, _, rfl⟩ := h
        exact (WantLe.uni (g' := { gen with want := Ca.uni gen.want _ }) rfl).trans
          (IH _ _ _ _ _ _ _ _ hi)
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨d, _, h⟩ := h
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact WantLe.uni rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact fun _ h => h

theorem meanArm_mono {go : FolGo} (IH : GoMono go) {tag : Nat} {h : FolOut} {mk : Option Noun}
    {bc : Bool} {gen : Gen} {r : Option (Bell × Option Noun) × Gen}
    (hm : meanArm go tag h mk bc gen = some r) : WantLe gen r.2 := by
  unfold meanArm at hm
  split at hm
  · simp only [Option.some.injEq] at hm; subst hm; exact WantLe.refl _
  · simp only [Option.bind_eq_some_iff] at hm
    obtain ⟨bat, _, hm⟩ := hm
    split at hm
    · simp only [Option.bind_eq_some_iff] at hm
      obtain ⟨cg, hcg, hm⟩ := hm
      split at hm
      · simp only [Option.some.injEq] at hm; subst hm; exact IH _ _ _ _ _ _ _ _ hcg
      · cases hm
    · simp only [Option.some.injEq] at hm; subst hm; exact WantLe.refl _

theorem folStep_mono {tab : Tab} {go : FolGo} (IH : GoMono go) : GoMono (folStep tab go) := by
  intro fol sub mk bc df gen out gen' h
  unfold folStep at h
  split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact WantLe.refl _)
    | skip
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, _, rfl⟩ := h
    exact (IH _ _ _ _ _ _ _ _ h1).trans (IH _ _ _ _ _ _ _ _ h2)
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h; exact WantLe.refl _
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨s, g1⟩, h1, ⟨f, g2⟩, h2, h⟩ := h
    exact (IH _ _ _ _ _ _ _ _ h1).trans ((IH _ _ _ _ _ _ _ _ h2).trans (callStep_mono IH h))
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p, g1⟩, h1, _, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ h1
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p, g1⟩, h1, _, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ h1
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p, g1⟩, h1, ⟨q, g2⟩, h2, _, rfl⟩ := h
    exact (IH _ _ _ _ _ _ _ _ h1).trans (IH _ _ _ _ _ _ _ _ h2)
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p, g1⟩, h1, ⟨q, g2⟩, h2, ⟨r, g3⟩, h3, _, rfl⟩ := h
    exact (IH _ _ _ _ _ _ _ _ h1).trans ((IH _ _ _ _ _ _ _ _ h2).trans (IH _ _ _ _ _ _ _ _ h3))
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p, g1⟩, h1, ⟨q, g2⟩, h2, _, rfl⟩ := h
    exact (IH _ _ _ _ _ _ _ _ h1).trans (IH _ _ _ _ _ _ _ _ h2)
  · exact IH _ _ _ _ _ _ _ _ h
  · exact IH _ _ _ _ _ _ _ _ h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact WantLe.refl _
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, _, _, _, rfl⟩ := h
      exact (IH _ _ _ _ _ _ _ _ h1).trans (IH _ _ _ _ _ _ _ _ h2)
  · split at h
    · exact IH _ _ _ _ _ _ _ _ h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q, g1⟩, h1, _, rfl⟩ := h
      exact IH _ _ _ _ _ _ _ _ h1
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, h1, h⟩ := h
    split at h
    · exact (IH _ _ _ _ _ _ _ _ h1).trans (IH _ _ _ _ _ _ _ _ h)
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨arm, harm, ⟨fr, g3⟩, h3, _, rfl⟩ := h
      exact (IH _ _ _ _ _ _ _ _ h1).trans ((meanArm_mono IH harm).trans (IH _ _ _ _ _ _ _ _ h3))
  · exact IH _ _ _ _ _ _ _ _ h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p, g1⟩, h1, ⟨q, g2⟩, h2, _, rfl⟩ := h
    exact (IH _ _ _ _ _ _ _ _ h1).trans (IH _ _ _ _ _ _ _ _ h2)

/-- **`want` only grows along a run of `fol-loop`.** -/
theorem folLoopF_want_mono (tab : Tab) : ∀ n, GoMono (folLoopF tab n)
  | 0 => fun _ _ _ _ _ _ _ _ h => by cases h
  | n + 1 => folStep_mono (folLoopF_want_mono tab n)

end SkaModel
end Formalization
