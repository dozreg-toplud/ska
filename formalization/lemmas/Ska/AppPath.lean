import lemmas.Ska.ProvFacts

/-!
# `+app:ca` along a path that the mask covers

`fitsOpt_app_part`: below a path that the mask `W` covers entirely, a noun
of `app:ca W s` fits what `s` itself says there.  This is how a subject of a
function's code requirement `app:ca want bus` gives the parts that `want`
records exactly as `bus` knows them.
-/

namespace Formalization
namespace SkaModel

open Nock

theorem fitsOpt_void_false {o : Option Noun} (h : FitsOpt Sock.void o) : False := by
  cases o with
  | none => exact Sock.Blank.not_void h
  | some n => exact h

theorem has_nil_yes {c : Cape} (h : c.Has []) : c = Cape.yes := by
  cases c with
  | yes => rfl
  | no => exact absurd h id
  | cell _ _ => exact absurd h id

theorem knit_blank_inv {A B : Sock} (h : (So.knit A B).Blank) : A.Blank ∧ B.Blank := by
  cases A with
  | void => exact absurd h (by simp [So.knit]; exact Sock.Blank.not_void)
  | mk l d1 =>
    cases B with
    | void => exact absurd h (by simp [So.knit]; exact Sock.Blank.not_void)
    | mk r d2 =>
      simp only [So.knit] at h
      split at h
      · rename_i hc
        unfold Ca.con at hc
        split at hc
        · rename_i hh
          obtain ⟨rfl, rfl⟩ := hh
          exact ⟨⟨_, _, rfl, rfl⟩, ⟨_, _, rfl, rfl⟩⟩
        · cases hc
      · rename_i hc
        obtain ⟨c, d, he, hn⟩ := h
        cases he
        rw [con_ne_no hc] at hn
        simp only [Cape.isNo, Bool.and_eq_true] at hn
        exact ⟨⟨_, _, rfl, hn.1⟩, ⟨_, _, rfl, hn.2⟩⟩

theorem app_void (c : Cape) : Ca.app c Sock.void = Sock.void := by
  unfold Ca.app; rfl

theorem app_ne_void : ∀ (c : Cape) {s : Sock}, s ≠ Sock.void → Ca.app c s ≠ Sock.void := by
  intro c
  induction c with
  | yes =>
    intro s hs
    cases s with
    | void => exact absurd rfl hs
    | mk cs d => simp only [Ca.app]; split <;> (try split) <;> simp_all [Sock.dunno]
  | no =>
    intro s hs
    cases s with
    | void => exact absurd rfl hs
    | mk cs d => simp only [Ca.app]; split <;> (try split) <;> simp_all [Sock.dunno]
  | cell ch ct ih1 ih2 =>
    intro s hs
    cases s with
    | void => exact absurd rfl hs
    | mk cs d =>
      simp only [Ca.app]
      split
      · simp
      · split
        · simp [Sock.dunno]
        · exact knit_ne_void (ih1 (hed_ne_void hs)) (ih2 (tel_ne_void hs))

theorem hed_tel_knit {A B : Sock} (hA : A ≠ Sock.void) (hB : B ≠ Sock.void) (hn : ¬ (So.knit A B).Blank) :
    So.hed (So.knit A B) = A ∧ So.tel (So.knit A B) = B := by
  cases A with
  | void => exact absurd rfl hA
  | mk l d1 =>
    cases B with
    | void => exact absurd rfl hB
    | mk r d2 =>
      simp only [So.knit] at hn ⊢
      split
      · rename_i hc; rw [if_pos hc] at hn; exact absurd ⟨_, _, rfl, rfl⟩ hn
      · rename_i hc
        rw [con_ne_no hc]
        exact ⟨rfl, rfl⟩

/-- Where the mask covers a path entirely and the masked sock knows nothing,
the sock knows nothing there. -/
theorem app_blank_part : ∀ (q : List Bool) (c : Cape) (t : Sock), (Ca.app c t).Blank →
    (∀ r, c.Has (q ++ r)) → (sockAt t q).Blank := by
  intro q
  induction q with
  | nil =>
    intro c t hb hc
    have := has_nil_yes (by simpa using hc [])
    subst this
    cases t with
    | void => exact absurd hb (by simp [Ca.app]; exact Sock.Blank.not_void)
    | mk cs d =>
      simp only [Ca.app] at hb
      split at hb
      · exact hb
      · split at hb
        · rename_i h1 h2
          rcases h2 with h2 | h2
          · cases h2
          · subst h2; exact ⟨_, _, rfl, rfl⟩
        · exact hb
  | cons b q ih =>
    intro c t hb hc
    cases t with
    | void => exact absurd hb (by simp [Ca.app]; exact Sock.Blank.not_void)
    | mk cs d =>
      unfold Ca.app at hb
      split at hb
      · exact sockAt_blank _ hb
      · split at hb
        · rename_i h1 h2
          rcases h2 with h2 | h2
          · subst h2; exact absurd (hc []) id
          · subst h2; exact sockAt_blank _ ⟨_, _, rfl, rfl⟩
        · cases c with
          | yes => exact sockAt_blank _ hb
          | no => exact absurd (hc []) id
          | cell ch ct =>
            obtain ⟨h1, h2⟩ := knit_blank_inv hb
            cases b
            · exact ih ch _ h1 (fun r => hc r)
            · exact ih ct _ h2 (fun r => hc r)

/-- **Below a path that the mask covers entirely, `+app:ca` keeps what the
sock knows.** -/
theorem fitsOpt_app_part : ∀ (q : List Bool) (W : Cape) (s : Sock) (o : Option Noun),
    (∀ r, W.Has (q ++ r)) → FitsOpt (sockAt (Ca.app W s) q) o → FitsOpt (sockAt s q) o := by
  intro q
  induction q with
  | nil =>
    intro W s o hW h
    have := has_nil_yes (by simpa using hW [])
    subst this
    cases s with
    | void => exact absurd h (fun h => fitsOpt_void_false h)
    | mk cs d =>
      simp only [sockAt, Ca.app] at h ⊢
      split at h
      · exact h
      · split at h
        · rename_i h1 h2
          rcases h2 with h2 | h2
          · cases h2
          · subst h2; exact fitsOpt_blank ⟨_, _, rfl, rfl⟩ o
        · exact h
  | cons b q ih =>
    intro W s o hW h
    cases s with
    | void => exact absurd h (fun h => fitsOpt_void_false (by rw [app_void, sockAt_void] at h; exact h))
    | mk cs d =>
      unfold Ca.app at h
      split at h
      · exact h
      · split at h
        · rename_i h1 h2
          rcases h2 with h2 | h2
          · subst h2; exact absurd (hW []) id
          · subst h2; exact fitsOpt_blank (sockAt_blank _ ⟨_, _, rfl, rfl⟩) o
        · cases W with
          | yes => exact h
          | no => exact absurd (hW []) id
          | cell wh wt =>
            simp only at h
            have hA := app_ne_void wh (hed_ne_void (s := Sock.mk cs d) (by simp))
            have hB := app_ne_void wt (tel_ne_void (s := Sock.mk cs d) (by simp))
            by_cases hk : (So.knit (Ca.app wh (So.hed (Sock.mk cs d))) (Ca.app wt (So.tel (Sock.mk cs d)))).Blank
            · obtain ⟨h1, h2⟩ := knit_blank_inv hk
              apply fitsOpt_blank
              cases b
              · exact app_blank_part q wh _ h1 (fun r => hW r)
              · exact app_blank_part q wt _ h2 (fun r => hW r)
            · obtain ⟨eh, et⟩ := hed_tel_knit hA hB hk
              cases b
              · have h' : FitsOpt (sockAt (So.hed (So.knit _ _)) q) o := h
                rw [eh] at h'
                exact ih wh _ o (fun r => hW r) h'
              · have h' : FitsOpt (sockAt (So.tel (So.knit _ _)) q) o := h
                rw [et] at h'
                exact ih wt _ o (fun r => hW r) h'

end SkaModel
end Formalization
