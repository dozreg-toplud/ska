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

/-! ## A formula the analysis knows, on a subject of the code requirement -/

/-- **The static condition** of a sock-annotated noun `[S σ]` within a
function on the subject sock `T`: at each part that comes from an axis of
the subject, `S` knows no more than `T` there. -/
def StatS (T S : Sock) (σ : Noun) : Prop :=
  ∀ π b, springAt σ π = A b → b ≠ 0 → ∃ q, axisPath b = some q ∧ PosLe (sockAt T q) (sockAt S π)

/-- Where the provenance is a cell, the sock may stand for a cell. -/
def ShapeOK (S : Sock) (σ : Noun) : Prop :=
  ∀ π, isCellN (springAt σ π) = true → Cellish (sockAt S π)

theorem slotO_eq_cell {o : Option Noun} {a b : Noun} (h1 : slotO o [false] = some a)
    (h2 : slotO o [true] = some b) : o = some (C a b) := by
  cases o with
  | none => cases h1
  | some n =>
    cases n with
    | atom _ => simp [slotO, slotAtPath] at h1
    | cell x y =>
      simp [slotO, slotAtPath] at h1 h2
      rw [h1, h2]

theorem fitsOpt_yes {F : Noun} {o : Option Noun} (h : FitsOpt (Sock.mk Cape.yes F) o) : o = some F := by
  cases o with
  | none => obtain ⟨_, _, e, hn⟩ := h; cases e; simp [Cape.isNo] at hn
  | some n => simp only [FitsOpt, Fits, FitsCape] at h; rw [h]

/-- **A part that the analysis knows fully is the same on every subject of
the code requirement**, if `want` covers its provenance: for a product `p`
satisfying the invariant on a subject `x` of `app:ca W bus`, with the static
condition and the shape condition, wherever the sock knows the part as `F`,
the part is `F`. -/
theorem known_part {x p : Noun} {bus S : Sock} {σ : Noun} {W : Cape}
    (hp : ProvO x S σ (some p)) (hst : StatS bus S σ) (hsh : ShapeOK S σ)
    (hX : Fits (Ca.app W bus) x) (hW : ∀ q, (distribute Cape.yes σ).Has q → W.Has q) :
    ∀ σ' π F, springAt σ π = σ' → sockAt S π = Sock.mk Cape.yes F → slotAtPath p π = some F := by
  intro σ'
  induction σ' with
  | atom b =>
    intro π F e hs
    by_cases hb : b = 0
    · subst hb
      have := hp.const π e
      rw [hs] at this
      exact fitsOpt_yes this
    · obtain ⟨q, hq, hle⟩ := hst π b e hb
      have hx := hp.exact π b e hb
      have h1 : FitsOpt (sockAt (Ca.app W bus) q) (slotO (some x) q) := fitsOpt_sockAt q hX
      have h2 := fitsOpt_app_part q W bus _ (fun r => hW _ (distribute_has σ Cape.yes π r b q trivial e hb hq)) h1
      have h3 := hle [] _ h2
      rw [show sockAt (sockAt S π) [] = sockAt S π from rfl, hs] at h3
      have h4 := fitsOpt_yes h3
      rw [show slotAtPath p π = slotO (some p) π from rfl, hx]
      simpa [slot?, hq, slotO] using h4
  | cell h t ih1 ih2 =>
    intro π F e hs
    have hc := hsh π (by rw [e]; rfl)
    rw [hs] at hc
    cases F with
    | atom _ => exact absurd hc id
    | cell F1 F2 =>
      have a1 := ih1 (π ++ [false]) F1 (by rw [springAt_app, e]; rfl) (by rw [sockAt_app, hs]; rfl)
      have a2 := ih2 (π ++ [true]) F2 (by rw [springAt_app, e]; rfl) (by rw [sockAt_app, hs]; rfl)
      rw [slotAtPath_app] at a1 a2
      exact slotO_eq_cell a1 a2

/-- **A formula the analysis knows is the formula on every subject of the
code requirement**: the use at a direct or an inlined call, where `want`
records `distribute & src` of the formula's product. -/
theorem known_formula {x p F : Noun} {bus : Sock} {σ : Noun} {W : Cape}
    (hp : ProvO x (Sock.mk Cape.yes F) σ (some p)) (hst : StatS bus (Sock.mk Cape.yes F) σ)
    (hsh : ShapeOK (Sock.mk Cape.yes F) σ) (hX : Fits (Ca.app W bus) x)
    (hW : ∀ q, (distribute Cape.yes σ).Has q → W.Has q) : p = F := by
  have := known_part hp hst hsh hX hW σ [] F rfl rfl
  simpa [slotAtPath] using this

end SkaModel
end Formalization
