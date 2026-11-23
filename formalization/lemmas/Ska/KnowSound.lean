import lemmas.Ska.Know
import lemmas.Ska.NommAgree
import lemmas.Ska.FolLoopFacts

/-!
# `+know` is sound

`knowGo_sound`: if a nomm stands for a formula on the subjects of `P`
(`Annot`, with the code table `code` of the analysis), then on every set `Q`
of subjects in `P` that fit the sock `+know` starts from, the nomm that
`knowGo` folds stands for the same formula (`Annot` again, with the table
`code'` of the variants that `res` names), and the product sock that `knowGo`
gives fits every product of the original nomm.

It assumes of `dat` that a code bell's datum's product, patched for what a
site knows, fits every product of the callee on a subject that fits both its
code requirement and the site's sock (`DatOK`), and of `res` that the
variant it names for a site has the callee's formula and a nomm in `code'`,
and is fitted by every subject that fits both the callee's code requirement
and the site's sock (`ResOK`, for the sites `knowGo` lists).

Each fold of `+know` drops a computation, and the Hoon checks it is safe
(`+safe-nomm`) where it must: a folded nomm that is safe is total
(`annot_safe_total`), so the dropped computation returns, and its value is
the one the sock knows.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Bake

section MinkParts

variable {lib : Lib} {gul : Noun}

theorem mink_mk_n3 {x b p : Noun} (h : Mink lib gul [] x b (Tone.zero p)) :
    Mink lib gul [] x (n2 (A 3) b) (Tone.zero (wut p)) := by
  obtain ⟨n, e⟩ := h
  exact ⟨n + 1, by rw [minkF_succ_eq]; simp only [minkStep, e, tbind_zero]⟩

theorem mink_mk_n4 {x b : Noun} {a : Nat} (h : Mink lib gul [] x b (Tone.zero (A a))) :
    Mink lib gul [] x (n2 (A 4) b) (Tone.zero (A (a + 1))) := by
  obtain ⟨n, e⟩ := h
  exact ⟨n + 1, by rw [minkF_succ_eq]; simp only [minkStep, e, tbind_zero]⟩

theorem mink_mk_n5 {x b c p q : Noun} (h1 : Mink lib gul [] x b (Tone.zero p))
    (h2 : Mink lib gul [] x c (Tone.zero q)) :
    Mink lib gul [] x (n3 (A 5) b c) (Tone.zero (eqCode p q)) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero, minkF_lift (Nat.le_max_right _ _) e2, tbind_zero]

theorem mink_mk_six0 {x b c d p : Noun} (h1 : Mink lib gul [] x b (Tone.zero (A 0)))
    (h2 : Mink lib gul [] x c (Tone.zero p)) : Mink lib gul [] x (n4 (A 6) b c d) (Tone.zero p) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero]
  exact minkF_lift (Nat.le_max_right _ _) e2

theorem mink_mk_six1 {x b c d p : Noun} (h1 : Mink lib gul [] x b (Tone.zero (A 1)))
    (h2 : Mink lib gul [] x d (Tone.zero p)) : Mink lib gul [] x (n4 (A 6) b c d) (Tone.zero p) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero]
  exact minkF_lift (Nat.le_max_right _ _) e2

theorem mink_mk_n7 {x b c z p : Noun} (h1 : Mink lib gul [] x b (Tone.zero z))
    (h2 : Mink lib gul [] z c (Tone.zero p)) : Mink lib gul [] x (n3 (A 7) b c) (Tone.zero p) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero]
  exact minkF_lift (Nat.le_max_right _ _) e2

theorem mink_mk_n8 {x b c z p : Noun} (h1 : Mink lib gul [] x b (Tone.zero z))
    (h2 : Mink lib gul [] (C z x) c (Tone.zero p)) : Mink lib gul [] x (n3 (A 8) b c) (Tone.zero p) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero]
  exact minkF_lift (Nat.le_max_right _ _) e2

theorem mink_mk_n9 {x c core p : Noun} {axis : Nat} (h1 : Mink lib gul [] x c (Tone.zero core))
    (h2 : Mink lib gul [] core (n3 (A 2) (slot 1) (slot axis)) (Tone.zero p)) :
    Mink lib gul [] x (n3 (A 9) (A axis) c) (Tone.zero p) := by
  obtain ⟨y, g, hy, hg, h3⟩ := mink_inv_n2 h2
  have ey := mink_inv_n0 hy
  simp only [slot?_one, Option.some.injEq] at ey
  subst ey
  have eg := mink_inv_n0 hg
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n3, e3⟩ := h3
  refine ⟨max n1 n3 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero]
  simp only [eg]
  exact minkF_lift (Nat.le_max_right _ _) e3

theorem mink_mk_n10 {x v t a b u : Noun} {axis : Nat} (hax : axis ≠ 0)
    (h1 : Mink lib gul [] x v (Tone.zero a)) (h2 : Mink lib gul [] x t (Tone.zero b))
    (he : edit? axis a b = some u) :
    Mink lib gul [] x (n3 (A 10) (n2 (A axis) v) t) (Tone.zero u) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep, hax, if_false]
  rw [minkF_lift (Nat.le_max_right _ _) e2, tbind_zero, minkF_lift (Nat.le_max_left _ _) e1, tbind_zero]
  simp only [he]

end MinkParts

/-! ## A sock that knows a part whole, and Nock 0 -/

theorem pullLoop_isNo : ∀ (axe : Nat) (c : Cape) (d : Noun), c.isNo = true →
    known (So.pullLoop c d axe) = none := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d hc
  rw [So.pullLoop.eq_def]
  split
  · simp [known, isNo_all hc]
  · rename_i hax
    have h2 : 2 ≤ axe := by omega
    have hlt := mas_lt axe h2
    split
    · rfl
    · rename_i hcno
      split
      · rfl
      · split
        · rename_i ch ct
          simp only [Cape.isNo, Bool.and_eq_true] at hc
          split
          · exact ih _ hlt _ _ hc.1
          · exact ih _ hlt _ _ hc.2
        · split <;> exact ih _ hlt _ _ hc

theorem pullLoop_slot : ∀ (axe : Nat) (c : Cape) (d n v : Noun), 1 ≤ axe → FitsCape c d n →
    known (So.pullLoop c d axe) = some v → slot? axe n = some v := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d n v h1 hf hk
  rw [So.pullLoop.eq_def] at hk
  split at hk
  · have : axe = 1 := by omega
    subst this
    simp only [known] at hk
    split at hk
    · cases hk
      rw [slot?_one, all_fits (by assumption) hf]
    · cases hk
  · rename_i hax
    have h2 : 2 ≤ axe := by omega
    have hlt := mas_lt axe h2
    have hpos := mas_pos axe h2
    split at hk
    · simp [known, Sock.dunno, Ca.all] at hk
    · rename_i hcno
      split at hk
      · simp [known, Sock.dunno, Ca.all] at hk
      · rename_i dh dt
        rw [slot?_cap h2]
        split at hk
        · rename_i ch ct
          simp only [FitsCape] at hf
          rcases hf with hno | ⟨dh', dt', nh, nt, hd, rfl, fh, ft⟩
          · simp only [Bool.and_eq_true] at hno
            exfalso
            by_cases hc : cap axe = 2
            · simp only [hc, if_true] at hk
              rw [pullLoop_isNo (mas axe) ch dh hno.1] at hk
              cases hk
            · simp only [hc, if_false] at hk
              rw [pullLoop_isNo (mas axe) ct dt hno.2] at hk
              cases hk
          · cases hd
            by_cases hc : cap axe = 2
            · simp only [hc, if_true] at hk ⊢
              exact ih _ hlt _ _ _ _ hpos fh hk
            · simp only [hc, if_false] at hk ⊢
              exact ih _ hlt _ _ _ _ hpos ft hk
        · rename_i hnc
          cases c with
          | no => exact absurd rfl hcno
          | cell ch ct => exact absurd rfl (hnc ch ct)
          | yes =>
            simp only [FitsCape] at hf
            subst hf
            by_cases hc : cap axe = 2
            · simp only [hc, if_true] at hk ⊢
              exact ih _ hlt Cape.yes _ _ _ hpos (show FitsCape Cape.yes dh dh from rfl) hk
            · simp only [hc, if_false] at hk ⊢
              exact ih _ hlt Cape.yes _ _ _ hpos (show FitsCape Cape.yes dt dt from rfl) hk

/-- **A part that a sock knows whole is there**: Nock 0 at that axis returns
it on every noun of the sock. -/
theorem pull_known {s s' : Sock} {axe : Nat} {n v : Noun} (hf : Fits s n)
    (hp : So.pull s axe = some s') (hk : known s' = some v) : slot? axe n = some v := by
  unfold So.pull at hp
  split at hp
  · simp at hp
  · rename_i hax
    cases s with
    | void => exact absurd hf id
    | mk c d =>
      simp only [Option.some.injEq] at hp
      subst hp
      exact pullLoop_slot axe c d n v (by omega) hf hk

theorem known_fits {s : Sock} {v y : Noun} (hk : known s = some v) (hf : Fits s y) : y = v := by
  cases s with
  | void => exact absurd hf id
  | mk c d =>
    simp only [known] at hk
    split at hk
    · cases hk; exact all_fits (by assumption) hf
    · cases hk

/-! ## Safe and literal nomms -/

/-- **A safe nomm is total**: on every subject, its formula returns. -/
theorem annot_safe_total {lib : Lib} {code : Bell → Option Nomm} :
    ∀ {Q f n}, Annot lib code Q f n → safeNomm n = true →
      ∀ x gul, Q x → ∃ y, Mink lib gul [] x f (Tone.zero y) := by
  intro Q f n h
  induction h with
  | cons _ _ ih1 ih2 =>
    intro hs x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hs
    obtain ⟨y1, h1⟩ := ih1 hs.1 x gul hx
    obtain ⟨y2, h2⟩ := ih2 hs.2 x gul hx
    exact ⟨_, mink_mk_cons h1 h2⟩
  | n1 => intro _ x gul _; exact ⟨_, mink_mk_n1 x _⟩
  | fold hv => intro _ x gul hx; exact ⟨_, hv x gul hx⟩
  | six0 hb _ ih =>
    intro hs x gul hx
    obtain ⟨y, h⟩ := ih hs x gul hx
    exact ⟨y, mink_mk_six0 (hb x gul hx) h⟩
  | six1 hb _ ih =>
    intro hs x gul hx
    obtain ⟨y, h⟩ := ih hs x gul hx
    exact ⟨y, mink_mk_six1 (hb x gul hx) h⟩
  | n11s _ ih =>
    intro hs x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hs
    obtain ⟨y, h⟩ := ih hs.2 x gul hx
    exact ⟨y, mink_mk_n11s _ h⟩
  | n11d _ _ ih1 ih2 =>
    intro hs x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hs
    obtain ⟨c, h1⟩ := ih1 hs.1.2 x gul hx
    obtain ⟨y, h2⟩ := ih2 hs.2 x gul hx
    exact ⟨y, mink_mk_n11d _ h1 h2⟩
  | mean _ _ ih1 ih2 =>
    intro hs x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hs
    obtain ⟨c, h1⟩ := ih1 hs.1 x gul hx
    obtain ⟨y, h2⟩ := ih2 hs.2 x gul hx
    exact ⟨y, mink_mk_n11d _ h1 h2⟩
  | memo hh _ ih =>
    intro hs x gul hx
    obtain ⟨y, h⟩ := ih hs x gul hx
    exact ⟨y, (mink_memo_iff (hh x gul hx)).mpr h⟩
  | _ => intro hs; simp [safeNomm] at hs

/-- **A literal nomm's formula returns the literal.** -/
theorem annot_lit {lib : Lib} {code : Bell → Option Nomm} :
    ∀ {Q f n}, Annot lib code Q f n → ∀ v, n = Nomm.n1 v → ∀ x gul, Q x → Mink lib gul [] x f (Tone.zero v) := by
  intro Q f n h
  induction h with
  | n1 => intro v hv x gul _; cases hv; exact mink_mk_n1 x _
  | fold hv' => intro v hv x gul hx; cases hv; exact hv' x gul hx
  | six0 hb _ ih => intro v hv x gul hx; exact mink_mk_six0 (hb x gul hx) (ih v hv x gul hx)
  | six1 hb _ ih => intro v hv x gul hx; exact mink_mk_six1 (hb x gul hx) (ih v hv x gul hx)
  | memo hh _ ih => intro v hv x gul hx; exact (mink_memo_iff (hh x gul hx)).mpr (ih v hv x gul hx)
  | _ => intro v hv; cases hv

/-! ## The sites only grow -/

theorem knowGo_suffix (fold : Bool) (dat : Bell → Option Datum) (res : Bell → Sock → Option Bell) :
    ∀ (nm : Nomm) (sub : Anno) (st : List Site) (r : (Nomm × Anno) × List Site),
      knowGo fold dat res nm sub st = some r → st <:+ r.2 := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r', hr, h⟩ := h
    have := (ihp _ _ _ hl).trans (ihq _ _ _ hr)
    split at h <;> (cases h; exact this)
  | n0 p =>
    intro sub st r h
    simp only [knowGo] at h
    split at h
    · cases h; exact List.suffix_refl _
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h <;> (cases h; exact List.suffix_refl _)
  | n1 p => intro sub st r h; simp only [knowGo, Option.some.injEq] at h; cases h; exact List.suffix_refl _
  | n2 p q info ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, f, hf, h⟩ := h
    have := (ihp _ _ _ hs).trans (ihq _ _ _ hf)
    split at h
    · cases h; exact this
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      cases h; exact this.trans (List.suffix_cons _ _)
  | n3 p ih =>
    intro sub st r h
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨r', hr, h⟩ := h
    have := ih _ _ _ hr
    split at h <;> (cases h; exact this)
  | n4 p ih =>
    intro sub st r h
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨r', hr, h⟩ := h
    have := ih _ _ _ hr
    split at h <;> (cases h; exact this)
  | n5 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have := (ihp _ _ _ ha).trans (ihq _ _ _ hb)
    split at h <;> (cases h; exact this)
  | n6 p q r ihp ihq ihr =>
    intro sub st out h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    have h1 := ihp _ _ _ ha
    split at h
    · exact h1.trans (ihq _ _ _ h)
    · exact h1.trans (ihr _ _ _ h)
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, c, hc, h⟩ := h
      have := h1.trans ((ihq _ _ _ hb).trans (ihr _ _ _ hc))
      cases h
      exact this
  | n7 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have := (ihp _ _ _ ha).trans (ihq _ _ _ hb)
    split at h <;> (cases h; exact this)
  | n10 ax v q ihv ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have := (ihv _ _ _ ha).trans (ihq _ _ _ hb)
    split at h
    · cases h; exact this
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      cases h; exact this
  | n11s tag q body ih =>
    intro sub st r h
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    have := ih _ _ _ ha
    split at h <;> (cases h; exact this)
  | n11d tag hh q body ihh ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have := (ihh _ _ _ ha).trans (ihq _ _ _ hb)
    split at h <;> (cases h; exact this)
  | n12 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have := (ihp _ _ _ ha).trans (ihq _ _ _ hb)
    cases h
    exact this
  | mean p b q body k ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, v, _, c, hc, h⟩ := h
    have := (ihp _ _ _ ha).trans ((List.suffix_cons _ _).trans (ihq _ _ _ hc))
    cases h
    exact this

end Bake

end SkaModel
end Formalization
