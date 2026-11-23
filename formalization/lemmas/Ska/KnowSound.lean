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

/-! ## The soundness of `+know` -/

section Sound

variable {lib : Lib} {code code' : Bell → Option Nomm} {fold : Bool} {dat : Bell → Option Datum}
  {res : Bell → Sock → Option Bell} {stF : List Site}

/-- What `+know` needs of a code bell's datum: its product, patched for what
a site knows, fits every product of the callee on a subject that fits both
the code requirement and the site's sock. -/
def DatOK (lib : Lib) (dat : Bell → Option Datum) : Prop :=
  ∀ b d, dat b = some d → ∀ (k : Sock) s y gul, Fits b.less s → Fits k s →
    Mink lib gul [] s b.fol (Tone.zero y) → Fits (patchProd d.prod d.map k).sock y

/-- What `+know` needs of `res` on the sites `stF`: the variant has the
callee's formula and a nomm in `code'`, and every subject that fits both the
callee's code requirement and the site's sock fits it. -/
def ResOK (code' : Bell → Option Nomm) (res : Bell → Sock → Option Bell) (stF : List Site) : Prop :=
  ∀ b k v, (b, k) ∈ stF → res b k = some v →
    v.fol = b.fol ∧ (∃ nb, code' v = some nb) ∧ ∀ y, Fits b.less y → Fits k y → Fits v.less y

/-- **What `+know` gives**: the folded nomm stands for the formula on `Q`
with the table `code'`, and the product sock fits every product of the
original nomm (with the table `code`) on `Q`. -/
def KnowOK (lib : Lib) (code code' : Bell → Option Nomm) (Q : Noun → Prop) (f : Noun) (nm : Nomm)
    (out : Nomm × Anno) : Prop :=
  Annot lib code' Q f out.1 ∧
    ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x nm = some (Tone.zero y) → Fits out.2.sock y

theorem nommF_succ_inv {gul : Noun} {m : Nat} {t : Trace} {x : Noun} {nm : Nomm} {r : Tone}
    (h : nommF lib gul code m t x nm = some r) :
    ∃ m', m = m' + 1 ∧ nommStep lib gul code (nommF lib gul code m') (minkF lib gul m') t x nm = some r := by
  cases m with
  | zero => simp [nommF] at h
  | succ m' => exact ⟨m', rfl, h⟩

theorem nomm_mink (hc : CodeOK lib code) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hA : Annot lib code P f nm) {x : Noun} (hx : P x) {gul : Noun} {t : Trace} {m : Nat} {y : Noun}
    (h : nommF lib gul code m t x nm = some (Tone.zero y)) : Mink lib gul [] x f (Tone.zero y) := by
  obtain ⟨n, hn⟩ := (nomm_agree lib gul code hc hA hx t _).mpr ⟨m, h⟩
  exact ⟨n, mink_nil_of_zero hn⟩

theorem mink_nomm (hc : CodeOK lib code) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hA : Annot lib code P f nm) {x : Noun} (hx : P x) {gul y : Noun}
    (h : Mink lib gul [] x f (Tone.zero y)) : ∃ m, nommF lib gul code m [] x nm = some (Tone.zero y) :=
  (nomm_agree lib gul code hc hA hx [] _).mp h

theorem lit_eq {n : Nomm} {v : Noun} (h : lit n = some v) : n = Nomm.n1 v := by
  cases n <;> simp [lit] at h
  subst h; rfl

/-- The value of an original nomm whose fold is the literal `v` is `v`. -/
theorem lit_val (hc : CodeOK lib code) {P Q : Noun → Prop} {f : Noun} {p : Nomm} {v : Noun}
    (hA : Annot lib code P f p) (hQP : ∀ x, Q x → P x) (hl : Annot lib code' Q f (Nomm.n1 v))
    {x gul : Noun} {t : Trace} {m : Nat} {y : Noun} (hx : Q x)
    (h : nommF lib gul code m t x p = some (Tone.zero y)) : y = v := by
  obtain ⟨n, hn⟩ := nomm_mink hc hA (hQP x hx) h
  have := mink_det_zero (annot_lit hl v rfl x gul hx) hn
  cases this; rfl

/-- A safe folded nomm whose sock is known: its formula returns the known
value on every subject. -/
theorem safe_known (hc : CodeOK lib code) {P Q : Noun → Prop} {b : Noun} {p : Nomm} {out : Nomm × Anno}
    {d : Noun} (hA : Annot lib code P b p) (hQP : ∀ x, Q x → P x) (hk : KnowOK lib code code' Q b p out)
    (hs : safeNomm out.1 = true) (hkn : known out.2.sock = some d) :
    ∀ x gul, Q x → Mink lib gul [] x b (Tone.zero d) := by
  intro x gul hx
  obtain ⟨y, hy⟩ := annot_safe_total hk.1 hs x gul hx
  obtain ⟨m, hm⟩ := mink_nomm hc hA (hQP x hx) hy
  have := known_fits hkn (hk.2 x hx gul [] m y hm)
  subst this; exact hy

theorem fits_dunno' (y : Noun) : Fits Anno.dunno.sock y := fits_dunno y

theorem fits_litAnno {v y : Noun} (h : y = v) : Fits (litAnno v).sock y := h

theorem wut_eq (d : Noun) : wut d = A (if isCellN d = true then 0 else 1) := by
  cases d <;> rfl

theorem eqCode_eq (p q : Noun) : eqCode p q = A (if p = q then 0 else 1) := by
  unfold eqCode; split <;> rfl

/-- `knowGo` on Nock 0: the sites are kept, and the read is the original or
its literal. -/
theorem knowGo_n0 {sub : Anno} {st : List Site} {axis : Nat} {r : (Nomm × Anno) × List Site}
    (h : knowGo fold dat res (Nomm.n0 axis) sub st = some r) {Q : Noun → Prop}
    (hQ : ∀ x, Q x → Fits sub.sock x) :
    r.2 = st ∧ KnowOK lib code code' Q (slot axis) (Nomm.n0 axis) r.1 ∧
      (r.1.1 = Nomm.n0 axis ∨ ∃ d, r.1.1 = Nomm.n1 d ∧ ∀ x, Q x → slot? axis x = some d) := by
  have hslot : ∀ {x gul t m y}, nommF lib gul code m t x (Nomm.n0 axis) = some (Tone.zero y) →
      slot? axis x = some y := by
    intro x gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    split at hm'
    · cases hm'
    · rename_i p hp; cases hm'; exact hp
  simp only [knowGo] at h
  split at h
  · cases h
    exact ⟨rfl, ⟨Annot.n0, fun _ _ _ _ _ _ _ => fits_dunno _⟩, Or.inl rfl⟩
  · rename_i hax
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨prod, hprod, h⟩ := h
    have hfit : ∀ x, Q x → ∀ y, slot? axis x = some y → Fits prod.sock y := by
      intro x hx y hy
      split at hprod
      · cases hprod
        rename_i h1; subst h1
        simp only [slot?_one, Option.some.injEq] at hy
        subst hy; exact hQ x hx
      · simp only [Option.map_eq_some_iff] at hprod
        obtain ⟨s', hs', rfl⟩ := hprod
        exact pull_fits (hQ x hx) hy hs'
    have hkn : ∀ d, known prod.sock = some d → ∀ x, Q x → slot? axis x = some d := by
      intro d hd x hx
      split at hprod
      · cases hprod
        rename_i h1; subst h1
        rw [slot?_one, known_fits hd (hQ x hx)]
      · simp only [Option.map_eq_some_iff] at hprod
        obtain ⟨s', hs', rfl⟩ := hprod
        exact pull_known (hQ x hx) hs' hd
    split at h
    · rename_i d hd
      cases h
      refine ⟨rfl, ⟨Annot.fold fun x gul hx => mink_mk_n0 (hkn d hd x hx), ?_⟩, Or.inr ⟨d, rfl, hkn d hd⟩⟩
      intro x hx gul t m y hm
      exact hfit x hx y (hslot hm)
    · cases h
      exact ⟨rfl, ⟨Annot.n0, fun x hx gul t m y hm => hfit x hx y (hslot hm)⟩, Or.inl rfl⟩

/-- The statement of `knowGo_sound` for one annotation, as an induction
motive. -/
def IHK (lib : Lib) (code code' : Bell → Option Nomm) (fold : Bool) (dat : Bell → Option Datum)
    (res : Bell → Sock → Option Bell) (stF : List Site) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ sub st r, knowGo fold dat res nm sub st = some r → r.2 <:+ stF →
    ∀ Q : Noun → Prop, (∀ x, Q x → P x ∧ Fits sub.sock x) → KnowOK lib code code' Q f nm r.1

/-- The Nock 7 family (`%7`, an inlined `%2`, `%9`): the first nomm gives
the subject of the second. -/
theorem seven_core (hc : CodeOK lib code) {P : Noun → Prop} {f b g : Noun} {p q : Nomm}
    (hA1 : Annot lib code P b p) (hA2 : Annot lib code (Img lib P b) g q)
    (ih1 : IHK lib code code' fold dat res stF P b p)
    (ih2 : IHK lib code code' fold dat res stF (Img lib P b) g q)
    (hmk : ∀ {Q : Noun → Prop} {p' q' : Nomm}, (∀ x, Q x → P x) → Annot lib code' Q b p' →
      Annot lib code' (Img lib Q b) g q' → Annot lib code' Q f (Nomm.n7 p' q'))
    (hfold : ∀ {Q : Noun → Prop}, (∀ x, Q x → P x) → ∀ v x gul z, Q x → Mink lib gul [] x b (Tone.zero z) →
      Mink lib gul [] z g (Tone.zero v) → Mink lib gul [] x f (Tone.zero v)) :
    IHK lib code code' fold dat res stF P f (Nomm.n7 p q) := by
  intro sub st r h hsuf Q hQ
  simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨pp, hp, qq, hq, h⟩ := h
  have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
  have hp2 : pp.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
  have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
  have K1 := ih1 sub st pp hp hp2 Q hQ
  have hQ2 : ∀ z, Img lib Q b z → Img lib P b z ∧ Fits pp.1.2.sock z := by
    rintro z ⟨x, gul, hx, hm⟩
    refine ⟨⟨x, gul, hQP x hx, hm⟩, ?_⟩
    obtain ⟨m, hm'⟩ := mink_nomm hc hA1 (hQP x hx) hm
    exact K1.2 x hx gul [] m z hm'
  have K2 := ih2 pp.1.2 pp.2 qq hq hq2 (Img lib Q b) hQ2
  have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n7 p q) = some (Tone.zero y) →
      ∃ z m', Img lib Q b z ∧ nommF lib gul code m' t z q = some (Tone.zero y) := by
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    obtain ⟨z, hz, hzq⟩ := tbind_zero_inv hm'
    exact ⟨z, m', ⟨x, gul, hx, nomm_mink hc hA1 (hQP x hx) hz⟩, hzq⟩
  split at h
  · rename_i v hv hs
    cases h
    have hl := lit_eq hv
    have K21 := K2.1
    rw [hl] at K21
    refine ⟨?_, ?_⟩
    · show Annot lib code' Q f qq.1.1
      rw [hl]
      refine Annot.fold fun x gul hx => ?_
      obtain ⟨z, hz⟩ := annot_safe_total K1.1 hs x gul hx
      exact hfold hQP v x gul z hx hz (annot_lit K21 v rfl z gul ⟨x, gul, hx, hz⟩)
    · intro x hx gul t m y hm
      obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
      exact fits_litAnno (lit_val hc hA2 (fun z hz => (hQ2 z hz).1) K21 hz hzq)
  · cases h
    refine ⟨hmk hQP K1.1 K2.1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
    exact K2.2 z hz gul t m' y hzq

theorem slot1_eq {lib : Lib} {gul x w : Noun} (h : Mink lib gul [] x (slot 1) (Tone.zero w)) : w = x := by
  have e := mink_inv_n0 h
  simp only [slot?_one, Option.some.injEq] at e
  exact e.symm

/-- `%8` and the forms `+know` gives it: the pushed pair `[b 0 1]`, as a
cons of two nomms or folded whole. -/
theorem n8_core (hc : CodeOK lib code) {P : Noun → Prop} {b c : Noun} {p r' q : Nomm}
    (hA1 : Annot lib code P b p) (hA2 : Annot lib code P (slot 1) r')
    (hA3 : Annot lib code (Img8 lib P b) c q)
    (ih1 : IHK lib code code' fold dat res stF P b p)
    (ih2 : IHK lib code code' fold dat res stF P (slot 1) r')
    (ih3 : IHK lib code code' fold dat res stF (Img8 lib P b) c q) :
    IHK lib code code' fold dat res stF P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p r') q) := by
  intro sub st r h hsuf Q hQ
  simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨pp, ⟨l, hl, r0, hr0, hcons⟩, qq, hq, h⟩ := h
  have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
  have hcases : (∃ x1 x2, lit l.1.1 = some x1 ∧ lit r0.1.1 = some x2 ∧
      pp = ((Nomm.n1 (C x1 x2), litAnno (C x1 x2)), r0.2)) ∨
      pp = ((Nomm.cons l.1.1 r0.1.1, ⟨So.knit l.1.2.sock r0.1.2.sock, Pi.cons l.1.2.src r0.1.2.src⟩), r0.2) := by
    split at hcons
    · rename_i x1 x2 h1 h2
      exact Or.inl ⟨_, _, h1, h2, (Option.some.inj hcons).symm⟩
    · exact Or.inr (Option.some.inj hcons).symm
  have hpp : pp.2 = r0.2 := by rcases hcases with ⟨_, _, _, _, rfl⟩ | rfl <;> rfl
  have hpq : pp.2 <:+ qq.2 := knowGo_suffix fold dat res q _ _ _ hq
  have hr02 : r0.2 <:+ stF := hpp ▸ hpq.trans hq2
  have hl2 : l.2 <:+ stF := (knowGo_suffix fold dat res r' _ _ _ hr0).trans hr02
  have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
  have K1 := ih1 sub st l hl hl2 Q hQ
  have K0 := ih2 sub l.2 r0 hr0 hr02 Q hQ
  have hself : ∀ x, Q x → ∀ gul t m w, nommF lib gul code m t x r' = some (Tone.zero w) → w = x :=
    fun x hx gul t m w hm => slot1_eq (nomm_mink hc hA2 (hQP x hx) hm)
  have hself' : ∀ x, Q x → ∀ gul, ∃ m, nommF lib gul code m [] x r' = some (Tone.zero x) :=
    fun x hx gul => mink_nomm hc hA2 (hQP x hx) (mink_mk_n0 (slot?_one x))
  have hQ2 : ∀ z, Img8 lib Q b z → Img8 lib P b z ∧ Fits pp.1.2.sock z := by
    rintro z ⟨x, y, gul, hx, hy, rfl⟩
    refine ⟨⟨x, y, gul, hQP x hx, hy, rfl⟩, ?_⟩
    rcases hcases with ⟨x1, x2, h1, h2, rfl⟩ | rfl
    · have e1 := Mink.det hy (annot_lit K1.1 x1 (lit_eq h1) x gul hx)
      cases e1
      have e2 := slot1_eq (annot_lit K0.1 x2 (lit_eq h2) x gul hx)
      exact fits_litAnno (by rw [e2])
    · obtain ⟨m, hm⟩ := mink_nomm hc hA1 (hQP x hx) hy
      obtain ⟨m', hm'⟩ := hself' x hx gul
      exact knit_fits (K1.2 x hx gul [] m y hm) (K0.2 x hx gul [] m' x hm')
  have K3 := ih3 pp.1.2 pp.2 qq hq hq2 (Img8 lib Q b) hQ2
  have hsem : ∀ x, Q x → ∀ gul t m y,
      nommF lib gul code m t x (Nomm.n7 (Nomm.cons p r') q) = some (Tone.zero y) →
      ∃ z m', Img8 lib Q b z ∧ nommF lib gul code m' t z q = some (Tone.zero y) := by
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    obtain ⟨z, hz, hzq⟩ := tbind_zero_inv hm'
    obtain ⟨m'', rfl, hz'⟩ := nommF_succ_inv hz
    simp only [nommStep] at hz'
    obtain ⟨u, hu, hz'⟩ := tbind_zero_inv hz'
    obtain ⟨w, hw, hz'⟩ := tbind_zero_inv hz'
    cases hz'
    have hwx := hself x hx gul t m'' w hw
    subst hwx
    exact ⟨_, m'' + 1, ⟨_, u, gul, hx, nomm_mink hc hA1 (hQP _ hx) hu, rfl⟩, hzq⟩
  split at h
  · rename_i v hv hs
    cases h
    have K31 := K3.1
    rw [lit_eq hv] at K31
    refine ⟨?_, ?_⟩
    · show Annot lib code' Q (n3 (A 8) b c) qq.1.1
      rw [lit_eq hv]
      refine Annot.fold fun x gul hx => ?_
      have hb : ∃ z, Mink lib gul [] x b (Tone.zero z) := by
        rcases hcases with ⟨x1, x2, h1, h2, rfl⟩ | rfl
        · exact ⟨x1, annot_lit K1.1 x1 (lit_eq h1) x gul hx⟩
        · simp only [safeNomm, Bool.and_eq_true] at hs
          exact annot_safe_total K1.1 hs.1 x gul hx
      obtain ⟨z, hz⟩ := hb
      exact mink_mk_n8 hz (annot_lit K31 v rfl _ gul ⟨x, z, gul, hx, hz, rfl⟩)
    · intro x hx gul t m y hm
      obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
      exact fits_litAnno (lit_val hc hA3 (fun z hz => (hQ2 z hz).1) K31 hz hzq)
  · cases h
    refine ⟨?_, ?_⟩
    · show Annot lib code' Q (n3 (A 8) b c) (Nomm.n7 pp.1.1 qq.1.1)
      rcases hcases with ⟨x1, x2, h1, h2, rfl⟩ | rfl
      · refine Annot.n8l (fun x gul hx => ⟨annot_lit K1.1 x1 (lit_eq h1) x gul hx, ?_⟩) K3.1
        exact (slot1_eq (annot_lit K0.1 x2 (lit_eq h2) x gul hx)).symm
      · exact Annot.n8g K1.1 K0.1 K3.1
    · intro x hx gul t m y hm
      obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
      exact K3.2 z hz gul t m' y hzq

end Sound

end Bake

end SkaModel
end Formalization
