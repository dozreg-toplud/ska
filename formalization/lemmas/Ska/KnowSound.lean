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

/-- **`+know` is sound.**  If a nomm stands for a formula on the subjects of
`P` with the analysis' table `code`, then on every set `Q` of subjects in
`P` that fit the sock `+know` starts from, the nomm `knowGo` folds stands for
the same formula with the variants' table `code'`, and its product sock fits
every product of the original nomm (`KnowOK`). -/
theorem knowGo_sound (hc : CodeOK lib code) (hdat : DatOK lib dat) (hres : ResOK code' res stF) :
    ∀ {P f nm}, Annot lib code P f nm → IHK lib code code' fold dat res stF P f nm := by
  intro P f nm hA
  induction hA with
  | cons hA1 hA2 ih1 ih2 =>
    rename_i P a1 a2 b p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r', hr, h⟩ := h
    have hr2 : r'.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hl2 : l.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hr).trans hr2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st l hl hl2 Q hQ
    have K2 := ih2 sub l.2 r' hr hr2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.cons p q) = some (Tone.zero y) →
        ∃ m' u w, nommF lib gul code m' t x p = some (Tone.zero u) ∧
          nommF lib gul code m' t x q = some (Tone.zero w) ∧ y = C u w := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨u, hu, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨w, hw, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', u, w, hu, hw, rfl⟩
    split at h
    · rename_i x1 x2 h1 h2
      cases h
      have K11 := K1.1
      rw [lit_eq h1] at K11
      have K21 := K2.1
      rw [lit_eq h2] at K21
      refine ⟨Annot.fold fun x gul hx =>
        mink_mk_cons (annot_lit K11 x1 rfl x gul hx) (annot_lit K21 x2 rfl x gul hx), ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', u, w, hu, hw, rfl⟩ := hsem x hx gul t m y hm
      exact fits_litAnno (by rw [lit_val hc hA1 hQP K11 hx hu, lit_val hc hA2 hQP K21 hx hw])
    · cases h
      refine ⟨Annot.cons K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', u, w, hu, hw, rfl⟩ := hsem x hx gul t m y hm
      exact knit_fits (K1.2 x hx gul t m' u hu) (K2.2 x hx gul t m' w hw)
  | n0 =>
    intro sub st r h hsuf Q hQ
    exact (knowGo_n0 h (fun x hx => (hQ x hx).2)).2.1
  | n1 =>
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.some.injEq] at h
    cases h
    refine ⟨Annot.n1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep, Option.some.injEq, Tone.zero.injEq] at hm'
    exact fits_litAnno hm'.symm
  | indirect hA1 hA2 ih1 ih2 =>
    rename_i P b c p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨s, hs, fq, hf, rfl⟩ := h
    have hs2 : s.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hf).trans hsuf
    exact ⟨Annot.indirect (ih1 sub st s hs hs2 Q hQ).1 (ih2 sub s.2 fq hf hsuf Q hQ).1,
      fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | direct hA1 hA2 hcode hy hg ih1 ih2 =>
    rename_i P b c p q bl k nb
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, fq, hf, v, hv, rfl⟩ := h
    have hmem : (bl, s.1.2.sock) ∈ stF := hsuf.subset List.mem_cons_self
    obtain ⟨hvf, ⟨nb', hnb'⟩, hvfit⟩ := hres bl s.1.2.sock v hmem hv
    have hf2 : fq.2 <:+ stF := (List.suffix_cons _ _).trans hsuf
    have hs2 : s.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hf).trans hf2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st s hs hs2 Q hQ
    have K2 := ih2 sub s.2 fq hf hf2 Q hQ
    refine ⟨Annot.direct K1.1 K2.1 hnb' (fun x gul y hx hm => hvfit y (hy x gul y (hQP x hx) hm) ?_)
      (fun x gul g hx hm => (hg x gul g (hQP x hx) hm).trans hvf.symm), ?_⟩
    · obtain ⟨m, hm'⟩ := mink_nomm hc hA1 (hQP x hx) hm
      exact K1.2 x hx gul [] m y hm'
    · intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨s', hs', hm'⟩ := tbind_zero_inv hm'
      obtain ⟨g, hg', hm'⟩ := tbind_zero_inv hm'
      rw [hcode, Option.bind_some] at hm'
      dsimp only
      split
      · exact fits_dunno _
      · rename_i d hd
        have hsfit : Fits bl.less s' := hy x gul s' (hQP x hx) (nomm_mink hc hA1 (hQP x hx) hs')
        have hk : Fits s.1.2.sock s' := K1.2 x hx gul t m' s' hs'
        exact hdat bl d hd s.1.2.sock s' y gul hsfit hk (nomm_mink hc (hc bl nb hcode) hsfit hm')
  | inline hA1 htot hA2 ih1 ih2 =>
    exact seven_core hc hA1 hA2 ih1 ih2
      (fun hQP a1 a2 => Annot.inline a1 (fun x gul hx => htot x gul (hQP x hx)) a2)
      (fun hQP _ x gul _ hx hz hzv => mink_mk_n2 hz (htot x gul (hQP x hx)) hzv)
  | n3 hA1 ih1 =>
    rename_i P b p
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have hp2 : pp.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n3 p) = some (Tone.zero y) →
        ∃ m' z, nommF lib gul code m' t x p = some (Tone.zero z) ∧ y = wut z := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', z, hz, rfl⟩
    split at h
    · rename_i d hd hs
      cases h
      refine ⟨Annot.fold fun x gul hx => ?_, ?_⟩
      · rw [← wut_eq]; exact mink_mk_n3 (safe_known hc hA1 hQP K1 hs hd x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', z, hz, rfl⟩ := hsem x hx gul t m y hm
        rw [known_fits hd (K1.2 x hx gul t m' z hz)]
        exact fits_litAnno (wut_eq d)
    · cases h
      exact ⟨Annot.n3 K1.1, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | n4 hA1 ih1 =>
    rename_i P b p
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have hp2 : pp.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n4 p) = some (Tone.zero y) →
        ∃ m' a, nommF lib gul code m' t x p = some (Tone.zero (A a)) ∧ y = A (a + 1) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases z with
      | cell _ _ => cases hm'
      | atom a => cases hm'; exact ⟨m', a, hz, rfl⟩
    split at h
    · rename_i a hd hs
      cases h
      refine ⟨Annot.fold fun x gul hx => mink_mk_n4 (safe_known hc hA1 hQP K1 hs hd x gul hx), ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', a', hz, rfl⟩ := hsem x hx gul t m y hm
      have e := known_fits hd (K1.2 x hx gul t m' _ hz)
      cases e
      exact fits_litAnno rfl
    · cases h
      exact ⟨Annot.n4 K1.1, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | n5 hA1 hA2 ih1 ih2 =>
    rename_i P b c p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hp2 : pp.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have K2 := ih2 sub pp.2 qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n5 p q) = some (Tone.zero y) →
        ∃ m' u w, nommF lib gul code m' t x p = some (Tone.zero u) ∧
          nommF lib gul code m' t x q = some (Tone.zero w) ∧ y = eqCode u w := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨u, hu, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨w, hw, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', u, w, hu, hw, rfl⟩
    split at h
    · rename_i dp dq hdp hsp hdq hsq
      cases h
      refine ⟨Annot.fold fun x gul hx => ?_, ?_⟩
      · rw [← eqCode_eq]
        exact mink_mk_n5 (safe_known hc hA1 hQP K1 hsp hdp x gul hx) (safe_known hc hA2 hQP K2 hsq hdq x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', u, w, hu, hw, rfl⟩ := hsem x hx gul t m y hm
        rw [known_fits hdp (K1.2 x hx gul t m' u hu), known_fits hdq (K2.2 x hx gul t m' w hw)]
        exact fits_litAnno (eqCode_eq dp dq)
    · cases h
      exact ⟨Annot.n5 K1.1 K2.1, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | n6 hA1 hA2 hA3 ih1 ih2 ih3 =>
    rename_i P b c d p q r0
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n6 p q r0) = some (Tone.zero y) →
        ∃ m' z, nommF lib gul code m' t x p = some (Tone.zero z) ∧
          ((z = A 0 ∧ nommF lib gul code m' t x q = some (Tone.zero y)) ∨
            (z = A 1 ∧ nommF lib gul code m' t x r0 = some (Tone.zero y))) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      refine ⟨m', z, hz, ?_⟩
      match z, hm' with
      | Noun.atom 0, hm' => exact Or.inl ⟨rfl, hm'⟩
      | Noun.atom 1, hm' => exact Or.inr ⟨rfl, hm'⟩
      | Noun.atom (k + 2), hm' => cases hm'
      | Noun.cell _ _, hm' => cases hm'
    split at h
    · rename_i hd hs
      have hq2 := h
      have hp2 : pp.2 <:+ stF := (knowGo_suffix _ dat res q _ _ _ h).trans hsuf
      have K1 := ih1 sub st pp hp hp2 Q hQ
      have K2 := ih2 sub pp.2 r h hsuf Q hQ
      refine ⟨Annot.six0 (safe_known hc hA1 hQP K1 hs hd) K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', z, hz, ⟨rfl, hzq⟩ | ⟨rfl, _⟩⟩ := hsem x hx gul t m y hm
      · exact K2.2 x hx gul t m' y hzq
      · cases known_fits hd (K1.2 x hx gul t m' _ hz)
    · rename_i hd hs
      have hp2 : pp.2 <:+ stF := (knowGo_suffix _ dat res r0 _ _ _ h).trans hsuf
      have K1 := ih1 sub st pp hp hp2 Q hQ
      have K3 := ih3 sub pp.2 r h hsuf Q hQ
      refine ⟨Annot.six1 (safe_known hc hA1 hQP K1 hs hd) K3.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', z, hz, ⟨rfl, _⟩ | ⟨rfl, hzr⟩⟩ := hsem x hx gul t m y hm
      · cases known_fits hd (K1.2 x hx gul t m' _ hz)
      · exact K3.2 x hx gul t m' y hzr
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨qq, hq, rr, hr, rfl⟩ := h
      have hr2 : rr.2 <:+ stF := hsuf
      have hq2 : qq.2 <:+ stF := (knowGo_suffix _ dat res r0 _ _ _ hr).trans hr2
      have hp2 : pp.2 <:+ stF := (knowGo_suffix _ dat res q _ _ _ hq).trans hq2
      have K1 := ih1 sub st pp hp hp2 Q hQ
      have K2 := ih2 sub pp.2 qq hq hq2 Q hQ
      have K3 := ih3 sub qq.2 rr hr hr2 Q hQ
      refine ⟨Annot.n6 K1.1 K2.1 K3.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', z, hz, ⟨_, hzq⟩ | ⟨_, hzr⟩⟩ := hsem x hx gul t m y hm
      · exact doubleInt_fits_left _ _ (K2.2 x hx gul t m' y hzq)
      · exact doubleInt_fits_right _ _ (K3.2 x hx gul t m' y hzr)
  | n7 hA1 hA2 ih1 ih2 =>
    exact seven_core hc hA1 hA2 ih1 ih2 (fun _ a1 a2 => Annot.n7 a1 a2)
      (fun _ _ _ _ _ _ hz hzv => mink_mk_n7 hz hzv)
  | n8 hA1 hA2 ih1 ih2 =>
    refine n8_core hc hA1 Annot.n0 hA2 ih1 ?_ ih2
    intro sub st r h hsuf Q hQ
    exact (knowGo_n0 h (fun x hx => (hQ x hx).2)).2.1
  | n9 hA1 hA2 ih1 ih2 =>
    exact seven_core hc hA1 hA2 ih1 ih2 (fun _ a1 a2 => Annot.n9 a1 a2)
      (fun _ _ _ _ _ _ hz hzv => mink_mk_n9 hz hzv)
  | n10 hax hA1 hA2 ih1 ih2 =>
    rename_i P axis v t0 p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨dn, hdn, rc, hrc, h⟩ := h
    have hrc2 : rc.2 <:+ stF := by
      split at h
      · cases h; exact hsuf
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        exact hsuf
    have hdn2 : dn.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hrc).trans hrc2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st dn hdn hdn2 Q hQ
    have K2 := ih2 sub dn.2 rc hrc hrc2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n10 axis p q) = some (Tone.zero y) →
        ∃ m' a b, nommF lib gul code m' t x p = some (Tone.zero a) ∧
          nommF lib gul code m' t x q = some (Tone.zero b) ∧ edit? axis a b = some y := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep, hax, if_false] at hm'
      obtain ⟨b, hb, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨a, ha, hm'⟩ := tbind_zero_inv hm'
      split at hm'
      · cases hm'
      · rename_i u hu
        cases hm'
        exact ⟨m', a, b, ha, hb, hu⟩
    split at h
    · rename_i u hu
      cases h
      -- the literal: both parts are literals and the edit succeeds
      revert hu
      split
      · rename_i x1 x2 h1 h2
        intro hu
        have K11 := K1.1
        rw [lit_eq h1] at K11
        have K21 := K2.1
        rw [lit_eq h2] at K21
        refine ⟨Annot.fold fun x gul hx =>
          mink_mk_n10 hax (annot_lit K11 x1 rfl x gul hx) (annot_lit K21 x2 rfl x gul hx) hu, ?_⟩
        intro x hx gul t m y hm
        obtain ⟨m', a, b, ha, hb, he⟩ := hsem x hx gul t m y hm
        rw [lit_val hc hA1 hQP K11 hx ha, lit_val hc hA2 hQP K21 hx hb, hu] at he
        exact fits_litAnno (Option.some.inj he).symm
      · intro hu; cases hu
    · rename_i hl
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨s', hs', rfl⟩ := h
      refine ⟨Annot.n10 hax K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', a, b, ha, hb, he⟩ := hsem x hx gul t m y hm
      exact darn_fits (K2.2 x hx gul t m' b hb) (K1.2 x hx gul t m' a ha) he hs'
  | n11s hA1 ih1 =>
    rename_i P tag q f0
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n11s tag q f0) = some (Tone.zero y) →
        ∃ m', nommF lib gul code m' t x q = some (Tone.zero y) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', hz⟩
    split at h
    · rename_i v hfree hv
      cases h
      have K11 := K1.1
      rw [lit_eq hv] at K11
      refine ⟨?_, ?_⟩
      · show Annot lib code' Q _ qq.1.1
        rw [lit_eq hv]
        exact Annot.fold fun x gul hx => mink_mk_n11s tag (annot_lit K11 v rfl x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', hm'⟩ := hsem x hx gul t m y hm
        exact fits_litAnno (lit_val hc hA1 hQP K11 hx hm')
    · cases h
      refine ⟨Annot.n11s K1.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', hm'⟩ := hsem x hx gul t m y hm
      exact K1.2 x hx gul t m' y hm'
  | n11d hA1 hA2 ih1 ih2 =>
    rename_i P tag h0 f0 p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨hh, hhh, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hh2 : hh.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st hh hhh hh2 Q hQ
    have K2 := ih2 sub hh.2 qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n11d tag p q f0) = some (Tone.zero y) →
        ∃ m' t', nommF lib gul code m' t' x q = some (Tone.zero y) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨c0, _, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', _, hz⟩
    split at h
    · rename_i v hfree hs hv
      cases h
      have K21 := K2.1
      rw [lit_eq hv] at K21
      refine ⟨?_, ?_⟩
      · show Annot lib code' Q _ qq.1.1
        rw [lit_eq hv]
        refine Annot.fold fun x gul hx => ?_
        obtain ⟨c0, hc0⟩ := annot_safe_total K1.1 hs x gul hx
        exact mink_mk_n11d tag hc0 (annot_lit K21 v rfl x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', t', hm'⟩ := hsem x hx gul t m y hm
        exact fits_litAnno (lit_val hc hA2 hQP K21 hx hm')
    · cases h
      refine ⟨Annot.n11d K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', t', hm'⟩ := hsem x hx gul t m y hm
      exact K2.2 x hx gul t' m' y hm'
  | mean hA1 hA2 ih1 ih2 =>
    rename_i P h0 f0 p q b k
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, v, hv, qq, hq, rfl⟩ := h
    have hp2 : pp.2 <:+ stF :=
      (List.suffix_cons _ _).trans ((knowGo_suffix fold dat res q _ _ _ hq).trans hsuf)
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have K2 := ih2 sub _ qq hq hsuf Q hQ
    refine ⟨Annot.mean K1.1 K2.1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    obtain ⟨c0, _, hm'⟩ := tbind_zero_inv hm'
    obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
    cases hm'
    exact K2.2 x hx gul _ m' _ hz
  | n12 hA1 hA2 ih1 ih2 =>
    rename_i P b c p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, rfl⟩ := h
    have hp2 : pp.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hsuf
    exact ⟨Annot.n12 (ih1 sub st pp hp hp2 Q hQ).1 (ih2 sub pp.2 qq hq hsuf Q hQ).1,
      fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | bare hb =>
    rename_i P f0
    intro sub st r h hsuf Q hQ
    have e2 : knowGo fold dat res (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f0) none) sub st =
        (knowGo fold dat res (Nomm.n0 1) sub st).bind fun s =>
          (knowGo fold dat res (Nomm.n1 f0) sub s.2).bind fun fq =>
            some ((Nomm.n2 s.1.1 fq.1.1 none, Anno.dunno), fq.2) := rfl
    rw [e2] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨s, hs, fq, hf, rfl⟩ := h
    obtain ⟨_, _, hshape⟩ := knowGo_n0 (lib := lib) (code := code) (code' := code') hs (Q := Q) (fun x hx => (hQ x hx).2)
    simp only [knowGo, Option.some.injEq] at hf
    cases hf
    refine ⟨?_, fun _ _ _ _ _ _ _ => fits_dunno _⟩
    rcases hshape with e | ⟨d, e, hd⟩
    · show Annot lib code' Q f0 (Nomm.n2 s.1.1 (Nomm.n1 f0) none)
      rw [e]; exact Annot.bare hb
    · show Annot lib code' Q f0 (Nomm.n2 s.1.1 (Nomm.n1 f0) none)
      rw [e]
      exact Annot.bareLit hb fun x hx => by
        have := hd x hx
        simp only [slot?_one, Option.some.injEq] at this
        exact this
  | memo hh hA1 ih1 =>
    intro sub st r h hsuf Q hQ
    have hQP : ∀ x, Q x → _ := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st r h hsuf Q hQ
    exact ⟨Annot.memo (fun x gul hx => hh x gul (hQP x hx)) K1.1, K1.2⟩
  | crash hcr =>
    intro sub st r h hsuf Q hQ
    simp only [knowGo, if_true, Option.some.injEq] at h
    cases h
    exact ⟨Annot.crash hcr, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | fold hv =>
    rename_i P f0 v
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.some.injEq] at h
    cases h
    refine ⟨Annot.fold fun x gul hx => hv x gul (hQ x hx).1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep, Option.some.injEq, Tone.zero.injEq] at hm'
    exact fits_litAnno hm'.symm
  | six0 hb hA1 ih1 =>
    intro sub st r h hsuf Q hQ
    have K1 := ih1 sub st r h hsuf Q hQ
    exact ⟨Annot.six0 (fun x gul hx => hb x gul (hQ x hx).1) K1.1, K1.2⟩
  | six1 hb hA1 ih1 =>
    intro sub st r h hsuf Q hQ
    have K1 := ih1 sub st r h hsuf Q hQ
    exact ⟨Annot.six1 (fun x gul hx => hb x gul (hQ x hx).1) K1.1, K1.2⟩
  | n8g hA1 hA2 hA3 ih1 ih2 ih3 => exact n8_core hc hA1 hA2 hA3 ih1 ih2 ih3
  | n8l hb hA1 ih1 =>
    rename_i P b c y d q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    obtain ⟨pp, rfl, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have hQ2 : ∀ z, Img8 lib Q b z → Img8 lib P b z ∧ Fits (litAnno (C y d)).sock z := by
      rintro z ⟨x, y', gul, hx, hy, rfl⟩
      refine ⟨⟨x, y', gul, hQP x hx, hy, rfl⟩, ?_⟩
      obtain ⟨hby, hxd⟩ := hb x gul (hQP x hx)
      cases Mink.det hy hby
      exact fits_litAnno (by rw [hxd])
    have K1 := ih1 _ _ qq hq hq2 (Img8 lib Q b) hQ2
    have hsem : ∀ x, Q x → ∀ gul t m v, nommF lib gul code m t x (Nomm.n7 (Nomm.n1 (C y d)) q) =
        some (Tone.zero v) → ∃ m', Img8 lib Q b (C y d) ∧ nommF lib gul code m' t (C y d) q = some (Tone.zero v) := by
      intro x hx gul t m v hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hzq⟩ := tbind_zero_inv hm'
      obtain ⟨m'', rfl, hz'⟩ := nommF_succ_inv hz
      simp only [nommStep, Option.some.injEq, Tone.zero.injEq] at hz'
      subst hz'
      obtain ⟨hby, hxd⟩ := hb x gul (hQP x hx)
      exact ⟨_, ⟨x, y, gul, hx, hby, by rw [hxd]⟩, hzq⟩
    split at h
    · rename_i v hv hs
      cases h
      have K11 := K1.1
      rw [lit_eq hv] at K11
      refine ⟨?_, ?_⟩
      · show Annot lib code' Q _ qq.1.1
        rw [lit_eq hv]
        refine Annot.fold fun x gul hx => ?_
        obtain ⟨hby, hxd⟩ := hb x gul (hQP x hx)
        exact mink_mk_n8 hby (annot_lit K11 v rfl _ gul ⟨x, y, gul, hx, hby, rfl⟩)
      · intro x hx gul t m w hm
        obtain ⟨m', hz, hzq⟩ := hsem x hx gul t m w hm
        exact fits_litAnno (lit_val hc hA1 (fun z hz => (hQ2 z hz).1) K11 hz hzq)
    · cases h
      refine ⟨Annot.n8l (fun x gul hx => hb x gul (hQP x hx)) K1.1, ?_⟩
      intro x hx gul t m w hm
      obtain ⟨m', hz, hzq⟩ := hsem x hx gul t m w hm
      exact K1.2 _ hz gul t m' w hzq
  | bareLit hb hd =>
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨s, rfl, fq, rfl, rfl⟩ := h
    exact ⟨Annot.bareLit hb fun x hx => hd x (hQ x hx).1, fun _ _ _ _ _ _ _ => fits_dunno _⟩

end Sound

end Bake

end SkaModel
end Formalization
