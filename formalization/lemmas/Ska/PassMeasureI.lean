import lemmas.Ska.PassMeasureS
import lemmas.Ska.SockNorm

/-!
# `indi` as a number (track F, Gaps 16)

With `less-code`, the product and the map the same, `+run` writes the old
`indi` again or `+lack:ca` of `+msg-ca` of the run's `indi` with the old one,
by `dark` (`runDatum_indi_seek`).  That cape rises in `CapeLe`: `+msg-ca`
rises over the old cape (`capeLe_msgCa`), `+lack:ca` by `dark` is monotone
(`lack_mono`), and the old `indi` is fixed by `+lack:ca` of `dark`
(`runDatum_indi_lack`).  It can gain cells (`|` under a `dark` of `[& |]`
becomes `[| &]`), but only where the old cape or `dark` has them
(`within_lack`, `within_msgCa`): its cells lie in `shU old dark`.

The weight `wB B c` of a cape `c` whose cells lie in a shape `B` falls
strictly as `c` rises in `CapeLe` between normal capes (`wB_step`): `&` weighs
`0`, `|` weighs `topB B`, more than any other cape in `B`, and a cell one more
than its parts.  So `indi` is the number `wB (shU indi dark) indi`, which falls
strictly at every change of the merge (`indi_merge_step`): the shape of the new
cape lies in the old shape, and the weight is monotone in the shape
(`wB_mono_B`).
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## `+con:ca`, `+hed:ca`, `+tel:ca` and `CapeLe` -/

theorem capeNo_of_le {c n : Cape} (h : CapeLe c n) (hn : CapeNo n) : CapeNo c := by
  induction h with
  | no hc _ => exact hc
  | yes _ => cases hn
  | cell _ _ ih1 ih2 =>
    cases hn with
    | cell h1 h2 => exact CapeNo.cell (ih1 h1) (ih2 h2)

theorem con_capeNo {a b : Cape} (ha : CapeNo a) (hb : CapeNo b) : CapeNo (Ca.con a b) := by
  unfold Ca.con
  split
  · exact CapeNo.no
  · exact CapeNo.cell ha hb

theorem con_mono {a b a' b' : Cape} (h1 : CapeLe a a') (h2 : CapeLe b b') :
    CapeLe (Ca.con a b) (Ca.con a' b') := by
  unfold Ca.con
  split
  · exact CapeLe.no CapeNo.no _
  · split
    · rename_i _ e
      obtain ⟨rfl, rfl⟩ := e
      exact CapeLe.no (CapeNo.cell (capeNo_of_le h1 CapeNo.no) (capeNo_of_le h2 CapeNo.no)) _
    · exact CapeLe.cell h1 h2

theorem capeNo_hed {c : Cape} (h : CapeNo c) : CapeNo (Ca.hed c) := by
  cases h with
  | no => exact CapeNo.no
  | cell h1 _ => exact h1

theorem capeNo_tel {c : Cape} (h : CapeNo c) : CapeNo (Ca.tel c) := by
  cases h with
  | no => exact CapeNo.no
  | cell _ h2 => exact h2

theorem capeLe_hed {x y : Cape} (h : CapeLe x y) : CapeLe (Ca.hed x) (Ca.hed y) := by
  cases h with
  | no hc _ => exact CapeLe.no (capeNo_hed hc) _
  | yes _ => exact CapeLe.yes _
  | cell h1 _ => exact h1

theorem capeLe_tel {x y : Cape} (h : CapeLe x y) : CapeLe (Ca.tel x) (Ca.tel y) := by
  cases h with
  | no hc _ => exact CapeLe.no (capeNo_tel hc) _
  | yes _ => exact CapeLe.yes _
  | cell _ h2 => exact h2

/-! ## `+lack:ca` is monotone -/

theorem lack_capeNo : ∀ (d x : Cape), CapeNo x → CapeNo (Ca.lack x d) := by
  intro d
  induction d with
  | yes => intro x _; rw [lack_yes_right]; exact CapeNo.no
  | no => intro x hx; rw [lack_no_right]; exact hx
  | cell bh bT ih1 ih2 =>
    intro x hx
    by_cases e : x = Cape.no
    · rw [e, lack_no_left]; exact CapeNo.no
    rw [lack_cell_right x bh bT e]
    split
    · exact CapeNo.no
    · exact con_capeNo (ih1 _ (capeNo_hed hx)) (ih2 _ (capeNo_tel hx))

theorem lack_self (d : Cape) : CapeNo (Ca.lack d d) := by
  cases d with
  | yes => exact CapeNo.no
  | no => exact CapeNo.no
  | cell bh bT => rw [lack_cell_right _ bh bT (by simp)]; rw [if_pos rfl]; exact CapeNo.no

/-- **`+lack:ca` by a fixed cape is monotone in `CapeLe`.** -/
theorem lack_mono : ∀ (d x y : Cape), CapeLe x y → CapeLe (Ca.lack x d) (Ca.lack y d) := by
  intro d
  induction d with
  | yes => intro x y _; rw [lack_yes_right, lack_yes_right]; exact capeLe_refl _
  | no => intro x y h; rw [lack_no_right, lack_no_right]; exact h
  | cell bh bT ih1 ih2 =>
    intro x y h
    by_cases hx : x = Cape.no
    · rw [hx, lack_no_left]; exact CapeLe.no CapeNo.no _
    by_cases hy : y = Cape.no
    · subst hy
      exact CapeLe.no (lack_capeNo _ _ (capeLe_no_inv h)) _
    rw [lack_cell_right x bh bT hx, lack_cell_right y bh bT hy]
    split
    · exact CapeLe.no CapeNo.no _
    · split
      · rename_i _ ey
        subst ey
        refine CapeLe.no (con_capeNo ?_ ?_) _
        · exact capeNo_of_le (ih1 _ _ (capeLe_hed h)) (lack_self bh)
        · exact capeNo_of_le (ih2 _ _ (capeLe_tel h)) (lack_self bT)
      · exact con_mono (ih1 _ _ (capeLe_hed h)) (ih2 _ _ (capeLe_tel h))

/-! ## Shapes -/

/-- `c` has cells only where `B` has. -/
def Within : Cape → Cape → Prop
  | Cape.cell a b, Cape.cell c d => Within a c ∧ Within b d
  | Cape.cell _ _, _ => False
  | _, _ => True

/-- The union of the cells of two capes. -/
def shU : Cape → Cape → Cape
  | Cape.cell a b, Cape.cell c d => Cape.cell (shU a c) (shU b d)
  | Cape.cell a b, _ => Cape.cell a b
  | _, Cape.cell c d => Cape.cell c d
  | _, _ => Cape.no

theorem within_leaf {c : Cape} (h : ∀ a b, c ≠ Cape.cell a b) (B : Cape) : Within c B := by
  cases c with
  | cell a b => exact absurd rfl (h a b)
  | no => cases B <;> trivial
  | yes => cases B <;> trivial

theorem within_no (B : Cape) : Within Cape.no B := by cases B <;> trivial

theorem within_yes (B : Cape) : Within Cape.yes B := by cases B <;> trivial

theorem within_refl : ∀ c : Cape, Within c c
  | Cape.cell a b => ⟨within_refl a, within_refl b⟩
  | Cape.no => trivial
  | Cape.yes => trivial

theorem within_trans : ∀ {a b c : Cape}, Within a b → Within b c → Within a c
  | Cape.cell _ _, Cape.cell _ _, Cape.cell _ _, h1, h2 => ⟨within_trans h1.1 h2.1, within_trans h1.2 h2.2⟩
  | Cape.cell _ _, Cape.cell _ _, Cape.no, _, h2 => h2.elim
  | Cape.cell _ _, Cape.cell _ _, Cape.yes, _, h2 => h2.elim
  | Cape.cell _ _, Cape.no, _, h1, _ => h1.elim
  | Cape.cell _ _, Cape.yes, _, h1, _ => h1.elim
  | Cape.no, _, c, _, _ => within_no c
  | Cape.yes, _, c, _, _ => within_yes c

theorem within_shU_left : ∀ a b : Cape, Within a (shU a b)
  | Cape.cell a1 a2, Cape.cell _ _ => ⟨within_shU_left a1 _, within_shU_left a2 _⟩
  | Cape.cell a1 a2, Cape.no => within_refl (Cape.cell a1 a2)
  | Cape.cell a1 a2, Cape.yes => within_refl (Cape.cell a1 a2)
  | Cape.no, b => within_no _
  | Cape.yes, b => within_yes _

theorem within_shU_right : ∀ a b : Cape, Within b (shU a b)
  | Cape.cell _ _, Cape.cell b1 b2 => ⟨within_shU_right _ b1, within_shU_right _ b2⟩
  | Cape.cell _ _, Cape.no => trivial
  | Cape.cell _ _, Cape.yes => trivial
  | Cape.no, Cape.cell b1 b2 => within_refl (Cape.cell b1 b2)
  | Cape.yes, Cape.cell b1 b2 => within_refl (Cape.cell b1 b2)
  | Cape.no, Cape.no => trivial
  | Cape.no, Cape.yes => trivial
  | Cape.yes, Cape.no => trivial
  | Cape.yes, Cape.yes => trivial

theorem within_shU_of : ∀ {a b B : Cape}, Within a B → Within b B → Within (shU a b) B
  | Cape.cell _ _, Cape.cell _ _, Cape.cell _ _, h1, h2 => ⟨within_shU_of h1.1 h2.1, within_shU_of h1.2 h2.2⟩
  | Cape.cell _ _, Cape.cell _ _, Cape.no, h1, _ => h1.elim
  | Cape.cell _ _, Cape.cell _ _, Cape.yes, h1, _ => h1.elim
  | Cape.cell _ _, Cape.no, _, h1, _ => h1
  | Cape.cell _ _, Cape.yes, _, h1, _ => h1
  | Cape.no, Cape.cell _ _, _, _, h2 => h2
  | Cape.yes, Cape.cell _ _, _, _, h2 => h2
  | Cape.no, Cape.no, B, _, _ => within_no B
  | Cape.no, Cape.yes, B, _, _ => within_no B
  | Cape.yes, Cape.no, B, _, _ => within_no B
  | Cape.yes, Cape.yes, B, _, _ => within_no B

theorem within_hed {x B1 B2 : Cape} (h : Within x (Cape.cell B1 B2)) : Within (Ca.hed x) B1 := by
  cases x with
  | cell a b => exact h.1
  | no => exact within_no _
  | yes => exact within_yes _

theorem within_tel {x B1 B2 : Cape} (h : Within x (Cape.cell B1 B2)) : Within (Ca.tel x) B2 := by
  cases x with
  | cell a b => exact h.2
  | no => exact within_no _
  | yes => exact within_yes _

theorem within_con {a b B1 B2 : Cape} (ha : Within a B1) (hb : Within b B2) :
    Within (Ca.con a b) (Cape.cell B1 B2) := by
  unfold Ca.con
  split
  · trivial
  · exact ⟨ha, hb⟩

/-- **`+lack:ca` makes cells only where its arguments have them.** -/
theorem within_lack : ∀ (d x B : Cape), Within x B → Within d B → Within (Ca.lack x d) B := by
  intro d
  induction d with
  | yes => intro x B _ _; rw [lack_yes_right]; exact within_no B
  | no => intro x B hx _; rw [lack_no_right]; exact hx
  | cell bh bT ih1 ih2 =>
    intro x B hx hd
    by_cases e : x = Cape.no
    · rw [e, lack_no_left]; exact within_no B
    rw [lack_cell_right x bh bT e]
    cases B with
    | no => exact hd.elim
    | yes => exact hd.elim
    | cell B1 B2 =>
      split
      · trivial
      · exact within_con (ih1 _ _ (within_hed hx) hd.1) (ih2 _ _ (within_tel hx) hd.2)

/-- **`+msg-ca` makes cells only where its second argument has them.** -/
theorem within_msgCa : ∀ (b a : Cape), Within (msgCa a b) b := by
  intro b
  induction b with
  | cell bh bT ih1 ih2 =>
    intro a
    rcases msgCa_cases a (Cape.cell bh bT) with ⟨e, _⟩ | ⟨ah, aT, bh', bT', _, eb, _, e⟩ | ⟨_, e⟩
    · rw [e]; subst ‹a = _›; exact within_refl _
    · cases eb; rw [e]; exact ⟨ih1 ah, ih2 aT⟩
    · rw [e]; trivial
  | no =>
    intro a
    rcases msgCa_cases a Cape.no with ⟨e, _⟩ | ⟨_, _, _, _, _, eb, _, _⟩ | ⟨_, e⟩
    · rw [e]; subst ‹a = _›; trivial
    · cases eb
    · rw [e]; trivial
  | yes =>
    intro a
    rcases msgCa_cases a Cape.yes with ⟨e, _⟩ | ⟨_, _, _, _, _, eb, _, _⟩ | ⟨_, e⟩
    · rw [e]; subst ‹a = _›; trivial
    · cases eb
    · rw [e]; trivial

/-- A `+msg-ca` that knows nothing is its second argument. -/
theorem msgCa_isNo : ∀ (q p : Cape), (msgCa p q).isNo = true → msgCa p q = q := by
  intro q
  induction q with
  | cell qh qT ih1 ih2 =>
    intro p h
    rcases msgCa_cases p (Cape.cell qh qT) with ⟨e, ea⟩ | ⟨ph, pT, qh', qT', _, eb, _, e⟩ | ⟨_, e⟩
    · rw [e, ea]
    · cases eb
      rw [e] at h ⊢
      simp only [Cape.isNo, Bool.and_eq_true] at h
      rw [ih1 ph h.1, ih2 pT h.2]
    · rw [e] at h; simp [Cape.isNo] at h
  | no =>
    intro p h
    rcases msgCa_cases p Cape.no with ⟨e, ea⟩ | ⟨_, _, _, _, _, eb, _, _⟩ | ⟨_, e⟩
    · rw [e, ea]
    · cases eb
    · rw [e] at h; simp [Cape.isNo] at h
  | yes =>
    intro p h
    rcases msgCa_cases p Cape.yes with ⟨e, ea⟩ | ⟨_, _, _, _, _, eb, _, _⟩ | ⟨_, e⟩
    · rw [e, ea]
    · cases eb
    · rw [e] at h; simp [Cape.isNo] at h

/-- **`+msg-ca` keeps a normal second argument normal**, whatever the first. -/
theorem normCape_msgCa_right : ∀ (b a : Cape), NormCape b → NormCape (msgCa a b) := by
  intro b
  induction b with
  | cell bh bT ih1 ih2 =>
    intro a hb
    rcases msgCa_cases a (Cape.cell bh bT) with ⟨e, ea⟩ | ⟨ah, aT, bh', bT', _, eb, _, e⟩ | ⟨_, e⟩
    · rw [e, ea]; exact hb
    · cases eb
      rw [e]
      have n1 := ih1 ah hb.2.1
      have n2 := ih2 aT hb.2.2
      refine ⟨?_, n1, n2⟩
      refine Bool.eq_false_iff.mpr (fun h => ?_)
      rw [Bool.and_eq_true] at h
      have hb1 := hb.1
      have e1 := msgCa_isNo bh ah h.1
      have e2 := msgCa_isNo bT aT h.2
      rw [e1] at h; rw [e2] at h
      rw [h.1, h.2] at hb1
      exact absurd hb1 (by decide)
    · rw [e]; trivial
  | no =>
    intro a _
    rcases msgCa_cases a Cape.no with ⟨e, ea⟩ | ⟨_, _, _, _, _, eb, _, _⟩ | ⟨_, e⟩
    · rw [e, ea]; trivial
    · cases eb
    · rw [e]; trivial
  | yes =>
    intro a _
    rcases msgCa_cases a Cape.yes with ⟨e, ea⟩ | ⟨_, _, _, _, _, eb, _, _⟩ | ⟨_, e⟩
    · rw [e, ea]; trivial
    · cases eb
    · rw [e]; trivial

/-! ## The weight -/

/-- The weight of `|` in the shape `B`: more than any other cape in `B`. -/
def topB : Cape → Nat
  | Cape.cell a b => topB a + topB b + 2
  | _ => 1

/-- **The weight of a cape in the shape `B`**: `&` weighs `0`, `|` weighs
`topB B`, a cell one more than its parts. -/
def wB : Cape → Cape → Nat
  | Cape.cell B1 B2, Cape.cell c1 c2 => wB B1 c1 + wB B2 c2 + 1
  | B, Cape.no => topB B
  | _, _ => 0

theorem wB_no (B : Cape) : wB B Cape.no = topB B := by cases B <;> rfl

theorem wB_yes (B : Cape) : wB B Cape.yes = 0 := by cases B <;> rfl

theorem topB_pos (B : Cape) : 1 ≤ topB B := by cases B <;> simp [topB]

theorem wB_lt_top : ∀ (B c : Cape), Within c B → c ≠ Cape.no → wB B c < topB B := by
  intro B
  induction B with
  | cell B1 B2 ih1 ih2 =>
    intro c hc hn
    cases c with
    | no => exact absurd rfl hn
    | yes => rw [wB_yes]; exact Nat.lt_of_lt_of_le (by decide) (topB_pos _)
    | cell c1 c2 =>
      simp only [wB, topB]
      have h1 : wB B1 c1 ≤ topB B1 := by
        by_cases e : c1 = Cape.no
        · rw [e, wB_no]; exact Nat.le_refl _
        · exact Nat.le_of_lt (ih1 c1 hc.1 e)
      have h2 : wB B2 c2 ≤ topB B2 := by
        by_cases e : c2 = Cape.no
        · rw [e, wB_no]; exact Nat.le_refl _
        · exact Nat.le_of_lt (ih2 c2 hc.2 e)
      omega
  | no =>
    intro c hc hn
    cases c with
    | no => exact absurd rfl hn
    | yes => decide
    | cell _ _ => exact hc.elim
  | yes =>
    intro c hc hn
    cases c with
    | no => exact absurd rfl hn
    | yes => decide
    | cell _ _ => exact hc.elim

theorem wB_le_top (B c : Cape) (hc : Within c B) : wB B c ≤ topB B := by
  by_cases e : c = Cape.no
  · rw [e, wB_no]; exact Nat.le_refl _
  · exact Nat.le_of_lt (wB_lt_top B c hc e)

theorem capeNo_norm : ∀ {c : Cape}, CapeNo c → NormCape c → c = Cape.no := by
  intro c hc hn
  induction hc with
  | no => rfl
  | cell h1 h2 ih1 ih2 =>
    have e1 := ih1 hn.2.1
    have e2 := ih2 hn.2.2
    have := hn.1
    rw [e1, e2] at this
    exact absurd this (by decide)

theorem wB_pos {B c : Cape} (hc : Within c B) (hy : c ≠ Cape.yes) : 0 < wB B c := by
  cases c with
  | yes => exact absurd rfl hy
  | no => rw [wB_no]; exact topB_pos _
  | cell c1 c2 =>
    cases B with
    | cell B1 B2 => simp only [wB]; omega
    | no => exact hc.elim
    | yes => exact hc.elim

/-- **The weight falls as the cape rises**, strictly when it changes, between
normal capes in the shape `B`. -/
theorem wB_step {c c' : Cape} (h : CapeLe c c') : ∀ (B : Cape), Within c B → Within c' B →
    NormCape c → NormCape c' → wB B c' ≤ wB B c ∧ (c ≠ c' → wB B c' < wB B c) := by
  induction h with
  | no hc d =>
    intro B _ hd hn _
    rename_i c0
    have e := capeNo_norm hc hn
    subst e
    rw [wB_no]
    refine ⟨wB_le_top B d hd, fun hne => wB_lt_top B d hd (Ne.symm hne)⟩
  | yes c0 =>
    intro B hc _ _ _
    rw [wB_yes]
    exact ⟨Nat.zero_le _, fun hne => wB_pos hc hne⟩
  | cell h1 h2 ih1 ih2 =>
    intro B hc hc' hn hn'
    cases B with
    | no => exact hc.elim
    | yes => exact hc.elim
    | cell B1 B2 =>
      obtain ⟨a1, s1⟩ := ih1 B1 hc.1 hc'.1 hn.2.1 hn'.2.1
      obtain ⟨a2, s2⟩ := ih2 B2 hc.2 hc'.2 hn.2.2 hn'.2.2
      simp only [wB]
      refine ⟨by omega, fun hne => ?_⟩
      rename_i a b c d
      by_cases e1 : a = c
      · have e2 : b ≠ d := fun e2 => hne (by rw [e1, e2])
        have := s2 e2
        omega
      · have := s1 e1
        omega

theorem topB_mono : ∀ {B' B : Cape}, Within B' B → topB B' ≤ topB B
  | Cape.cell _ _, Cape.cell _ _, h => by
    simp only [topB]; have := topB_mono h.1; have := topB_mono h.2; omega
  | Cape.cell _ _, Cape.no, h => h.elim
  | Cape.cell _ _, Cape.yes, h => h.elim
  | Cape.no, B, _ => topB_pos B
  | Cape.yes, B, _ => topB_pos B

/-- **The weight is monotone in the shape.** -/
theorem wB_mono_B : ∀ (B' B c : Cape), Within c B' → Within B' B → wB B' c ≤ wB B c := by
  intro B'
  induction B' with
  | cell B1' B2' ih1 ih2 =>
    intro B c hc hB
    cases B with
    | no => exact hB.elim
    | yes => exact hB.elim
    | cell B1 B2 =>
      cases c with
      | no => rw [wB_no, wB_no]; exact topB_mono hB
      | yes => rw [wB_yes, wB_yes]; exact Nat.le_refl _
      | cell c1 c2 =>
        simp only [wB]
        have := ih1 B1 c1 hc.1 hB.1
        have := ih2 B2 c2 hc.2 hB.2
        omega
  | no =>
    intro B c hc hB
    cases c with
    | no => rw [wB_no, wB_no]; exact topB_mono hB
    | yes => rw [wB_yes, wB_yes]; exact Nat.le_refl _
    | cell _ _ => exact hc.elim
  | yes =>
    intro B c hc hB
    cases c with
    | no => rw [wB_no, wB_no]; exact topB_mono hB
    | yes => rw [wB_yes, wB_yes]; exact Nat.le_refl _
    | cell _ _ => exact hc.elim

/-! ## The step of `indi` -/

/-- The number of `indi` for an identity whose subject's cape is `dark`. -/
def indiW (dark c : Cape) : Nat := wB (shU c dark) c

/-- **A change of the merge lowers the number of `indi`**: the old `indi` is
normal and fixed by `+lack:ca` of `dark`; then the merged cape rises over it in
`CapeLe` and, when it differs, `indiW` falls strictly. -/
theorem indi_merge_step {dark x old : Cape} (ho : NormCape old) (hfix : Ca.lack old dark = old) :
    CapeLe old (Ca.lack (msgCa x old) dark) ∧
      (Ca.lack (msgCa x old) dark ≠ old → indiW dark (Ca.lack (msgCa x old) dark) < indiW dark old) := by
  have hle : CapeLe old (Ca.lack (msgCa x old) dark) := by
    have := lack_mono dark _ _ (capeLe_msgCa x old)
    rwa [hfix] at this
  refine ⟨hle, fun hne => ?_⟩
  have hB : Within (Ca.lack (msgCa x old) dark) (shU old dark) :=
    within_lack dark _ _ (within_trans (within_msgCa old x) (within_shU_left old dark)) (within_shU_right old dark)
  have hn : NormCape (Ca.lack (msgCa x old) dark) := normCape_lack (normCape_msgCa_right old x ho)
  have s := (wB_step hle (shU old dark) (within_shU_left old dark) hB ho hn).2 (Ne.symm hne)
  have m := wB_mono_B (shU (Ca.lack (msgCa x old) dark) dark) (shU old dark) (Ca.lack (msgCa x old) dark)
    (within_shU_left _ _) (within_shU_of hB (within_shU_right old dark))
  unfold indiW
  omega

end SkaModel
end Formalization
