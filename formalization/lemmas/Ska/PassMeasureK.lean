import lemmas.Ska.PassMeasure
import lemmas.Ska.SockNorm

/-!
# The per-entry measure of the pass loop: knowledge, the mask, the map (track F)

`PassMeasure.lean` measured on the real compiler that a run of `+run` moves an
entry `[less-code prod map indi seek]` the right way in a lexicographic order.
This file proves it of the model `runDatum` for the first three fields.

## 1. One weight for `less-code` and the product

`kS` weighs what a sock knows: an atom known as `&` weighs `1`, a cell known
as `&` weighs `2` more than its two halves (so `&` over a cell is above the
cell of capes `[& &]` over it, which is what the six runs of `[[& &] |]` to
`[& |]` need), a cell of capes one more than its parts, a `|` part `0` if its
data is `0` and `1` otherwise.  `GenZ T S` (`S` forgets parts of `T`: `S` is
`T`, the unknown sock, or the knit of such of `T`'s head and tail) is what
`+app:ca` makes of a sock (`genZ_app`), what the merge of `+run` makes of the
old product (`mergeProd_genZ`), and, through `+uni:ca` with the old cape, what
the old `less-code` is of the new one (`less_genZ`).  Along `GenZ` the weight
only falls, and strictly unless the socks are equal, for a normal `T`
(`genZ_k`).

So, per entry, after its first run: `less-code` only rises in `kS`, strictly
when it changes, and stays at most `kS bus` (`runDatum_less_step`); and the
product only falls in `kS`, strictly when it changes (`runDatum_prod_step`).

`less-code` needs a condition on `bus` that the model of the analysis does not
carry yet: `Tidy` (data `0` under every `|`, a cell of data under every cell of
the cape, no `[| |]`).  Without it the step is false: on
`bus = [[& |] [1 7]]` the old `less-code` `+app:ca [& |]` is `bus` itself and
the new one with a `want` of `[& &]` is `[[& |] [1 0]]`, with the same cape, and
a later `want` of `|` gives `bus` again (`less_untidy_example`).  Every sock
operation of the analysis keeps `Tidy` (`+knit:so`, `+hed:so`, `+tel:so`,
`+app:ca` here; the others, every run of `fol-loop` and every write of the
graph in `PassMeasureT.lean`, with the data and the pokes: no untidy sock
occurs on the real compiler), and the root `&+sub` is tidy.

## 2. The map

For a product that does not change, the map moves in the order `MapLt`: the
number of leaves of the product's cape whose map is not `~` falls, else the
number of cells of the cape at which the map is a non-zero atom falls
(`mergeProd_map`).  The map must be `PiNorm` (no `[~ ~]`, which `+cons:pi`
never makes); the merge keeps it.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## The weight -/

/-- The weight of a noun known as `&`. -/
def kW : Noun → Nat
  | Noun.atom _ => 1
  | Noun.cell x y => kW x + kW y + 2

/-- The weight of a cape over its data. -/
def kC : Cape → Noun → Nat
  | Cape.no, d => if d = A 0 then 0 else 1
  | Cape.yes, d => kW d
  | Cape.cell _ _, Noun.atom _ => 1
  | Cape.cell l r, Noun.cell x y => kC l x + kC r y + 1

/-- **What a sock knows**, as a number. -/
def kS : Sock → Nat
  | Sock.void => 0
  | Sock.mk c d => kC c d

theorem kS_dunno : kS Sock.dunno = 0 := rfl

/-- **`S` forgets parts of `T`**: `S` is `T`, the unknown sock, or the knit of
such of the head and the tail of `T`.  (`GenLe` with the unknown sock `[| ~]`
only.) -/
inductive GenZ : Sock → Sock → Prop where
  | refl (T : Sock) : GenZ T T
  | dunno (T : Sock) : GenZ T Sock.dunno
  | knit {T S1 S2 : Sock} : GenZ (So.hed T) S1 → GenZ (So.tel T) S2 → GenZ T (So.knit S1 S2)

theorem knit_dunno_dunno : So.knit Sock.dunno Sock.dunno = Sock.dunno := by decide

theorem hed_dunno : So.hed Sock.dunno = Sock.dunno := rfl
theorem tel_dunno : So.tel Sock.dunno = Sock.dunno := rfl

theorem genZ_dunno_inv {T S : Sock} (h : GenZ T S) : T = Sock.dunno → S = Sock.dunno := by
  induction h with
  | refl => exact id
  | dunno => intro _; rfl
  | knit _ _ ih1 ih2 =>
    intro e; subst e
    rw [ih1 hed_dunno, ih2 tel_dunno]; exact knit_dunno_dunno

/-- The knit of two socks: `%void`, the unknown sock, or a cell of capes over a
cell of data with the two socks as its head and tail. -/
theorem knit_cases (S1 S2 : Sock) :
    So.knit S1 S2 = Sock.void ∨ So.knit S1 S2 = Sock.dunno ∨
      ∃ l r d1 d2, S1 = Sock.mk l d1 ∧ S2 = Sock.mk r d2 ∧ ¬ (l = Cape.no ∧ r = Cape.no) ∧
        So.knit S1 S2 = Sock.mk (Cape.cell l r) (C d1 d2) := by
  cases S1 with
  | void => left; cases S2 <;> rfl
  | mk l d1 =>
    cases S2 with
    | void => left; rfl
    | mk r d2 =>
      right
      simp only [So.knit, Ca.con]
      by_cases hc : l = Cape.no ∧ r = Cape.no
      · left; simp [hc]
      · right; exact ⟨l, r, d1, d2, rfl, rfl, hc, by simp [hc]⟩

theorem kS_knit_le (S1 S2 : Sock) : kS (So.knit S1 S2) ≤ kS S1 + kS S2 + 1 := by
  rcases knit_cases S1 S2 with e | e | ⟨l, r, d1, d2, rfl, rfl, _, e⟩
  · rw [e]; simp [kS]
  · rw [e, kS_dunno]; omega
  · rw [e]; simp [kS, kC]

theorem kW_pos : ∀ d : Noun, 1 ≤ kW d
  | Noun.atom _ => by simp [kW]
  | Noun.cell x y => by simp [kW]

theorem kC_zero : ∀ (c : Cape) (d : Noun), kC c d = 0 → Sock.mk c d = Sock.dunno
  | Cape.no, d, h => by
    simp only [kC] at h
    by_cases hd : d = A 0
    · subst hd; rfl
    · rw [if_neg hd] at h; cases h
  | Cape.yes, d, h => by have := kW_pos d; simp only [kC] at h; omega
  | Cape.cell _ _, Noun.atom _, h => by simp [kC] at h
  | Cape.cell _ _, Noun.cell _ _, h => by simp [kC] at h

/-- A sock whose head and tail are unknown forgets to itself or to `[| ~]`. -/
theorem genZ_flat {T S : Sock} (h : GenZ T S) (h1 : So.hed T = Sock.dunno) (h2 : So.tel T = Sock.dunno) :
    S = T ∨ S = Sock.dunno := by
  cases h with
  | refl => exact Or.inl rfl
  | dunno => exact Or.inr rfl
  | knit g1 g2 =>
    right
    rw [genZ_dunno_inv g1 h1, genZ_dunno_inv g2 h2]; exact knit_dunno_dunno

/-- **Along `GenZ` the weight falls, strictly unless the socks are equal**, for
a normal `T` that is not `%void`. -/
theorem genZ_k {T S : Sock} (h : GenZ T S) : NormSock T → T ≠ Sock.void → S = T ∨ kS S < kS T := by
  induction h with
  | refl => intro _ _; exact Or.inl rfl
  | dunno T =>
    intro _ hv
    cases T with
    | void => exact absurd rfl hv
    | mk c d =>
      by_cases h0 : kC c d = 0
      · left; exact (kC_zero c d h0).symm
      · right; show 0 < kC c d; omega
  | @knit T S1 S2 g1 g2 ih1 ih2 =>
    intro hn hv
    cases T with
    | void => exact absurd rfl hv
    | mk c d =>
    have flat : So.hed (Sock.mk c d) = Sock.dunno → So.tel (Sock.mk c d) = Sock.dunno →
        So.knit S1 S2 = Sock.mk c d ∨ kS (So.knit S1 S2) < kS (Sock.mk c d) := by
      intro e1 e2
      rw [genZ_dunno_inv g1 e1, genZ_dunno_inv g2 e2, knit_dunno_dunno]
      by_cases h0 : kC c d = 0
      · left; exact (kC_zero c d h0).symm
      · right; show 0 < kC c d; omega
    have i1 := ih1 (normSock_hed hn) (hed_ne_void hv)
    have i2 := ih2 (normSock_tel hn) (tel_ne_void hv)
    have b1 : kS S1 ≤ kS (So.hed (Sock.mk c d)) := by
      rcases i1 with e | e
      · exact Nat.le_of_eq (congrArg kS e)
      · exact Nat.le_of_lt e
    have b2 : kS S2 ≤ kS (So.tel (Sock.mk c d)) := by
      rcases i2 with e | e
      · exact Nat.le_of_eq (congrArg kS e)
      · exact Nat.le_of_lt e
    have kl := kS_knit_le S1 S2
    cases c with
    | no => exact flat rfl rfl
    | yes =>
      cases d with
      | atom _ => exact flat rfl rfl
      | cell x y =>
        right
        have b1' : kS S1 ≤ kW x := b1
        have b2' : kS S2 ≤ kW y := b2
        show kS (So.knit S1 S2) < kW x + kW y + 2
        omega
    | cell l r =>
      cases d with
      | atom _ => exact flat rfl rfl
      | cell x y =>
        simp only [So.hed, So.tel] at i1 i2 b1 b2
        have hn' : ¬ (l = Cape.no ∧ r = Cape.no) := by
          intro ⟨e1, e2⟩; subst e1; subst e2; exact absurd hn.1 (by simp [Cape.isNo])
        rcases knit_cases S1 S2 with e | e | ⟨l', r', d1, d2, rfl, rfl, _, e⟩
        · right; rw [e]; show 0 < kC l x + kC r y + 1; omega
        · right; rw [e]; show 0 < kC l x + kC r y + 1; omega
        · rcases i1 with e1 | e1
          · rcases i2 with e2 | e2
            · left; cases e1; cases e2; simp [So.knit, Ca.con, hn']
            · right; rw [e]; simp only [kS] at e2 b1 ⊢; show kC l' d1 + kC r' d2 + 1 < kC l x + kC r y + 1; omega
          · right; rw [e]; simp only [kS] at e1 b2 ⊢; show kC l' d1 + kC r' d2 + 1 < kC l x + kC r y + 1; omega

/-! ## `+app:ca` on a tidy sock -/

/-- `S` forgets parts of `s` when it is `+app:ca` of a mask on `s`. -/
theorem genZ_app : ∀ (c : Cape) (s : Sock), GenZ s (Ca.app c s) := by
  intro c
  induction c with
  | yes =>
    intro s; cases s with
    | void => exact GenZ.refl _
    | mk cs d => unfold Ca.app; split <;> (try split) <;> first | exact GenZ.refl _ | exact GenZ.dunno _
  | no =>
    intro s; cases s with
    | void => exact GenZ.refl _
    | mk cs d => unfold Ca.app; split <;> (try split) <;> first | exact GenZ.refl _ | exact GenZ.dunno _
  | cell x y ihx ihy =>
    intro s; cases s with
    | void => exact GenZ.refl _
    | mk cs d =>
      unfold Ca.app; split
      · exact GenZ.refl _
      · split
        · exact GenZ.dunno _
        · exact GenZ.knit (ihx _) (ihy _)

/-- **A tidy cape over its data**: `0` under every `|`, a cell of data under
every cell of the cape, and no cell `[| |]`. -/
def TidyC : Cape → Noun → Prop
  | Cape.no, d => d = A 0
  | Cape.yes, _ => True
  | Cape.cell _ _, Noun.atom _ => False
  | Cape.cell l r, Noun.cell x y => ¬ (l = Cape.no ∧ r = Cape.no) ∧ TidyC l x ∧ TidyC r y

/-- A tidy sock (`%void` is tidy). -/
def Tidy : Sock → Prop
  | Sock.void => True
  | Sock.mk c d => TidyC c d

theorem tidy_dunno : Tidy Sock.dunno := rfl

theorem tidy_root (sub : Noun) : Tidy (Sock.mk Cape.yes sub) := trivial

theorem tidy_hed {s : Sock} (h : Tidy s) : Tidy (So.hed s) := by
  cases s with
  | void => trivial
  | mk c d =>
    cases c with
    | no => exact tidy_dunno
    | yes => cases d with
      | atom _ => exact tidy_dunno
      | cell _ _ => trivial
    | cell l r => cases d with
      | atom _ => exact absurd h id
      | cell x y => exact h.2.1

theorem tidy_tel {s : Sock} (h : Tidy s) : Tidy (So.tel s) := by
  cases s with
  | void => trivial
  | mk c d =>
    cases c with
    | no => exact tidy_dunno
    | yes => cases d with
      | atom _ => exact tidy_dunno
      | cell _ _ => trivial
    | cell l r => cases d with
      | atom _ => exact absurd h id
      | cell x y => exact h.2.2

theorem tidy_knit {a b : Sock} (ha : Tidy a) (hb : Tidy b) : Tidy (So.knit a b) := by
  rcases knit_cases a b with e | e | ⟨l, r, d1, d2, rfl, rfl, hn, e⟩
  · rw [e]; trivial
  · rw [e]; exact tidy_dunno
  · rw [e]; exact ⟨hn, ha, hb⟩

theorem tidyC_norm : ∀ (c : Cape) (d : Noun), TidyC c d → NormCape c
  | Cape.no, _, _ => trivial
  | Cape.yes, _, _ => trivial
  | Cape.cell _ _, Noun.atom _, h => absurd h id
  | Cape.cell l r, Noun.cell x y, h => by
    have nl := tidyC_norm l x h.2.1
    have nr := tidyC_norm r y h.2.2
    refine ⟨?_, nl, nr⟩
    cases e1 : l.isNo <;> cases e2 : r.isNo <;> simp
    exact h.1 ⟨nl.eq_no e1, nr.eq_no e2⟩

theorem tidy_norm {s : Sock} (h : Tidy s) : NormSock s := by
  cases s with
  | void => trivial
  | mk c d => exact tidyC_norm c d h

theorem app_dunno (c : Cape) : Ca.app c Sock.dunno = Sock.dunno := by
  cases c <;> simp [Ca.app, Sock.dunno]

theorem app_no_tidy {s : Sock} (hs : Tidy s) (hv : s ≠ Sock.void) : Ca.app Cape.no s = Sock.dunno := by
  cases s with
  | void => exact absurd rfl hv
  | mk cs d =>
    unfold Ca.app; split
    · rename_i h; subst h; have : d = A 0 := hs; subst this; rfl
    · rw [if_pos (Or.inl rfl)]

theorem app_yes_tidy {s : Sock} (hs : Tidy s) : Ca.app Cape.yes s = s := by
  cases s with
  | void => rfl
  | mk cs d =>
    unfold Ca.app; split
    · rfl
    · split
      · rename_i _ h
        rcases h with h | h
        · cases h
        · subst h; have : d = A 0 := hs; subst this; rfl
      · rfl

theorem app_cell_tidy {s : Sock} (x y : Cape) (hs : Tidy s) (hv : s ≠ Sock.void) :
    Ca.app (Cape.cell x y) s = So.knit (Ca.app x (So.hed s)) (Ca.app y (So.tel s)) := by
  cases s with
  | void => exact absurd rfl hv
  | mk cs d =>
    by_cases h1 : Cape.cell x y = cs
    · subst h1
      cases d with
      | atom _ => exact absurd hs id
      | cell dh dt =>
        rw [app_self]
        simp only [So.hed, So.tel, app_self]
        simp [So.knit, Ca.con, hs.1]
    · by_cases h2 : cs = Cape.no
      · subst h2
        have : d = A 0 := hs; subst this
        show Ca.app (Cape.cell x y) Sock.dunno = So.knit (Ca.app x Sock.dunno) (Ca.app y Sock.dunno)
        rw [app_dunno, app_dunno, app_dunno, knit_dunno_dunno]
      · rw [Ca.app.eq_def]; dsimp only
        rw [if_neg h1, if_neg (by rintro (h | h) <;> first | exact h2 h | cases h)]

theorem tidy_app : ∀ (c : Cape) {s : Sock}, Tidy s → Tidy (Ca.app c s) := by
  intro c
  induction c with
  | yes => intro s hs; rw [app_yes_tidy hs]; exact hs
  | no =>
    intro s hs
    by_cases hv : s = Sock.void
    · subst hv; rw [app_void]; trivial
    · rw [app_no_tidy hs hv]; exact tidy_dunno
  | cell x y ihx ihy =>
    intro s hs
    by_cases hv : s = Sock.void
    · subst hv; rw [app_void]; trivial
    · rw [app_cell_tidy x y hs hv]; exact tidy_knit (ihx (tidy_hed hs)) (ihy (tidy_tel hs))

theorem app_capeNo {c : Cape} (hc : CapeNo c) : ∀ {s : Sock}, Tidy s → s ≠ Sock.void → Ca.app c s = Sock.dunno := by
  induction hc with
  | no => intro s hs hv; exact app_no_tidy hs hv
  | cell _ _ iha ihb =>
    intro s hs hv
    rw [app_cell_tidy _ _ hs hv, iha (tidy_hed hs) (hed_ne_void hv), ihb (tidy_tel hs) (tel_ne_void hv)]
    exact knit_dunno_dunno

theorem knit_eq_dunno {a b : Sock} (e : So.knit a b = Sock.dunno) (ha : Tidy a) (hb : Tidy b) :
    a = Sock.dunno ∧ b = Sock.dunno := by
  rcases knit_cases a b with e' | e' | ⟨l, r, d1, d2, rfl, rfl, hn, e'⟩
  · rw [e'] at e; cases e
  · cases a with
    | void => simp [So.knit, Sock.dunno] at e
    | mk l d1 =>
      cases b with
      | void => simp [So.knit, Sock.dunno] at e
      | mk r d2 =>
        simp only [So.knit, Ca.con] at e
        by_cases hc : l = Cape.no ∧ r = Cape.no
        · obtain ⟨rfl, rfl⟩ := hc
          have e1 : d1 = A 0 := ha
          have e2 : d2 = A 0 := hb
          subst e1; subst e2; exact ⟨rfl, rfl⟩
        · simp [hc, Sock.dunno] at e
  · rw [e'] at e; cases e

/-- The knit of two forgetful socks forgets the knit. -/
theorem genZ_knit_cong {X1 X2 Y1 Y2 : Sock} (g1 : GenZ X1 Y1) (g2 : GenZ X2 Y2) (t1 : Tidy X1) (t2 : Tidy X2)
    (v1 : X1 ≠ Sock.void) (v2 : X2 ≠ Sock.void) :
    GenZ (So.knit X1 X2) (So.knit Y1 Y2) := by
  rcases knit_cases X1 X2 with e | e | ⟨l, r, d1, d2, rfl, rfl, hn, e⟩
  · exact absurd e (knit_ne_void v1 v2)
  · obtain ⟨h1, h2⟩ := knit_eq_dunno e t1 t2
    subst h1; subst h2
    rw [e, genZ_dunno_inv g1 rfl, genZ_dunno_inv g2 rfl, knit_dunno_dunno]
    exact GenZ.refl _
  · rw [e]
    exact GenZ.knit g1 g2

/-- **`+app:ca` is monotone in the mask** (`CapeLe`) on a tidy sock: a higher
mask forgets less. -/
theorem app_mono {c1 c2 : Cape} (h : CapeLe c1 c2) : ∀ {s : Sock}, Tidy s → GenZ (Ca.app c2 s) (Ca.app c1 s) := by
  induction h with
  | no hc d =>
    intro s hs
    by_cases hv : s = Sock.void
    · subst hv; rw [app_void, app_void]; exact GenZ.refl _
    · rw [app_capeNo hc hs hv]; exact GenZ.dunno _
  | yes c =>
    intro s hs; rw [app_yes_tidy hs]; exact genZ_app c s
  | cell _ _ ih1 ih2 =>
    intro s hs
    by_cases hv : s = Sock.void
    · subst hv; rw [app_void, app_void]; exact GenZ.refl _
    · rw [app_cell_tidy _ _ hs hv, app_cell_tidy _ _ hs hv]
      exact genZ_knit_cong (ih1 (tidy_hed hs)) (ih2 (tidy_tel hs))
        (tidy_app _ (tidy_hed hs)) (tidy_app _ (tidy_tel hs))
        (app_ne_void _ (hed_ne_void hv)) (app_ne_void _ (tel_ne_void hv))

/-- **`+app:ca` with the cape of its own result** gives the result again, on a
tidy sock. -/
theorem app_idem : ∀ (c : Cape) {s : Sock}, Tidy s → Ca.app (darkOf (Ca.app c s)) s = Ca.app c s := by
  intro c
  induction c with
  | yes =>
    intro s hs; rw [app_yes_tidy hs]
    cases s with
    | void => rfl
    | mk cs d => exact app_self cs d
  | no =>
    intro s hs
    by_cases hv : s = Sock.void
    · subst hv; rfl
    · rw [app_no_tidy hs hv]; exact app_no_tidy hs hv
  | cell x y ihx ihy =>
    intro s hs
    by_cases hv : s = Sock.void
    · subst hv; rfl
    rw [app_cell_tidy x y hs hv]
    rcases knit_cases (Ca.app x (So.hed s)) (Ca.app y (So.tel s)) with e | e | ⟨l, r, d1, d2, e1, e2, _, e⟩
    · exact absurd e (knit_ne_void (app_ne_void _ (hed_ne_void hv)) (app_ne_void _ (tel_ne_void hv)))
    · rw [e]; exact app_no_tidy hs hv
    · rw [e]
      show Ca.app (Cape.cell l r) s = Sock.mk (Cape.cell l r) (C d1 d2)
      rw [app_cell_tidy l r hs hv]
      have i1 := ihx (tidy_hed hs); rw [e1] at i1; simp only [darkOf] at i1
      have i2 := ihy (tidy_tel hs); rw [e2] at i2; simp only [darkOf] at i2
      rw [i1, i2]; rw [e1, e2] at e; exact e

/-- **The new `less-code` of `+run` is above the old one**: the old one forgets
parts of it, on a tidy `bus`. -/
theorem less_genZ {bus : Sock} (hb : Tidy bus) (want c0 : Cape) :
    GenZ (Ca.app (Ca.uni want (darkOf (Ca.app c0 bus))) bus) (Ca.app c0 bus) := by
  have h := app_mono (capeLe_uni_right want (darkOf (Ca.app c0 bus))) hb
  rw [app_idem c0 hb] at h
  exact h

/-! ## The product -/

theorem genZ_ne_void {T S : Sock} (h : GenZ T S) : T ≠ Sock.void → S ≠ Sock.void := by
  induction h with
  | refl => exact id
  | dunno => intro _ h; cases h
  | knit _ _ ih1 ih2 => intro hv; exact knit_ne_void (ih1 (hed_ne_void hv)) (ih2 (tel_ne_void hv))

theorem doubleInt_genZ : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    b.sock ≠ Sock.void → GenZ b.sock (doubleInt a b).sock := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact GenZ.refl _
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  simp only at hb
  cases sb with
  | void => exact absurd rfl hb
  | mk cb db =>
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact GenZ.refl _
  | mk ca da =>
    apply doubleInt_cases (fun r => GenZ (Sock.mk cb db) r.sock) hab (GenZ.dunno _)
    intro hno
    simp only [not_or] at hno
    have h1 := msr_hed_lt hno.1 da; have h2 := msr_hed_lt hno.2 db
    have h3 := msr_tel_lt hno.1 da; have h4 := msr_tel_lt hno.2 db
    simp only at hk
    exact GenZ.knit
      (ih ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩ (by simp only; omega)
        (hed_ne_void (s := Sock.mk cb db) (by intro h; cases h)))
      (ih ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩ (by simp only; omega)
        (tel_ne_void (s := Sock.mk cb db) (by intro h; cases h)))

theorem msgAnno_genZ : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    b.sock ≠ Sock.void → GenZ b.sock (msgAnno a b).sock := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  simp only at hb
  unfold msgAnno
  split
  · rename_i heq
    simp only [Anno.mk.injEq] at heq
    rw [heq.1]; exact GenZ.refl _
  · split
    · exact GenZ.refl _
    · exfalso
      rename_i hh _
      simp only [Anno.mk.injEq] at hh
      exact hb hh.1
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only at hk
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      exact GenZ.knit
        (ih ⟨So.hed (Sock.mk (Cape.cell ah aT) da), Pi.hed ra⟩ ⟨So.hed (Sock.mk (Cape.cell bh bT) db), Pi.hed rb⟩
          (by simp only; omega) (hed_ne_void (s := Sock.mk (Cape.cell bh bT) db) (by intro h; cases h)))
        (ih ⟨So.tel (Sock.mk (Cape.cell ah aT) da), Pi.tel ra⟩ ⟨So.tel (Sock.mk (Cape.cell bh bT) db), Pi.tel rb⟩
          (by simp only; omega) (tel_ne_void (s := Sock.mk (Cape.cell bh bT) db) (by intro h; cases h)))
    · exact GenZ.dunno _

/-- **The product an entry keeps forgets parts of the old one.** -/
theorem mergeProd_genZ (moved : Bool) (new old : Anno) (hv : old.sock ≠ Sock.void) :
    GenZ old.sock (mergeProd moved new old).sock := by
  unfold mergeProd
  split
  · exact msgAnno_genZ _ new old (Nat.lt_succ_self _) hv
  · exact doubleInt_genZ _ new old (Nat.lt_succ_self _) hv

/-- **The product of an entry only falls in `kS`, strictly when it changes**,
and stays not `%void`, once it is not `%void`. -/
theorem runDatum_prod_step (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (hv : old.prod ≠ Sock.void) (hn : NormSock old.prod) :
    ((runDatum moved bus out gen' old).1.prod = old.prod ∨
      kS (runDatum moved bus out gen' old).1.prod < kS old.prod) ∧
    (runDatum moved bus out gen' old).1.prod ≠ Sock.void := by
  have g := mergeProd_genZ moved out.prod ⟨old.prod, old.map⟩ hv
  exact ⟨genZ_k g hn hv, genZ_ne_void g hv⟩

/-! ## `less-code` -/

/-- **`less-code` of an entry only rises in `kS`, strictly when it changes, and
stays at most `kS bus`**, on a tidy `bus`, once it is a mask of `bus` (which
it is after the first run, `runDatum_less`). -/
theorem runDatum_less_step (moved : Bool) {bus : Sock} (out : FolOut) (gen' : Gen) (old : Datum)
    (hb : Tidy bus) {c0 : Cape} (h0 : old.less = Ca.app c0 bus) :
    ((runDatum moved bus out gen' old).1.less = old.less ∨
      kS old.less < kS (runDatum moved bus out gen' old).1.less) ∧
    kS (runDatum moved bus out gen' old).1.less ≤ kS bus := by
  show (Ca.app (Ca.uni gen'.want (darkOf old.less)) bus = old.less ∨
      kS old.less < kS (Ca.app (Ca.uni gen'.want (darkOf old.less)) bus)) ∧
    kS (Ca.app (Ca.uni gen'.want (darkOf old.less)) bus) ≤ kS bus
  by_cases hv : bus = Sock.void
  · subst hv; rw [h0, app_void, app_void]; exact ⟨Or.inl rfl, Nat.le_refl _⟩
  refine ⟨?_, ?_⟩
  · have g := less_genZ hb gen'.want c0
    rw [← h0] at g
    rcases genZ_k g (tidy_norm (tidy_app _ hb)) (app_ne_void _ hv) with e | e
    · exact Or.inl e.symm
    · exact Or.inr e
  · rcases genZ_k (genZ_app (Ca.uni gen'.want (darkOf old.less)) bus) (tidy_norm hb) hv with e | e
    · rw [e]; exact Nat.le_refl _
    · exact Nat.le_of_lt e

/-- Without `Tidy` the step is false: on `[[& |] [1 7]]` the mask `[& |]`
keeps the `7`, the mask `[& &]` (the old cape united with a `want` of
`[& &]`) drops it, with the same cape, and a `want` of `|` brings it back. -/
theorem less_untidy_example :
    let bus := Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 1) (A 7))
    Ca.app (Cape.cell Cape.yes Cape.no) bus = bus ∧
    Ca.app (Ca.uni (Cape.cell Cape.yes Cape.yes) (Cape.cell Cape.yes Cape.no)) bus =
      Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 1) (A 0)) ∧
    Ca.app (Ca.uni Cape.no (darkOf (Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 1) (A 0))))) bus = bus := by
  decide

/-! ## The map, for a product that does not change -/

/-- A map with no `[~ ~]`, which `+cons:pi` never makes. -/
def PiNorm : Noun → Prop
  | Noun.atom _ => True
  | Noun.cell x y => ¬ (x = A 0 ∧ y = A 0) ∧ PiNorm x ∧ PiNorm y

theorem pi_hed_cons (x y : Noun) : Pi.hed (Pi.cons x y) = x := by
  unfold Pi.cons; split
  · rename_i h; rw [h.1]; rfl
  · rfl

theorem pi_tel_cons (x y : Noun) : Pi.tel (Pi.cons x y) = y := by
  unfold Pi.cons; split
  · rename_i h; rw [h.2]; rfl
  · rfl

theorem piNorm_hed {m : Noun} (h : PiNorm m) : PiNorm (Pi.hed m) := by
  cases m with
  | atom p => cases p <;> trivial
  | cell x y => exact h.2.1

theorem piNorm_tel {m : Noun} (h : PiNorm m) : PiNorm (Pi.tel m) := by
  cases m with
  | atom p => cases p <;> trivial
  | cell x y => exact h.2.2

/-- `1` where the map at a cell of the cape is a non-zero atom (an axis not
spelled out along the cells). -/
def mapInd : Noun → Nat
  | Noun.atom 0 => 0
  | Noun.atom _ => 1
  | Noun.cell _ _ => 0

theorem mapInd_cons (x y : Noun) : mapInd (Pi.cons x y) = 0 := by
  unfold Pi.cons; split
  · rfl
  · rfl

/-- The leaves of the cape whose map is not `~`. -/
def mapL : Cape → Noun → Nat
  | Cape.cell l r, m => mapL l (Pi.hed m) + mapL r (Pi.tel m)
  | _, m => if m = A 0 then 0 else 1

/-- The cells of the cape at which the map is a non-zero atom. -/
def mapA : Cape → Noun → Nat
  | Cape.cell l r, m => mapA l (Pi.hed m) + mapA r (Pi.tel m) + mapInd m
  | _, _ => 0

/-- **The order in which the map of a fixed product moves**: fewer leaves of
the product's cape with a map, else fewer cells of it at which the map is an
atom. -/
def MapLt (c : Cape) (m' m : Noun) : Prop :=
  mapL c m' < mapL c m ∨ (mapL c m' = mapL c m ∧ mapA c m' < mapA c m)

theorem map_cell_step (l r : Cape) (rb hs ts : Noun) (hp : PiNorm rb)
    (i1 : hs = Pi.hed rb ∨ MapLt l hs (Pi.hed rb)) (i2 : ts = Pi.tel rb ∨ MapLt r ts (Pi.tel rb)) :
    Pi.cons hs ts = rb ∨ MapLt (Cape.cell l r) (Pi.cons hs ts) rb := by
  have eL : mapL (Cape.cell l r) (Pi.cons hs ts) = mapL l hs + mapL r ts := by
    simp only [mapL, pi_hed_cons, pi_tel_cons]
  have eA : mapA (Cape.cell l r) (Pi.cons hs ts) = mapA l hs + mapA r ts := by
    simp only [mapA, pi_hed_cons, pi_tel_cons, mapInd_cons, Nat.add_zero]
  have oL : mapL (Cape.cell l r) rb = mapL l (Pi.hed rb) + mapL r (Pi.tel rb) := by simp only [mapL]
  have oA : mapA (Cape.cell l r) rb = mapA l (Pi.hed rb) + mapA r (Pi.tel rb) + mapInd rb := by
    simp only [mapA]
  unfold MapLt at i1 i2 ⊢
  rcases i1 with e1 | e1 <;> rcases i2 with e2 | e2
  · subst e1; subst e2
    cases rb with
    | atom p =>
      cases p with
      | zero => left; rfl
      | succ q =>
        right; right
        have : mapInd (Noun.atom (q + 1)) = 1 := rfl
        omega
    | cell x y =>
      left
      show Pi.cons x y = C x y
      unfold Pi.cons
      exact if_neg hp.1
  · right; subst e1; omega
  · right; subst e2; omega
  · right; omega

theorem map_knit_step {h t : Anno} {cb : Cape} {db rb : Noun} (hp : PiNorm rb)
    (e : So.knit h.sock t.sock = Sock.mk cb db) (hcb : cb ≠ Cape.no)
    (ih1 : h.sock = So.hed (Sock.mk cb db) →
      h.src = Pi.hed rb ∨ MapLt (darkOf (So.hed (Sock.mk cb db))) h.src (Pi.hed rb))
    (ih2 : t.sock = So.tel (Sock.mk cb db) →
      t.src = Pi.tel rb ∨ MapLt (darkOf (So.tel (Sock.mk cb db))) t.src (Pi.tel rb)) :
    Pi.cons h.src t.src = rb ∨ MapLt cb (Pi.cons h.src t.src) rb := by
  rcases knit_cases h.sock t.sock with e' | e' | ⟨l, r, d1, d2, e1, e2, _, e'⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; simp only [Sock.dunno, Sock.mk.injEq] at e; exact absurd e.1.symm hcb
  · rw [e'] at e; simp only [Sock.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact map_cell_step l r rb _ _ hp (ih1 e1) (ih2 e2)

theorem map_dunno_step {cb : Cape} {db rb : Noun} (e : Sock.dunno = Sock.mk cb db) :
    A 0 = rb ∨ MapLt cb (A 0) rb := by
  simp only [Sock.dunno, Sock.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  by_cases h0 : rb = A 0
  · exact Or.inl h0.symm
  · right; left; simp [mapL, h0]

theorem doubleInt_map : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    b.sock ≠ Sock.void → PiNorm b.src → (doubleInt a b).sock = b.sock →
    (doubleInt a b).src = b.src ∨ MapLt (darkOf b.sock) (doubleInt a b).src b.src := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb hp he
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact Or.inl rfl
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  simp only at hb hp he hk ⊢
  cases sb with
  | void => exact absurd rfl hb
  | mk cb db =>
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact Or.inl rfl
  | mk ca da =>
    revert he
    apply doubleInt_cases (fun r => r.sock = Sock.mk cb db → r.src = rb ∨ MapLt cb r.src rb) hab
    · exact map_dunno_step
    · intro hno e
      simp only [not_or] at hno
      have h1 := msr_hed_lt hno.1 da; have h2 := msr_hed_lt hno.2 db
      have h3 := msr_tel_lt hno.1 da; have h4 := msr_tel_lt hno.2 db
      exact map_knit_step hp e hno.2
        (fun e1 => ih ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩
          (by simp only; omega) (hed_ne_void (s := Sock.mk cb db) (by intro h; cases h)) (piNorm_hed hp) e1)
        (fun e2 => ih ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩
          (by simp only; omega) (tel_ne_void (s := Sock.mk cb db) (by intro h; cases h)) (piNorm_tel hp) e2)

theorem msgAnno_map : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    b.sock ≠ Sock.void → PiNorm b.src → (msgAnno a b).sock = b.sock →
    (msgAnno a b).src = b.src ∨ MapLt (darkOf b.sock) (msgAnno a b).src b.src := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb hp he
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  simp only at hb hp hk
  revert he
  unfold msgAnno
  split
  · rename_i heq
    simp only [Anno.mk.injEq] at heq
    intro _; exact Or.inl heq.2
  · split
    · intro _; exact Or.inl rfl
    · exfalso
      rename_i hh _
      simp only [Anno.mk.injEq] at hh
      exact hb hh.1
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      intro e
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      exact map_knit_step hp e (by intro h; cases h)
        (fun e1 => ih ⟨So.hed (Sock.mk (Cape.cell ah aT) da), Pi.hed ra⟩
          ⟨So.hed (Sock.mk (Cape.cell bh bT) db), Pi.hed rb⟩ (by simp only; omega)
          (hed_ne_void (s := Sock.mk (Cape.cell bh bT) db) (by intro h; cases h)) (piNorm_hed hp) e1)
        (fun e2 => ih ⟨So.tel (Sock.mk (Cape.cell ah aT) da), Pi.tel ra⟩
          ⟨So.tel (Sock.mk (Cape.cell bh bT) db), Pi.tel rb⟩ (by simp only; omega)
          (tel_ne_void (s := Sock.mk (Cape.cell bh bT) db) (by intro h; cases h)) (piNorm_tel hp) e2)
    · intro e
      cases sb with
      | void => exact absurd rfl hb
      | mk cb db => exact map_dunno_step e

/-- **Open point (a), for any product**: when the product an entry keeps does
not change, its map stays or moves down in `MapLt` over the product's cape. -/
theorem runDatum_map_step (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (hv : old.prod ≠ Sock.void) (hp : PiNorm old.map)
    (he : (runDatum moved bus out gen' old).1.prod = old.prod) :
    (runDatum moved bus out gen' old).1.map = old.map ∨
      MapLt (darkOf old.prod) (runDatum moved bus out gen' old).1.map old.map := by
  simp only [runDatum] at he ⊢
  unfold mergeProd at he ⊢
  split
  · rename_i hm; rw [if_pos hm] at he
    exact msgAnno_map _ out.prod ⟨old.prod, old.map⟩ (Nat.lt_succ_self _) hv hp he
  · rename_i hm; rw [if_neg hm] at he
    exact doubleInt_map _ out.prod ⟨old.prod, old.map⟩ (Nat.lt_succ_self _) hv hp he

/-! ## `indi` and `seek`, and the step of an entry -/

/-- `+msg-ca` only rises in `CapeLe` over its second argument. -/
theorem capeLe_msgCa : ∀ a b : Cape, CapeLe b (msgCa a b)
  | a, b => by
    unfold msgCa
    split
    · rename_i h; subst h; exact capeLe_refl _
    · split
      · rename_i ah aT bh bT _
        exact CapeLe.cell (capeLe_msgCa ah bh) (capeLe_msgCa aT bT)
      · exact CapeLe.yes _

/-- When `less-code`, the product and the map stay, `indi` stays or is merged
by `+msg-ca` with the old one (then `+lack:ca` of `dark`), and when `indi`
stays too, `seek` stays or rises by `+msg-ca` over the old one. -/
theorem runDatum_indi_seek (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (hl : (runDatum moved bus out gen' old).1.less = old.less)
    (hp : (runDatum moved bus out gen' old).1.prod = old.prod)
    (hm : (runDatum moved bus out gen' old).1.map = old.map) :
    ((runDatum moved bus out gen' old).1.indi = old.indi ∨
      (runDatum moved bus out gen' old).1.indi =
        Ca.lack (msgCa (Ca.lack gen'.indi (darkOf bus)) old.indi) (darkOf bus)) ∧
    ((runDatum moved bus out gen' old).1.indi = old.indi →
      (runDatum moved bus out gen' old).1.seek = old.seek ∨
        ((runDatum moved bus out gen' old).1.seek = msgCa gen'.seek old.seek ∧
          CapeLe old.seek (runDatum moved bus out gen' old).1.seek)) := by
  simp only [runDatum] at hl hp hm ⊢
  rw [hl, hp, hm]
  refine ⟨?_, ?_⟩
  · by_cases hi : Ca.lack gen'.indi (darkOf bus) = old.indi
    · left; simp [hi]
    · right; simp [hi]
  · intro hi
    rw [hi]
    by_cases hs : gen'.seek = old.seek
    · left; simp [hs]
    · right; simp; rw [if_neg hs]; exact ⟨fun h => absurd h hs, capeLe_msgCa _ _⟩

/-- **The step of an entry** (`+run` on an entry after its first run, on a
tidy `bus`): `less-code` stays at most `kS bus`, and the entry moves in the
lexicographic order of track F: `less-code` rises in `kS`, else the product
falls in `kS`, else the map falls in `MapLt` over the product's cape, else
`indi` stays or is merged with the old one, and with `indi` the same `seek`
stays or rises in `CapeLe`.  The invariants it needs are kept: `less-code`
is a mask of `bus` (by construction), the product is not `%void` and is
normal (`runDatum_prod_step`, `runDatum_norm`).  Not here: that the map stays
`PiNorm`, and the bound of the `indi` and `seek` merges. -/
theorem runDatum_measure (moved : Bool) {bus : Sock} (out : FolOut) (gen' : Gen) (old : Datum)
    (hb : Tidy bus) {c0 : Cape} (h0 : old.less = Ca.app c0 bus)
    (hv : old.prod ≠ Sock.void) (hn : NormSock old.prod) (hp : PiNorm old.map) :
    let d := (runDatum moved bus out gen' old).1
    kS d.less ≤ kS bus ∧ d.prod ≠ Sock.void ∧
    (kS old.less < kS d.less ∨
      (d.less = old.less ∧
        (kS d.prod < kS old.prod ∨
          (d.prod = old.prod ∧
            (MapLt (darkOf old.prod) d.map old.map ∨
              (d.map = old.map ∧
                (d.indi = old.indi ∨ d.indi = Ca.lack (msgCa (Ca.lack gen'.indi (darkOf bus)) old.indi) (darkOf bus)) ∧
                (d.indi = old.indi → d.seek = old.seek ∨ (d.seek = msgCa gen'.seek old.seek ∧ CapeLe old.seek d.seek)))))))) := by
  intro d
  obtain ⟨hl, hlb⟩ := runDatum_less_step moved out gen' old hb h0
  obtain ⟨hpr, hpv⟩ := runDatum_prod_step moved bus out gen' old hv hn
  refine ⟨hlb, hpv, ?_⟩
  rcases hl with hl | hl
  · right; refine ⟨hl, ?_⟩
    rcases hpr with hpr | hpr
    · right; refine ⟨hpr, ?_⟩
      rcases runDatum_map_step moved bus out gen' old hv hp hpr with hm | hm
      · right; exact ⟨hm, runDatum_indi_seek moved bus out gen' old hl hpr hm⟩
      · left; exact hm
    · left; exact hpr
  · left; exact hl

end SkaModel
end Formalization
