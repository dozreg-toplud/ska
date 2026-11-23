import lemmas.Ska.SockFacts

/-!
# Provenance: `+pi`, `+distribute`, `+double-int`, and the sock-annotated type

Lean models of the arms of `nock-compilation.hoon` that `fol-loop` uses on
provenance, arm by arm:

* `+peg` of `hoon.hoon`;
* the arms `cons`, `hed`, `tel`, `slot`, `compose`, `edit` of `+pi`;
* `+distribute`, which turns a use of a noun into a use of the subject along
  its provenance;
* `+double-int`, the join of two sock-annotated products (the two branches of
  a Nock 6).

A provenance (`+$spring`) is any noun: `~` (the atom `0`) is a noun that does
not come from the subject, another atom is an axis of the subject, and a cell
is the provenance of a cell, head and tail.  It is a `Noun` here.

`+$sock-anno` is `Anno`.  Arms that call `+cap`, `+mas`, `+peg` or `+pat:ca`
on an axis that would crash them (`0`, or `1` for `+cap` and `+mas`) never do
so from `fol-loop`; the models return junk there, and say so.

`double_int_fits_left` and `double_int_fits_right` say that the join knows no
more than either side, as `purr_fits_left` does for `+purr:so`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## `+peg` -/

/-- `+peg`: the axis `b` within the axis `a`.  The Hoon loops on `b = 0`;
nothing here calls it so. -/
def peg (a : Nat) : Nat → Nat
  | 0 => 0
  | 1 => a
  | 2 => a * 2
  | 3 => a * 2 + 1
  | b + 4 => (b + 4) % 2 + peg a ((b + 4) / 2) * 2
decreasing_by omega

/-! ## The sock-annotated type -/

/-- `+$sock-anno`: `[=sock src=spring]`. -/
structure Anno where
  sock : Sock
  src : Noun
  deriving DecidableEq

def Anno.toNoun (a : Anno) : Noun := C a.sock.toNoun a.src

/-- `*sock-anno`: `[[| ~] ~]`. -/
def Anno.dunno : Anno := ⟨Sock.dunno, A 0⟩

/-- `?=(^ n)`. -/
def isCellN : Noun → Bool
  | Noun.cell _ _ => true
  | Noun.atom _ => false

/-- `?=(^ c)` for a cape. -/
def Cape.isCellB : Cape → Bool
  | Cape.cell _ _ => true
  | _ => false

/-! ## `+pi` -/

namespace Pi

/-- `+cons:pi`. -/
def cons (a b : Noun) : Noun := if a = A 0 ∧ b = A 0 then A 0 else C a b

/-- `+hed:pi`. -/
def hed : Noun → Noun
  | Noun.atom 0 => A 0
  | Noun.atom p => A (peg p 2)
  | Noun.cell h _ => h

/-- `+tel:pi`. -/
def tel : Noun → Noun
  | Noun.atom 0 => A 0
  | Noun.atom p => A (peg p 3)
  | Noun.cell _ t => t

/-- `+slot:pi`.  On an axis `0` the Hoon crashes in `+cap` or loops in `+peg`
(the result here is junk); `fol-loop` calls it with an axis of at least `2`. -/
def slot (pin : Noun) (ax : Nat) : Noun :=
  if ax = 1 then pin else
  match pin with
  | Noun.atom 0 => A 0
  | Noun.atom p => A (peg p ax)
  | Noun.cell h t =>
    if _hax : ax < 2 then A 0 else
    if cap ax = 2 then slot h (mas ax) else slot t (mas ax)
termination_by ax
decreasing_by all_goals exact mas_lt ax (by omega)

/-- The inner loop of `+compose:pi`. -/
def composeLoop (b : Noun) : Noun → Noun
  | Noun.atom 0 => A 0
  | Noun.atom a => slot b a
  | Noun.cell h t => cons (composeLoop b h) (composeLoop b t)

/-- `+compose:pi`: `a` is provenance from `b`, `b` from the subject. -/
def compose (a b : Noun) : Noun := if b = A 0 then A 0 else composeLoop b a

/-- The upward loop of `+edit:pi`. -/
def editUp (don : Noun) : List (Nat × Noun) → Noun
  | [] => don
  | (2, p) :: tack => editUp (cons don p) tack
  | (_, p) :: tack => editUp (cons p don) tack

/-- The downward loop of `+edit:pi`.  An axis `0` crashes `+cap` (junk here). -/
def editDown (rec : Noun) (ax : Nat) (don : Noun) (tack : List (Nat × Noun)) : Noun :=
  if ax = 1 then editUp don tack else
  if _hax : ax < 2 then A 0 else
  if cap ax = 2 then editDown (hed rec) (mas ax) don ((2, tel rec) :: tack)
  else editDown (tel rec) (mas ax) don ((3, hed rec) :: tack)
termination_by ax
decreasing_by all_goals exact mas_lt ax (by omega)

/-- `+edit:pi`. -/
def edit (rec : Noun) (ax : Nat) (don : Noun) : Noun :=
  if ax = 1 then don else
  if rec = A 0 ∧ don = A 0 then A 0 else
  editDown rec ax don []

end Pi

/-! ## `+distribute` -/

/-- `+distribute`: the use `c` of a noun, as a use of the subject along the
noun's provenance `s`.  `+pat:ca` is called on an atom `s` that is not `0`,
where it does not crash. -/
def distribute (c : Cape) (s : Noun) : Cape :=
  match s with
  | Noun.atom 0 => Cape.no
  | Noun.atom a => if c = Cape.no then Cape.no else (Ca.pat c a).getD Cape.no
  | Noun.cell sh st =>
    if c = Cape.no then Cape.no else
    match c with
    | Cape.cell p q => Ca.uni (distribute p sh) (distribute q st)
    | _ => Ca.uni (distribute Cape.yes sh) (distribute Cape.yes st)

/-! ## `+double-int` -/

/-- The size of a noun. -/
def nsize : Noun → Nat
  | Noun.atom _ => 1
  | Noun.cell h t => nsize h + nsize t + 1

/-- The measure of `+double-int`: what a sock still knows. -/
def Sock.msr : Sock → Nat
  | Sock.void => 0
  | Sock.mk Cape.no _ => 0
  | Sock.mk _ d => nsize d

theorem Sock.msr_le (c : Cape) (d : Noun) : Sock.msr (Sock.mk c d) ≤ nsize d := by
  cases c <;> simp [Sock.msr]

theorem msr_hed_lt {c : Cape} (hc : c ≠ Cape.no) (d : Noun) :
    Sock.msr (So.hed (Sock.mk c d)) < Sock.msr (Sock.mk c d) := by
  cases c with
  | no => exact absurd rfl hc
  | yes =>
    cases d with
    | atom _ => simp [So.hed, Sock.dunno, Sock.msr, nsize]
    | cell h t => simp [So.hed, Sock.msr, nsize]; omega
  | cell ch ct =>
    cases d with
    | atom _ => simp [So.hed, Sock.dunno, Sock.msr, nsize]
    | cell h t =>
      have := Sock.msr_le ch h
      show Sock.msr (Sock.mk ch h) < nsize (C h t)
      simp only [nsize]
      omega

theorem msr_tel_lt {c : Cape} (hc : c ≠ Cape.no) (d : Noun) :
    Sock.msr (So.tel (Sock.mk c d)) < Sock.msr (Sock.mk c d) := by
  cases c with
  | no => exact absurd rfl hc
  | yes =>
    cases d with
    | atom _ => simp [So.tel, Sock.dunno, Sock.msr, nsize]
    | cell h t => simp [So.tel, Sock.msr, nsize]; omega
  | cell ch ct =>
    cases d with
    | atom _ => simp [So.tel, Sock.dunno, Sock.msr, nsize]
    | cell h t =>
      have := Sock.msr_le ct t
      show Sock.msr (Sock.mk ct t) < nsize (C h t)
      simp only [nsize]
      omega

/-- `+double-int`: the join of two sock-annotated nouns, which knows only what
both know and agree on, with the provenance both agree on. -/
def doubleInt (a b : Anno) : Anno :=
  if a = b then a else
  match a, b with
  | ⟨Sock.void, _⟩, b => b
  | a, ⟨Sock.void, _⟩ => a
  | ⟨Sock.mk ca da, ra⟩, ⟨Sock.mk cb db, rb⟩ =>
    if hc : ca = Cape.no ∨ cb = Cape.no then Anno.dunno else
    if !(ca.isCellB || cb.isCellB || isCellN ra || isCellN rb) then Anno.dunno else
    let h := doubleInt ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩
    let t := doubleInt ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩
    ⟨So.knit h.sock t.sock, Pi.cons h.src t.src⟩
termination_by Sock.msr a.sock + Sock.msr b.sock
decreasing_by
  all_goals simp only [not_or] at hc
  · exact Nat.add_lt_add (msr_hed_lt hc.1 da) (msr_hed_lt hc.2 db)
  · exact Nat.add_lt_add (msr_tel_lt hc.1 da) (msr_tel_lt hc.2 db)

theorem doubleInt_self (a : Anno) : doubleInt a a = a := by
  unfold doubleInt; simp

theorem doubleInt_void_left {a b : Anno} (h : a.sock = Sock.void) (hne : a ≠ b) :
    doubleInt a b = b := by
  obtain ⟨sa, ra⟩ := a
  simp only at h
  subst h
  rw [doubleInt]; simp [hne]

theorem doubleInt_void_right {a b : Anno} (h : b.sock = Sock.void) (ha : a.sock ≠ Sock.void)
    (hne : a ≠ b) : doubleInt a b = a := by
  obtain ⟨sb, rb⟩ := b
  obtain ⟨sa, ra⟩ := a
  simp only at h ha
  subst h
  cases sa with
  | void => exact absurd rfl ha
  | mk ca da => rw [doubleInt]; simp only [hne, if_false]; intro _ h; cases h

theorem doubleInt_mk {ca cb : Cape} {da db ra rb : Noun}
    (hne : (⟨Sock.mk ca da, ra⟩ : Anno) ≠ ⟨Sock.mk cb db, rb⟩) :
    doubleInt ⟨Sock.mk ca da, ra⟩ ⟨Sock.mk cb db, rb⟩ =
      if ca = Cape.no ∨ cb = Cape.no then Anno.dunno else
      if !(ca.isCellB || cb.isCellB || isCellN ra || isCellN rb) then Anno.dunno else
      let h := doubleInt ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩
      let t := doubleInt ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩
      ⟨So.knit h.sock t.sock, Pi.cons h.src t.src⟩ := by
  rw [doubleInt]
  simp only [hne, if_false]
  rfl

/-! ## What `+double-int` knows -/

/-- The cases of `+double-int` on two socks that are not `%void`, from the
induction hypothesis on the recursive calls. -/
theorem doubleInt_cases (P : Anno → Prop) {ca cb : Cape} {da db ra rb : Noun}
    (hne : (⟨Sock.mk ca da, ra⟩ : Anno) ≠ ⟨Sock.mk cb db, rb⟩)
    (hd : P Anno.dunno)
    (hr : ¬ (ca = Cape.no ∨ cb = Cape.no) →
      P ⟨So.knit (doubleInt ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩).sock
          (doubleInt ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩).sock,
        Pi.cons (doubleInt ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩).src
          (doubleInt ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩).src⟩) :
    P (doubleInt ⟨Sock.mk ca da, ra⟩ ⟨Sock.mk cb db, rb⟩) := by
  rw [doubleInt_mk hne]
  split
  · exact hd
  · rename_i hno
    split
    · exact hd
    · exact hr hno

theorem doubleInt_blank_left : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    a.sock.Blank → (doubleInt a b).sock.Blank := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact hb
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  obtain ⟨c, d, hs, hc⟩ := hb
  simp only at hs
  subst hs
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact ⟨c, d, rfl, hc⟩
  | mk cb db =>
    apply doubleInt_cases (fun r => r.sock.Blank) hab dunno_blank
    intro hno
    simp only [not_or] at hno
    exact knit_blank
      (ih _ _ (by have := msr_hed_lt hno.1 d; have := msr_hed_lt hno.2 db; simp only at hk ⊢; omega)
        (hed_blank ⟨_, _, rfl, hc⟩))
      (ih _ _ (by have := msr_tel_lt hno.1 d; have := msr_tel_lt hno.2 db; simp only at hk ⊢; omega)
        (tel_blank ⟨_, _, rfl, hc⟩))

theorem doubleInt_blank_right : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    b.sock.Blank → (doubleInt a b).sock.Blank := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact hb
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  obtain ⟨c, d, hs, hc⟩ := hb
  simp only at hs
  subst hs
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact ⟨c, d, rfl, hc⟩
  | mk ca da =>
    apply doubleInt_cases (fun r => r.sock.Blank) hab dunno_blank
    intro hno
    simp only [not_or] at hno
    exact knit_blank
      (ih _ _ (by have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 d; simp only at hk ⊢; omega)
        (hed_blank ⟨_, _, rfl, hc⟩))
      (ih _ _ (by have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 d; simp only at hk ⊢; omega)
        (tel_blank ⟨_, _, rfl, hc⟩))

/-- The join keeps what holds of a noun of the first side. -/
theorem doubleInt_fits_left' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    ∀ n, Fits a.sock n → Fits (doubleInt a b).sock n := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk n hf
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact hf
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => exact absurd hf id
  | mk ca da =>
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact hf
  | mk cb db =>
    apply doubleInt_cases (fun r => Fits r.sock n) hab (fits_dunno n)
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    cases n with
    | cell nh nt =>
      exact knit_fits (ih _ _ h1 _ (hed_fits hf)) (ih _ _ h2 _ (tel_fits hf))
    | atom m =>
      obtain ⟨bh, bt⟩ := hed_tel_blank_of_atom (c := ca) (d := da) (k := m) hf
      exact (knit_blank (doubleInt_blank_left _ _ _ (Nat.lt_succ_self _) bh)
        (doubleInt_blank_left _ _ _ (Nat.lt_succ_self _) bt)).fits _

/-- The join keeps what holds of a noun of the second side. -/
theorem doubleInt_fits_right' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    ∀ n, Fits b.sock n → Fits (doubleInt a b).sock n := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk n hf
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact hf
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sb with
  | void => exact absurd hf id
  | mk cb db =>
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact hf
  | mk ca da =>
    apply doubleInt_cases (fun r => Fits r.sock n) hab (fits_dunno n)
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    cases n with
    | cell nh nt =>
      exact knit_fits (ih _ _ h1 _ (hed_fits hf)) (ih _ _ h2 _ (tel_fits hf))
    | atom m =>
      obtain ⟨bh, bt⟩ := hed_tel_blank_of_atom (c := cb) (d := db) (k := m) hf
      exact (knit_blank (doubleInt_blank_right _ _ _ (Nat.lt_succ_self _) bh)
        (doubleInt_blank_right _ _ _ (Nat.lt_succ_self _) bt)).fits _

/-- **`+double-int` knows no more than its first side.** -/
theorem doubleInt_fits_left (a b : Anno) {n : Noun} (h : Fits a.sock n) :
    Fits (doubleInt a b).sock n :=
  doubleInt_fits_left' _ a b (Nat.lt_succ_self _) n h

/-- **`+double-int` knows no more than its second side.** -/
theorem doubleInt_fits_right (a b : Anno) {n : Noun} (h : Fits b.sock n) :
    Fits (doubleInt a b).sock n :=
  doubleInt_fits_right' _ a b (Nat.lt_succ_self _) n h

end SkaModel
end Formalization
