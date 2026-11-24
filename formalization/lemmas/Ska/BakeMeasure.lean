import lemmas.Ska.BakeImp

/-!
# A measure on bakes in the normal form of `+norm-sock`

The worklist of `+bake-graph` ends (`BakeEnds` of `PokeHalt.lean`) if every
change of a bake loses knowledge strictly.  `rebakeG_grows` gives the loss in
nouns (`Sub old new`); this file turns it into a decreasing number, for the
socks that `+norm-sock` makes:

* `CanonCD`: the normal form (`|` with data `0`, `&`, or a cell of normal
  capes that is neither `[| |]` nor `[& &]`), and `normCD_canon`: every
  output of `+norm-sock` has it;
* `kap`: the knowledge of a cape on its data (`&` on a noun of size `n`
  counts `2 n + 1`, `|` counts `0`, a cell the sum of its halves);
* `kap_sub`: on normal socks, `Sub a b` gives `kap b ≤ kap a`, and
  `kap b < kap a` when `a ≠ b`;
* `canon_ext`: two normal socks with the same nouns are equal, and
  `normCD_of_canon`: `+norm-sock` leaves a normal sock as it is;
* `noLoss_lessc`: a change of a bake that keeps its nouns goes to or from
  `less.c`.

For example `[[& |] [7 0]]` (cells whose head is `7`) has `kap = 3`, and
`&` on `[7 8]` has `kap = 7`: the second is under the first and knows more.

What `BakeEnds` still needs: a bake is `less.c` or the output of
`+norm-sock` (`rebakeG_canon`), and `less.c` need not be normal (the analysis
keeps `[& &]` apart from `&`), so a bake can change between `less.c` and a
normal sock with the same nouns without a loss (`noLoss_lessc`: only so).  On
the real compiler most code requirements are not normal: after pokes of
fifteen programs up to `(ream '(add 1 2)')`, 2,045 of 3,033 pairs of a code
bell and a bake (every variant, and every memo entry under its own code
requirement) had `!=(less.c (norm-sock less.c))`.  So "the output of
`+app:ca` is normal" is false, and the way left is to bound the changes back
to `less.c`, which happen only when no caller's site informs the callee any
more (`ks = []`): for example from a `+know` whose sites do not shrink when
the caller's bake loses knowledge, or by counting such changes against the
losses of the callers' bakes.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-- The normal form of `+norm-sock` on a cape and its data. -/
def CanonCD : Cape → Noun → Prop
  | Cape.no, d => d = A 0
  | Cape.yes, _ => True
  | Cape.cell h t, d => ∃ dh dt, d = C dh dt ∧ CanonCD h dh ∧ CanonCD t dt ∧
      ¬ (h = Cape.no ∧ t = Cape.no) ∧ ¬ (h = Cape.yes ∧ t = Cape.yes)

/-- A sock in the normal form of `+norm-sock`. -/
def Canon : Sock → Prop
  | Sock.void => True
  | Sock.mk c d => CanonCD c d

/-- **`+norm-sock` gives the normal form.** -/
theorem normCD_canon : ∀ {c : Cape} {d : Noun} {p : Cape × Noun}, normCD c d = some p → CanonCD p.1 p.2
  | Cape.no, _, _, h => by simp only [normCD, Option.some.injEq] at h; rw [← h]; rfl
  | Cape.yes, _, _, h => by simp only [normCD, Option.some.injEq] at h; rw [← h]; trivial
  | Cape.cell _ _, Noun.atom _, _, h => by simp [normCD] at h
  | Cape.cell h t, Noun.cell dh dt, p, e => by
    simp only [normCD, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
    obtain ⟨l, hl, r, hr, rfl⟩ := e
    have cl := normCD_canon hl
    have cr := normCD_canon hr
    by_cases hnn : l.1 = Cape.no ∧ r.1 = Cape.no
    · rw [if_pos hnn]; rfl
    · rw [if_neg hnn]
      by_cases hy : (l.1 = Cape.yes ∨ l.1 = Cape.no) ∧ l.1 = r.1
      · rw [if_pos hy]
        rcases hy with ⟨hy1 | hy1, hy2⟩
        · simp only [hy1]; trivial
        · exact absurd ⟨hy1, hy2 ▸ hy1⟩ hnn
      · rw [if_neg hy]
        refine ⟨l.2, r.2, rfl, cl, cr, hnn, fun ⟨h1, h2⟩ => hy ⟨Or.inl h1, h1.trans h2.symm⟩⟩

theorem normSockH_canon {s s' : Sock} (h : normSockH s = some s') : Canon s' := by
  cases s with
  | void => simp only [normSockH, Option.some.injEq] at h; subst h; trivial
  | mk c d =>
    simp only [normSockH, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    exact normCD_canon hp

/-- `+norm-sock` leaves a normal sock as it is. -/
theorem normCD_of_canon : ∀ {c : Cape} {d : Noun}, CanonCD c d → normCD c d = some (c, d)
  | Cape.no, _, h => by simp only [CanonCD] at h; subst h; rfl
  | Cape.yes, _, _ => rfl
  | Cape.cell h t, _, ⟨dh, dt, rfl, ch, ct, hnn, hyy⟩ => by
    simp only [normCD, normCD_of_canon ch, normCD_of_canon ct, Option.bind_some, Option.map_some]
    rw [if_neg hnn, if_neg]
    rintro ⟨hy | hy, e⟩
    · exact hyy ⟨hy, e ▸ hy⟩
    · exact hnn ⟨hy, e ▸ hy⟩

theorem normSockH_of_canon {s : Sock} (h : Canon s) : normSockH s = some s := by
  cases s with
  | void => rfl
  | mk c d => simp only [normSockH, normCD_of_canon (c := c) (d := d) h, Option.map_some]

/-! ## The nouns of a normal sock -/

/-- A normal cape that knows nothing is `|`. -/
theorem canon_isNo : ∀ {c : Cape} {d : Noun}, CanonCD c d → c.isNo = true → c = Cape.no
  | Cape.no, _, _, _ => rfl
  | Cape.yes, _, _, h => by simp [Cape.isNo] at h
  | Cape.cell h t, _, ⟨dh, dt, _, ch, ct, hnn, _⟩, e => by
    simp only [Cape.isNo, Bool.and_eq_true] at e
    exact absurd ⟨canon_isNo ch e.1, canon_isNo ct e.2⟩ hnn

/-- The data of a normal cape is one of its nouns. -/
theorem canon_self : ∀ {c : Cape} {d : Noun}, CanonCD c d → FitsCape c d d
  | Cape.no, _, _ => trivial
  | Cape.yes, _, _ => rfl
  | Cape.cell _ _, _, ⟨dh, dt, rfl, ch, ct, _, _⟩ => Or.inr ⟨dh, dt, dh, dt, rfl, rfl, canon_self ch, canon_self ct⟩

/-- The nouns of a normal cell cape are the cells of nouns of its halves. -/
theorem canon_cell_fits {h t : Cape} {d x : Noun} (hc : CanonCD (Cape.cell h t) d) (hx : FitsCape (Cape.cell h t) d x) :
    ∃ dh dt xh xt, d = C dh dt ∧ x = C xh xt ∧ FitsCape h dh xh ∧ FitsCape t dt xt := by
  rcases hx with hno | hx
  · have := canon_isNo hc hno
    cases this
  · exact hx

/-- A normal cape with one noun is `&`. -/
theorem canon_single : ∀ {c : Cape} {d e : Noun}, CanonCD c d → (∀ x, FitsCape c d x → x = e) → c = Cape.yes
  | Cape.no, _, _, _, h => by
    have h0 := h (A 0) trivial
    have h1 := h (A 1) trivial
    rw [← h1] at h0
    cases h0
  | Cape.yes, _, _, _, _ => rfl
  | Cape.cell h t, d, e, hc, hs => by
    obtain ⟨dh, dt, rfl, ch, ct, _, hyy⟩ := hc
    have hc' : CanonCD (Cape.cell h t) (C dh dt) := ⟨dh, dt, rfl, ch, ct, by assumption, hyy⟩
    have he := hs _ (canon_self hc')
    subst he
    have sh : ∀ x, FitsCape h dh x → x = dh := fun x hx => by
      have := hs (C x dt) (Or.inr ⟨dh, dt, x, dt, rfl, rfl, hx, canon_self ct⟩)
      cases this; rfl
    have st : ∀ x, FitsCape t dt x → x = dt := fun x hx => by
      have := hs (C dh x) (Or.inr ⟨dh, dt, dh, x, rfl, rfl, canon_self ch, hx⟩)
      cases this; rfl
    exact absurd ⟨canon_single ch sh, canon_single ct st⟩ hyy

/-! ## The measure -/

/-- The size of a noun. -/
def nsz : Noun → Nat
  | Noun.atom _ => 1
  | Noun.cell x y => nsz x + nsz y + 1

/-- What a cape knows of its data. -/
def kap : Cape → Noun → Nat
  | Cape.no, _ => 0
  | Cape.yes, d => 2 * nsz d + 1
  | Cape.cell h t, Noun.cell dh dt => kap h dh + kap t dt
  | Cape.cell _ _, Noun.atom _ => 0

theorem kap_yes_cell (x y : Noun) : kap Cape.yes (C x y) = kap Cape.yes x + kap Cape.yes y + 1 := by
  simp only [kap, nsz]; omega

/-- A normal cape that is not `|` knows something. -/
theorem kap_pos : ∀ {c : Cape} {d : Noun}, CanonCD c d → c ≠ Cape.no → 0 < kap c d
  | Cape.no, _, _, h => absurd rfl h
  | Cape.yes, _, _, _ => by simp only [kap]; omega
  | Cape.cell h t, _, ⟨dh, dt, rfl, ch, ct, hnn, _⟩, _ => by
    show 0 < kap h dh + kap t dt
    by_cases eh : h = Cape.no
    · have := kap_pos ct (fun et => hnn ⟨eh, et⟩); omega
    · have := kap_pos ch eh; omega

/-- A normal cape knows no more than `&` on any of its nouns, and less unless
it is `&`. -/
theorem kap_le_yes : ∀ {c : Cape} {d x : Noun}, CanonCD c d → FitsCape c d x →
    kap c d ≤ kap Cape.yes x ∧ (c ≠ Cape.yes → kap c d < kap Cape.yes x)
  | Cape.no, _, x, _, _ => by
    refine ⟨Nat.zero_le _, fun _ => ?_⟩
    simp only [kap]; omega
  | Cape.yes, d, x, _, hx => by
    simp only [FitsCape] at hx
    subst hx
    exact ⟨Nat.le_refl _, fun h => absurd rfl h⟩
  | Cape.cell h t, d, x, hc, hx => by
    obtain ⟨dh, dt, xh, xt, rfl, rfl, fh, ft⟩ := canon_cell_fits hc hx
    obtain ⟨_, _, e, ch, ct, _, _⟩ := hc
    cases e
    have ih1 := (kap_le_yes ch fh).1
    have ih2 := (kap_le_yes ct ft).1
    have hk : kap (Cape.cell h t) (C dh dt) = kap h dh + kap t dt := rfl
    rw [hk, kap_yes_cell]
    constructor <;> intros <;> omega

/-- The halves of a sub-sock of a normal cell cape. -/
theorem sub_halves {h t h' t' : Cape} {dh dt dh' dt' : Noun}
    (hb : CanonCD (Cape.cell h t) (C dh dt)) (ha : CanonCD (Cape.cell h' t') (C dh' dt'))
    (hs : ∀ x, FitsCape (Cape.cell h' t') (C dh' dt') x → FitsCape (Cape.cell h t) (C dh dt) x) :
    (∀ x, FitsCape h' dh' x → FitsCape h dh x) ∧ (∀ x, FitsCape t' dt' x → FitsCape t dt x) := by
  obtain ⟨_, _, e', ch', ct', _, _⟩ := ha
  cases e'
  constructor
  · intro x hx
    have := hs (C x dt') (Or.inr ⟨dh', dt', x, dt', rfl, rfl, hx, canon_self ct'⟩)
    obtain ⟨_, _, _, _, e1, e2, f1, _⟩ := canon_cell_fits hb this
    cases e1; cases e2; exact f1
  · intro x hx
    have := hs (C dh' x) (Or.inr ⟨dh', dt', dh', x, rfl, rfl, canon_self ch', hx⟩)
    obtain ⟨_, _, _, _, e1, e2, _, f2⟩ := canon_cell_fits hb this
    cases e1; cases e2; exact f2

/-- **The measure on normal capes**: a cape whose nouns include those of
another knows no more, and strictly less when the two differ. -/
theorem kap_sub : ∀ (cb : Cape) {db : Noun} {ca : Cape} {da : Noun}, CanonCD ca da → CanonCD cb db →
    (∀ x, FitsCape ca da x → FitsCape cb db x) →
    kap cb db ≤ kap ca da ∧ ((ca, da) ≠ (cb, db) → kap cb db < kap ca da)
  | Cape.no, db, ca, da, ha, hb, _ => by
    refine ⟨Nat.zero_le _, fun hne => ?_⟩
    show 0 < kap ca da
    by_cases e : ca = Cape.no
    · subst e
      simp only [CanonCD] at ha hb
      subst ha hb
      exact absurd rfl hne
    · exact kap_pos ha e
  | Cape.yes, db, ca, da, ha, _, hs => by
    have hd : da = db := (hs da (canon_self ha)).symm ▸ rfl
    have hd' : ∀ x, FitsCape ca da x → x = db := fun x hx => hs x hx
    have ey := canon_single ha hd'
    subst ey hd
    exact ⟨Nat.le_refl _, fun hne => absurd rfl hne⟩
  | Cape.cell h t, db, ca, da, ha, hb, hs => by
    obtain ⟨dh, dt, rfl, ch, ct, hnn, hyy⟩ := hb
    have hb' : CanonCD (Cape.cell h t) (C dh dt) := ⟨dh, dt, rfl, ch, ct, hnn, hyy⟩
    have hk : kap (Cape.cell h t) (C dh dt) = kap h dh + kap t dt := rfl
    cases ca with
    | no =>
      have := hs (A 0) trivial
      obtain ⟨_, _, _, _, _, e, _, _⟩ := canon_cell_fits hb' this
      cases e
    | yes =>
      have k := kap_le_yes hb' (hs da (canon_self ha))
      exact ⟨Nat.le_of_lt (k.2 (by simp)), fun _ => k.2 (by simp)⟩
    | cell h' t' =>
      obtain ⟨dh', dt', rfl, ch', ct', hnn', hyy'⟩ := ha
      have ha' : CanonCD (Cape.cell h' t') (C dh' dt') := ⟨dh', dt', rfl, ch', ct', hnn', hyy'⟩
      obtain ⟨s1, s2⟩ := sub_halves hb' ha' hs
      have i1 := kap_sub h ch' ch s1
      have i2 := kap_sub t ct' ct s2
      have hk' : kap (Cape.cell h' t') (C dh' dt') = kap h' dh' + kap t' dt' := rfl
      rw [hk, hk']
      refine ⟨by omega, fun hne => ?_⟩
      by_cases e1 : (h', dh') = (h, dh)
      · have e2 : (t', dt') ≠ (t, dt) := fun e2 => by
          simp only [Prod.mk.injEq] at e1 e2
          obtain ⟨rfl, rfl⟩ := e1
          obtain ⟨rfl, rfl⟩ := e2
          exact hne rfl
        have := i2.2 e2; omega
      · have := i1.2 e1; omega

/-- The measure on socks, for the bakes (which are never `%void`). -/
def kapS : Sock → Nat
  | Sock.void => 0
  | Sock.mk c d => kap c d

/-- **A bake that loses knowledge loses measure**: of two normal socks that
are not `%void`, if the nouns of the first are nouns of the second and the
two differ, the second has a smaller measure. -/
theorem kapS_lt {a b : Sock} (ha : Canon a) (hb : Canon b) (va : a ≠ Sock.void) (vb : b ≠ Sock.void)
    (hs : Sub a b) (hne : a ≠ b) : kapS b < kapS a := by
  cases a with
  | void => exact absurd rfl va
  | mk ca da =>
  cases b with
  | void => exact absurd rfl vb
  | mk cb db =>
  exact (kap_sub cb ha hb hs).2 fun e => by
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact hne rfl

theorem kapS_le {a b : Sock} (ha : Canon a) (hb : Canon b) (va : a ≠ Sock.void) (vb : b ≠ Sock.void)
    (hs : Sub a b) : kapS b ≤ kapS a := by
  cases a with
  | void => exact absurd rfl va
  | mk ca da =>
  cases b with
  | void => exact absurd rfl vb
  | mk cb db =>
  exact (kap_sub cb ha hb hs).1

/-- **Normal socks are canonical**: two normal socks with the same nouns are
equal. -/
theorem canon_ext {a b : Sock} (ha : Canon a) (hb : Canon b) (hab : Sub a b) (hba : Sub b a) : a = b := by
  cases a with
  | void =>
    cases b with
    | void => rfl
    | mk cb db => exact absurd (hba _ (canon_self (c := cb) (d := db) hb)) id
  | mk ca da =>
  cases b with
  | void => exact absurd (hab _ (canon_self (c := ca) (d := da) ha)) id
  | mk cb db =>
  refine Classical.byContradiction fun hne => ?_
  have h1 := kapS_lt ha hb (by simp) (by simp) hab hne
  have h2 := kapS_lt hb ha (by simp) (by simp) hba (Ne.symm hne)
  omega

/-! ## The bakes of the worklist -/

/-- **A bake is `less.c` or normal**: what `bakeOf` gives, and what a rebake
of it gives. -/
theorem bakeOf_canon {fixed : Bool} {lessc s : Sock} {ks : List Sock} (h : bakeOf fixed lessc ks = some s) :
    s = lessc ∨ Canon s := by
  unfold bakeOf at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inl rfl
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨both, hb, hv, _, rfl⟩ := h
      split
      · exact Or.inr (normSockH_canon hb)
      · exact Or.inl rfl

theorem rebakeG_canon {lessc bake s : Sock} {old : Option Sock} {g g' : Nat} (hb : bake = lessc ∨ Canon bake)
    (h : rebakeG bake old g = some (s, g')) : s = lessc ∨ Canon s := by
  unfold rebakeG at h
  split at h
  · cases h; exact hb
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨hv, _, h⟩ := h
    split at h
    · cases h; exact hb
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨s', hs', rfl, -⟩ := h
      exact Or.inr (normSockH_canon hs')

/-- **A change without a loss goes to or from `less.c`**: when two bakes
that are each `less.c` or normal have the same nouns and differ, one of
them is `less.c`.  So the only changes of a bake that `kapS` may miss are the
changes between `less.c` and the normal sock with its nouns. -/
theorem noLoss_lessc {lessc o s : Sock} (hs : s = lessc ∨ Canon s) (ho : o = lessc ∨ Canon o)
    (h1 : Sub o s) (h2 : Sub s o) (hne : s ≠ o) : s = lessc ∨ o = lessc := by
  rcases hs with hs | hs
  · exact Or.inl hs
  rcases ho with ho | ho
  · exact Or.inr ho
  exact absurd (canon_ext hs ho h2 h1) hne

section Loop

variable {M : Type → Type → Type} [Treap M]

/-- **Every bake at the end of the worklist is its code requirement or
normal.** -/
theorem bakes_canon (E : BEnv M) {n : Nat} {st : BSt M}
    (h : bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st) :
    ∀ c s, Treap.get st.bak c = some s → s = c.less ∨ Canon s :=
  bakeLoop_pred E (I := fun _ _ => True) (Or.inl rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ hb _ hre => rebakeG_canon (bakeOf_canon hb) hre) h

end Loop

end Bake

end SkaModel
end Formalization
