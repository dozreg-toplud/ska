import lemmas.Ska.BakeGraph

/-!
# When a bake implies its code requirement

A bake of `+bake-graph` is `norm-sock (uni-sock less.c meet)`, intersected
with the old bake by `+purr:so` and `+norm-sock` when it is not a loss.
`uniSock_drops_less` (`Bake.lean`) shows that it need not imply `less.c`.
This file proves how far it does:

* `uniSock_left`: if `less.c` and the meet share a noun, every noun of
  `uni-sock less.c meet` fits `less.c`;
* `purr_sub`: the `+purr:so` of two socks that each have a noun and imply a
  sock `L` implies `L` (no normal form needed);
* `normSockH_rev`: `+norm-sock` adds no noun (with `normSockH_fits`, it keeps
  exactly the nouns of its sock);
* `bakeOf_sub`, `rebake_sub`: so a bake implies `less.c` and has a noun when
  one of the sites it is made from shares a noun with `less.c`, and a rebake
  of two such bakes does too.

What is left of the question is whether every callee with a bake made from
sites has a site whose sock shares a noun with its code requirement.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Bake

/-- Every noun of `a` is a noun of `b`. -/
def Sub (a b : Sock) : Prop := ∀ x, Fits a x → Fits b x

theorem Sub.refl (a : Sock) : Sub a a := fun _ h => h

theorem Sub.trans {a b c : Sock} (h1 : Sub a b) (h2 : Sub b c) : Sub a c := fun x h => h2 x (h1 x h)

/-! ## Facts about the nouns of a sock -/

/-- A cape that every noun fits, on some data, knows nothing. -/
theorem isNo_of_all : ∀ {c : Cape} {d : Noun}, (∀ x, FitsCape c d x) → c.isNo = true
  | Cape.yes, d, h => by
    exfalso
    cases d with
    | atom n =>
      have := h (A (n + 1))
      simp [FitsCape, A] at this
    | cell _ _ =>
      have := h (A 0)
      simp [FitsCape, A] at this
  | Cape.no, _, _ => rfl
  | Cape.cell _ _, _, h => by
    have := h (A 0)
    simp only [FitsCape] at this
    rcases this with hno | ⟨_, _, _, _, _, hn, _⟩
    · exact hno
    · cases hn

/-- A sock that every noun fits is blank. -/
theorem blank_of_all {s : Sock} (h : ∀ x, Fits s x) : s.Blank := by
  cases s with
  | void => exact absurd (h (A 0)) id
  | mk c d => exact ⟨c, d, rfl, isNo_of_all h⟩

/-- The nouns of a cons of two socks: every noun, if both know nothing, else
the cells of their nouns. -/
theorem knit_fits_inv {u v : Sock} {x : Noun} (h : Fits (So.knit u v) x) :
    (u.Blank ∧ v.Blank) ∨ ∃ x1 x2, x = C x1 x2 ∧ Fits u x1 ∧ Fits v x2 := by
  cases u with
  | void => exact absurd h id
  | mk l d1 =>
  cases v with
  | void => exact absurd h id
  | mk r d2 =>
  simp only [So.knit] at h
  split at h
  · rename_i hc
    unfold Ca.con at hc
    split at hc
    · rename_i hlr
      obtain ⟨rfl, rfl⟩ := hlr
      exact Or.inl ⟨⟨_, _, rfl, rfl⟩, ⟨_, _, rfl, rfl⟩⟩
    · cases hc
  · rename_i hc
    simp only [Fits] at h
    rw [con_ne_no hc] at h
    simp only [FitsCape] at h
    rcases h with hno | ⟨dh, dt, nh, nt, hd, rfl, hh, ht⟩
    · simp only [Bool.and_eq_true] at hno
      exact Or.inl ⟨⟨_, _, rfl, hno.1⟩, ⟨_, _, rfl, hno.2⟩⟩
    · cases hd
      exact Or.inr ⟨nh, nt, rfl, hh, ht⟩

/-- A sock with a cell among its nouns has every cell of a noun of its head
and a noun of its tail. -/
theorem fits_join_of_cell {s : Sock} {y1 y2 x1 x2 : Noun} (hy : Fits s (C y1 y2))
    (h1 : Fits (So.hed s) x1) (h2 : Fits (So.tel s) x2) : Fits s (C x1 x2) := by
  cases s with
  | void => exact absurd hy id
  | mk c d =>
  cases c with
  | no => trivial
  | yes =>
    simp only [Fits, FitsCape] at hy
    subst hy
    simp only [Fits, FitsCape, So.hed, So.tel] at h1 h2 ⊢
    rw [h1, h2]
  | cell ch ct =>
    simp only [Fits, FitsCape] at hy
    rcases hy with hno | ⟨dh, dt, _, _, rfl, _, _, _⟩
    · exact Or.inl hno
    · exact Or.inr ⟨dh, dt, x1, x2, rfl, rfl, h1, h2⟩

/-- A sock with a cell among its nouns, whose head and tail every noun fits,
is blank. -/
theorem blank_of_hed_tel {s : Sock} {y1 y2 : Noun} (hy : Fits s (C y1 y2))
    (h1 : ∀ x, Fits (So.hed s) x) (h2 : ∀ x, Fits (So.tel s) x) : s.Blank := by
  cases s with
  | void => exact absurd hy id
  | mk c d =>
  cases c with
  | no => exact ⟨_, _, rfl, rfl⟩
  | yes =>
    simp only [Fits, FitsCape] at hy
    subst hy
    exact absurd (isNo_of_all (c := Cape.yes) (d := y1) (h1 ·)) (by simp [Cape.isNo])
  | cell ch ct =>
    simp only [Fits, FitsCape] at hy
    rcases hy with hno | ⟨dh, dt, _, _, rfl, _, _, _⟩
    · exact ⟨_, _, rfl, hno⟩
    · have e1 := isNo_of_all (c := ch) (d := dh) (h1 ·)
      have e2 := isNo_of_all (c := ct) (d := dt) (h2 ·)
      exact ⟨_, _, rfl, by simp [Cape.isNo, e1, e2]⟩

/-- The three kinds of sock: blank, only cells, or at most one noun. -/
theorem sock_cases (L : Sock) :
    L.Blank ∨ (∀ x, Fits L x → ∃ x1 x2, x = C x1 x2) ∨ (∀ x y, Fits L x → Fits L y → x = y) := by
  cases L with
  | void => exact Or.inr (Or.inl fun _ h => absurd h id)
  | mk c d =>
  cases c with
  | no => exact Or.inl ⟨_, _, rfl, rfl⟩
  | yes => exact Or.inr (Or.inr fun _ _ hx hy => hx.trans hy.symm)
  | cell ch ct =>
    by_cases hno : (ch.isNo && ct.isNo) = true
    · exact Or.inl ⟨_, _, rfl, hno⟩
    · refine Or.inr (Or.inl fun x hx => ?_)
      simp only [Fits, FitsCape] at hx
      rcases hx with h | ⟨_, _, nh, nt, _, rfl, _, _⟩
      · exact absurd h hno
      · exact ⟨nh, nt, rfl⟩

/-- The head of a sock under a sock with a cell among its nouns is under the
head. -/
theorem hed_sub {a L : Sock} {y1 y2 : Noun} (h : Sub a L) (hy : Fits a (C y1 y2)) :
    Sub (So.hed a) (So.hed L) := fun x hx =>
  hed_fits (h _ (fits_join_of_cell hy hx (tel_fits hy)))

theorem tel_sub {a L : Sock} {y1 y2 : Noun} (h : Sub a L) (hy : Fits a (C y1 y2)) :
    Sub (So.tel a) (So.tel L) := fun x hx =>
  tel_fits (h _ (fits_join_of_cell hy (hed_fits hy) hx))

/-- **A cons under a sock with a cell among its nouns**: if the head is
under its head and the tail under its tail. -/
theorem knit_sub {u v L : Sock} {y1 y2 : Noun} (hy : Fits L (C y1 y2)) (hu : Sub u (So.hed L))
    (hv : Sub v (So.tel L)) : Sub (So.knit u v) L := by
  intro x hx
  rcases knit_fits_inv hx with ⟨bu, bv⟩ | ⟨x1, x2, rfl, h1, h2⟩
  · exact (blank_of_hed_tel hy (fun z => hu z (bu.fits z)) (fun z => hv z (bv.fits z))).fits x
  · exact fits_join_of_cell hy (hu x1 h1) (hv x2 h2)

/-! ## `+uni-sock` -/

/-- **`+uni-sock` keeps the first sock when the two share a noun**: every
noun of the union fits the first sock. -/
theorem uniSock_left : ∀ (k : Nat) (a b : Sock), So.depth a + So.depth b < k → ∀ x0, Fits a x0 → Fits b x0 →
    Sub (uniSock a b) a := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk x0 ha hb x hx
  rw [uniSock.eq_def] at hx
  by_cases hab : a = b
  · rw [if_pos hab] at hx; exact hx
  rw [if_neg hab] at hx
  cases a with
  | void => exact absurd ha id
  | mk ca da =>
  cases b with
  | void => exact hx
  | mk cb db =>
  dsimp only at hx
  by_cases e1 : Ca.all ca = true
  · rw [if_pos e1] at hx; exact hx
  rw [if_neg e1] at hx
  by_cases e2 : Ca.all cb = true
  · rw [if_pos e2] at hx
    have h1 : x = db := all_fits e2 hx
    have h2 : x0 = db := all_fits e2 hb
    rw [h1, ← h2]; exact ha
  rw [if_neg e2] at hx
  by_cases e3 : ca = Cape.no
  · subst e3; trivial
  rw [if_neg e3] at hx
  by_cases e4 : cb = Cape.no
  · rw [if_pos e4] at hx; exact hx
  rw [if_neg e4] at hx
  cases ca with
  | yes => exact hx
  | no => exact absurd rfl e3
  | cell ah aT =>
  cases cb with
  | yes => exact hx
  | no => exact absurd rfl e4
  | cell bh bT =>
  dsimp only at hx
  have d1 := So.depth_hed_lt (ch := ah) (ct := aT) (d := da)
  have d2 := So.depth_hed_lt (ch := bh) (ct := bT) (d := db)
  have d3 := So.depth_tel_lt (ch := ah) (ct := aT) (d := da)
  have d4 := So.depth_tel_lt (ch := bh) (ct := bT) (d := db)
  by_cases hno : (ah.isNo && aT.isNo) = true
  · exact Or.inl hno
  have ha' := ha
  simp only [Fits, FitsCape] at ha'
  rcases ha' with h | ⟨dah, dat, x01, x02, rfl, rfl, _, _⟩
  · exact absurd h hno
  have hu := ih _ _ (by omega) x01 (hed_fits ha) (hed_fits hb)
  have hv := ih _ _ (by omega) x02 (tel_fits ha) (tel_fits hb)
  exact knit_sub ha hu hv x hx

/-! ## `+purr:so` -/

/-- The meet of two nouns of `L` is under `L`. -/
theorem purrData_sub : ∀ (d1 d2 : Noun) (L : Sock), Fits L d1 → Fits L d2 → Sub (So.purrData d1 d2) L
  | d1, d2, L, h1, h2 => by
    intro x hx
    rw [So.purrData.eq_def] at hx
    by_cases e : d1 = d2
    · rw [if_pos e] at hx
      simp only [Fits, FitsCape] at hx
      rw [hx]; exact h1
    rw [if_neg e] at hx
    have hblank : (¬ ∃ p q r s, d1 = C p q ∧ d2 = C r s) → Fits L x := by
      intro hnc
      rcases sock_cases L with hb | hc | hs
      · exact hb.fits x
      · obtain ⟨p, q, rfl⟩ := hc d1 h1
        obtain ⟨r, s, rfl⟩ := hc d2 h2
        exact absurd ⟨p, q, r, s, rfl, rfl⟩ hnc
      · exact absurd (hs _ _ h1 h2) e
    match d1, d2, h1, h2, hx with
    | Noun.cell p q, Noun.cell r s, h1, h2, hx =>
      exact knit_sub h1 (purrData_sub p r _ (hed_fits h1) (hed_fits h2))
        (purrData_sub q s _ (tel_fits h1) (tel_fits h2)) x hx
    | Noun.atom _, _, _, _, _ => exact hblank (fun ⟨_, _, _, _, h, _⟩ => Noun.noConfusion h)
    | Noun.cell _ _, Noun.atom _, _, _, _ => exact hblank (fun ⟨_, _, _, _, _, h⟩ => Noun.noConfusion h)

/-- The cons case of `+purr:so`: both socks have a cell among their nouns. -/
theorem purr_knit_sub {a b L : Sock} {ya1 ya2 yb1 yb2 : Noun} (ha : Sub a L) (hb : Sub b L)
    (hya : Fits a (C ya1 ya2)) (hyb : Fits b (C yb1 yb2))
    (ih : ∀ a' b' L', Sub a' L' → Sub b' L' → (∃ y, Fits a' y) → (∃ y, Fits b' y) →
      (a' = So.hed a ∧ b' = So.hed b ∨ a' = So.tel a ∧ b' = So.tel b) → Sub (So.purr a' b') L') :
    Sub (So.knit (So.purr (So.hed a) (So.hed b)) (So.purr (So.tel a) (So.tel b))) L :=
  knit_sub (ha _ hya)
    (ih _ _ _ (hed_sub ha hya) (hed_sub hb hyb) ⟨_, hed_fits hya⟩ ⟨_, hed_fits hyb⟩ (Or.inl ⟨rfl, rfl⟩))
    (ih _ _ _ (tel_sub ha hya) (tel_sub hb hyb) ⟨_, tel_fits hya⟩ ⟨_, tel_fits hyb⟩ (Or.inr ⟨rfl, rfl⟩))

/-- In the cons case, a sock with a noun under `L` has a cell among its nouns
when another one does, unless `L` is blank. -/
theorem cell_of_other {a b L : Sock} {y : Noun} {yb1 yb2 : Noun} (ha : Sub a L) (hb : Sub b L)
    (hy : Fits a y) (hyb : Fits b (C yb1 yb2)) :
    L.Blank ∨ ∃ y1 y2, Fits a (C y1 y2) := by
  rcases sock_cases L with hl | hc | hs
  · exact Or.inl hl
  · obtain ⟨y1, y2, rfl⟩ := hc y (ha y hy)
    exact Or.inr ⟨y1, y2, hy⟩
  · have e := hs _ _ (ha y hy) (hb _ hyb)
    subst e
    exact Or.inr ⟨yb1, yb2, hy⟩

/-- **The meet of two socks under `L` is under `L`**, when each has a noun. -/
theorem purr_sub : ∀ (k : Nat) (a b L : Sock), So.depth a + So.depth b < k → Sub a L → Sub b L →
    (∃ y, Fits a y) → (∃ y, Fits b y) → Sub (So.purr a b) L := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b L hk ha hb ⟨ya, hya⟩ ⟨yb, hyb⟩ x hx
  rw [So.purr.eq_def] at hx
  by_cases hab : a = b
  · rw [if_pos hab] at hx; exact ha x hx
  rw [if_neg hab] at hx
  cases a with
  | void => exact absurd hya id
  | mk c1 d1 =>
  cases b with
  | void => exact absurd hyb id
  | mk c2 d2 =>
  dsimp only at hx
  by_cases e : c1 = Cape.no ∨ c2 = Cape.no
  · rw [if_pos e] at hx
    rcases e with rfl | rfl
    · exact ha x trivial
    · exact hb x trivial
  rw [if_neg e] at hx
  have ihk : ∀ (a' b' : Sock), So.depth a' + So.depth b' < k → ∀ L', Sub a' L' → Sub b' L' →
      (∃ y, Fits a' y) → (∃ y, Fits b' y) → Sub (So.purr a' b') L' :=
    fun a' b' hd L' => ih a' b' L' hd
  -- a cell cape that knows nothing makes `L` blank
  have hblankA : ∀ ch ct, c1 = Cape.cell ch ct → (ch.isNo && ct.isNo) = true → Fits L x := by
    intro ch ct hc hno; subst hc; exact ha x (Or.inl hno)
  have hblankB : ∀ ch ct, c2 = Cape.cell ch ct → (ch.isNo && ct.isNo) = true → Fits L x := by
    intro ch ct hc hno; subst hc; exact hb x (Or.inl hno)
  cases c1 with
  | no => exact absurd (Or.inl rfl) e
  | yes =>
    cases c2 with
    | no => exact absurd (Or.inr rfl) e
    | yes =>
      simp only [Fits, FitsCape] at hya hyb
      subst hya hyb
      exact purrData_sub _ _ L (ha _ rfl) (hb _ rfl) x hx
    | cell bh bT =>
      dsimp only at hx
      by_cases hno : (bh.isNo && bT.isNo) = true
      · exact hblankB bh bT rfl hno
      have hyb' := hyb
      simp only [Fits, FitsCape] at hyb'
      rcases hyb' with h | ⟨db1, db2, yb1, yb2, rfl, rfl, _, _⟩
      · exact absurd h hno
      rcases cell_of_other ha hb hya hyb with hl | ⟨ya1, ya2, hya2⟩
      · exact hl.fits x
      have d1' := So.depth_hed_le (Sock.mk Cape.yes d1)
      have d2' := So.depth_hed_lt (ch := bh) (ct := bT) (d := C db1 db2)
      have d3' := So.depth_tel_le (Sock.mk Cape.yes d1)
      have d4' := So.depth_tel_lt (ch := bh) (ct := bT) (d := C db1 db2)
      refine purr_knit_sub ha hb hya2 hyb (fun a' b' L' h1 h2 h3 h4 hw => ?_) x hx
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ihk _ _ (by omega) L' h1 h2 h3 h4
      · exact ihk _ _ (by omega) L' h1 h2 h3 h4
  | cell ah aT =>
    by_cases hno : (ah.isNo && aT.isNo) = true
    · exact hblankA ah aT rfl hno
    have hya' := hya
    simp only [Fits, FitsCape] at hya'
    rcases hya' with h | ⟨da1, da2, ya1, ya2, rfl, rfl, _, _⟩
    · exact absurd h hno
    have d1' := So.depth_hed_lt (ch := ah) (ct := aT) (d := C da1 da2)
    have d2' := So.depth_hed_le (Sock.mk c2 d2)
    have d3' := So.depth_tel_lt (ch := ah) (ct := aT) (d := C da1 da2)
    have d4' := So.depth_tel_le (Sock.mk c2 d2)
    rcases cell_of_other hb ha hyb hya with hl | ⟨yb1, yb2, hyb2⟩
    · exact hl.fits x
    have key := purr_knit_sub ha hb hya hyb2 (fun a' b' L' h1 h2 h3 h4 hw => by
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ihk _ _ (by omega) L' h1 h2 h3 h4
      · exact ihk _ _ (by omega) L' h1 h2 h3 h4)
    cases c2 with
    | no => exact absurd (Or.inr rfl) e
    | yes => exact key x hx
    | cell bh bT => exact key x hx

/-! ## `+norm-sock` -/

/-- `+norm-sock` adds no noun. -/
theorem normCD_rev : ∀ {c : Cape} {d x : Noun} {p : Cape × Noun}, normCD c d = some p →
    FitsCape p.1 p.2 x → FitsCape c d x
  | Cape.no, _, _, _, _, _ => trivial
  | Cape.yes, _, _, _, h, hf => by simp only [normCD, Option.some.injEq] at h; rw [← h] at hf; exact hf
  | Cape.cell _ _, Noun.atom _, _, _, h, _ => by simp [normCD] at h
  | Cape.cell h t, Noun.cell dh dt, x, p, e, hf => by
    simp only [normCD, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
    obtain ⟨l, hl, r, hr, rfl⟩ := e
    -- a part normalized to `|` knows nothing
    have allL : l.1 = Cape.no → h.isNo = true := fun hn =>
      isNo_of_all (d := dh) fun z => normCD_rev hl (by rw [hn]; trivial)
    have allR : r.1 = Cape.no → t.isNo = true := fun hn =>
      isNo_of_all (d := dt) fun z => normCD_rev hr (by rw [hn]; trivial)
    split at hf
    · rename_i hnn
      exact Or.inl (by simp [allL hnn.1, allR hnn.2])
    · rename_i hnn
      dsimp only at hf
      split at hf
      · rename_i hy
        obtain ⟨hy1 | hy1, hy2⟩ := hy
        · rw [hy1] at hf
          simp only [FitsCape] at hf
          subst hf
          have fl : FitsCape l.1 l.2 l.2 := by rw [hy1]; rfl
          have fr : FitsCape r.1 r.2 r.2 := by rw [← hy2, hy1]; rfl
          exact Or.inr ⟨dh, dt, l.2, r.2, rfl, rfl, normCD_rev hl fl, normCD_rev hr fr⟩
        · exact absurd ⟨hy1, hy2 ▸ hy1⟩ hnn
      · simp only [FitsCape] at hf
        rcases hf with hno | ⟨_, _, xh, xt, hd, rfl, fh, ft⟩
        · simp only [Bool.and_eq_true] at hno
          have e1 : h.isNo = true := isNo_of_all (d := dh) fun z => normCD_rev hl (FitsCape_isNo hno.1 _ _)
          have e2 : t.isNo = true := isNo_of_all (d := dt) fun z => normCD_rev hr (FitsCape_isNo hno.2 _ _)
          exact Or.inl (by simp [e1, e2])
        · cases hd
          exact Or.inr ⟨dh, dt, xh, xt, rfl, rfl, normCD_rev hl fh, normCD_rev hr ft⟩

theorem normSockH_rev {s s' : Sock} (h : normSockH s = some s') : Sub s' s := by
  intro x hx
  cases s with
  | void => simp only [normSockH, Option.some.injEq] at h; subst h; exact hx
  | mk c d =>
    simp only [normSockH, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    exact normCD_rev hp hx

/-! ## The bake -/

/-- A bake is under the code requirement, or is the code requirement, and has
a noun when it is not: the invariant that keeps a bake from promising what its
code does not keep. -/
def BakeOK (lessc s : Sock) : Prop := s = lessc ∨ (Sub s lessc ∧ ∃ y, Fits s y)

theorem BakeOK.sub {lessc s : Sock} (h : BakeOK lessc s) : Sub s lessc := by
  rcases h with rfl | ⟨h, _⟩
  · exact Sub.refl _
  · exact h

/-- **A bake made from sites one of which shares a noun with `less.c`** is
under `less.c` and has a noun; a fixed bake, or one no site informs, is
`less.c`. -/
theorem bakeOf_ok {fixed : Bool} {lessc s : Sock} {ks : List Sock} (h : bakeOf fixed lessc ks = some s)
    (hmeet : fixed = false → ks ≠ [] → ∃ k ∈ ks, ∃ y, Fits lessc y ∧ Fits k y) : BakeOK lessc s := by
  unfold bakeOf at h
  split at h
  · cases h; exact Or.inl rfl
  · rename_i hf
    split at h
    · cases h; exact Or.inl rfl
    · rename_i k0 ks0
      obtain ⟨k, hk, y, hy, hky⟩ := hmeet (by simpa using hf) (List.cons_ne_nil _ _)
      have hm : Fits (meet k0 ks0) y := by
        refine meet_fits ks0 k0 y ?_
        rcases List.mem_cons.mp hk with rfl | hk
        · exact Or.inl hky
        · exact Or.inr ⟨k, hk, hky⟩
      refine Or.inr ⟨(normSockH_rev h).trans (uniSock_left _ _ _ (Nat.lt_succ_self _) y hy hm), y, ?_⟩
      exact normSockH_fits (uniSock_fits _ _ _ (Nat.lt_succ_self _) y hy hm) h

theorem hugeMk_self (c : Cape) (d : Noun) : So.hugeMk c d c d = some true := by
  unfold So.hugeMk; simp

/-- **A rebake keeps the invariant**: the `+norm-sock` of the `+purr:so` of
two bakes under `less.c` is under `less.c`. -/
theorem rebakeG_ok {lessc bake s : Sock} {old : Option Sock} {g g' : Nat} (hb : BakeOK lessc bake)
    (ho : ∀ o, old = some o → BakeOK lessc o) (h : rebakeG bake old g = some (s, g')) : BakeOK lessc s := by
  unfold rebakeG at h
  split at h
  · cases h; exact hb
  · rename_i o
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨hv, hh, h⟩ := h
    split at h
    · cases h; exact hb
    · rename_i hnot
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨s', hs', rfl, -⟩ := h
      have hoo := ho o rfl
      -- both are `less.c` only if `+huge:so` says yes
      have hinh : (∃ y, Fits bake y) ∧ ∃ y, Fits o y := by
        rcases hb with rfl | ⟨hbs, yb⟩
        · rcases hoo with rfl | ⟨hos, yo⟩
          · exfalso
            have hself : ∀ z : Sock, So.huge z z = some true := fun z => by
              cases z <;> simp [So.huge, hugeMk_self]
            rw [hself] at hh
            exact hnot (Option.some.inj hh).symm
          · obtain ⟨y, hy⟩ := yo
            exact ⟨⟨y, hos y hy⟩, ⟨y, hy⟩⟩
        · rcases hoo with rfl | ⟨_, yo⟩
          · obtain ⟨y, hy⟩ := yb
            exact ⟨⟨y, hy⟩, ⟨y, hbs y hy⟩⟩
          · exact ⟨yb, yo⟩
      have hp := purr_sub _ bake o lessc (Nat.lt_succ_self _) hb.sub hoo.sub hinh.1 hinh.2
      obtain ⟨y, hy⟩ := hinh.1
      exact Or.inr ⟨(normSockH_rev hs').trans hp, y, normSockH_fits (purr_fits_left _ _ _ hy) hs'⟩

end Bake

end SkaModel
end Formalization
