import lemmas.Ska.PassClosure

/-!
# The closure invariant, part 2: the region lemmas left (track F, Gaps 16)

`Ska/PassClosure.lean` proves that `+knit:so`, `+hed`, `+tel`, `+pull:so`
and `+darn:so` keep good `&` regions (`SockG`).  Here the rest of the sock
operations of the analysis do too, each proof the mirror of its tidy proof:

* `sockG_doubleInt` (`+double-int`, of `annoTP_doubleInt'`),
* `sockG_msgAnno`, `sockG_mergeProd` (`+msg-anno` and the merge of `+run`),
* `sockG_patchProd` (`+patch-prod`, of `annoTP_patchProd`),
* `sockG_msgSock` (`+msg-sock`, of `tidy_msgSock'`),
* `sockG_app` (`+app:ca`, of `tidy_app`),
* `sockG_runDatum` (the product of the datum `+run` writes, of `runDatum_tp`).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

section Regions2

variable {G : Noun → Prop}

/-- Every `&` region of the annotation's sock is in `G`. -/
def AnnoG (G : Noun → Prop) (a : Anno) : Prop := SockG G a.sock

theorem annoG_dunno : AnnoG G Anno.dunno := trivial

theorem annoG_knit {h t : Anno} (hh : AnnoG G h) (ht : AnnoG G t) : AnnoG G (knitAnno h t) :=
  sockG_knit hh ht

theorem sockG_doubleInt' (hG : SubC G) : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    AnnoG G a → AnnoG G b → AnnoG G (doubleInt a b) := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact ha
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact hb
  | mk ca da =>
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact ha
  | mk cb db =>
    apply doubleInt_cases (AnnoG G) hab annoG_dunno
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    exact sockG_knit (ih _ _ h1 (sockG_hed hG ha) (sockG_hed hG hb))
      (ih _ _ h2 (sockG_tel hG ha) (sockG_tel hG hb))

/-- **`+double-int` keeps good regions.** -/
theorem sockG_doubleInt (hG : SubC G) {a b : Anno} (ha : AnnoG G a) (hb : AnnoG G b) :
    AnnoG G (doubleInt a b) :=
  sockG_doubleInt' hG _ a b (Nat.lt_succ_self _) ha hb

/-- **`+msg-anno` keeps good regions.** -/
theorem sockG_msgAnno (hG : SubC G) (a b : Anno) (ha : AnnoG G a) (hb : AnnoG G b) :
    AnnoG G (msgAnno a b) := by
  fun_induction msgAnno a b with
  | case1 => exact ha
  | case2 => exact hb
  | case3 => exact ha
  | case4 _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact sockG_knit (ih1 (sockG_hed hG ha) (sockG_hed hG hb)) (ih2 (sockG_tel hG ha) (sockG_tel hG hb))
  | case5 => exact annoG_dunno

/-- **The merge of `+run` keeps good regions.** -/
theorem sockG_mergeProd (hG : SubC G) (moved : Bool) {a b : Anno} (ha : AnnoG G a) (hb : AnnoG G b) :
    AnnoG G (mergeProd moved a b) := by
  unfold mergeProd
  split
  · exact sockG_msgAnno hG a b ha hb
  · exact sockG_doubleInt hG ha hb

/-- **`+patch-prod` keeps good regions**, for a subject sock with good
regions: each part is a part of the product or a `+pull:so` of `new`. -/
theorem sockG_patchProd (hG : SubC G) {new : Sock} (hn : SockG G new) :
    ∀ (σ : Noun) (S : Sock), SockG G S → AnnoG G (patchProd S σ new) := by
  intro σ
  induction σ with
  | atom a =>
    intro S hS
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; exact hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd_void']; exact hS
    rw [patchProd_atom new ha hv]
    show SockG G ((So.pull new a).getD Sock.void)
    cases hp : So.pull new a with
    | none => trivial
    | some s' => exact sockG_pull hG hn hp
  | cell h t ih1 ih2 =>
    intro S hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd_void']; exact hS
    rw [patchProd_cell new hv]
    exact annoG_knit (ih1 _ (sockG_hed hG hS)) (ih2 _ (sockG_tel hG hS))

theorem sockG_msgSock' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → SockG G a → SockG G b →
    msgSock a b = some m → SockG G m := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hb hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact ha
  · split at hm
    · cases hm; exact hb
    · cases hm; exact ha
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      exact sockG_knit (ih (Sock.mk ah ad1) (Sock.mk bh bd1) _ (by simp only [Sock.data]; omega) ha.1 hb.1 hh)
        (ih (Sock.mk aT ad2) (Sock.mk bT bd2) _ (by simp only [Sock.data]; omega) ha.2 hb.2 ht)
    · cases hm
    · cases hm; trivial

/-- **`+msg-sock` (the `%he` generalization) keeps good regions.** -/
theorem sockG_msgSock {a b m : Sock} (ha : SockG G a) (hb : SockG G b) (hm : msgSock a b = some m) :
    SockG G m :=
  sockG_msgSock' _ a b m (Nat.lt_succ_self _) ha hb hm

/-- **`+app:ca` keeps good regions.** -/
theorem sockG_app (hG : SubC G) : ∀ (c : Cape) {s : Sock}, SockG G s → SockG G (Ca.app c s) := by
  intro c
  induction c with
  | yes =>
    intro s hs
    rcases s with _ | ⟨cs, d⟩
    · trivial
    · unfold Ca.app; simp only
      split
      · exact hs
      · split
        · trivial
        · exact hs
  | no =>
    intro s hs
    rcases s with _ | ⟨cs, d⟩
    · trivial
    · unfold Ca.app; simp only
      split
      · exact hs
      · split
        · trivial
        · rename_i h; exact absurd (Or.inl trivial) h
  | cell x y ihx ihy =>
    intro s hs
    rcases s with _ | ⟨cs, d⟩
    · trivial
    · rw [Ca.app.eq_def]; simp only
      split
      · exact hs
      · split
        · trivial
        · exact sockG_knit (ihx (sockG_hed hG hs)) (ihy (sockG_tel hG hs))

/-- **The product of the datum `+run` writes has good regions**, from a good
product of `fol-loop` and a good old product. -/
theorem sockG_runDatum (hG : SubC G) {moved : Bool} {bus : Sock} {out : FolOut} {gen' : Gen} {old : Datum}
    (ho : AnnoG G out.prod) (hd : SockG G old.prod) :
    SockG G (runDatum moved bus out gen' old).1.prod :=
  sockG_mergeProd hG moved (b := ⟨old.prod, old.map⟩) ho hd

/-- `less-code` of that datum too, from a good `bus`. -/
theorem sockG_runDatum_less (hG : SubC G) {moved : Bool} {bus : Sock} {out : FolOut} {gen' : Gen} {old : Datum}
    (hb : SockG G bus) : SockG G (runDatum moved bus out gen' old).1.less :=
  sockG_app hG _ hb

end Regions2

end Ana
end SkaModel
end Formalization
