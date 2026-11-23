import lemmas.Ska.Sock

/-!
# What the operations on socks mean

A sock is a set of nouns: `Fits s n` (in `Contract.lean`).  The analysis
reads a sock as what it knows of a noun, and every operation must keep that
reading true: if the noun fits the sock before, the result of the Nock
operation fits the result of the sock operation.

* `knit_fits`, `hed_fits`, `tel_fits`: a cons and its parts.
* `pull_fits`: `+pull:so` and Nock 0.
* `darn_fits`: `+darn:so` and Nock 10.
* `purr_fits_left`, `purr_fits_right`: `+purr:so` knows no more than either
  sock, the join of two branches.
* `huge_sound`: if `+huge:so` says that `two` nests under `one`, every noun of
  `two` is a noun of `one`.
* `app_fits`: `+app:ca` only forgets.
* `all_fits`: a cape that knows all determines the noun.
* `jibe_of_fits`: two socks that a noun fits agree where both know (for capes
  without empty cells).

The cases where a cape is a cell that knows nothing, like `[| |]`, which
`+con:ca` normalizes away but other arms can make, need care throughout:
such a cape says nothing, not even that the noun is a cell.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Axes, top down -/

theorem cap_cases : ∀ a, 2 ≤ a → cap a = 2 ∨ cap a = 3
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by simp [cap]
  | 3, _ => by simp [cap]
  | a + 4, _ => by
    rw [cap]
    exact cap_cases ((a + 4) / 2) (by omega)
decreasing_by omega

/-- The first step of an axis is `+cap`, the rest is `+mas`. -/
theorem axisPath_cap : ∀ a, 2 ≤ a →
    axisPath a = (axisPath (mas a)).map (decide (cap a = 3) :: ·)
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by rw [show cap 2 = 2 by simp [cap], show mas 2 = 1 by simp [mas]]; rfl
  | 3, _ => by rw [show cap 3 = 3 by simp [cap], show mas 3 = 1 by simp [mas]]; rfl
  | a + 4, _ => by
    have ih := axisPath_cap ((a + 4) / 2) (by omega)
    have hm := mas_pos ((a + 4) / 2) (by omega)
    rw [axisPath_step (a + 4) (by omega), ih, cap, mas,
      axisPath_step ((a + 4) % 2 + mas ((a + 4) / 2) * 2) (by omega)]
    have h1 : ((a + 4) % 2 + mas ((a + 4) / 2) * 2) / 2 = mas ((a + 4) / 2) := by omega
    have h2 : ((a + 4) % 2 + mas ((a + 4) / 2) * 2) % 2 = (a + 4) % 2 := by omega
    rw [h1, h2]
    cases axisPath (mas ((a + 4) / 2)) <;> simp
decreasing_by omega

theorem slot?_cap {a : Nat} (ha : 2 ≤ a) (n : Noun) :
    slot? a n = match n with
      | Noun.cell h t => slot? (mas a) (if cap a = 2 then h else t)
      | Noun.atom _ => none := by
  unfold slot?
  rw [axisPath_cap a ha]
  rcases cap_cases a ha with hc | hc <;>
    cases axisPath (mas a) <;> cases n <;> simp [hc, slotAtPath]

theorem edit?_cap {a : Nat} (ha : 2 ≤ a) (v n : Noun) :
    edit? a v n = match n with
      | Noun.cell h t =>
        if cap a = 2 then (edit? (mas a) v h).map (C · t) else (edit? (mas a) v t).map (C h ·)
      | Noun.atom _ => none := by
  unfold edit?
  rw [axisPath_cap a ha]
  rcases cap_cases a ha with hc | hc <;>
    cases axisPath (mas a) <;> cases n <;> simp [hc, editAtPath] <;> split <;> simp_all

/-! ## Capes that know nothing -/

theorem FitsCape_isNo : ∀ {c : Cape}, c.isNo = true → ∀ d n, FitsCape c d n
  | Cape.yes, h, _, _ => by simp [Cape.isNo] at h
  | Cape.no, _, _, _ => trivial
  | Cape.cell _ _, h, _, _ => Or.inl h

theorem fits_dunno (n : Noun) : Fits Sock.dunno n := trivial

/-- A sock whose cape knows nothing (`Sock.isNo` is the narrower test of a
cape that is `|` itself). -/
def Sock.Blank (s : Sock) : Prop := ∃ c d, s = Sock.mk c d ∧ c.isNo = true

theorem Sock.Blank.fits {s : Sock} (h : s.Blank) (n : Noun) : Fits s n := by
  obtain ⟨c, d, rfl, hc⟩ := h
  exact FitsCape_isNo hc d n

theorem dunno_blank : Sock.dunno.Blank := ⟨Cape.no, A 0, rfl, rfl⟩

theorem con_isNo {l r : Cape} (hl : l.isNo = true) (hr : r.isNo = true) :
    (Ca.con l r).isNo = true := by
  unfold Ca.con; split <;> simp [Cape.isNo, hl, hr]

theorem con_ne_no {l r : Cape} (h : Ca.con l r ≠ Cape.no) : Ca.con l r = Cape.cell l r := by
  unfold Ca.con at *; split <;> simp_all

theorem knit_blank {one two : Sock} (h1 : one.Blank) (h2 : two.Blank) : (So.knit one two).Blank := by
  obtain ⟨l, d1, rfl, hl⟩ := h1
  obtain ⟨r, d2, rfl, hr⟩ := h2
  simp only [So.knit]
  split
  · exact dunno_blank
  · exact ⟨_, _, rfl, con_isNo hl hr⟩

theorem hed_blank {s : Sock} (h : s.Blank) : (So.hed s).Blank := by
  obtain ⟨c, d, rfl, hc⟩ := h
  cases c with
  | yes => simp [Cape.isNo] at hc
  | no => exact dunno_blank
  | cell ch ct =>
    simp only [Cape.isNo, Bool.and_eq_true] at hc
    cases d with
    | atom _ => exact dunno_blank
    | cell _ _ => exact ⟨ch, _, rfl, hc.1⟩

theorem tel_blank {s : Sock} (h : s.Blank) : (So.tel s).Blank := by
  obtain ⟨c, d, rfl, hc⟩ := h
  cases c with
  | yes => simp [Cape.isNo] at hc
  | no => exact dunno_blank
  | cell ch ct =>
    simp only [Cape.isNo, Bool.and_eq_true] at hc
    cases d with
    | atom _ => exact dunno_blank
    | cell _ _ => exact ⟨ct, _, rfl, hc.2⟩

/-- A non-void sock that an atom fits, and whose cape is not `|`: its head
and its tail know nothing. -/
theorem hed_tel_blank_of_atom {c : Cape} {d : Noun} {k : Nat} (hf : FitsCape c d (A k)) :
    (So.hed (Sock.mk c d)).Blank ∧ (So.tel (Sock.mk c d)).Blank := by
  cases c with
  | no => exact ⟨dunno_blank, dunno_blank⟩
  | yes =>
    simp only [FitsCape] at hf
    subst hf
    exact ⟨dunno_blank, dunno_blank⟩
  | cell ch ct =>
    simp only [FitsCape] at hf
    rcases hf with hno | ⟨_, _, _, _, _, hn, _⟩
    · exact ⟨hed_blank ⟨_, _, rfl, hno⟩, tel_blank ⟨_, _, rfl, hno⟩⟩
    · cases hn

/-! ## Cons, head, tail -/

theorem knit_fits {one two : Sock} {a b : Noun} (h1 : Fits one a) (h2 : Fits two b) :
    Fits (So.knit one two) (C a b) := by
  cases one with
  | void => exact absurd h1 id
  | mk l d1 =>
    cases two with
    | void => exact absurd h2 id
    | mk r d2 =>
      simp only [So.knit]
      split
      · exact fits_dunno _
      · rename_i hne
        simp only [Fits]
        rw [con_ne_no hne]
        exact Or.inr ⟨d1, d2, a, b, rfl, rfl, h1, h2⟩

theorem hed_fits {s : Sock} {a b : Noun} (h : Fits s (C a b)) : Fits (So.hed s) a := by
  cases s with
  | void => exact absurd h id
  | mk c d =>
    cases c with
    | no => exact fits_dunno _
    | yes =>
      simp only [Fits, FitsCape] at h
      subst h
      exact rfl
    | cell ch ct =>
      simp only [Fits, FitsCape] at h
      rcases h with hno | ⟨dh, dt, nh, nt, rfl, hn, hh, _⟩
      · simp only [Bool.and_eq_true] at hno
        cases d with
        | atom _ => exact fits_dunno _
        | cell dh _ => exact FitsCape_isNo hno.1 _ _
      · cases hn; exact hh

theorem tel_fits {s : Sock} {a b : Noun} (h : Fits s (C a b)) : Fits (So.tel s) b := by
  cases s with
  | void => exact absurd h id
  | mk c d =>
    cases c with
    | no => exact fits_dunno _
    | yes =>
      simp only [Fits, FitsCape] at h
      subst h
      exact rfl
    | cell ch ct =>
      simp only [Fits, FitsCape] at h
      rcases h with hno | ⟨dh, dt, nh, nt, rfl, hn, _, ht⟩
      · simp only [Bool.and_eq_true] at hno
        cases d with
        | atom _ => exact fits_dunno _
        | cell _ dt => exact FitsCape_isNo hno.2 _ _
      · cases hn; exact ht

/-! ## `+pull:so` -/

theorem pullLoop_fits : ∀ (axe : Nat) (c : Cape) (d n m : Noun), 1 ≤ axe →
    FitsCape c d n → slot? axe n = some m → Fits (So.pullLoop c d axe) m := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d n m h1 hf hs
  rw [So.pullLoop.eq_def]
  split
  · have : axe = 1 := by omega
    subst this
    simp only [slot?_one, Option.some.injEq] at hs
    subst hs
    exact hf
  · rename_i hax
    have h2 : 2 ≤ axe := by omega
    have hlt := mas_lt axe h2
    have hpos := mas_pos axe h2
    split
    · exact fits_dunno _
    · rename_i hcno
      rw [slot?_cap h2] at hs
      cases n with
      | atom _ => simp at hs
      | cell nh nt =>
        simp only at hs
        cases d with
        | atom _ =>
          cases c with
          | yes => simp [FitsCape] at hf
          | no => exact absurd rfl hcno
          | cell ch ct =>
            simp only [FitsCape] at hf
            rcases hf with hno | ⟨_, _, _, _, hd, _⟩
            · exact fits_dunno _
            · cases hd
        | cell dh dt =>
          simp only
          cases c with
          | no => exact absurd rfl hcno
          | yes =>
            simp only [FitsCape, Noun.cell.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            by_cases hc : cap axe = 2
            · simp only [hc, if_true] at hs ⊢
              exact ih _ hlt Cape.yes _ _ _ hpos rfl hs
            · simp only [hc, if_false] at hs ⊢
              exact ih _ hlt Cape.yes _ _ _ hpos rfl hs
          | cell ch ct =>
            simp only [FitsCape] at hf
            rcases hf with hno | ⟨dh', dt', nh', nt', hd, hn, hh, ht⟩
            · simp only [Bool.and_eq_true] at hno
              by_cases hc : cap axe = 2
              · simp only [hc, if_true] at hs ⊢
                exact ih _ hlt _ _ _ _ hpos (FitsCape_isNo hno.1 _ _) hs
              · simp only [hc, if_false] at hs ⊢
                exact ih _ hlt _ _ _ _ hpos (FitsCape_isNo hno.2 _ _) hs
            · cases hd; cases hn
              by_cases hc : cap axe = 2
              · simp only [hc, if_true] at hs ⊢
                exact ih _ hlt _ _ _ _ hpos hh hs
              · simp only [hc, if_false] at hs ⊢
                exact ih _ hlt _ _ _ _ hpos ht hs

/-- **`+pull:so` and Nock 0.**  If a noun fits a sock, its part at an axis
fits the sock's part there. -/
theorem pull_fits {s s' : Sock} {axe : Nat} {n m : Noun} (hf : Fits s n)
    (hs : slot? axe n = some m) (hp : So.pull s axe = some s') : Fits s' m := by
  unfold So.pull at hp
  split at hp
  · simp at hp
  · rename_i hax
    cases s with
    | void => exact absurd hf id
    | mk c d =>
      simp only [Option.some.injEq] at hp
      subst hp
      exact pullLoop_fits axe c d n m (by omega) hf hs

/-! ## `+purr:so` -/

theorem purrData_fits_left (d1 d2 : Noun) : Fits (So.purrData d1 d2) d1 := by
  fun_induction So.purrData d1 d2 with
  | case1 => exact rfl
  | case2 a b c d _ ih1 ih2 => exact knit_fits ih1 ih2
  | case3 => exact fits_dunno _

theorem purrData_fits_right (d1 d2 : Noun) : Fits (So.purrData d1 d2) d2 := by
  fun_induction So.purrData d1 d2 with
  | case1 => exact rfl
  | case2 a b c d _ ih1 ih2 => exact knit_fits ih1 ih2
  | case3 => exact fits_dunno _

theorem Sock.Blank.not_void : ¬ Sock.void.Blank := fun ⟨_, _, h, _⟩ => Sock.noConfusion h

theorem purr_blank_left (one two : Sock) (h : one.Blank) : (So.purr one two).Blank := by
  fun_induction So.purr one two with
  | case1 => exact h
  | case2 => exact absurd h Sock.Blank.not_void
  | case3 => exact h
  | case4 => exact dunno_blank
  | case5 =>
    obtain ⟨c, d, hs, hc⟩ := h
    cases hs; simp [Cape.isNo] at hc
  | case6 _ _ _ _ _ _ _ ih2 ih1 => exact knit_blank (ih2 (hed_blank h)) (ih1 (tel_blank h))
  | case7 _ _ c1 _ _ hcell hno _ _ _ =>
    obtain ⟨c, d, hs, hc⟩ := h
    cases hs
    cases c1 with
    | yes => simp [Cape.isNo] at hc
    | no => exact absurd (Or.inl rfl) hno
    | cell ch ct => exact absurd rfl (hcell ch ct)
  | case8 => exact dunno_blank

theorem purr_blank_right (one two : Sock) (h : two.Blank) : (So.purr one two).Blank := by
  fun_induction So.purr one two with
  | case1 => exact h
  | case2 => exact h
  | case3 => exact absurd h Sock.Blank.not_void
  | case4 => exact dunno_blank
  | case5 =>
    obtain ⟨c, d, hs, hc⟩ := h
    cases hs; simp [Cape.isNo] at hc
  | case6 _ _ _ _ _ _ _ ih2 ih1 => exact knit_blank (ih2 (hed_blank h)) (ih1 (tel_blank h))
  | case7 _ _ _ _ _ _ _ _ ih2 ih1 => exact knit_blank (ih2 (hed_blank h)) (ih1 (tel_blank h))
  | case8 => exact dunno_blank

/-- The knit of the meets of the heads and of the tails of two socks keeps a
noun of the first. -/
theorem purr_knit_fits {one two : Sock} {c : Cape} {d n : Noun} (hone : one = Sock.mk c d)
    (hf : Fits one n)
    (ih2 : ∀ n, Fits (So.hed one) n → Fits (So.purr (So.hed one) (So.hed two)) n)
    (ih1 : ∀ n, Fits (So.tel one) n → Fits (So.purr (So.tel one) (So.tel two)) n) :
    Fits (So.knit (So.purr (So.hed one) (So.hed two)) (So.purr (So.tel one) (So.tel two))) n := by
  cases n with
  | cell a b => exact knit_fits (ih2 a (hed_fits hf)) (ih1 b (tel_fits hf))
  | atom k =>
    subst hone
    obtain ⟨hh, ht⟩ := hed_tel_blank_of_atom (k := k) hf
    exact (knit_blank (purr_blank_left _ _ hh) (purr_blank_left _ _ ht)).fits _

theorem purr_knit_fits_right {one two : Sock} {c : Cape} {d n : Noun} (htwo : two = Sock.mk c d)
    (hf : Fits two n)
    (ih2 : ∀ n, Fits (So.hed two) n → Fits (So.purr (So.hed one) (So.hed two)) n)
    (ih1 : ∀ n, Fits (So.tel two) n → Fits (So.purr (So.tel one) (So.tel two)) n) :
    Fits (So.knit (So.purr (So.hed one) (So.hed two)) (So.purr (So.tel one) (So.tel two))) n := by
  cases n with
  | cell a b => exact knit_fits (ih2 a (hed_fits hf)) (ih1 b (tel_fits hf))
  | atom k =>
    subst htwo
    obtain ⟨hh, ht⟩ := hed_tel_blank_of_atom (k := k) hf
    exact (knit_blank (purr_blank_right _ _ hh) (purr_blank_right _ _ ht)).fits _

/-- **`+purr:so` knows no more than its first sock.** -/
theorem purr_fits_left (one two : Sock) : ∀ n, Fits one n → Fits (So.purr one two) n := by
  fun_induction So.purr one two with
  | case1 => exact fun _ h => h
  | case2 => exact fun _ h => absurd h id
  | case3 => exact fun _ h => h
  | case4 => exact fun n _ => fits_dunno n
  | case5 d1 d2 =>
    intro n h
    simp only [Fits, FitsCape] at h
    subst h
    exact purrData_fits_left _ _
  | case6 _ _ _ _ _ _ _ ih2 ih1 => exact fun n h => purr_knit_fits rfl h ih2 ih1
  | case7 _ _ _ _ _ _ _ _ ih2 ih1 => exact fun n h => purr_knit_fits rfl h ih2 ih1
  | case8 => exact fun n _ => fits_dunno n

/-- **`+purr:so` knows no more than its second sock.** -/
theorem purr_fits_right (one two : Sock) : ∀ n, Fits two n → Fits (So.purr one two) n := by
  fun_induction So.purr one two with
  | case1 => exact fun _ h => h
  | case2 => exact fun _ h => h
  | case3 => exact fun _ h => absurd h id
  | case4 => exact fun n _ => fits_dunno n
  | case5 d1 d2 =>
    intro n h
    simp only [Fits, FitsCape] at h
    subst h
    exact purrData_fits_right _ _
  | case6 _ _ _ _ _ _ _ ih2 ih1 => exact fun n h => purr_knit_fits_right rfl h ih2 ih1
  | case7 _ _ _ _ _ _ _ _ ih2 ih1 => exact fun n h => purr_knit_fits_right rfl h ih2 ih1
  | case8 => exact fun n _ => fits_dunno n

/-! ## `+darn:so` -/

/-- A noun put back in its context: the siblings on the way up, innermost
first, each with the side of the edited part (`2` the head). -/
def plug (v : Noun) : List (Nat × Noun) → Noun
  | [] => v
  | (k, x) :: ctx => if k = 2 then plug (C v x) ctx else plug (C x v) ctx

theorem darnUp_eq (two : Sock) (k : Nat) (s : Sock) (acc : List (Nat × Sock)) :
    So.darnUp two ((k, s) :: acc) =
      if k = 2 then So.darnUp (So.knit two s) acc else So.darnUp (So.knit s two) acc := by
  by_cases hk : k = 2
  · subst hk; simp [So.darnUp]
  · rw [if_neg hk]
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | n + 3, _ => rfl

/-- The siblings of the sock stand for the siblings of the noun. -/
def CtxFits (acc : List (Nat × Sock)) (ctx : List (Nat × Noun)) : Prop :=
  Forall2 (fun (p : Nat × Sock) (q : Nat × Noun) => p.1 = q.1 ∧ Fits p.2 q.2) acc ctx

theorem darnUp_fits : ∀ {acc : List (Nat × Sock)} {ctx : List (Nat × Noun)} {two : Sock}
    {v : Noun}, CtxFits acc ctx → Fits two v → Fits (So.darnUp two acc) (plug v ctx)
  | [], [], _, _, _, h => h
  | (k, s) :: acc, (k', x) :: ctx, two, v, Forall2.cons ⟨hk, hs⟩ hrest, h => by
    simp only at hk hs
    subst hk
    rw [darnUp_eq]
    simp only [plug]
    split
    · exact darnUp_fits hrest (knit_fits h hs)
    · exact darnUp_fits hrest (knit_fits hs h)

theorem darnDown_fits : ∀ (axe : Nat) (one two : Sock) (acc : List (Nat × Sock))
    (ctx : List (Nat × Noun)) (n v n'' : Noun) (s : Sock),
    Fits one n → Fits two v → edit? axe v n = some n'' → CtxFits acc ctx →
    So.darnDown one axe two acc = some s → Fits s (plug n'' ctx) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro one two acc ctx n v n'' s h1 h2 he hc hd
  rw [So.darnDown.eq_def] at hd
  split at hd
  · rename_i hstop
    simp only [Option.some.injEq] at hd
    subst hd
    rcases hstop with rfl | ⟨_, hno⟩
    · simp only [edit?_one, Option.some.injEq] at he
      subst he
      exact darnUp_fits hc h2
    · cases two with
      | void => exact absurd h2 id
      | mk c d =>
        cases c <;> simp [Sock.isNo] at hno
        exact darnUp_fits hc trivial
  · rename_i hstop
    split at hd
    · simp at hd
    · rename_i h0
      have h2' : 2 ≤ axe := by omega
      have hlt := mas_lt axe h2'
      rw [edit?_cap h2'] at he
      cases n with
      | atom _ => simp at he
      | cell h t =>
        simp only at he
        split at hd
        · rename_i hcap
          rw [if_pos hcap] at he
          obtain ⟨h', he', rfl⟩ := Option.map_eq_some_iff.mp he
          have := ih _ hlt _ _ _ ((2, t) :: ctx) h v h' s (hed_fits h1) h2 he'
            (Forall2.cons ⟨rfl, tel_fits h1⟩ hc) hd
          simpa [plug] using this
        · rename_i hcap
          rw [if_neg hcap] at he
          obtain ⟨t', he', rfl⟩ := Option.map_eq_some_iff.mp he
          have := ih _ hlt _ _ _ ((3, h) :: ctx) t v t' s (tel_fits h1) h2 he'
            (Forall2.cons ⟨rfl, hed_fits h1⟩ hc) hd
          simpa [plug] using this

/-- **`+darn:so` and Nock 10.**  If a noun fits `one` and the replacement
fits `two`, the edited noun fits the edited sock. -/
theorem darn_fits {one two s : Sock} {axe : Nat} {n v n' : Noun} (h1 : Fits one n)
    (h2 : Fits two v) (he : edit? axe v n = some n') (hd : So.darn one axe two = some s) :
    Fits s n' := by
  unfold So.darn at hd
  split at hd
  · rename_i hax
    subst hax
    simp only [edit?_one, Option.some.injEq] at he hd
    subst he; subst hd
    exact h2
  · split at hd
    · rename_i hv
      rcases hv with rfl | rfl
      · exact absurd h1 id
      · exact absurd h2 id
    · split at hd
      · simp only [Option.some.injEq] at hd
        subst hd
        exact fits_dunno _
      · exact darnDown_fits axe one two [] [] n v n' s h1 h2 he Forall2.nil hd

/-! ## Splitting a cape -/

theorem isNo_hed {c : Cape} (h : c.isNo = true) : (Ca.hed c).isNo = true := by
  cases c <;> simp_all [Cape.isNo, Ca.hed]

theorem isNo_tel {c : Cape} (h : c.isNo = true) : (Ca.tel c).isNo = true := by
  cases c <;> simp_all [Cape.isNo, Ca.tel]

/-- A cape that knows something, on a cell of data: the noun is a cell, and
its halves fit the halves. -/
theorem FitsCape_split {c : Cape} {dh dt n : Noun} (hc : c.isNo = false)
    (h : FitsCape c (C dh dt) n) :
    ∃ nh nt, n = C nh nt ∧ FitsCape (Ca.hed c) dh nh ∧ FitsCape (Ca.tel c) dt nt := by
  cases c with
  | yes =>
    simp only [FitsCape] at h
    subst h
    exact ⟨dh, dt, rfl, rfl, rfl⟩
  | no => simp [Cape.isNo] at hc
  | cell ch ct =>
    simp only [FitsCape] at h
    rcases h with hno | ⟨dh', dt', nh, nt, hd, rfl, hh, ht⟩
    · simp_all [Cape.isNo]
    · cases hd; exact ⟨nh, nt, rfl, hh, ht⟩

theorem FitsCape_join {c : Cape} {dh dt nh nt : Noun} (hh : FitsCape (Ca.hed c) dh nh)
    (ht : FitsCape (Ca.tel c) dt nt) : FitsCape c (C dh dt) (C nh nt) := by
  cases c with
  | yes =>
    simp only [Ca.hed, Ca.tel, FitsCape] at hh ht ⊢
    rw [hh, ht]
  | no => trivial
  | cell ch ct => exact Or.inr ⟨dh, dt, nh, nt, rfl, rfl, hh, ht⟩

/-! ## `+huge:so` -/

theorem hugeMk_blank : ∀ (d1 : Noun) (c1 c2 : Cape) (d2 : Noun),
    So.hugeMk c1 d1 c2 d2 = some true → c2.isNo = true → c1.isNo = true
  | Noun.atom k, c1, c2, d2, h, h2 => by
    rw [So.hugeMk.eq_def] at h
    split at h
    · rename_i he; rw [he.1]; exact h2
    · cases c1 with
      | cell _ _ => simp at h
      | no => rfl
      | yes =>
        simp only [Option.some.injEq, decide_eq_true_eq] at h
        rw [h.1] at h2; simp [Cape.isNo] at h2
  | Noun.cell d1h d1t, c1, c2, d2, h, h2 => by
    rw [So.hugeMk.eq_def] at h
    split at h
    · rename_i he; rw [he.1]; exact h2
    · cases d2 with
      | atom _ =>
        simp only at h
        cases c2 with
        | cell _ _ => simp at h
        | yes => split at h <;> simp at h
        | no => split at h <;> simp at h
      | cell d2h d2t =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨l, hl, h⟩ := h
        cases l with
        | false => simp at h
        | true =>
          simp only [if_true] at h
          have ih1 := hugeMk_blank d1h _ _ _ hl (isNo_hed h2)
          have ih2 := hugeMk_blank d1t _ _ _ h (isNo_tel h2)
          cases c1 with
          | yes => simp [Ca.hed, Cape.isNo] at ih1
          | no => rfl
          | cell ch ct => simp_all [Ca.hed, Ca.tel, Cape.isNo]

theorem hugeMk_sound : ∀ (d1 : Noun) (c1 c2 : Cape) (d2 n : Noun),
    So.hugeMk c1 d1 c2 d2 = some true → FitsCape c2 d2 n → FitsCape c1 d1 n
  | Noun.atom k, c1, c2, d2, n, h, hf => by
    rw [So.hugeMk.eq_def] at h
    split at h
    · rename_i he; rw [he.1, he.2]; exact hf
    · cases c1 with
      | cell _ _ => simp at h
      | no => trivial
      | yes =>
        simp only [Option.some.injEq, decide_eq_true_eq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hf
  | Noun.cell d1h d1t, c1, c2, d2, n, h, hf => by
    have hb := hugeMk_blank _ _ _ _ h
    rw [So.hugeMk.eq_def] at h
    split at h
    · rename_i he; rw [he.1, he.2]; exact hf
    · cases d2 with
      | atom _ =>
        simp only at h
        cases c2 with
        | cell _ _ => simp at h
        | yes => split at h <;> simp at h
        | no => split at h <;> simp at h
      | cell d2h d2t =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨l, hl, h⟩ := h
        cases l with
        | false => simp at h
        | true =>
          simp only [if_true] at h
          cases hc1 : c1.isNo with
          | true => exact FitsCape_isNo hc1 _ _
          | false =>
            cases hc2 : c2.isNo with
            | true => rw [hb hc2] at hc1; cases hc1
            | false =>
              obtain ⟨nh, nt, rfl, hh, ht⟩ := FitsCape_split hc2 hf
              exact FitsCape_join (hugeMk_sound d1h _ _ _ _ hl hh)
                (hugeMk_sound d1t _ _ _ _ h ht)

/-- **`+huge:so` is sound.**  If it says that `two` nests under `one`, every
noun of `two` is a noun of `one`. -/
theorem huge_sound {one two : Sock} (h : So.huge one two = some true) {n : Noun}
    (hf : Fits two n) : Fits one n := by
  cases one with
  | void =>
    cases two with
    | void => exact absurd hf id
    | mk _ _ => simp [So.huge] at h
  | mk c1 d1 =>
    cases two with
    | void => exact absurd hf id
    | mk c2 d2 => exact hugeMk_sound d1 c1 c2 d2 n h hf

/-! ## `+app:ca` -/

theorem app_blank : ∀ (c : Cape) (s : Sock), s.Blank → (Ca.app c s).Blank := by
  intro c
  induction c with
  | yes =>
    intro s hs
    obtain ⟨cs, ds, rfl, _⟩ := hs
    unfold Ca.app
    split
    · exact ⟨cs, ds, rfl, by assumption⟩
    · split
      · exact dunno_blank
      · exact ⟨cs, ds, rfl, by assumption⟩
  | no =>
    intro s hs
    obtain ⟨cs, ds, rfl, hcs⟩ := hs
    unfold Ca.app
    split
    · exact ⟨cs, ds, rfl, hcs⟩
    · rw [if_pos (Or.inl rfl)]; exact dunno_blank
  | cell ch ct ih1 ih2 =>
    intro s hs
    have hs' := hs
    obtain ⟨cs, ds, rfl, hcs⟩ := hs
    unfold Ca.app
    split
    · exact ⟨cs, ds, rfl, hcs⟩
    · split
      · exact dunno_blank
      · exact knit_blank (ih1 _ (hed_blank hs')) (ih2 _ (tel_blank hs'))

/-- **`+app:ca` only forgets.**  A noun of a sock is a noun of the sock
masked by any cape. -/
theorem app_fits : ∀ (c : Cape) (s : Sock) (n : Noun), Fits s n → Fits (Ca.app c s) n := by
  intro c
  induction c with
  | yes =>
    intro s n hf
    cases s with
    | void => exact absurd hf id
    | mk cs ds =>
      unfold Ca.app
      split
      · exact hf
      · split
        · exact fits_dunno _
        · exact hf
  | no =>
    intro s n hf
    cases s with
    | void => exact absurd hf id
    | mk cs ds =>
      unfold Ca.app
      split
      · exact hf
      · rw [if_pos (Or.inl rfl)]; exact fits_dunno _
  | cell ch ct ih1 ih2 =>
    intro s n hf
    cases s with
    | void => exact absurd hf id
    | mk cs ds =>
      unfold Ca.app
      split
      · exact hf
      · split
        · exact fits_dunno _
        · cases n with
          | cell a b => exact knit_fits (ih1 _ _ (hed_fits hf)) (ih2 _ _ (tel_fits hf))
          | atom k =>
            obtain ⟨hh, ht⟩ := hed_tel_blank_of_atom (k := k) hf
            exact (knit_blank (app_blank _ _ hh) (app_blank _ _ ht)).fits _

/-! ## `+all:ca` -/

theorem all_isNo {c : Cape} (h : Ca.all c = true) : c.isNo = false := by
  induction c with
  | yes => rfl
  | no => simp [Ca.all] at h
  | cell h' t ih1 ih2 =>
    simp only [Ca.all, Bool.and_eq_true] at h
    simp [Cape.isNo, ih1 h.1]

/-- **A cape that knows all determines the noun.** -/
theorem all_fits : ∀ {c : Cape} {d n : Noun}, Ca.all c = true → FitsCape c d n → n = d
  | Cape.yes, _, _, _, h => h
  | Cape.no, _, _, h, _ => by simp [Ca.all] at h
  | Cape.cell ch ct, d, n, h, hf => by
    have hall := h
    simp only [Ca.all, Bool.and_eq_true] at h
    simp only [FitsCape] at hf
    rcases hf with hno | ⟨dh, dt, nh, nt, rfl, rfl, hh, ht⟩
    · have := all_isNo hall; simp_all [Cape.isNo]
    · rw [all_fits h.1 hh, all_fits h.2 ht]

/-! ## `+jibe:so` -/

/-- A cape in normal form: no cell of it knows nothing. -/
def Cape.Normal : Cape → Prop
  | Cape.cell h t => (Cape.cell h t).isNo = false ∧ h.Normal ∧ t.Normal
  | _ => True

theorem Normal_hed {c : Cape} (h : c.Normal) : (Ca.hed c).Normal := by
  cases c with
  | cell ch ct => exact h.2.1
  | _ => trivial

theorem Normal_tel {c : Cape} (h : c.Normal) : (Ca.tel c).Normal := by
  cases c with
  | cell ch ct => exact h.2.2
  | _ => trivial

/-- **Two socks in normal form that a noun fits agree where both know.** -/
theorem jibeMk_of_fits : ∀ (n : Noun) (c1 c2 : Cape) (d1 d2 : Noun), c1.Normal → c2.Normal →
    FitsCape c1 d1 n → FitsCape c2 d2 n → So.jibeMk c1 d1 c2 d2 = true := by
  intro n
  induction n with
  | atom k =>
    intro c1 c2 d1 d2 hn1 hn2 h1 h2
    rw [So.jibeMk.eq_def]
    split; · rfl
    split; · rfl
    split
    · rename_i _ _ hy
      obtain ⟨rfl, rfl⟩ := hy
      simp only [FitsCape] at h1 h2
      subst h1; subst h2; simp
    · rename_i _ hno hy
      exfalso
      cases c1 with
      | no => exact hno (Or.inl rfl)
      | yes =>
        cases c2 with
        | no => exact hno (Or.inr rfl)
        | yes => exact hy ⟨rfl, rfl⟩
        | cell _ _ =>
          simp only [FitsCape] at h2
          rcases h2 with h | ⟨_, _, _, _, _, h, _⟩
          · have := hn2.1; simp_all [Cape.isNo]
          · cases h
      | cell _ _ =>
        simp only [FitsCape] at h1
        rcases h1 with h | ⟨_, _, _, _, _, h, _⟩
        · have := hn1.1; simp_all [Cape.isNo]
        · cases h
  | cell nh nt ih1 ih2 =>
    intro c1 c2 d1 d2 hn1 hn2 h1 h2
    rw [So.jibeMk.eq_def]
    split; · rfl
    split; · rfl
    split
    · rename_i _ _ hy
      obtain ⟨rfl, rfl⟩ := hy
      simp only [FitsCape] at h1 h2
      subst h1; subst h2; simp
    · rename_i _ hno hy
      have hc1 : c1.isNo = false := by
        cases c1 with
        | yes => rfl
        | no => exact absurd (Or.inl rfl) hno
        | cell _ _ => exact hn1.1
      have hc2 : c2.isNo = false := by
        cases c2 with
        | yes => rfl
        | no => exact absurd (Or.inr rfl) hno
        | cell _ _ => exact hn2.1
      have hd : ∀ c d, c.isNo = false → FitsCape c d (C nh nt) → ∃ dh dt, d = C dh dt := by
        intro c d hc h
        cases c with
        | yes => exact ⟨nh, nt, h.symm⟩
        | no => simp [Cape.isNo] at hc
        | cell _ _ =>
          simp only [FitsCape] at h
          rcases h with h | ⟨dh, dt, _, _, hd, _⟩
          · simp_all [Cape.isNo]
          · exact ⟨dh, dt, hd⟩
      obtain ⟨d1h, d1t, rfl⟩ := hd c1 d1 hc1 h1
      obtain ⟨d2h, d2t, rfl⟩ := hd c2 d2 hc2 h2
      obtain ⟨nh1, nt1, he1, hh1, ht1⟩ := FitsCape_split hc1 h1
      obtain ⟨nh2, nt2, he2, hh2, ht2⟩ := FitsCape_split hc2 h2
      cases he1; cases he2
      simp only [Bool.and_eq_true]
      exact ⟨ih1 _ _ _ _ (Normal_hed hn1) (Normal_hed hn2) hh1 hh2,
        ih2 _ _ _ _ (Normal_tel hn1) (Normal_tel hn2) ht1 ht2⟩

end SkaModel
end Formalization
