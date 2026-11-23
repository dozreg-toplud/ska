import lemmas.Ska.SitesMeetNF

/-!
# `KnowMeetsNF`: the run under a bake against the run without folding

`KnowMeetsNF` (`SitesMeetNF.lean`) compares two runs of `+know` on one
nomm: run A under a bake `s` with the poke's fold flag, run B under
`less.cur` without folding.  The two subject socks share a noun (`Meets`),
and this file shows, by induction on the nomm, that the products of the two
runs share a noun and that every site of A has a site of the same callee in
B whose sock shares a noun with it (`knowGo_meets`).

Run B never folds, so it walks every branch that A walks: at a `%6` that A
folds, B walks both branches, and `+double-int` of B's two branches knows no
more than either (`doubleInt_fits_left`, `doubleInt_fits_right`).  Each sock
operation keeps `Meets`: `+knit:so`, `+pull:so`, `+double-int`
(`SitesMeetNF.lean`), and here `+patch-prod` (`meets_patchProd`, when the
callee's product sock has a noun) and `+darn:so` (`meets_darn`, with the
noun edited by `forceEdit`, which turns atoms on the path into cells).  A
literal of A knows exactly its noun (`knowGo_lit`), so where A folds and B
does not, B's sock has that noun.

Run B returns whenever no `%10` of the nomm has axis `0`
(`knowGo_nf_some`): without folding and with `idc`, the only crash of
`+know` is `+darn:so` at axis `0`.  So A returning never needs B to return
at a place A skipped.

What this assumes, each a named hypothesis of `knowMeetsNF_of`:

1. `DatInhab`: every datum's product sock has a noun (`+pop` turns
   `%void` into `|+~`), for `+patch-prod`.
2. `LessInhab`: every code bell with a datum has a code requirement with a
   noun, so that the bake meets it (`meets_of_bakeOK`).
3. `NoAx0Dat`: no `%10` of a datum's nomm has axis `0` (the analysis
   turns those into `[0 0]`, see `Analysis.lean`).
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-! ## A sock with a noun has a head and a tail with nouns -/

/-- The head of a noun, `0` for an atom. -/
def nhed : Noun → Noun
  | Noun.cell h _ => h
  | Noun.atom _ => A 0

/-- The tail of a noun, `0` for an atom. -/
def ntel : Noun → Noun
  | Noun.cell _ t => t
  | Noun.atom _ => A 0

theorem parts_fit {s : Sock} {y : Noun} (h : Fits s y) :
    Fits (So.hed s) (nhed y) ∧ Fits (So.tel s) (ntel y) := by
  cases y with
  | cell a b => exact ⟨hed_fits h, tel_fits h⟩
  | atom k =>
    cases s with
    | void => exact absurd h id
    | mk c d =>
      have := hed_tel_blank_of_atom (k := k) h
      exact ⟨this.1.fits _, this.2.fits _⟩

/-! ## `+patch-prod` keeps `Meets` -/

/-- **`+patch-prod` keeps `Meets`** in the subject sock, when the product
sock has a noun: patch each part from the shared noun of the two subject
socks, and keep the product's noun where there is no provenance. -/
theorem meets_patchProd {k k' : Sock} (hk : Meets k k') :
    ∀ (src : Noun) (s : Sock), (∃ y, Fits s y) →
      Meets (patchProd s src k).sock (patchProd s src k').sock := by
  intro src
  induction src with
  | atom a =>
    intro s ⟨y, hy⟩
    by_cases h0 : a = 0
    · subst h0
      rw [patchProd, if_pos rfl]
      exact ⟨y, hy, hy⟩
    · have hs : s ≠ Sock.void := by rintro rfl; exact hy
      have hne : Noun.atom a ≠ A 0 := fun h => h0 (by cases h; rfl)
      rw [patchProd, if_neg hne, if_neg hs, patchProd, if_neg hne, if_neg hs]
      have hp : ∀ m : Sock, (∃ z, Fits m z) → ∃ r, So.pull m a = some r := by
        intro m ⟨z, hz⟩
        unfold So.pull
        rw [if_neg h0]
        cases m with
        | void => exact absurd hz id
        | mk c d => exact ⟨_, rfl⟩
      obtain ⟨y', h1, h2⟩ := hk
      obtain ⟨r, hr⟩ := hp k ⟨y', h1⟩
      obtain ⟨r', hr'⟩ := hp k' ⟨y', h2⟩
      simp only [hr, hr', Option.getD_some]
      exact meets_pull ⟨y', h1, h2⟩ h0 hr hr'
  | cell h t ih1 ih2 =>
    intro s ⟨y, hy⟩
    have hs : s ≠ Sock.void := by rintro rfl; exact hy
    have hne : Noun.cell h t ≠ A 0 := fun h => by cases h
    rw [patchProd, if_neg hne, if_neg hs, patchProd, if_neg hne, if_neg hs]
    exact meets_knit (ih1 _ ⟨_, (parts_fit hy).1⟩) (ih2 _ ⟨_, (parts_fit hy).2⟩)

/-! ## `+darn:so` keeps `Meets` -/

/-- The noun `n` edited at `axe` with `v`, where an atom on the path is first
taken as the cell `[0 0]`: a noun of the `+darn:so` of every two socks that
`n` and `v` fit, whether or not `n` has a part at `axe`. -/
def forceEdit (axe : Nat) (v n : Noun) : Noun :=
  if axe ≤ 1 then v else
  if cap axe = 2 then C (forceEdit (mas axe) v (nhed n)) (ntel n)
  else C (nhed n) (forceEdit (mas axe) v (ntel n))
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

theorem darnDown_fits_force : ∀ (axe : Nat) (one two : Sock) (acc : List (Nat × Sock))
    (ctx : List (Nat × Noun)) (n v : Noun) (s : Sock),
    Fits one n → Fits two v → CtxFits acc ctx →
    So.darnDown one axe two acc = some s → Fits s (plug (forceEdit axe v n) ctx) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro one two acc ctx n v s h1 h2 hc hd
  rw [So.darnDown.eq_def] at hd
  split at hd
  · rename_i hstop
    simp only [Option.some.injEq] at hd
    subst hd
    rcases hstop with rfl | ⟨_, hno⟩
    · rw [forceEdit, if_pos (Nat.le_refl 1)]
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
      rw [forceEdit, if_neg (by omega)]
      split at hd
      · rename_i hcap
        rw [if_pos hcap]
        have := ih _ hlt _ _ _ ((2, ntel n) :: ctx) (nhed n) v s (parts_fit h1).1 h2
          (Forall2.cons ⟨rfl, (parts_fit h1).2⟩ hc) hd
        simpa [plug] using this
      · rename_i hcap
        rw [if_neg hcap]
        have := ih _ hlt _ _ _ ((3, nhed n) :: ctx) (ntel n) v s (parts_fit h1).2 h2
          (Forall2.cons ⟨rfl, (parts_fit h1).1⟩ hc) hd
        simpa [plug] using this

/-- **`+darn:so` and a forced edit**: if `n` fits `one` and `v` fits `two`,
the forced edit fits the result, even where `n` has no part at `axe`. -/
theorem darn_fits_force {one two s : Sock} {axe : Nat} {n v : Noun} (h1 : Fits one n)
    (h2 : Fits two v) (hd : So.darn one axe two = some s) : Fits s (forceEdit axe v n) := by
  unfold So.darn at hd
  split at hd
  · rename_i hax
    subst hax
    simp only [Option.some.injEq] at hd
    subst hd
    rw [forceEdit, if_pos (Nat.le_refl 1)]
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
      · exact darnDown_fits_force axe one two [] [] n v s h1 h2 Forall2.nil hd

/-- **`+darn:so` keeps `Meets`**: the shared noun of the two records, edited
at the axis with the shared noun of the two replacements, atoms on the path
taken as cells. -/
theorem meets_darn {one one' two two' s s' : Sock} {axe : Nat} (h1 : Meets one one')
    (h2 : Meets two two') (hd : So.darn one axe two = some s) (hd' : So.darn one' axe two' = some s') :
    Meets s s' :=
  let ⟨y, hy, hy'⟩ := h1
  let ⟨v, hv, hv'⟩ := h2
  ⟨forceEdit axe v y, darn_fits_force hy hv hd, darn_fits_force hy' hv' hd'⟩

theorem darnDown_some : ∀ (axe : Nat) (one two : Sock) (acc : List (Nat × Sock)), axe ≠ 0 →
    ∃ s, So.darnDown one axe two acc = some s := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro one two acc h0
  rw [So.darnDown.eq_def]
  split
  · exact ⟨_, rfl⟩
  · rename_i hstop
    have h2' : 2 ≤ axe := by omega
    have hm : mas axe ≠ 0 := by have := mas_pos axe h2'; omega
    split
    · exact ih _ (mas_lt axe h2') _ _ _ hm
    · exact ih _ (mas_lt axe h2') _ _ _ hm

/-- `+darn:so` crashes only at axis `0`. -/
theorem darn_some (one two : Sock) {axe : Nat} (h0 : axe ≠ 0) : ∃ s, So.darn one axe two = some s := by
  unfold So.darn
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact darnDown_some axe one two [] h0

end Bake

end SkaModel
end Formalization
