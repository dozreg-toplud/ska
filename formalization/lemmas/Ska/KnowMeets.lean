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
   turns those into `[0 0]`, see `Analysis.lean`, and the Hoon type of
   `nomm` says `p.p != 0`).

Checked on the real compiler (runhoon.sh, 2026-11-24), with no failure.
`tools/hoon/sitesmeet4.hoon` (the fifteen pokes of `sitesmeet3.hoon`, with
a copy of `+know` that takes `fold` as a sample): after the last poke, 3,033
pairs of a code bell and a bake (1,555 strict), 11,370 sites under the
bakes with folding and 11,661 sites of the runs without folding under
`less.cur`; `LessProvidesNF` failed at 0 sites (roots included),
`KnowMeetsNF` at 0 sites (roots included), `SitesMeet` at 0, and `+know`
without folding never crashed.  `tools/hoon/sitesmeet5.hoon`: after every
poke, no datum of the memo (1,463 after the last poke) has a product or a
code requirement without a noun, and no nomm has a `%10` at axis `0`; no
pruned graph (1,094 entries for the last poke) has two identities of one
code bell, so the residue below was not exercised.
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

/-! ## A literal of `+know` knows exactly its noun -/

theorem litAnno_only {v x z : Noun} (hx : lit (Nomm.n1 v) = some x) (hz : Fits (litAnno v).sock z) : z = x := by
  simp only [lit, Option.some.injEq] at hx
  subst hx
  exact hz

theorem lit_none_n1 {n : Nomm} {x : Noun} (hx : lit n = some x) (hn : ∀ v, n ≠ Nomm.n1 v) : False :=
  hn x (lit_eq hx)

/-- **A literal that `+know` returns knows exactly its noun.** -/
theorem knowGo_lit (fold : Bool) (dat : Bell → Option Datum) (res : Bell → Sock → Option Bell) :
    ∀ (nm : Nomm) (sub : Anno) (st : List Site) (r : (Nomm × Anno) × List Site),
      knowGo fold dat res nm sub st = some r → ∀ x, lit r.1.1 = some x → ∀ z, Fits r.1.2.sock z → z = x := by
  intro nm
  induction nm with
  | cons p q _ _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, _, r1, _, h⟩ := h
    split at h
    · cases h; exact litAnno_only hx hz
    · cases h; simp [lit] at hx
  | n0 p =>
    intro sub st r h x hx z hz
    simp only [knowGo] at h
    split at h
    · cases h; simp [lit] at hx
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨prod, _, h⟩ := h
      split at h
      · rename_i d hk
        cases h
        simp only [lit, Option.some.injEq] at hx
        subst hx
        exact known_fits hk hz
      · cases h; simp [lit] at hx
  | n1 p =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.some.injEq] at h
    subst h
    exact litAnno_only hx hz
  | n2 p q info _ _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s, _, f, _, h⟩ := h
    split at h
    · cases h; simp [lit] at hx
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, h⟩ := h
      cases h; simp [lit] at hx
  | n3 p _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, _, h⟩ := h
    split at h
    · cases h; exact litAnno_only hx hz
    · cases h; simp [lit] at hx
  | n4 p _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, _, h⟩ := h
    split at h
    · cases h; exact litAnno_only hx hz
    · cases h; simp [lit] at hx
  | n5 p q _ _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, _, b, _, h⟩ := h
    split at h
    · cases h; exact litAnno_only hx hz
    · cases h; simp [lit] at hx
  | n6 p q r0 _ ihq ihr =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, _, h⟩ := h
    split at h
    · exact ihq _ _ _ h x hx z hz
    · exact ihr _ _ _ h x hx z hz
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, c, _, rfl⟩ := h
      simp [lit] at hx
  | n7 p q ihp ihq =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    split at h
    · rename_i hl _
      cases h
      rw [hl, Option.some.injEq] at hx
      subst hx
      exact hz
    · cases h; simp [lit] at hx
  | n10 ax v q _ _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, _, b, _, h⟩ := h
    split at h
    · cases h; exact litAnno_only hx hz
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s, _, h⟩ := h
      cases h; simp [lit] at hx
  | n11s tag q body ihq =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    split at h
    · rename_i hl
      cases h
      rw [hl, Option.some.injEq] at hx
      subst hx
      exact hz
    · cases h; simp [lit] at hx
  | n11d tag hh q body ihh ihq =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    split at h
    · rename_i hl
      cases h
      rw [hl, Option.some.injEq] at hx
      subst hx
      exact hz
    · cases h; simp [lit] at hx
  | n12 p q _ _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, _, b, _, rfl⟩ := h
    simp [lit] at hx
  | mean p b q body k _ _ =>
    intro sub st r h x hx z hz
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, _, v, _, c, _, rfl⟩ := h
    simp [lit] at hx

/-! ## Run B returns -/

/-- No `%10` of the nomm has axis `0`. -/
def NoAx0 : Nomm → Prop
  | Nomm.cons p q => NoAx0 p ∧ NoAx0 q
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n2 p q _ => NoAx0 p ∧ NoAx0 q
  | Nomm.n3 p => NoAx0 p
  | Nomm.n4 p => NoAx0 p
  | Nomm.n5 p q => NoAx0 p ∧ NoAx0 q
  | Nomm.n6 p q r => NoAx0 p ∧ NoAx0 q ∧ NoAx0 r
  | Nomm.n7 p q => NoAx0 p ∧ NoAx0 q
  | Nomm.n10 a v q => a ≠ 0 ∧ NoAx0 v ∧ NoAx0 q
  | Nomm.n11s _ q _ => NoAx0 q
  | Nomm.n11d _ h q _ => NoAx0 h ∧ NoAx0 q
  | Nomm.n12 p q => NoAx0 p ∧ NoAx0 q
  | Nomm.mean p _ q _ _ => NoAx0 p ∧ NoAx0 q

/-- **`+know` without folding and with `idc` never crashes** on a nomm with
no `%10` at axis `0`: its only crash is `+darn:so` there. -/
theorem knowGo_nf_some (dat : Bell → Option Datum) :
    ∀ (nm : Nomm), NoAx0 nm → ∀ (sub : Anno) (st : List Site), ∃ r, knowGo false dat idc nm sub st = some r := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro hn sub st
    obtain ⟨l, hl⟩ := ihp hn.1 sub st
    obtain ⟨r, hr⟩ := ihq hn.2 sub l.2
    simp [knowGo, hl, hr]
  | n0 p =>
    intro _ sub st
    by_cases h0 : p = 0
    · subst h0; simp [knowGo]
    · by_cases h1 : p = 1
      · subst h1; simp [knowGo]
      · obtain ⟨s, src⟩ := sub
        cases s <;> simp [knowGo, h0, h1, So.pull]
  | n1 p => intro _ sub st; simp [knowGo]
  | n2 p q info ihp ihq =>
    intro hn sub st
    obtain ⟨s, hs⟩ := ihp hn.1 sub st
    obtain ⟨f, hf⟩ := ihq hn.2 sub s.2
    cases info <;> simp [knowGo, hs, hf, idc]
  | n3 p ih =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ih hn sub st
    simp [knowGo, ha]
  | n4 p ih =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ih hn sub st
    simp [knowGo, ha]
  | n5 p q ihp ihq =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihp hn.1 sub st
    obtain ⟨b, hb⟩ := ihq hn.2 sub a.2
    simp [knowGo, ha, hb]
  | n6 p q r0 ihp ihq ihr =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihp hn.1 sub st
    obtain ⟨b, hb⟩ := ihq hn.2.1 sub a.2
    obtain ⟨c, hc⟩ := ihr hn.2.2 sub b.2
    simp [knowGo, ha, hb, hc]
  | n7 p q ihp ihq =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihp hn.1 sub st
    obtain ⟨b, hb⟩ := ihq hn.2 a.1.2 a.2
    simp [knowGo, ha, hb]
  | n10 ax v q ihv ihq =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihv hn.2.1 sub st
    obtain ⟨b, hb⟩ := ihq hn.2.2 sub a.2
    obtain ⟨s, hs⟩ := darn_some b.1.2.sock a.1.2.sock hn.1
    simp [knowGo, ha, hb, hs]
  | n11s tag q body ih =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ih hn sub st
    simp [knowGo, ha]
  | n11d tag hh q body ihh ihq =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihh hn.1 sub st
    obtain ⟨b, hb⟩ := ihq hn.2 sub a.2
    simp [knowGo, ha, hb]
  | n12 p q ihp ihq =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihp hn.1 sub st
    obtain ⟨b, hb⟩ := ihq hn.2 sub a.2
    simp [knowGo, ha, hb]
  | mean p b q body k ihp ihq =>
    intro hn sub st
    obtain ⟨a, ha⟩ := ihp hn.1 sub st
    obtain ⟨c, hc⟩ := ihq hn.2 sub ((b, a.1.2.sock) :: a.2)
    simp [knowGo, ha, hc, idc]

/-! ## The two runs -/

/-- Every site of `L` has a site of the same callee in `L'` whose sock
shares a noun with it. -/
def SitesRel (L L' : List Site) : Prop := ∀ c k, (c, k) ∈ L → ∃ k', (c, k') ∈ L' ∧ Meets k k'

theorem SitesRel.mono {L L1 L2 : List Site} (h : SitesRel L L1) (hs : L1 <:+ L2) : SitesRel L L2 :=
  fun c k hck => let ⟨k', hm, hk⟩ := h c k hck; ⟨k', hs.subset hm, hk⟩

theorem SitesRel.cons {L L' : List Site} (h : SitesRel L L') {c : Bell} {k k' : Sock} (hk : Meets k k') :
    SitesRel ((c, k) :: L) ((c, k') :: L') := by
  intro c0 k0 hm
  rcases List.mem_cons.mp hm with he | hm
  · cases he; exact ⟨k', List.mem_cons_self, hk⟩
  · obtain ⟨k1, h1, h2⟩ := h c0 k0 hm
    exact ⟨k1, List.mem_cons_of_mem _ h1, h2⟩

theorem fits_of_only {a a' : Sock} {x : Noun} (honly : ∀ z, Fits a z → z = x) (hm : Meets a a') : Fits a' x :=
  let ⟨w, h1, h2⟩ := hm; (honly w h1) ▸ h2

theorem meets_dunno_dunno : Meets Anno.dunno.sock Anno.dunno.sock := ⟨A 0, fits_dunno _, fits_dunno _⟩

theorem meets_lit_dunno (v : Noun) : Meets (litAnno v).sock Anno.dunno.sock := ⟨v, rfl, fits_dunno _⟩

/-- A branch taken by a fold meets the join of both branches without the
fold, on the second branch. -/
theorem meets_doubleInt_right {b a' b' : Anno} (hb : Meets b.sock b'.sock) :
    Meets b.sock (doubleInt a' b').sock :=
  let ⟨x, h1, h2⟩ := hb
  ⟨x, h1, doubleInt_fits_right a' b' h2⟩

/-- `knowGo` on Nock 0 at a nonzero axis: the sites are kept, and the
product's sock is what the subject's sock knows at the axis. -/
theorem knowGo_n0_read {fold : Bool} {dat : Bell → Option Datum} {res : Bell → Sock → Option Bell}
    {sub : Anno} {st : List Site} {p : Nat} {r : (Nomm × Anno) × List Site} (hp0 : p ≠ 0)
    (h : knowGo fold dat res (Nomm.n0 p) sub st = some r) :
    r.2 = st ∧ (if p = 1 then some sub.sock else So.pull sub.sock p) = some r.1.2.sock := by
  simp only [knowGo, if_neg hp0, Option.map_eq_some_iff] at h
  obtain ⟨prod, hprod, h⟩ := h
  have e : r.2 = st ∧ r.1.2.sock = prod.sock := by
    split at h <;> (subst h; exact ⟨rfl, rfl⟩)
  refine ⟨e.1, ?_⟩
  rw [e.2]
  split at hprod
  · rename_i h1; cases hprod; rw [if_pos h1]
  · rename_i h1
    rw [if_neg h1]
    simp only [Option.map_eq_some_iff] at hprod
    obtain ⟨s', hs', rfl⟩ := hprod
    exact hs'

/-- **The run under a bake against the run without folding.**  If the two
subject socks share a noun, so do the two products, and every site of the
first run has a site of the same callee in the second whose sock shares a
noun with it.  `fold` is the first run's flag; the second never folds. -/
theorem knowGo_meets (fold : Bool) (dat : Bell → Option Datum)
    (hdat : ∀ b d, dat b = some d → ∃ y, Fits d.prod y) :
    ∀ (nm : Nomm) (sub sub' : Anno) (st st' : List Site) (r r' : (Nomm × Anno) × List Site),
      knowGo fold dat idc nm sub st = some r → knowGo false dat idc nm sub' st' = some r' →
      Meets sub.sock sub'.sock → SitesRel st st' →
      Meets r.1.2.sock r'.1.2.sock ∧ SitesRel r.2 r'.2 := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff] at h h'
    obtain ⟨l, hl, r1, hr1, h⟩ := h
    obtain ⟨l', hl', r1', hr1', h'⟩ := h'
    simp only [Option.some.injEq] at h'
    subst h'
    obtain ⟨ml, sl⟩ := ihp sub sub' st st' l l' hl hl' hs hst
    obtain ⟨mr, sr⟩ := ihq sub sub' l.2 l'.2 r1 r1' hr1 hr1' hs sl
    split at h
    · rename_i x y hx hy
      cases h
      exact ⟨⟨C x y, rfl, knit_fits (fits_of_only (knowGo_lit _ _ _ _ _ _ _ hl x hx) ml)
        (fits_of_only (knowGo_lit _ _ _ _ _ _ _ hr1 y hy) mr)⟩, sr⟩
    · cases h
      exact ⟨meets_knit ml mr, sr⟩
  | n0 p =>
    intro sub sub' st st' r r' h h' hs hst
    by_cases hp0 : p = 0
    · subst hp0
      simp only [knowGo, if_pos, Option.some.injEq] at h h'
      subst h; subst h'
      exact ⟨meets_dunno_dunno, hst⟩
    · obtain ⟨e1, e2⟩ := knowGo_n0_read hp0 h
      obtain ⟨e1', e2'⟩ := knowGo_n0_read hp0 h'
      rw [e1, e1']
      refine ⟨?_, hst⟩
      by_cases hp1 : p = 1
      · rw [if_pos hp1] at e2 e2'
        rw [← Option.some.inj e2, ← Option.some.inj e2']
        exact hs
      · rw [if_neg hp1] at e2 e2'
        exact meets_pull hs hp0 e2 e2'
  | n1 p =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.some.injEq] at h h'
    subst h; subst h'
    exact ⟨⟨p, rfl, rfl⟩, hst⟩
  | n2 p q info ihp ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff] at h h'
    obtain ⟨s, hs1, f, hf, h⟩ := h
    obtain ⟨s', hs1', f', hf', h'⟩ := h'
    obtain ⟨ms, ss⟩ := ihp sub sub' st st' s s' hs1 hs1' hs hst
    obtain ⟨-, sf⟩ := ihq sub sub' s.2 s'.2 f f' hf hf' hs ss
    cases info with
    | none =>
      simp only [Option.some.injEq] at h h'
      subst h; subst h'
      exact ⟨meets_dunno_dunno, sf⟩
    | some i =>
      obtain ⟨b, mk⟩ := i
      simp only [idc, Option.map_some, Option.some.injEq] at h h'
      subst h; subst h'
      refine ⟨?_, sf.cons ms⟩
      cases hd : dat b with
      | none => exact meets_dunno_dunno
      | some d => exact meets_patchProd ms d.map d.prod (hdat b d hd)
  | n3 p ih =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', h'⟩ := h'
    subst h'
    obtain ⟨-, sa⟩ := ih sub sub' st st' a a' ha ha' hs hst
    split at h <;> (subst h; first | exact ⟨meets_lit_dunno _, sa⟩ | exact ⟨meets_dunno_dunno, sa⟩)
  | n4 p ih =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', h'⟩ := h'
    subst h'
    obtain ⟨-, sa⟩ := ih sub sub' st st' a a' ha ha' hs hst
    split at h <;> (subst h; first | exact ⟨meets_lit_dunno _, sa⟩ | exact ⟨meets_dunno_dunno, sa⟩)
  | n5 p q ihp ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', b', hb', h'⟩ := h'
    subst h'
    obtain ⟨-, sa⟩ := ihp sub sub' st st' a a' ha ha' hs hst
    obtain ⟨-, sb⟩ := ihq sub sub' a.2 a'.2 b b' hb hb' hs sa
    split at h <;> (subst h; first | exact ⟨meets_lit_dunno _, sb⟩ | exact ⟨meets_dunno_dunno, sb⟩)
  | n6 p q r0 ihp ihq ihr =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
    obtain ⟨a', ha', b', hb', c', hc', h'⟩ := h'
    subst h'
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨-, sa⟩ := ihp sub sub' st st' a a' ha ha' hs hst
    split at h
    · obtain ⟨mq, sq⟩ := ihq sub sub' a.2 a'.2 r b' h hb' hs sa
      exact ⟨meets_doubleInt_left mq, sq.mono (knowGo_suffix _ _ _ _ _ _ c' hc')⟩
    · obtain ⟨mr, sr⟩ := ihr sub sub' a.2 b'.2 r c' h hc' hs (sa.mono (knowGo_suffix _ _ _ _ _ _ _ hb'))
      exact ⟨meets_doubleInt_right mr, sr⟩
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, c, hc, rfl⟩ := h
      obtain ⟨mq, sq⟩ := ihq sub sub' a.2 a'.2 b b' hb hb' hs sa
      obtain ⟨-, sr⟩ := ihr sub sub' b.2 b'.2 c c' hc hc' hs sq
      exact ⟨meets_doubleInt mq, sr⟩
  | n7 p q ihp ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', b', hb', h'⟩ := h'
    subst h'
    obtain ⟨ma, sa⟩ := ihp sub sub' st st' a a' ha ha' hs hst
    obtain ⟨mb, sb⟩ := ihq a.1.2 a'.1.2 a.2 a'.2 b b' hb hb' ma sa
    split at h
    · rename_i x hx _
      subst h
      exact ⟨⟨x, rfl, fits_of_only (knowGo_lit _ _ _ _ _ _ _ hb x hx) mb⟩, sb⟩
    · subst h
      exact ⟨mb, sb⟩
  | n10 ax v q ihv ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff] at h h'
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', b', hb', h'⟩ := h'
    obtain ⟨ma, sa⟩ := ihv sub sub' st st' a a' ha ha' hs hst
    obtain ⟨mb, sb⟩ := ihq sub sub' a.2 a'.2 b b' hb hb' hs sa
    simp only [Option.map_eq_some_iff] at h'
    obtain ⟨s', hs', rfl⟩ := h'
    split at h
    · rename_i u hu
      cases h
      split at hu
      · rename_i x y hx hy
        exact ⟨⟨u, rfl, darn_fits (fits_of_only (knowGo_lit _ _ _ _ _ _ _ hb y hy) mb)
          (fits_of_only (knowGo_lit _ _ _ _ _ _ _ ha x hx) ma) hu hs'⟩, sb⟩
      · cases hu
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s, hs1, rfl⟩ := h
      exact ⟨meets_darn mb ma hs1 hs', sb⟩
  | n11s tag q body ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', h'⟩ := h'
    subst h'
    obtain ⟨ma, sa⟩ := ihq sub sub' st st' a a' ha ha' hs hst
    split at h
    · rename_i x _ hx
      subst h
      exact ⟨⟨x, rfl, fits_of_only (knowGo_lit _ _ _ _ _ _ _ ha x hx) ma⟩, sa⟩
    · subst h
      exact ⟨ma, sa⟩
  | n11d tag hh q body ihh ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', b', hb', h'⟩ := h'
    subst h'
    obtain ⟨-, sa⟩ := ihh sub sub' st st' a a' ha ha' hs hst
    obtain ⟨mb, sb⟩ := ihq sub sub' a.2 a'.2 b b' hb hb' hs sa
    split at h
    · rename_i x _ _ hx
      subst h
      exact ⟨⟨x, rfl, fits_of_only (knowGo_lit _ _ _ _ _ _ _ hb x hx) mb⟩, sb⟩
    · subst h
      exact ⟨mb, sb⟩
  | n12 p q ihp ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', b', hb', rfl⟩ := h'
    obtain ⟨-, sa⟩ := ihp sub sub' st st' a a' ha ha' hs hst
    obtain ⟨-, sb⟩ := ihq sub sub' a.2 a'.2 b b' hb hb' hs sa
    exact ⟨meets_dunno_dunno, sb⟩
  | mean p b q body k ihp ihq =>
    intro sub sub' st st' r r' h h' hs hst
    simp only [knowGo, idc, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨a, ha, c, hc, rfl⟩ := h
    obtain ⟨a', ha', c', hc', rfl⟩ := h'
    obtain ⟨ma, sa⟩ := ihp sub sub' st st' a a' ha ha' hs hst
    exact ihq sub sub' _ _ c c' hc hc' hs (sa.cons ma)

/-! ## `KnowMeetsNF` -/

section Env

variable {M : Type → Type → Type} [Treap M]

/-- **Every datum's product sock has a noun** (`+pop` turns `%void` into
`|+~`). -/
def DatInhab (E : BEnv M) : Prop := ∀ b d, E.dat b = some d → ∃ y, Fits d.prod y

/-- **Every code bell with a datum has a code requirement with a noun.** -/
def LessInhab (E : BEnv M) : Prop := ∀ cur d, E.dat cur = some d → ∃ y, Fits cur.less y

/-- **No `%10` of a datum's nomm has axis `0`.** -/
def NoAx0Dat (E : BEnv M) : Prop := ∀ cur d, E.dat cur = some d → NoAx0 d.nomm

omit [Treap M] in
/-- **`KnowMeetsNF` from three facts about the datums**: products and code
requirements have nouns, and no `%10` has axis `0`. -/
theorem knowMeetsNF_of {E : BEnv M} (hp : DatInhab E) (hl : LessInhab E) (hn : NoAx0Dat E) :
    KnowMeetsNF E := by
  intro cur s d out sites hb hd hk
  obtain ⟨rB, hrB⟩ := knowGo_nf_some E.dat d.nomm (hn cur d hd) ⟨cur.less, A 1⟩ []
  simp only [know, Option.map_eq_some_iff] at hk
  obtain ⟨rA, hrA, he⟩ := hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨rB.1.1, rB.2, by simp [know, hrB], ?_⟩
  obtain ⟨-, hs⟩ := knowGo_meets E.fold E.dat hp d.nomm _ _ [] [] rA rB hrA hrB
    (meets_of_bakeOK hb (hl cur d hd)) (fun _ _ h => by simp at h)
  intro c k hck _
  exact hs c k hck

omit [Treap M] in
/-- **`SitesMeet` from `LessProvidesNF` and the three facts about the
datums.** -/
theorem sitesMeet_of_lessNF {E : BEnv M} (hlp : LessProvidesNF E) (hp : DatInhab E) (hl : LessInhab E)
    (hn : NoAx0Dat E) : SitesMeet E :=
  sitesMeet_of_nf hlp (knowMeetsNF_of hp hl hn)

end Env

/-! ## The residue of `LessProvidesNF`

`LessProvidesNF` asks that, under `less.cur` and without folding, every
site provides its callee's code requirement (`Sub k c.less`).  The analysis
never folds a `%6` (`folStep` joins both branches with `doubleInt`), so its
walk of the same nomm under its own subject sock is `+know` without folding,
with two differences: its subject sock knows more than `less.cur` only off
the code cape, and a call's product is the product of the identity it
resolved to, where `+know` reads the product of `dat`'s datum for the
callee's code bell, patched for the site.  A part of a site's sock that the
callee's code requirement knows comes from the caller's subject through
provenance (then the caller's code requirement knows it, as the analysis'
subject did), from a constant of the formula, or from a callee's product
without provenance.  Only the last can differ: when two identities of one
code bell have products that differ there, `dat` may give the other one.

Two forms of the residue, over the entries of one call graph:

1. `ProdMeet`: the two patched products share a noun.  This is what the
   products' soundness gives whenever the callee returns on some subject of
   its code requirement and the site, and it is what `SitesMeet` needs in
   spirit, but it does not give `LessProvidesNF`: a part that one identity's
   product knows and the other's does not is lost at the site.
2. `ProdSame`: the two patched products have the same nouns.  This gives
   `LessProvidesNF` by the argument above (not proved here: it needs the
   analysis' walk and `+know`'s walk related node by node, as
   `knowGo_meets` relates two walks of `+know`).

`tools/hoon/sitesmeet5.hoon` checks `ProdMeet` (with the sock `less.c` and
the two identities' subjects) and the equality of the patched products
under `less.c`, over every two entries of one code bell in the pruned graph
of each poke: there were none in the fifteen pokes. -/

section Residue

variable {M : Type → Type → Type} [Treap M]

/-- **Two identities of one code bell have products that do not
contradict**: patched for any sock with a noun under the code requirement,
they share a noun. -/
def ProdMeet (g : Callgraph M) : Prop :=
  ∀ (id1 id2 : Ident) (d1 d2 : FDatum M), Treap.get g id1 = some d1 → Treap.get g id2 = some d2 →
    id1.2 = id2.2 → d1.less = d2.less → ∀ k, Sub k d1.less → (∃ y, Fits k y) →
      Meets (patchProd d1.prod d1.map k).sock (patchProd d2.prod d2.map k).sock

/-- **Two identities of one code bell have the same products**, patched for
any sock under the code requirement: the form of the residue that gives
`LessProvidesNF`. -/
def ProdSame (g : Callgraph M) : Prop :=
  ∀ (id1 id2 : Ident) (d1 d2 : FDatum M), Treap.get g id1 = some d1 → Treap.get g id2 = some d2 →
    id1.2 = id2.2 → d1.less = d2.less → ∀ k, Sub k d1.less →
      Sub (patchProd d1.prod d1.map k).sock (patchProd d2.prod d2.map k).sock

/-- `ProdSame` gives `ProdMeet` when the products have nouns. -/
theorem prodMeet_of_same {g : Callgraph M} (h : ProdSame g)
    (hinh : ∀ id d k, Treap.get g id = some d → Sub k d.less → (∃ y, Fits k y) →
      ∃ y, Fits (patchProd d.prod d.map k).sock y) : ProdMeet g := by
  intro id1 id2 d1 d2 h1 h2 hf hl k hk hky
  obtain ⟨y, hy⟩ := hinh id1 d1 k h1 hk hky
  exact ⟨y, hy, h id1 id2 d1 d2 h1 h2 hf hl k hk y hy⟩

end Residue

end Bake

end SkaModel
end Formalization
