import lemmas.Ska.SitesMeet

/-!
# `SitesMeet` against `+know` without folding

`knowMono_false` (`KnowMonoFalse.lean`) shows that `KnowMono` cannot come
from the sock operations alone: under a bake, a fold can make `+double-int`
forget a part that it keeps under `less.cur`.  A second effect of the same
kind: the run under `less.cur` may fold a `%6` that the run under the bake
does not (when the bake's run forgot the test's part), and then the bake's
run lists sites of a branch that the run under `less.cur` never walks.

Both effects go away when the run under the bake is compared with the run
of `+know` *without folding* under `less.cur` (`fold = false`): that run
walks every branch, as the analysis does (`Analysis.lean` never folds a
`%6`), so every site of the bake's run has a site at the same place, and
the relation between the two runs is that their socks share a noun
(`Meets`), which `+double-int` keeps since it knows no more than either
side.  So:

1. `LessProvidesNF`: under the code requirement, without folding, every
   site provides its callee's code requirement.  This is the form of
   `LessProvides` closest to the analysis.
2. `KnowMeetsNF`: every site of `+know` under a bake (with the poke's fold
   flag) has a site of the same callee in the run without folding under
   `less.cur` whose sock shares a noun with it.

`sitesMeet_of_nf`: the two give `SitesMeet`, with no `SitesInhab` (the
shared noun is the noun of the site).  The operations keep `Meets`:
`meets_knit`, `meets_doubleInt`, `meets_doubleInt_left`, `meets_pull`.
`KnowMeetsNF` is proved in `KnowMeets.lean` (`knowMeetsNF_of`), by
induction on the nomm over the two runs, from three facts about the datums
(`DatInhab`, `LessInhab`, `NoAx0Dat`), all three checked on the real
compiler.  `LessProvidesNF` is not proved; it held on the real compiler,
and `KnowMeets.lean` states its residue (`ProdSame`).
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

variable {M : Type → Type → Type} [Treap M]

/-- **Without folding, under the code requirement, every site provides its
callee's code requirement**, for callees that are not the root. -/
def LessProvidesNF (E : BEnv M) : Prop :=
  ∀ cur d out sites, E.dat cur = some d → know false d.nomm cur.less E.dat idc = some (out, sites) →
    ∀ c k, (c, k) ∈ sites → c ≠ E.root → Sub k c.less

/-- **Every site under a bake meets a site of the same callee of the run
without folding under `less.cur`.** -/
def KnowMeetsNF (E : BEnv M) : Prop :=
  ∀ cur s d out sites, BakeOK cur.less s → E.dat cur = some d →
    know E.fold d.nomm s E.dat idc = some (out, sites) →
      ∃ out' sites', know false d.nomm cur.less E.dat idc = some (out', sites') ∧
        ∀ c k, (c, k) ∈ sites → c ≠ E.root → ∃ k', (c, k') ∈ sites' ∧ Meets k k'

omit [Treap M] in
/-- **`SitesMeet` from `LessProvidesNF` and `KnowMeetsNF`.**  The noun the
site shares with the site without folding fits that site's sock, which is
under the callee's code requirement. -/
theorem sitesMeet_of_nf {E : BEnv M} (hl : LessProvidesNF E) (hm : KnowMeetsNF E) : SitesMeet E := by
  intro cur s d out sites hb hd hk c k hck hc
  obtain ⟨out', sites', hk', hmatch⟩ := hm cur s d out sites hb hd hk
  obtain ⟨k', hk'm, y, hy, hy'⟩ := hmatch c k hck hc
  exact ⟨y, hl cur d out' sites' hd hk' c k' hk'm hc y hy', hy⟩

/-! ## The sock operations keep `Meets` -/

/-- `+knit:so` keeps `Meets`. -/
theorem meets_knit {a a' b b' : Sock} (ha : Meets a a') (hb : Meets b b') :
    Meets (So.knit a b) (So.knit a' b') :=
  let ⟨x, h1, h2⟩ := ha
  let ⟨y, h3, h4⟩ := hb
  ⟨C x y, knit_fits h1 h3, knit_fits h2 h4⟩

/-- `+double-int` keeps `Meets` of its first sides, whatever its second
sides are. -/
theorem meets_doubleInt {a a' b b' : Anno} (ha : Meets a.sock a'.sock) :
    Meets (doubleInt a b).sock (doubleInt a' b').sock :=
  let ⟨x, h1, h2⟩ := ha
  ⟨x, doubleInt_fits_left a b h1, doubleInt_fits_left a' b' h2⟩

/-- A branch taken by a fold meets the join of both branches without the
fold. -/
theorem meets_doubleInt_left {a a' b' : Anno} (ha : Meets a.sock a'.sock) :
    Meets a.sock (doubleInt a' b').sock :=
  let ⟨x, h1, h2⟩ := ha
  ⟨x, h1, doubleInt_fits_left a' b' h2⟩

/-- `+pull:so` keeps `Meets`: the shared noun's part at the axis, or any
noun when the shared noun has no such part (both pulls are blank then). -/
theorem meets_pull {a a' r r' : Sock} {p : Nat} (ha : Meets a a') (hp : p ≠ 0)
    (h1 : So.pull a p = some r) (h2 : So.pull a' p = some r') : Meets r r' := by
  obtain ⟨y, h1y, h2y⟩ := ha
  cases hs : slot? p y with
  | some m => exact ⟨m, pull_fits h1y hs h1, pull_fits h2y hs h2⟩
  | none =>
    exact ⟨A 0, (pull_blank_of_none h1y hp hs h1).fits _, (pull_blank_of_none h2y hp hs h2).fits _⟩

/-- A sock that knows less than one with a noun meets it: the run under a
bake starts from a subject sock that meets `less.cur`. -/
theorem meets_of_bakeOK {L s : Sock} (hb : BakeOK L s) (hL : ∃ y, Fits L y) : Meets s L := by
  rcases hb with rfl | ⟨hsub, y, hy⟩
  · obtain ⟨y, hy⟩ := hL; exact ⟨y, hy, hy⟩
  · exact ⟨y, hy, hsub y hy⟩

end Bake

end SkaModel
end Formalization
