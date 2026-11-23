import lemmas.Ska.PokeAna

/-!
# `SitesMeet` from three invariants

`SitesMeet` (`BakeImp.lean`) asks, of every code bell `cur` that `dat`
has a datum for and of every bake `s` under `less.cur`, that every site
`[c k]` that `+know` lists under `s`, of a callee that is not the root,
shares a noun with `less.c`.  This file reduces it to three statements
about `+know` and the datums, each smaller than `SitesMeet` and each
checked on the real compiler (see below):

1. `LessProvides`: under the code requirement itself, every site provides
   its callee's code requirement (`huge:so less.c k`).  This is the sock
   form of what a memo hit of `cur` needs: the code requirement was chosen
   so that what it knows reaches every callee's code.  It is stronger than
   `SitesMeet` at `s = less.cur`.
2. `KnowMono`: `+know` is monotone in the subject sock.  Under a bake that
   knows more than `less.cur` (and has a noun), `+know` returns whenever it
   returns under `less.cur`, and each of its sites has a site of the same
   callee under `less.cur` whose sock knows no more (`huge:so k' k`).  The
   sites under the bake are fewer when a fold takes one branch of a `%6`,
   never new.  This is a statement about `knowGo` alone, by induction on the
   nomm, from the monotonicity of each sock operation (`+pull:so`,
   `+knit:so`, `+darn:so`, `+patch-prod` in its new sock, and `+double-int`,
   whose provenance test is the one place where a fold, which drops
   provenance, has to be looked at).  That last case defeats it:
   `knowMono_false` (`KnowMonoFalse.lean`) is a model counterexample, and
   `SitesMeetNF.lean` replaces `KnowMono` and `LessProvides` by forms that
   compare with `+know` without folding under `less.cur`.
3. `SitesInhab`: under a bake, every site's sock has a noun (it is not
   `%void`).

`sitesMeet_of_parts`: the three give `SitesMeet`.  A site under the bake
knows at least what the matching site under `less.cur` knows, which knows at
least what `less.c` knows, and it has a noun.  At `s = less.cur` the first
step is the identity, so `LessProvides` and `SitesInhab` alone give
`SitesMeet` there (`sitesMeet_at_less`).

Why `LessProvides` is the right invariant to aim at next (an argument, not
proved here).  `less.c` knows a part of the callee's subject only where the
analysis' sock at the site knew it and the callee uses it as code.  Such a
part is (a) a part of `cur`'s subject, through provenance, which is then in
`cur`'s want, so `less.cur` knows it as the analysis' subject did; (b) a
constant of the formula; (c) a part of a callee's product without
provenance, which `+know` reads from `dat`.  Only (c) can differ, when `dat`
gives the datum of another identity of the same code bell than the one the
analysis read; a join of two branches keeps a part only where both
branches agree on sock and provenance, which (a), (b), (c) are, under
`less.cur` as under the analysis' subject.  So `LessProvides` reduces to a
coherence of the products of the identities of one code bell, which is the
residue the earlier reports describe.

Checked on the real compiler (runhoon.sh, `tools/hoon/sitesmeet3.hoon`,
2026-11-24), with no failure: the fifteen pokes of `sitesmeet2.hoon` in
sequence, and after each one every pair of a code bell and a bake of the
state (every variant `v` of `vars` under `less.v`, every memo entry under its
own code requirement): 3,033 pairs after the last poke, 1,555 of them with a
bake other than `less.c`, and 11,370 sites.  `LessProvides` as `huge:so less.b
k'` for every site of `+know` under `less.c` whose callee is not a root,
`KnowMono` as a site `[b k']` under `less.c` with `huge:so k' k` for every
site `[b k]` under the bake (and `+know` under `less.c` did not crash), and
`SitesInhab` as `k` not `%void`.  These are the checks of `sitesmeet2.hoon`
(`SitesMeet` itself) split along the proof.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

variable {M : Type → Type → Type} [Treap M]

/-- Two socks share a noun. -/
def Meets (a b : Sock) : Prop := ∃ y, Fits a y ∧ Fits b y

theorem Meets.symm {a b : Sock} (h : Meets a b) : Meets b a :=
  let ⟨y, h1, h2⟩ := h; ⟨y, h2, h1⟩

/-- `Meets` is closed upward on each side. -/
theorem Meets.mono {a a' b b' : Sock} (h : Meets a b) (ha : Sub a a') (hb : Sub b b') : Meets a' b' :=
  let ⟨y, h1, h2⟩ := h; ⟨y, ha y h1, hb y h2⟩

/-- A sock with a noun meets every sock above it. -/
theorem meets_of_sub {a b : Sock} (hy : ∃ y, Fits a y) (h : Sub a b) : Meets b a :=
  let ⟨y, hy⟩ := hy; ⟨y, h y hy, hy⟩

/-- **Under the code requirement, every site provides its callee's code
requirement** (`huge:so less.c k`), for callees that are not the root. -/
def LessProvides (E : BEnv M) : Prop :=
  ∀ cur d out sites, E.dat cur = some d → know E.fold d.nomm cur.less E.dat idc = some (out, sites) →
    ∀ c k, (c, k) ∈ sites → c ≠ E.root → Sub k c.less

/-- **`+know` is monotone in the subject sock**: under a sock with a noun
that knows at least what `less.cur` knows, `+know` returns when it does
under `less.cur`, and every site has a site of the same callee under
`less.cur` that knows no more. -/
def KnowMono (E : BEnv M) : Prop :=
  ∀ cur d s out sites, Sub s cur.less → (∃ y, Fits s y) → E.dat cur = some d →
    know E.fold d.nomm s E.dat idc = some (out, sites) →
      ∃ out' sites', know E.fold d.nomm cur.less E.dat idc = some (out', sites') ∧
        ∀ c k, (c, k) ∈ sites → ∃ k', (c, k') ∈ sites' ∧ Sub k k'

/-- **Every site's sock has a noun** under every bake that `BakeOK`
allows. -/
def SitesInhab (E : BEnv M) : Prop :=
  ∀ cur s d out sites, BakeOK cur.less s → E.dat cur = some d →
    know E.fold d.nomm s E.dat idc = some (out, sites) → ∀ c k, (c, k) ∈ sites → ∃ y, Fits k y

/-! ## Toward `KnowMono`: the sock operations of `+know` are monotone -/

omit [Treap M] in
/-- **`+knit:so` is monotone** in both socks. -/
theorem knit_mono {a a' b b' : Sock} (ha : Sub a a') (hb : Sub b b') : Sub (So.knit a b) (So.knit a' b') := by
  intro x hx
  rcases knit_fits_inv hx with ⟨ba, bb⟩ | ⟨x1, x2, rfl, h1, h2⟩
  · have ba' : a'.Blank := blank_of_all fun z => ha z (ba.fits z)
    have bb' : b'.Blank := blank_of_all fun z => hb z (bb.fits z)
    exact (knit_blank ba' bb').fits x
  · exact knit_fits (ha x1 h1) (hb x2 h2)

omit [Treap M] in
/-- `SitesMeet` at the code requirement itself, from `LessProvides` and
`SitesInhab`. -/
theorem sitesMeet_at_less {E : BEnv M} (hl : LessProvides E) (hi : SitesInhab E) {cur : Bell} {d : Datum}
    {out : Nomm} {sites : List Site} (hd : E.dat cur = some d)
    (hk : know E.fold d.nomm cur.less E.dat idc = some (out, sites)) :
    ∀ c k, (c, k) ∈ sites → c ≠ E.root → Meets c.less k := by
  intro c k hck hc
  exact meets_of_sub (hi cur cur.less d out sites (Or.inl rfl) hd hk c k hck) (hl cur d out sites hd hk c k hck hc)

omit [Treap M] in
/-- **`SitesMeet` from the three invariants.**  A site under the bake has
a noun, which fits the matching site under `less.cur` (`KnowMono`), which
fits `less.c` (`LessProvides`). -/
theorem sitesMeet_of_parts {E : BEnv M} (hl : LessProvides E) (hm : KnowMono E) (hi : SitesInhab E) :
    SitesMeet E := by
  intro cur s d out sites hb hd hk c k hck hc
  obtain ⟨y, hy⟩ := hi cur s d out sites hb hd hk c k hck
  rcases hb with rfl | ⟨hsub, hinh⟩
  · exact ⟨y, hl cur d out sites hd hk c k hck hc y hy, hy⟩
  · obtain ⟨out', sites', hk', hmatch⟩ := hm cur d s out sites hsub hinh hd hk
    obtain ⟨k', hk'm, hkk⟩ := hmatch c k hck
    exact ⟨y, hl cur d out' sites' hd hk' c k' hk'm hc y (hkk y hy), hy⟩

end Bake

namespace PokeM

open Bake

variable {M : Type → Type → Type} [Treap M] {J H R : Type}

/-- **The three invariants of every poke** from a state that satisfies
`InvB`. -/
def PokeParts (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    let E := anaEnv jet fold frozen s f L j hot dats memo' rd reg'
    LessProvides E ∧ KnowMono E ∧ SitesInhab E

/-- **`PokeSites` from the three invariants**, so `gap_of_meet` holds with
`PokeParts` in place of `PokeSites`. -/
theorem pokeSites_of_parts {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : PokeParts lib env jet fold frozen fuel regOf) : PokeSites lib env jet fold frozen fuel regOf :=
  fun s f L j hot pr dats memo' rd reg' hI hs =>
    let ⟨hl, hm, hi⟩ := h s f L j hot pr dats memo' rd reg' hI hs
    sitesMeet_of_parts hl hm hi

end PokeM

end SkaModel
end Formalization
