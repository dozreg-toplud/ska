import lemmas.Ska.LessProvides

/-!
# `SiteCover` from a replay of the analysis and a comparison of two walks

`knowT`: `+know` without folding and with `idc`, whose call product is read
from a table `T` indexed by the sites so far, the callee's code bell and the
site sock.  `+know false` with `dat` is the instance `datTab dat`
(`knowT_datTab`), so its sites are those of `knowT` (`know_sites_knowT`).
The analysis' walk of an identity `[more fol]` is meant to be the instance
whose table gives, at each site, the product (and map) of the identity the
analysis resolved there.

`SiteCover` is proved from two named statements (`siteCover_of`):

1. `Replay`: for every datum of `dat`, some `knowT` walk of its nomm (the
   analysis' walk under the identity's subject sock `more`, whose code
   requirement is `+app:ca` of `want` and `more`) returns, and every site of
   it that is not the root has a sock with a noun that provides the callee's
   code requirement.
2. `Compare`: on every such walk, each site of the walk of `+know` without
   folding under `less.cur` (the instance `datTab`) has a site of the same
   callee in the replayed walk whose sock it knows, on the callee's code
   requirement's cape, no less than.

Both walks walk the same nomm without folding, so their sites correspond
one to one, in order.  The induction that should prove `Compare` (as
`knowGo_meets` does for `Meets`) keeps equal provenance on the two sides and
"B knows, on every part whose provenance lies in `want`, what A knows
there"; at a call it needs the two tables to agree on maps and on the nouns
of the patched products (`ProdSameM` below, checked on the real compiler by
`tools/hoon/prodmaps.hoon`) and `want` to cover `distribute lc s.src` at
every site of A (what `callStep` adds to `want`).  None of the cases is
proved here.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-- A table of call products: from the sites before the call, the callee's
code bell and the site sock, the product and its map (before the
composition with the site's provenance), or `none` for no datum. -/
abbrev PTab := List Site → Bell → Sock → Option Anno

/-- The product of a call from the table's answer and the site's anno. -/
def callProd (pm : Option Anno) (s : Anno) : Anno :=
  match pm with
  | none => Anno.dunno
  | some p => ⟨p.sock, Pi.compose p.src s.src⟩

/-- **`+know` without folding and with `idc`, with a table of products.** -/
def knowT (T : PTab) : Nomm → Anno → List Site → Option (Anno × List Site)
  | Nomm.cons p q, sub, st =>
    (knowT T p sub st).bind fun l =>
    (knowT T q sub l.2).map fun r =>
    (⟨So.knit l.1.sock r.1.sock, Pi.cons l.1.src r.1.src⟩, r.2)
  | Nomm.n0 p, sub, st =>
    if p = 0 then some (Anno.dunno, st) else
    (if p = 1 then some sub else (So.pull sub.sock p).map fun s => (⟨s, Pi.slot sub.src p⟩ : Anno)).map
      fun prod => (prod, st)
  | Nomm.n1 p, _, st => some (litAnno p, st)
  | Nomm.n2 p q info, sub, st =>
    (knowT T p sub st).bind fun s =>
    (knowT T q sub s.2).map fun f =>
    match info with
    | none => (Anno.dunno, f.2)
    | some (b, _) => (callProd (T f.2 b s.1.sock) s.1, (b, s.1.sock) :: f.2)
  | Nomm.n3 p, sub, st => (knowT T p sub st).map fun r => (Anno.dunno, r.2)
  | Nomm.n4 p, sub, st => (knowT T p sub st).map fun r => (Anno.dunno, r.2)
  | Nomm.n5 p q, sub, st =>
    (knowT T p sub st).bind fun a => (knowT T q sub a.2).map fun b => (Anno.dunno, b.2)
  | Nomm.n6 p q r, sub, st =>
    (knowT T p sub st).bind fun a =>
    (knowT T q sub a.2).bind fun b =>
    (knowT T r sub b.2).map fun c => (doubleInt b.1 c.1, c.2)
  | Nomm.n7 p q, sub, st => (knowT T p sub st).bind fun a => knowT T q a.1 a.2
  | Nomm.n10 ax don rec, sub, st =>
    (knowT T don sub st).bind fun dn =>
    (knowT T rec sub dn.2).bind fun rc =>
    (So.darn rc.1.sock ax dn.1.sock).map fun s => (⟨s, Pi.edit rc.1.src ax dn.1.src⟩, rc.2)
  | Nomm.n11s _ q _, sub, st => knowT T q sub st
  | Nomm.n11d _ h q _, sub, st => (knowT T h sub st).bind fun hh => knowT T q sub hh.2
  | Nomm.n12 p q, sub, st =>
    (knowT T p sub st).bind fun a => (knowT T q sub a.2).map fun b => (Anno.dunno, b.2)
  | Nomm.mean p b q _ _, sub, st =>
    (knowT T p sub st).bind fun pp => knowT T q sub ((b, pp.1.sock) :: pp.2)

/-- The table of `+know` with `dat`: the datum's product patched for the
site sock. -/
def datTab (dat : Bell → Option Datum) : PTab :=
  fun _ b k => (dat b).map fun d => patchProd d.prod d.map k

/-- **`+know` without folding is the `knowT` walk with `datTab`.** -/
theorem knowT_datTab (dat : Bell → Option Datum) :
    ∀ (nm : Nomm) (sub : Anno) (st : List Site),
      (knowGo false dat idc nm sub st).map (fun r => (r.1.2, r.2)) = knowT (datTab dat) nm sub st := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1]
    | some l =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub l.2 with
      | none => simp [knowGo, h1, h2]
      | some r => simp [knowGo, h1, h2]
  | n0 p =>
    intro sub st
    by_cases h0 : p = 0
    · subst h0; simp [knowGo, knowT]
    · by_cases h1 : p = 1
      · subst h1; simp [knowGo, knowT]
      · simp only [knowGo, knowT, if_neg h0, if_neg h1]
        cases So.pull sub.sock p <;> simp
  | n1 p => intro sub st; simp [knowGo, knowT]
  | n2 p q info ihp ihq =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1]
    | some s =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub s.2 with
      | none => simp [knowGo, h1, h2]
      | some f =>
        cases info with
        | none => simp [knowGo, h1, h2]
        | some i =>
          obtain ⟨b, mk⟩ := i
          cases hd : dat b <;> simp [knowGo, h1, h2, idc, datTab, callProd, hd]
  | n3 p ih =>
    intro sub st
    rw [knowT, ← ih]
    cases h1 : knowGo false dat idc p sub st <;> simp [knowGo, h1]
  | n4 p ih =>
    intro sub st
    rw [knowT, ← ih]
    cases h1 : knowGo false dat idc p sub st <;> simp [knowGo, h1]
  | n5 p q ihp ihq =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub a.2 <;> simp [knowGo, h1, h2]
  | n6 p q r ihp ihq ihr =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub a.2 with
      | none => simp [knowGo, h1, h2]
      | some b =>
        simp only [Option.map_some, Option.bind_some]
        rw [← ihr]
        cases h3 : knowGo false dat idc r sub b.2 <;> simp [knowGo, h1, h2, h3]
  | n7 p q ihp ihq =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q a.1.2 a.2 <;> simp [knowGo, h1, h2]
  | n10 ax v q ihv ihq =>
    intro sub st
    rw [knowT, ← ihv]
    cases h1 : knowGo false dat idc v sub st with
    | none => simp [knowGo, h1]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub a.2 with
      | none => simp [knowGo, h1, h2]
      | some b =>
        cases h3 : So.darn b.1.2.sock ax a.1.2.sock <;> simp [knowGo, h1, h2, h3]
  | n11s tag q body ihq =>
    intro sub st
    rw [knowT, ← ihq]
    cases h1 : knowGo false dat idc q sub st <;> simp [knowGo, h1]
  | n11d tag hh q body ihh ihq =>
    intro sub st
    rw [knowT, ← ihh]
    cases h1 : knowGo false dat idc hh sub st with
    | none => simp [knowGo, h1]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub a.2 <;> simp [knowGo, h1, h2]
  | n12 p q ihp ihq =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub a.2 <;> simp [knowGo, h1, h2]
  | mean p b q body k ihp ihq =>
    intro sub st
    rw [knowT, ← ihp]
    cases h1 : knowGo false dat idc p sub st with
    | none => simp [knowGo, h1, idc]
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      rw [← ihq]
      cases h2 : knowGo false dat idc q sub ((b, a.1.2.sock) :: a.2) <;> simp [knowGo, h1, h2, idc]

/-- **The sites of `+know` without folding are those of `knowT` with
`datTab`.** -/
theorem know_sites_knowT {dat : Bell → Option Datum} {nm : Nomm} {sub : Sock} {out : Nomm}
    {sites : List Site} (h : know false nm sub dat idc = some (out, sites)) :
    ∃ a, knowT (datTab dat) nm ⟨sub, A 1⟩ [] = some (a, sites) := by
  unfold know at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, he⟩ := h
  simp only [Prod.mk.injEq] at he
  refine ⟨r.1.2, ?_⟩
  rw [← knowT_datTab, hr, ← he.2]
  rfl

/-! ## The two statements and `SiteCover` -/

variable {M : Type → Type → Type} [Treap M]

/-- A site sock `ka` that `k` knows no less than on the cape of the callee's
code requirement. -/
def CoverAt (c : Bell) (ka k : Sock) : Prop := ∀ cl dl, c.less = Sock.mk cl dl → Sub k (Ca.app cl ka)

/-- **The replayed walk of a datum**: a `knowT` walk of its nomm under the
identity's subject sock `more`, whose code requirement is `+app:ca` of
`want` and `more`. -/
def ReplayWalk (cur : Bell) (d : Datum) (T : PTab) (more : Sock) (want : Cape) (r : Anno × List Site) : Prop :=
  cur.less = Ca.app want more ∧ knowT T d.nomm ⟨more, A 1⟩ [] = some r

/-- **`Replay`**: every datum has a replayed walk whose sites, but the
root's, have socks with a noun that provide their callees' code
requirements. -/
def Replay (E : BEnv M) : Prop :=
  ∀ cur d, E.dat cur = some d → ∃ T more want r, ReplayWalk cur d T more want r ∧
    ∀ c ka, (c, ka) ∈ r.2 → c ≠ E.root → (∃ y, Fits ka y) ∧ Sub ka c.less

/-- **`Compare`**: on every replayed walk, every site of `+know` without
folding under `less.cur` has a site of the same callee in the replayed walk
that it covers on the callee's code requirement's cape. -/
def Compare (E : BEnv M) : Prop :=
  ∀ cur d T more want rA rB, E.dat cur = some d → ReplayWalk cur d T more want rA →
    knowT (datTab E.dat) d.nomm ⟨cur.less, A 1⟩ [] = some rB →
    ∀ c k, (c, k) ∈ rB.2 → c ≠ E.root → ∃ ka, (c, ka) ∈ rA.2 ∧ CoverAt c ka k

omit [Treap M] in
/-- **`SiteCover` from `Replay` and `Compare`.** -/
theorem siteCover_of {E : BEnv M} (hr : Replay E) (hc : Compare E) : SiteCover E := by
  intro cur d out sites hd hk c k hck hcr
  obtain ⟨T, more, want, rA, hw, hA⟩ := hr cur d hd
  obtain ⟨a, hB⟩ := know_sites_knowT hk
  obtain ⟨ka, hka, hcov⟩ := hc cur d T more want rA (a, sites) hd hw hB c k hck hcr
  obtain ⟨hy, hs⟩ := hA c ka hka hcr
  exact ⟨ka, hy, hs, hcov⟩

omit [Treap M] in
/-- **`LessProvidesNF` from `Replay` and `Compare`.** -/
theorem lessProvidesNF_of_replay {E : BEnv M} (hr : Replay E) (hc : Compare E) : LessProvidesNF E :=
  lessProvidesNF_of_cover (siteCover_of hr hc)

/-! ## `ProdSame` with maps

`tools/hoon/prodmaps.hoon` (runhoon.sh, 2026-11-24), on the ten pokes of
`prodsites.hoon`, at the same 490 site socks and 6,848 comparisons: the maps
of every two identities of one code bell, patched for the site sock, are
equal as nouns (0 differ, so also 0 differ on the parts the product knows),
including the 6,610 comparisons in groups of two or more identities.  At the
230 callee identities (the analysis' site socks of new identities), the
product the analysis used for the call (the callee's datum, not patched)
has the nouns and the map of itself patched for its own subject sock, and
of `dat`'s datum patched for that sock (0 failures each).  So the weakest
clause the comparison needs, equal maps, holds in its strongest form. -/

/-- **Two identities of one code bell have the same patched products and
the same maps.** -/
def ProdSameM (g : Callgraph M) : Prop :=
  ∀ (id1 id2 : Ident) (d1 d2 : FDatum M), Treap.get g id1 = some d1 → Treap.get g id2 = some d2 →
    id1.2 = id2.2 → d1.less = d2.less → ∀ k, Sub k d1.less →
      Sub (patchProd d1.prod d1.map k).sock (patchProd d2.prod d2.map k).sock ∧
      (patchProd d1.prod d1.map k).src = (patchProd d2.prod d2.map k).src

theorem prodSame_of_M {g : Callgraph M} (h : ProdSameM g) : ProdSame g :=
  fun id1 id2 d1 d2 h1 h2 hf hl k hk => (h id1 id2 d1 d2 h1 h2 hf hl k hk).1

end Bake

end SkaModel
end Formalization
