import lemmas.Ska.SitesMeetFalse

/-!
# A miscompile: two code bells share a variant key

`tools/hoon/collide.hoon` (runhoon.sh, 2026-11-24) runs two pokes on `&+lib`
and compares `+eval-top` with `+mock` on the second formula.

1. Poke 1 is `bakeDropWitness` (`SitesMeetFalse.lean`).  It leaves `H`'s
   code bell `c1 = [witnessLessH H]` (axis `4` is `[1 7]`) with the variant
   `v = [witnessSiteH H]` (axis `4` is `[3 0]`), from a site that follows a
   call that never returns, and the table entry of `v` is the nomm
   `[7 [0 1] [1 7]]`, which returns `7` on every subject.
2. Poke 2 is `collideFol2 x` with `x = !=((dec 40))` against the library:
   `[[[3 0] 5] (dec 40)]`, then `H` on it.  The analysis cannot compute the
   product of `(dec 40)` (its recursion is generalized by `%he`), so `H`'s
   new code bell is `c2 = [collideLessH2 H]` (axis `4` is `[3 0]`) and its
   only site knows `witnessSiteH`.  `+uni-sock` of the two is `witnessSiteH`
   again (`collide_same_bake`), so the variant of `c2` has the key `v`.
   `new-code` skips a key that `code.lon` has, so the table keeps `c1`'s
   nomm under `v`, and `vars.lon` lists `v` under `c1` and `c2`
   (`tools/hoon/collide-vars.hoon` prints both, with the one nomm).
3. The live call of `c2` names `v`, so the compiled code returns `[%0 7]`,
   while `+mink` crashes (`[3 0]` has an atom operand): `+eval-top` says
   `[%0 p=7]`, `+mock` says `[%2 p=~]`.  The second formula alone agrees.

So the compiler is wrong, not only the invariant `BakesImply`.  A variant is
keyed by `[bake fol]`, and its nomm stands for the formula only on the
subjects of its bake and of its own code bell's code requirement
(`variant_annot`).  Once a bake need not lie under its code requirement, two
code bells of one formula can bake to one sock, and the second runs the
first's code on subjects outside the first's domain.  No invariant with a
domain per bell can repair this, since the key does not say which code bell
the entry belongs to.

Two fixes in the Hoon would restore a true invariant, and each needs a
change to the model of `+bake-graph` (`BakeGraph.lean`) before the proofs.

* The guard of the header of `PokeBake.lean`: in `+bake-graph`, use `less.c`
  as the bake when `(huge:so less.c bake)` fails.  Then every bake lies under
  its code requirement, which is `BakesImply`, and `skaPokeB_sound` and
  `gap_of_meet` hold with `himp` discharged by construction.  `GoodSite` of
  `bakeLoop_sound` is already stated on the subjects of the callee's code
  requirement, so it survives the fallback (`bakeGuard_fits`: a subject of
  both the code requirement and the unguarded bake fits the guarded one).
  In the witness `H`'s dead variant would then be `c1` itself, and its site
  is dead, so `Annot.direct` holds of it vacuously.
* Or key a variant by its code bell as well.  Then the domain design
  (`Fits less.v ∧ Fits less.c` per variant) is needed throughout, down to
  `Sound` of `Contract.lean`, whose `dire_code` for a dead variant's bell is
  false today on subjects of the bake outside `less.c`.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-- The code requirement of `H`'s code bell in the second poke of
`collide.hoon` on the real compiler: axis `4` is `[3 0]`. -/
def collideLessH2 : Sock :=
  Sock.mk (Cape.cell (Cape.cell Cape.yes Cape.no) Cape.no) (C (C (C (A 3) (A 0)) (A 0)) (A 0))

/-- `H = [2 [0 1] [0 4]]`. -/
def witnessH : Noun := C (A 2) (C (C (A 0) (A 1)) (C (A 0) (A 4)))

/-- The second formula of `collide.hoon`, with the formula `x` of
`(dec 40)` against the library as a parameter:
`[7 [[1 [[3 0] 5]] x] [2 [0 1] [1 H]]]`. -/
def collideFol2 (x : Noun) : Noun :=
  C (A 7) (C (C (C (A 1) (C (C (A 3) (A 0)) (A 5))) x)
    (C (A 2) (C (C (A 0) (A 1)) (C (A 1) witnessH))))

/-- **The two code bells of `H` bake to one sock**: `+uni-sock` of each code
requirement with the site's sock is the site's sock, which `+norm-sock`
keeps, so the two variants have the key `[witnessSiteH H]`. -/
theorem collide_same_bake :
    normSockH (uniSock witnessLessH witnessSiteH) = some witnessSiteH ∧
      normSockH (uniSock collideLessH2 witnessSiteH) = some witnessSiteH := by
  constructor <;>
  · repeat (rw [uniSock.eq_def]; simp (config := { decide := true }) [witnessLessH, witnessSiteH,
      collideLessH2, Ca.all, So.knit, So.hed, So.tel, normSockH, normCD, C])

/-- The bake of the first code bell shares no noun with its code
requirement, so its variant's nomm is right on no subject of the key
(`witness_no_meet`), and the live site of the second code bell runs it. -/
theorem collide_key_dead : ¬ ∃ y, Fits witnessLessH y ∧ Fits witnessSiteH y :=
  witness_no_meet

/-- **The guard keeps the domain**: with the fallback to `less.c` when
`huge:so less.c bake` fails, a subject that fits the code requirement and
the unguarded bake fits the guarded bake, and every subject of the guarded
bake fits the code requirement. -/
theorem bakeGuard_fits {lessc bake : Sock} {h : Bool} (hh : So.huge lessc bake = some h) :
    (∀ y, Fits lessc y → Fits bake y → Fits (if h then bake else lessc) y) ∧
      ∀ y, Fits (if h then bake else lessc) y → Fits lessc y := by
  cases h with
  | true =>
    exact ⟨fun _ _ hb => hb, fun y hy => huge_sound hh hy⟩
  | false =>
    exact ⟨fun _ hl _ => hl, fun _ hy => hy⟩

end Bake

end SkaModel
end Formalization
