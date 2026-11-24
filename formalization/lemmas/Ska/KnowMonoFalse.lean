import lemmas.Ska.SitesMeet

/-!
# `KnowMono` does not follow from the sock operations

**Obsolete for good** since the guard of commit 8f2162e in `+bake-graph`:
`bakes_ok` (`BakeImp.lean`) needs no `SitesMeet`, of whose route `KnowMono`
was a part.

`KnowMono` (`SitesMeet.lean`) asks that each site of `+know` under a bake
`s` below `less.cur` knows at least what a site of the same callee knows
under `less.cur`.  This file shows that the model of `+know` alone does not
give it: for a nomm, a code requirement, a bake and one datum of a callee,
the site under the bake knows nothing (`|`) while the site under the code
requirement knows a head `7` (`knowMono_false`).  So a proof of `KnowMono`
has to use what the analysis puts in `dat` and in the nomm, or `KnowMono`
has to be weakened (see the end of this file).

The nomm is `[2 [6 [0 3] [0 2] [2 [0 1] [1 0 2]]] [1 0 3]]` with both calls
direct.  The callee `kmB` returns its subject's head (product `|+~`, with
provenance `2`).  The code requirement `less.cur` knows the head of the
subject's head (`7`), the bake knows the whole head (`[7 8]`).

1. Under the bake, the read `[0 2]` is fully known, so it folds to `[1 7 8]`
   with provenance `~`.  The call to `kmB` is patched for the subject: the
   same sock `&+[7 8]`, with provenance `2`.  `+double-int` of `[&+[7 8] ~]`
   and `[&+[7 8] 2]` sees two different annotations with capes `&` and atom
   provenances, and gives `[|+~ ~]`.  The outer site knows `|`.
2. Under `less.cur`, the read is not fully known and does not fold: it is
   `[[& |] [7 0]]` with provenance `2`, and so is the patched call.  The two
   are equal, `+double-int` keeps them, and the outer site knows `[& |]`
   `[7 0]`.

The fold drops provenance on one branch, the call keeps it on the other, and
the provenance test of `+double-int` then forgets a part that both branches
know alike.  The comment above `+bake-graph` in the Hoon describes the same
effect ("a join of branches that no longer fold, which may keep more").
`SitesMeet` itself is not refuted by this: the site under the bake knows
`|`, which meets every code requirement.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

set_option linter.unusedSimpArgs false

/-- The bake: the subject's head is the fully known `[7 8]`. -/
def kmS : Sock := Sock.mk (Cape.cell Cape.yes Cape.no) (C (C (A 7) (A 8)) (A 0))

/-- The code requirement: of the subject's head only its head `7` is known. -/
def kmL : Sock := Sock.mk (Cape.cell (Cape.cell Cape.yes Cape.no) Cape.no) (C (C (A 7) (A 0)) (A 0))

/-- The callee that returns its subject's head. -/
def kmB : Bell := ⟨Sock.dunno, C (A 0) (A 2)⟩

/-- The callee of the outer call. -/
def kmB2 : Bell := ⟨Sock.dunno, C (A 0) (A 3)⟩

/-- `[2 [6 [0 3] [0 2] [2 [0 1] [1 0 2]]] [1 0 3]]`, both calls direct. -/
def kmNomm : Nomm :=
  Nomm.n2 (Nomm.n6 (Nomm.n0 3) (Nomm.n0 2) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 kmB.fol) (some (kmB, none))))
    (Nomm.n1 kmB2.fol) (some (kmB2, none))

/-- The datum of `kmB`: its product is its subject's head. -/
def kmDB : Datum := ⟨Nomm.n0 2, Sock.dunno, Cape.no, Cape.no, Sock.dunno, A 2⟩

/-- Under the bake: the read `[0 2]` folds (provenance `~`), the call keeps
provenance `2`, so `+double-int` gives `|`. -/
theorem km_know_bake (dat : Bell → Option Datum) (hB : dat kmB = some kmDB) :
    know true kmNomm kmS dat idc = some
      (Nomm.n2 (Nomm.n6 (Nomm.n0 3) (Nomm.n1 (C (A 7) (A 8)))
          (Nomm.n2 (Nomm.n0 1) (Nomm.n1 kmB.fol) (some (kmB, none))))
        (Nomm.n1 kmB2.fol) (some (kmB2, none)),
       [(kmB2, Sock.dunno), (kmB, kmS)]) := by
  have hB' : dat ⟨Sock.mk Cape.no (A 0), C (A 0) (A 2)⟩ = some kmDB := hB
  simp [know, knowGo, kmNomm, hB', kmS, So.pull, So.pullLoop, known, Ca.all, cap, mas, Pi.slot, peg, idc,
    patchProd, Pi.compose, Pi.composeLoop, doubleInt_self, doubleInt_mk, Sock.dunno, Cape.isCellB, isCellN, Anno.dunno, kmB, kmB2, kmDB]

/-- Under the code requirement: neither the read nor the call folds, both
are `[[& |] [7 0]]` with provenance `2`, and `+double-int` keeps it. -/
theorem km_know_less (dat : Bell → Option Datum) (hB : dat kmB = some kmDB) :
    know true kmNomm kmL dat idc = some
      (kmNomm, [(kmB2, Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 7) (A 0))), (kmB, kmL)]) := by
  have hB' : dat ⟨Sock.mk Cape.no (A 0), C (A 0) (A 2)⟩ = some kmDB := hB
  simp [know, knowGo, kmNomm, hB', kmL, So.pull, So.pullLoop, known, Ca.all, cap, mas, Pi.slot, peg, idc,
    patchProd, Pi.compose, Pi.composeLoop, doubleInt_self, doubleInt_mk, Sock.dunno, Cape.isCellB, isCellN, Anno.dunno, kmB, kmB2, kmDB]

/-- **`KnowMono` fails** for every environment that folds and has these
datums: a code bell `cur` with the nomm `kmNomm` and the code requirement
`kmL`, and the callee `kmB` returning its subject's head. -/
theorem knowMono_false {M : Type → Type → Type} [Treap M] (E : BEnv M) (cur : Bell) (d : Datum)
    (hf : E.fold = true) (hc : cur.less = kmL) (hd : E.dat cur = some d) (hn : d.nomm = kmNomm)
    (hB : E.dat kmB = some kmDB) : ¬ KnowMono E := by
  intro h
  have hsub : Sub kmS cur.less := by
    rw [hc]
    intro x hx
    simp only [kmS, kmL, Fits, FitsCape, Cape.isNo, Bool.false_and, Bool.false_eq_true, false_or,
      Bool.and_true, Bool.and_false] at hx ⊢
    obtain ⟨dh, dt, nh, nt, hd1, rfl, hh, -⟩ := hx
    cases hd1
    subst hh
    exact ⟨_, _, _, _, rfl, rfl, ⟨_, _, _, _, rfl, rfl, rfl, trivial⟩, trivial⟩
  have hinh : ∃ y, Fits kmS y := ⟨C (C (A 7) (A 8)) (A 0), by
    simp [kmS, Fits, FitsCape]⟩
  have hk := km_know_bake E.dat hB
  rw [← hf, ← hn] at hk
  obtain ⟨out', sites', hk', hm⟩ := h cur d kmS _ _ hsub hinh hd hk
  rw [hc, hf, hn, km_know_less E.dat hB] at hk'
  cases hk'
  obtain ⟨k', hmem, hsk⟩ := hm kmB2 Sock.dunno (by simp)
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨-, rfl⟩ | ⟨hb, -⟩
  · have := hsk (A 0) trivial
    simp [Fits, FitsCape, Cape.isNo] at this
  · simp [kmB, kmB2] at hb

end Bake
end SkaModel
end Formalization
