import lemmas.Ska.AnnotSDet

/-!
# `DetK` and `KC` on the real compiler (track Q, `InvBSR` step 1, README Gaps 27)

`tools/hoon/annots3.hoon` (`runhoon.sh annots3.hoon 600`, about 30 s) runs the
pokes of `annots.hoon` (28), `annots2.hoon` (4) and `hinttab.hoon` (16) in one
state and walks the ANALYSIS's nomm of each of the 63 datums of
`memo.long-ska` from its code requirement `less-code` with the analysis's
product rules (`+fol-loop`: `%0` pull/slot, a cons the constant if both sides
are safe, else knit; `%6` `+double-int`; `%7` `q` on `p`'s product; `%10`
darn/edit; hints the body's; a direct call the memo's patched product; a call
with a void subject or formula void).  On 2026-11-28:

* 47 direct calls with no memo key, `DetK` of the formula part at the call's
  subject sock holds at all 47 (45 of them pass `+safe-fol-fol` in the
  analysis, 32 are not literals: the analysis folds nothing);
* 21 `%6`, none with a void branch and no void product on a subject that is
  not void (a finished callee's void product becomes `[| ~]`, `+pop`);
* with every direct call void (the first pass, where a callee in progress has
  the bunt entry, void product): 10 void branches of a `%6` and 95 nomms with
  a void product on a subject that is not void, all `KC`.

So neither clause is too strong for real code.  Frozen here: `detKB` and
`kcB`, the checkers the driver runs (`detKB_sound`, `kcB_iff`), on the
formula parts of `%j1` and `%j2` (`annots2.hoon`: the read `[0 2]` that the
bake keeps, and `[6 [5 [1 0] [1 0]] [0 2] [0 2]]`, which fails
`+safe-fol-fol` in the analysis), the recursive call of
`r = [6 [3 0 3] [9 2 10 [3 0 7] 0 1] 0 3]`, the void branches of `r` and of
the loop of `%j3`, and the sock that knows nothing (a read is not `DetK`
there: the walk with an empty memo, which the driver's first version had).
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock

/-- `KC` as the driver tests it. -/
def kcB : Nomm → Bool
  | Nomm.n0 _ => false
  | Nomm.n1 _ => false
  | Nomm.n2 _ _ _ => true
  | Nomm.cons p q => kcB p || kcB q
  | Nomm.n3 p => kcB p
  | Nomm.n4 p => kcB p
  | Nomm.n5 p q => kcB p || kcB q
  | Nomm.n6 p q r => kcB p || (kcB q && kcB r)
  | Nomm.n7 p q => kcB p || kcB q
  | Nomm.n10 _ p q => kcB p || kcB q
  | Nomm.n11s _ q _ => kcB q
  | Nomm.n11d _ p q _ => kcB p || kcB q
  | Nomm.mean p _ q _ _ => kcB p || kcB q
  | Nomm.n12 p q => kcB p || kcB q

theorem kcB_iff : ∀ n, kcB n = true ↔ KC n
  | Nomm.n0 _ => by simp [kcB, KC]
  | Nomm.n1 _ => by simp [kcB, KC]
  | Nomm.n2 _ _ _ => by simp [kcB, KC]
  | Nomm.cons p q => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]
  | Nomm.n3 p => by simp only [kcB, KC, kcB_iff p]
  | Nomm.n4 p => by simp only [kcB, KC, kcB_iff p]
  | Nomm.n5 p q => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]
  | Nomm.n6 p q r => by
    simp only [kcB, KC, Bool.or_eq_true, Bool.and_eq_true, kcB_iff p, kcB_iff q, kcB_iff r]
  | Nomm.n7 p q => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]
  | Nomm.n10 _ p q => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]
  | Nomm.n11s _ q _ => by simp only [kcB, KC, kcB_iff q]
  | Nomm.n11d _ p q _ => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]
  | Nomm.mean p _ q _ _ => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]
  | Nomm.n12 p q => by simp only [kcB, KC, Bool.or_eq_true, kcB_iff p, kcB_iff q]

/-- `DetK` on the nouns of a sock, as the driver tests it: a read needs its
axis in every noun of the sock (`sockHas`, the test `node` of
`annots.hoon`). -/
def detKB (s : Sock) : Nomm → Bool
  | Nomm.n0 a => sockHas s a
  | Nomm.n1 _ => true
  | Nomm.cons p q => detKB s p && detKB s q
  | Nomm.n11s _ q _ => detKB s q
  | Nomm.n11d _ _ q _ => detKB s q
  | Nomm.mean _ _ q _ _ => detKB s q
  | Nomm.n6 _ q r => (detKB s q || kcB q) && (detKB s r || kcB r)
  | Nomm.n2 _ _ _ => true
  | Nomm.n3 _ => true
  | Nomm.n4 _ => true
  | Nomm.n5 _ _ => true
  | Nomm.n7 _ _ => true
  | Nomm.n10 _ _ _ => true
  | Nomm.n12 _ _ => true

theorem detKB_sound {s : Sock} : ∀ (n : Nomm), detKB s n = true → DetK (Fits s) n
  | Nomm.n0 _, h => sockHas_axisIn h
  | Nomm.n1 _, _ => trivial
  | Nomm.cons p q, h => by
    simp only [detKB, Bool.and_eq_true] at h
    exact ⟨detKB_sound p h.1, detKB_sound q h.2⟩
  | Nomm.n11s _ q _, h => detKB_sound q h
  | Nomm.n11d _ _ q _, h => detKB_sound q h
  | Nomm.mean _ _ q _ _, h => detKB_sound q h
  | Nomm.n6 _ q r, h => by
    simp only [detKB, Bool.and_eq_true, Bool.or_eq_true] at h
    refine ⟨?_, ?_⟩
    · rcases h.1 with d | k
      · exact Or.inl (detKB_sound q d)
      · exact Or.inr ((kcB_iff q).mp k)
    · rcases h.2 with d | k
      · exact Or.inl (detKB_sound r d)
      · exact Or.inr ((kcB_iff r).mp k)
  | Nomm.n2 _ _ _, _ | Nomm.n3 _, _ | Nomm.n4 _, _ | Nomm.n5 _ _, _ | Nomm.n7 _ _, _
  | Nomm.n10 _ _ _, _ | Nomm.n12 _ _, _ => trivial

/-! ## Cases of `annots3.hoon` -/

/-- `v = [2 [0 1] [1 [0 3]]]` of `annots2.hoon`. -/
def chkV : Noun := C (A 2) (C (C (A 0) (A 1)) (C (A 1) (C (A 0) (A 3))))

/-- The subject sock at the calls of `%j1` and `%j2`, from `less-code`:
`[[& |] [v 0]]`. -/
def chkSJ : Sock := Sock.mk (Cape.cell Cape.yes Cape.no) (C chkV (A 0))

/-- The formula part of `%j2` in the analysis. -/
def chkQ2 : Nomm := Nomm.n6 (Nomm.n5 (Nomm.n1 (A 0)) (Nomm.n1 (A 0))) (Nomm.n0 2) (Nomm.n0 2)

#guard detKB chkSJ (Nomm.n0 2)
#guard safeFolFol (Nomm.n0 2)
#guard detKB chkSJ chkQ2
#guard !safeFolFol chkQ2

/-- `r = [6 [3 0 3] [9 2 10 [3 0 7] 0 1] 0 3]`. -/
def chkR : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 3) (C (A 0) (A 7)))
    (C (A 0) (A 1)))))) (C (A 0) (A 3))))

/-- `r`'s code requirement `[[& |] [r 0]]`. -/
def chkSR : Sock := Sock.mk (Cape.cell Cape.yes Cape.no) (C chkR (A 0))

/-- `r`'s yes branch: the recursive call, void in the first pass. -/
def chkRYes : Nomm :=
  Nomm.n7 (Nomm.n10 3 (Nomm.n0 7) (Nomm.n0 1))
    (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) (some (⟨chkSR, chkR⟩, none)))

/-- The loop of `%j3`: `[8 [1 [9 2 0 1]] [9 2 0 1]]`, void in the first pass. -/
def chkL : Noun := C (A 9) (C (A 2) (C (A 0) (A 1)))

def chkLoop : Nomm :=
  Nomm.n7 (Nomm.cons (Nomm.n1 chkL) (Nomm.n0 1))
    (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2)
      (some (⟨Sock.mk (Cape.cell Cape.yes Cape.no) (C chkL (A 0)), chkL⟩, none))))

#guard detKB chkSR (Nomm.n0 2)
#guard kcB chkRYes
#guard kcB chkLoop
#guard detKB chkSR (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) chkRYes (Nomm.n0 3))
#guard !detKB Sock.dunno (Nomm.n0 2)
#guard !kcB (Nomm.n0 2)

end AnnotSF
end SkaModel
end Formalization
