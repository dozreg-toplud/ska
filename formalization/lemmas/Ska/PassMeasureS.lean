import lemmas.Ska.PassMeasureT

/-!
# The last two components of the measure: `seek` as numbers, `indi` (track F)

`runDatum_indi_seek` (`PassMeasureK.lean`): when `less-code`, the product
and the map stay, `indi` stays or becomes `+lack:ca (+msg-ca new old) dark`,
and with `indi` the same, `seek` stays or becomes `+msg-ca new old`.

`+msg-ca` makes a cell only where both capes are cells and `&` wherever they
disagree otherwise, so a change of `seek` by it lowers the pair (cells of the
cape, `|` leaves of the cape) lexicographically (`msgCa_lex`): `seek` changes
finitely often while the first four components stay (`runDatum_seek_lex`).

`indi` is not bounded that way (`+lack:ca` with `dark` can make cells: `|`
under a `dark` of `[& |]` becomes `&` by `+msg-ca`, then `[| &]` by
`+lack:ca`).  What is proved: `+lack:ca` with a normal `dark` is idempotent
(`lack_idem`), so an `indi` that `+run` wrote is its own `+lack:ca` of
`dark`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## `seek` -/

/-- The cells of a cape. -/
def cellsC : Cape → Nat
  | Cape.cell a b => cellsC a + cellsC b + 1
  | _ => 0

/-- The `|` leaves of a cape. -/
def nosC : Cape → Nat
  | Cape.no => 1
  | Cape.cell a b => nosC a + nosC b
  | Cape.yes => 0

theorem msgCa_cases (a b : Cape) :
    (msgCa a b = a ∧ a = b) ∨
    (∃ ah aT bh bT, a = Cape.cell ah aT ∧ b = Cape.cell bh bT ∧ a ≠ b ∧
      msgCa a b = Cape.cell (msgCa ah bh) (msgCa aT bT)) ∨
    (a ≠ b ∧ msgCa a b = Cape.yes) := by
  by_cases e : a = b
  · left; subst e; refine ⟨?_, rfl⟩; rw [msgCa.eq_def]; simp
  · right
    cases a with
    | cell ah aT =>
      cases b with
      | cell bh bT =>
        left; refine ⟨ah, aT, bh, bT, rfl, rfl, e, ?_⟩
        rw [msgCa.eq_def]; simp only [if_neg e]; try rfl
      | no => right; refine ⟨e, ?_⟩; rw [msgCa.eq_def]; simp only [if_neg e]; try rfl
      | yes => right; refine ⟨e, ?_⟩; rw [msgCa.eq_def]; simp only [if_neg e]; try rfl
    | no => right; refine ⟨e, ?_⟩; rw [msgCa.eq_def]; simp only [if_neg e]; try rfl
    | yes => right; refine ⟨e, ?_⟩; rw [msgCa.eq_def]; simp only [if_neg e]; try rfl

/-- **A change of `+msg-ca` lowers (cells, `|` leaves) lexicographically.** -/
theorem msgCa_lex : ∀ (b a : Cape), msgCa a b ≠ b →
    cellsC (msgCa a b) < cellsC b ∨ (cellsC (msgCa a b) = cellsC b ∧ nosC (msgCa a b) < nosC b) := by
  intro b
  induction b with
  | no =>
    intro a h
    rcases msgCa_cases a Cape.no with ⟨e1, e2⟩ | ⟨_, _, _, _, _, e, _⟩ | ⟨_, e⟩
    · exact absurd (e1.trans e2) h
    · cases e
    · rw [e]; right; exact ⟨rfl, by simp [nosC]⟩
  | yes =>
    intro a h
    rcases msgCa_cases a Cape.yes with ⟨e1, e2⟩ | ⟨_, _, _, _, _, e, _⟩ | ⟨_, e⟩
    · exact absurd (e1.trans e2) h
    · cases e
    · exact absurd e h
  | cell bh bT ih1 ih2 =>
    intro a h
    rcases msgCa_cases a (Cape.cell bh bT) with ⟨e1, e2⟩ | ⟨ah, aT, bh', bT', rfl, e, hne, hm⟩ | ⟨_, e⟩
    · exact absurd (e1.trans e2) h
    · cases e
      rw [hm]
      rw [hm] at h
      have p1 : msgCa ah bh = bh ∨ cellsC (msgCa ah bh) < cellsC bh ∨
          (cellsC (msgCa ah bh) = cellsC bh ∧ nosC (msgCa ah bh) < nosC bh) := by
        by_cases q : msgCa ah bh = bh
        · exact Or.inl q
        · exact Or.inr (ih1 ah q)
      have p2 : msgCa aT bT = bT ∨ cellsC (msgCa aT bT) < cellsC bT ∨
          (cellsC (msgCa aT bT) = cellsC bT ∧ nosC (msgCa aT bT) < nosC bT) := by
        by_cases q : msgCa aT bT = bT
        · exact Or.inl q
        · exact Or.inr (ih2 aT q)
      simp only [cellsC, nosC]
      rcases p1 with q1 | q1 | ⟨q1, q1'⟩ <;> rcases p2 with q2 | q2 | ⟨q2, q2'⟩
      · exact absurd (by rw [q1, q2]) h
      all_goals first
        | (rw [q1]; omega)
        | (rw [q2]; omega)
        | omega
    · rw [e]; left; simp [cellsC]

/-- **`seek` changes finitely often while the first four components stay**:
when `less-code`, the product, the map and `indi` stay, `seek` stays or the
pair (cells, `|` leaves) of its cape falls lexicographically. -/
theorem runDatum_seek_lex (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (hl : (runDatum moved bus out gen' old).1.less = old.less)
    (hp : (runDatum moved bus out gen' old).1.prod = old.prod)
    (hm : (runDatum moved bus out gen' old).1.map = old.map)
    (hi : (runDatum moved bus out gen' old).1.indi = old.indi) :
    let s := (runDatum moved bus out gen' old).1.seek
    s = old.seek ∨ cellsC s < cellsC old.seek ∨ (cellsC s = cellsC old.seek ∧ nosC s < nosC old.seek) := by
  intro s
  rcases (runDatum_indi_seek moved bus out gen' old hl hp hm).2 hi with e | ⟨e, _⟩
  · exact Or.inl e
  · by_cases q : s = old.seek
    · exact Or.inl q
    · right
      have q' : msgCa gen'.seek old.seek ≠ old.seek := by
        intro c; exact q (e.trans c)
      have := msgCa_lex old.seek gen'.seek q'
      show cellsC s < cellsC old.seek ∨ (cellsC s = cellsC old.seek ∧ nosC s < nosC old.seek)
      rw [show s = msgCa gen'.seek old.seek from e]
      exact this

/-! ## `indi` -/

theorem lack_no_left (b : Cape) : Ca.lack Cape.no b = Cape.no := by
  cases b <;> rfl

theorem lack_yes_right (a : Cape) : Ca.lack a Cape.yes = Cape.no := by
  cases a <;> rfl

theorem lack_no_right (a : Cape) : Ca.lack a Cape.no = a := by
  cases a <;> rfl

theorem lack_cell_right (a bh bT : Cape) (ha : a ≠ Cape.no) :
    Ca.lack a (Cape.cell bh bT) =
      if a = Cape.cell bh bT then Cape.no else Ca.con (Ca.lack (Ca.hed a) bh) (Ca.lack (Ca.tel a) bT) := by
  cases a with
  | no => exact absurd rfl ha
  | yes => rfl
  | cell _ _ => rfl

/-- `+lack:ca` gives back a normal `b` only if `b` is `|`. -/
theorem lack_eq_self : ∀ (b : Cape), NormCape b → ∀ a, Ca.lack a b = b → b = Cape.no := by
  intro b
  induction b with
  | no => intros; rfl
  | yes => intro _ a h; rw [lack_yes_right] at h; cases h
  | cell bh bT ih1 ih2 =>
    intro hn a h
    by_cases ha : a = Cape.no
    · subst ha; rw [lack_no_left] at h; cases h
    rw [lack_cell_right _ _ _ ha] at h
    split at h
    · cases h
    · unfold Ca.con at h
      split at h
      · cases h
      · simp only [Cape.cell.injEq] at h
        have e1 := ih1 hn.2.1 _ h.1
        have e2 := ih2 hn.2.2 _ h.2
        subst e1; subst e2
        exact absurd hn.1 (by decide)

/-- **`+lack:ca` of a normal `dark` is idempotent**, so an `indi` that `+run`
wrote (always a `+lack:ca` of `dark`) is its own `+lack:ca` of `dark`. -/
theorem lack_idem : ∀ (d : Cape), NormCape d → ∀ y, Ca.lack (Ca.lack y d) d = Ca.lack y d := by
  intro d
  induction d with
  | no => intro _ y; rw [lack_no_right, lack_no_right]
  | yes => intro _ y; rw [lack_yes_right, lack_yes_right]
  | cell dh dt ih1 ih2 =>
    intro hn y
    by_cases hy : y = Cape.no
    · subst hy; rw [lack_no_left, lack_no_left]
    rw [lack_cell_right _ _ _ hy]
    by_cases e : y = Cape.cell dh dt
    · rw [if_pos e, lack_no_left]
    rw [if_neg e]
    have i1 := ih1 hn.2.1 (Ca.hed y)
    have i2 := ih2 hn.2.2 (Ca.tel y)
    generalize hp : Ca.lack (Ca.hed y) dh = p at i1 ⊢
    generalize hq : Ca.lack (Ca.tel y) dt = q at i2 ⊢
    unfold Ca.con
    split
    · exact lack_no_left _
    · rename_i hc
      rw [lack_cell_right _ _ _ (by intro c; cases c)]
      have hne : Cape.cell p q ≠ Cape.cell dh dt := by
        intro c
        simp only [Cape.cell.injEq] at c
        have e1 := lack_eq_self dh hn.2.1 _ (hp.trans c.1)
        have e2 := lack_eq_self dt hn.2.2 _ (hq.trans c.2)
        subst e1; subst e2
        exact absurd hn.1 (by decide)
      rw [if_neg hne]
      show Ca.con (Ca.lack p dh) (Ca.lack q dt) = _
      rw [i1, i2]
      unfold Ca.con; rw [if_neg hc]

/-- **The `indi` of an entry after a run is a `+lack:ca` of `dark`** (both
branches of `+run`), so on a tidy `bus` it is fixed by `+lack:ca` of `dark`. -/
theorem runDatum_indi_lack (moved : Bool) {bus : Sock} (out : FolOut) (gen' : Gen) (old : Datum)
    (hb : Tidy bus) :
    Ca.lack (runDatum moved bus out gen' old).1.indi (darkOf bus) = (runDatum moved bus out gen' old).1.indi := by
  have hn : NormCape (darkOf bus) := by
    cases bus with
    | void => trivial
    | mk c d => exact tidyC_norm c d hb
  simp only [runDatum]
  split
  · exact lack_idem _ hn _
  · exact lack_idem _ hn _

end SkaModel
end Formalization
