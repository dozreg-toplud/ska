import lemmas.Ska.Prov

/-!
# Provenance along paths: what `+pi` does to the invariant

`ProvO` is the provenance invariant `ProvR` of `Prov.lean` for a part that
may be absent (`Option Noun`), so that it can be taken apart into head and
tail even where the product is an atom.  This file proves that the operations
of `fol-loop` on sock-annotated nouns keep it:

* paths: `sockAt` and `springAt` of an axis are `+pull:so` and `+slot:pi`
  (`pull_eq_sockAt`, `springAt_slot`), with `+peg` read as the concatenation
  of paths (`peg_eq_pegPath`);
* `provO_slot`: Nock 0, `+pull:so` with `+slot:pi`;
* `provO_knit`: a cons, `+knit:so` with `+cons:pi`, including the
  normalization `cons:pi ~ ~ = ~`;
* `provO_doubleInt_left`, `provO_doubleInt_right`: the join of the two
  branches of a Nock 6.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Paths -/

/-- The part of a part that may be absent, at a path. -/
def slotO (o : Option Noun) (π : List Bool) : Option Noun := o.bind (slotAtPath · π)

theorem slotO_nil (o : Option Noun) : slotO o [] = o := by
  cases o <;> simp [slotO, slotAtPath]

theorem slotO_some (p : Noun) (π : List Bool) : slotO (some p) π = slotAtPath p π := rfl

theorem slotAtPath_app : ∀ (n : Noun) (π ρ : List Bool),
    slotAtPath n (π ++ ρ) = slotO (slotAtPath n π) ρ
  | n, [], ρ => by simp [slotAtPath, slotO]
  | Noun.atom _, _ :: _, ρ => by simp [slotAtPath, slotO]
  | Noun.cell h _, false :: π, ρ => by simp only [List.cons_append, slotAtPath]; exact slotAtPath_app h π ρ
  | Noun.cell _ t, true :: π, ρ => by simp only [List.cons_append, slotAtPath]; exact slotAtPath_app t π ρ

theorem slotO_app (o : Option Noun) (π ρ : List Bool) : slotO o (π ++ ρ) = slotO (slotO o π) ρ := by
  cases o with
  | none => rfl
  | some n => exact slotAtPath_app n π ρ

theorem slotO_cons (o : Option Noun) (b : Bool) (π : List Bool) :
    slotO o (b :: π) = slotO (slotO o [b]) π := slotO_app o [b] π

theorem sockAt_app : ∀ (S : Sock) (π ρ : List Bool), sockAt S (π ++ ρ) = sockAt (sockAt S π) ρ
  | _, [], _ => rfl
  | S, false :: π, ρ => sockAt_app (So.hed S) π ρ
  | S, true :: π, ρ => sockAt_app (So.tel S) π ρ

theorem springAt_app : ∀ (σ : Noun) (π ρ : List Bool), springAt σ (π ++ ρ) = springAt (springAt σ π) ρ
  | _, [], _ => rfl
  | σ, false :: π, ρ => springAt_app (Pi.hed σ) π ρ
  | σ, true :: π, ρ => springAt_app (Pi.tel σ) π ρ

theorem springAt_zero : ∀ π, springAt (A 0) π = A 0
  | [] => rfl
  | false :: π => springAt_zero π
  | true :: π => springAt_zero π

theorem sockAt_void : ∀ π, sockAt Sock.void π = Sock.void
  | [] => rfl
  | false :: π => sockAt_void π
  | true :: π => sockAt_void π

theorem sockAt_dunno : ∀ π, sockAt Sock.dunno π = Sock.dunno
  | [] => rfl
  | false :: π => sockAt_dunno π
  | true :: π => sockAt_dunno π

theorem sockAt_ne_void : ∀ {S : Sock} (π : List Bool), S ≠ Sock.void → sockAt S π ≠ Sock.void
  | _, [], h => h
  | _, false :: π, h => sockAt_ne_void π (hed_ne_void h)
  | _, true :: π, h => sockAt_ne_void π (tel_ne_void h)

theorem sockAt_blank : ∀ {S : Sock} (π : List Bool), S.Blank → (sockAt S π).Blank
  | _, [], h => h
  | _, false :: π, h => sockAt_blank π (hed_blank h)
  | _, true :: π, h => sockAt_blank π (tel_blank h)

/-- What a sock says of a part that may be absent carries to the parts of
that part. -/
theorem fitsOpt_sockAt : ∀ {S : Sock} {o : Option Noun} (π : List Bool), FitsOpt S o →
    FitsOpt (sockAt S π) (slotO o π)
  | _, o, [], h => by rw [slotO_nil]; exact h
  | S, none, b :: π, h => by
      simp only [FitsOpt] at h
      have := sockAt_blank (b :: π) h
      simpa [slotO, FitsOpt] using this
  | S, some (Noun.atom k), b :: π, h => by
      have hb : (sockAt S [b]).Blank := by
        cases S with
        | void => exact absurd h id
        | mk c d =>
          obtain ⟨h1, h2⟩ := hed_tel_blank_of_atom (c := c) (d := d) (k := k) h
          cases b
          · exact h1
          · exact h2
      have := sockAt_blank π hb
      rw [← sockAt_app] at this
      simpa [slotO, slotAtPath, FitsOpt] using this
  | S, some (Noun.cell x y), false :: π, h => by
      have := fitsOpt_sockAt (S := So.hed S) (o := some x) π (hed_fits h)
      simpa [slotO, slotAtPath, sockAt] using this
  | S, some (Noun.cell x y), true :: π, h => by
      have := fitsOpt_sockAt (S := So.tel S) (o := some y) π (tel_fits h)
      simpa [slotO, slotAtPath, sockAt] using this

/-! ## Axes as paths -/

theorem axisPath_pos : ∀ a, 1 ≤ a → ∃ q, axisPath a = some q := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro h
  by_cases h1 : a = 1
  · subst h1; exact ⟨[], rfl⟩
  · obtain ⟨q, hq⟩ := ih (a / 2) (by omega) (by omega)
    exact ⟨q ++ [decide (a % 2 = 1)], by rw [axisPath_step a (by omega), hq]; rfl⟩

/-- The axis at the path `π` under the axis `p`: `+peg` one step at a time. -/
def pegPath : Nat → List Bool → Nat
  | p, [] => p
  | p, false :: π => pegPath (p * 2) π
  | p, true :: π => pegPath (p * 2 + 1) π

theorem pegPath_app : ∀ (p : Nat) (π : List Bool) (b : Bool),
    pegPath p (π ++ [b]) = (if b then pegPath p π * 2 + 1 else pegPath p π * 2)
  | p, [], false => rfl
  | p, [], true => rfl
  | p, false :: π, b => pegPath_app (p * 2) π b
  | p, true :: π, b => pegPath_app (p * 2 + 1) π b

theorem pegPath_pegPath : ∀ (p : Nat) (r s : List Bool), pegPath (pegPath p r) s = pegPath p (r ++ s)
  | _, [], _ => rfl
  | p, false :: r, s => pegPath_pegPath (p * 2) r s
  | p, true :: r, s => pegPath_pegPath (p * 2 + 1) r s

theorem pegPath_ne_zero :∀ (p : Nat) (π : List Bool), p ≠ 0 → pegPath p π ≠ 0
  | _, [], h => h
  | p, false :: π, _ => pegPath_ne_zero (p * 2) π (by omega)
  | p, true :: π, _ => pegPath_ne_zero (p * 2 + 1) π (by omega)

theorem axisPath_pegPath : ∀ (p : Nat) (π : List Bool) (q : List Bool), 1 ≤ p → axisPath p = some q →
    axisPath (pegPath p π) = some (q ++ π)
  | _, [], q, _, h => by simpa [pegPath] using h
  | p, false :: π, q, h1, h => by
      have h2 : axisPath (p * 2) = some (q ++ [false]) := by
        rw [axisPath_step (p * 2) (by omega)]
        have e1 : p * 2 / 2 = p := by omega
        have e2 : decide (p * 2 % 2 = 1) = false := decide_eq_false (by omega)
        rw [e1, e2, h]; rfl
      have := axisPath_pegPath (p * 2) π (q ++ [false]) (by omega) h2
      rw [List.append_assoc] at this
      exact this
  | p, true :: π, q, h1, h => by
      have h2 : axisPath (p * 2 + 1) = some (q ++ [true]) := by
        rw [axisPath_step (p * 2 + 1) (by omega)]
        have e1 : (p * 2 + 1) / 2 = p := by omega
        have e2 : decide ((p * 2 + 1) % 2 = 1) = true := decide_eq_true (by omega)
        rw [e1, e2, h]; rfl
      have := axisPath_pegPath (p * 2 + 1) π (q ++ [true]) (by omega) h2
      rw [List.append_assoc] at this
      exact this

/-- `+peg` is the concatenation of paths. -/
theorem peg_eq_pegPath : ∀ (b : Nat) (p : Nat) (q : List Bool), 1 ≤ b → axisPath b = some q →
    peg p b = pegPath p q := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
  intro p q hb hq
  by_cases h1 : b = 1
  · subst h1; simp only [axisPath_one, Option.some.injEq] at hq; subst hq; simp [peg, pegPath]
  · have h2 : 2 ≤ b := by omega
    rw [axisPath_step b h2] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    have ihb := ih (b / 2) (by omega) p q' (by omega) hq'
    rw [pegPath_app, ← ihb]
    match b, h2 with
    | 2, _ => simp [peg]
    | 3, _ => simp [peg]
    | b + 4, _ =>
      rw [peg]
      by_cases hm : (b + 4) % 2 = 1
      · simp only [hm, decide_true, if_true]; omega
      · simp only [hm, decide_false, if_false, Bool.false_eq_true]; omega

theorem springAt_atom : ∀ (p : Nat) (π : List Bool), p ≠ 0 → springAt (A p) π = A (pegPath p π)
  | _, [], _ => rfl
  | p, false :: π, h => by
      show springAt (Pi.hed (A p)) π = _
      have : Pi.hed (A p) = A (p * 2) := by
        unfold Pi.hed
        split
        · rename_i hh; cases hh; exact absurd rfl h
        · rename_i hh; cases hh; simp [peg]
        · rename_i hh; cases hh
      rw [this]; exact springAt_atom (p * 2) π (by omega)
  | p, true :: π, h => by
      show springAt (Pi.tel (A p)) π = _
      have : Pi.tel (A p) = A (p * 2 + 1) := by
        unfold Pi.tel
        split
        · rename_i hh; cases hh; exact absurd rfl h
        · rename_i hh; cases hh; simp [peg]
        · rename_i hh; cases hh
      rw [this]; exact springAt_atom (p * 2 + 1) π (by omega)

/-! ## `+pull:so` and `+slot:pi` along the path of an axis -/

theorem pullLoop_eq_sockAt : ∀ (a : Nat) (c : Cape) (d : Noun) (q : List Bool), 1 ≤ a →
    axisPath a = some q → So.pullLoop c d a = sockAt (Sock.mk c d) q := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro c d q h1 hq
  rw [So.pullLoop.eq_def]
  split
  · have : a = 1 := by omega
    subst this
    simp only [axisPath_one, Option.some.injEq] at hq
    subst hq; rfl
  · rename_i hax
    have h2 : 2 ≤ a := by omega
    rw [axisPath_cap a h2] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    have ih' := ih (mas a) (mas_lt a h2)
    have hm := mas_pos a h2
    by_cases hcn : c = Cape.no
    · subst hcn
      simp only [if_true]
      rcases cap_cases a h2 with hc | hc <;> simp [hc, sockAt, So.hed, So.tel, sockAt_dunno]
    · simp only [hcn, if_false]
      cases d with
      | atom k =>
        simp only
        rcases cap_cases a h2 with hc | hc <;> cases c <;>
          simp_all [sockAt, So.hed, So.tel, sockAt_dunno]
      | cell dh dt =>
        cases c with
        | no => exact absurd rfl hcn
        | yes =>
          simp only
          rcases cap_cases a h2 with hc | hc
          · simp only [hc, if_true, decide_false, Bool.false_eq_true]
            exact ih' _ _ _ hm hq'
          · simp only [hc, decide_true]
            rw [if_neg (by omega)]
            exact ih' _ _ _ hm hq'
        | cell ch ct =>
          simp only
          rcases cap_cases a h2 with hc | hc
          · simp only [hc, if_true, decide_false, Bool.false_eq_true]
            exact ih' _ _ _ hm hq'
          · simp only [hc, decide_true]
            rw [if_neg (by omega)]
            exact ih' _ _ _ hm hq'

/-- **`+pull:so` is the sock at the path of the axis.** -/
theorem pull_eq_sockAt {S : Sock} {a : Nat} {q : List Bool} (ha : 1 ≤ a) (hq : axisPath a = some q) :
    So.pull S a = some (sockAt S q) := by
  unfold So.pull
  rw [if_neg (by omega)]
  cases S with
  | void => simp [sockAt_void]
  | mk c d => simp only [Option.some.injEq]; exact pullLoop_eq_sockAt a c d q ha hq

theorem Pi.slot_atom {p b : Nat} (hp : p ≠ 0) (hb : b ≠ 1) : Pi.slot (A p) b = A (peg p b) := by
  rw [Pi.slot.eq_def, if_neg hb]
  cases p with
  | zero => exact absurd rfl hp
  | succ k => rfl

/-- **`+slot:pi` is the provenance at the path of the axis.** -/
theorem springAt_slot : ∀ (b : Nat) (σ : Noun) (q π : List Bool), 1 ≤ b → axisPath b = some q →
    springAt (Pi.slot σ b) π = springAt σ (q ++ π) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
  intro σ q π h1 hq
  by_cases hb1 : b = 1
  · subst hb1
    simp only [axisPath_one, Option.some.injEq] at hq
    subst hq
    rw [Pi.slot.eq_def]; simp
  have h2 : 2 ≤ b := by omega
  have hq0 := hq
  rw [axisPath_cap b h2] at hq
  obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
  cases σ with
  | atom p =>
    by_cases hp : p = 0
    · subst hp; rw [Pi.slot.eq_def, if_neg hb1]; simp [springAt_zero]
    · rw [Pi.slot_atom hp hb1, peg_eq_pegPath b p _ h1 hq0,
        springAt_atom _ _ (pegPath_ne_zero _ _ hp), springAt_atom _ _ hp, pegPath_pegPath]
  | cell h t =>
    rw [Pi.slot.eq_def, if_neg hb1]
    simp only
    rw [dif_neg (by omega)]
    have hm := mas_pos b h2
    rcases cap_cases b h2 with hc | hc
    · simp only [hc, if_true, decide_false, Bool.false_eq_true, List.cons_append]
      exact ih (mas b) (mas_lt b h2) h q' π hm hq'
    · simp only [hc, decide_true, List.cons_append]
      rw [if_neg (by omega)]
      exact ih (mas b) (mas_lt b h2) t q' π hm hq'

/-! ## The invariant for a part that may be absent -/

/-- The `exact` half of the invariant: a part whose provenance is an axis is
the part of the subject there. -/
def ExactAt (y σ : Noun) (o : Option Noun) : Prop :=
  ∀ π a, springAt σ π = A a → a ≠ 0 → slotO o π = slot? a y

/-- **The provenance invariant** `ProvR`, for a part that may be absent. -/
structure ProvO (y : Noun) (S : Sock) (σ : Noun) (o : Option Noun) : Prop where
  nonvoid : S ≠ Sock.void
  exact : ExactAt y σ o
  const : ∀ π, springAt σ π = A 0 → FitsOpt (sockAt S π) (slotO o π)

theorem provO_iff {y : Noun} {S : Sock} {σ p : Noun} : ProvO y S σ (some p) ↔ ProvR y S σ p :=
  ⟨fun h => ⟨h.nonvoid, h.exact, h.const⟩, fun h => ⟨h.nonvoid, h.exact, h.const⟩⟩

theorem fitsOpt_dunno (o : Option Noun) : FitsOpt Sock.dunno o := by
  cases o with
  | none => exact dunno_blank
  | some n => exact fits_dunno n

theorem fitsOpt_blank {S : Sock} (h : S.Blank) (o : Option Noun) : FitsOpt S o := by
  cases o with
  | none => exact h
  | some n => exact Sock.Blank.fits h n

theorem exactAt_zero (y : Noun) (o : Option Noun) : ExactAt y (A 0) o := by
  intro π a e ha
  rw [springAt_zero] at e
  cases e; exact absurd rfl ha

theorem ExactAt.part {y σ : Noun} {o : Option Noun} (h : ExactAt y σ o) (π : List Bool) :
    ExactAt y (springAt σ π) (slotO o π) := fun ρ a e ha => by
  rw [← slotO_app]; exact h (π ++ ρ) a (by rw [springAt_app]; exact e) ha

theorem ProvO.part {y : Noun} {S : Sock} {σ : Noun} {o : Option Noun} (h : ProvO y S σ o)
    (π : List Bool) : ProvO y (sockAt S π) (springAt σ π) (slotO o π) where
  nonvoid := sockAt_ne_void π h.nonvoid
  exact := h.exact.part π
  const := fun ρ e => by
    rw [← slotO_app, ← sockAt_app]; exact h.const (π ++ ρ) (by rw [springAt_app]; exact e)

theorem ProvO.congr {y : Noun} {S : Sock} {σ σ' : Noun} {o : Option Noun}
    (he : ∀ π, springAt σ' π = springAt σ π) (h : ProvO y S σ o) : ProvO y S σ' o where
  nonvoid := h.nonvoid
  exact := fun π a e ha => h.exact π a (by rw [← he]; exact e) ha
  const := fun π e => h.const π (by rw [← he]; exact e)

/-- A part without provenance that the sock knows nothing of. -/
theorem provO_dunno (y : Noun) (o : Option Noun) : ProvO y Sock.dunno (A 0) o where
  nonvoid := by simp [Sock.dunno]
  exact := exactAt_zero y o
  const := fun π _ => by rw [sockAt_dunno]; exact fitsOpt_dunno _

/-- A blank sock: only the `exact` half is left. -/
theorem provO_blank {y : Noun} {S : Sock} {σ : Noun} {o : Option Noun} (hb : S.Blank)
    (he : ExactAt y σ o) : ProvO y S σ o where
  nonvoid := fun h => by subst h; exact Sock.Blank.not_void hb
  exact := he
  const := fun π _ => fitsOpt_blank (sockAt_blank π hb) _

/-! ## Nock 0 -/

/-- **Nock 0 keeps the invariant**: the part at an axis, with `+pull:so` and
`+slot:pi`. -/
theorem provO_slot {y : Noun} {S : Sock} {σ : Noun} {o : Option Noun} {b : Nat} {q : List Bool}
    (h : ProvO y S σ o) (hb : 1 ≤ b) (hq : axisPath b = some q) :
    ProvO y (sockAt S q) (Pi.slot σ b) (slotO o q) :=
  (h.part q).congr fun π => by rw [springAt_slot b σ q π hb hq, springAt_app]

/-! ## Cons -/

theorem springAt_cons_cons (x z : Noun) (b : Bool) (π : List Bool) :
    springAt (Pi.cons x z) (b :: π) = springAt (if b then z else x) π := by
  unfold Pi.cons
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    cases b <;> simp [springAt, springAt_zero, Pi.hed, Pi.tel]
  · cases b <;> rfl

theorem cons_ne_atom {x z : Noun} {a : Nat} (h : Pi.cons x z = A a) : a = 0 ∧ x = A 0 ∧ z = A 0 := by
  unfold Pi.cons at h
  split at h
  · rename_i hh; cases h; exact ⟨rfl, hh⟩
  · cases h

theorem knit_ne_void {Sl Sr : Sock} (hl : Sl ≠ Sock.void) (hr : Sr ≠ Sock.void) :
    So.knit Sl Sr ≠ Sock.void := by
  cases Sl with
  | void => exact absurd rfl hl
  | mk l d1 =>
    cases Sr with
    | void => exact absurd rfl hr
    | mk r d2 => simp only [So.knit]; split <;> simp [Sock.dunno]

theorem fitsOpt_knit_part {Sl Sr : Sock} (hl : Sl ≠ Sock.void) (hr : Sr ≠ Sock.void) (b : Bool)
    (π : List Bool) (o : Option Noun) (h : FitsOpt (sockAt (if b then Sr else Sl) π) o) :
    FitsOpt (sockAt (So.knit Sl Sr) (b :: π)) o := by
  cases Sl with
  | void => exact absurd rfl hl
  | mk l d1 =>
    cases Sr with
    | void => exact absurd rfl hr
    | mk r d2 =>
      simp only [So.knit]
      split
      · show FitsOpt (sockAt Sock.dunno (b :: π)) o
        rw [sockAt_dunno]; exact fitsOpt_dunno o
      · rename_i hc
        rw [con_ne_no hc]
        cases b
        · simpa [sockAt, So.hed] using h
        · simpa [sockAt, So.tel] using h

/-- **A cons keeps the invariant**: `+knit:so` with `+cons:pi`, on any part
whose head and tail satisfy it, including the normalization
`cons:pi ~ ~ = ~`. -/
theorem provO_knit {y : Noun} {Sl Sr : Sock} {σl σr : Noun} {o : Option Noun}
    (hl : ProvO y Sl σl (slotO o [false])) (hr : ProvO y Sr σr (slotO o [true])) :
    ProvO y (So.knit Sl Sr) (Pi.cons σl σr) o where
  nonvoid := knit_ne_void hl.nonvoid hr.nonvoid
  exact := by
    intro π a e ha
    cases π with
    | nil => exact absurd (cons_ne_atom e).1 ha
    | cons b ρ =>
      rw [springAt_cons_cons] at e
      rw [slotO_cons]
      cases b
      · exact hl.exact ρ a e ha
      · exact hr.exact ρ a e ha
  const := by
    intro π e
    cases π with
    | nil =>
      obtain ⟨_, h1, h2⟩ := cons_ne_atom e
      have fl := hl.const [] (by rw [h1]; rfl)
      have fr := hr.const [] (by rw [h2]; rfl)
      cases o with
      | none => exact knit_blank fl fr
      | some n =>
        cases n with
        | atom k => exact Sock.Blank.fits (knit_blank fl fr) _
        | cell x z =>
          rw [slotO_nil] at fl fr
          exact knit_fits (by simpa [slotO, slotAtPath, sockAt, FitsOpt] using fl)
            (by simpa [slotO, slotAtPath, sockAt, FitsOpt] using fr)
    | cons b ρ =>
      rw [springAt_cons_cons] at e
      rw [slotO_cons]
      apply fitsOpt_knit_part hl.nonvoid hr.nonvoid
      cases b
      · exact hl.const ρ e
      · exact hr.const ρ e

end SkaModel
end Formalization
