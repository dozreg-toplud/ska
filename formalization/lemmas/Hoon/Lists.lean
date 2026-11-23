module

public import lemmas.Hoon.Arith
public import lemmas.Pill.Arm.Lent
public import lemmas.Pill.Arm.Weld
public import lemmas.Pill.Arm.Flop
public import lemmas.Pill.Arm.Homo
public import lemmas.Pill.Arm.Snag
public import lemmas.Pill.Arm.Scag
public import lemmas.Pill.Arm.Slag
public import lemmas.Pill.Arm.Turn
public import lemmas.Pill.Arm.Roll
public import lemmas.Pill.Arm.Levy
public import lemmas.Pill.Arm.Lien
import all lemmas.Pill.Arm.Lent
import all lemmas.Pill.Arm.Weld
import all lemmas.Pill.Arm.Flop
import all lemmas.Pill.Arm.Homo
import all lemmas.Pill.Arm.Snag
import all lemmas.Pill.Arm.Scag
import all lemmas.Pill.Arm.Slag
import all lemmas.Pill.Arm.Turn
import all lemmas.Pill.Arm.Roll
import all lemmas.Pill.Arm.Levy
import all lemmas.Pill.Arm.Lien
/-!
The list arms of the pill's `hoon.hoon`, against `List Noun`:

| arm | model | reads from the context `c` |
| --- | --- | --- |
| `+lent` | `l.length` | nothing |
| `+weld` | `appendN l b` (`l ++ l'` when `b` is a list) | nothing |
| `+flop` | `l.reverse` | `+homo` |
| `+snag` | `l[n]`, a crash when `l.length ≤ n` | `+dec`, below |
| `+scag` | `l.take n` | `+dec`, below |
| `+slag` | `l.drop n` | `+dec`, below |
| `+turn` | `l.map f` | `+homo` |
| `+roll` | `l.foldl` | nothing |
| `+levy`, `+lien` | `l.all p`, `l.any p` | nothing |

A list is the noun `listN l`.  The wet gates (`|*`) are the cores of their
arms, as the pill holds them: a caller with a more specific type runs the same
Nock.

`+turn`, `+roll`, `+levy` and `+lien` take a gate `b = [bp bs bc]`.  Their
theorems assume what slamming `b` does on the elements of the list:
`nock (C bp (C x bc)) bp = some (f x)`, which is what `+turn` runs when it
slams `b` on `x`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## What the gates read from their context -/

/-- `+homo` is the identity gate `[[0 6] 0 c]`. -/
abbrev HomoIn (c : Noun) : Prop := slot? homo.axis c = some homo.arm

@[nock_exec] theorem homo_arm (c : Noun) :
    nock c homo.arm = some (C (C (A 0) (A 6)) (C (A 0) c)) := by
  nock_open homo.arm; simp only [nock_exec]

/-! ## The arms build their gates -/

@[nock_exec] theorem lent_arm (c : Noun) :
    nock c lent.arm = some (C lent.battery (C (A 0) c)) := by
  nock_open lent.arm; simp only [nock_exec]

@[nock_exec] theorem weld_arm (c : Noun) :
    nock c weld.arm = some (C weld.battery (C (C (A 0) (A 0)) c)) := by
  nock_open weld.arm; simp only [nock_exec]

@[nock_exec] theorem flop_arm (c : Noun) :
    nock c flop.arm = some (C flop.battery (C (A 0) c)) := by
  nock_open flop.arm; simp only [nock_exec]

@[nock_exec] theorem snag_arm (c : Noun) :
    nock c snag.arm = some (C snag.battery (C (C (A 0) (A 0)) c)) := by
  nock_open snag.arm; simp only [nock_exec]

@[nock_exec] theorem scag_arm (c : Noun) :
    nock c scag.arm = some (C scag.battery (C (C (A 0) (A 0)) c)) := by
  nock_open scag.arm; simp only [nock_exec]

@[nock_exec] theorem slag_arm (c : Noun) :
    nock c slag.arm = some (C slag.battery (C (C (A 0) (A 0)) c)) := by
  nock_open slag.arm; simp only [nock_exec]

/-- The bunt of a gate argument of `+turn`, `+levy`, `+lien`. -/
def buntGate : Noun := C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0)))

@[nock_exec] theorem turn_arm (c : Noun) :
    nock c turn.arm = some (C turn.battery (C (C (A 0) buntGate) c)) := by
  nock_open turn.arm; simp only [nock_exec]; rfl

@[nock_exec] theorem roll_arm (c : Noun) :
    nock c roll.arm
      = some (C roll.battery (C (C (A 0) (C (C (A 0) (A 13)) (C (C (A 0) (A 0)) (A 0)))) c)) := by
  nock_open roll.arm; simp only [nock_exec]

@[nock_exec] theorem levy_arm (c : Noun) :
    nock c levy.arm = some (C levy.battery (C (C (A 0) buntGate) c)) := by
  nock_open levy.arm; simp only [nock_exec]; rfl

@[nock_exec] theorem lien_arm (c : Noun) :
    nock c lien.arm = some (C lien.battery (C (C (A 0) buntGate) c)) := by
  nock_open lien.arm; simp only [nock_exec]; rfl

/-! ## `+lent` -/

theorem lent_loop (c : Noun) : ∀ (l : List Noun) (k : Nat),
    nock (C lent.loop (C (A k) (C lent.battery (C (listN l) c)))) lent.loop
      = some (A (k + l.length)) := by
  intro l
  induction l with
  | nil =>
    intro k
    nock_open lent.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro k
    nock_open lent.loop
    simp [nock_exec, ih]
    omega

/-- Slamming the `+lent` gate on a list. -/
theorem lent_gate (c : Noun) (l : List Noun) :
    nock (C lent.battery (C (listN l) c)) lent.battery = some (A l.length) := by
  nock_open lent.battery
  simp only [nock_exec, lent_loop c l 0, Nat.zero_add]

/-! ## `+weld` -/

theorem weld_loop (c b : Noun) : ∀ (l : List Noun),
    nock (C weld.loop (C weld.battery (C (C (listN l) b) c))) weld.loop = some (appendN l b) := by
  intro l
  induction l with
  | nil =>
    nock_open weld.loop
    simp [nock_exec]
  | cons x xs ih =>
    nock_open weld.loop
    simp [nock_exec, ih]

/-- Slamming the `+weld` gate on a list and any noun `b`. -/
theorem weld_gate (c b : Noun) (l : List Noun) :
    nock (C weld.battery (C (C (listN l) b) c)) weld.battery = some (appendN l b) := by
  nock_open weld.battery
  simp only [nock_exec, weld_loop c b l]

/-- Slamming the `+weld` gate on two lists. -/
theorem weld_gate_list (c : Noun) (l l' : List Noun) :
    nock (C weld.battery (C (C (listN l) (listN l')) c)) weld.battery = some (listN (l ++ l')) := by
  rw [weld_gate, appendN_listN]

/-! ## `+flop` -/

theorem appendN_append (l l' : List Noun) (t : Noun) :
    appendN (l ++ l') t = appendN l (appendN l' t) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem flop_loop (c : Noun) : ∀ (l : List Noun) (t : Noun),
    nock (C flop.loop (C t (C flop.battery (C (listN l) c)))) flop.loop
      = some (appendN l.reverse t) := by
  intro l
  induction l with
  | nil =>
    intro t
    nock_open flop.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro t
    nock_open flop.loop
    simp [nock_exec, ih, appendN_append]

/-- Slamming the `+flop` gate on a list. -/
theorem flop_gate (c : Noun) (hc : HomoIn c) (l : List Noun) :
    nock (C flop.battery (C (listN l) c)) flop.battery = some (listN l.reverse) := by
  nock_open flop.battery
  simp only [nock_exec, hc, homo_arm, flop_loop c l (A 0)]
  rfl

/-! ## `+snag`, `+scag`, `+slag` -/

theorem snag_loop (bat t : Noun) (ht : DecIn t) : ∀ (l : List Noun) (n : Nat) (x : Noun),
    l[n]? = some x →
    nock (C snag.loop (C snag.battery (C (C (A n) (listN l)) (C bat t)))) snag.loop = some x := by
  intro l
  induction l with
  | nil => intro n x h; simp at h
  | cons y ys ih =>
    intro n x h
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      nock_open snag.loop
      simp [nock_exec]
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      nock_open snag.loop
      simp [nock_exec, ht, dec_gate t (n + 1) (by omega), ih n x h]

/-- Slamming the `+snag` gate on an index `n` and a list whose element `n`
is `x`. -/
theorem snag_gate (c : Noun) (hc : Below DecIn c) (n : Nat) (l : List Noun) (x : Noun)
    (h : l[n]? = some x) :
    nock (C snag.battery (C (C (A n) (listN l)) c)) snag.battery = some x := by
  obtain ⟨bat, t, rfl, ht⟩ := hc.elim
  nock_open snag.battery
  simp only [nock_exec, snag_loop bat t ht l n x h]

theorem snag_loop_none (bat t : Noun) (ht : DecIn t) : ∀ (l : List Noun) (n : Nat),
    l.length ≤ n →
    nock (C snag.loop (C snag.battery (C (C (A n) (listN l)) (C bat t)))) snag.loop = none := by
  intro l
  induction l with
  | nil =>
    intro n _
    nock_open snag.loop
    simp [nock_exec]
  | cons y ys ih =>
    intro n h
    cases n with
    | zero => simp at h
    | succ n =>
      nock_open snag.loop
      simp [nock_exec, ht, dec_gate t (n + 1) (by omega), ih n (by simp at h; omega)]

/-- `(snag n l)` crashes when `l` has no element `n`. -/
theorem snag_gate_none (c : Noun) (hc : Below DecIn c) (n : Nat) (l : List Noun)
    (h : l.length ≤ n) :
    nock (C snag.battery (C (C (A n) (listN l)) c)) snag.battery = none := by
  obtain ⟨bat, t, rfl, ht⟩ := hc.elim
  nock_open snag.battery
  simp only [nock_exec, snag_loop_none bat t ht l n h]

theorem scag_loop (bat t : Noun) (ht : DecIn t) : ∀ (l : List Noun) (n : Nat),
    nock (C scag.loop (C scag.battery (C (C (A n) (listN l)) (C bat t)))) scag.loop
      = some (listN (l.take n)) := by
  intro l
  induction l with
  | nil =>
    intro n
    nock_open scag.loop
    simp [nock_exec]
  | cons y ys ih =>
    intro n
    cases n with
    | zero =>
      nock_open scag.loop
      simp [nock_exec]
    | succ n =>
      nock_open scag.loop
      simp [nock_exec, ht, dec_gate t (n + 1) (by omega), ih n]

/-- Slamming the `+scag` gate on a count `n` and a list. -/
theorem scag_gate (c : Noun) (hc : Below DecIn c) (n : Nat) (l : List Noun) :
    nock (C scag.battery (C (C (A n) (listN l)) c)) scag.battery = some (listN (l.take n)) := by
  obtain ⟨bat, t, rfl, ht⟩ := hc.elim
  nock_open scag.battery
  simp only [nock_exec, scag_loop bat t ht l n]

theorem slag_loop (bat t : Noun) (ht : DecIn t) : ∀ (l : List Noun) (n : Nat),
    nock (C slag.loop (C slag.battery (C (C (A n) (listN l)) (C bat t)))) slag.loop
      = some (listN (l.drop n)) := by
  intro l
  induction l with
  | nil =>
    intro n
    cases n with
    | zero =>
      nock_open slag.loop
      simp [nock_exec]
    | succ n =>
      nock_open slag.loop
      simp [nock_exec]
  | cons y ys ih =>
    intro n
    cases n with
    | zero =>
      nock_open slag.loop
      simp [nock_exec]
    | succ n =>
      nock_open slag.loop
      simp [nock_exec, ht, dec_gate t (n + 1) (by omega), ih n]

/-- Slamming the `+slag` gate on a count `n` and a list. -/
theorem slag_gate (c : Noun) (hc : Below DecIn c) (n : Nat) (l : List Noun) :
    nock (C slag.battery (C (C (A n) (listN l)) c)) slag.battery = some (listN (l.drop n)) := by
  obtain ⟨bat, t, rfl, ht⟩ := hc.elim
  nock_open slag.battery
  simp only [nock_exec, slag_loop bat t ht l n]

/-! ## `+turn` -/

theorem turn_loop (c bp bs bc : Noun) (f : Noun → Noun) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (f x)) →
    nock (C turn.loop (C turn.battery (C (C (listN l) (C bp (C bs bc))) c))) turn.loop
      = some (listN (l.map f)) := by
  intro l
  induction l with
  | nil =>
    intro _
    nock_open turn.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open turn.loop
    simp [nock_exec, hx, hxs]

/-- Slamming the `+turn` gate on a list and a gate `[bp bs bc]` that maps each
element `x` of the list to `f x`. -/
theorem turn_gate (c : Noun) (hc : HomoIn c) (bp bs bc : Noun) (f : Noun → Noun)
    (l : List Noun) (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (f x)) :
    nock (C turn.battery (C (C (listN l) (C bp (C bs bc))) c)) turn.battery
      = some (listN (l.map f)) := by
  nock_open turn.battery
  simp only [nock_exec, hc, homo_arm, turn_loop c bp bs bc f l hf]

/-! ## `+roll` -/

theorem roll_loop (c bp e bc : Noun) (f : Noun → Noun → Noun) : ∀ (l : List Noun) (acc : Noun),
    (∀ x ∈ l, ∀ acc, nock (C bp (C (C x acc) bc)) bp = some (f x acc)) →
    nock (C roll.loop (C roll.battery (C (C (listN l) (C bp (C (C e acc) bc))) c))) roll.loop
      = some (l.foldl (fun acc x => f x acc) acc) := by
  intro l
  induction l with
  | nil =>
    intro acc _
    nock_open roll.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro acc hf
    have hx := hf x (by simp)
    have hxs := ih (f x acc) (fun y hy => hf y (by simp [hy]))
    nock_open roll.loop
    simp [nock_exec, hx, hxs]

/-- Slamming the `+roll` gate on a list and a gate `[bp [e acc] bc]` that
maps an element `x` and an accumulator `acc` to `f x acc`. -/
theorem roll_gate (c bp e acc bc : Noun) (f : Noun → Noun → Noun) (l : List Noun)
    (hf : ∀ x ∈ l, ∀ acc, nock (C bp (C (C x acc) bc)) bp = some (f x acc)) :
    nock (C roll.battery (C (C (listN l) (C bp (C (C e acc) bc))) c)) roll.battery
      = some (l.foldl (fun acc x => f x acc) acc) := by
  nock_open roll.battery
  simp only [nock_exec, roll_loop c bp e bc f l acc hf]

/-! ## `+levy`, `+lien` -/

theorem levy_loop (c bp bs bc : Noun) (p : Noun → Bool) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) →
    nock (C levy.loop (C levy.battery (C (C (listN l) (C bp (C bs bc))) c))) levy.loop
      = some (loob (l.all p)) := by
  intro l
  induction l with
  | nil =>
    intro _
    nock_open levy.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open levy.loop
    cases hp : p x <;> simp [nock_exec, hx, hxs, hp]

/-- Slamming the `+levy` gate on a list and a gate that maps each element `x`
to the flag `p x`. -/
theorem levy_gate (c bp bs bc : Noun) (p : Noun → Bool) (l : List Noun)
    (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) :
    nock (C levy.battery (C (C (listN l) (C bp (C bs bc))) c)) levy.battery
      = some (loob (l.all p)) := by
  nock_open levy.battery
  simp only [nock_exec, levy_loop c bp bs bc p l hf]

theorem lien_loop (c bp bs bc : Noun) (p : Noun → Bool) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) →
    nock (C lien.loop (C lien.battery (C (C (listN l) (C bp (C bs bc))) c))) lien.loop
      = some (loob (l.any p)) := by
  intro l
  induction l with
  | nil =>
    intro _
    nock_open lien.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open lien.loop
    cases hp : p x <;> simp [nock_exec, hx, hxs, hp]

/-- Slamming the `+lien` gate on a list and a gate that maps each element `x`
to the flag `p x`. -/
theorem lien_gate (c bp bs bc : Noun) (p : Noun → Bool) (l : List Noun)
    (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) :
    nock (C lien.battery (C (C (listN l) (C bp (C bs bc))) c)) lien.battery
      = some (loob (l.any p)) := by
  nock_open lien.battery
  simp only [nock_exec, lien_loop c bp bs bc p l hf]

end Hoon
end Formalization

end
