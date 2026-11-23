module

public import lemmas.Hoon.Lists
public import lemmas.Pill.Arm.Skip
public import lemmas.Pill.Arm.Skim
public import lemmas.Pill.Arm.Murn
public import lemmas.Pill.Arm.Rear
public import lemmas.Pill.Arm.Snip
import all lemmas.Pill.Arm.Skip
import all lemmas.Pill.Arm.Skim
import all lemmas.Pill.Arm.Murn
import all lemmas.Pill.Arm.Rear
import all lemmas.Pill.Arm.Snip

/-!
More list arms of the pill's `hoon.hoon`: `+skip`, `+skim`, `+murn`, `+rear`,
`+snip`.

```hoon
++  skim                                                ::  only
  ~/  %skim
  |*  [a=(list) b=$-(* ?)]
  |-
  ^+  a
  ?~  a  ~
  ?:((b i.a) [i.a $(a t.a)] $(a t.a))
::
++  skip                                                ::  except
  ~/  %skip
  |*  [a=(list) b=$-(* ?)]
  |-
  ^+  a
  ?~  a  ~
  ?:((b i.a) $(a t.a) [i.a $(a t.a)])
::
++  murn                                                ::  maybe transform
  ~/  %murn
  |*  [a=(list) b=$-(* (unit))]
  =>  .(a (homo a))
  |-  ^-  (list _?>(?=(^ a) (need (b i.a))))
  ?~  a  ~
  =/  c  (b i.a)
  ?~  c  $(a t.a)
  [+.c $(a t.a)]
::
++  rear                                                ::  last item of list
  ~/  %rear
  |*  a=(list)
  ^-  _?>(?=(^ a) i.a)
  ?>  ?=(^ a)
  ?:  =(~ t.a)  i.a  ::NOTE  avoiding tmi
  $(a t.a)
::
++  snip                                                ::  drop tail off list
  ~/  %snip
  |*  a=(list)
  ^+  a
  ?~  a  ~
  ?:  =(~ t.a)  ~
  [i.a $(a t.a)]
```
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## `+skim`, `+skip` -/

theorem skim_loop (c bp bs bc : Noun) (p : Noun → Bool) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) →
    nock (C skim.loop (C skim.battery (C (C (listN l) (C bp (C bs bc))) c))) skim.loop
      = some (listN (l.filter p)) := by
  intro l
  induction l with
  | nil => intro _; nock_open skim.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open skim.loop
    cases hp : p x <;> simp [nock_exec, hx, hxs, hp]

/-- Slamming the `+skim` gate: the elements on which the gate says yes. -/
theorem skim_gate (c bp bs bc : Noun) (p : Noun → Bool) (l : List Noun)
    (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) :
    nock (C skim.battery (C (C (listN l) (C bp (C bs bc))) c)) skim.battery
      = some (listN (l.filter p)) := by
  nock_open skim.battery
  simp only [nock_exec, skim_loop c bp bs bc p l hf]

theorem skip_loop (c bp bs bc : Noun) (p : Noun → Bool) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) →
    nock (C skip.loop (C skip.battery (C (C (listN l) (C bp (C bs bc))) c))) skip.loop
      = some (listN (l.filter (fun x => !p x))) := by
  intro l
  induction l with
  | nil => intro _; nock_open skip.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open skip.loop
    cases hp : p x <;> simp [nock_exec, hx, hxs, hp]

/-- Slamming the `+skip` gate: the elements on which the gate says no. -/
theorem skip_gate (c bp bs bc : Noun) (p : Noun → Bool) (l : List Noun)
    (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) :
    nock (C skip.battery (C (C (listN l) (C bp (C bs bc))) c)) skip.battery
      = some (listN (l.filter (fun x => !p x))) := by
  nock_open skip.battery
  simp only [nock_exec, skip_loop c bp bs bc p l hf]

/-! ## `+murn` -/

/-- The value of a unit, `none` for `~`. -/
def unitVal : Noun → Option Noun
  | Noun.cell _ v => some v
  | _ => none

theorem murn_loop (c bp bs bc : Noun) (f : Noun → Noun) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (f x) ∧ (f x = A 0 ∨ ∃ h v, f x = C h v)) →
    nock (C murn.loop (C murn.battery (C (C (listN l) (C bp (C bs bc))) c))) murn.loop
      = some (listN (l.filterMap fun x => unitVal (f x))) := by
  intro l
  induction l with
  | nil => intro _; nock_open murn.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    obtain ⟨hx, hu⟩ := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open murn.loop
    rcases hu with hu | ⟨h, v, hu⟩
    · simp [nock_exec, hx, hxs, hu, unitVal]
    · simp [nock_exec, hx, hxs, hu, unitVal]

/-- Slamming the `+murn` gate on a list and a gate that maps each element `x`
to a unit `f x`: the values of the units that are not `~`. -/
theorem murn_gate (c : Noun) (hc : HomoIn c) (bp bs bc : Noun) (f : Noun → Noun) (l : List Noun)
    (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (f x) ∧ (f x = A 0 ∨ ∃ h v, f x = C h v)) :
    nock (C murn.battery (C (C (listN l) (C bp (C bs bc))) c)) murn.battery
      = some (listN (l.filterMap fun x => unitVal (f x))) := by
  nock_open murn.battery
  simp only [nock_exec, hc, homo_arm, murn_loop c bp bs bc f l hf]

/-! ## `+rear`, `+snip` -/

/-- Slamming the `+rear` gate on a list that is not empty: its last element. -/
theorem rear_gate (c : Noun) : ∀ (l : List Noun) (h : l ≠ []),
    nock (C rear.battery (C (listN l) c)) rear.battery = some (l.getLast h)
  | [], h => absurd rfl h
  | [x], _ => by nock_open rear.battery; simp [nock_exec]
  | x :: y :: ys, _ => by
    have ih := rear_gate c (y :: ys) (by simp)
    simp only [listN_cons] at ih
    nock_open rear.battery
    simp [nock_exec, ih]

/-- `(rear ~)` crashes. -/
theorem rear_gate_nil (c : Noun) : nock (C rear.battery (C (A 0) c)) rear.battery = none := by
  nock_open rear.battery; simp [nock_exec]

/-- Slamming the `+snip` gate on a list: the list without its last element. -/
theorem snip_gate (c : Noun) : ∀ (l : List Noun),
    nock (C snip.battery (C (listN l) c)) snip.battery = some (listN l.dropLast)
  | [] => by nock_open snip.battery; simp [nock_exec]
  | [x] => by nock_open snip.battery; simp [nock_exec]
  | x :: y :: ys => by
    have ih := snip_gate c (y :: ys)
    simp only [listN_cons] at ih
    nock_open snip.battery
    simp [nock_exec, ih]

end Hoon
end Formalization

end
