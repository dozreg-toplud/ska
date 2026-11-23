module

public import lemmas.Hoon.Lists
public import lemmas.Pill.Arm.Welp
public import lemmas.Pill.Arm.Zing
public import lemmas.Pill.Arm.Snoc
public import lemmas.Pill.Arm.Skid
public import lemmas.Pill.Arm.Sort
public import lemmas.Pill.Arm.Spin
import all lemmas.Pill.Arm.Welp
import all lemmas.Pill.Arm.Zing
import all lemmas.Pill.Arm.Snoc
import all lemmas.Pill.Arm.Skid
import all lemmas.Pill.Arm.Sort
import all lemmas.Pill.Arm.Spin

/-!
The list arms `+welp`, `+zing`, `+snoc`, `+skid`, `+sort` and `+spin` of the
pill's `hoon.hoon`.

```hoon
++  welp                                                ::  faceless weld
  ~/  %welp
  |*  [* *]
  ?~  +<-
    +<-(. +<+)
  +<-(+ $(+<- +<->))
::
++  zing                                                ::  promote
  ~/  %zing
  |*  *
  ?~  +<
    +<
  (welp +<- $(+< +<+))
::
++  snoc
  |*  [a=(list) b=*]
  (weld a ^+(a [b]~))
::
++  skid                                                ::  separate
  ~/  %skid
  |*  [a=(list) b=$-(* ?)]
  |-  ^+  [p=a q=a]
  ?~  a  [~ ~]
  =+  c=$(a t.a)
  ?:((b i.a) [[i.a p.c] q.c] [p.c [i.a q.c]])
::
++  sort  !.                                            ::  quicksort
  ~/  %sort
  |*  [a=(list) b=$-([* *] ?)]
  =>  .(a ^.(homo a))
  |-  ^+  a
  ?~  a  ~
  =+  s=(skid t.a |:(c=i.a (b c i.a)))
  %+  weld
    $(a p.s)
  ^+  t.a
  [i.a $(a q.s)]
::
++  spin                                                ::  stateful turn
  ~/  %spin
  |*  [a=(list) b=* c=_|=(^ [** +<+])]
  =>  .(c `$-([_?>(?=(^ a) i.a) _b] [_-:(c) _b])`c)
  =/  acc=(list _-:(c))  ~
  |-  ^-  (pair _acc _b)
  ?~  a
    [(flop acc) b]
  =^  res  b  (c i.a b)
  $(acc [res acc], a t.a)
```

`+zing` reads `+welp` from its context, `+snoc` reads `+weld`, `+sort` reads
`+skid` and `+weld`, and `+spin` reads `+flop`, which reads `+homo`.  The cast
`^.(homo a)` of `+sort` is a cast only: the pill's `+sort` does not call
`+homo`.

`+skid` slams its gate on the elements from the last to the first, since it
splits the tail before it tests the head.  `+sort` is the quicksort `qsort`
below: the elements `c` of the tail with `(b c i.a)` go before the head, in the
order that `+sort` gives them, and the others after it.  `+spin` slams its gate
on the elements from the first to the last, threading the state.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

abbrev WelpIn (c : Noun) : Prop := slot? welp.axis c = some welp.arm
abbrev WeldIn (c : Noun) : Prop := slot? weld.axis c = some weld.arm
abbrev SortIn (c : Noun) : Prop := slot? skid.axis c = some skid.arm ∧ WeldIn c
abbrev SpinIn (c : Noun) : Prop := slot? flop.axis c = some flop.arm ∧ HomoIn c

/-! ## `+welp`, `+zing` -/

@[nock_exec] theorem welp_arm (c : Noun) :
    nock c welp.arm = some (C welp.battery (C (C (A 0) (A 0)) c)) := by
  nock_open welp.arm; simp only [nock_exec]

/-- Slamming the `+welp` gate on a list and any noun `b`. -/
@[nock_exec] theorem welp_gate (c b : Noun) : ∀ (l : List Noun),
    nock (C welp.battery (C (C (listN l) b) c)) welp.battery = some (appendN l b)
  | [] => by nock_open welp.battery; simp [nock_exec]
  | x :: xs => by
    have ih := welp_gate c b xs
    nock_open welp.battery
    simp [nock_exec, ih]

/-- Slamming the `+zing` gate on a list of lists: their concatenation. -/
theorem zing_gate (c : Noun) (hc : WelpIn c) : ∀ (ls : List (List Noun)),
    nock (C zing.battery (C (listN (ls.map listN)) c)) zing.battery = some (listN ls.flatten)
  | [] => by nock_open zing.battery; simp [nock_exec]
  | l :: ls => by
    have ih := zing_gate c hc ls
    nock_open zing.battery
    simp [nock_exec, hc, ih, appendN_listN]

/-! ## `+snoc` -/

/-- Slamming the `+snoc` gate on a list and a noun: the list with the noun at
its end. -/
theorem snoc_gate (c : Noun) (hc : WeldIn c) (l : List Noun) (b : Noun) :
    nock (C snoc.battery (C (C (listN l) b) c)) snoc.battery = some (listN (l ++ [b])) := by
  nock_open snoc.battery
  have hw := weld_gate_list c l [b]
  simp only [listN_cons, listN_nil] at hw
  simp [nock_exec, hc, hw]

/-! ## `+skid` -/

@[nock_exec] theorem skid_arm (c : Noun) :
    nock c skid.arm = some (C skid.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) c)) := by
  nock_open skid.arm; simp only [nock_exec]

theorem skid_loop (c bp bs bc : Noun) (p : Noun → Bool) : ∀ (l : List Noun),
    (∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) →
    nock (C skid.loop (C skid.battery (C (C (listN l) (C bp (C bs bc))) c))) skid.loop
      = some (C (listN (l.filter p)) (listN (l.filter (fun x => !p x)))) := by
  intro l
  induction l with
  | nil => intro _; nock_open skid.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open skid.loop
    cases hp : p x <;> simp [nock_exec, hx, hxs, hp]

/-- Slamming the `+skid` gate: the elements on which the gate says yes, and
those on which it says no. -/
theorem skid_gate (c bp bs bc : Noun) (p : Noun → Bool) (l : List Noun)
    (hf : ∀ x ∈ l, nock (C bp (C x bc)) bp = some (loob (p x))) :
    nock (C skid.battery (C (C (listN l) (C bp (C bs bc))) c)) skid.battery
      = some (C (listN (l.filter p)) (listN (l.filter (fun x => !p x)))) := by
  nock_open skid.battery
  simp only [nock_exec, skid_loop c bp bs bc p l hf]

/-! ## `+sort` -/

-- Without `wf.preprocess`, the recursive calls keep their plain `List.filter`.
set_option wf.preprocess false in
/-- The quicksort of `+sort`, with the order `p`: `p c x` puts `c` before the
pivot `x`. -/
def qsort (p : Noun → Noun → Bool) : List Noun → List Noun
  | [] => []
  | x :: xs => qsort p (xs.filter (fun c => p c x)) ++ x :: qsort p (xs.filter (fun c => !p c x))
termination_by l => l.length
decreasing_by
  all_goals (simp only [List.length_cons]; exact Nat.lt_succ_of_le (List.length_filter_le _ _))

/-- The gate that `+sort` hands to `+skid` slams `b` on the element and the
head of the list. -/
@[nock_exec] theorem sort_cmp (y x xs bp bs bc ctx : Noun) :
    nock (C sort.cmp (C y (C sort.loop (C sort.battery
        (C (C (C x xs) (C bp (C bs bc))) ctx))))) sort.cmp
      = nock (C bp (C (C y x) bc)) bp := by
  nock_open sort.cmp; simp only [nock_exec]

theorem appendN_cons_listN (l l' : List Noun) (x : Noun) :
    appendN l (C x (listN l')) = listN (l ++ x :: l') := by
  rw [← listN_cons, appendN_listN]

theorem sort_loop (ctx : Noun) (hc : SortIn ctx) (bp bs bc : Noun) (p : Noun → Noun → Bool) :
    ∀ (l : List Noun), (∀ x ∈ l, ∀ y ∈ l, nock (C bp (C (C x y) bc)) bp = some (loob (p x y))) →
    nock (C sort.loop (C sort.battery (C (C (listN l) (C bp (C bs bc))) ctx))) sort.loop
      = some (listN (qsort p l)) := by
  intro l
  fun_induction qsort p l with
  | case1 => intro _; nock_open sort.loop; simp [nock_exec]
  | case2 x xs ih1 ih2 =>
    intro hf
    obtain ⟨hskid, hweld⟩ := hc
    have h1 := ih1 (fun a ha b hb =>
      hf a (List.mem_cons_of_mem _ (List.mem_filter.1 ha).1) b
        (List.mem_cons_of_mem _ (List.mem_filter.1 hb).1))
    have h2 := ih2 (fun a ha b hb =>
      hf a (List.mem_cons_of_mem _ (List.mem_filter.1 ha).1) b
        (List.mem_cons_of_mem _ (List.mem_filter.1 hb).1))
    have hs := skid_gate ctx sort.cmp x
      (C sort.loop (C sort.battery (C (C (C x (listN xs)) (C bp (C bs bc))) ctx)))
      (fun c => p c x) xs
      (fun y hy => by
        rw [sort_cmp]
        exact hf y (List.mem_cons_of_mem _ hy) x List.mem_cons_self)
    nock_open sort.loop
    simp [nock_exec, hskid, hweld, hs, h1, h2, weld_gate, appendN_cons_listN]

/-- Slamming the `+sort` gate on a list and a gate that says whether `x` goes
before `y`, on the elements of the list: `qsort`. -/
theorem sort_gate (ctx : Noun) (hc : SortIn ctx) (bp bs bc : Noun) (p : Noun → Noun → Bool)
    (l : List Noun)
    (hf : ∀ x ∈ l, ∀ y ∈ l, nock (C bp (C (C x y) bc)) bp = some (loob (p x y))) :
    nock (C sort.battery (C (C (listN l) (C bp (C bs bc))) ctx)) sort.battery
      = some (listN (qsort p l)) := by
  nock_open sort.battery
  simp only [nock_exec, sort_loop ctx hc bp bs bc p l hf]

/-- `qsort` sorts by a permutation. -/
theorem qsort_perm (p : Noun → Noun → Bool) (l : List Noun) : (qsort p l).Perm l := by
  fun_induction qsort p l with
  | case1 => exact List.Perm.refl _
  | case2 x xs ih1 ih2 =>
    refine (List.Perm.append ih1 (List.Perm.cons x ih2)).trans ?_
    refine List.perm_middle.trans (List.Perm.cons x ?_)
    exact List.filter_append_perm _ xs

/-! ## `+spin` -/

/-- `+spin` with the gate `g`, from the state `s`: the products and the last
state. -/
def spinF (g : Noun → Noun → Noun × Noun) : List Noun → Noun → List Noun × Noun
  | [], s => ([], s)
  | x :: xs, s => ((g x s).1 :: (spinF g xs (g x s).2).1, (spinF g xs (g x s).2).2)

theorem spin_loop (ctx : Noun) (hc : SpinIn ctx) (cp cs cc : Noun)
    (g : Noun → Noun → Noun × Noun) : ∀ (l : List Noun),
    (∀ x ∈ l, ∀ s, nock (C cp (C (C x s) cc)) cp = some (C (g x s).1 (g x s).2)) →
    ∀ (acc : List Noun) (s : Noun),
    nock (C spin.loop (C (listN acc) (C spin.battery
        (C (C (listN l) (C s (C cp (C cs cc)))) ctx)))) spin.loop
      = some (C (listN (acc.reverse ++ (spinF g l s).1)) (spinF g l s).2) := by
  obtain ⟨hflop, hhomo⟩ := hc
  intro l
  induction l with
  | nil =>
    intro _ acc s
    nock_open spin.loop
    simp [nock_exec, hflop, flop_gate ctx hhomo, spinF]
  | cons x xs ih =>
    intro hf acc s
    have hx := hf x (by simp) s
    have hxs := ih (fun y hy => hf y (by simp [hy])) ((g x s).1 :: acc) (g x s).2
    simp only [listN_cons] at hxs
    nock_open spin.loop
    simp [nock_exec, hx, hxs, spinF]

/-- Slamming the `+spin` gate on a list, a state and a gate that maps each
element `x` and state `s` to the cell `g x s`. -/
theorem spin_gate (ctx : Noun) (hc : SpinIn ctx) (cp cs cc : Noun)
    (g : Noun → Noun → Noun × Noun) (l : List Noun) (s : Noun)
    (hf : ∀ x ∈ l, ∀ s, nock (C cp (C (C x s) cc)) cp = some (C (g x s).1 (g x s).2)) :
    nock (C spin.battery (C (C (listN l) (C s (C cp (C cs cc)))) ctx)) spin.battery
      = some (C (listN (spinF g l s).1) (spinF g l s).2) := by
  nock_open spin.battery
  have h := spin_loop ctx hc cp cs cc g l hf [] s
  simp only [listN_nil, List.reverse_nil, List.nil_append] at h
  simp only [nock_exec, h]

end Hoon
end Formalization

end
