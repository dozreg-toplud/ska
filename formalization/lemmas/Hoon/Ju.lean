module

public import lemmas.Hoon.Sets
public import lemmas.Hoon.GasBy
public import lemmas.Hoon.SetFolds
public import lemmas.Pill.Arm.Ju
public import lemmas.Pill.Arm.Ja
import all lemmas.Pill.Arm.Ju
import all lemmas.Pill.Arm.Ja
import all lemmas.Pill.Arm.By
import all lemmas.Pill.Arm.In

/-!
The doors `+ju` (jugs: maps from keys to sets) and `+ja` (jars: maps from
keys to lists) of the pill's `hoon.hoon`.

```hoon
++  ju                                                  ::  jug engine
  =|  a=(tree (pair * (tree)))  ::  (jug)
  |@
  ++  get                                               ::  gets set by key
    |*  b=*
    =+  c=(~(get by a) b)
    ?~(c ~ u.c)
  ::
  ++  has                                               ::  existence check
    |*  [b=* c=*]
    ^-  ?
    (~(has in (get b)) c)
  ::
  ++  put                                               ::  add key-set pair
    |*  [b=* c=*]
    ^+  a
    =+  d=(get b)
    (~(put by a) b (~(put in d) c))
  ::
  ++  gas                                               ::  concatenate
    |*  b=(list [p=* q=*])
    =>  .(b `(list _?>(?=([[* ^] ^] a) [p=p q=n.q]:n.a))`b)
    |-  ^+  a
    ?~  b
      a
    $(b t.b, a (put p.i.b q.i.b))
  --
++  ja                                                  ::  jar engine
  =|  a=(tree (pair * (list)))  ::  (jar)
  |@
  ++  get                                               ::  gets list by key
    |*  b=*
    =+  c=(~(get by a) b)
    ?~(c ~ u.c)
  ::
  ++  add                                               ::  adds key-list pair
    |*  [b=* c=*]
    =+  d=(get b)
    (~(put by a) b [c d])
  --
```

`get` of `+ja` is the noun of `get` of `+ju`.  The arms build the doors
`+by` and `+in` from their context, which therefore holds `+by`, `+in` and
what their arms read (`JuIn`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

abbrev JuIn (mug : Noun → Nat) (c : Noun) : Prop :=
  slot? by.axis c = some by.arm ∧ slot? in.axis c = some in.arm ∧ SomeIn c ∧ GorIn mug c ∧
    MorIn mug c

/-! ## The models -/

/-- The unit that `+get:by` returns, read as `+get:ju` reads it. -/
def unUnit : Noun → Noun
  | Noun.cell _ u => u
  | _ => A 0

/-- `+get:ju`: the set under `b`, or `~`. -/
def juGetF (mug : Noun → Nat) (b a : Noun) : Option Noun := (getF mug b a).map unUnit

/-- `+put:ju`: put `c` into the set under `b`. -/
def juPutF (mug : Noun → Nat) (b c a : Noun) : Option Noun :=
  (juGetF mug b a).bind fun d => (putInF mug c d).bind fun e => putF mug b e a

/-- `+has:ju`: whether the set under `b` holds `c`. -/
def juHasF (mug : Noun → Nat) (b c a : Noun) : Option Bool :=
  (juGetF mug b a).bind fun d => hasInF mug c d

/-- `+add:ja`: push `c` onto the list under `b`. -/
def jaAddF (mug : Noun → Nat) (b c a : Noun) : Option Noun :=
  (juGetF mug b a).bind fun d => putF mug b (C c d) a

/-- `+del:ju`: delete `c` from the set under `b`, and the key when the set
becomes empty. -/
def juDelF (mug : Noun → Nat) (b c a : Noun) : Option Noun :=
  (juGetF mug b a).bind fun d => (delInF mug c d).bind fun e =>
    if e = A 0 then delF mug b a else putF mug b e a

/-- `+gas:ju`: `juPutF` of each pair, in order. -/
def juGasF (mug : Noun → Nat) : Noun → List (Noun × Noun) → Option Noun
  | a, [] => some a
  | a, (b, c) :: rest =>
    match juPutF mug b c a with
    | some a' => juGasF mug a' rest
    | none => none

/-! ## The Nock -/

@[nock_exec] theorem ju_arm (c : Noun) : nock c ju.arm = some (C ju.battery (C (A 0) c)) := by
  nock_open ju.arm; simp only [nock_exec]

@[nock_exec] theorem ja_arm (c : Noun) : nock c ja.arm = some (C ja.battery (C (A 0) c)) := by
  nock_open ja.arm; simp only [nock_exec]

@[nock_exec] theorem ju_get_arm (d : Noun) :
    nock d ju.get.arm = some (C ju.get.battery (C (A 0) d)) := by
  nock_open ju.get.arm; simp only [nock_exec]

@[nock_exec] theorem ju_put_arm (d : Noun) :
    nock d ju.put.arm = some (C ju.put.battery (C (C (A 0) (A 0)) d)) := by
  nock_open ju.put.arm; simp only [nock_exec]

@[nock_exec] theorem ju_has_arm (d : Noun) :
    nock d ju.has.arm = some (C ju.has.battery (C (C (A 0) (A 0)) d)) := by
  nock_open ju.has.arm; simp only [nock_exec]

@[nock_exec] theorem ju_gas_arm (d : Noun) :
    nock d ju.gas.arm = some (C ju.gas.battery (C (A 0) d)) := by
  nock_open ju.gas.arm; simp only [nock_exec]

@[nock_exec] theorem ja_add_arm (d : Noun) :
    nock d ja.add.arm = some (C ja.add.battery (C (C (A 0) (A 0)) d)) := by
  nock_open ja.add.arm; simp only [nock_exec]

/-- `getF` returns a unit. -/
theorem getF_unit {mug : Noun → Nat} {b a out : Noun} (h : getF mug b a = some out) :
    out = A 0 ∨ ∃ q, out = C (A 0) q := by
  fun_induction getF mug b a
  all_goals first
    | (rename_i ih; exact ih h)
    | (cases h <;> simp)

/-- The gate `get` of a door with battery `B` (`+ju` or `+ja`), jug `a`. -/
theorem ju_get_gate {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (B b a out : Noun)
    (h : getF mug b a = some out) :
    nock (C ju.get.battery (C b (C B (C a ctx)))) ju.get.battery = some (unUnit out) := by
  obtain ⟨hby, _, hs, hg, _⟩ := hc
  nock_open ju.get.battery
  have hget := get_gate (mug := mug) ctx ⟨hs, hg⟩ b a out h
  rcases getF_unit h with rfl | ⟨q, rfl⟩
  · simp [nock_exec, hby, by_arm, get_arm, hget, unUnit]
  · simp [nock_exec, hby, by_arm, get_arm, hget, unUnit]

theorem ju_put_gate {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (b c a out : Noun)
    (h : juPutF mug b c a = some out) :
    nock (C ju.put.battery (C (C b c) (C ju.battery (C a ctx)))) ju.put.battery = some out := by
  unfold juPutF juGetF at h
  cases hg : getF mug b a with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    simp only [Option.map_some, Option.bind_some] at h
    cases hp : putInF mug c (unUnit g) with
    | none => rw [hp] at h; cases h
    | some e =>
      rw [hp] at h
      simp only [Option.bind_some] at h
      have hju := ju_get_gate ctx hc ju.battery b a g hg
      obtain ⟨hby, hin, hs, hgo, hmo⟩ := hc
      nock_open ju.put.battery
      simp [nock_exec, hby, hin, by_arm, in_arm, hju, put_arm, put_in_arm,
        put_in_gate ctx ⟨hgo, hmo⟩ c (unUnit g) e hp, put_gate ctx ⟨hgo, hmo⟩ b e a out h]

theorem ju_has_gate {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (b c a : Noun) (t : Bool)
    (h : juHasF mug b c a = some t) :
    nock (C ju.has.battery (C (C b c) (C ju.battery (C a ctx)))) ju.has.battery
      = some (loob t) := by
  unfold juHasF juGetF at h
  cases hg : getF mug b a with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    simp only [Option.map_some, Option.bind_some] at h
    have hju := ju_get_gate ctx hc ju.battery b a g hg
    obtain ⟨hby, hin, hs, hgo, hmo⟩ := hc
    nock_open ju.has.battery
    simp [nock_exec, hin, in_arm, hju, has_in_arm, has_in_gate ctx hgo c (unUnit g) t h]

theorem ja_add_gate {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (b c a out : Noun)
    (h : jaAddF mug b c a = some out) :
    nock (C ja.add.battery (C (C b c) (C ja.battery (C a ctx)))) ja.add.battery = some out := by
  unfold jaAddF juGetF at h
  cases hg : getF mug b a with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    simp only [Option.map_some, Option.bind_some] at h
    have hju := ju_get_gate ctx hc ja.battery b a g hg
    obtain ⟨hby, hin, hs, hgo, hmo⟩ := hc
    nock_open ja.add.battery
    simp [nock_exec, hby, by_arm, hju, put_arm, put_gate ctx ⟨hgo, hmo⟩ b _ a out h]

@[nock_exec] theorem ju_del_arm (d : Noun) :
    nock d ju.del.arm = some (C ju.del.battery (C (C (A 0) (A 0)) d)) := by
  nock_open ju.del.arm; simp only [nock_exec]

theorem ju_del_gate {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (b c a out : Noun)
    (h : juDelF mug b c a = some out) :
    nock (C ju.del.battery (C (C b c) (C ju.battery (C a ctx)))) ju.del.battery = some out := by
  unfold juDelF juGetF at h
  cases hg : getF mug b a with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    simp only [Option.map_some, Option.bind_some] at h
    cases hd : delInF mug c (unUnit g) with
    | none => rw [hd] at h; cases h
    | some e =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      have hju := ju_get_gate ctx hc ju.battery b a g hg
      obtain ⟨hby, hin, hs, hgo, hmo⟩ := hc
      nock_open ju.del.battery
      by_cases e0 : e = A 0
      · subst e0
        simp only [if_true] at h
        simp [nock_exec, hby, hin, by_arm, in_arm, hju, del_arm, del_in_arm,
          del_in_gate ctx ⟨hgo, hmo⟩ c (unUnit g) _ hd, del_gate ctx ⟨hgo, hmo⟩ b a out h]
      · simp only [e0, if_false] at h
        have e0' : ¬ (A 0 = e) := Ne.symm e0
        simp [nock_exec, hby, hin, by_arm, in_arm, hju, del_in_arm, put_arm, e0',
          del_in_gate ctx ⟨hgo, hmo⟩ c (unUnit g) e hd, put_gate ctx ⟨hgo, hmo⟩ b e a out h]

theorem ju_gas_loop {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) :
    ∀ (l : List (Noun × Noun)) (a out : Noun), juGasF mug a l = some out →
      nock (C ju.gas.loop (C ju.gas.battery (C (listN (l.map pairNoun)) (C ju.battery (C a ctx)))))
        ju.gas.loop = some out := by
  intro l
  induction l with
  | nil =>
    intro a out h
    cases h
    nock_open ju.gas.loop
    simp [nock_exec]
  | cons x rest ih =>
    intro a out h
    obtain ⟨b, c⟩ := x
    simp only [juGasF] at h
    cases hp : juPutF mug b c a with
    | none => rw [hp] at h; cases h
    | some a' =>
      rw [hp] at h
      nock_open ju.gas.loop
      simp [nock_exec, pairNoun, ju_put_gate ctx hc b c a a' hp, ih a' out h]

/-! ## On jugs -/

/-- `+get:ju` on a map: the set under the key, or `~`. -/
theorem ju_get {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (a b : Noun)
    (h : IsMap mug a) :
    (∀ s, Get a b s →
      Eval (C ju.get.battery (C b (C ju.battery (C a ctx)))) ju.get.battery s) ∧
    ((∀ s, ¬ Get a b s) →
      Eval (C ju.get.battery (C b (C ju.battery (C a ctx)))) ju.get.battery (A 0)) :=
  ⟨fun s hs => eval_of_nock (by rw [ju_get_gate ctx hc ju.battery b a _ (getF_some h hs)]; rfl),
   fun hn => eval_of_nock (by rw [ju_get_gate ctx hc ju.battery b a _ (getF_none h hn)]; rfl)⟩

open Classical in
theorem juGetF_some {mug : Noun → Nat} {a b : Noun} (h : IsMap mug a) :
    juGetF mug b a = some (if hx : ∃ s, Get a b s then hx.choose else A 0) := by
  unfold juGetF
  by_cases hx : ∃ s, Get a b s
  · rw [getF_some h hx.choose_spec, dif_pos hx]; rfl
  · rw [getF_none h (fun s hs => hx ⟨s, hs⟩), dif_neg hx]; rfl

open Classical in
/-- `+put:ju` on a map whose values are sets: the set under `b` gains `c`,
and the other pairs stay. -/
theorem ju_put {mug : Noun → Nat} (ctx : Noun) (hc : JuIn mug ctx) (a b c : Noun)
    (h : IsMap mug a) (hs : ∀ s, Get a b s → IsSet mug s) :
    ∃ out e,
      Eval (C ju.put.battery (C (C b c) (C ju.battery (C a ctx)))) ju.put.battery out ∧
      IsMap mug out ∧ IsSet mug e ∧
      (∀ k, Has e k ↔ k = c ∨ ∃ s, Get a b s ∧ Has s k) ∧
      ∀ k v, Get out k v ↔ (k = b ∧ v = e) ∨ (k ≠ b ∧ Get a k v) := by
  obtain ⟨d, hd⟩ : ∃ d, d = (if hx : ∃ s, Get a b s then hx.choose else A 0) := ⟨_, rfl⟩
  have hdset : IsSet mug d := by
    rw [hd]; split
    · rename_i hx; exact hs _ hx.choose_spec
    · exact IsMap.nil
  have hdhas : ∀ k, Has d k ↔ ∃ s, Get a b s ∧ Has s k := by
    intro k
    rw [hd]; split
    · rename_i hx
      constructor
      · intro hk; exact ⟨_, hx.choose_spec, hk⟩
      · rintro ⟨s, hgs, hk⟩
        rwa [Get.unique h hx.choose_spec hgs]
    · rename_i hx
      constructor
      · intro hk; unfold Has at hk; simp at hk; exact absurd hk Get_atom
      · rintro ⟨s, hgs, _⟩; exact absurd ⟨s, hgs⟩ hx
  obtain ⟨e, hp, he, hhe⟩ := putInF_spec mug d c hdset
  obtain ⟨out, ho, hm, hg⟩ := putF_spec mug a b e h
  refine ⟨out, e, eval_of_nock (ju_put_gate ctx hc b c a out ?_), hm, he, fun k => ?_, hg⟩
  · simp only [juPutF, juGetF_some h, ← hd, Option.bind_some, hp, ho]
  · rw [hhe, hdhas]

end Hoon
end Formalization

end
