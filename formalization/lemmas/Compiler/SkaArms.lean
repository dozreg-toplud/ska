import lemmas.Compiler.SkaCore
import lemmas.Compiler.TreapSet
import lemmas.Compiler.CapeSize
import lemmas.Hoon.SetFolds

/-!
# `+dirty`, `+sweep` and `+cull` of the core of `+ska-callgraph`

The arms `94`, `93` and `10` of the core `K` (`SkaCore.lean`), each against
its model in `Ska/Analysis.lean`, in every context `K` with `ana` at axis
`31`, through which they read the library's layers (`K_layer1`, `K_layer2`).

`+dirty` runs `~(any in callees:(git-g g.st m))` with a gate that slams
`+gte` of layer 1 on `chg` of `~(gut by ticks.st)`.  The gate crashes on a
noun that is no callee entry, so `+any:in` is taken here with a test that
holds only on the members of the set (`any_in_loop_on`), and the members of
the set's noun are the encoded entries (`mem_preorder_setNoun`), which gives
the `List.any` over `Treap.tap` of the model (`dirty_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## The layers through `ana` -/

/-- Layer 1 in the core `K`, through `ana` at its axis `31`. -/
theorem K_layer1 {K : Noun} (h : slot? 31 K = some ana) : slot? 262143 K = some layer1 := by
  have h' : slot? 31 K = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 13
  simp only [show 2 ^ 13 * (31 + 1) - 1 = 262143 from rfl,
    show 2 ^ 13 * (1 + 1) - 1 = 16383 from rfl] at this
  rw [this]; exact ana_layer1

/-! ## `+gut:by` on a finite map -/

/-- `+gut:by` on the noun of a `FinMap`, with the noun of a default. -/
theorem gut_finMap {κ ν : Type} [DecidableEq κ] [TKey κ] (l2 : Noun)
    (hc : FallIn l2 ∧ SomeIn l2 ∧ GorIn mugF l2) (f : ν → Noun) (m : FinMap κ ν) (k : κ) (d : ν) :
    nock (C by.gut.battery (C (C (TKey.enc k) (f d)) (C by.battery (C (m.toNoun f) l2)))) by.gut.battery
      = some (f ((m.get k).getD d)) := by
  have hg := FinMap.getF_toNoun f m k
  cases e : m.get k with
  | none =>
    rw [e] at hg
    simp only [unitNoun] at hg
    rw [gut_gate l2 hc _ _ _ _ hg (Or.inl rfl)]
    simp
  | some v =>
    rw [e] at hg
    simp only [unitNoun] at hg
    rw [gut_gate l2 hc _ _ _ _ hg (Or.inr ⟨_, rfl⟩)]
    simp

/-! ## `+any:in` with a test that holds on the members -/

/-- The loop of `+any:in`, with a gate whose test is known only on the
members of the set. -/
theorem any_in_loop_on (B ctx fp fs fc : Noun) (g : Noun → Bool) :
    ∀ (a : Noun), Tree a → (∀ x ∈ preorder a, nock (C fp (C x fc)) fp = some (loob (g x))) →
      nock (C in.any.loop (C in.any.battery (C (C fp (C fs fc)) (C B (C a ctx))))) in.any.loop
        = some (loob ((preorder a).any g)) := by
  intro a ha
  induction ha with
  | nil =>
    intro _
    nock_open in.any.loop
    simp [nock_exec, preorder]
  | @node n l r _ _ ihl ihr =>
    intro hg
    have hn := hg n (by simp [preorder])
    have hl := ihl (fun x hx => hg x (by simp [preorder, hx]))
    have hr := ihr (fun x hx => hg x (by simp [preorder, hx]))
    nock_open in.any.loop
    cases e1 : g n <;> cases e2 : (preorder l).any g <;> cases e3 : (preorder r).any g <;>
      rw [e1] at hn <;> rw [e2] at hl <;> rw [e3] at hr <;>
      simp [nock_exec, preorder, hn, hl, hr, e1, e2, e3, List.any_append, loob]

@[nock_exec] theorem any_in_arm (d : Noun) :
    nock d in.any.arm = some (C in.any.battery (C (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0)))) d)) := by
  nock_open in.any.arm; simp only [nock_exec]

/-- The gate of `+any:in` slammed on a gate whose test is known on the
members. -/
theorem any_in_gate_on (B ctx fp fs fc : Noun) (g : Noun → Bool) (a : Noun) (ha : Tree a)
    (hg : ∀ x ∈ preorder a, nock (C fp (C x fc)) fp = some (loob (g x))) :
    nock (C in.any.battery (C (C fp (C fs fc)) (C B (C a ctx)))) in.any.battery
      = some (loob ((preorder a).any g)) := by
  nock_open in.any.battery
  simp only [nock_exec, any_in_loop_on B ctx fp fs fc g a ha hg]

/-! ## The members of a set's noun -/

theorem mem_preorder_setNoun {κ : Type} [TKey κ] (m : FinMap κ Unit) (x : Noun) :
    x ∈ preorder m.setNoun ↔ ∃ k, m.1 k = some () ∧ x = TKey.enc k := by
  rw [mem_preorder_tapList, mem_tapList_set (FinMap.isSet_setNoun m), FinMap.has_setNoun]

/-- A `List.any` over the pre-order of a set's noun is the `List.any` over
`Treap.tap` of the set, for a test that decodes the members. -/
theorem any_preorder_setNoun {κ : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ Unit) (g : Noun → Bool)
    (p : κ → Bool) (hg : ∀ k, g (TKey.enc k) = p k) :
    (preorder m.setNoun).any g = (Treap.tap m).any fun e => p e.1 := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hgx⟩
    obtain ⟨k, hk, rfl⟩ := (mem_preorder_setNoun m x).1 hx
    exact ⟨(k, ()), (Treap.mem_tap m k ()).2 hk, by rw [← hg]; exact hgx⟩
  · rintro ⟨⟨k, u⟩, hk, hp⟩
    cases u
    exact ⟨TKey.enc k, (mem_preorder_setNoun m _).2 ⟨k, (Treap.mem_tap m k ()).1 hk, rfl⟩,
      by rw [hg]; exact hp⟩

/-! ## `+dirty` -/

/-- The test of `+dirty` on a callee entry: `(gte chg ran)`, with `chg` read
from `ticks` by `+gut:by`.  It reads `ran` at the head of its context, the
`ticks` of the state below it, and layers 1 and 2 through `ana`. -/
theorem dirty_test (ran : Nat) (dbat mN gN doneN orderN stkN nextN movedN tickN rest K : Noun)
    (hK : slot? 31 K = some ana) (ticks : FinMap Ident (Nat × Nat)) (ce : CalleeEntry) :
    nock (C ska_cg.dirty.gate (C ce.toNoun (C (A ran) (C dbat (C (C mN (C gN (C doneN (C orderN
      (C stkN (C nextN (C movedN (C tickN
        (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) rest))))))))) K)))))
      ska_cg.dirty.gate
      = some (loob (decide (ran ≤ (Treap.gut ticks ce.id (0, 0)).2))) := by
  have hl1 := K_layer1 hK
  have hl2 := K_layer2 hK
  have hgu : nock (C by.gut.battery (C (C (identNoun ce.id) (C (A 0) (A 0)))
      (C by.battery (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) layer2))))
      by.gut.battery = some (C (A (Treap.gut ticks ce.id (0, 0)).1) (A (Treap.gut ticks ce.id (0, 0)).2)) :=
    gut_finMap layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
      (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks ce.id (0, 0)
  have hgte := fun a b => gte_gate layer1 arith_layer1.2.2.2.1 a b
  nock_open ska_cg.dirty.gate
  simp [nock_exec, CalleeEntry.toNoun, hl1, hl2, by_arm, by.arm_at, by.gut.arm_at, gut_arm, hgu,
    gte.arm_at, gte_arm, hgte]

/-- `+dirty`: did the entry of a callee of `m` change since `m` last ran?
As `Ana.dirty`, on every state, in every context `K` with `ana` at axis
`31`. -/
theorem dirty_gate (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (m : Ident)
    (st : SkaState FinMap R) :
    nock (C ska_cg.dirty.battery (C (C (identNoun m) (st.toNoun regsNoun)) K)) ska_cg.dirty.battery
      = some (loob (Ana.dirty m st)) := by
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hl2 := K_layer2 hK
  have hgg := git_g_pill g m
  have hgu : nock (C by.gut.battery (C (C (identNoun m) (C (A 0) (A 0)))
      (C by.battery (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) layer2))))
      by.gut.battery = some (C (A (Treap.gut ticks m (0, 0)).1) (A (Treap.gut ticks m (0, 0)).2)) :=
    gut_finMap layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
      (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks m (0, 0)
  generalize hd : Ana.gitG g m = d at hgg
  obtain ⟨dc, dn, dl, di, ds, dp, dm, da⟩ := d
  have hany := any_in_gate_on in.battery layer2 ska_cg.dirty.gate
    (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))))
    (C (A ((Treap.gut ticks m (0, 0)).1)) (C ska_cg.dirty.battery (C (C (identNoun m)
      (C (Treap.toNoun FDatum.toNoun g) (C (memoNoun done) (C (Treap.toNoun A order)
        (C (listNoun identNoun stk) (C (A next) (C (Treap.setNoun moved) (C (A tick)
          (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks)
            (C (regsNoun regs) stats.toNoun)))))))))) K)))
    (fun x => match (FinMap.decode? x : Option CalleeEntry) with
      | some ce => decide ((Treap.gut ticks m (0, 0)).1 ≤ (Treap.gut ticks ce.id (0, 0)).2)
      | none => false)
    (Treap.setNoun dc) (Tree.of_isSet (FinMap.isSet_setNoun dc)) (by
      intro x hx
      obtain ⟨ce, -, rfl⟩ := (mem_preorder_setNoun dc x).1 hx
      refine (dirty_test _ _ _ _ _ _ _ _ _ _ _ _ hK ticks ce).trans ?_
      simp only [FinMap.decode?_enc])
  have hp := any_preorder_setNoun dc
    (fun x => match (FinMap.decode? x : Option CalleeEntry) with
      | some ce => decide ((Treap.gut ticks m (0, 0)).1 ≤ (Treap.gut ticks ce.id (0, 0)).2)
      | none => false)
    (fun ce => decide ((Treap.gut ticks m (0, 0)).1 ≤ (Treap.gut ticks ce.id (0, 0)).2))
    (fun k => by simp only [FinMap.decode?_enc])
  rw [show Treap.setNoun dc = FinMap.setNoun dc from rfl, hp] at hany
  nock_open ska_cg.dirty.battery
  simp [nock_exec, SkaState.toNoun, hK, hl2, by_arm, by.arm_at, by.gut.arm_at, gut_arm, hgu,
    git_g.arm_at, git_g_arm, hgg, FDatum.toNoun, in_arm, in.arm_at, in.any.arm_at, any_in_arm, Ana.dirty, hd]
  exact hany

/-! ## Lists and sets as nouns -/

theorem listNoun_map_listN {α : Type} (f : α → Noun) : ∀ l : List α, listNoun f l = listN (l.map f)
  | [] => rfl
  | x :: l => by
    show C (f x) (listNoun f l) = appendN (f x :: l.map f) (A 0)
    rw [listNoun_map_listN f l]; rfl

theorem map_cell_inj (z : Noun) : ∀ l1 l2 : List Noun,
    l1.map (fun n => C n z) = l2.map (fun n => C n z) → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons.injEq, Noun.cell.injEq, and_true] at h
    rw [h.1, map_cell_inj z l1 l2 h.2]

/-- `~(tap in ...)` of the noun of a set lists `Treap.tap` of the set. -/
theorem tapList_setNoun {κ : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ Unit) :
    tapList (FinMap.setNoun m) = (Treap.tap m).map fun e => TKey.enc e.1 := by
  apply map_cell_inj (A 0)
  rw [← tapList_toMap, FinMap.toMap_setNoun, FinMap.tapList_toNoun, List.map_map]
  rfl

theorem tap_in_setNoun {κ : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ Unit) :
    nock (C in.battery (C (Treap.setNoun m) layer2)) by.tap.arm
      = some (listN ((Treap.tap m).map fun e => TKey.enc e.1)) := by
  show nock (C in.battery (C (FinMap.setNoun m) layer2)) by.tap.arm = _
  rw [← tapList_setNoun, tap_arm, tap_loop, show A 0 = listN [] from rfl,
    tapF_list (Tree.of_isSet (FinMap.isSet_setNoun m)), List.append_nil]

theorem has_in_setNoun {κ : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ Unit) (k : κ) :
    nock (C in.has.battery (C (TKey.enc k) (C in.battery (C (Treap.setNoun m) layer2)))) in.has.battery
      = some (loob (Treap.has m k)) := by
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mugF (FinMap.setNoun m) (TKey.enc k) (FinMap.isSet_setNoun m)
  show nock (C in.has.battery (C (TKey.enc k) (C in.battery (C (FinMap.setNoun m) layer2)))) in.has.battery = _
  rw [has_in_gate layer2 gorIn_morIn_layer2.1 _ _ t ht]
  congr 2
  apply Bool.eq_iff_iff.2
  rw [hiff, FinMap.has_setNoun]
  constructor
  · rintro ⟨k', h1, h2⟩
    rw [TKey.enc_inj _ _ h2.symm] at h1
    show (m.1 k).isSome = true
    rw [h1]; rfl
  · intro h
    refine ⟨k, ?_, rfl⟩
    show m.1 k = some ()
    revert h
    show (m.1 k).isSome = true → m.1 k = some ()
    cases m.1 k <;> simp

theorem put_in_setNoun {κ : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ Unit) (k : κ) :
    nock (C in.put.battery (C (TKey.enc k) (C in.battery (C (Treap.setNoun m) layer2)))) in.put.battery
      = some (Treap.setNoun (Treap.ins m k)) :=
  put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (FinMap.putInF_setNoun m k)

/-! ## `+sweep` -/

/-- The gate `kids` of `+sweep`: the identities of the callees of `i`, in the
order of `~(tap in ...)`, as `Ana.kids`.  Its context is the subject of
`+sweep`, `[sweep-battery [[id [was st]] K]]`. -/
theorem kids_gate (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (sbat idN wasN : Noun)
    (st : SkaState FinMap R) (i : Ident) :
    nock (C ska_cg.sweep.gate (C (identNoun i) (C sbat (C (C idN (C wasN (st.toNoun regsNoun))) K))))
      ska_cg.sweep.gate = some (listNoun identNoun (Ana.kids st i)) := by
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hl2 := K_layer2 hK
  have hgg := git_g_pill g i
  generalize hd : Ana.gitG g i = d at hgg
  obtain ⟨dc, dn, dl, di, ds, dp, dm, da⟩ := d
  have htap := tap_in_setNoun dc
  have hturn := turn_gate layer2 homoIn_layer2 (C (A 0) (A 13))
    (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))))
    (C ska_cg.sweep.gate (C (identNoun i) (C sbat (C (C idN (C wasN
      (SkaState.toNoun regsNoun ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩))) K))))
    (fun x => match x with | Noun.cell _ b => b | _ => A 0)
    ((Treap.tap dc).map fun e => TKey.enc e.1) (by
      intro x hx
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, TKey.enc, CalleeEntry.toNoun])
  rw [List.map_map] at hturn
  have hk : Ana.kids ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ i
      = (Treap.tap dc).map fun e => e.1.id := by
    simp only [Ana.kids, hd]
  rw [hk, listNoun_map_listN, List.map_map]
  nock_open ska_cg.sweep.gate
  simp [nock_exec, SkaState.toNoun, hl2, hK, git_g.arm_at, git_g_arm, hgg, FDatum.toNoun, in_arm,
    in.arm_at, in.tap.arm_at, htap, turn.arm_at, turn_arm] at hturn ⊢
  rw [hturn]
  rfl

end Compiler
end Formalization
