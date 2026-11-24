import lemmas.Compiler.SkaArms
import lemmas.Hoon.DifIn
import lemmas.Hoon.ListsMore
import lemmas.KernelRfl

/-!
# `+cull` of the core of `+ska-callgraph`

The arm `10` of the core `K` (`SkaCore.lean`) against `Ana.cull`, in every
context `K` with `ana` at axis `31`.

```hoon
++  cull
  |=  [id=identity st=ska-state]
  ^-  ska-state
  =/  members=(set identity)  (silt (above id stk.st))
  =/  live=(set identity)  ...                      ::  the loop live
  =/  dead=(set identity)  (~(dif in members) live)
  ?:  =(~ dead)  st
  =.  culled.stats.st  (add culled.stats.st ~(wyt in dead))
  =.  stk.st  (skip stk.st ~(has in dead))
  =.  moved.st  (~(dif in moved.st) dead)
  %-  ~(rep in dead)
  |=  [i=identity =_st]
  %=  st
    order  (~(del by order.st) i)
    ticks  (~(del by ticks.st) i)
    g      (~(del by g.st) i)
  ==
```

The generator names no noun of `+silt` (arm `767` of layer 2), so it is
defined here (`siltArm`, `silt_arm_at`, checked by the kernel); it is wanted
as `silt.*` at the next regeneration.  `+silt` is `+gas:in` from `~`.
The sample of the gate of `+rep` is `[*identity st]`; the bunt of
`identity` is computed by the mold at arm `186` of the tail of `ana`
(`identBunt`, `mold_bunt`, by the kernel through `evalFuel`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## `+silt` -/

/-- The battery of the gate `+silt`. -/
def siltBattery : Noun := C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 15)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))))

/-- The arm `+silt` of layer 2. -/
def siltArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) siltBattery) (C (A 0) (A 1))))

theorem silt_arm_at : slot? 767 layer2 = some siltArm := by kernel_rfl

@[nock_exec] theorem silt_arm (d : Noun) : nock d siltArm = some (C siltBattery (C (A 0) d)) := by
  unfold siltArm; simp only [nock_exec]

theorem gas_in_gate (l : List Noun) (a out : Noun) (h : gasInF mugF a l = some out) :
    nock (C in.gas.battery (C (listN l) (C in.battery (C a layer2)))) in.gas.battery = some out := by
  nock_open in.gas.battery
  simp only [nock_exec, gas_in_loop layer2 gorIn_morIn_layer2 l a out h]

/-- `+silt` is `+gas:in` from the empty set. -/
theorem silt_gate (l : List Noun) (out : Noun) (h : gasInF mugF (A 0) l = some out) :
    nock (C siltBattery (C (listN l) layer2)) siltBattery = some out := by
  have hg := gas_in_gate l (A 0) out h
  unfold siltBattery
  simp [nock_exec, in_arm, in.arm_at, in.gas.arm_at, gas_in_arm, hg]

/-! ## Sets of identities as nouns -/

theorem get_foldl_ins : ∀ (l : List Ident) (m : FinMap Ident Unit) (k : Ident),
    Treap.get (l.foldl Treap.ins m) k = some () ↔ k ∈ l ∨ Treap.get m k = some ()
  | [], m, k => by simp
  | x :: l, m, k => by
    rw [List.foldl_cons, get_foldl_ins l (Treap.ins m x) k]
    show k ∈ l ∨ Treap.get (Treap.put m x ()) k = some () ↔ _
    rw [Treap.get_put]
    by_cases e : k = x
    · subst e; simp
    · simp [e]

/-- `+silt` of a list of identities is the noun of `Treap.silt`. -/
theorem silt_setNoun (l : List Ident) :
    gasInF mugF (A 0) (l.map identNoun) = some (Treap.setNoun (Treap.silt l : FinMap Ident Unit)) := by
  obtain ⟨out, h, hs, hh⟩ := gasInF_spec (mug := mugF) (l.map identNoun) (A 0) isSet_nil
  rw [h]
  congr 1
  apply isSet_ext hs (FinMap.isSet_setNoun _)
  intro kn
  rw [hh, FinMap.has_setNoun]
  have e := get_foldl_ins l Treap.empty
  simp only [Treap.get_empty] at e
  constructor
  · rintro (h | h)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      exact ⟨k, (e k).2 (Or.inl hk), rfl⟩
    · exact absurd h not_has_atom
  · rintro ⟨k, hk, rfl⟩
    have hk' : k ∈ l := by
      rcases (e k).1 hk with h | h
      · exact h
      · cases h
    exact Or.inl (List.mem_map.2 ⟨k, hk', rfl⟩)

theorem get_foldl_del (k : Ident) : ∀ (L : List (Ident × Unit)) (s : FinMap Ident Unit),
    Treap.get (L.foldl (fun s k => Treap.del s k.1) s) k
      = if k ∈ L.map Prod.fst then none else Treap.get s k
  | [], s => by simp
  | x :: L, s => by
    rw [List.foldl_cons, get_foldl_del k L, Treap.get_del]
    by_cases e : k = x.1
    · simp [e]
    · by_cases h : k ∈ L.map Prod.fst <;> simp [e, h]

theorem get_dif (a b : FinMap Ident Unit) (k : Ident) :
    Treap.get (Treap.dif a b) k = if Treap.has b k then none else Treap.get a k := by
  unfold Treap.dif
  rw [get_foldl_del]
  congr 1
  apply propext
  simp only [List.mem_map, Treap.has]
  constructor
  · rintro ⟨⟨k', u⟩, hk, rfl⟩
    cases u
    rw [(Treap.mem_tap b k' ()).1 hk]; rfl
  · intro h
    cases e : Treap.get b k with
    | none => rw [e] at h; cases h
    | some u => cases u; exact ⟨(k, ()), (Treap.mem_tap b k ()).2 e, rfl⟩

/-- `+dif:in` of two sets of identities is the noun of `Treap.dif`. -/
theorem dif_setNoun (a b : FinMap Ident Unit) :
    difInF mugF (Treap.setNoun a) (Treap.setNoun b) = some (Treap.setNoun (Treap.dif a b)) := by
  obtain ⟨out, h, hs, hh⟩ := difInF_spec (FinMap.isSet_setNoun b) _ (FinMap.isSet_setNoun a)
  show difInF mugF (FinMap.setNoun a) (FinMap.setNoun b) = _
  rw [h]
  congr 1
  apply isSet_ext hs (FinMap.isSet_setNoun _)
  intro kn
  rw [hh, FinMap.has_setNoun, FinMap.has_setNoun, FinMap.has_setNoun]
  have hd := get_dif a b
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hn⟩
    refine ⟨k, ?_, rfl⟩
    show Treap.get (Treap.dif a b) k = some ()
    rw [hd]
    have : Treap.has b k = false := by
      cases e : Treap.has b k
      · rfl
      · exfalso; apply hn
        refine ⟨k, ?_, rfl⟩
        simp only [Treap.has] at e
        cases e' : Treap.get b k with
        | none => rw [e'] at e; cases e
        | some u => cases u; exact e'
    rw [this]; exact hk
  · rintro ⟨k, hk, rfl⟩
    have hk' : Treap.get (Treap.dif a b) k = some () := hk
    rw [hd] at hk'
    cases e : Treap.has b k
    · rw [e] at hk'
      refine ⟨⟨k, hk', rfl⟩, ?_⟩
      rintro ⟨k', hk'', he⟩
      rw [← TKey.enc_inj _ _ he] at hk''
      have : Treap.has b k = true := by
        show (Treap.get b k).isSome = true
        rw [show Treap.get b k = b.1 k from rfl, hk'']; rfl
      rw [e] at this; cases this
    · rw [e] at hk'; simp at hk'

/-- The noun of a set is `~` exactly when the set is empty. -/
theorem setNoun_nil_iff (m : FinMap Ident Unit) : Treap.setNoun m = A 0 ↔ Treap.tap m = [] := by
  constructor
  · intro h
    have e := tapList_setNoun m
    rw [show FinMap.setNoun m = Treap.setNoun m from rfl, h] at e
    simp [tapList] at e
    exact e
  · intro h
    apply isSet_ext (FinMap.isSet_setNoun m) isSet_nil
    intro kn
    rw [FinMap.has_setNoun]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have := (Treap.mem_tap m k ()).2 hk
      rw [h] at this; cases this
    · intro h'; exact absurd h' not_has_atom

theorem preorder_toMap : ∀ a : Noun, preorder (toMap a) = (preorder a).map (fun n => C n (A 0))
  | Noun.atom k => by simp [preorder]
  | Noun.cell n (Noun.atom k) => by simp [preorder]
  | Noun.cell n (Noun.cell l r) => by
    rw [toMap_node]
    simp only [preorder, preorder_toMap l, preorder_toMap r, List.map_cons, List.map_append]

/-- The pre-order of `+rep` on the noun of a set lists `Treap.rap` of it. -/
theorem preorder_setNoun (m : FinMap Ident Unit) :
    preorder (Treap.setNoun m) = (Treap.rap m).map fun e => identNoun e.1 := by
  apply map_cell_inj (A 0)
  rw [← preorder_toMap, show Treap.setNoun m = FinMap.setNoun m from rfl, FinMap.toMap_setNoun,
    FinMap.preorder_toNoun, List.map_map]
  rfl

theorem length_preorder : ∀ a : Noun, (preorder a).length = (tapList a).length
  | Noun.atom k => by simp [preorder, tapList]
  | Noun.cell n (Noun.atom k) => by simp [preorder, tapList]
  | Noun.cell n (Noun.cell l r) => by
    simp only [preorder, tapList, List.length_cons, List.length_append, length_preorder l,
      length_preorder r]
    omega

theorem wyt_setNoun (m : FinMap Ident Unit) : (preorder (Treap.setNoun m)).length = Treap.wyt m := by
  rw [length_preorder, show Treap.setNoun m = FinMap.setNoun m from rfl, tapList_setNoun, List.length_map]
  rfl

/-! ## The bunt of `identity` -/

/-- The bunt of `identity`, as the mold at arm `186` of the tail of `ana`
computes it. -/
def identBunt : Noun := C (C (A 1) (A 0)) (C (A 0) (A 0))

/-- The formula of `+cull` that computes the bunt, kept whole so that `simp`
does not take it apart. -/
def buntF : Noun := C (A 7) (C (C (A 9) (C (A 186) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

theorem nock_buntF_cons (s d : Noun) :
    nock s (C buntF d) = (nock s buntF).bind fun x => (nock s d).bind fun y => some (C x y) := by
  unfold buntF; rw [nock_cell]

theorem mold_bunt_ana :
    nock ana (C (A 7) (C (C (A 9) (C (A 186) (C (A 0) (A 3)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
      = some identBunt :=
  nock_of_evalFuel (fuel := 300) (by kernel_rfl)

theorem mold_bunt (X : Noun) (h : slot? 2047 X = slot? 3 ana) : nock X buntF = some identBunt := by
  have e := mold_bunt_ana
  unfold buntF
  rw [nock_op7, nock_op9, nock_op0, h]
  rw [nock_op7, nock_op9, nock_op0] at e
  exact e

/-! ## The gate of `+rep` -/

/-- What the gate of `+rep` in `+cull` does to the state for one member. -/
noncomputable def cullDel (st : SkaState FinMap R) (i : Ident) : SkaState FinMap R :=
  { st with order := Treap.del st.order i, ticks := Treap.del st.ticks i, g := Treap.del st.g i }

/-- The gate of `+rep` in `+cull`: three `+del:by`, on every state, in a
context `ctx` that holds layer 2 at its axis `0x3fffff`. -/
theorem cull_rep_gate (regsNoun : R → Noun) (ctx : Noun) (hl2 : slot? 0x3fffff ctx = some layer2)
    (i : Ident) (st : SkaState FinMap R) :
    nock (C ska_cg.cull.gate (C (C (identNoun i) (st.toNoun regsNoun)) ctx)) ska_cg.cull.gate
      = some ((cullDel st i).toNoun regsNoun) := by
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hdo : nock (C by.del.battery (C (identNoun i) (C by.battery (C (Treap.toNoun A order) layer2))))
      by.del.battery = some (Treap.toNoun A (Treap.del order i)) :=
    del_gate layer2 gorIn_morIn_layer2 _ _ _ (FinMap.delF_toNoun A order i)
  have hdt : nock (C by.del.battery (C (identNoun i) (C by.battery
      (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) layer2))))
      by.del.battery = some (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) (Treap.del ticks i)) :=
    del_gate layer2 gorIn_morIn_layer2 _ _ _ (FinMap.delF_toNoun _ ticks i)
  have hdg : nock (C by.del.battery (C (identNoun i) (C by.battery (C (Treap.toNoun FDatum.toNoun g) layer2))))
      by.del.battery = some (Treap.toNoun FDatum.toNoun (Treap.del g i)) :=
    del_gate layer2 gorIn_morIn_layer2 _ _ _ (FinMap.delF_toNoun FDatum.toNoun g i)
  nock_open ska_cg.cull.gate
  simp [nock_exec, SkaState.toNoun, hl2, by_arm, by.arm_at, by.del.arm_at, hdo, hdt, hdg, cullDel]

/-- The loop of `+rep` with a gate known on the nodes of the tree and on the
accumulators `toN s`. -/
theorem rep_loop_on {σ : Type} (toN : σ → Noun) (gf : Noun → σ → σ) (B ctx bp e bc : Noun) :
    ∀ (a : Noun), Tree a → ∀ (s : σ),
    (∀ x ∈ preorder a, ∀ s, nock (C bp (C (C x (toN s)) bc)) bp = some (toN (gf x s))) →
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e (toN s)) bc)) (C B (C a ctx)))))
      by.rep.loop = some (toN ((preorder a).foldl (fun s x => gf x s) s)) := by
  intro a ha
  induction ha with
  | nil =>
    intro s _
    nock_open by.rep.loop
    simp [nock_exec, preorder]
  | @node n l r _ _ ihl ihr =>
    intro s hf
    have hn := hf n (by simp [preorder]) s
    have hl := ihl (gf n s) (fun x hx s => hf x (by simp [preorder, hx]) s)
    have hr := fun s' => ihr s' (fun x hx s => hf x (by simp [preorder, hx]) s)
    nock_open by.rep.loop
    simp [nock_exec, preorder, hn, hl, hr, List.foldl_append]

theorem rep_gate_on {σ : Type} (toN : σ → Noun) (gf : Noun → σ → σ) (B ctx bp e bc : Noun)
    (a : Noun) (ha : Tree a) (s : σ)
    (hf : ∀ x ∈ preorder a, ∀ s, nock (C bp (C (C x (toN s)) bc)) bp = some (toN (gf x s))) :
    nock (C by.rep.battery (C (C bp (C (C e (toN s)) bc)) (C B (C a ctx)))) by.rep.battery
      = some (toN ((preorder a).foldl (fun s x => gf x s) s)) := by
  nock_open by.rep.battery
  simp only [nock_exec, rep_loop_on toN gf B ctx bp e bc a ha s hf]

/-! ## The battery of `+cull` -/

theorem kc_above_at : slot? 14 ska_cg.k_bat = some ska_cg.above.arm := by kernel_rfl

theorem slot_K22 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 22 K = some ska_cg.above.arm := by
  cases K with
  | atom n => simp [nock_exec] at h
  | cell b t =>
    have hb : b = ska_cg.k_bat := by simpa [nock_exec] using h
    subst hb
    simp only [nock_exec]

@[nock_exec] theorem above_arm (d : Noun) :
    nock d ska_cg.above.arm = some (C ska_cg.above.battery (C (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0)) d)) := by
  nock_open ska_cg.above.arm; simp only [nock_exec]

@[nock_exec] theorem skip_arm (d : Noun) :
    nock d skip.arm = some (C skip.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) d)) := by
  nock_open skip.arm; simp only [nock_exec]

theorem K_tail63 {K : Noun} (h : slot? 31 K = some ana) : slot? 63 K = slot? 3 ana := by
  have h' : slot? 31 K = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 1
  simp only [show 2 ^ 1 * (31 + 1) - 1 = 63 from rfl, show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  exact this

/-- The tail of `ana`. -/
noncomputable def anaTail : Noun := (slot? 3 ana).getD (A 0)

theorem ana_tail : slot? 3 ana = some anaTail := by kernel_rfl

theorem mold_bunt' (T X : Noun) (hT : slot? 3 ana = some T) (h : slot? 2047 X = some T) :
    nock X buntF = some identBunt :=
  mold_bunt X (by rw [h, hT])

theorem decode_ident (i : Ident) : (FinMap.decode? (identNoun i) : Option Ident) = some i :=
  FinMap.decode?_enc i

/-- One step of the `+rep` of `+cull` on a node of the set's noun. -/
noncomputable def cullStep (x : Noun) (s : SkaState FinMap R) : SkaState FinMap R :=
  match (FinMap.decode? x : Option Ident) with
  | some i => cullDel s i
  | none => s

theorem foldl_cullStep (dead : FinMap Ident Unit) (st0 : SkaState FinMap R) :
    (preorder (Treap.setNoun dead)).foldl (fun s x => cullStep x s) st0
      = (Treap.rap dead).foldl (fun st i => cullDel st i.1) st0 := by
  rw [preorder_setNoun, List.foldl_map]
  congr 1
  funext s e
  simp only [cullStep, show identNoun e.1 = TKey.enc e.1 from rfl, FinMap.decode?_enc]

/-- `+rep` of the gate of `+cull` over the noun of `dead`, in a context that
holds layer 2 at `0x3fffff`. -/
theorem cull_rep (regsNoun : R → Noun) (dead : FinMap Ident Unit) (st0 : SkaState FinMap R) (ctx : Noun)
    (hc : slot? 0x3fffff ctx = some layer2) :
    nock (C by.rep.battery (C (C ska_cg.cull.gate (C (C identBunt (st0.toNoun regsNoun)) ctx))
      (C in.battery (C (Treap.setNoun dead) layer2)))) by.rep.battery
      = some (((Treap.rap dead).foldl (fun st i => cullDel st i.1) st0).toNoun regsNoun) := by
  rw [rep_gate_on (SkaState.toNoun regsNoun) cullStep in.battery layer2 ska_cg.cull.gate identBunt ctx
    (Treap.setNoun dead) (Tree.of_isSet (FinMap.isSet_setNoun dead)) st0 (by
      intro x hx s
      rw [preorder_setNoun] at hx
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
      rw [cull_rep_gate regsNoun ctx hc e.1 s]
      simp only [cullStep, show identNoun e.1 = TKey.enc e.1 from rfl, FinMap.decode?_enc]),
    foldl_cullStep]

/-- `+skip` of the stack with `~(has in dead)`. -/
theorem cull_skip (dead : FinMap Ident Unit) (stk : List Ident) :
    nock (C skip.battery (C (C (listNoun identNoun stk) (C in.has.battery (C (A 0)
      (C in.battery (C (Treap.setNoun dead) layer2))))) layer2)) skip.battery
      = some (listNoun identNoun (stk.filter (fun i => !Treap.has dead i))) := by
  rw [listNoun_map_listN, listNoun_map_listN, skip_gate layer2 in.has.battery (A 0)
    (C in.battery (C (Treap.setNoun dead) layer2))
    (fun x => match (FinMap.decode? x : Option Ident) with | some i => Treap.has dead i | none => false) _ (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      have h := has_in_setNoun dead i
      rw [show identNoun i = TKey.enc i from rfl, h, FinMap.decode?_enc])]
  simp [List.filter_map, Function.comp_def, decode_ident]

/-- The subject of `+cull` as its gate is slammed. -/
noncomputable def cullS0 (regsNoun : R → Noun) (K : Noun) (id : Ident) (st : SkaState FinMap R) : Noun :=
  C ska_cg.cull.battery (C (C (identNoun id) (st.toNoun regsNoun)) K)

/-- What `+cull` does after the loop `live`. -/
noncomputable def cullEnd (st : SkaState FinMap R) (members live : FinMap Ident Unit) : SkaState FinMap R :=
  let dead := Treap.dif members live
  if Treap.tap dead = [] then st else
  (Treap.rap dead).foldl (fun st i => cullDel st i.1)
    { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt dead },
              stk := st.stk.filter (fun i => !Treap.has dead i),
              moved := Treap.dif st.moved dead }

theorem cull_eq (n : Nat) (id : Ident) (st : SkaState FinMap R) :
    Ana.cull n id st = (Ana.above id st.stk).bind fun ab =>
      (liveLoop st (Treap.silt ab) n [id] Treap.empty).map (cullEnd st (Treap.silt ab)) := rfl

set_option maxHeartbeats 4000000 in
/-- The battery of `+cull` after `+above` returned `ab`, given what the loop
`live` returns. -/
theorem cull_run (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana)
    (hKb : slot? 2 K = some ska_cg.k_bat) (id : Ident) (st : SkaState FinMap R) (ab : List Ident)
    (hab : Ana.above id st.stk = some ab) (o : Option (FinMap Ident Unit))
    (hl : nock (liveSubj regsNoun K id st (Treap.silt ab) [id] Treap.empty) ska_cg.cull.loop
      = o.map Treap.setNoun) :
    nock (cullS0 regsNoun K id st) ska_cg.cull.battery
      = (o.map (cullEnd st (Treap.silt ab))).map (SkaState.toNoun regsNoun) := by
  have hl1 := K_layer1 hK
  have hl2 := K_layer2 hK
  have hK22 := slot_K22 hKb
  have hK63 : slot? 63 K = some anaTail := by rw [K_tail63 hK, ana_tail]
  have hbunt := mold_bunt' anaTail
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
  simp only at hab
  have habv := above_gate K id stk
  rw [hab] at habv
  have hsilt : nock (C siltBattery (C (listNoun identNoun ab) layer2)) siltBattery
      = some (Treap.setNoun (Treap.silt ab : FinMap Ident Unit)) := by
    rw [listNoun_map_listN]; exact silt_gate _ _ (silt_setNoun ab)
  simp only [liveSubj, listNoun] at hl
  rw [show Treap.setNoun (Treap.empty : FinMap Ident Unit) = A 0 from FinMap.setNoun_empty] at hl
  simp only [SkaState.toNoun, Stats.toNoun, Option.map_some] at hl habv
  generalize hM : (Treap.silt ab : FinMap Ident Unit) = members at hsilt hl
  cases o with
  | none =>
    simp only [Option.map_none] at hl ⊢
    unfold cullS0
    nock_open ska_cg.cull.battery
    simp [nock_exec, SkaState.toNoun, Stats.toNoun, hK22, habv, hl2, silt_arm_at, hsilt, hl]
  | some live =>
    have hdead := dif_in_gate layer2 gorIn_morIn_layer2 _ _ _ (dif_setNoun members live)
    simp only [Option.map_some, cullEnd]
    generalize hD : Treap.dif members live = dead at hdead
    by_cases hd : Treap.tap dead = []
    · have h0 := (setNoun_nil_iff dead).2 hd
      rw [h0] at hdead
      simp only [hd, if_true]
      unfold cullS0
      nock_open ska_cg.cull.battery
      simp [nock_exec, SkaState.toNoun, Stats.toNoun, hK22, habv, hl2, silt_arm_at, hsilt, hl, in_arm,
        in.arm_at, in.dif.arm_at, dif_in_arm, hdead]
    · have h0 : ¬ Treap.setNoun dead = A 0 := fun e => hd ((setNoun_nil_iff dead).1 e)
      have h0' : ¬ A 0 = Treap.setNoun dead := fun e => h0 e.symm
      simp only [hd, if_false]
      have hwyt := wyt_loop layer2 (arith_layer1.1 : Below AddIn layer2) in.battery (Treap.setNoun dead)
        (Tree.of_isSet (FinMap.isSet_setNoun dead))
      rw [wyt_setNoun] at hwyt
      have hadd := add_gate layer1 arith_layer1.1.2 culled (Treap.wyt dead)
      have hskip := cull_skip dead stk
      have hmov := dif_in_gate layer2 gorIn_morIn_layer2 _ _ _ (dif_setNoun moved dead)
      have hrep := cull_rep regsNoun dead
        { g := g, done := done, order := order, stk := stk.filter (fun i => !Treap.has dead i), next := next,
          moved := Treap.dif moved dead, tick := tick, ticks := ticks, regs := regs,
          stats := { runs := runs, passes := passes, lateRuns := lateRuns, misses := misses,
                     culled := culled + Treap.wyt dead } }
        (C (Treap.setNoun dead) (C (Treap.setNoun live) (C (Treap.setNoun members) (C ska_cg.cull.battery
          (C (C (identNoun id) (SkaState.toNoun regsNoun
            { g := g, done := done, order := order, stk := stk.filter (fun i => !Treap.has dead i), next := next,
              moved := Treap.dif moved dead, tick := tick, ticks := ticks, regs := regs,
              stats := { runs := runs, passes := passes, lateRuns := lateRuns, misses := misses,
                         culled := culled + Treap.wyt dead } })) K)))))
        (by simp [nock_exec, hl2])
      simp only [SkaState.toNoun, Stats.toNoun] at hrep
      unfold cullS0
      nock_open ska_cg.cull.battery
      rw [show (C (A 7) (C (C (A 9) (C (A 186) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
        = buntF from rfl]
      simp [nock_exec, SkaState.toNoun, Stats.toNoun, hK22, habv, hl2, hl1, silt_arm_at, hsilt, hl, in_arm,
        in.arm_at, in.dif.arm_at, dif_in_arm, hdead, h0', in.wyt.arm_at, wyt_arm, hwyt, add.arm_at,
        add_arm, hadd, skip.arm_at, skip_arm, hskip, has_in_arm, in.has.arm_at, hmov, in.rep.arm_at, rep_arm,
        nock_buntF_cons, hbunt, ana_tail, hK63, hrep]

/-- The battery of `+cull` crashes when `id` is not on the stack. -/
theorem cull_run_none (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana)
    (hKb : slot? 2 K = some ska_cg.k_bat) (id : Ident) (st : SkaState FinMap R)
    (hab : Ana.above id st.stk = none) :
    nock (cullS0 regsNoun K id st) ska_cg.cull.battery = none := by
  have hl2 := K_layer2 hK
  have hK22 := slot_K22 hKb
  have habv := above_gate K id st.stk
  rw [hab] at habv
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  simp only [Option.map_none] at habv
  unfold cullS0
  nock_open ska_cg.cull.battery
  simp [nock_exec, SkaState.toNoun, hK22, habv, hl2, silt_arm_at]

/-- `+cull` (arm `10` of `K`): the gate returns exactly what `Ana.cull`
returns at some fuel, on every state, in every context `K` with `ana` at axis
`31` and the battery `K_bat`. -/
theorem cull_gate (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana)
    (hKb : slot? 2 K = some ska_cg.k_bat) (id : Ident) (st : SkaState FinMap R) (x : Noun) :
    nock (cullS0 regsNoun K id st) ska_cg.cull.battery = some x ↔
      ∃ n r, Ana.cull n id st = some r ∧ x = r.toNoun regsNoun := by
  constructor
  · intro h
    cases hab : Ana.above id st.stk with
    | none => rw [cull_run_none regsNoun K hK hKb id st hab] at h; cases h
    | some ab =>
      cases hL : nock (liveSubj regsNoun K id st (Treap.silt ab) [id] Treap.empty) ska_cg.cull.loop with
      | none =>
        rw [cull_run regsNoun K hK hKb id st ab hab none hL] at h; cases h
      | some y =>
        obtain ⟨n, live, hn, rfl⟩ := (live_loop_iff regsNoun K hK id st _ [id] Treap.empty y).1 hL
        rw [cull_run regsNoun K hK hKb id st ab hab (some live) hL] at h
        refine ⟨n, cullEnd st (Treap.silt ab) live, ?_, ?_⟩
        · rw [cull_eq, hab]; simp [hn]
        · simp only [Option.map_some, Option.some.injEq] at h; exact h.symm
  · rintro ⟨n, r, hr, rfl⟩
    rw [cull_eq] at hr
    cases hab : Ana.above id st.stk with
    | none => rw [hab] at hr; cases hr
    | some ab =>
      rw [hab] at hr
      simp only [Option.bind_some] at hr
      cases hn : liveLoop st (Treap.silt ab) n [id] Treap.empty with
      | none => rw [hn] at hr; cases hr
      | some live =>
        rw [hn] at hr
        simp only [Option.map_some, Option.some.injEq] at hr
        have hL := (live_loop_iff regsNoun K hK id st _ [id] Treap.empty _).2 ⟨n, live, hn, rfl⟩
        rw [cull_run regsNoun K hK hKb id st ab hab (some live) hL]
        simp only [Option.map_some, hr]

end Compiler
end Formalization
