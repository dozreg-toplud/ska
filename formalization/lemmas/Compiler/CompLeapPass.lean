import lemmas.Compiler.CompLeapNeed
import lemmas.Hoon.ListsSort

/-!
# `+pass` and its helpers, arms of the core `K` of `+comp`

`+pass-bomb` (K `715742`), `+pass-then` (K `86`), `+pass-edit` (K `48046`),
and the mutual pair `+pass` (K `340`) and `+pass-both` (K `94`), all arms of
the core `K` in which `+comp` is defined (`compK`).  They read of `K` each
other, `+gep` (K `5597`) and layer 2 at `65535` (`+turn`, `+murn`, `+zing`,
`+weld`), and of layer 1 behind it `+cap`, `+mas`, `+peg` (`PassIn`, met by
`compK`: `passIn_compK`).

A list of parts `List (Nat × Nat)` is the noun `lN`.  The invariant: no axis
in it is `0` (`PosL`).  On such lists every `+gep` and `+peg` these arms run
has positive axes, so nothing crashes and the model's `Option`s are `some`.
`+pass` takes a nomm with no `%10` at axis `0` (`Bake.NoAx0`, which
`+fol-loop` guarantees: it turns `[10 [0 v] q]` into `[0 0]`); there
`+pass-edit` would run `(peg 0 p)`, a crash, where the model's `pegF` is
total.

Compared with the Hoon part by part: no departure on these inputs.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## Nouns, the invariant, what the arms read -/

/-- The noun of a part `[p s]`. -/
def pN (e : Nat × Nat) : Noun := C (A e.1) (A e.2)

/-- The noun of a list of parts. -/
def lN (l : List (Nat × Nat)) : Noun := listN (l.map pN)

/-- No axis of a list of parts is `0`. -/
def PosL (l : List (Nat × Nat)) : Prop := ∀ e ∈ l, e.1 ≠ 0 ∧ e.2 ≠ 0

/-- What the arms of `+pass` read of the core `K`. -/
def PassIn (K : Noun) : Prop :=
  slot? 65535 K = some layer2 ∧ slot? 5597 K = some gepArm ∧ slot? 715742 K = some pboArm ∧
  slot? 340 K = some pasArm ∧ slot? 86 K = some pthArm ∧ slot? 48046 K = some pedArm ∧
  slot? 94 K = some pbtArm

theorem passIn_compK : PassIn compK :=
  ⟨compK_layer2, compK_gep, pbo_at, pas_at, pth_at, ped_at, pbt_at⟩

theorem pi_layer1 {K : Noun} (hK : PassIn K) : slot? 131071 K = some layer1 := by
  have h := slot_bit 65535 (by decide) 1 (by decide) K
  rw [hK.1] at h
  rw [show (131071 : Nat) = 2 * 65535 + 1 from rfl, h]
  exact (slot_three layer2).symm.trans layer2_layer1

/-- `+gep` of two positive axes does not crash. -/
theorem gep_pos {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) : gep a b = some (gep a b).join := by
  unfold gep
  simp only [ha, hb, ↓reduceIte]
  split <;> (try split) <;> (try split) <;> simp

theorem lq_gep_ss {a l r : Nat} (h : gep a l = some (some r)) : r ≠ 0 := by
  unfold gep at h
  by_cases a0 : a = 0
  · simp [a0] at h
  by_cases l0 : l = 0
  · simp [a0, l0] at h
  by_cases e : a = l
  · simp [a0, l0, e] at h; omega
  by_cases lt : l < a
  · simp [a0, l0, e, lt] at h
  simp only [a0, l0, e, lt, if_false] at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    rw [← h]
    intro h0
    have := (Nat.or_eq_zero_iff.1 h0).2
    have := Nat.two_pow_pos (Hoon.metF 0 l - Hoon.metF 0 a)
    omega

theorem lq_nomm_cell (n : Nomm) : ∃ a b, n.toNoun = C a b := by
  cases n <;> exact ⟨_, _, rfl⟩

theorem gep_join_pos {a b d : Nat} (h : (gep a b).join = some d) : d ≠ 0 := by
  cases e : gep a b with
  | none => rw [e] at h; simp at h
  | some r =>
    rw [e] at h
    simp only [Option.join_some] at h
    subst h
    exact lq_gep_ss e

/-- The gate `+gep` of `K`, on two positive axes. -/
theorem pi_gep {K : Noun} (hK : PassIn K) {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    nock (C gepBat (C (C (A a) (A b)) K)) gepBat = some (unitNoun A (gep a b).join) := by
  rw [gep_gate K hK.1 a b, gep_pos ha hb]; rfl

/-- The gate `+peg` of layer 1, on two positive axes. -/
theorem pi_peg {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    nock (C peg.battery (C (C (A a) (A b)) layer1)) peg.battery = some (A (pegF a b)) :=
  peg_gate layer1 cf_arith a (by omega) b (by omega)

theorem pegF_ne {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) : pegF a b ≠ 0 := by
  have := pegF_pos a (by omega) b (by omega); omega

/-! ## `+turn` and `+murn` over typed lists -/

theorem lq_turn_loop {α β : Type} (E : α → Noun) (F : β → Noun) (c bp bs bc : Noun) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (F (g a))) →
    nock (C turn.loop (C turn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c))) turn.loop
      = some (listN ((l.map g).map F)) := by
  intro l
  induction l with
  | nil => intro _; nock_open turn.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open turn.loop
    simp [nock_exec, hx, hxs]

theorem lq_turn_gate {α β : Type} (E : α → Noun) (F : β → Noun) (c : Noun) (hc : HomoIn c)
    (bp bs bc : Noun) (g : α → β) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (F (g a))) :
    nock (C turn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) turn.battery
      = some (listN ((l.map g).map F)) := by
  nock_open turn.battery
  simp only [nock_exec, hc, homo_arm, lq_turn_loop E F c bp bs bc g l hf]

theorem lq_murn_loop {α β : Type} (E : α → Noun) (F : β → Noun) (c bp bs bc : Noun)
    (g : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (unitNoun F (g a))) →
    nock (C murn.loop (C murn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c))) murn.loop
      = some (listN ((l.filterMap g).map F)) := by
  intro l
  induction l with
  | nil => intro _; nock_open murn.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open murn.loop
    cases e : g x with
    | none => rw [e] at hx; simp [nock_exec, hx, hxs, unitNoun, e, List.filterMap_cons]
    | some b => rw [e] at hx; simp [nock_exec, hx, hxs, unitNoun, e, List.filterMap_cons]

theorem lq_murn_gate {α β : Type} (E : α → Noun) (F : β → Noun) (c : Noun) (hc : HomoIn c)
    (bp bs bc : Noun) (g : α → Option β) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (unitNoun F (g a))) :
    nock (C murn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) murn.battery
      = some (listN ((l.filterMap g).map F)) := by
  nock_open murn.battery
  simp only [nock_exec, hc, homo_arm, lq_murn_loop E F c bp bs bc g l hf]

theorem lq_zing_arm (c : Noun) : nock c zing.arm = some (C zing.battery (C (A 0) c)) := by
  nock_open zing.arm; simp only [nock_exec]

theorem lq_murn_arm (c : Noun) :
    nock c murn.arm = some (C murn.battery (C (C (A 0) buntGate) c)) := by
  nock_open murn.arm; simp only [nock_exec]; rfl

/-- `+zing` of the lists of parts. -/
theorem lq_zing (ls : List (List (Nat × Nat))) :
    nock (C zing.battery (C (listN ((ls.map fun l => l.map pN).map listN)) layer2)) zing.battery
      = some (lN ls.flatten) := by
  rw [zing_gate layer2 welp.arm_at]
  unfold lN
  simp [List.map_flatten]

theorem murnO_some {α β : Type} (f : α → Option (Option β)) (g : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → murnO f l = some (l.filterMap g)
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have hxs := murnO_some f g xs (fun y hy => h y (by simp [hy]))
    simp only [murnO, hx, hxs, Option.bind_some, Option.map_some, List.filterMap_cons]
    cases g x <;> rfl

theorem turnO_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → turnO f l = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have hxs := turnO_some f g xs (fun y hy => h y (by simp [hy]))
    simp only [turnO, hx, hxs, Option.bind_some, Option.map_some, List.map_cons]

/-! ## `+pass-bomb` -/

/-- **`+pass-bomb`** is `passBomb` on every nomm. -/
theorem pbo_gate (K : Noun) : ∀ n : Nomm, nock (C pboBat (C n.toNoun K)) pboBat = some (loob (passBomb n))
  | Nomm.cons p q => by
    obtain ⟨a, b, hab⟩ := lq_nomm_cell p
    nock_open pboBat
    simp [nock_exec, Nomm.toNoun, hab, passBomb, loob]
  | Nomm.n0 ax => by
    nock_open pboBat
    by_cases h : ax = 0
    · subst h; simp [nock_exec, Nomm.toNoun, passBomb, loob, eqCode_self]
    · have h' : ¬ (0 = ax) := fun e => h e.symm
      simp [nock_exec, Nomm.toNoun, passBomb, loob, h, h', eqCode_atom]
  | Nomm.n1 k => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n2 p q info => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n3 p => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n4 p => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n5 p q => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n6 p q r => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n7 p q => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n10 a v q => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.n11s tag q body => by
    have hq := pbo_gate K q
    nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, hq]
  | Nomm.n11d tag h q body => by
    have hq := pbo_gate K q
    nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, hq]
  | Nomm.n12 p q => by nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob]
  | Nomm.mean p b q body k => by
    nock_open pboBat; simp [nock_exec, Nomm.toNoun, passBomb, loob, Tag.mean]

/-! ## `+pass-then` -/

/-- The `murn` gate of `+pass-then` on a part `y = [pp sp]` of `p`, for a
part `x = [pq sq]` of `q`, on positive axes. -/
def ptOne (x y : Nat × Nat) : Option (Nat × Nat) :=
  match (gep y.1 x.2).join with
  | some d => some (x.1, pegF y.2 d)
  | Option.none => match (gep x.2 y.1).join with
    | some d => some (pegF x.1 d, y.2)
    | Option.none => Option.none

theorem passThen_pos {a b : List (Nat × Nat)} (ha : PosL a) (hb : PosL b) :
    passThen a b = some (if a.isEmpty then [] else (b.map fun x => a.filterMap (ptOne x)).flatten) := by
  unfold passThen
  by_cases e : a.isEmpty
  · simp [e]
  simp only [e, Bool.false_eq_true, ↓reduceIte]
  rw [turnO_some _ (fun x => a.filterMap (ptOne x)) b (fun x hx => murnO_some _ _ a (fun y hy => by
    obtain ⟨hy1, hy2⟩ := ha y hy
    obtain ⟨hx1, hx2⟩ := hb x hx
    rw [gep_pos hy1 hx2]
    unfold ptOne
    cases e1 : (gep y.1 x.2).join with
    | some d => simp
    | none =>
      simp only [Option.bind_some]
      rw [gep_pos hx2 hy1]
      cases (gep x.2 y.1).join <;> simp))]
  rfl

theorem ptOne_pos {x y e : Nat × Nat} (hx : x.1 ≠ 0 ∧ x.2 ≠ 0) (hy : y.1 ≠ 0 ∧ y.2 ≠ 0)
    (h : ptOne x y = some e) : e.1 ≠ 0 ∧ e.2 ≠ 0 := by
  unfold ptOne at h
  cases e1 : (gep y.1 x.2).join with
  | some d =>
    rw [e1] at h; simp only [Option.some.injEq] at h; subst h
    exact ⟨hx.1, pegF_ne hy.2 (gep_join_pos e1)⟩
  | none =>
    rw [e1] at h
    cases e2 : (gep x.2 y.1).join with
    | some d =>
      rw [e2] at h; simp only [Option.some.injEq] at h; subst h
      exact ⟨pegF_ne hx.1 (gep_join_pos e2), hy.2⟩
    | none => rw [e2] at h; simp at h

theorem passThen_posL {a b r : List (Nat × Nat)} (ha : PosL a) (hb : PosL b)
    (h : passThen a b = some r) : PosL r := by
  rw [passThen_pos ha hb] at h
  simp only [Option.some.injEq] at h
  subst h
  split
  · intro e he; simp at he
  · intro e he
    simp only [List.mem_flatten, List.mem_map] at he
    obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := he
    obtain ⟨y, hy, hxy⟩ := List.mem_filterMap.1 he
    exact ptOne_pos (hb x hx) (ha y hy) hxy

/-- The inner gate of `+pass-then`. -/
theorem pth_g1 {K : Noun} (hK : PassIn K) (x y : Nat × Nat) (hx : x.1 ≠ 0 ∧ x.2 ≠ 0)
    (hy : y.1 ≠ 0 ∧ y.2 ≠ 0) (X : Noun) :
    nock (C pthG1 (C (pN y) (C pthG2 (C (pN x) (C pthBat (C X K)))))) pthG1
      = some (unitNoun pN (ptOne x y)) := by
  obtain ⟨p1, p2⟩ := x
  obtain ⟨q1, q2⟩ := y
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only at hx1 hx2 hy1 hy2
  have hl1 := pi_layer1 hK
  have hg1 := pi_gep hK hy1 hx2
  have hg2 := pi_gep hK hx2 hy1
  unfold ptOne
  nock_open pthG1
  cases e1 : (gep q1 p2).join with
  | some d =>
    rw [e1] at hg1
    have hp := pi_peg hy2 (gep_join_pos e1)
    simp [nock_exec, pN, hK.2.1, gepArm, hg1, unitNoun, hl1, peg_arm, peg.arm_at, hp]
  | none =>
    rw [e1] at hg1
    cases e2 : (gep p2 q1).join with
    | some d =>
      rw [e2] at hg2
      have hp := pi_peg hx1 (gep_join_pos e2)
      simp [nock_exec, pN, hK.2.1, gepArm, hg1, hg2, unitNoun, hl1, peg_arm, peg.arm_at, hp]
    | none =>
      rw [e2] at hg2
      simp [nock_exec, pN, hK.2.1, gepArm, hg1, hg2, unitNoun]

/-- The outer gate of `+pass-then`. -/
theorem pth_g2 {K : Noun} (hK : PassIn K) (x : Nat × Nat) (hx : x.1 ≠ 0 ∧ x.2 ≠ 0)
    (a : List (Nat × Nat)) (ha : PosL a) (lb : Noun) :
    nock (C pthG2 (C (pN x) (C pthBat (C (C (lN a) lb) K)))) pthG2
      = some (listN ((a.filterMap (ptOne x)).map pN)) := by
  have hm := lq_murn_gate pN pN layer2 homoIn_layer2 pthG1 (C (A 0) (A 0))
    (C pthG2 (C (pN x) (C pthBat (C (C (lN a) lb) K)))) (ptOne x) a
    (fun y hy => pth_g1 hK x y hx (ha y hy) _)
  simp only [lN] at hm ⊢
  nock_open pthG2
  simp [nock_exec, hK.1, murn.arm_at, lq_murn_arm, hm]

/-- **`+pass-then`** is `passThen` on lists of parts with no axis `0`. -/
theorem pth_gate {K : Noun} (hK : PassIn K) (a b : List (Nat × Nat)) (ha : PosL a) (hb : PosL b) :
    nock (C pthBat (C (C (lN a) (lN b)) K)) pthBat = (passThen a b).map lN := by
  rw [passThen_pos ha hb]
  by_cases e : a.isEmpty
  · have : a = [] := List.isEmpty_iff.1 e
    subst this
    nock_open pthBat
    simp [nock_exec, lN]
  · have hne : a ≠ [] := fun h => by simp [h] at e
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
    have ht := lq_turn_gate pN listN layer2 homoIn_layer2 pthG2 (C (A 0) (A 0))
      (C pthBat (C (C (lN (y :: ys)) (lN b)) K)) (fun x => ((y :: ys).filterMap (ptOne x)).map pN) b
      (fun x hx => pth_g2 hK x (hb x hx) (y :: ys) ha (lN b))
    have hz : nock (C zing.battery (C (listN (b.map fun x =>
        listN (((y :: ys).filterMap (ptOne x)).map pN))) layer2)) zing.battery
        = some (lN (b.map fun x => (y :: ys).filterMap (ptOne x)).flatten) := by
      have := lq_zing (b.map fun x => (y :: ys).filterMap (ptOne x))
      simpa [List.map_map, Function.comp_def] using this
    simp only [List.map_map, Function.comp_def] at ht
    have hlb : lN (y :: ys) = listN ((y :: ys).map pN) := rfl
    have hlb2 : lN b = listN (b.map pN) := rfl
    have hn0 : ¬ (A 0 = lN (y :: ys)) := by simp [lN, listN, appendN]
    rw [hlb2] at ht ⊢
    nock_open pthBat
    simp [nock_exec, hK.1, turn.arm_at, turn_arm, zing.arm_at, lq_zing_arm, ht, hz, e, hn0]

end Compiler
end Formalization
