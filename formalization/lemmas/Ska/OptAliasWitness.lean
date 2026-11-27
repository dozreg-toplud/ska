import lemmas.Ska.OptAliasOnce
import lemmas.Ska.OptSwitch

/-!
# Witnesses: `DefOnceB` of the result of `+alias` fails, and a miscompile

`LM`: a map as an association list (`HoonMap`, `MapKeys`), so that the models
evaluate in the kernel (`decide`).

## `¬ AliasOnceB` (so `AliasRestSSAB` is false)

`vBlocks` (`nargs = 2`): block `0` is `[%inc 0 2] [%inc 0 3]`,
`[%brn 1 [~ 1] [~ 2]]`; block `1` is `[%cel 2] [%imm 0 2]`, `[%bom ~]` (a
dead fill of `2`); block `2` is `[%don 3]`.  **`v_dinvS`**, **`v_topo`**: the
blocks have `DInvS` and `TopoInvR` on the order of `+bb-topo`, `[0 2 1]`.
**`v_alias`**: the model of `+alias` keeps `[%inc 0 2]`, drops `[%inc 0 3]`
(renaming `3` to `2`), keeps block `1`, and makes block `2` `[%don 2]`.
**`not_aliasOnceB`**: in the result register `2` has two definitions that
count, so `DefOnceB` fails.

## A miscompile of the model of `+optimize` (`w_opt`)

`wBlocks` (`nargs = 2`, registers `0`, `1` the arguments):

* `0`: `[%inc 0 2] [%inc 0 3] [%imm 1 4]`, `[%brn 4 [~ 1] [~ 2]]`;
* `1`: `[%imm 7 5]`, `[%hop [[~ ~] 3]]` (passes `~` to the parameter of `3`);
* `2`: `[%imm 8 6]`, `[%hop [[~ ~] 3]]`;
* `3`: parameter `7`, `[%brn 1 [~ 5] [~ 4]]`;
* `4`: `[%cel 2] [%imm 0 2]`, `[%bom ~]` (a dead fill of `2`);
* `5`: `[%don 3]`.

**`w_dinvS`**: they have `DInvS` (`2` has the definition that counts
`(0, 0)` and the dead fill `(4, 1)`, read only by `[%cel 2]`).  Round 1 of `+optimize`: `+alias` folds the `%brn` of block `0`
(`4` holds `1`) to a hop to `2`, drops block `1`, drops `[%inc 0 3]`
renaming `3` to `2`, keeps the fill (no immediate `0` is known) and makes
block `5` `[%don 2]`; `+remove-dead-code` drops `[%imm 1 4]` and `[%imm 8 6]`
(its `saw` is one set for the whole walk, so the fill stays: block `5` reads
`2`); `+remove-hops` merges `2` and `3` into `0`, the `~` passed to `7`
becoming `[%imm 0 7]`.  Round 2: `+alias` walks `[0 4 5]`; at block `4` the
immediate `0` is known in `7`, so it drops `[%imm 0 2]` and renames `2` to `7`
in the global `old`; block `5`, walked after, becomes `[%don 7]`
(**`w_opt`**).  With the arguments `s` (an atom) and `0`, the code before
runs `0`, `2`, `3`, `5` and returns `s + 1`; the code after runs `0`, `5` and
returns `0`.

The models of the passes were checked against the Hoon (README), so the real
`+optimize` should do the same on these blocks.  `+comp` no longer emits
blocks of this shape: the fill of `+crash-need` on the first `%inc`'s register
(the register its `%cel` tests) is gone since commit `af5cc39`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

/-- A map as an association list, newest first. -/
structure LM (ν : Type) where
  l : List (Nat × ν)

def LM.find (m : LM ν) (k : Nat) : Option ν := (m.l.find? fun e => e.1 = k).map Prod.snd

theorem lm_find_filter {ν : Type} (k k' : Nat) (h : k' ≠ k) : ∀ l : List (Nat × ν),
    (l.filter fun e => e.1 ≠ k).find? (fun e => e.1 = k') = l.find? fun e => e.1 = k'
  | [] => rfl
  | e :: l => by
    rw [List.filter_cons]
    by_cases he : e.1 = k
    · have he' : ¬ e.1 = k' := fun h' => h (h' ▸ he)
      rw [if_neg (by simpa using he), List.find?_cons_of_neg (by simpa using he'), lm_find_filter k k' h l]
    · rw [if_pos (by simpa using he)]
      by_cases he' : e.1 = k'
      · rw [List.find?_cons_of_pos (by simpa using he'), List.find?_cons_of_pos (by simpa using he')]
      · rw [List.find?_cons_of_neg (by simpa using he'), List.find?_cons_of_neg (by simpa using he'),
          lm_find_filter k k' h l]

instance : HoonMap LM where
  empty := ⟨[]⟩
  get m k := m.find k
  put m k v := ⟨(k, v) :: m.l.filter fun e => e.1 ≠ k⟩
  del m k := ⟨m.l.filter fun e => e.1 ≠ k⟩
  toNoun _ _ := A 0
  get_empty _ := rfl
  get_put m k v k' := by
    show (((k, v) :: m.l.filter fun e => e.1 ≠ k).find? fun e => e.1 = k').map Prod.snd =
      if k' = k then some v else (m.l.find? fun e => e.1 = k').map Prod.snd
    by_cases e : k' = k
    · subst e; rw [List.find?_cons_of_pos (by simp), if_pos rfl]; rfl
    · rw [List.find?_cons_of_neg (by simpa using fun h => e h.symm), lm_find_filter k k' e, if_neg e]
  get_del m k k' := by
    show ((m.l.filter fun e => e.1 ≠ k).find? fun e => e.1 = k').map Prod.snd =
      if k' = k then none else (m.l.find? fun e => e.1 = k').map Prod.snd
    by_cases e : k' = k
    · subst e; rw [if_pos rfl]; simp [List.find?_eq_none]
    · rw [lm_find_filter k k' e, if_neg e]
  toNoun_empty _ := rfl

instance : MapKeys LM where
  keys m := dedupN (m.l.map Prod.fst)
  mem_keys m k := by
    rw [awr_dedup_mem]
    simp only [HoonMap.get, LM.find, Option.isSome_map, List.find?_isSome, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨e, he, by simp⟩
    · rintro ⟨e, he, h⟩; exact ⟨e, he, by simpa using h⟩
  nodup m := awr_dedup_nodup _

/-! ## `DefOnceB` of the result fails (`¬ AliasOnceB`) -/

def V0 : Blob := ⟨[], [Pole.inc 0 2, Pole.inc 0 3], Termin.brn 1 ⟨[], 1⟩ ⟨[], 2⟩⟩
def V1 : Blob := ⟨[], [Pole.cel 2, Pole.imm (A 0) 2], Termin.bom none⟩
def V2 : Blob := ⟨[], [], Termin.don 3⟩

/-- **The blocks of the witness**: two `%inc` of the argument `0`, a dead fill
of the first one's register on the side `1` of a `%brn` on the argument `1`,
the second one's register returned on the side `2`. -/
def vBlocks : LM Blob := ⟨[(0, V0), (1, V1), (2, V2)]⟩

theorem v_get {o : Nat} {b : Blob} (h : HoonMap.get vBlocks o = some b) :
    (o = 0 ∧ b = V0) ∨ (o = 1 ∧ b = V1) ∨ (o = 2 ∧ b = V2) := by
  change vBlocks.find o = some b at h
  rcases o with _ | _ | _ | o
  · simp [LM.find, vBlocks] at h; exact Or.inl ⟨rfl, h.symm⟩
  · simp [LM.find, vBlocks] at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
  · simp [LM.find, vBlocks] at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
  · simp [LM.find, vBlocks] at h

theorem v_get0 : HoonMap.get vBlocks 0 = some V0 := rfl
theorem v_get1 : HoonMap.get vBlocks 1 = some V1 := rfl
theorem v_get2 : HoonMap.get vBlocks 2 = some V2 := rfl

theorem v_jmps {o : Nat} {b : Blob} {j : Jmp} (h : HoonMap.get vBlocks o = some b) (hj : j ∈ getJmps b.fin) :
    o = 0 ∧ (j.there = 1 ∨ j.there = 2) ∧ j.args = [] := by
  rcases v_get h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [V0, getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨rfl, Or.inl rfl, rfl⟩
    · exact ⟨rfl, Or.inr rfl, rfl⟩
  · simp [V1, getJmps] at hj
  · simp [V2, getJmps] at hj

theorem v_reach {o : Nat} (h : Reach vBlocks o) : o = 0 ∨ o = 1 ∨ o = 2 := by
  induction h with
  | zero => exact Or.inl rfl
  | jump _ hb hj _ =>
    rcases (v_jmps hb hj).2.1 with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

theorem v_bpath : ∀ {L : List Nat}, BPath vBlocks L → L = [0] ∨ L = [1, 0] ∨ L = [2, 0]
  | _, BPath.start => Or.inl rfl
  | _, BPath.step hp hb hj => by
    obtain ⟨rfl, ht, -⟩ := v_jmps hb hj
    rcases v_bpath hp with e | e | e
    · cases e
      rcases ht with e2 | e2
      · rw [e2]; exact Or.inr (Or.inl rfl)
      · rw [e2]; exact Or.inr (Or.inr rfl)
    · cases e
    · cases e

theorem v_allDefs : allDefs vBlocks = [2, 3, 2] := by decide

/-- The only reads of register `2`: by `[%cel 2]`. -/
theorem v_read2 {o j : Nat} {b : Blob} (hb : HoonMap.get vBlocks o = some b) (hr : ReadAt b j 2) : o = 1 ∧ j = 0 := by
  rcases v_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases j with _ | _ | _ | j <;> simp [ReadAt, V0, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
  · rcases j with _ | _ | _ | j <;> simp [ReadAt, V1, aliasReads, aliasDst, poleRegs, finRegs] at hr
    exact ⟨rfl, rfl⟩
  · rcases j with _ | j <;> simp [ReadAt, V2, aliasReads, aliasDst, poleRegs, finRegs] at hr

theorem v_fill : DeadFill vBlocks 2 1 1 :=
  ⟨V1, v_get1, ⟨none, rfl⟩, ⟨A 0, rfl⟩, fun op hop => by
    simp only [V1, List.drop_succ_cons, List.drop_zero, List.mem_singleton] at hop
    exact ⟨A 0, 2, hop⟩,
   fun o' b' j _ hb' hr => by obtain ⟨rfl, rfl⟩ := v_read2 hb' hr; exact ⟨rfl, by omega⟩⟩

theorem v_live {r : Nat} {s : Nat × Option Nat} (h : LiveDef vBlocks r s) :
    (r = 2 ∧ s = (0, some 0)) ∨ (r = 3 ∧ s = (0, some 1)) := by
  obtain ⟨-, hd, hnf⟩ := h
  obtain ⟨o, _ | i⟩ := s
  · obtain ⟨b, hb, hm⟩ := hd
    rcases v_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [V0, V1, V2] at hm
  · obtain ⟨b, op, hb, hop, hdst⟩ := hd
    rcases v_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases i with _ | _ | i <;> simp [V0] at hop <;> subst hop <;> simp [aliasDst] at hdst <;> subst hdst
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rcases i with _ | _ | i <;> simp [V1] at hop <;> subst hop <;> simp [aliasDst] at hdst
      subst hdst
      exact absurd v_fill (hnf 1 rfl)
    · simp [V2] at hop

/-- **The witness blocks have `DInvS`.** -/
theorem v_dinvS : DInvS vBlocks := by
  refine ⟨⟨⟨⟨fun o b hb => ?_, fun o b j b2 hb hj _ r hr => ?_⟩, ⟨fun o => if o = 0 then 1 else 0, fun o b j hb hj => ?_⟩,
    fun y b j hb hj r hr => ?_⟩, ⟨fun _ => [], rfl, fun o b _ hb => ?_⟩⟩, ⟨fun r s s' hs hs' => ?_, ?_⟩, ?_⟩
  · rcases v_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [V0, V1, V2]
  · rw [(v_jmps hb hj).2.2] at hr; cases hr
  · obtain ⟨rfl, ht, -⟩ := v_jmps hb hj
    rcases ht with e | e <;> rw [e] <;> decide
  · rw [(v_jmps hb hj).2.2] at hr; cases hr
  · rcases v_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨[], rfl, fun _ _ => rfl⟩
    · exact ⟨[], rfl, fun _ _ => rfl⟩
    · exact ⟨[], rfl, fun _ _ => rfl⟩
  · rcases v_live hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases v_live hs' with ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
      first | rfl | cases e
  · intro o p b hπ hb i r hr hall
    rw [v_allDefs] at hall
    rcases v_bpath hπ with e | e | e <;> cases e
    · have hb' := hb; rw [v_get0] at hb'; cases hb'
      rcases i with _ | _ | _ | i <;>
        simp [V0, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr <;> subst hr <;> simp at hall
    · have hb' := hb; rw [v_get1] at hb'; cases hb'
      right; right
      refine ⟨0, List.mem_singleton_self _, V0, v_get0, ?_⟩
      rcases i with _ | _ | _ | i <;> simp [V1, aliasReads, aliasDst, poleRegs, finRegs] at hr
      subst hr; simp [blockDefs, V0, aliasDst]
    · have hb' := hb; rw [v_get2] at hb'; cases hb'
      right; right
      refine ⟨0, List.mem_singleton_self _, V0, v_get0, ?_⟩
      rcases i with _ | i <;> simp [V2, aliasReads, aliasDst, poleRegs, finRegs] at hr
      subst hr; simp [blockDefs, V0, aliasDst]
  · intro o b hb n s z o' e
    rcases v_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [V0, V1, V2] at e

/-- **`TopoInvR` of the witness** on the order `+bb-topo` gives and its
`+rev-cfg`. -/
theorem v_topo : TopoInvR vBlocks [0, 2, 1] (revCfg vBlocks [0, 2, 1]) := by
  have ht : TopoOK vBlocks [0, 2, 1] := by
    refine ⟨by decide, rfl, by decide, fun o h => ?_, fun i o b j hi hb hj => ?_⟩
    · rcases v_reach h with rfl | rfl | rfl <;> decide
    · obtain ⟨rfl, ht, -⟩ := v_jmps hb hj
      rcases i with _ | _ | _ | i <;> simp at hi
      rcases ht with e | e <;> rw [e]
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
  exact ⟨topoInv_revCfg ht, revCfg_sound _ _⟩

/-- **The model of `+alias` on the witness.** -/
theorem v_alias : (aliasWalk (fun l => l.headD 0) 2 vBlocks [0, 2, 1] (aliasInit (revCfg vBlocks [0, 2, 1]))).map
    (fun g => (HoonMap.get g.new 0, HoonMap.get g.new 1, HoonMap.get g.new 2)) =
    some (some ⟨[], [Pole.inc 0 2], Termin.brn 1 ⟨[], 1⟩ ⟨[], 2⟩⟩,
      some ⟨[], [Pole.cel 2, Pole.imm (A 0) 2], Termin.bom none⟩, some ⟨[], [], Termin.don 2⟩) := by decide

/-- **`AliasOnceB` is false** (so `AliasRestSSAB` is): on blocks with `DInvS`
and `TopoInvR`, the result of the model of `+alias` has two definitions that
count of register `2`, `(0, 0)` and `(1, 1)`. -/
theorem not_aliasOnceB : ¬ AliasOnceB LM (fun l => l.headD 0) := by
  intro H
  cases hw : aliasWalk (fun l => l.headD 0) 2 vBlocks [0, 2, 1] (aliasInit (revCfg vBlocks [0, 2, 1])) with
  | none => have := v_alias; rw [hw] at this; cases this
  | some g =>
    have hv := v_alias
    rw [hw] at hv
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨h0, h1, h2⟩ := hv
    have hO := H 2 vBlocks [0, 2, 1] _ g v_dinvS v_topo hw
    have hR1 : Reach g.new 1 := Reach.jump (j := ⟨[], 1⟩) Reach.zero h0 (by simp [getJmps])
    have hR2 : Reach g.new 2 := Reach.jump (j := ⟨[], 2⟩) Reach.zero h0 (by simp [getJmps])
    have l0 : LiveDef g.new 2 (0, some 0) := ⟨Reach.zero, ⟨_, Pole.inc 0 2, h0, rfl, rfl⟩, fun i _ hdf => by
      obtain ⟨b, hb, ⟨u, hu⟩, -⟩ := hdf
      rw [h0] at hb; cases hb; cases hu⟩
    have l1 : LiveDef g.new 2 (1, some 1) := ⟨hR1, ⟨_, Pole.imm (A 0) 2, h1, rfl, rfl⟩, fun i _ hdf => by
      obtain ⟨-, -, -, -, -, hrd⟩ := hdf
      have := (hrd 2 _ 0 hR2 h2 (Or.inr ⟨rfl, by simp [finRegs]⟩)).1
      cases this⟩
    have := hO 2 _ _ l0 l1
    simp at this

/-! ## A miscompile of the model of `+optimize` -/

def W0 : Blob := ⟨[], [Pole.inc 0 2, Pole.inc 0 3, Pole.imm (A 1) 4], Termin.brn 4 ⟨[], 1⟩ ⟨[], 2⟩⟩
def W1 : Blob := ⟨[], [Pole.imm (A 7) 5], Termin.hop ⟨[none], 3⟩⟩
def W2 : Blob := ⟨[], [Pole.imm (A 8) 6], Termin.hop ⟨[none], 3⟩⟩
def W3 : Blob := ⟨[7], [], Termin.brn 1 ⟨[], 5⟩ ⟨[], 4⟩⟩
def W4 : Blob := ⟨[], [Pole.cel 2, Pole.imm (A 0) 2], Termin.bom none⟩
def W5 : Blob := ⟨[], [], Termin.don 3⟩

/-- The blocks of the miscompile (see the header). -/
def wBlocks : LM Blob := ⟨[(0, W0), (1, W1), (2, W2), (3, W3), (4, W4), (5, W5)]⟩

theorem w_get {o : Nat} {b : Blob} (h : HoonMap.get wBlocks o = some b) :
    (o = 0 ∧ b = W0) ∨ (o = 1 ∧ b = W1) ∨ (o = 2 ∧ b = W2) ∨ (o = 3 ∧ b = W3) ∨ (o = 4 ∧ b = W4) ∨
      (o = 5 ∧ b = W5) := by
  change wBlocks.find o = some b at h
  rcases o with _ | _ | _ | _ | _ | _ | o <;> simp [LM.find, wBlocks] at h
  · exact Or.inl ⟨rfl, h.symm⟩
  · exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, h.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h.symm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h.symm⟩))))

theorem w_get0 : HoonMap.get wBlocks 0 = some W0 := rfl
theorem w_get3 : HoonMap.get wBlocks 3 = some W3 := rfl
theorem w_get4 : HoonMap.get wBlocks 4 = some W4 := rfl

/-- The jumps of `wBlocks`, with the label of their block. -/
theorem w_jmps {o : Nat} {b : Blob} {j : Jmp} (h : HoonMap.get wBlocks o = some b) (hj : j ∈ getJmps b.fin) :
    (o = 0 ∧ (j = ⟨[], 1⟩ ∨ j = ⟨[], 2⟩)) ∨ ((o = 1 ∨ o = 2) ∧ j = ⟨[none], 3⟩) ∨
      (o = 3 ∧ (j = ⟨[], 5⟩ ∨ j = ⟨[], 4⟩)) := by
  rcases w_get h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [W0, W1, W2, W3, W4, W5, getJmps] at hj
  · exact Or.inl ⟨rfl, hj⟩
  · exact Or.inr (Or.inl ⟨Or.inl rfl, hj⟩)
  · exact Or.inr (Or.inl ⟨Or.inr rfl, hj⟩)
  · exact Or.inr (Or.inr ⟨rfl, hj⟩)

/-- The paths of `wBlocks`: every path to `3`, `4`, `5` runs through `0`. -/
theorem w_bpath : ∀ {L : List Nat}, BPath wBlocks L → ∀ {o p}, L = o :: p →
    (o = 0 ∧ p = []) ∨ ((o = 1 ∨ o = 2) ∧ p = [0]) ∨ ((o = 3 ∨ o = 4 ∨ o = 5) ∧ 0 ∈ p)
  | _, BPath.start, o, p, e => by cases e; exact Or.inl ⟨rfl, rfl⟩
  | _, BPath.step hp hb hj, o, p, e => by
    cases e
    rcases w_jmps hb hj with ⟨rfl, rfl | rfl⟩ | ⟨ho, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · rcases w_bpath hp rfl with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)
      · omega
      · omega
    · rcases w_bpath hp rfl with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl ⟨Or.inr rfl, rfl⟩)
      · omega
      · omega
    · rcases w_bpath hp rfl with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
      · omega
      · exact Or.inr (Or.inr ⟨Or.inl rfl, by simp⟩)
      · omega
    · rcases w_bpath hp rfl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h0⟩
      · omega
      · omega
      · exact Or.inr (Or.inr ⟨Or.inr (Or.inr rfl), List.mem_cons_of_mem _ h0⟩)
    · rcases w_bpath hp rfl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h0⟩
      · omega
      · omega
      · exact Or.inr (Or.inr ⟨Or.inr (Or.inl rfl), List.mem_cons_of_mem _ h0⟩)

theorem w_allDefs : allDefs wBlocks = [2, 3, 4, 5, 6, 7, 2] := by decide

theorem w_read2 {o j : Nat} {b : Blob} (hb : HoonMap.get wBlocks o = some b) (hr : ReadAt b j 2) :
    o = 4 ∧ j = 0 := by
  rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases j with _ | _ | _ | _ | j <;> simp [ReadAt, W0, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
  · rcases j with _ | _ | j <;> simp [ReadAt, W1, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
  · rcases j with _ | _ | j <;> simp [ReadAt, W2, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
  · rcases j with _ | j <;> simp [ReadAt, W3, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
  · rcases j with _ | _ | _ | j <;> simp [ReadAt, W4, aliasReads, aliasDst, poleRegs, finRegs] at hr
    exact ⟨rfl, rfl⟩
  · rcases j with _ | j <;> simp [ReadAt, W5, aliasReads, aliasDst, poleRegs, finRegs] at hr

theorem w_fill : DeadFill wBlocks 2 4 1 :=
  ⟨W4, w_get4, ⟨none, rfl⟩, ⟨A 0, rfl⟩, fun op hop => by
    simp only [W4, List.drop_succ_cons, List.drop_zero, List.mem_singleton] at hop
    exact ⟨A 0, 2, hop⟩,
   fun o' b' j _ hb' hr => by obtain ⟨rfl, rfl⟩ := w_read2 hb' hr; exact ⟨rfl, by omega⟩⟩

/-- The definitions that count in `wBlocks`: one per register. -/
theorem w_live {r : Nat} {s : Nat × Option Nat} (h : LiveDef wBlocks r s) :
    (r = 2 ∧ s = (0, some 0)) ∨ (r = 3 ∧ s = (0, some 1)) ∨ (r = 4 ∧ s = (0, some 2)) ∨
      (r = 5 ∧ s = (1, some 0)) ∨ (r = 6 ∧ s = (2, some 0)) ∨ (r = 7 ∧ s = (3, none)) := by
  obtain ⟨-, hd, hnf⟩ := h
  obtain ⟨o, _ | i⟩ := s
  · obtain ⟨b, hb, hm⟩ := hd
    rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [W0, W1, W2, W3, W4, W5] at hm
    subst hm; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  · obtain ⟨b, op, hb, hop, hdst⟩ := hd
    rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases i with _ | _ | _ | i <;> simp [W0] at hop <;> subst hop <;> simp [aliasDst] at hdst <;> subst hdst
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rcases i with _ | i <;> simp [W1] at hop <;> subst hop <;> simp [aliasDst] at hdst
      subst hdst; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · rcases i with _ | i <;> simp [W2] at hop <;> subst hop <;> simp [aliasDst] at hdst
      subst hdst; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · simp [W3] at hop
    · rcases i with _ | _ | i <;> simp [W4] at hop <;> subst hop <;> simp [aliasDst] at hdst
      subst hdst
      exact absurd w_fill (hnf 1 rfl)
    · simp [W5] at hop

/-- **`wBlocks` have `DInvS`.** -/
theorem w_dinvS : DInvS wBlocks := by
  refine ⟨⟨⟨⟨fun o b hb => ?_, fun o b j b2 hb hj _ r hr => ?_⟩,
    ⟨fun o => if o = 0 then 3 else if o = 1 ∨ o = 2 then 2 else if o = 3 then 1 else 0, fun o b j hb hj => ?_⟩,
    fun y b j hb hj r hr => ?_⟩, ⟨fun _ => [], rfl, fun o b _ hb => ?_⟩⟩, ⟨fun r s s' hs hs' => ?_, ?_⟩, ?_⟩
  · rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [W0, W1, W2, W3, W4, W5]
  · rcases w_jmps hb hj with ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩ <;> simp at hr
  · rcases w_jmps hb hj with ⟨rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide
  · rcases w_jmps hb hj with ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩ <;> simp at hr
  · rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨[], rfl, fun _ _ => rfl⟩
  · rcases w_live hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases w_live hs' with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
      first | rfl | cases e
  · intro o p b hπ hb i r hr hall
    rw [w_allDefs] at hall
    have h0 : ∀ q : List Nat, 0 ∈ q → r ∈ blockDefs W0 →
        r ∈ b.par ∨ r ∈ (b.body.take i).filterMap aliasDst ∨
          ∃ o' ∈ q, ∃ b', HoonMap.get wBlocks o' = some b' ∧ r ∈ blockDefs b' :=
      fun q hq hd => Or.inr (Or.inr ⟨0, hq, W0, w_get0, hd⟩)
    rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases i with _ | _ | _ | _ | i <;>
        simp [W0, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr <;> subst hr <;> simp at hall
      right; left; decide
    · rcases i with _ | _ | i <;> simp [W1, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
    · rcases i with _ | _ | i <;> simp [W2, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
    · rcases i with _ | i <;> simp [W3, aliasReads, aliasDst, poleRegs, finRegs, jmpRegs] at hr
      subst hr; simp at hall
    · rcases w_bpath hπ rfl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp0⟩
      · omega
      · omega
      · rcases i with _ | _ | _ | i <;> simp [W4, aliasReads, aliasDst, poleRegs, finRegs] at hr
        subst hr; exact h0 p hp0 (by simp [blockDefs, W0, aliasDst])
    · rcases w_bpath hπ rfl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp0⟩
      · omega
      · omega
      · rcases i with _ | i <;> simp [W5, aliasReads, aliasDst, poleRegs, finRegs] at hr
        subst hr; exact h0 p hp0 (by simp [blockDefs, W0, aliasDst])
  · intro o b hb n s z o' e
    rcases w_get hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [W0, W1, W2, W3, W4, W5] at e

def wPasses : Passes LM := ⟨aliasM (fun l => l.headD 0), trimTraceHints, switchChains 20⟩

/-- **The model of `+optimize` on `wBlocks`**: block `5` returns register `7`
(the `0` that `+remove-hops` moved into the parameter of block `3`) where
the code before returns register `3` (`s + 1`). -/
theorem w_opt : (optimizeF 20 wPasses ⟨NeedOrd.none, 2, wBlocks⟩).map (fun s => HoonMap.get s.blocks 5) =
    some (some ⟨[], [], Termin.don 7⟩) := by decide


end Opt
end SkaModel
end Formalization
