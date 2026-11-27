import lemmas.Compiler.OptLinkOnce
import lemmas.Ska.OptTopoOK
import lemmas.Ska.OptDriverFields

/-!
# The fuelled passes return with enough fuel

The models of `+bb-topo`, `+remove-hops` and `+remove-empty-middle` take
fuel where the Hoon loops have none; their links (`bb_gate`, `rh_gate`,
`rem_gate`) hold where the model returns.  Here: on blocks with the
invariants of the model side, some fuel makes the model return, so the links
hold with no condition on the model.  The measure of every loop is a rank
`ρ` that decreases along every jump (`Acyclic`):

* `+bb-topo` (`bbTopo_some`): a visit of `o` with fuel above `ρ o` returns,
  since it visits only the targets of `o`, of lower rank; fuel `ρ 0 + 1`.
* `+remove-hops` (`removeHops_some`): the chain of merges at `o` follows
  hops, each to a target of lower rank; fuel above the ranks of `topo`.
* `+remove-empty-middle` (`removeEmptyMiddle_some`): `rewrite-jump` and
  `rewrite-hop` follow hops from a target, each of lower rank; fuel above
  the ranks of the blocks.

The conditions beyond `Acyclic` are what the Hoon needs not to crash:
`Closed` (every jump of a block goes to a block: `got` of a missing block
crashes), `ArityOK` (a jump passes as many arguments as its target has
parameters: `?>  =(~ par.nex)` of `rewrite-jump`, the `!!` of the segment of
`+remove-hops` and of `sub` in `rewrite-hop`), and for `+remove-hops`
`TopoInv` (`topo` from `+bb-topo` and `rev` from `+rev-cfg`: `?<  =(~
pre-o1)`).

* `bb_gate_total`, `rh_gate_total`, `rem_gate_total`: the links with the
  fuel found here.

Not proved here: the structural loop of `+optimize-once` (`structLoop`,
whose count `n` bounds the rounds; proved in `OptLinkTotalLoop.lean`,
`structLoop_total`).  Its measure is the triple (number of blocks, weight of
the two-way ends, `2` for a `%brn` and `1` for the others, since `+alias`
reports a change when it turns a `%brn` into a `%brz`, sum over the jumps of every
block of `ρ` of the target), ordered lexicographically, with `ρ` the rank of
`Acyclic`, which every pass keeps with the same `ρ` (`hops_acyclic`,
`rub_acyclic`, `mid_acyclic` of `Ska/OptDriverTopo.lean`).  A round that
reports a change lowers it: `+remove-hops` with a merge drops the merged
blocks (without one it keeps the blocks of `topo` and drops only the others,
`hops_same`); `+remove-useless-branching` with a change turns a two-way end
into a hop and keeps the labels; `+remove-empty-middle` with a change sends a
jump past at least one empty block, to a target of lower rank
(`rewriteJump_rank`, `rewriteHop_rank` give `≤`; a jump that is rewritten
goes strictly down), and keeps the labels and the kinds of ends.  What the
proof needs besides the measure is that every round's passes return, so
that `Closed`, `ArityOK`, the two-way ends passing no arguments (the `?>` of
`+remove-useless-branching`) and the block `0` hold of every round's blocks:
facts about the passes that the model side has not stated yet.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {Map : Type → Type} [HoonMap Map]

/-- Every jump of a block goes to a block. -/
def Closed (bl : Map Blob) : Prop :=
  ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → (HoonMap.get bl j.there).isSome

/-- A jump passes as many arguments as its target has parameters. -/
def ArityOK (bl : Map Blob) : Prop :=
  ∀ o b j b2, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → HoonMap.get bl j.there = some b2 →
    j.args.length = b2.par.length

theorem foldlM_isSome {α σ : Type} (g : σ → α → Option σ) :
    ∀ (l : List α) (s : σ), (∀ x ∈ l, ∀ s, (g s x).isSome) → (l.foldlM g s).isSome
  | [], s, _ => rfl
  | x :: l, s, h => by
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 (h x (by simp) s)
    simp only [List.foldlM_cons, hs', Option.bind_some]
    exact foldlM_isSome g l s' (fun y hy => h y (by simp [hy]))

theorem le_sum_map {α : Type} (f : α → Nat) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum
  | [], x, h => absurd h List.not_mem_nil
  | y :: l, x, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_map f l x h; omega

theorem foldl_bind_isSome {α σ : Type} (g : σ → α → Option σ) :
    ∀ (l : List α) (s : σ), (∀ x ∈ l, ∀ s, (g s x).isSome) →
      (l.foldl (fun acc x => acc.bind fun s => g s x) (some s)).isSome
  | [], s, _ => rfl
  | x :: l, s, h => by
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 (h x (by simp) s)
    simp only [List.foldl_cons, Option.bind_some, hs']
    exact foldl_bind_isSome g l s' (fun y hy => h y (by simp [hy]))

/-! ## `+bb-topo` -/

theorem dfs_isSome {bl : Map Blob} (hc : Closed bl) {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → ρ j.there < ρ o) :
    ∀ (n o : Nat) (acc : List Nat × List Nat), ρ o < n → (HoonMap.get bl o).isSome → (Opt.dfs bl n o acc).isSome := by
  intro n
  induction n with
  | zero => intro o acc h; omega
  | succ n ih =>
    intro o ⟨out, saw⟩ hn hb
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb
    simp only [Opt.dfs, hb, Option.bind_some, Option.isSome_map]
    refine foldlM_isSome _ _ _ (fun j hj acc => ?_)
    split
    · rfl
    · exact ih j.there acc (by have := hρ o b j hb hj; omega) (hc o b j hb hj)

/-- **`+bb-topo` returns with enough fuel** on an acyclic closed CFG with a
block `0`: any fuel above the rank of `0`. -/
theorem bbTopo_some {bl : Map Blob} (ha : Opt.Acyclic bl) (hc : Closed bl) (h0 : (HoonMap.get bl 0).isSome) :
    ∃ F, ∀ fuel, F ≤ fuel → (Opt.bbTopo fuel bl).isSome := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨ρ 0 + 1, fun fuel hf => ?_⟩
  simp only [Opt.bbTopo, Option.isSome_map]
  exact dfs_isSome hc hρ fuel 0 _ (by omega) h0

/-! ## `+remove-hops` -/

theorem hopSeg_isSome : ∀ (args : List (Option Nat)) (par : List Nat) (ops : List Pole),
    args.length = par.length → (Opt.hopSeg args par ops).isSome
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, p :: ps, ops, h => by
    simp only [Opt.hopSeg]
    exact hopSeg_isSome as ps _ (by simpa using h)

theorem hopChain_isSome {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (hi : Opt.TopoInv bl topo rev)
    (har : ArityOK bl) {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → ρ j.there < ρ o) :
    ∀ (n o : Nat) (b0 bnew : Blob) (segs : List (List Pole)) (saw : List Nat), o ∈ topo →
      HoonMap.get bl o = some b0 → bnew.fin = b0.fin → ρ o < n →
      (Opt.hopChain bl rev n o bnew segs saw).isSome := by
  intro n
  induction n with
  | zero => intro o b0 bnew segs saw _ _ _ h; omega
  | succ n ih =>
    intro o b0 bnew segs saw ho hb hf hn
    simp only [Opt.hopChain]
    split
    · rename_i t ht
      have hj : t ∈ Opt.getJmps b0.fin := by rw [← hf, ht]; simp [Opt.getJmps]
      have hpre : o ∈ Opt.getJa rev t.there := hi.2 o b0 t ho hb hj
      have hne : Opt.getJa rev t.there ≠ [] := fun h => by rw [h] at hpre; cases hpre
      simp only [hne, if_false]
      split
      · rfl
      · obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.1 ho
        obtain ⟨k, -, hk⟩ := hi.1.2.2.2.2 i o b0 t hi' hb hj
        have ht1 : t.there ∈ topo := List.mem_iff_getElem?.2 ⟨k, hk⟩
        obtain ⟨b1, hb1⟩ := Option.isSome_iff_exists.1 (hi.1.2.2.1 t.there ht1)
        have hlen := har o b0 t b1 hb hj hb1
        obtain ⟨seg, hseg⟩ := Option.isSome_iff_exists.1 (hopSeg_isSome t.args b1.par b1.body hlen)
        simp only [hb1, Option.bind_some, hseg]
        exact ih t.there b1 _ _ _ ht1 hb1 rfl (by have := hρ o b0 t hb hj; omega)
    · rfl

/-- **`+remove-hops` returns with enough fuel** on an acyclic CFG with
`topo` and `rev` of `TopoInv` and jumps of the arity of their targets: any
fuel above the ranks of `topo`. -/
theorem removeHops_some {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (hi : Opt.TopoInv bl topo rev)
    (ha : Opt.Acyclic bl) (har : ArityOK bl) :
    ∃ F, ∀ fuel, F ≤ fuel → (Opt.removeHops fuel bl rev topo).isSome := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨(topo.map ρ).sum + 1, fun fuel hf => ?_⟩
  simp only [Opt.removeHops, Option.isSome_map]
  refine foldlM_isSome _ _ _ (fun o ho acc => ?_)
  simp only [Opt.hopsStep]
  split
  · rfl
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hi.1.2.2.1 o ho)
    simp only [hb, Option.bind_some, Option.isSome_map]
    have hle : ρ o ≤ (topo.map ρ).sum := le_sum_map ρ topo o ho
    exact hopChain_isSome hi har hρ fuel o b b [] acc.2 ho hb rfl (by omega)

/-! ## `+remove-empty-middle` -/

/-- The jump has the target and the arity of a jump of some block. -/
def JumpOf (bl : Map Blob) (j : Jmp) : Prop :=
  ∃ o b j0, HoonMap.get bl o = some b ∧ j0 ∈ Opt.getJmps b.fin ∧ j0.there = j.there ∧ j0.args.length = j.args.length

theorem jumpOf_self {bl : Map Blob} {o : Nat} {b : Blob} {j : Jmp} (hb : HoonMap.get bl o = some b)
    (hj : j ∈ Opt.getJmps b.fin) : JumpOf bl j := ⟨o, b, j, hb, hj, rfl, rfl⟩

theorem rewriteJump_isSome {bl : Map Blob} (hc : Closed bl) (har : ArityOK bl) {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → ρ j.there < ρ o) :
    ∀ (n : Nat) (j : Jmp), JumpOf bl j → ρ j.there < n → (Opt.rewriteJump bl n j).isSome := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j ⟨o, b, j0, hb, hj0, ht, hl⟩ hn
    simp only [Opt.rewriteJump]
    split
    · rfl
    · rename_i hargs
      have hargs' : j.args = [] := by simpa using hargs
      have hsome : (HoonMap.get bl j.there).isSome := by rw [← ht]; exact hc o b j0 hb hj0
      obtain ⟨nex, hnex⟩ := Option.isSome_iff_exists.1 hsome
      have hpar : nex.par = [] := by
        have := har o b j0 nex hb hj0 (by rw [ht]; exact hnex)
        rw [hl, hargs'] at this
        exact List.length_eq_zero_iff.1 this.symm
      simp only [hnex, Option.bind_some, hpar, ne_eq, not_true_eq_false, if_false]
      split
      · rfl
      · split
        · rename_i t htf
          split
          · rfl
          · have htj : t ∈ Opt.getJmps nex.fin := by rw [htf]; simp [Opt.getJmps]
            exact ih t (jumpOf_self hnex htj) (by have := hρ _ nex t hnex htj; omega)
        · rfl

theorem mkSub_isSome : ∀ (par : List Nat) (args : List (Option Nat)) (s : Nat → Option (Option Nat)),
    par.length = args.length → (Opt.mkSub par args s).isSome
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | p :: ps, a :: as, s, h => by
    simp only [Opt.mkSub]
    exact mkSub_isSome ps as _ (by simpa using h)

theorem rewriteHop_isSome {bl : Map Blob} (rd : Nat → List Nat) (hc : Closed bl) (har : ArityOK bl)
    {ρ : Nat → Nat} (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → ρ j.there < ρ o) :
    ∀ (n : Nat) (j : Jmp), JumpOf bl j → ρ j.there < n → (Opt.rewriteHop bl rd n j).isSome := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j ⟨o, b, j0, hb, hj0, ht, hl⟩ hn
    simp only [Opt.rewriteHop]
    have hsome : (HoonMap.get bl j.there).isSome := by rw [← ht]; exact hc o b j0 hb hj0
    obtain ⟨nex, hnex⟩ := Option.isSome_iff_exists.1 hsome
    simp only [hnex, Option.bind_some]
    split
    · rfl
    · split
      · rename_i t htf
        split
        · rfl
        · have hlen : nex.par.length = j.args.length := by
            rw [← hl]; exact (har o b j0 nex hb hj0 (by rw [ht]; exact hnex)).symm
          obtain ⟨sb, hsb⟩ := Option.isSome_iff_exists.1 (mkSub_isSome nex.par j.args (fun _ => none) hlen)
          simp only [hsb, Option.bind_some]
          have htj : t ∈ Opt.getJmps nex.fin := by rw [htf]; simp [Opt.getJmps]
          exact ih _ ⟨j.there, nex, t, hnex, htj, rfl, by simp⟩ (by have := hρ _ nex t hnex htj; simp only; omega)
      · rfl

theorem middleFin_isSome {bl : Map Blob} (rd : Nat → List Nat) (hc : Closed bl) (har : ArityOK bl)
    {ρ : Nat → Nat} (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → ρ j.there < ρ o)
    (fuel o : Nat) (b : Blob) (hb : HoonMap.get bl o = some b) (hf : ρ o < fuel) :
    (Opt.middleFin bl rd fuel b.fin).isSome := by
  have J : ∀ j, j ∈ Opt.getJmps b.fin → (Opt.rewriteJump bl fuel j).isSome := fun j hj =>
    rewriteJump_isSome hc har hρ fuel j (jumpOf_self hb hj) (by have := hρ o b j hb hj; omega)
  have H : ∀ j, j ∈ Opt.getJmps b.fin → (Opt.rewriteHop bl rd fuel j).isSome := fun j hj =>
    rewriteHop_isSome rd hc har hρ fuel j (jumpOf_self hb hj) (by have := hρ o b j hb hj; omega)
  cases e : b.fin with
  | clq s z w =>
    rw [e] at J
    obtain ⟨z', hz⟩ := Option.isSome_iff_exists.1 (J z (by simp [Opt.getJmps]))
    obtain ⟨w', hw⟩ := Option.isSome_iff_exists.1 (J w (by simp [Opt.getJmps]))
    simp [Opt.middleFin, hz, hw]
  | eqq l r z w =>
    rw [e] at J
    obtain ⟨z', hz⟩ := Option.isSome_iff_exists.1 (J z (by simp [Opt.getJmps]))
    obtain ⟨w', hw⟩ := Option.isSome_iff_exists.1 (J w (by simp [Opt.getJmps]))
    simp [Opt.middleFin, hz, hw]
  | brn s z w =>
    rw [e] at J
    obtain ⟨z', hz⟩ := Option.isSome_iff_exists.1 (J z (by simp [Opt.getJmps]))
    obtain ⟨w', hw⟩ := Option.isSome_iff_exists.1 (J w (by simp [Opt.getJmps]))
    simp [Opt.middleFin, hz, hw]
  | brz s z w =>
    rw [e] at J
    obtain ⟨z', hz⟩ := Option.isSome_iff_exists.1 (J z (by simp [Opt.getJmps]))
    obtain ⟨w', hw⟩ := Option.isSome_iff_exists.1 (J w (by simp [Opt.getJmps]))
    simp [Opt.middleFin, hz, hw]
  | hop t =>
    rw [e] at H
    obtain ⟨t', ht⟩ := Option.isSome_iff_exists.1 (H t (by simp [Opt.getJmps]))
    simp [Opt.middleFin, ht]
  | _ => simp [Opt.middleFin]

variable [Opt.MapKeys Map]

/-- **`+remove-empty-middle` returns with enough fuel** on an acyclic closed
CFG whose jumps have the arity of their targets: any fuel above the ranks of
the blocks. -/
theorem removeEmptyMiddle_some {bl : Map Blob} (ha : Opt.Acyclic bl) (hc : Closed bl) (har : ArityOK bl) :
    ∃ F, ∀ fuel, F ≤ fuel → (Opt.removeEmptyMiddle fuel bl).isSome := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨((Opt.MapKeys.keys bl).map ρ).sum + 1, fun fuel hf => ?_⟩
  unfold Opt.removeEmptyMiddle
  apply foldl_bind_isSome
  intro o ho s
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((Opt.MapKeys.mem_keys bl o).1 ho)
  have hle := le_sum_map ρ _ o ho
  obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.1
    (middleFin_isSome (Opt.readersOf bl) hc har hρ fuel o b hb (by omega))
  simp [hb, hf']

end

/-! ## The links with no condition on the model -/

/-- **`+bb-topo`** on an acyclic closed CFG with a block `0` and no `%lti`:
the gate returns the model's `topo` at the fuel found by `bbTopo_some`. -/
theorem bb_gate_total (bl : TreapMap mugF Blob) (hl : NoLti bl) (ha : Opt.Acyclic bl) (hc : Closed bl)
    (h0 : (HoonMap.get bl 0).isSome) :
    ∃ fuel t, Opt.bbTopo fuel bl = some t ∧
      nock (C bbBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) bbBody = some (listNoun A t) := by
  obtain ⟨F, hF⟩ := bbTopo_some ha hc h0
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hF F (Nat.le_refl _))
  exact ⟨F, t, ht, bb_gate bl hl F t ht⟩

/-- **`+remove-hops`** on an acyclic CFG with `TopoInv` and jumps of the
arity of their targets. -/
theorem rh_gate_total (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (topo : List Nat)
    (hi : Opt.TopoInv bl topo rev) (ha : Opt.Acyclic bl) (har : ArityOK bl) :
    ∃ fuel r, Opt.removeHops fuel bl rev topo = some r ∧
      nock (C rhBody (C (C (HoonMap.toNoun Blob.toNoun bl) (C (jarN rev) (listNoun A topo))) optC)) rhBody
        = some (C (flag r.1) (HoonMap.toNoun Blob.toNoun r.2)) := by
  obtain ⟨F, hF⟩ := removeHops_some hi ha har
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hF F (Nat.le_refl _))
  exact ⟨F, r, hr, rh_gate bl rev topo F r hr⟩

/-- **`+remove-empty-middle`** on an acyclic closed CFG with no `%lti` whose
jumps have the arity of their targets. -/
theorem rem_gate_total (bl : TreapMap mugF Blob) (hl : NoLti bl) (ha : Opt.Acyclic bl) (hc : Closed bl)
    (har : ArityOK bl) :
    ∃ fuel r, Opt.removeEmptyMiddle fuel bl = some r ∧
      nock (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) remBody = some (remN r) := by
  obtain ⟨F, hF⟩ := removeEmptyMiddle_some ha hc har
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hF F (Nat.le_refl _))
  exact ⟨F, r, hr, rem_gate bl hl F r hr⟩

end Compiler
end Formalization
