import lemmas.Compiler.CompTarjanPop
import lemmas.Hoon.RepBy

/-!
# `+tarjan`: `enter`, the visited kid, and `+rep` with a partial gate (track Q)

* `TjMapIs VIS vis`: `VIS` is a map noun whose pairs are `[k idx]` for
  `vis k = some idx`;
* **`tj_enter`**: the edit `tjEnter` of `connect` (`idx` `+(idx)`, `vis`
  `+put:by` of `[v index]`, `stk` `[v stk]`, `cur` `+put:in` of `v`) is
  the model's `enter`;
* **`tj_rep_loop`**, `tj_rep_gate`: `+rep` (`rep:by`, `rep:in`: the same
  noun) with ANY gate is the monadic fold, in pre-order, of the gate's own
  slam (`List.foldlM` over `Option`): the gates of `+tarjan` may crash;
* **`tj_kvis`**: the gate `tjKBat` on a kid that `vis` holds returns the
  model's step of `kidsLoop`: `lowest` lowered to the kid's index when `cur`
  holds the kid, the state unchanged.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `VIS` is a map noun with the pairs `[k idx]` of `vis`. -/
def TjMapIs (VIS : Noun) (vis : Noun → Option Nat) : Prop :=
  IsMap mugF VIS ∧ ∀ k v, Get VIS k v ↔ ∃ i, vis k = some i ∧ v = A i

/-- **`enter`**: the edit of `acc` at the start of `connect`. -/
theorem tj_enter {CTX : Noun} (hL : slot? 32767 CTX = some layer2) (V KIDS FIN : Noun) (s : St Noun)
    {VIS CUR : Noun} (hv : TjMapIs VIS s.vis) (hc : TjSet CUR fun k => s.cur k = true) :
    ∃ VIS' CUR', TjMapIs VIS' (enter V s).vis ∧ TjSet CUR' (fun k => (enter V s).cur k = true) ∧
      nock (C (A s.idx) (tjConnCore V KIDS (tjAccN (A s.idx) VIS (listNoun id s.stk) CUR FIN) CTX)) tjEnter
        = some (C (A s.idx) (tjConnCore V KIDS (tjAccN (A (s.idx + 1)) VIS' (listNoun id (V :: s.stk)) CUR' FIN)
            CTX)) := by
  obtain ⟨VIS', he, hm, hg⟩ := put_by layer2 gorIn_morIn_layer2 VIS V (A s.idx) hv.1
  obtain ⟨CUR', hpe, hcs, hch⟩ := put_in layer2 gorIn_morIn_layer2 CUR V hc.1
  have hp := nock_of_eval hpe
  refine ⟨VIS', CUR', ⟨hm, fun k v => ?_⟩, ⟨hcs, fun k => ?_⟩, ?_⟩
  · rw [hg k v, hv.2 k v]
    by_cases e : k = V
    · subst e; simp [enter]
    · simp [enter, e]
  · rw [hch k, hc.2 k]
    by_cases e : k = V
    · subst e; simp [enter]
    · simp [enter, e, hc.2 k]
  · have hp' : nock (C in.put.battery (C V (C in.battery (C CUR layer2)))) in.put.battery = some CUR' := hp
    have he' := nock_of_eval he
    rw [tjEnter_eq]
    simp [tjConnCore, tjAccN, listNoun, nock_exec, hL, in.arm_at, in_arm, in.put.arm_at, put_in_arm, hp',
      by.arm_at, by_arm, by.put.arm_at, put_arm, he']

/-- **`+rep` with any gate**: the fold, in pre-order, of the gate's slam. -/
theorem tj_rep_loop (B ctx bp e bc : Noun) : ∀ (a : Noun), Tree a → ∀ (N : Noun),
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e N) bc)) (C B (C a ctx))))) by.rep.loop
      = (preorder a).foldlM (fun N x => nock (C bp (C (C x N) bc)) bp) N := by
  intro a ha
  induction ha with
  | nil =>
    intro N
    nock_open by.rep.loop
    simp [nock_exec, preorder]
  | @node n l r _ _ ihl ihr =>
    intro N
    nock_open by.rep.loop
    simp only [preorder, List.foldlM_cons, List.foldlM_append]
    cases h1 : nock (C bp (C (C n N) bc)) bp with
    | none => simp [nock_exec, h1]
    | some N1 =>
      cases h2 : (preorder l).foldlM (fun N x => nock (C bp (C (C x N) bc)) bp) N1 with
      | none => simp [nock_exec, h1, ihl, h2]
      | some N2 => simp [nock_exec, h1, ihl, h2, ihr]

/-- `+rep` slammed on any gate. -/
theorem tj_rep_gate (B ctx bp e acc bc a : Noun) (ha : Tree a) :
    nock (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C a ctx)))) by.rep.battery
      = (preorder a).foldlM (fun N x => nock (C bp (C (C x N) bc)) bp) acc := by
  nock_open by.rep.battery
  simp only [nock_exec, tj_rep_loop B ctx bp e bc a ha acc]

/-- The core of the kids gate on `[kid [lowest acc]]`, in the context
`[index tcore]`. -/
def tjKCore (KID : Noun) (LO : Nat) (ACC KC : Noun) : Noun := C tjKBat (C (C KID (C (A LO) ACC)) KC)

/-- **A visited kid**: `vis` holds `kid` with index `ki`; the gate returns
`lowest` lowered to `ki` when `cur` holds `kid`, and `acc`. -/
theorem tj_kvis {CTX : Noun} (hL : slot? 32767 CTX = some layer2) (IX V0 KIDS0 ACC0 : Noun) (s : St Noun)
    {VIS CUR : Noun} (STK FIN : Noun) (hv : TjMapIs VIS s.vis) (hc : TjSet CUR fun k => s.cur k = true)
    (KID : Noun) (LO ki : Nat) (hk : s.vis KID = some ki) :
    nock (tjKCore KID LO (tjAccN (A s.idx) VIS STK CUR FIN) (C IX (tjConnCore V0 KIDS0 ACC0 CTX))) tjKBat
      = some (C (A (if s.cur KID then min LO ki else LO)) (tjAccN (A s.idx) VIS STK CUR FIN)) := by
  have hgk : Get VIS KID (A ki) := (hv.2 KID (A ki)).2 ⟨ki, hk, rfl⟩
  have hget := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ KID VIS _ (getF_some hv.1 hgk)
  obtain ⟨t, hth, ht⟩ := has_in layer2 gorIn_morIn_layer2.1 CUR KID hc.1
  have hhas := nock_of_eval hth
  have hl1 : slot? 65535 CTX = some layer1 := by
    have h := layer2_layer1
    revert h
    cases layer2 with
    | atom _ => intro h; simp [nock_exec] at h
    | cell a b =>
      intro h
      simp only [nock_exec, Option.some.injEq] at h
      subst h
      exact slot?_right hL
  rw [tjKBat_eq, tjKVis_eq, tjKGet_eq]
  cases hcur : s.cur KID
  · have hf : t = false := by
      cases t
      · rfl
      · exact absurd ((hc.2 KID).1 (ht.1 rfl)) (by simp [hcur])
    subst hf
    simp [tjKCore, tjConnCore, tjAccN, nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hget,
      in.arm_at, in_arm, in.has.arm_at, has_in_arm, hhas, loob]
  · have hf : t = true := ht.2 ((hc.2 KID).2 hcur)
    subst hf
    simp [tjKCore, tjConnCore, tjAccN, nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hget,
      in.arm_at, in_arm, in.has.arm_at, has_in_arm, hhas, loob, min.arm_at, min_arm,
      min_gate layer1 arith_layer1.2.2.2.1, hl1]

end Compiler
end Formalization
