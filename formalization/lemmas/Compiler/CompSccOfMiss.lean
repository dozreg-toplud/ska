import lemmas.Compiler.CompSccOfMissCut
import lemmas.Ska.TarjanSccOf
import lemmas.Hoon.RollUni
import lemmas.Hoon.TapIn
import lemmas.Hoon.Layer2

/-!
# The `sub` loop of the miss of `+scc-of` against `scoSub` (track Q)

The miss runs on `scoM0 B CA SC CTX = [~ [sccBat [[b calls sccs] ctx]]]`
(any context `CTX` with the hoon core at axis `65535`, as `sccCore`); the
trap of the `sub` loop is the core `scoT q sub M0 = [smTrap [q [sub M0]]]`.

* `sco_foldlM`: a monadic fold whose steps return what the model's steps
  return, when these do, returns what the model's fold returns;
* `sco_csg`: the gate of `cs` (`smCsG`) is `scoCsStep`;
* `sco_cs`: `smCs` (the `+rep:in` of `(~(gut by calls) i.q ~)` with that
  gate) is `scoCs`, on a `calls` noun that is a map of trees (`CallsOK`);
* **`sco_trap`**: at every fuel, whenever `scoSub` returns, the trap returns
  the same `sub`;
* **`sco_sub`**: `smSub` on the miss subject is `scoSub … [b] ~`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The subject of the miss: `[~ [sccBat [[b calls sccs] ctx]]]`. -/
def scoM0 (B CA SC CTX : Noun) : Noun := C (A 0) (C sccBat (C (C B (C CA SC)) CTX))

/-- The core of the trap of the `sub` loop. -/
def scoT (Q SUB M0 : Noun) : Noun := C smTrap (C Q (C SUB M0))

/-- `calls` is a map whose values are trees (sets of bells). -/
def CallsOK (CA : Noun) : Prop := IsMap mugF CA ∧ ∀ k v, Get CA k v → Tree v

/-- A monadic fold whose steps return what the model's do. -/
theorem sco_foldlM {f g : Noun → Noun → Option Noun} (h : ∀ a x r, f a x = some r → g a x = some r) :
    ∀ (l : List Noun) (a r : Noun), l.foldlM f a = some r → l.foldlM g a = some r := by
  intro l
  induction l with
  | nil => intro a r h0; simpa using h0
  | cons x xs ih =>
    intro a r h0
    simp only [List.foldlM_cons] at h0 ⊢
    cases e : f a x with
    | none => rw [e] at h0; cases h0
    | some b =>
      rw [e] at h0
      rw [h a x b e]
      exact ih b r h0

/-- The lookup of `calls`: `~` or `[~ v]` with `v` a tree. -/
theorem sco_gut {CA : Noun} (hCA : CallsOK CA) (k : Noun) :
    ∃ out, getF mugF k CA = some out ∧ (out = A 0 ∨ ∃ v, out = C (A 0) v) ∧ Tree (scoGut out) := by
  by_cases h : ∃ v, Get CA k v
  · obtain ⟨v, hv⟩ := h
    exact ⟨_, getF_some hCA.1 hv, Or.inr ⟨v, rfl⟩, by simpa [scoGut] using hCA.2 k v hv⟩
  · exact ⟨_, getF_none hCA.1 (fun v hv => h ⟨v, hv⟩), Or.inl rfl, by simp [scoGut]; exact Tree.nil⟩

/-- **The gate of `cs`** is `scoCsStep`. -/
theorem sco_csg {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (B CA SC Q SUB c N : Noun) :
    ∀ r, scoCsStep SC N c = some r →
      nock (C smCsG (C (C c N) (scoT Q SUB (scoM0 B CA SC CTX)))) smCsG = some r := by
  intro r h
  unfold scoCsStep at h
  cases hg : getF mugF c SC with
  | none => rw [hg] at h; cases h
  | some o =>
    rw [hg] at h
    have hh := has_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ c SC o hg
    by_cases e : o = A 0
    · subst e
      simp only [ne_eq, not_true_eq_false, if_false] at h
      have hp := put_in_gate layer2 gorIn_morIn_layer2 c N r h
      rw [smCsG_eq]
      simp [scoT, scoM0, nock_exec, hL, by.arm_at, by_arm, by.has.arm_at, has_arm, hh, in.arm_at, in_arm,
        in.put.arm_at, put_in_arm, hp, loob]
    · simp only [Option.bind_some, ne_eq, e, not_false_eq_true, if_true, Option.some.injEq] at h
      subst h
      rw [smCsG_eq]
      simp [scoT, scoM0, nock_exec, hL, by.arm_at, by_arm, by.has.arm_at, has_arm, hh, e, loob]

/-- A fold whose steps keep `P` keeps `P`. -/
theorem sco_foldlM_inv {f : Noun → Noun → Option Noun} (P : Noun → Prop) (h : ∀ a x r, P a → f a x = some r → P r) :
    ∀ (l : List Noun) (a r : Noun), P a → l.foldlM f a = some r → P r := by
  intro l
  induction l with
  | nil => intro a r ha h0; simp at h0; subst h0; exact ha
  | cons x xs ih =>
    intro a r ha h0
    simp only [List.foldlM_cons] at h0
    cases e : f a x with
    | none => rw [e] at h0; cases h0
    | some b => rw [e] at h0; exact ih b r (h a x b ha e) h0

/-- `cs` is a set noun. -/
theorem scoCs_set {CA SC k r : Noun} (h : scoCs CA SC k = some r) : IsSet mugF r := by
  unfold scoCs at h
  cases hg : getF mugF k CA with
  | none => rw [hg] at h; cases h
  | some out =>
    rw [hg, Option.bind_some] at h
    refine sco_foldlM_inv (IsSet mugF) (fun a c r ha hr => ?_) _ _ _
      (by simpa [IsSet] using (IsMap.nil : IsMap mugF (A 0))) h
    unfold scoCsStep at hr
    cases hg' : getF mugF c SC with
    | none => rw [hg'] at hr; cases hr
    | some o =>
      rw [hg', Option.bind_some] at hr
      by_cases e : o = A 0
      · simp only [e, ne_eq, not_true_eq_false, if_false] at hr
        obtain ⟨out, ho, hs, -⟩ := putInF_spec mugF a c ha
        rw [ho] at hr; cases hr; exact hs
      · simp only [ne_eq, e, not_false_eq_true, if_true, Option.some.injEq] at hr
        subst hr; exact ha

/-- **`cs`**: the `+rep:in` of `(~(gut by calls) i.q ~)` with the gate of
`cs` is `scoCs`. -/
theorem sco_cs {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (B CA SC x Q SUB : Noun) (hCA : CallsOK CA) :
    ∀ r, scoCs CA SC x = some r → nock (scoT (C x Q) SUB (scoM0 B CA SC CTX)) smCs = some r := by
  intro r h
  obtain ⟨out, hg, hout, ht⟩ := sco_gut hCA x
  unfold scoCs at h
  rw [hg, Option.bind_some] at h
  have hgut := gut_gate layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ x (A 0) CA out hg hout
  have hgut' : nock (C by.gut.battery (C (C x (A 0)) (C by.battery (C CA layer2)))) by.gut.battery
      = some (scoGut out) := by rcases hout with rfl | ⟨v, rfl⟩ <;> simpa [scoGut] using hgut
  have hrep := tj_rep_gate in.battery layer2 smCsG (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0)
    (scoT (C x Q) SUB (scoM0 B CA SC CTX)) (scoGut out) ht
  have hf := sco_foldlM (g := fun N c => nock (C smCsG (C (C c N) (scoT (C x Q) SUB (scoM0 B CA SC CTX)))) smCsG)
    (fun a c r hr => sco_csg hL B CA SC (C x Q) SUB c a r hr) _ _ _ h
  have hr := hrep.trans hf
  simp only [scoT, scoM0] at hr
  rw [smCs_eq]
  simp [scoT, scoM0, nock_exec, hL, smGut_eq, by.arm_at, by_arm, by.gut.arm_at, gut_arm, hgut', in.arm_at, in_arm,
    in.rep.arm_at, rep_arm, hr]

/-- **The trap of the `sub` loop is `scoSub`**: at every fuel, whenever the
model returns, the trap returns the same `sub`. -/
theorem sco_trap {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (B CA SC : Noun) (hCA : CallsOK CA) :
    ∀ n q SUB r, scoSub CA SC n q SUB = some r →
      nock (scoT (listN q) SUB (scoM0 B CA SC CTX)) smTrap = some r
  | 0, q, SUB, r, h => by simp [scoSub] at h
  | n + 1, [], SUB, r, h => by
    simp only [scoSub, Option.some.injEq] at h
    subst h
    rw [smTrap_eq]
    simp [scoT, scoM0, nock_exec, listN]
  | n + 1, x :: q, SUB, r, h => by
    simp only [scoSub] at h
    cases hg : getF mugF x SUB with
    | none => rw [hg] at h; cases h
    | some o =>
      rw [hg, Option.bind_some] at h
      have hh := has_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ x SUB o hg
      by_cases e : o = A 0
      · simp only [e, ne_eq, not_true_eq_false, if_false] at h
        cases hc : scoCs CA SC x with
        | none => rw [hc] at h; cases h
        | some cs =>
          rw [hc, Option.bind_some] at h
          cases hp : putF mugF x cs SUB with
          | none => rw [hp] at h; cases h
          | some sub' =>
            rw [hp, Option.bind_some] at h
            have ih := sco_trap hL B CA SC hCA n _ _ r h
            have hcs := sco_cs hL B CA SC x (listN q) SUB hCA cs hc
            have htap := nock_of_eval (tap_in layer2 cs (scoCs_set hc)).1
            have hw := weld_gate_list layer2 (tapList cs) q
            have hpb := put_gate layer2 gorIn_morIn_layer2 x cs SUB sub' hp
            simp only [scoT, scoM0] at ih hcs
            rw [smTrap_eq]
            simp [scoT, scoM0, nock_exec, hL, smTrapNo_eq, smHasQ_eq, smMain_eq, smRec_eq, by.arm_at, by_arm,
              by.has.arm_at, has_arm, hh, e, loob, hcs, in.arm_at, in_arm, in.tap.arm_at, htap, weld.arm_at,
              weld_arm, hw, by.put.arm_at, put_arm, hpb, ih]
      · simp only [ne_eq, e, not_false_eq_true, if_true] at h
        have ih := sco_trap hL B CA SC hCA n q SUB r h
        simp only [scoT, scoM0] at ih
        rw [smTrap_eq]
        simp [scoT, scoM0, nock_exec, hL, smTrapNo_eq, smHasQ_eq, by.arm_at, by_arm, by.has.arm_at, has_arm, hh,
          e, loob, ih]

/-- **`sub`**: the push `smSub` on the miss subject is `scoSub … [b] ~`. -/
theorem sco_sub {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (B CA SC : Noun) (hCA : CallsOK CA) (n : Nat)
    (r : Noun) (h : scoSub CA SC n [B] (A 0) = some r) :
    nock (scoM0 B CA SC CTX) smSub = some r := by
  have ht := sco_trap hL B CA SC hCA n [B] (A 0) r h
  simp only [scoT, scoM0, listN_cons, show listN [] = A 0 from rfl] at ht
  rw [smSub_eq]
  simp [scoM0, nock_exec, ht]

end Compiler
end Formalization
