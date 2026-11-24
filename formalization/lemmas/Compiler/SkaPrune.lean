import lemmas.Compiler.SkaCallgraph

/-!
# `+prune-callgraph` against `Ana.pruneCallgraph`

The gate `+prune-callgraph` is the arm `22007` of `ana` (`prune_cg_at`).  Its
battery `[8 [1 0] [8 [[0 29] [1 0]] [8 [1 loop] [9 2 0 1]]]]` pushes `out=~`
and `q=~[root]` and kicks the loop `prune_cg.loop` on the subject
`[loop [q [out [bat [[g root] ctx]]]]]` (`pruneSubj`).  The loop reads the
library's layer 2 through the context at axis `8191` (`+has:by`, `+got:by`,
`+put:by`, `+tap:in`, `+turn`, `+weld`), and its recursion is the formula
`prune_cg.loop` itself.  One turn over an evaluator `c` is `prune_stepW`,
against `pruneStepH`, which is `pruneLoop` one fuel up (`pruneLoop_succ`);
the loop under `evOne prune_cg.loop j` computes `pruneLoop` at fuel `j`
exactly (`pruneE_is`), so the loop and the gate return exactly what
`pruneLoop` and `pruneCallgraph` return at some fuel (`prune_loop_iff`,
`prune_gate_iff`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

set_option linter.unusedSimpArgs false

/-! ## Where the arm is -/

theorem prune_cg_at : slot? 22007 ana = some prune_cg.arm := by kernel_rfl

/-- Layer 2 in `ana`. -/
theorem ana_l2 : slot? 8191 ana = some layer2 := ana_layer2

/-! ## The maps of datums -/

/-- `+has:by` on the noun of a graph. -/
theorem pr_has (m : Callgraph FinMap) (k : Ident) :
    nock (C by.has.battery (C (identNoun k) (C by.battery (C (Treap.toNoun FDatum.toNoun m) layer2))))
      by.has.battery = some (loob (Treap.has m k)) := by
  have h := FinMap.getF_toNoun FDatum.toNoun m k
  show nock (C by.has.battery (C (TKey.enc k) (C by.battery (C (FinMap.toNoun FDatum.toNoun m) layer2))))
    by.has.battery = _
  rw [has_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _ h]
  show _ = some (loob (FinMap.get m k).isSome)
  cases FinMap.get m k <;> simp [unitNoun]

/-- `+got:by` on the noun of a graph, at a key it holds. -/
theorem pr_got (m : Callgraph FinMap) (k : Ident) (d : FDatum FinMap) (e : Treap.get m k = some d) :
    nock (C by.got.battery (C (identNoun k) (C by.battery (C (Treap.toNoun FDatum.toNoun m) layer2))))
      by.got.battery = some d.toNoun := by
  have h := FinMap.getF_toNoun FDatum.toNoun m k
  have e' : FinMap.get m k = some d := e
  rw [e'] at h
  exact got_gate layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _ h

/-- `+got:by` crashes at a key the graph does not hold. -/
theorem pr_got_none (m : Callgraph FinMap) (k : Ident) (e : Treap.get m k = none) :
    nock (C by.got.battery (C (identNoun k) (C by.battery (C (Treap.toNoun FDatum.toNoun m) layer2))))
      by.got.battery = none := by
  have h := FinMap.getF_toNoun FDatum.toNoun m k
  have e' : FinMap.get m k = none := e
  rw [e'] at h
  exact got_gate_nil layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ h

/-- `+put:by` on the noun of a graph. -/
theorem pr_put (m : Callgraph FinMap) (k : Ident) (d : FDatum FinMap) :
    nock (C by.put.battery (C (C (identNoun k) d.toNoun) (C by.battery (C (Treap.toNoun FDatum.toNoun m) layer2))))
      by.put.battery = some (Treap.toNoun FDatum.toNoun (Treap.put m k d)) :=
  put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun FDatum.toNoun m k d)

/-! ## The loop -/

/-- A formula other than the loop of `+prune-callgraph`, told apart by its cut. -/
def PFar (f : Noun) : Prop := ftrunc 8 f ≠ ftrunc 8 prune_cg.loop

instance : DecidablePred PFar := fun _ => inferInstanceAs (Decidable (_ ≠ _))

macro "pfar_disch" : tactic => `(tactic| (show PFar _; decide))

theorem PFar.ne {f : Noun} (h : PFar f) : f ≠ prune_cg.loop := fun e => h (e ▸ rfl)

/-- The subject of the loop: `[loop [q [out [bat [[g root] ctx]]]]]`. -/
noncomputable def pruneSubj (ctx : Noun) (g : Callgraph FinMap) (root : Ident) (q : List Ident)
    (out : Callgraph FinMap) : Noun :=
  C prune_cg.loop (C (listNoun identNoun q) (C (Treap.toNoun FDatum.toNoun out)
    (C prune_cg.battery (C (C (Treap.toNoun FDatum.toNoun g) (identNoun root)) ctx))))

/-- One turn of the loop, with its calls to itself as `go`. -/
noncomputable def pruneStepH (g : Callgraph FinMap)
    (go : List Ident → Callgraph FinMap → Option (Callgraph FinMap)) :
    List Ident → Callgraph FinMap → Option (Callgraph FinMap)
  | [], out => some out
  | i :: q, out =>
    if Treap.has out i = true then go q out else
    (Treap.get g i).bind fun d => go (q ++ (Treap.tap d.callees).map (·.1.id)) (Treap.put out i d)

theorem pruneLoop_succ (g : Callgraph FinMap) (n : Nat) :
    pruneLoop g (n + 1) = pruneStepH g (pruneLoop g n) := by
  funext q out
  match q with
  | [] => rfl
  | i :: q => rfl

/-- The gate of the `+turn`, `|=(callee-entry id)`, on the callees of `d`. -/
theorem pr_turn (d : FDatum FinMap) (bs bc : Noun) :
    nock (C turn.battery (C (C (listN ((Treap.tap d.callees).map fun e => TKey.enc e.1))
        (C (C (A 0) (A 13)) (C bs bc))) layer2)) turn.battery
      = some (listNoun identNoun ((Treap.tap d.callees).map (·.1.id))) := by
  rw [turn_gate layer2 homoIn_layer2 _ _ _ (fun x => match x with | Noun.cell _ b => b | _ => A 0) _
    (by
      intro x hx
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, TKey.enc, CalleeEntry.toNoun]),
    List.map_map, listNoun_map_listN, List.map_map]
  rfl

theorem pr_weld (q l : List Ident) :
    nock (C weld.battery (C (C (listNoun identNoun q) (listNoun identNoun l)) layer2)) weld.battery
      = some (listNoun identNoun (q ++ l)) := by
  rw [listNoun_map_listN, listNoun_map_listN, listNoun_map_listN, List.map_append]
  exact weld_gate_list layer2 _ _

set_option maxHeartbeats 1000000 in
/-- One turn of the loop over an evaluator `c` that is `nock` off the loop,
given what `c` returns on the loop's calls to itself. -/
theorem prune_stepW (c : Noun → Noun → Option Noun) (hcf : ∀ s f, PFar f → c s f = nock s f)
    (ctx : Noun) (hl2 : slot? 8191 ctx = some layer2) (g : Callgraph FinMap) (root : Ident)
    (go : List Ident → Callgraph FinMap → Option (Callgraph FinMap))
    (hgo : ∀ q out, c (pruneSubj ctx g root q out) prune_cg.loop = (go q out).map (Treap.toNoun FDatum.toNoun))
    (q : List Ident) (out : Callgraph FinMap) :
    nockW c (pruneSubj ctx g root q out) prune_cg.loop
      = (pruneStepH g go q out).map (Treap.toNoun FDatum.toNoun) := by
  match q with
  | [] =>
    nockW_open prune_cg.loop
    simp (disch := pfar_disch) [nock_exec, hcf, pruneSubj, listNoun, pruneStepH]
  | i :: q =>
    have h1 := hgo q out
    simp only [pruneSubj] at h1
    have hh := pr_has out i
    cases e1 : Treap.has out i
    · cases e2 : Treap.get g i with
      | none =>
        have hn := pr_got_none g i e2
        nockW_open prune_cg.loop
        simp (disch := pfar_disch) [nock_exec, hcf, pruneSubj, listNoun, pruneStepH, hl2, by.arm_at, by_arm,
          by.has.arm_at, has_arm, hh, e1, e2, by.got.arm_at, got_arm, hn]
      | some d =>
        have h2 := hgo (q ++ (Treap.tap d.callees).map (·.1.id)) (Treap.put out i d)
        simp only [pruneSubj] at h2
        have hg := pr_got g i d e2
        have hp := pr_put out i d
        have htap := tap_in_setNoun d.callees
        have hturn := pr_turn d (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))))
          (C d.toNoun (pruneSubj ctx g root (i :: q) out))
        have hweld := pr_weld q ((Treap.tap d.callees).map (·.1.id))
        simp only [pruneSubj, listNoun] at hturn
        simp only [FDatum.toNoun] at hp hturn
        nockW_open prune_cg.loop
        simp (disch := pfar_disch) [nock_exec, hcf, pruneSubj, listNoun, pruneStepH, hl2, by.arm_at, by_arm,
          by.has.arm_at, has_arm, hh, e1, e2, by.got.arm_at, got_arm, hg, by.put.arm_at, put_arm, hp,
          in.arm_at, in_arm, in.tap.arm_at, htap, FDatum.toNoun, turn.arm_at, turn_arm, hturn,
          weld.arm_at, weld_arm, hweld, h2]
    · nockW_open prune_cg.loop
      simp (disch := pfar_disch) [nock_exec, hcf, pruneSubj, listNoun, pruneStepH, hl2, by.arm_at, by_arm,
        by.has.arm_at, has_arm, hh, e1, h1]

theorem evOne_ne (lf : Noun) (j : Nat) {s f : Noun} (h : f ≠ lf) : evOne lf j s f = nock s f := by
  cases j <;> simp only [evOne, if_neg h]

/-- Under `evOne` of the loop, `j` deep, the loop computes `pruneLoop` at
fuel `j`, exactly. -/
theorem pruneE_is (ctx : Noun) (hl2 : slot? 8191 ctx = some layer2) (g : Callgraph FinMap) (root : Ident) :
    ∀ (j : Nat) (q : List Ident) (out : Callgraph FinMap),
    evOne prune_cg.loop j (pruneSubj ctx g root q out) prune_cg.loop
      = (pruneLoop g j q out).map (Treap.toNoun FDatum.toNoun)
  | 0, _, _ => by simp [evOne, pruneLoop]
  | j + 1, q, out => by
    simp only [evOne, if_true]
    rw [prune_stepW (evOne prune_cg.loop j) (fun _ _ h => evOne_ne _ j h.ne) ctx hl2 g root
      (pruneLoop g j) (pruneE_is ctx hl2 g root j) q out, pruneLoop_succ]

/-- **The loop of `+prune-callgraph`** returns exactly what `pruneLoop`
returns at some fuel. -/
theorem prune_loop_iff (ctx : Noun) (hl2 : slot? 8191 ctx = some layer2) (g : Callgraph FinMap) (root : Ident)
    (q : List Ident) (out : Callgraph FinMap) (x : Noun) :
    nock (pruneSubj ctx g root q out) prune_cg.loop = some x ↔
      ∃ n r, pruneLoop g n q out = some r ∧ x = Treap.toNoun FDatum.toNoun r := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := iterN_complete h
    have he := iterN_le_evOne prune_cg.loop j _ _ x hj
    rw [pruneE_is ctx hl2 g root j] at he
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 he
    exact ⟨j, r, hr, rfl⟩
  · rintro ⟨n, r, hr, rfl⟩
    have he := pruneE_is ctx hl2 g root n q out
    rw [hr] at he
    exact evOne_le_nock _ n _ _ _ he

/-- The battery of the gate runs the loop on `q = ~[root]` and `out = ~`. -/
theorem prune_battery_run (ctx : Noun) (g : Callgraph FinMap) (root : Ident) :
    nock (C prune_cg.battery (C (C (Treap.toNoun FDatum.toNoun g) (identNoun root)) ctx)) prune_cg.battery
      = nock (pruneSubj ctx g root [root] Treap.empty) prune_cg.loop := by
  have e : Treap.toNoun FDatum.toNoun (Treap.empty : Callgraph FinMap) = A 0 := FinMap.toNoun_empty _
  unfold pruneSubj
  rw [e]
  nock_open prune_cg.battery
  simp only [nock_exec, listNoun, Option.bind_some]

/-- **`+prune-callgraph`**: the gate on `[g root]`, in a context with layer 2
at `8191`, returns exactly what `pruneCallgraph` returns at some fuel. -/
theorem prune_gate_iff (ctx : Noun) (hl2 : slot? 8191 ctx = some layer2) (g : Callgraph FinMap) (root : Ident)
    (x : Noun) :
    nock (C prune_cg.battery (C (C (Treap.toNoun FDatum.toNoun g) (identNoun root)) ctx)) prune_cg.battery
      = some x ↔ ∃ n r, pruneCallgraph n g root = some r ∧ x = Treap.toNoun FDatum.toNoun r := by
  rw [prune_battery_run]
  exact prune_loop_iff ctx hl2 g root [root] Treap.empty x

/-- The arm builds the gate, with the bunt `[~ *identity]` as its sample. -/
theorem prune_arm_run (ctx : Noun) :
    nock ctx prune_cg.arm = some (C prune_cg.battery (C (C (A 0) identBunt) ctx)) := by
  nock_open prune_cg.arm
  simp only [nock_exec, identBunt]

end Compiler
end Formalization
