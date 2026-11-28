import lemmas.Compiler.PokeLinkGood7

/-!
# `new-cores` linked: `srCores` is `newCoresO` (track P, README Gaps 23)

Push 10 of `spRest` (54 cells):

    =/  new-cores  (~(gas ju *(jug path sock)) (turn new.regs |=([p=path s=sock *] [p s])))

On the tail's subject `srT10` (layer 2 at axis `0x7ffffff`, `new.regs` at
`0x1ffdf` of `[turn-gate subject]`): the gate of `+gas:ju` (arm 22 of `ju`,
arm 760 of layer 2) on `~`, slammed on the `+turn` (arm `0xbef7e`) of the
list with the gate `[[0 12] [0 26]]` (`turn_gate_mapM`, the pair `[p s]`
read by `turnPairO`), runs the loop of `+gas:ju` (`ju_gas_loop`).

* `listN_of_nounList`, `mapM_turnPair`;
* **`srCores_run`**: where `newCoresO new = some nco`, `srCores` returns
  `nco` on every `srT10` subject whose regs are `[ro co ba ar new]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

theorem listN_of_nounList : ∀ (x : Noun) (l : List Noun), nounList? x = some l → x = listN l
  | Noun.atom 0, l, h => by simp only [nounList?, Option.some.injEq] at h; subst h; rfl
  | Noun.atom (_ + 1), _, h => by simp [nounList?] at h
  | Noun.cell i t, l, h => by
    simp only [nounList?] at h
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 h
    rw [listN_of_nounList t l' hl']
    rfl

/-- The pairs `[p s]` of `+turn`, as nouns. -/
def turnPairN (x : Noun) : Option Noun := (turnPairO x).map pairNoun

theorem mapM_turnPair : ∀ l : List Noun, l.mapM turnPairN = (l.mapM turnPairO).map (List.map pairNoun)
  | [] => rfl
  | x :: l => by
    simp only [List.mapM_cons, turnPairN]
    cases turnPairO x with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.bind_some, mapM_turnPair l]
      cases l.mapM turnPairO <;> rfl

/-- The battery of the gate of `+turn` in `new-cores`. -/
def coresBat : Noun := C (C (A 0) (A 12)) (C (A 0) (A 26))

/-- Its bunt sample. -/
def coresSam : Noun := C (A 0) (C (C (A 1) (A 0)) (A 0))

theorem coresBat_run (x S : Noun) : nock (C coresBat (C x S)) coresBat = turnPairN x := by
  match x with
  | Noun.atom _ => simp [coresBat, turnPairN, turnPairO, nock_exec]
  | Noun.cell p (Noun.atom _) => simp [coresBat, turnPairN, turnPairO, nock_exec]
  | Noun.cell p (Noun.cell s _) => simp [coresBat, turnPairN, turnPairO, pairNoun, nock_exec]

/-- The gate of `+gas:ju` on a door with sample `a`. -/
theorem ju_gas_gate (ctx : Noun) (hc : JuIn mugF ctx) (l : List (Noun × Noun)) (a out : Noun)
    (h : juGasF mugF a l = some out) :
    nock (C ju.gas.battery (C (listN (l.map pairNoun)) (C ju.battery (C a ctx)))) ju.gas.battery = some out := by
  have hl := ju_gas_loop ctx hc l a out h
  nock_open ju.gas.battery
  simp [nock_exec, hl]

set_option maxHeartbeats 2000000 in
/-- **`new-cores` linked**: on the tail's subject whose regs are
`[ro co ba ar nw]`, `srCores` returns the model's `newCoresO nw`. -/
theorem srCores_run (q ncN bkN g0 rN a b c g1 ro co ba ar nw e e0 J mN cN caN vN sN hN nco : Noun)
    (h : newCoresO nw = some nco) :
    nock (srT10 q ncN bkN g0 rN a b c (C g1 (C ro (C co (C ba (C ar nw))))) e e0 J mN cN caN vN sN hN) srCores =
      some nco := by
  unfold newCoresO at h
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ps, hps, h⟩ := Option.bind_eq_some_iff.1 h
  rw [listN_of_nounList nw l hl]
  have hL2 : slot? 0x7ffffff (srT10 q ncN bkN g0 rN a b c (C g1 (C ro (C co (C ba (C ar (listN l)))))) e e0 J mN cN
      caN vN sN hN) = some layer2 := by
    simp [srT10, srS3x, srSk, srSam, nock_exec, ana_l2]
  have hNw : slot? 0xffdf (srT10 q ncN bkN g0 rN a b c (C g1 (C ro (C co (C ba (C ar (listN l)))))) e e0 J mN cN
      caN vN sN hN) = some (listN l) := by
    simp [srT10, srS3x, srSk, srSam, nock_exec]
  generalize srT10 q ncN bkN g0 rN a b c (C g1 (C ro (C co (C ba (C ar (listN l)))))) e e0 J mN cN caN vN sN hN = S
    at hL2 hNw ⊢
  have hturn : nock (C turn.battery (C (C (listN l) (C coresBat (C coresSam S))) layer2)) turn.battery =
      some (listN (ps.map pairNoun)) := by
    rw [turn_gate_mapM layer2 homoIn_layer2 coresBat coresSam S turnPairN l (fun x _ => coresBat_run x S),
      mapM_turnPair, hps]
    rfl
  have hgas := ju_gas_gate layer2 juIn_layer2 ps (A 0) nco h
  unfold srCores
  simp only [nock_exec, hL2, hNw, ju.arm_at, ju_arm, ju.gas.arm_at, ju_gas_arm, turn.arm_at, turn_arm,
    Option.bind_some]
  simp only [coresBat, coresSam] at hturn
  rw [hturn]
  simp [nock_exec, hgas]

end Compiler
end Formalization
