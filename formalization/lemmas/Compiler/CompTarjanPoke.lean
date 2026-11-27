import lemmas.Compiler.CompTarjanJug
import lemmas.Compiler.CompTarjanLink
import lemmas.Compiler.PokeLinkRestNew

/-!
# Push 8 of `spRest`: `+tarjan` on the jug of `new-code`, flopped (track Q)

`desk/lib/nock-compilation.hoon`, `+ska-poke`:

    =/  sccs=(list (set bell))
      ?:  =(~ new-code)  ~
      %-  flop
      =<  $  ~%  %poke-tarjan  ..ride  ~  |.
      %-  tarjan
      ^-  (jug bell bell)
      %-  ~(rep by new-code)
      |=  [[b=bell v=[=nomm calls=(set bell) seek=cape]] acc=(jug bell bell)]
      %+  ~(put by acc)  b
      %-  silt
      (skim ~(tap in calls.v) |=(c=bell (~(has by new-code) c)))

The formula (`srSccs`, 188 cells) is cut into its pieces by
`tools/gen/tarjanpoke.py` (`srSccs_eq`, by `rfl`).  On the subject
`[new-code baked SP]`, `SP` any noun with the hoon core at `0xffffff` and
`ana` at `4095` (`srSp` has both, `srSp_l2`, `srSp_ana`):

* `tp_has`: the gate of the `skim`: `+has:by` on `new-code`;
* `tp_silt`: `(silt (skim ~(tap in calls.v) ..))` is the set noun of
  `keysIn nc calls.v`;
* `tp_gate`: the gate of the `rep`: `+put:by` of `b` with that set;
* `tp_jug`: the `rep` is `jugNoun nc` (`jugOf_foldl`);
* `tp_trap`: the trap slams `+tarjan` (`tarjanLinkAt_jug`);
* **`srSccs_empty`**: on an empty `new-code`, `~`;
* **`srSccs_tarjan`**: otherwise, when `tarjanM` of the jug's graph returns
  `L`, the list of the set nouns of `L` (`TjFinIs`), flopped.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

-- BEGIN tarjanpoke
/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpHBunt : Noun :=
  (C (C (A 1) (A 0)) (C (A 0) (A 0)))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpHB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpTap : Noun :=
  (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2))))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpSkim : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x5f7bb) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C tpTap (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) tpHBunt) (C (C (A 1) tpHB) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpSilt : Noun :=
  (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) tpSkim))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpPutDoor : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17d7) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpGB : Noun :=
  (C (A 8) (C tpPutDoor (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 7) (C (C (A 0) (A 3)) tpSilt)))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpBunt : Noun :=
  (C (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 1)))) (A 0))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpRepDoor : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17d7) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpJug : Noun :=
  (C (A 8) (C tpRepDoor (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) tpBunt) (C (C (A 1) tpGB) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpTrap : Noun :=
  (C (A 8) (C (C (A 9) (C (A 2815) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) tpJug))) (C (A 0) (A 2))))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6e616a7261742d656b6f70) (C (C (A 0) (A 0xffffff)) (A 0))))) (C (A 0) (A 1))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpRun : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) tpTrap) tpHint)) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

/-- A piece of push 8 (`tools/gen/tarjanpoke.py`). -/
def tpFlop : Noun :=
  (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x3ffffff))))

theorem srSccs_eq : srSccs = (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 8) (C tpFlop (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) tpRun))) (C (A 0) (A 2))))))))))) := rfl

-- END tarjanpoke

/-! ## The arms -/

/-- The arm `+skim` of `layer2`, its hint and bunt (as `OptLinkOnceAfter.lean`). -/
def tpSkimHint : Noun :=
  C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6d696b73) (C (C (A 0) (A 7)) (A 0))))) (C (A 0) (A 1)))

def tpSkimBunt : Noun := C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))

theorem tp_skim_arm_eq : skim.arm
    = C (A 7) (C (C (A 8) (C (C (A 1) tpSkimBunt) (C (C (A 1) skim.battery) (C (A 0) (A 1))))) tpSkimHint) := by
  kernel_rfl

@[nock_exec] theorem tp_skim_arm (d : Noun) : nock d skim.arm = some (C skim.battery (C tpSkimBunt d)) := by
  rw [tp_skim_arm_eq]; unfold tpSkimHint; generalize skim.battery = B; generalize tpSkimBunt = U; simp [nock_exec]

theorem tp_tjArm_at : slot? 2815 ana = some tjArm := by kernel_rfl

/-! ## The gates, on an abstract subject -/

section Gates

variable {SP NCN BKN : Noun} (hL2 : slot? 0xffffff SP = some layer2)

/-- The gate core of the `rep` on a node `x` and an accumulator `acc`. -/
def tpGC (x acc NCN BKN SP : Noun) : Noun := C tpGB (C (C x acc) (C tpTrap (C NCN (C BKN SP))))

include hL2 in
set_option maxHeartbeats 1000000 in
/-- **The gate of the `skim`**: `(~(has by new-code) c)`. -/
theorem tp_has (x acc c out : Noun) (h : getF mugF c NCN = some out) :
    nock (C tpHB (C c (tpGC x acc NCN BKN SP))) tpHB = some (loob (decide (out ≠ A 0))) := by
  have hh := has_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ c NCN out h
  unfold tpHB tpGC
  simp [nock_exec, hL2, by.arm_at, by_arm, by.has.arm_at, has_arm, hh]

/-- The test of the `skim`, on a member's noun. -/
def tpP (NCN : Noun) (x : Noun) : Bool :=
  match getF mugF x NCN with
  | some out => decide (out ≠ A 0)
  | none => false

include hL2 in
set_option maxHeartbeats 1000000 in
/-- **`(silt (skim ~(tap in calls.v) ..))`** on a node `[b [nomm calls seek]]`. -/
theorem tp_silt (bn nomN seekN acc : Noun) (calls : FinMap Bell Unit) (out : Noun)
    (hg : ∀ x, getF mugF x NCN ≠ none)
    (ho : gasInF mugF (A 0) ((((Treap.tap calls).map fun e => TKey.enc e.1)).filter (tpP NCN)) = some out) :
    nock (tpGC (C bn (C nomN (C (FinMap.setNoun calls) seekN))) acc NCN BKN SP) tpSilt = some out := by
  have htap : nock (C in.battery (C (FinMap.setNoun calls) layer2)) by.tap.arm
      = some (listN ((Treap.tap calls).map fun e => TKey.enc e.1)) := tap_in_setNoun calls
  have hsk := skim_gate layer2 tpHB tpHBunt (tpGC (C bn (C nomN (C (FinMap.setNoun calls) seekN))) acc NCN BKN SP)
    (tpP NCN) ((Treap.tap calls).map fun e => TKey.enc e.1) (fun x _ => by
      cases e : getF mugF x NCN with
      | none => exact absurd e (hg x)
      | some o =>
        rw [tp_has hL2 _ _ x o e]
        simp [tpP, e])
  have hs := silt_gate _ out ho
  unfold tpSilt tpSkim tpTap
  unfold tpGC at hsk ⊢
  simp [nock_exec, hL2, silt_arm_at, silt_arm, skim.arm_at, tp_skim_arm, in.arm_at, in_arm, in.tap.arm_at,
    htap, hsk, hs]

/-- `getF` returns on a map. -/
theorem tp_getF_total {a : Noun} (h : IsMap mugF a) (x : Noun) : getF mugF x a ≠ none := by
  by_cases e : ∃ w, Get a x w
  · obtain ⟨w, hw⟩ := e; rw [getF_some h hw]; simp
  · rw [getF_none h (fun w hw => e ⟨w, hw⟩)]; simp

/-- The members `skim` keeps are the keys of `nc`: the `silt` is the set noun
of `keysIn nc calls`. -/
theorem tp_keys (nc : FinMap Bell (VarEntry FinMap)) (calls : FinMap Bell Unit) :
    gasInF mugF (A 0) (((Treap.tap calls).map fun e => TKey.enc e.1).filter (tpP (nc.toNoun varEntryNoun)))
      = some (FinMap.setNoun (keysIn nc calls)) := by
  obtain ⟨out, h, hs, hh⟩ := gasInF_spec (mug := mugF)
    (((Treap.tap calls).map fun e => TKey.enc e.1).filter (tpP (nc.toNoun varEntryNoun))) (A 0) isSet_nil
  rw [h]
  congr 1
  apply isSet_ext hs (FinMap.isSet_setNoun _)
  intro kn
  rw [hh, FinMap.has_setNoun]
  have h0 : ¬ Has (A 0) kn := by unfold Has; exact Get_atom
  have hp : ∀ k, tpP (nc.toNoun varEntryNoun) (TKey.enc k) = true ↔ ∃ e, FinMap.get nc k = some e := by
    intro k
    unfold tpP
    rw [FinMap.getF_toNoun]
    cases e : FinMap.get nc k with
    | none => simp [unitNoun]
    | some v => simp [unitNoun]
  simp only [h0, or_false, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨⟨k, u⟩, hk, rfl⟩, hq⟩
    refine ⟨k, ?_, rfl⟩
    have h1 : calls.1 k = some u := (FinMap.mem_tap calls k u).1 hk
    exact (keysIn_get nc calls k).2 ⟨h1, (hp k).1 hq⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (keysIn_get nc calls k).1 hk
    exact ⟨⟨(k, ()), (FinMap.mem_tap calls k ()).2 h1, rfl⟩, (hp k).2 h2⟩

include hL2 in
set_option maxHeartbeats 1000000 in
/-- **The gate of the `rep`** on a node `[b v]` of `new-code`. -/
theorem tp_gate (nc : FinMap Bell (VarEntry FinMap)) (b : Bell) (e : VarEntry FinMap)
    (s : FinMap Bell (FinMap Bell Unit)) :
    nock (tpGC (C (TKey.enc b) (varEntryNoun e)) (s.toNoun FinMap.setNoun) (nc.toNoun varEntryNoun) BKN SP) tpGB
      = some ((s.put b (keysIn nc e.calls)).toNoun FinMap.setNoun) := by
  have hsl := tp_silt (NCN := nc.toNoun varEntryNoun) (BKN := BKN) hL2 (TKey.enc b) e.nomm.toNoun e.seek.toNoun (s.toNoun FinMap.setNoun) e.calls _
    (tp_getF_total (FinMap.isMap_toNoun varEntryNoun nc)) (tp_keys nc e.calls)
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (TKey.enc b) (FinMap.setNoun (keysIn nc e.calls))
    (s.toNoun FinMap.setNoun) _ (FinMap.putF_toNoun FinMap.setNoun s b _)
  have hv : varEntryNoun e = C e.nomm.toNoun (C (FinMap.setNoun e.calls) e.seek.toNoun) := rfl
  rw [hv]
  unfold tpGC at hsl ⊢
  conv => lhs; arg 2; unfold tpGB
  simp [nock_exec, tpPutDoor, hL2, by.arm_at, by_arm, by.put.arm_at, put_arm, hsl, hput]

/-- The step of the `rep` on a node noun of `new-code`. -/
noncomputable def tpF (nc : FinMap Bell (VarEntry FinMap)) (x : Noun) (s : FinMap Bell (FinMap Bell Unit)) :
    FinMap Bell (FinMap Bell Unit) :=
  match FinMap.entry nc x with
  | some e => FinMap.put s e.1 (keysIn nc e.2.calls)
  | none => s

theorem tp_foldl (nc : FinMap Bell (VarEntry FinMap)) :
    ∀ (L : List (Bell × VarEntry FinMap)), (∀ e ∈ L, nc.1 e.1 = some e.2) → ∀ s,
    (L.map fun e => C (TKey.enc e.1) (varEntryNoun e.2)).foldl (fun s x => tpF nc x s) s
      = L.foldl (fun acc p => FinMap.put acc p.1 (keysIn nc p.2.calls)) s
  | [], _, _ => rfl
  | e :: L, h, s => by
    have he := h e List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    have : tpF nc (C (TKey.enc e.1) (varEntryNoun e.2)) s = FinMap.put s e.1 (keysIn nc e.2.calls) := by
      simp [tpF, FinMap.entry, FinMap.decode?_enc, he]
    rw [this]
    exact tp_foldl nc L (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _

include hL2 in
set_option maxHeartbeats 1000000 in
/-- **The `rep`**: the jug of `new-code`. -/
theorem tp_jug (nc : FinMap Bell (VarEntry FinMap)) :
    nock (C tpTrap (C (nc.toNoun varEntryNoun) (C BKN SP))) tpJug = some (jugNoun nc) := by
  have hr := rep_gate_on (fun s : FinMap Bell (FinMap Bell Unit) => s.toNoun FinMap.setNoun) (tpF nc)
    by.battery layer2 tpGB (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 1))))
    (C tpTrap (C (nc.toNoun varEntryNoun) (C BKN SP))) (nc.toNoun varEntryNoun)
    (Tree.of_isMap (FinMap.isMap_toNoun varEntryNoun nc)) FinMap.empty ?hf
  · rw [FinMap.toNoun_empty] at hr
    rw [FinMap.preorder_toNoun, tp_foldl nc _ (fun e he => (FinMap.mem_rap nc e.1 e.2).1 he), jugOf_foldl] at hr
    unfold tpJug tpRepDoor tpBunt
    simp [nock_exec, hL2, by.arm_at, by_arm, by.rep.arm_at, rep_arm, hr]
    rfl
  · intro x hx s
    rw [FinMap.preorder_toNoun] at hx
    obtain ⟨⟨k, v⟩, hm, rfl⟩ := List.mem_map.1 hx
    have hkv := (FinMap.mem_rap nc k v).1 hm
    have : tpF nc (C (TKey.enc k) (varEntryNoun v)) s = FinMap.put s k (keysIn nc v.calls) := by
      simp [tpF, FinMap.entry, FinMap.decode?_enc, hkv]
    rw [this]
    exact tp_gate hL2 nc k v s

/-- The jug is a `TjJug`, a cell once `nc` has a key. -/
theorem tjJug_jugNoun (nc : FinMap Bell (VarEntry FinMap)) : TjJug (jugNoun nc) := by
  refine ⟨FinMap.isMap_toNoun _ _, fun k v hg => ?_⟩
  obtain ⟨b, S, -, -, rfl⟩ := (FinMap.get_toNoun _ _ k v).1 hg
  exact FinMap.isSet_setNoun S

theorem jugNoun_ne {nc : FinMap Bell (VarEntry FinMap)} {b0 : Bell} {e0 : VarEntry FinMap}
    (h0 : FinMap.get nc b0 = some e0) : jugNoun nc ≠ A 0 := by
  intro e
  have hg : Get (jugNoun nc) (TKey.enc b0) (FinMap.setNoun (keysIn nc e0.calls)) :=
    (FinMap.get_toNoun _ _ _ _).2 ⟨b0, keysIn nc e0.calls, by
      show FinMap.get (jugOf nc) b0 = _; rw [jugOf_get, h0]; rfl, rfl, rfl⟩
  rw [e] at hg
  exact Get_atom hg

variable (hA : slot? 4095 SP = some ana)

include hL2 hA in
set_option maxHeartbeats 1000000 in
/-- **The trap**: `+tarjan` slammed on the jug. -/
theorem tp_trap (nc : FinMap Bell (VarEntry FinMap)) {b0 : Bell} {e0 : VarEntry FinMap}
    (h0 : FinMap.get nc b0 = some e0) {L : List (List Noun)} (hL : tarjanM (tjGraph (jugNoun nc)) = some L) :
    ∃ FIN, TjFinIs FIN L ∧
      nock (C tpTrap (C (nc.toNoun varEntryNoun) (C BKN SP))) tpTrap = some FIN := by
  obtain ⟨FIN, hF, hn⟩ := tarjanLinkAt_jug (tjJug_jugNoun nc) (jugNoun_ne h0) L hL
  have hj := tp_jug (BKN := BKN) hL2 nc
  refine ⟨FIN, hF, ?_⟩
  conv => lhs; arg 2; unfold tpTrap
  simp [nock_exec, hA, tp_tjArm_at, tjArm_gate, hj, hn]

/-- The noun of `fin` is a list noun. -/
theorem tjFinIs_listN' : ∀ (L : List (List Noun)) (FIN : Noun), TjFinIs FIN L → ∃ Ss, FIN = listN Ss
  | [], FIN, h => ⟨[], h⟩
  | l :: ls, FIN, h => by
    obtain ⟨S, REST, rfl, -, hR⟩ := h
    obtain ⟨Ss, rfl⟩ := tjFinIs_listN' ls REST hR
    exact ⟨S :: Ss, rfl⟩

include hL2 hA in
set_option maxHeartbeats 1000000 in
/-- **Push 8 on a nonempty `new-code`**, on an abstract rest `[baked SP]`. -/
theorem tp_sccs (nc : FinMap Bell (VarEntry FinMap)) {b0 : Bell} {e0 : VarEntry FinMap}
    (h0 : FinMap.get nc b0 = some e0) {L : List (List Noun)} (hL : tarjanM (tjGraph (jugNoun nc)) = some L) :
    ∃ Ss : List Noun, TjFinIs (listN Ss) L ∧
      nock (C (nc.toNoun varEntryNoun) (C BKN SP)) srSccs = some (listN Ss.reverse) := by
  obtain ⟨FIN, hF, ht⟩ := tp_trap (BKN := BKN) hL2 hA nc h0 hL
  obtain ⟨Ss, rfl⟩ := tjFinIs_listN' L FIN hF
  refine ⟨Ss, hF, ?_⟩
  have hfl := flop_gate layer2 homoIn_layer2 Ss
  have hne : nc.toNoun varEntryNoun ≠ A 0 := by
    intro e
    have hg := FinMap.getF_toNoun varEntryNoun nc b0
    rw [e, h0] at hg
    simp [getF, unitNoun] at hg
  generalize hN : nc.toNoun varEntryNoun = NC at ht hne
  rw [srSccs_eq]
  unfold tpRun tpHint tpFlop
  cases NC with
  | atom a =>
    cases a with
    | zero => exact absurd rfl hne
    | succ a => simp [nock_exec, hL2, flop.arm_at, flop_arm, ht, hfl]
  | cell x y => simp [nock_exec, hL2, flop.arm_at, flop_arm, ht, hfl]

theorem tp_empty (nc : FinMap Bell (VarEntry FinMap)) (h : ∀ b, FinMap.get nc b = none) :
    nock (C (nc.toNoun varEntryNoun) (C BKN SP)) srSccs = some (A 0) := by
  have e : nc = FinMap.empty := Subtype.ext (funext h)
  subst e
  rw [FinMap.toNoun_empty, srSccs_eq]
  simp [nock_exec]

end Gates

/-! ## On the subject of `SccsLeafAt` -/

section Leaf

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

theorem srSp_l2 (c v : Noun) :
    slot? 0xffffff (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r c v) = some layer2 := by
  simp [srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2]

theorem srSp_ana (c v : Noun) :
    slot? 4095 (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r c v) = some ana := by
  simp [srSp, srS3x, srS0, spAfter, spT0, nock_exec]

/-- **Push 8 on an empty `new-code`**: `~`. -/
theorem srSccs_empty (nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) (h : ∀ b, FinMap.get nc b = none) :
    nock (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr))) srSccs = some (A 0) :=
  tp_empty nc h

/-- **Push 8 on a nonempty `new-code`**: when `tarjanM` of the jug's graph
returns `L`, the pill returns the list of the set nouns of `L`, flopped. -/
theorem srSccs_tarjan (nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) {b0 : Bell} {e0 : VarEntry FinMap}
    (h0 : FinMap.get nc b0 = some e0) {L : List (List Noun)} (hL : tarjanM (tjGraph (jugNoun nc)) = some L) :
    ∃ Ss : List Noun, TjFinIs (listN Ss) L ∧
      nock (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
        (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr))) srSccs =
        some (listN Ss.reverse) :=
  tp_sccs (srSp_l2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr)
    (srSp_ana root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr) nc h0 hL

end Leaf

end Compiler
end Formalization
