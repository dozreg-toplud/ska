import lemmas.Compiler.SkaPrune
import lemmas.Compiler.GitMi

/-!
# `+memo-final-entry` and the analysis part of `+ska-poke`

`+memo-final-entry` is the gate at arm `340` of `ana` (`mfe_at`), with the
battery `mfeBat` written out here:
`[[[8 [7 [9 20 [0 31]] [9 341 [0 1]]] [9 2 [10 [6 [[0 478] [0 56]]] [0 2]]]] [0 25]] [10 [2 [1 0]] [0 13]]]`,
that is `[[(app:ca indi.d more.id) fol.id] d(callees ~)]` with `+app:ca`
pulled from `lib` at axis `7` of its context (`mfe_gate`, against
`Ana.memoFinalEntry`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

set_option linter.unusedSimpArgs false

/-! ## `+memo-final-entry` -/

/-- The battery of the gate `+memo-final-entry`. -/
def mfeBat : Noun :=
  let pull := C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 31)))) (C (A 9) (C (A 341) (C (A 0) (A 1)))))
  let slam := C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 478)) (C (A 0) (A 56)))) (C (A 0) (A 2)))))
  C (C (C (A 8) (C pull slam)) (C (A 0) (A 25)))
    (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 13))))

/-- The bunt of the sample of `+memo-final-entry`, kept whole. -/
noncomputable def mfeBunt : Noun := (slot? 2725 ana).getD (A 0)

theorem mfe_at : slot? 340 ana = some (C (A 8) (C (C (A 1) mfeBunt) (C (C (A 1) mfeBat) (C (A 0) (A 1))))) := by
  kernel_rfl

theorem mfe_arm_run (ctx : Noun) (h : slot? 340 ctx = slot? 340 ana) :
    nock ctx (C (A 9) (C (A 340) (C (A 0) (A 1)))) = some (C mfeBat (C mfeBunt ctx)) := by
  rw [nock_op9, nock_op0]
  simp only [slot?_one, Option.bind_some, h, mfe_at]
  simp only [nock_exec]

theorem ana_lib7 : slot? 7 ana = some lib := knit_anno.lib.arm_at

/-- **`+memo-final-entry`** on `[id d]`, in a context with `lib` at axis `7`,
returns the noun of `Ana.memoFinalEntry id d`. -/
theorem mfe_gate (ctx : Noun) (hlib : slot? 7 ctx = some lib) (id : Ident) (d : FDatum FinMap) :
    nock (C mfeBat (C (C (identNoun id) d.toNoun) ctx)) mfeBat
      = some (C (identNoun (memoFinalEntry id d).1) (memoFinalEntry id d).2.toNoun) := by
  have hs : Treap.setNoun (Treap.empty : FinMap CalleeEntry Unit) = A 0 := FinMap.setNoun_empty
  unfold mfeBat
  simp only [nock_exec, hlib, Option.bind_some, ca.lib.arm_at, ca_lib_arm, ca.app.arm_at, ca_app_arm,
    identNoun, FDatum.toNoun, ca_app_pill, memoFinalEntry, hs]

/-! ## The gate of `~(rep by pruned)` in the trap `%poke-just-code` -/

/-- Its head: `(~(put by dats) [less-code.d fol.id] d)`. -/
def pjHead : Noun :=
  let door := C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 8388607))))
    (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))
  let key := C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 206)) (C (A 0) (A 49))))
  C (A 8) (C door (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C key (C (A 0) (A 57)))) (C (A 0) (A 2)))))))

/-- Its tail: `(put:mi memo -.entry +.entry)` of `entry=(memo-final-entry id d)`. -/
def pjTail : Noun :=
  let mfe := C (A 8) (C (C (A 9) (C (A 340) (C (A 0) (A 2047))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 0) (A 57)))) (C (A 0) (A 2)))))))
  let pm := C (A 7) (C (C (A 9) (C (A 84) (C (A 0) (A 4095)))) (C (A 9) (C (A 4) (C (A 0) (A 1)))))
  let sl := C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 123)) (C (C (A 0) (A 12)) (C (A 0) (A 13)))))
    (C (A 0) (A 2)))))
  C (A 8) (C mfe (C (A 8) (C pm sl)))

/-- The battery of the gate of the `+rep`. -/
def pjGate : Noun := C pjHead pjTail

/-- The accumulator `[dats memo]` of the `+rep`. -/
noncomputable def pjAcc (s : FinMap Bell (FDatum FinMap) × Memo FinMap) : Noun :=
  C (Treap.toNoun FDatum.toNoun s.1) (memoNoun s.2)

/-- One step of `pokeMemo`. -/
noncomputable def pjStep (s : FinMap Bell (FDatum FinMap) × Memo FinMap) (e : Ident × FDatum FinMap) :
    FinMap Bell (FDatum FinMap) × Memo FinMap :=
  (Treap.put s.1 ⟨e.2.less, e.1.2⟩ e.2,
   let me := memoFinalEntry e.1 e.2
   putMi s.2 me.1 me.2)

/-- The layout that the gate reads from the context `bc` of its core: `ana`
(as `ctx`) at `511`, layer 2 at `2097151`. -/
structure PjCtx (bc ctx : Noun) : Prop where
  hctx : slot? 511 bc = some ctx
  l2 : slot? 2097151 bc = some layer2
  mfe : slot? 340 ctx = some (C (A 8) (C (C (A 1) mfeBunt) (C (C (A 1) mfeBat) (C (A 0) (A 1)))))
  lib : slot? 7 ctx = some lib
  mi : slot? 84 ctx = some mi.arm
  miIn : MiIn ctx

set_option maxHeartbeats 1000000 in
/-- **The gate of the `+rep`** on one entry `[id d]` and the accumulator. -/
theorem pj_gate {bc ctx : Noun} (h : PjCtx bc ctx) (k : Ident) (v : FDatum FinMap)
    (s : FinMap Bell (FDatum FinMap) × Memo FinMap) :
    nock (C pjGate (C (C (C (identNoun k) v.toNoun) (pjAcc s)) bc)) pjGate = some (pjAcc (pjStep s (k, v))) := by
  have hp : nock (C by.put.battery (C (C (Bell.toNoun ⟨v.less, k.2⟩) v.toNoun)
      (C by.battery (C (Treap.toNoun FDatum.toNoun s.1) layer2)))) by.put.battery
      = some (Treap.toNoun FDatum.toNoun (Treap.put s.1 (⟨v.less, k.2⟩ : Bell) v)) :=
    put_gate layer2 gorIn_morIn_layer2 _ _ _ _
      (FinMap.putF_toNoun FDatum.toNoun s.1 (⟨v.less, k.2⟩ : Bell) v)
  have hm := mfe_gate ctx h.lib k v
  have hpm := mi_put_gate ctx h.miIn s.2 (memoFinalEntry k v).1 (memoFinalEntry k v).2
  simp only [Bell.toNoun, FDatum.toNoun] at hp
  simp only [identNoun, FDatum.toNoun] at hm hpm
  unfold pjGate pjHead pjTail pjAcc pjStep
  simp only [nock_exec, Option.bind_some, h.hctx, h.l2, h.mfe, h.mi, by.arm_at, by_arm, by.put.arm_at, put_arm,
    identNoun, FDatum.toNoun, hp, mi_arm, mi.put.arm_at, mi_put_arm, hm, hpm]

/-- The gate of the `+rep` as a function of the node noun, through the map. -/
noncomputable def pjF (pruned : Callgraph FinMap) (x : Noun)
    (s : FinMap Bell (FDatum FinMap) × Memo FinMap) : FinMap Bell (FDatum FinMap) × Memo FinMap :=
  match FinMap.entry pruned x with
  | some e => pjStep s e
  | none => s

theorem pj_foldl (pruned : Callgraph FinMap) :
    ∀ (L : List (Ident × FDatum FinMap)), (∀ e ∈ L, pruned.1 e.1 = some e.2) → ∀ s,
    (L.map fun e => C (TKey.enc e.1) (FDatum.toNoun e.2)).foldl (fun s x => pjF pruned x s) s
      = L.foldl pjStep s
  | [], _, _ => rfl
  | e :: L, h, s => by
    have he := h e List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    have : pjF pruned (C (TKey.enc e.1) (FDatum.toNoun e.2)) s = pjStep s e := by
      simp [pjF, FinMap.entry, FinMap.decode?_enc, he]
    rw [this]
    exact pj_foldl pruned L (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _

/-- **The `~(rep by pruned)`** with the gate `pjGate` from the accumulator
`[~ memo]` computes `pokeMemo`. -/
theorem pj_rep {bc ctx : Noun} (h : PjCtx bc ctx) (e : Noun) (pruned : Callgraph FinMap) (memo : Memo FinMap) :
    nock (C by.rep.battery (C (C pjGate (C (C e (pjAcc (Treap.empty, memo))) bc))
      (C by.battery (C (Treap.toNoun FDatum.toNoun pruned) layer2)))) by.rep.battery
      = some (pjAcc (pokeMemo pruned memo)) := by
  show nock (C by.rep.battery (C (C pjGate (C (C e (pjAcc (Treap.empty, memo))) bc))
    (C by.battery (C (FinMap.toNoun FDatum.toNoun pruned) layer2)))) by.rep.battery = _
  rw [rep_gate_on pjAcc (pjF pruned) by.battery layer2 pjGate e bc _
    (Tree.of_isMap (FinMap.isMap_toNoun FDatum.toNoun pruned)) _ ?hf]
  · show some (pjAcc ((preorder (FinMap.toNoun FDatum.toNoun pruned)).foldl _ _)) = _
    rw [FinMap.preorder_toNoun, pj_foldl pruned _ (fun e he => (FinMap.mem_rap pruned e.1 e.2).1 he)]
    rfl
  · intro x hx s
    have hx' : x ∈ (FinMap.rap pruned).map fun e => C (TKey.enc e.1) (FDatum.toNoun e.2) := by
      have := FinMap.preorder_toNoun FDatum.toNoun pruned
      rw [← this]; exact hx
    obtain ⟨⟨k, v⟩, hm, rfl⟩ := List.mem_map.1 hx'
    have hkv := (FinMap.mem_rap pruned k v).1 hm
    have : pjF pruned (C (TKey.enc k) (FDatum.toNoun v)) s = pjStep s (k, v) := by
      simp [pjF, FinMap.entry, FinMap.decode?_enc, hkv]
    rw [this]
    exact pj_gate h k v s

/-! ## The bunts of the sample of the gate of the `+rep` -/

/-- `*identity`. -/
def pjIdB : Noun := C (A 7) (C (C (A 9) (C (A 186) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

/-- `*datum`. -/
def pjDatB : Noun := C (A 7) (C (C (A 9) (C (A 375) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

/-- `*(map bell datum)`. -/
def pjMapB : Noun :=
  let m1 := C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 382) (C (A 0) (A 1023)))))
  let m2 := C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 375) (C (A 0) (A 1023)))))
  let mk := C (A 8) (C (C (A 9) (C (A 12198) (C (A 0) (A 2097151))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C m1 m2)) (C (A 0) (A 2)))))))
  C (A 7) (C mk (C (A 9) (C (A 2) (C (A 0) (A 1)))))

/-- The sample `[[*identity *datum] *(map bell datum) memo.lon]`. -/
def pjSample : Noun := C (C pjIdB pjDatB) (C pjMapB (C (A 0) (A 8170)))

/-- A subject with `K` at `511`. -/
def sub511 (K a0 a1 a2 a3 a4 a5 a6 a7 : Noun) : Noun :=
  C a0 (C a1 (C a2 (C a3 (C a4 (C a5 (C a6 (C a7 K)))))))

/-- A subject with `ana` at `511`. -/
def ana511 (a0 a1 a2 a3 a4 a5 a6 a7 : Noun) : Noun := sub511 ana a0 a1 a2 a3 a4 a5 a6 a7

/-- The value of `*datum`, kept whole. -/
noncomputable def pjDatV : Noun := (evalFuel 2000 (ana511 (A 0) (A 0) (A 0) (A 0) (A 0) (A 0) (A 0) (A 0)) pjDatB).getD (A 0)

theorem pj_idb (a0 a1 a2 a3 a4 a5 a6 a7 : Noun) :
    nock (ana511 a0 a1 a2 a3 a4 a5 a6 a7) pjIdB = some identBunt :=
  nock_of_evalFuel (fuel := 300) (by kernel_rfl)

theorem pj_datb (a0 a1 a2 a3 a4 a5 a6 a7 : Noun) :
    nock (ana511 a0 a1 a2 a3 a4 a5 a6 a7) pjDatB = some pjDatV :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

theorem pj_mapb (a0 a1 a2 a3 a4 a5 a6 a7 : Noun) :
    nock (ana511 a0 a1 a2 a3 a4 a5 a6 a7) pjMapB = some (A 0) :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-! ## The trap `%poke-just-code` -/

/-- The door `~(rep by pruned)`. -/
def pjDoor : Noun :=
  C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 2097151))))
    (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))

/-- The battery of the trap `%poke-just-code`. -/
def pjTB : Noun :=
  let g := C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C pjSample (C (C (A 1) pjGate) (C (A 0) (A 1))))))
  C (A 8) (C pjDoor (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) g) (C (A 0) (A 2)))))))

theorem pjAcc_init (memo : Memo FinMap) : pjAcc (Treap.empty, memo) = C (A 0) (memoNoun memo) := by
  unfold pjAcc
  show C (FinMap.toNoun FDatum.toNoun (FinMap.empty : FinMap Bell (FDatum FinMap))) _ = _
  rw [FinMap.toNoun_empty]

/-- An autocons whose head is a cell formula given by name. -/
theorem nock_pair_of (s f g : Noun) (hf : ∃ x y, f = C x y) :
    nock s (C f g) = (nock s f).bind fun a => (nock s g).bind fun b => some (C a b) := by
  obtain ⟨x, y, rfl⟩ := hf
  exact nock_cell s x y g

theorem pjSample_run (s : Noun) :
    nock s pjSample = (((nock s pjIdB).bind fun a => (nock s pjDatB).bind fun b => some (C a b)).bind
      fun l => ((nock s pjMapB).bind fun m => (slot? 8170 s).bind fun c => some (C m c)).bind
        fun r => some (C l r)) := by
  unfold pjSample
  rw [nock_cell, nock_pair_of s pjIdB pjDatB ⟨_, _, rfl⟩, nock_pair_of s pjMapB _ ⟨_, _, rfl⟩]
  simp only [nock_exec]

set_option maxHeartbeats 1000000 in
/-- **The trap `%poke-just-code`**, kicked on its core, computes
`pokeMemo pruned memo`, given the layout of `K` (the analysis core) at axis
`511` of the core and the bunts of its gate's sample. -/
theorem pj_trap (K : Noun) (hl2 : slot? 8191 K = some layer2)
    (hmfe : slot? 340 K = some (C (A 8) (C (C (A 1) mfeBunt) (C (C (A 1) mfeBat) (C (A 0) (A 1))))))
    (hlib : slot? 7 K = some lib) (hmi : slot? 84 K = some mi.arm) (hmiIn : MiIn K)
    (hidb : ∀ a0 a1 a2 a3 a4 a5 a6 a7, nock (sub511 K a0 a1 a2 a3 a4 a5 a6 a7) pjIdB = some identBunt)
    (hdatb : ∀ a0 a1 a2 a3 a4 a5 a6 a7, nock (sub511 K a0 a1 a2 a3 a4 a5 a6 a7) pjDatB = some pjDatV)
    (hmapb : ∀ a0 a1 a2 a3 a4 a5 a6 a7, nock (sub511 K a0 a1 a2 a3 a4 a5 a6 a7) pjMapB = some (A 0))
    (pruned : Callgraph FinMap) (memo : Memo FinMap) (rdN cgN ridN a5 a6 ridN' jetsN lonRest hotN : Noun) :
    nock (sub511 K pjTB rdN (Treap.toNoun FDatum.toNoun pruned) cgN ridN a5 a6
        (C ridN' (C (C jetsN (C (memoNoun memo) lonRest)) hotN))) pjTB
      = some (pjAcc (pokeMemo pruned memo)) := by
  have h1 := hidb pjTB rdN (Treap.toNoun FDatum.toNoun pruned) cgN ridN a5 a6
    (C ridN' (C (C jetsN (C (memoNoun memo) lonRest)) hotN))
  have h2 := hdatb pjTB rdN (Treap.toNoun FDatum.toNoun pruned) cgN ridN a5 a6
    (C ridN' (C (C jetsN (C (memoNoun memo) lonRest)) hotN))
  have h3 := hmapb pjTB rdN (Treap.toNoun FDatum.toNoun pruned) cgN ridN a5 a6
    (C ridN' (C (C jetsN (C (memoNoun memo) lonRest)) hotN))
  have hP : PjCtx (sub511 K pjTB rdN (Treap.toNoun FDatum.toNoun pruned) cgN ridN a5 a6
      (C ridN' (C (C jetsN (C (memoNoun memo) lonRest)) hotN))) K :=
    ⟨by simp [sub511, nock_exec], by simp [sub511, nock_exec, hl2], hmfe, hlib, hmi, hmiIn⟩
  have hr := pj_rep hP (C identBunt pjDatV) pruned memo
  rw [pjAcc_init] at hr
  simp only [sub511] at h1 h2 h3 hr
  conv => lhs; arg 2; unfold pjTB
  unfold pjDoor
  simp only [sub511, nock_exec, Option.bind_some, hl2, by.arm_at, by_arm, by.rep.arm_at, rep_arm, pjSample_run,
    h1, h2, h3, hr]

/-! ## The gate `+ska-poke`: its battery and the trap it hands `road-pure` -/

/-- The bunt of the sample of `+ska-callgraph`, kept whole. -/
noncomputable def cgBunt : Noun := (slot? 53 ska_cg.arm).getD (A 0)

/-- The clue of the `%fast` hint of `+ska-callgraph`, kept whole. -/
noncomputable def cgClue : Noun := (slot? 123 ska_cg.arm).getD (A 0)

theorem ska_cg_arm_eq : ska_cg.arm = C (A 7) (C (C (A 8) (C (C (A 1) cgBunt) (C (C (A 1) ska_cg.battery)
    (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) cgClue)) (C (A 0) (A 1))))) := by kernel_rfl

theorem ska_cg_arm_run (K : Noun) : nock K ska_cg.arm = some (C ska_cg.battery (C cgBunt K)) := by
  rw [ska_cg_arm_eq]; simp only [nock_exec]

/-- The bunt of the sample of `+ska-poke`, kept whole. -/
noncomputable def spBunt : Noun := (slot? 165 ana).getD (A 0)

/-- The trap `|.` that `+ska-poke` hands `road-pure`: its battery, kept
whole (`spX_eq` splits it). -/
noncomputable def spX : Noun := (slot? 683997 ana).getD (A 0)

/-- The baking part of `+ska-poke`: the formula that runs after the
analysis, on `[dats [root-datum [pruned [[g regs] [root-identity T0']]]]]`. -/
noncomputable def spRest : Noun := (slot? 44826492927 ana).getD (A 0)

/-- The clue of the `%fast` hint of the trap `%poke-just-code`, kept whole. -/
noncomputable def spClue : Noun := (slot? 2868895546299 ana).getD (A 0)

/-- The battery of the gate `+ska-poke`: `(road-pure |.(...))`. -/
noncomputable def spBat : Noun :=
  C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3))
    (C (C (A 1) spX) (C (A 0) (A 1)))))) (C (A 0) (A 2)))))))

theorem sp_at : slot? 20 ana = some (C (A 8) (C (C (A 1) spBunt) (C (C (A 1) spBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The call of `+ska-callgraph`. -/
def spCG : Noun :=
  let regs := C (C (A 0) (A 2)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 30)) (C (A 1) (A 0)))))
  let sam := C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 2)) (C (C (A 0) (A 490)) (C (A 7) (C (C (A 0) (A 244)) regs)))))
  C (A 8) (C (C (A 9) (C (A 341) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) sam) (C (A 0) (A 2)))))))

/-- The call of `+prune-callgraph`. -/
def spPR : Noun :=
  C (A 8) (C (C (A 9) (C (A 22007) (C (A 0) (A 63))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))

/-- `(~(got by pruned) root-identity)`. -/
def spGOT : Noun :=
  let door := C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 524287))))
    (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))
  let sl := C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))
  C (A 8) (C door sl)

/-- The trap `%poke-just-code`, built and kicked. -/
noncomputable def spTC : Noun :=
  let h := C (A 11) (C (C (A 0x74736166) (C (A 1) spClue)) (C (A 0) (A 1)))
  let mk := C (A 8) (C (C (A 1) pjTB) h)
  C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C mk (C (A 9) (C (A 2) (C (A 0) (A 1)))))))

/-- `=^  dats  memo.lon`: the new memo into `lon`, then `dats` pushed. -/
noncomputable def spEnd : Noun :=
  let ed := C (A 10) (C (C (A 8170) (C (A 0) (A 5))) (C (A 0) (A 1)))
  let sw := C (C (A 0) (A 4)) (C (A 0) (A 3))
  C (A 7) (C ed (C (A 7) (C sw spRest)))

/-- The split of `spX`. -/
noncomputable def spXF : Noun :=
  let t := C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C spTC spEnd)))
  let t := C (A 8) (C spGOT t)
  let t := C (A 8) (C spPR t)
  let t := C (A 8) (C spCG t)
  C (A 8) (C (C (C (A 0) (A 56)) (C (A 0) (A 57))) t)

theorem spX_eq : spX = spXF := by kernel_rfl

/-- The subject of the trap: `[spX [spBat [[root-identity [lon hot]] K]]]`
with `lon = [jets [memo lonRest]]` and `jets = [r1 [r2 [r3 [r4 jRest]]]]`. -/
noncomputable def spT0 (K : Noun) (root : Ident) (r1 r2 r3 r4 jRest memoN lonRest hotN : Noun) : Noun :=
  C spX (C spBat (C (C (identNoun root) (C (C (C r1 (C r2 (C r3 (C r4 jRest)))) (C memoN lonRest)) hotN)) K))

theorem nock_cons_triv (s : Noun) (a b : Nat) :
    nock s (C (C (A 0) (A a)) (C (A 0) (A b))) =
      (slot? a s).bind fun x => (slot? b s).bind fun y => some (C x y) := by
  simp only [nock_exec]

set_option maxHeartbeats 2000000 in
/-- **The analysis part of the trap**, with the analysis core `K` a variable:
the calls of `+ska-callgraph`, `+prune-callgraph`, `+got:by` and the trap
`%poke-just-code`, then `spEnd`. -/
theorem sp_chain (K : Noun) (hcg : slot? 341 K = some ska_cg.arm) (hpr : slot? 22007 K = some prune_cg.arm)
    (hl2 : slot? 8191 K = some layer2) (root : Ident) (r1 r2 r3 r4 jRest memoN lonRest hotN : Noun) :
    nock (spT0 K root r1 r2 r3 r4 jRest memoN lonRest hotN) spX =
      (nock (C ska_cg.battery (C (C (identNoun root) (C memoN (C r1 (C r2 (C r3 (C r4 (A 0))))))) K))
        ska_cg.battery).bind fun cgr =>
      (slot? 2 cgr).bind fun gN =>
      (nock (C prune_cg.battery (C (C gN (identNoun root)) K)) prune_cg.battery).bind fun prN =>
      (nock (C by.got.battery (C (identNoun root) (C by.battery (C prN layer2)))) by.got.battery).bind fun rdN =>
      let T4 := C rdN (C prN (C cgr (C (identNoun root) (spT0 K root r1 r2 r3 r4 jRest memoN lonRest hotN))))
      (nock (C pjTB T4) pjTB).bind fun res => nock (C res T4) spEnd := by
  conv => lhs; arg 2; rw [spX_eq]
  unfold spXF
  have hr : C (Sock.toNoun root.1) root.2 = identNoun root := rfl
  unfold spCG spPR spGOT spTC
  simp only [spT0, nock_exec, Option.bind_some, hr, hcg, ska_cg_arm_run, hpr, prune_arm_run, hl2, by.arm_at,
    by_arm, by.got.arm_at, got_arm, Option.bind_assoc]

/-- `spEnd`: the new memo into `lon`, `dats` pushed, then the baking part. -/
theorem sp_end (K : Noun) (root : Ident) (r1 r2 r3 r4 jRest memoN lonRest hotN datsN memoN' rdN prN cgr : Noun) :
    nock (C (C datsN memoN') (C rdN (C prN (C cgr (C (identNoun root)
        (spT0 K root r1 r2 r3 r4 jRest memoN lonRest hotN)))))) spEnd
      = nock (C datsN (C rdN (C prN (C cgr (C (identNoun root)
        (spT0 K root r1 r2 r3 r4 jRest memoN' lonRest hotN)))))) spRest := by
  unfold spEnd spT0
  simp only [nock_exec, Option.bind_some]

/-- The subject on which the baking part `spRest` runs, from the graph `gr`
of `+ska-callgraph` and what `Ana.skaPoke` returns. -/
noncomputable def spAfter {R : Type} (regsNoun : R → Noun) (root : Ident) (r1 r2 r3 r4 jRest lonRest hotN : Noun)
    (gr : Callgraph FinMap × R)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × R) : Noun :=
  C (Treap.toNoun FDatum.toNoun r.2.1) (C r.2.2.2.1.toNoun (C (Treap.toNoun FDatum.toNoun r.1)
    (C (C (Treap.toNoun FDatum.toNoun gr.1) (regsNoun gr.2)) (C (identNoun root)
      (spT0 ana root r1 r2 r3 r4 jRest (memoNoun r.2.2.1) lonRest hotN)))))

theorem pj_trap_ana (pruned : Callgraph FinMap) (memo : Memo FinMap) (rdN cgN ridN a5 a6 ridN' jetsN lonRest hotN : Noun) :
    nock (sub511 ana pjTB rdN (Treap.toNoun FDatum.toNoun pruned) cgN ridN a5 a6
        (C ridN' (C (C jetsN (C (memoNoun memo) lonRest)) hotN))) pjTB
      = some (pjAcc (pokeMemo pruned memo)) :=
  pj_trap ana ana_l2 mfe_at ana_lib7 mi.arm_at miIn_ana pj_idb pj_datb pj_mapb pruned memo _ _ _ _ _ _ _ _ _

section
variable {R : Type} (regsNoun : R → Noun) (env : Env R)
  (hhe : env.he = heSock) (hth : env.threshold = 32) (hsoft : env.softSpot = softSpotF)
  (hreg : RegisterFastIs regsNoun env)
include hhe hth hsoft hreg

/-- **The analysis part of `+ska-poke`**: the trap that `+ska-poke` hands
`road-pure`, on the core of the gate `+ska-poke` with the sample
`[root-identity [lon hot]]` (`lon = [jets [memo lonRest]]`, the
registrations `[root core batt arms ~]:jets` being `regsNoun reg`), returns
`y` exactly when, at some fuel, `+ska-callgraph` returns a graph `gr`,
`Ana.skaPoke` returns `r`, and the baking part `spRest` returns `y` on the
subject `spAfter` built from them. -/
theorem ska_poke_ana_iff (root : Ident) (memo : Memo FinMap) (reg : R) (r1 r2 r3 r4 jRest lonRest hotN : Noun)
    (hregs : regsNoun reg = C r1 (C r2 (C r3 (C r4 (A 0))))) (y : Noun) :
    nock (spT0 ana root r1 r2 r3 r4 jRest (memoNoun memo) lonRest hotN) spX = some y ↔
      ∃ n gr r, Ana.skaCallgraph env n root memo reg = some gr ∧ Ana.skaPoke env n root memo reg = some r ∧
        nock (spAfter regsNoun root r1 r2 r3 r4 jRest lonRest hotN gr r) spRest = some y := by
  rw [sp_chain ana ska_cg.arm_at prune_cg_at ana_l2, ← hregs]
  have hcg := ska_callgraph_iff regsNoun env hhe hth hsoft hreg root memo reg
  simp only [cgSam] at hcg
  constructor
  · intro h
    obtain ⟨cgr, hc, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨gr, m, hgr, rfl⟩ := (hcg cgr).1 hc
    rw [show slot? 2 (C (Treap.toNoun FDatum.toNoun gr.1) (regsNoun gr.2))
      = some (Treap.toNoun FDatum.toNoun gr.1) by simp only [nock_exec], Option.bind_some] at h
    obtain ⟨prN, hpr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨n2, p, hp, rfl⟩ := (prune_gate_iff ana ana_l2 gr.1 root prN).1 hpr
    obtain ⟨rdN, hrd, h⟩ := Option.bind_eq_some_iff.1 h
    cases e : Treap.get p root with
    | none => rw [pr_got_none p root e] at hrd; cases hrd
    | some d =>
      rw [pr_got p root d e] at hrd
      cases hrd
      have ht := pj_trap_ana p memo d.toNoun (C (Treap.toNoun FDatum.toNoun gr.1) (regsNoun gr.2))
        (identNoun root) spX spBat (identNoun root) (C r1 (C r2 (C r3 (C r4 jRest)))) lonRest hotN
      simp only [sub511] at ht
      unfold spT0 at h
      dsimp only at h
      rw [ht, Option.bind_some] at h
      unfold pjAcc at h
      rw [show (C spX (C spBat (C (C (identNoun root) (C (C (C r1 (C r2 (C r3 (C r4 jRest)))) (C (memoNoun memo)
          lonRest)) hotN)) ana))) = spT0 ana root r1 r2 r3 r4 jRest (memoNoun memo) lonRest hotN from rfl,
        sp_end] at h
      refine ⟨max m n2, gr, (p, (pokeMemo p memo).1, (pokeMemo p memo).2, d, gr.2),
        skaCallgraph_fuel_le env (Nat.le_max_left _ _) _ _ _ _ hgr, ?_, h⟩
      unfold Ana.skaPoke
      rw [skaCallgraph_fuel_le env (Nat.le_max_left _ _) _ _ _ _ hgr, Option.bind_some,
        pruneCallgraph_fuel_le (Nat.le_max_right _ _) _ _ _ hp, Option.bind_some, e]
      rfl
  · rintro ⟨n, gr, r, hgr, hr, hy⟩
    have hr' := hr
    unfold Ana.skaPoke at hr'
    rw [hgr, Option.bind_some] at hr'
    obtain ⟨p, hp, hr'⟩ := Option.bind_eq_some_iff.1 hr'
    obtain ⟨d, e, rfl⟩ := Option.map_eq_some_iff.1 hr'
    rw [(hcg _).2 ⟨gr, n, hgr, rfl⟩, Option.bind_some,
      show slot? 2 (C (Treap.toNoun FDatum.toNoun gr.1) (regsNoun gr.2))
        = some (Treap.toNoun FDatum.toNoun gr.1) by simp only [nock_exec], Option.bind_some,
      (prune_gate_iff ana ana_l2 gr.1 root _).2 ⟨n, p, hp, rfl⟩, Option.bind_some, pr_got p root d e,
      Option.bind_some]
    have ht := pj_trap_ana p memo d.toNoun (C (Treap.toNoun FDatum.toNoun gr.1) (regsNoun gr.2))
      (identNoun root) spX spBat (identNoun root) (C r1 (C r2 (C r3 (C r4 jRest)))) lonRest hotN
    simp only [sub511] at ht
    unfold spT0
    dsimp only
    rw [ht, Option.bind_some]
    unfold pjAcc
    rw [show (C spX (C spBat (C (C (identNoun root) (C (C (C r1 (C r2 (C r3 (C r4 jRest)))) (C (memoNoun memo)
        lonRest)) hotN)) ana))) = spT0 ana root r1 r2 r3 r4 jRest (memoNoun memo) lonRest hotN from rfl,
      sp_end]
    exact hy

end

/-- The battery of the gate `+ska-poke` slams `road-pure` (the gate at axis
`62` of the analysis core `K`) with the trap `[spX [spBat [sam K]]]`, whose
run `ska_poke_ana_iff` describes. -/
theorem sp_bat_run (K sam : Noun) :
    nock (C spBat (C sam K)) spBat =
      (slot? 62 K).bind fun rp => (edit? 6 (C spX (C spBat (C sam K))) rp).bind fun core =>
        (slot? 2 core).bind fun f => nock core f := by
  conv => lhs; arg 2; unfold spBat
  simp only [nock_exec, Option.bind_some]

end Compiler
end Formalization
