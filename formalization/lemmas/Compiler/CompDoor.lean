import lemmas.Compiler.CompGen
import lemmas.Ska.CompLazyRun
import lemmas.Compiler.TreapMap
import lemmas.Hoon.Layer2
import lemmas.Hoon.GasBy
import lemmas.Pill.Facts
import lemmas.KernelRfl

/-!
# The state arms of the door of `+comp`

The gate `+comp` builds the door `|_  gen=line-short` with the formula
`[8 [1 bunt] [1 comp.door] 0 1]`, so an arm of the door runs on

    [comp.door [gen ctx]]

with `gen` at axis `6` and `ctx`, the core of the gate `+comp` (its battery,
its sample `[scc long-ska jets-hot map-local top b]`, the library), at axis
`7`.  A gate arm of the door builds `[battery [bunt door]]`, so its battery
runs on `[battery [sample [comp.door [gen ctx]]]]`, with `gen` at `30` and
`ctx` at `31`.

The arms linked here read of `ctx` only layer 2 of the library (`+by`,
`+weld`), at axis `262143` of `ctx` (`CompIn`), and layer 1 behind it.
The maps of the state are the treaps of the pill (`TreapMap mugF`).

`+dropping` (`[5 [1 %drop] 0 110]`, arm `1398` of the door) is shared with
another core of the pill, so the generator does not name it: `dropArm` is
written here and tied to the pill by `comp_drop_at`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel SkaModel.Comp Hoon

/-- What the arms of the door read of the context `ctx` of the door: layer 2
of the library at axis `262143`. -/
abbrev CompIn (ctx : Noun) : Prop := slot? 262143 ctx = some layer2

/-- `+dropping`: `?=(%drop mode.gen)`. -/
def dropArm : Noun := C (A 5) (C (C (A 1) (A 0x706f7264)) (C (A 0) (A 110)))

/-- `+dropping` is arm `1398` of the door (`886` of its battery). -/
theorem comp_drop_at : slot? 886 comp.door = some dropArm := by kernel_rfl

theorem comp_drop_at' (y : Noun) : slot? 1398 (C comp.door y) = some dropArm := by kernel_rfl

/-- The simprocs unfold `comp.door` down to `+dropping` and leave its axis
`[0 110]` as the generated noun that holds it (named by its content). -/
theorem comp_h110 : comp.h50f637450e98 = C (A 0) (A 110) := by kernel_rfl

/-- The battery positions of the arms, as `slot?` on `comp.door` (the form
the simprocs leave). -/
theorem comp_oo_at : slot? 3412 comp.door = some comp.oo.arm := by kernel_rfl
theorem comp_re_at : slot? 3538943 comp.door = some comp.re.arm := by kernel_rfl
theorem comp_id_at : slot? 27631 comp.door = some comp.id.arm := by kernel_rfl
theorem comp_emir_at : slot? 222 comp.door = some comp.emir.arm := by kernel_rfl

theorem cd_listNoun_listN {α : Type} (f : α → Noun) :
    ∀ l : List α, listNoun f l = listN (l.map f)
  | [] => rfl
  | y :: l => by simp [listNoun, listN, cd_listNoun_listN f l]

/-- `+weld` of two lists of nouns of `f`. -/
theorem cd_weld {α : Type} (f : α → Noun) (l l' : List α) :
    nock (C weld.battery (C (C (listNoun f l) (listNoun f l')) layer2)) weld.battery
      = some (listNoun f (l ++ l')) := by
  rw [cd_listNoun_listN, cd_listNoun_listN, cd_listNoun_listN, weld_gate_list, List.map_append]

/-- The core of the door on the noun of a state. -/
abbrev compCore (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  C comp.door (C (genNoun g x) ctx)

variable (ctx : Noun) (x : GenRest)

/-! ## `+re`, `+oo`, `+id`, `+dropping` -/

/-- `+re`: `[re-gen.gen gen(re-gen +(re-gen.gen))]`. -/
theorem comp_re (g : Gen (TreapMap mugF)) :
    nock (compCore g x ctx) comp.re.arm = (re g).map fun p => C (A p.1) (genNoun p.2 x) := by
  nock_open comp.re.arm
  simp [nock_exec, genNoun, re]

/-- `+oo`: a fresh block label. -/
theorem comp_oo (g : Gen (TreapMap mugF)) :
    nock (compCore g x ctx) comp.oo.arm = (oo g).map fun p => C (A p.1) (genNoun p.2 x) := by
  nock_open comp.oo.arm
  simp [nock_exec, genNoun, oo]

/-- `+id`: a fresh region identifier. -/
theorem comp_id (g : Gen (TreapMap mugF)) :
    nock (compCore g x ctx) comp.id.arm = (freshId g).map fun p => C (A p.1) (genNoun p.2 x) := by
  nock_open comp.id.arm
  simp [nock_exec, genNoun, freshId]

/-- `+dropping`: the flag of `drop`. -/
theorem comp_dropping (g : Gen (TreapMap mugF)) :
    nock (compCore g x ctx) dropArm = some (loob g.drop) := by
  unfold dropArm
  cases h : g.drop <;> simp [nock_exec, cgModeNoun, h, loob, eqCode_atom]

/-! ## `+emir`, `+set-tag`, `+add-ops` -/

variable {ctx} in
/-- `+emir`: `?:  dropping  gen`, else `+put:by` of `[o blob]` into `blocks`. -/
theorem comp_emir (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (o : Nat) (b : Blob) :
    nock (C comp.emir.battery (C (C (A o) b.toNoun) (compCore g x ctx))) comp.emir.battery
      = (emir o b g).map fun p => genNoun p.2 x := by
  have hput := put_gate layer2 gorIn_morIn_layer2 (A o) b.toNoun _ _
    (putF_hoonMap Blob.toNoun g.blocks o b)
  nock_open comp.emir.battery
  cases h : g.drop <;>
    simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
      by.put.arm_at, put_arm, hput, emir]

variable {ctx} in
/-- `+set-tag`: `?:  dropping  gen`, else `+put:by` of `[o region]` into `tags`. -/
theorem comp_set_tag (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (o : Nat) (region : List Nat) :
    nock (C comp.set_tag.battery (C (C (A o) (listNoun A region)) (compCore g x ctx)))
      comp.set_tag.battery = (setTag o region g).map fun p => genNoun p.2 x := by
  have hput := put_gate layer2 gorIn_morIn_layer2 (A o) (listNoun A region) _ _
    (putF_hoonMap (listNoun A) g.tags o region)
  nock_open comp.set_tag.battery
  cases h : g.drop <;>
    simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
      by.put.arm_at, put_arm, hput, setTag]

variable {ctx} in
/-- `+add-ops`: `?:  dropping  gen`, else `got` of block `o`, the ops welded in
front of its body, and the block put back; `got` crashes on a missing block,
where the model is `none`. -/
theorem comp_add_ops (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (o : Nat) (ops : List Pole) :
    nock (C comp.add_ops.battery (C (C (A o) (listNoun Pole.toNoun ops)) (compCore g x ctx)))
      comp.add_ops.battery = (addOps o ops g).map fun p => genNoun p.2 x := by
  have hget := getF_hoonMap Blob.toNoun g.blocks o
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  nock_open comp.add_ops.battery
  cases h : g.drop
  · cases e : HoonMap.get g.blocks o with
    | none =>
      rw [e] at hget
      have hgot := got_gate_nil layer2 hgc (A o) _ hget
      simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
        by.got.arm_at, got_arm, hgot, addOps, e]
    | some b =>
      rw [e] at hget
      have hgot := got_gate layer2 hgc (A o) _ _ hget
      have hput := put_gate layer2 gorIn_morIn_layer2 (A o)
        (Blob.toNoun { b with body := ops ++ b.body }) _ _
        (putF_hoonMap Blob.toNoun g.blocks o { b with body := ops ++ b.body })
      have hweld := cd_weld Pole.toNoun ops b.body
      simp only [Blob.toNoun] at hput
      simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
        by.got.arm_at, got_arm, hgot, addOps, e, Blob.toNoun, weld_arm, weld.arm_at,
        hweld, by.put.arm_at, put_arm, hput]
  · simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, addOps]

/-! ## `+emit` and `+bomb` -/

/-- The arm `emir` builds its gate. -/
theorem comp_emir_arm (d : Noun) : nock d comp.emir.arm =
    some (C comp.emir.battery (C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) d)) := by
  nock_open comp.emir.arm; simp only [nock_exec]

/-- The arm `emit` builds its gate. -/
theorem comp_emit_arm (d : Noun) : nock d comp.emit.arm =
    some (C comp.emit.battery (C (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))) d)) := by
  nock_open comp.emit.arm; simp only [nock_exec]

/-- What the model's `emit` computes. -/
theorem cd_emit_eq (g : Gen (TreapMap mugF)) (b : Blob) :
    emit b g = some (g.bo, if g.drop then { g with bo := g.bo + 1 }
      else { g with bo := g.bo + 1, blocks := HoonMap.put g.blocks g.bo b }) := by
  cases h : g.drop <;>
    simp [emit, oo, emir, bind, StateT.bind, pure, StateT.pure, h]

variable {ctx} in
/-- `+emit`: `+oo`, then `+emir` under the fresh label. -/
theorem comp_emit (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (b : Blob) :
    nock (C comp.emit.battery (C b.toNoun (compCore g x ctx))) comp.emit.battery
      = (emit b g).map fun p => C (A p.1) (genNoun p.2 x) := by
  nock_open comp.emit.battery
  rw [cd_emit_eq]
  cases h : g.drop <;> simp [nock_exec, comp_oo ctx x, oo, comp_emir_arm, comp_emir x hc, emir, h]

variable {ctx} in
/-- `+bomb`: a block that crashes, under a fresh label, and the next with the
bunt of `need-lazy`. -/
theorem comp_bomb {S : Type} [HoonSet S] (hc : CompIn ctx) (g : Gen (TreapMap mugF))
    (miss : Option Nat) :
    nock (C comp.bomb.battery (C (unitNoun A miss) (compCore g x ctx))) comp.bomb.battery
      = (bomb (S := S) miss g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have he := comp_emit x hc g ⟨[], [], Termin.bom miss⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.bom] at he
  nock_open comp.bomb.battery
  rw [cd_emit_eq] at he
  simp [nock_exec, comp_emit_arm, he, bomb, cd_emit_eq, Functor.map, StateT.map, Next.goal,
    CGoal.toNoun, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Jmp.toNoun,
    jmp0, listNoun, Tag.none]

/-! ## `+must` and `+split-need` -/

theorem cd_need_cell : ∀ n : Need, ∃ a b, n.toNoun = C a b
  | Need.pair _ _ => ⟨_, _, rfl⟩
  | Need.both _ _ _ => ⟨_, _, rfl⟩
  | Need.this _ => ⟨_, _, rfl⟩
  | Need.none => ⟨_, _, rfl⟩

/-- The arm `re` on the door, in the form the simprocs leave. -/
theorem comp_re' (g : Gen (TreapMap mugF)) :
    nock (C comp.door (C (genNoun g x) ctx)) comp.re.arm
      = some (C (A g.re) (genNoun { g with re := g.re + 1 } x)) := by
  rw [comp_re]; rfl

/-- `+must`: the register of a need that has one, or a fresh one. -/
theorem comp_must (g : Gen (TreapMap mugF)) (ned : Need) :
    nock (C comp.must.battery (C ned.toNoun (compCore g x ctx))) comp.must.battery
      = (must ned g).map fun p => C (C (A p.1.1) p.1.2.toNoun) (genNoun p.2 x) := by
  nock_open comp.must.battery
  cases ned with
  | pair p q =>
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    simp [nock_exec, Need.toNoun, hp, eqCode, comp_re' ctx x, must, bind, StateT.bind, re, pure,
      StateT.pure, Tag.both]
  | both r h t => simp [nock_exec, Need.toNoun, eqCode, must, pure, StateT.pure, Tag.both]
  | this r => simp [nock_exec, Need.toNoun, eqCode, must, pure, StateT.pure, Tag.this]
  | none =>
    simp [nock_exec, Need.toNoun, eqCode, comp_re' ctx x, must, bind, StateT.bind, re, pure,
      StateT.pure, Tag.this, Tag.none]

theorem cd_must_some (ned : Need) (g : Gen (TreapMap mugF)) : ∃ p, must ned g = some p := by
  cases ned <;> simp [must, bind, StateT.bind, re, pure, StateT.pure]

/-- The arm `must` builds its gate. -/
theorem comp_must_arm (d : Noun) : nock d comp.must.arm =
    some (C comp.must.battery (C (C (A 0x656e6f6e) (A 0)) d)) := by
  nock_open comp.must.arm; simp only [nock_exec]

/-- The arm `add-ops` builds its gate. -/
theorem comp_add_ops_arm (d : Noun) : nock d comp.add_ops.arm =
    some (C comp.add_ops.battery (C (C (A 0) (A 0)) d)) := by
  nock_open comp.add_ops.arm; simp only [nock_exec]

/-- `+add-ops` of one `%con`, in the form the simprocs leave. -/
theorem comp_add_con (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (o h t r : Nat) :
    nock (C comp.add_ops.battery (C (C (A o) (C (C (A 0x6e6f63) (C (A h) (C (A t) (A r)))) (A 0)))
      (C comp.door (C (genNoun g x) ctx)))) comp.add_ops.battery
      = (addOps o [Pole.con h t r] g).map fun p => genNoun p.2 x :=
  comp_add_ops x hc g o [Pole.con h t r]

/-- `+must` in the form the simprocs leave. -/
theorem comp_must' (g : Gen (TreapMap mugF)) (ned : Need) :
    nock (C comp.must.battery (C ned.toNoun (C comp.door (C (genNoun g x) ctx)))) comp.must.battery
      = (must ned g).map fun p => C (C (A p.1.1) p.1.2.toNoun) (genNoun p.2 x) :=
  comp_must ctx x g ned

variable {ctx} in
/-- `+split-need`: the needs of the head and the tail, with a `%con` added in
front of block `o` where the need has a register. -/
theorem comp_split_need (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (ned : Need) (o : Nat) :
    nock (C comp.split_need.battery (C (C ned.toNoun (A o)) (compCore g x ctx)))
      comp.split_need.battery
      = (splitNeed ned o g).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x) := by
  nock_open comp.split_need.battery
  cases ned with
  | pair p q =>
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    simp [nock_exec, Need.toNoun, hp, splitNeed, pure, StateT.pure]
  | none => simp [nock_exec, Need.toNoun, eqCode, splitNeed, pure, StateT.pure, Tag.none]
  | this r =>
    simp [nock_exec, Need.toNoun, eqCode, Tag.this, comp_re' ctx x, comp_add_ops_arm,
      comp_add_con ctx x hc, splitNeed, bind, StateT.bind, re, pure, StateT.pure]
    cases addOps (Map := TreapMap mugF) o [Pole.con g.re (g.re + 1) r]
      { g with re := g.re + 1 + 1 } <;> simp [nock_exec, Need.toNoun, Tag.this]
  | both r h t =>
    obtain ⟨⟨⟨r1, n1⟩, g1⟩, e1⟩ := cd_must_some h g
    obtain ⟨⟨⟨r2, n2⟩, g2⟩, e2⟩ := cd_must_some t g1
    simp [nock_exec, Need.toNoun, eqCode, Tag.both, comp_must_arm, comp_must' ctx x, e1, e2,
      comp_add_ops_arm, comp_add_con ctx x hc, splitNeed, bind, StateT.bind, pure, StateT.pure]
    cases addOps (Map := TreapMap mugF) o [Pole.con r1 r2 r] g2 <;> simp [nock_exec]

/-! ## `+copy-tag` -/

/-- `+gas:by` of the pairs `[o v]` for the labels of a list. -/
theorem cd_gas {ν : Type} (f : ν → Noun) (v : ν) :
    ∀ (tos : List Nat) (m : TreapMap mugF ν),
      gasF mugF (HoonMap.toNoun f m) (tos.map fun o => (A o, f v))
        = some (HoonMap.toNoun f (tos.foldl (fun m o => HoonMap.put m o v) m))
  | [], _ => rfl
  | o :: tos, m => by
    simp only [List.map_cons, gasF, putF_hoonMap, List.foldl_cons]
    exact cd_gas f v tos _

variable {ctx} in
/-- `+copy-tag`: `?:  dropping  gen`, else the region of block `from` (by
`got`, a crash where the model is `none`) put under each label of `to` by
`+gas:by` of a `+turn`. -/
theorem comp_copy_tag (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (frm : Nat) (tos : List Nat) :
    nock (C comp.copy_tag.battery (C (C (A frm) (listNoun A tos)) (compCore g x ctx)))
      comp.copy_tag.battery = (copyTag frm tos g).map fun p => genNoun p.2 x := by
  have hget := getF_hoonMap (listNoun A) g.tags frm
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  nock_open comp.copy_tag.battery
  cases h : g.drop
  · cases e : HoonMap.get g.tags frm with
    | none =>
      rw [e] at hget
      have hgot := got_gate_nil layer2 hgc (A frm) _ hget
      simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
        by.got.arm_at, got_arm, hgot, copyTag, e]
    | some region =>
      rw [e] at hget
      have hgot := got_gate layer2 hgc (A frm) _ _ hget
      have hturn := fun r rest => turn_gate layer2 homo.arm_at
        (C (C (A 0) (A 6)) (C (A 0) (A 14))) (A 0) (C r rest) (fun y => C y r) (tos.map A)
        (fun y _ => by simp [nock_exec])
      have hgas := gas_gate layer2 gorIn_morIn_layer2 (tos.map fun o => (A o, listNoun A region))
        _ _ (cd_gas (listNoun A) region tos g.tags)
      simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
        by.got.arm_at, got_arm, hgot, copyTag, e, turn_arm, turn.arm_at, hturn, gas_arm,
        by.gas.arm_at, Function.comp_def, pairNoun, cd_listNoun_listN] at hgas ⊢
      simp [hgas]
  · simp [nock_exec, genNoun, cgModeNoun, h, comp_h110, eqCode_atom, copyTag]

end Compiler
end Formalization
