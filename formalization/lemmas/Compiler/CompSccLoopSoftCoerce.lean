import lemmas.Compiler.CompSccLoopSoft
import lemmas.Compiler.CompCoerceLazyGen
import lemmas.Compiler.CompSect
import lemmas.Ska.SccLoopSoftFin

/-! # `+coerce-lazy` with `+soft-ask` in the pill (README Gaps 21.17)

Track A's link of `+coerce-lazy` (`comp_coerce_lazy_all`, `CompCoerceLazyGen.lean`) asks that no
visited block is a key of `soft.gen`.  Here the state threads the soft map: the rest of the noun
of the state is `czSx x sf` (`x` with the noun of the soft map `sf`), and at a `%this` of the
input need in a soft block the trap `sure-loop` calls **`+soft-ask`** (line 5227, battery axis
109246 of the door, `saskArm`, cut by `tools/gen/softask.py`): `?: dropping gen`, else the
`+jab:by` of `soft.gen` that puts `[src ned]` in front of `req` (`sask_gate`, `jab_mapF`).

* `czS_loop`: the trap is `sureLoopS`;
* `czS_x`: the root part is `coerceLazyS`;
* `czS_all`, `czS_bonds`, `czS_forks`: the gate is `coerceLazyLS` on every lazy need;
* **`comp_coerce_lazy_allS`**: from a rest whose `soft` is the noun of `sf`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The rest `x` with the noun of the soft map `sf`. -/
def czSx (x : GenRest) (sf : TreapMap mugF SoftCall) : GenRest := { x with soft := softMapNoun sf }

/-! ## `+soft-ask` -/

def saskBunt : Noun :=
  (C (A 1) (C (A 0) (C (A 0) (C (A 0x656e6f6e) (A 0)))))

def saskGB : Noun :=
  (C (A 10) (C (C (A 4095) (C (C (C (A 0) (A 122)) (C (A 0) (A 123))) (C (A 0) (A 0x37ff)))) (C (A 0) (A 6))))

def saskBody : Noun :=
  (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 7)))) (C (C (A 0) (A 30)) (C (A 10) (C (C (A 1022) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7dfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0x6e61656d) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (C (A 1) saskGB) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 30)))))))


/-- `+soft-ask`: the gate `[8 [1 bunt] [1 saskBody] [0 1]]`. -/
def saskArm : Noun := C (A 8) (C saskBunt (C (C (A 1) saskBody) (C (A 0) (A 1))))

/-- `+soft-ask` in the pill (battery axis 109246 of the door, core axis `0x2aabe`). -/
theorem sask_at : slot? 109246 comp.door = some saskArm := by kernel_rfl

/-- The arm `jab` of the door on a map that holds a key (any value noun `f`). -/
theorem jab_arm_mapF {ν : Type} (f : ν → Noun) (B c : Noun) (bs : TreapMap mugF ν) (o : Nat) (b : ν)
    (h : HoonMap.get bs o = some b) :
    ∃ S, nock (C B (C (HoonMap.toNoun f bs) c)) by.jab.arm
      = some (C by.jab.battery (C S (C B (C (HoonMap.toNoun f bs) c)))) := by
  rw [hoonMap_get] at h
  rw [hoonMap_toNoun]
  obtain ⟨t, ht⟩ := bs
  cases t with
  | nil => simp [TreapMap.get, Tr.get] at h
  | node k v l r =>
    simp only [TreapMap.toNoun, Tr.toNoun]
    exact ⟨C (A k) (C (C (A 0) (A 15)) (C (f v) (C (f v) (f v)))), by
      nock_open by.jab.arm; simp [nock_exec]⟩

/-- **`+jab:by` on a map** (any value noun `f`): at a value `b` that the gate maps to `b'`, the
noun of the map with `b'` put at the key. -/
theorem jab_mapF {ν : Type} (f : ν → Noun) (fp fs fc : Noun) (bs : TreapMap mugF ν) (o : Nat) (b b' : ν)
    (hb : HoonMap.get bs o = some b) (hg : nock (C fp (C (f b) fc)) fp = some (f b')) :
    nock (C by.jab.battery (C (C (A o) (C fp (C fs fc))) (C by.battery (C (HoonMap.toNoun f bs)
      layer2)))) by.jab.battery = some (HoonMap.toNoun f (HoonMap.put bs o b')) := by
  have hm := isMap_hoonMap f bs
  have hv : Get (HoonMap.toNoun f bs) (A o) (f b) := by
    rw [hoonMap_toNoun] at hm ⊢
    exact (Tr.Get_toNoun_iff f _ hm _ _).2 ⟨o, b, rfl, hb, rfl⟩
  obtain ⟨out, hj, hmo, hget⟩ := jabF_spec (A o) (fun _ => f b') hm hv
  obtain ⟨out', hp, hmp, hgp⟩ := putF_spec mugF (HoonMap.toNoun f bs) (A o) (f b') hm
  rw [jab_gate_at layer2 gorIn_morIn_layer2.1 by.battery (A o) fp fs fc (fun _ => f b') (f b) hg _ out
    (getF_some hm hv) hj]
  rw [putF_hoonMap] at hp
  cases hp
  congr 1
  exact isMap_ext hmo hmp (fun k w => by rw [hget, hgp])

/-- The gate of the `+jab`: `s(req [[src ned] req.s])`. -/
theorem sask_gb (c : SoftCall) (src : Nat) (ned : Need) (B G : Noun) (o : Nat) :
    nock (C saskGB (C (Compiler.SoftCall.toNoun c) (C B (C (C (A o) (C (A src) ned.toNoun)) G)))) saskGB
      = some (Compiler.SoftCall.toNoun { c with req := (src, ned) :: c.req }) := by
  unfold saskGB
  simp [nock_exec, Compiler.SoftCall.toNoun]

/-- **`+soft-ask`** at a key of the soft map: the model `softAsk`. -/
theorem sask_gate {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (st : GenSf (TreapMap mugF)) (o src : Nat)
    (ned : Need) (c : SoftCall) (hget : HoonMap.get st.soft o = some c) :
    nock (C saskBody (C (C (A o) (C (A src) ned.toNoun)) (compCore st.g (czSx x st.soft) ctx))) saskBody
      = (softAsk o src ned st).map fun p => genNoun p.2.g (czSx x p.2.soft) := by
  have hD := comp_drop_at
  unfold softAsk
  by_cases hd : st.g.drop = true
  · simp only [hd, if_true, Option.map_some]
    simp only [compCore]
    generalize comp.door = Dr at hD
    generalize czSx x st.soft = X
    unfold saskBody
    generalize saskGB = GB
    simp [nock_exec, genNoun, hd, cgModeNoun, hD, dropArm, comp_h110, eqCode_atom]
  · have hd' : st.g.drop = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, if_false, hget, Option.map_some]
    obtain ⟨S, hS⟩ := jab_arm_mapF Compiler.SoftCall.toNoun by.battery layer2 st.soft o c hget
    have hJ := fun (Dr fs : Noun) => jab_mapF Compiler.SoftCall.toNoun saskGB fs
      (C saskBody (C (C (A o) (C (A src) ned.toNoun)) (C Dr (C (genNoun st.g (czSx x st.soft)) ctx))))
      st.soft o c { c with req := (src, ned) :: c.req } hget (sask_gb c src ned saskBody _ o)
    have hm : cgModeNoun st.g.drop = A 0x6e7572 := by simp [cgModeNoun, hd']
    simp only [compCore, czSx, softMapNoun, genNoun, hm] at hJ ⊢
    generalize comp.door = Dr at hD hJ
    conv => { lhs; arg 2; unfold saskBody }
    simp [nock_exec, genNoun, hd', cgModeNoun, hD, dropArm, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
      by.jab.arm_at, hS, hJ]

/-! ## The trap `sure-loop` with the soft map -/

/-- The hypothesis of the recursion of `sure-loop` on a need, the soft map threaded. -/
def CzLoopAtS (ctx : Noun) (x : GenRest) (o : Nat) (REST : Noun) (n : Need) : Prop :=
  ∀ (tgt : Need) (st : GenSf (TreapMap mugF)),
    nock (czLS tgt.toNoun n.toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o n tgt st).map fun r => genNoun r.2.g (czSx x r.2.soft)

/-- A step on the `Gen` part only. -/
theorem czS_lift (x : GenRest) (m : CM (TreapMap mugF) Unit) (st : GenSf (TreapMap mugF)) :
    (liftS m st).map (fun p => genNoun p.2.g (czSx x p.2.soft)) = (m st.g).map fun p => genNoun p.2 (czSx x st.soft) := by
  unfold liftS; cases m st.g <;> rfl

theorem czS_loop_none {ctx : Noun} (x : GenRest) (o : Nat) (REST : Noun) (tgt : Need) (st : GenSf (TreapMap mugF)) :
    nock (czLS tgt.toNoun Need.none.toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o Need.none tgt st).map fun r => genNoun r.2.g (czSx x r.2.soft) := by
  rw [cz_loop_none (czSx x st.soft) o REST tgt st.g]
  by_cases e : tgt = Need.none
  · subst e; simp [sureLoop, sureLoopS, pure, StateT.pure]
  · simp only [sureLoop, sureLoopS, e, if_false]
    rw [czS_lift]

theorem czS_loop_this {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (REST : Noun) (r : Nat) (tgt : Need)
    (st : GenSf (TreapMap mugF)) :
    nock (czLS tgt.toNoun (Need.this r).toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o (Need.this r) tgt st).map fun p => genNoun p.2.g (czSx x p.2.soft) := by
  have hgF := getF_hoonMap Compiler.SoftCall.toNoun st.soft o
  cases hget : HoonMap.get st.soft o with
  | none =>
    rw [hget] at hgF
    have hs : (czSx x st.soft).SoftOut o := by
      unfold GenRest.SoftOut czSx softMapNoun; simpa [unitNoun] using hgF
    rw [cz_loop_this hc (czSx x st.soft) o hs REST r tgt st.g]
    simp only [sureLoopS, withSoft, GenSf.isSoft, hget, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [czS_lift]
    rfl
  | some c =>
    rw [hget] at hgF
    have hhas := has_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A o) (softMapNoun st.soft) _ hgF
    have hsk := sask_gate hc x st o r tgt c hget
    have hA := sask_at
    simp only [sureLoopS, withSoft, GenSf.isSoft, hget, Option.isSome_some, if_true]
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore] at hsk ⊢
    generalize czBody = BD
    generalize comp.door = Dr at hsk hA
    generalize (softAsk o r tgt st).map (fun p => genNoun p.2.g (czSx x p.2.soft)) = R at hsk
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas,
      czSx, genNoun, unitNoun, loob, hA, saskArm, saskBunt]
    simp only [czSx] at hsk
    exact hsk

theorem czS_loop_pair {ctx : Noun} (x : GenRest) (o : Nat) (REST : Noun) (p q : Need)
    (ihp : CzLoopAtS ctx x o REST p) (ihq : CzLoopAtS ctx x o REST q) (tgt : Need) (st : GenSf (TreapMap mugF)) :
    nock (czLS tgt.toNoun (Need.pair p q).toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o (Need.pair p q) tgt st).map fun r => genNoun r.2.g (czSx x r.2.soft) := by
  obtain ⟨a, b, hp⟩ := cd_need_cell p
  cases tgt with
  | none =>
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, hp, sureLoopS, pure, StateT.pure]
  | this r =>
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hp, sureLoopS, liftS, crashM]
  | both r h t =>
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, Tag.both, hp, sureLoopS, liftS, crashM]
  | pair tp tq =>
    obtain ⟨a', b', htp⟩ := cd_need_cell tp
    have h1 := ihp tp st
    simp only [czLS, compCore] at h1
    rw [hp, htp] at h1
    conv => { lhs; arg 2; unfold czLoop }
    simp only [sureLoopS, bind, StateT.bind]
    cases e1 : sureLoopS o p tp st with
    | none =>
      rw [e1] at h1
      simp only [czLS, compCore]
      generalize czBody = BD at h1 ⊢
      generalize comp.door = Dr at h1 ⊢
      simp [nock_exec, Need.toNoun, Tag.none, hp, htp, h1]
    | some r1 =>
      obtain ⟨u, st1⟩ := r1
      rw [e1] at h1
      have h2 := ihq tq st1
      simp only [czLS, compCore] at h2
      simp only [czLS, compCore, Option.map_some] at h1 ⊢
      generalize czBody = BD at h1 h2 ⊢
      generalize comp.door = Dr at h1 h2 ⊢
      simp [nock_exec, Need.toNoun, Tag.none, hp, htp, h1, h2]

theorem czS_loop_both_this {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (REST : Noun) (r : Nat)
    (h t : Need) (d : Nat) (st : GenSf (TreapMap mugF)) :
    nock (czLS (Need.this d).toNoun (Need.both r h t).toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o (Need.both r h t) (Need.this d) st).map fun p => genNoun p.2.g (czSx x p.2.soft) := by
  rw [cz_loop_both_this hc (czSx x st.soft) o REST r h t d st.g]
  by_cases e : r = d
  · simp only [sureLoop, sureLoopS, e, if_true]; rw [czS_lift]
  · simp only [sureLoop, sureLoopS, e, if_false]; rw [czS_lift]

theorem czS_loop_both_pair {ctx : Noun} (x : GenRest) (o : Nat) (REST : Noun) (r : Nat) (h t : Need)
    (ihh : CzLoopAtS ctx x o REST h) (iht : CzLoopAtS ctx x o REST t) (tp tq : Need) (st : GenSf (TreapMap mugF)) :
    nock (czLS (Need.pair tp tq).toNoun (Need.both r h t).toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o (Need.both r h t) (Need.pair tp tq) st).map fun p => genNoun p.2.g (czSx x p.2.soft) := by
  obtain ⟨a', b', htp⟩ := cd_need_cell tp
  have h1 := ihh tp st
  simp only [czLS, compCore] at h1
  rw [htp] at h1
  conv => { lhs; arg 2; unfold czLoop }
  simp only [sureLoopS, bind, StateT.bind]
  cases e1 : sureLoopS o h tp st with
  | none =>
    rw [e1] at h1
    simp only [czLS, compCore]
    generalize czBody = BD at h1 ⊢
    generalize comp.door = Dr at h1 ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, htp, h1]
  | some r1 =>
    obtain ⟨u, st1⟩ := r1
    rw [e1] at h1
    have h2 := iht tq st1
    simp only [czLS, compCore] at h2
    simp only [czLS, compCore, Option.map_some] at h1 ⊢
    generalize czBody = BD at h1 h2 ⊢
    generalize comp.door = Dr at h1 h2 ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, htp, h1, h2]

theorem czS_loop_both_both {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (REST : Noun) (r : Nat)
    (h t : Need) (ihh : CzLoopAtS ctx x o REST h) (iht : CzLoopAtS ctx x o REST t) (d : Nat) (th tt : Need)
    (st : GenSf (TreapMap mugF)) :
    nock (czLS (Need.both d th tt).toNoun (Need.both r h t).toNoun o REST (compCore st.g (czSx x st.soft) ctx)) czLoop
      = (sureLoopS o (Need.both r h t) (Need.both d th tt) st).map fun p => genNoun p.2.g (czSx x p.2.soft) := by
  have hD2 := comp_add_ops_at
  have hao := comp_add_ops (czSx x st.soft) hc st.g o [Pole.mov r d]
  simp only [listNoun, Pole.toNoun, Tag.mov] at hao
  by_cases e : r = d
  · subst e
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore, sureLoopS]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, liftS, crashM]
  · have e' : ¬ (d = r) := fun h => e h.symm
    conv => { lhs; arg 2; unfold czLoop }
    simp only [sureLoopS, e, if_false, bind, StateT.bind, liftS]
    cases e0 : addOps o [Pole.mov r d] st.g with
    | none =>
      rw [e0] at hao
      simp only [czLS, compCore] at hao ⊢
      generalize czBody = BD
      generalize comp.door = Dr at hD2 hao ⊢
      simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao]
    | some r0 =>
      obtain ⟨u0, g0⟩ := r0
      rw [e0] at hao
      have h1 := ihh th ⟨g0, st.soft⟩
      simp only [czLS, compCore] at h1
      cases e1 : sureLoopS o h th ⟨g0, st.soft⟩ with
      | none =>
        rw [e1] at h1
        simp only [czLS, compCore, Option.map_some] at hao ⊢
        generalize czBody = BD at h1 ⊢
        generalize comp.door = Dr at hD2 hao h1 ⊢
        simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao, h1, e1]
      | some r1 =>
        obtain ⟨u1, st1⟩ := r1
        rw [e1] at h1
        have h2 := iht tt st1
        simp only [czLS, compCore] at h2
        simp only [czLS, compCore, Option.map_some] at hao h1 ⊢
        generalize czBody = BD at h1 h2 ⊢
        generalize comp.door = Dr at hD2 hao h1 h2 ⊢
        simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao, h1, h2, e1]

/-- **The trap `sure-loop`** is `sureLoopS`, the soft map threaded. -/
theorem czS_loop {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (REST : Noun) :
    ∀ ned : Need, CzLoopAtS ctx x o REST ned
  | Need.none => fun tgt st => czS_loop_none x o REST tgt st
  | Need.this r => fun tgt st => czS_loop_this hc x o REST r tgt st
  | Need.pair p q => fun tgt st =>
      czS_loop_pair x o REST p q (czS_loop hc x o REST p) (czS_loop hc x o REST q) tgt st
  | Need.both r h t => by
    have ihh := czS_loop hc x o REST h
    have iht := czS_loop hc x o REST t
    intro tgt st
    cases tgt with
    | none =>
      conv => { lhs; arg 2; unfold czLoop }
      simp only [czLS, compCore]
      generalize czBody = BD
      generalize comp.door = Dr
      simp [nock_exec, Need.toNoun, Tag.none, Tag.both, sureLoopS, pure, StateT.pure]
    | this d => exact czS_loop_both_this hc x o REST r h t d st
    | pair tp tq => exact czS_loop_both_pair x o REST r h t ihh iht tp tq st
    | both d th tt => exact czS_loop_both_both hc x o REST r h t ihh iht d th tt st

/-! ## The root part and the recursion -/

variable {ctx : Noun}

/-- **The root part `czX`** on any lazy need, the soft map threaded: `coerceLazyS`. -/
theorem czS_x (h7 : slot? 7 ctx = some compK) (x : GenRest) (o : Nat)
    (ned : Need) (s : Sure CSet) (FB : Noun) (less : Cape) (st : GenSf (TreapMap mugF)) :
    nock (czOrig ned.toNoun o (C s.toNoun FB) less.toNoun comp.door (genNoun st.g (czSx x st.soft)) ctx) czX
      = (coerceLazyS ned o s less st).map fun p => genNoun p.2.g (czSx x p.2.soft) := by
  have hc := (comp_ctx_pill ctx h7).1
  have hsrl := cz_srlG hc h7 (czSx x st.soft) st.g o ned s FB less
  unfold coerceLazyS
  simp only [bind, StateT.bind, liftS]
  cases e : coerceLok s.lok less ned with
  | none =>
    rw [e] at hsrl
    unfold czX
    simp only [czOrig] at hsrl ⊢
    generalize czSrl = SR at hsrl ⊢
    generalize czLoop = LP
    simp [nock_exec, hsrl, e]
  | some lok =>
    rw [e] at hsrl
    simp only [Option.bind_some] at hsrl
    simp only [e, Option.map_some, Option.bind_some]
    cases e2 : sureRequireLook ⟨s.ned, lok⟩ st.g with
    | none =>
      rw [e2] at hsrl
      unfold czX
      simp only [czOrig] at hsrl ⊢
      generalize czSrl = SR at hsrl ⊢
      generalize czLoop = LP
      simp [nock_exec, hsrl, e2]
    | some r =>
      obtain ⟨tgt, g1⟩ := r
      rw [e2] at hsrl
      have hl := czS_loop hc x o (C (C s.toNoun FB) less.toNoun) ned tgt ⟨g1, st.soft⟩
      simp only [czLS, compCore] at hl
      unfold czX
      simp only [czOrig, compCore, Option.bind_some, Option.map_some, e2] at hsrl ⊢
      generalize czSrl = SR at hsrl ⊢
      cases e3 : sureLoopS o ned tgt ⟨g1, st.soft⟩ with
      | none =>
        rw [e3] at hl
        generalize czLoop = LP at hl ⊢
        simp [nock_exec, hsrl, hl]
      | some r3 =>
        obtain ⟨u3, st3⟩ := r3
        rw [e3] at hl
        simp only [Option.map_some] at hsrl hl ⊢
        generalize czLoop = LP at hl ⊢
        simp [nock_exec, hsrl, hl]

section
variable (h7 : slot? 7 ctx = some compK) (x : GenRest) (ned : Need) (less : Cape)
include h7

mutual
/-- **`+coerce-lazy` on every lazy need**, the soft map threaded: `coerceLazyLS`. -/
theorem czS_all : ∀ (laz : Lazy CSet) (o : Nat) (st : GenSf (TreapMap mugF)),
    nock (czOrig ned.toNoun o laz.toNoun less.toNoun comp.door (genNoun st.g (czSx x st.soft)) ctx) czBody
      = (coerceLazyLS ned less o laz st).map fun p => genNoun p.2.g (czSx x p.2.soft)
  | Lazy.mk s fk bd, o, st => by
    obtain ⟨hc, -, hm⟩ := comp_ctx_pill ctx h7
    rw [lazy_toNoun_mk, cz_step hc hm.1, czS_x h7 x o ned s _ less st]
    unfold czCont
    simp only [cz_fold_forks, cz_fold_bonds]
    cases e1 : coerceLazyS ned o s less st with
    | none => simp [coerceLazyLS, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, st1⟩ := p
      by_cases hfb : fk = [] ∧ bd = []
      · obtain ⟨rfl, rfl⟩ := hfb
        simp [coerceLazyLS, e1, bind, StateT.bind, pure, StateT.pure]
      · simp only [Option.map_some, Option.bind_some, hfb, if_false]
        rw [czS_bonds bd st1]
        cases e2 : coerceBondsS ned less bd st1 with
        | none => simp [coerceLazyLS, e1, e2, bind, StateT.bind, hfb]
        | some q =>
          obtain ⟨u2, st2⟩ := q
          simp only [Option.map_some, Option.bind_some]
          rw [czS_forks fk st2]
          simp [coerceLazyLS, e1, e2, bind, StateT.bind, hfb]

theorem czS_bonds : ∀ (bd : List (Nat × Lazy CSet)) (st : GenSf (TreapMap mugF)),
    bd.foldlM (fun acc e => nock (czOrig ned.toNoun e.1 e.2.toNoun less.toNoun comp.door acc ctx) czBody)
      (genNoun st.g (czSx x st.soft))
      = (coerceBondsS ned less bd st).map fun p => genNoun p.2.g (czSx x p.2.soft)
  | [], st => by simp [coerceBondsS, pure, StateT.pure]
  | (ob, l) :: rest, st => by
    simp only [List.foldlM_cons]
    rw [czS_all l ob st]
    cases e1 : coerceLazyLS ned less ob l st with
    | none => simp [coerceBondsS, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, st1⟩ := p
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
      rw [czS_bonds rest st1]
      simp [coerceBondsS, e1, bind, StateT.bind]

theorem czS_forks : ∀ (fk : List (Lazy.ForkE CSet)) (st : GenSf (TreapMap mugF)),
    fk.foldlM (fun acc e => (nock (czOrig ned.toNoun e.1.1 e.1.2.toNoun less.toNoun comp.door acc ctx) czBody).bind
      fun a1 => nock (czOrig ned.toNoun e.2.1 e.2.2.toNoun less.toNoun comp.door a1 ctx) czBody)
      (genNoun st.g (czSx x st.soft))
      = (coerceForksS ned less fk st).map fun p => genNoun p.2.g (czSx x p.2.soft)
  | [], st => by simp [coerceForksS, pure, StateT.pure]
  | ((oy, y), (on, n)) :: rest, st => by
    simp only [List.foldlM_cons]
    rw [czS_all y oy st]
    cases e1 : coerceLazyLS ned less oy y st with
    | none => simp [coerceForksS, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, st1⟩ := p
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
      rw [czS_all n on st1]
      cases e2 : coerceLazyLS ned less on n st1 with
      | none => simp [coerceForksS, e1, e2, bind, StateT.bind]
      | some q =>
        obtain ⟨u2, st2⟩ := q
        simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
        rw [czS_forks rest st2]
        simp [coerceForksS, e1, e2, bind, StateT.bind]
end

end

/-- **`+coerce-lazy` with `+soft-ask` on every lazy need**: from a rest whose `soft` is the
noun of `sf`, the gate on `[ned o laz less]` is `coerceLazyLS ned less o laz` from `⟨g, sf⟩`,
the rest getting the noun of the product's soft map. -/
theorem comp_coerce_lazy_allS {ctx : Noun} (h7 : slot? 7 ctx = some compK) (x : GenRest) (sf : TreapMap mugF SoftCall)
    (hx : x.soft = softMapNoun sf) (ned : Need) (o : Nat) (laz : Lazy CSet) (less : Cape) (g : Gen (TreapMap mugF)) :
    nock (C czBody (C (C ned.toNoun (C (A o) (C laz.toNoun less.toNoun))) (compCore g x ctx))) czBody
      = (coerceLazyLS ned less o laz ⟨g, sf⟩).map fun p => genNoun p.2.g { x with soft := softMapNoun p.2.soft } := by
  have e : czSx x sf = x := by
    unfold czSx; obtain ⟨c, s, f⟩ := x; simp only at hx; subst hx; rfl
  have h := czS_all h7 x ned less laz o ⟨g, sf⟩
  simp only [czOrig] at h
  rw [e] at h
  exact h

end Compiler
end Formalization
