import lemmas.Compiler.SkaCull
import lemmas.Compiler.MsgCa

/-!
# `+run` of the core of `+ska-callgraph`

The arm `95` of the core `K` (`SkaCore.lean`) against `Ana.runStep`, over an
evaluator `nockW c` with `c` equal to `nock` off `FFar`, with the trap
`fol-loop` as a parameter (`GoIsW`).

The battery `ska_run.battery` counts the run, reads the old datum with
`+git-g`, pushes `bus`, `fol` and `sub`, and runs `[8 runFolF runDatumF]`:
`runFolF` builds `gen` and the trap's subject and kicks the trap
(`ska_run_battery_eq`, by the kernel), and `runDatumF` makes the datum from
the trap's result and writes it into `g`.  The datum construction is its own
lemma (`run_datum`), so a change to it (for example `less-code` merged with
the old entry's) changes only that lemma.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-! ## The formulas -/

def rdLess : Noun :=
  (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 16383)))) (C (A 9) (C (A 341) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 0) (A 62)))) (C (A 0) (A 2))))))))

def rdDark : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 62))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 1)) (C (A 0) (A 124)))))

def rdIndi : Noun :=
  (C (A 10) (C (C (A 118) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 65535)))) (C (A 9) (C (A 171) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 246)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

def rdNew : Noun :=
  (C (C (A 0) (A 478)) (C (C (A 0) (A 56)) (C (C (A 0) (A 6)) (C (C (A 0) (A 118)) (C (C (A 0) (A 238)) (C (C (A 0) (A 114)) (C (A 0) (A 958))))))))

def rdPm : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfbffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8188))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 5495) (C (A 0) (A 32767)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 2)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 510)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 2)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 510)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))))) (C (A 0) (A 2)))))))))))

def rdProd : Noun :=
  (C (A 10) (C (C (A 892) (C (A 0) (A 4))) (C (A 0) (A 1))))

def rdMap : Noun :=
  (C (A 10) (C (C (A 893) (C (A 0) (A 5))) (C (A 0) (A 1))))

def rdMoved : Noun :=
  (C (A 10) (C (C (A 0xfbffe) (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x64696f76)) (C (A 0) (A 0x1ff7c)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fbffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 16380))) (C (A 0) (A 2)))))))) (C (A 0) (A 0xfbffe)))))) (C (A 0) (A 1))))

def rdIndi2 : Noun :=
  (C (A 10) (C (C (A 110) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (A 0) (A 253)))))) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (A 0) (A 253)))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 110)) (C (A 0) (A 16366)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 171) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 187) (C (A 0) (A 65535)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 238)) (C (A 0) (A 32750)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 30)))) (C (A 0) (A 2)))))))) (C (A 0) (A 110)))))) (C (A 0) (A 1))))

def rdSeek : Noun :=
  (C (A 10) (C (C (A 222) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (A 0) (A 30))))))) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (A 0) (A 30))))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 222)) (C (A 0) (A 32734)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 187) (C (A 0) (A 65535)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 478)) (C (A 0) (A 65502)))) (C (A 0) (A 2)))))))) (C (A 0) (A 222)))))) (C (A 0) (A 1))))

def rdChanged : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (C (A 0) (A 30)) (C (A 0) (A 62)))))))) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (C (A 0) (A 30)) (C (A 0) (A 62)))))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))

def rdTick : Noun :=
  (C (A 10) (C (C (A 0x3f7ffe) (C (A 4) (C (A 0) (A 0x3f7ffe)))) (C (A 0) (A 1))))

def rdTicks : Noun :=
  (C (A 10) (C (C (A 0x7efffe) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfefffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 32764)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 0x3f7ffe)) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 0) (A 0x3f7ffe)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfefffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 32764)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0) (A 0))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 3)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

def rdFin : Noun :=
  (C (C (C (A 0) (A 16254)) (C (C (A 0) (A 32510)) (C (A 0) (A 2)))) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 32764)) (C (A 0) (A 30)))) (C (A 0) (A 2))))))))) (C (A 0) (A 32511)))))

/-- The datum construction of `+run`, the formula after `fol-loop`. -/
def runDatumF : Noun :=
  C (A 8) (C rdLess (C (A 8) (C rdDark (C (A 7) (C rdIndi (C (A 8) (C rdNew (C (A 8) (C rdPm (C (A 7) (C rdProd (C (A 7) (C rdMap (C (A 7) (C rdMoved (C (A 7) (C rdIndi2 (C (A 7) (C rdSeek (C (A 8) (C rdChanged (C (A 7) (C rdTick (C (A 7) (C rdTicks (rdFin))))))))))))))))))))))))))

/-- The run of `fol-loop` in `+run`: its `gen` and the trap, kicked. -/
def runFolF : Noun :=
  (C (A 8) (C (C (C (A 1) (A 1)) (C (C (A 1) (A 1)) (C (C (A 1) (A 1)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 0) (A 506)) (C (C (A 1) (A 1)) (C (A 0) (A 507))))))))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) (A 1)) (C (A 7) (C (C (A 8) (C (C (A 1) fol_loop.battery) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x706f6f6c2d6c6f66) (C (C (A 0) (A 0x3ffffff)) (A 0))))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))

/-- The battery of `+run`, split at the trap and the datum construction. -/
theorem ska_run_battery_eq : ska_run.battery =
    (C (A 7) (C (C (A 10) (C (C (A 28670) (C (A 4) (C (A 0) (A 28670)))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 56)) (C (A 8) (C (C (A 0) (A 121)) (C (A 8) (C (C (C (A 0) (A 6)) (C (A 1) (A 1))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C runFolF runDatumF)))))))))))))) := by kernel_rfl

/-! ## The context -/

theorem K_lib {K : Noun} (h : slot? 31 K = some ana) : slot? 127 K = some lib := by
  have h' : slot? 31 K = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 2
  simp only [show 2 ^ 2 * (31 + 1) - 1 = 127 from rfl, show 2 ^ 2 * (1 + 1) - 1 = 7 from rfl] at this
  rw [this, show (7 : Nat) = knit_anno.lib.axis from rfl, knit_anno.lib.arm_at]

/-! ## The datum construction, piece by piece -/

section datum
variable (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
  (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (sb x : Noun) (id : Ident)
  (data : FDatum FinMap) (out : FolOut)

/-- The subject of `runDatumF` below its pushes: the result of `fol-loop`,
`sub`, `fol`, `bus`, the old datum and the gate of `+run`. -/
noncomputable def dBase (gen : GenS FinMap R) : Noun :=
  C (folOutNoun regsNoun (out, gen)) (C (Anno.toNoun ⟨id.1, A 1⟩) (C id.2 (C id.1.toNoun
    (C data.toNoun (C sb (C (C (identNoun id) x) K))))))

include hcf hK in
/-- `less-code`, `dark`, `indi` and the new datum. -/
theorem run_datum_new (gen : GenS FinMap R) (F : Noun) :
    nockW c (dBase regsNoun K sb x id data out gen)
      (C (A 8) (C rdLess (C (A 8) (C rdDark (C (A 7) (C rdIndi (C (A 8) (C rdNew F))))))))
    = nockW c (C (FDatum.toNoun ⟨gen.callees, out.nomm, Ca.app gen.want id.1,
          Ca.lack gen.indi (darkOf id.1), gen.seek, out.prod.sock, out.prod.src, gen.area⟩)
        (C (darkOf id.1).toNoun (C (Ca.app gen.want id.1).toNoun
          (dBase regsNoun K sb x id data out { gen with indi := Ca.lack gen.indi (darkOf id.1) })))) F := by
  have hlib := K_lib hK
  have hsv : Sock.void.toNoun = A 0x64696f76 := rfl
  have hsm : ∀ c n, (Sock.mk c n).toNoun = C c.toNoun n := fun _ _ => rfl
  obtain ⟨want, indi, seek, callees, area, low, back, st⟩ := gen
  obtain ⟨bus, fol⟩ := id
  cases bus with
  | void =>
    have hca := ca_app_pill want Sock.void
    have hla := ca_lack_pill indi (darkOf Sock.void)
    simp only [hsv, darkOf, Cape.toNoun] at hca hla
    simp (disch := ffar_disch) [hca, hla, dBase, rdLess, rdDark, rdIndi, rdNew, nock_exec, hcf, hlib, folOutNoun,
      FolOut.toNoun, GenS.toNoun, Anno.toNoun, FDatum.toNoun, darkOf, hsv, hsm, Cape.toNoun, ca.lib.arm_at, ca_lib_arm,
      ca.app.arm_at, ca_app_arm, ca_app_pill, ca.lack.arm_at, ca_lack_arm, ca_lack_pill]
  | mk cp dt =>
    have hca := ca_app_pill want (Sock.mk cp dt)
    have hla := ca_lack_pill indi (darkOf (Sock.mk cp dt))
    simp only [hsm, darkOf] at hca hla
    simp (disch := ffar_disch) [hca, hla, dBase, rdLess, rdDark, rdIndi, rdNew, nock_exec, hcf, hlib, folOutNoun,
      FolOut.toNoun, GenS.toNoun, Anno.toNoun, FDatum.toNoun, darkOf, hsv, hsm, Cape.toNoun, ca.lib.arm_at, ca_lib_arm,
      ca.app.arm_at, ca_app_arm, ca_app_pill, ca.lack.arm_at, ca_lack_arm, ca_lack_pill]

include hcf hK in
/-- `pm`: the merge of the products, `+msg-anno` when `id` is in `moved`,
else `+double-int`. -/
theorem run_datum_pm (gen : GenS FinMap R) (dn : FDatum FinMap) (dark less F : Noun) :
    nockW c (C dn.toNoun (C dark (C less (dBase regsNoun K sb x id data out gen)))) (C (A 8) (C rdPm F))
    = nockW c (C (mergeProd (Treap.has gen.st.moved id) ⟨dn.prod, dn.map⟩ ⟨data.prod, data.map⟩).toNoun
        (C dn.toNoun (C dark (C less (dBase regsNoun K sb x id data out gen))))) F := by
  have hl2 := K_layer2 hK
  have hlib := K_lib hK
  obtain ⟨want, indi, seek, callees, area, low, back, st⟩ := gen
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hhas : nock (C in.has.battery (C (identNoun id) (C in.battery (C (Treap.setNoun moved) layer2))))
      in.has.battery = some (loob (Treap.has moved id)) := has_in_setNoun moved id
  have hma := msg_anno_pill ⟨dn.prod, dn.map⟩ ⟨data.prod, data.map⟩
  have hdi := double_int_pill ⟨dn.prod, dn.map⟩ ⟨data.prod, data.map⟩
  simp only [Anno.toNoun] at hma hdi
  cases hm : Treap.has moved id
  · simp (disch := ffar_disch) [hm, hhas, hma, hdi, dBase, rdPm, nock_exec, hcf, hl2, hK, hlib, folOutNoun,
      FolOut.toNoun, GenS.toNoun, SkaState.toNoun, Anno.toNoun, FDatum.toNoun, mergeProd, in.arm_at, in_arm,
      in.has.arm_at, has_in_arm, msg_anno.arm_at, msg_anno_arm, double_int.arm_at, double_int_arm, loob]
  · simp (disch := ffar_disch) [hm, hhas, hma, hdi, dBase, rdPm, nock_exec, hcf, hl2, hK, hlib, folOutNoun,
      FolOut.toNoun, GenS.toNoun, SkaState.toNoun, Anno.toNoun, FDatum.toNoun, mergeProd, in.arm_at, in_arm,
      in.has.arm_at, has_in_arm, msg_anno.arm_at, msg_anno_arm, double_int.arm_at, double_int_arm, loob]

theorem void_noun_ne {s : Sock} (h : s ≠ Sock.void) : ¬ A 0x64696f76 = s.toNoun := by
  cases s with
  | void => exact absurd rfl h
  | mk c n => intro e; cases e

/-- Whether `+run` puts `id` into `moved`: `&(!?=(%void prod.data) !=(pm [prod map]:data))`. -/
def movedCond (old : Datum) (pm : Anno) : Prop := old.prod ≠ Sock.void ∧ pm ≠ ⟨old.prod, old.map⟩

instance (old : Datum) (pm : Anno) : Decidable (movedCond old pm) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `moved` after the run. -/
noncomputable def movedSet (old : Datum) (pm : Anno) (id : Ident) (m : FinMap Ident Unit) : FinMap Ident Unit :=
  if movedCond old pm then Treap.ins m id else m

include hcf hK in
/-- The product and its map into the new datum, and `moved`. -/
theorem run_datum_moved (gen : GenS FinMap R) (dn : FDatum FinMap) (pm : Anno) (dark less F : Noun) :
    nockW c (C pm.toNoun (C dn.toNoun (C dark (C less (dBase regsNoun K sb x id data out gen)))))
      (C (A 7) (C rdProd (C (A 7) (C rdMap (C (A 7) (C rdMoved F))))))
    = nockW c (C pm.toNoun (C (FDatum.toNoun { dn with prod := pm.sock, map := pm.src }) (C dark (C less
        (dBase regsNoun K sb x id data out
          { gen with st := { gen.st with moved := movedSet data.core pm id gen.st.moved } }))))) F := by
  have hl2 := K_layer2 hK
  obtain ⟨want, indi, seek, callees, area, low, back, st⟩ := gen
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hput : nock (C in.put.battery (C (identNoun id) (C in.battery (C (Treap.setNoun moved) layer2))))
      in.put.battery = some (Treap.setNoun (Treap.ins moved id)) := put_in_setNoun moved id
  have hsv : Sock.void.toNoun = A 0x64696f76 := rfl
  by_cases hv : data.prod = Sock.void
  · have hc : ¬ movedCond data.core pm := fun h => h.1 hv
    simp (disch := ffar_disch) [movedSet, hc, hv, hsv, dBase, rdProd, rdMap, rdMoved, nock_exec, hcf, hl2, folOutNoun,
      FolOut.toNoun, GenS.toNoun, SkaState.toNoun, Anno.toNoun, FDatum.toNoun]
  · have hv' := void_noun_ne hv
    by_cases hp : pm = ⟨data.prod, data.map⟩
    · have hc : ¬ movedCond data.core pm := fun h => h.2 hp
      subst hp
      simp (disch := ffar_disch) [movedSet, hc, hv', dBase, rdProd, rdMap, rdMoved, nock_exec, hcf, hl2, folOutNoun,
        FolOut.toNoun, GenS.toNoun, SkaState.toNoun, Anno.toNoun, FDatum.toNoun]
    · have hc : movedCond data.core pm := ⟨hv, hp⟩
      have hp' : ¬ (pm.sock.toNoun = data.prod.toNoun ∧ pm.src = data.map) := by
        rintro ⟨e1, e2⟩
        exact hp (by cases pm; simp only at e1 e2; rw [SkaModel.Ana.Sock.toNoun_inj _ _ e1, e2])
      simp (disch := ffar_disch) [movedSet, hc, hv', hp', hput, dBase, rdProd, rdMap, rdMoved, nock_exec, hcf, hl2,
        folOutNoun, FolOut.toNoun, GenS.toNoun, SkaState.toNoun, Anno.toNoun, FDatum.toNoun, in.arm_at, in_arm,
        in.put.arm_at, put_in_arm]

theorem sock_toNoun_iff (a b : Sock) : a.toNoun = b.toNoun ↔ a = b :=
  ⟨SkaModel.Ana.Sock.toNoun_inj a b, fun h => h ▸ rfl⟩

theorem cape_toNoun_iff (a b : Cape) : a.toNoun = b.toNoun ↔ a = b :=
  ⟨SkaModel.Ana.Cape.toNoun_inj a b, fun h => h ▸ rfl⟩

/-- `indi` of the new datum after the `=?` of `+run`. -/
def indiSet (dn : FDatum FinMap) (old : Datum) (dark : Cape) : Cape :=
  if (dn.less, dn.prod, dn.map) = (old.less, old.prod, old.map) ∧ dn.indi ≠ old.indi then
    Ca.lack (msgCa dn.indi old.indi) dark
  else dn.indi

/-- `seek` of the new datum after the `=?` of `+run`. -/
def seekSet (dn : FDatum FinMap) (old : Datum) : Cape :=
  if (dn.less, dn.prod, dn.map, dn.indi) = (old.less, old.prod, old.map, old.indi) ∧ dn.seek ≠ old.seek then
    msgCa dn.seek old.seek
  else dn.seek

include hcf hK in
/-- The `=?` on `indi`, through `+msg-ca` and `+lack:ca`. -/
theorem run_datum_indi (gen : GenS FinMap R) (dn : FDatum FinMap) (pm : Noun) (dark : Cape) (less F : Noun) :
    nockW c (C pm (C dn.toNoun (C dark.toNoun (C less (dBase regsNoun K sb x id data out gen)))))
      (C (A 7) (C rdIndi2 F))
    = nockW c (C pm (C (FDatum.toNoun { dn with indi := indiSet dn data.core dark }) (C dark.toNoun (C less
        (dBase regsNoun K sb x id data out gen))))) F := by
  have hlib := K_lib hK
  have hla := ca_lack_pill (msgCa dn.indi data.indi) dark
  have hmc := msg_ca_gate ana dn.indi data.indi
  by_cases h1 : dn.less = data.less ∧ dn.prod = data.prod ∧ dn.map = data.map
  · by_cases h2 : dn.indi = data.indi
    · simp (disch := ffar_disch) [indiSet, FDatum.core, h1, h2, dBase, rdIndi2, nock_exec, hcf, hlib, hK,
        sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun]
    · simp (disch := ffar_disch) [indiSet, FDatum.core, h1, h2, hla, hmc, dBase, rdIndi2, nock_exec, hcf, hlib,
        hK, sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun, ca.lib.arm_at, ca_lib_arm, ca.lack.arm_at,
        ca_lack_arm, msg_ca_arm_at, msg_ca_arm]
  · have h1' : ¬ (dn.less = data.less ∧ dn.prod = data.prod ∧ dn.map = data.map) := h1
    simp (disch := ffar_disch) [indiSet, FDatum.core, h1', dBase, rdIndi2, nock_exec, hcf, hlib, hK,
      sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun]

include hcf hK in
/-- The `=?` on `seek`, through `+msg-ca`. -/
theorem run_datum_seek (gen : GenS FinMap R) (dn : FDatum FinMap) (pm dark less F : Noun) :
    nockW c (C pm (C dn.toNoun (C dark (C less (dBase regsNoun K sb x id data out gen)))))
      (C (A 7) (C rdSeek F))
    = nockW c (C pm (C (FDatum.toNoun { dn with seek := seekSet dn data.core }) (C dark (C less
        (dBase regsNoun K sb x id data out gen))))) F := by
  have hmc := msg_ca_gate ana dn.seek data.seek
  by_cases h1 : dn.less = data.less ∧ dn.prod = data.prod ∧ dn.map = data.map ∧ dn.indi = data.indi
  · by_cases h2 : dn.seek = data.seek
    · simp (disch := ffar_disch) [seekSet, FDatum.core, h1, h2, dBase, rdSeek, nock_exec, hcf, hK,
        sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun]
    · simp (disch := ffar_disch) [seekSet, FDatum.core, h1, h2, hmc, dBase, rdSeek, nock_exec, hcf,
        hK, sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun, msg_ca_arm_at, msg_ca_arm]
  · have h1' : ¬ (dn.less = data.less ∧ dn.prod = data.prod ∧ dn.map = data.map ∧ dn.indi = data.indi) := h1
    simp (disch := ffar_disch) [seekSet, FDatum.core, h1', dBase, rdSeek, nock_exec, hcf, hK,
      sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun]

/-- Whether the entry changed for its callers: `less-code`, `prod`, `map`,
`indi` or `seek`. -/
def chgOf (dn : FDatum FinMap) (old : Datum) : Bool :=
  decide ((dn.less, dn.prod, dn.map, dn.indi, dn.seek) ≠ (old.less, old.prod, old.map, old.indi, old.seek))

/-- The state that `+run` returns, from the state of `fol-loop`'s `gen` with
`moved` set, and the new datum. -/
noncomputable def runSt (id : Ident) (st : SkaState FinMap R) (dn : FDatum FinMap) (chg : Bool) :
    SkaState FinMap R :=
  let tk := st.tick + 1
  { st with tick := tk,
            ticks := Treap.put st.ticks id (tk, if chg then tk else (Treap.gut st.ticks id (0, 0)).2),
            g := Treap.put st.g id dn }

/-- The noun of a result of `+run`: `[[low back changed] st]`. -/
noncomputable def runNoun (regsNoun : R → Noun) (r : (Nat × Bool × Bool) × SkaState FinMap R) : Noun :=
  C (C (A r.1.1) (C (flag r.1.2.1) (flag r.1.2.2))) (r.2.toNoun regsNoun)

include hcf hK in
/-- `changed`, the tick, `ticks` and the write of the datum into `g`. -/
theorem run_datum_end (gen : GenS FinMap R) (dn : FDatum FinMap) (pm dark less : Noun) :
    nockW c (C pm (C dn.toNoun (C dark (C less (dBase regsNoun K sb x id data out gen)))))
      (C (A 8) (C rdChanged (C (A 7) (C rdTick (C (A 7) (C rdTicks rdFin))))))
    = some (runNoun regsNoun ((gen.low, gen.back, chgOf dn data.core),
        runSt id gen.st dn (chgOf dn data.core))) := by
  have hl2 := K_layer2 hK
  obtain ⟨want, indi, seek, callees, area, low, back, st⟩ := gen
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hgu : nock (C by.gut.battery (C (C (identNoun id) (C (A 0) (A 0)))
      (C by.battery (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) layer2)))) by.gut.battery
      = some (C (A ((Treap.get ticks id).getD (0, 0)).1) (A ((Treap.get ticks id).getD (0, 0)).2)) :=
    gut_finMap layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
      (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks id (0, 0)
  have hpt : ∀ v : Nat × Nat, nock (C by.put.battery (C (C (identNoun id) (C (A v.1) (A v.2)))
      (C by.battery (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) layer2)))) by.put.battery
      = some (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) (Treap.put ticks id v)) := fun v =>
    put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks id v)
  have hpg : nock (C by.put.battery (C (C (identNoun id) dn.toNoun)
      (C by.battery (C (Treap.toNoun FDatum.toNoun g) layer2)))) by.put.battery
      = some (Treap.toNoun FDatum.toNoun (Treap.put g id dn)) :=
    put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun FDatum.toNoun g id dn)
  conv at hpg => lhs; simp only [FDatum.toNoun]
  by_cases h1 : dn.less = data.less ∧ dn.prod = data.prod ∧ dn.map = data.map ∧ dn.indi = data.indi ∧
      dn.seek = data.seek
  · have hc : chgOf dn data.core = false := by
      simp [chgOf, FDatum.core, h1]
    have hp1 := hpt (tick + 1, ((Treap.get ticks id).getD (0, 0)).2)
    simp only at hp1
    rw [hc]
    obtain ⟨dc, dno, dl, di, ds, dp, dm, da⟩ := data
    obtain ⟨e1, e2, e3, e4, e5⟩ := h1
    simp only at e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    simp (disch := ffar_disch) [hp1, hpg, hgu, dBase, rdChanged, rdTick, rdTicks, rdFin, nock_exec, hcf,
      hl2, sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun, runNoun, runSt, SkaState.toNoun, folOutNoun,
      FolOut.toNoun, GenS.toNoun, flag, by.arm_at, by_arm, by.put.arm_at, put_arm, by.gut.arm_at, gut_arm,
      Treap.gut]
  · have hc : chgOf dn data.core = true := by
      simp only [chgOf, FDatum.core, decide_eq_true_eq, ne_eq, Prod.mk.injEq]; exact h1
    have h1' : ¬ (dn.less = data.less ∧ dn.prod = data.prod ∧ dn.map = data.map ∧ dn.indi = data.indi ∧
      dn.seek = data.seek) := h1
    have hp1 := hpt (tick + 1, tick + 1)
    simp only at hp1
    rw [hc]
    simp (disch := ffar_disch) [h1', hp1, hpg, hgu, dBase, rdChanged, rdTick, rdTicks, rdFin, nock_exec, hcf,
      hl2, sock_toNoun_iff, cape_toNoun_iff, FDatum.toNoun, runNoun, runSt, SkaState.toNoun, folOutNoun,
      FolOut.toNoun, GenS.toNoun, flag, by.arm_at, by_arm, by.put.arm_at, put_arm, by.gut.arm_at, gut_arm]

end datum

end Compiler
end Formalization
