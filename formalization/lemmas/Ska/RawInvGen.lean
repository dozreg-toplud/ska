import lemmas.Ska.RawInvStep
import lemmas.Ska.CompFootX
import lemmas.Ska.CompDown

/-!
# Raw `+comp` output: the invariant of a state of `+comp`

README Gaps 14.  `SI g`: the state does not drop, its labels lie below `bo`,
its blocks jump down, mention only registers below `re`, define each
register once (`BlkNodup`, `Cross`), have no trace hint op, at most one
parameter, and arguments above the parameters at or below their targets.
The three steps that change a state keep it: allocating registers
(`si_reg`, `si_re`), a new block (`si_emit`, under `EmitOK`), ops in front
of a block (`si_addOps`, under `OpsOK`).

`defd_of_wroteIn`: the footprint of track C (`WroteIn`) bounds the new
definitions.  `GLive`: what a run may leave live, the registers live at its
goal's continuation that its goal does not name.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Reads of single ops -/

theorem reads_mov {s d r : Nat} : r ∈ aliasReads (Pole.mov s d) ↔ r = s := by
  by_cases h : s = d
  · subst h; simp [aliasReads, aliasDst, Opt.poleRegs]
  · simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h]

theorem reads_inc {s d r : Nat} : r ∈ aliasReads (Pole.inc s d) ↔ r = s := by
  by_cases h : s = d
  · subst h; simp [aliasReads, aliasDst, Opt.poleRegs]
  · simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h]

theorem reads_hed {s d r : Nat} : r ∈ aliasReads (Pole.hed s d) ↔ r = s := by
  by_cases h : s = d
  · subst h; simp [aliasReads, aliasDst, Opt.poleRegs]
  · simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h]

theorem reads_tal {s d r : Nat} : r ∈ aliasReads (Pole.tal s d) ↔ r = s := by
  by_cases h : s = d
  · subst h; simp [aliasReads, aliasDst, Opt.poleRegs]
  · simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h]

theorem reads_con {a c d r : Nat} : r ∈ aliasReads (Pole.con a c d) ↔ r = a ∨ r = c := by
  by_cases h1 : a = d
  · subst h1
    by_cases h2 : c = a
    · subst h2; simp [aliasReads, aliasDst, Opt.poleRegs]
    · simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h2, or_comm]
  · by_cases h2 : c = d
    · subst h2; simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h1]
    · simp [aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, h1, h2]

theorem reads_imm {n : Noun} {d r : Nat} : r ∉ aliasReads (Pole.imm n d) := by
  simp [aliasReads, aliasDst, Opt.poleRegs]

theorem reads_cel {p r : Nat} : r ∈ aliasReads (Pole.cel p) ↔ r = p := by
  simp [aliasReads, aliasDst, Opt.poleRegs]

theorem reads_equ {l q r : Nat} : r ∈ aliasReads (Pole.equ l q) ↔ r = l ∨ r = q := by
  simp [aliasReads, aliasDst, Opt.poleRegs]

/-- A destination is among the registers an op mentions. -/
theorem dst_mem_regs {op : Pole} {r : Nat} (h : aliasDst op = some r) : r ∈ Comp.poleRegs op := by
  cases op <;> simp_all [aliasDst, Comp.poleRegs]

/-! ## The invariant of a state -/

/-- **The invariant of a state on the first fragment.** -/
structure SI (g : Comp.Gen Map) : Prop where
  drop : g.drop = false
  bo1 : 1 ≤ g.bo
  lab : ∀ k b, HoonMap.get g.blocks k = some b → k < g.bo
  jd : JDown g.blocks
  regs : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b
  nd : BlkNodup g.blocks
  cr : Cross g.blocks
  tr : NoTr g.blocks
  p1 : Par1 g.blocks
  aa : ArgsAbove g.blocks

theorem SI.defd_lt {g : Comp.Gen Map} (h : SI g) {r : Nat} (hd : Defd g.blocks r) : r < g.re := by
  obtain ⟨o, b, hb, hm⟩ := defd_iff.mp hd
  have R := h.regs o b hb
  rcases mem_blockDefs.mp hm with hm | hm
  · exact R.1 r hm
  · obtain ⟨op, hop, hdst⟩ := mem_defsOf.mp hm
    exact R.2.1 op hop r (dst_mem_regs hdst)

theorem SI.below {g : Comp.Gen Map} (h : SI g) (L : Nat) : DownBelow g.blocks L := h.jd.below L

theorem SI.none {g : Comp.Gen Map} (h : SI g) {k : Nat} (hk : g.bo ≤ k) : HoonMap.get g.blocks k = Option.none := by
  cases e : HoonMap.get g.blocks k with
  | none => rfl
  | some b => have := h.lab k b e; omega

theorem si_reg {g : Comp.Gen Map} (h : SI g) {k : Nat} (hk : g.re ≤ k) : SI { g with re := k } :=
  ⟨h.drop, h.bo1, h.lab, h.jd, fun o b hb => (h.regs o b hb).mono fun x hx => Nat.lt_of_lt_of_le hx hk,
    h.nd, h.cr, h.tr, h.p1, h.aa⟩

theorem si_re {g g' : Comp.Gen Map} {r : Nat} (h : SI g) (hr : (re : CM Map Nat) g = some (r, g')) :
    SI g' ∧ r = g.re ∧ g'.re = g.re + 1 ∧ g'.blocks = g.blocks ∧ g'.bo = g.bo := by
  rw [re_apply] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨si_reg h (Nat.le_succ _), rfl, rfl, rfl, rfl⟩

/-- What a new block owes the invariant. -/
structure EmitOK (g : Comp.Gen Map) (b : Blob) : Prop where
  jd : ∀ j ∈ getJmps b.fin, j.there < g.bo
  regs : BlobIn (· < g.re) b
  nd : (blockDefs b).Nodup
  fresh : ∀ r ∈ blockDefs b, ¬ Defd g.blocks r
  tr : ∀ op ∈ b.body, trOp op = false
  p1 : b.par.length ≤ 1
  args : ∀ j ∈ getJmps b.fin, ∀ r, some r ∈ j.args → ∀ z bz, HoonMap.get (HoonMap.put g.blocks g.bo b) z = some bz →
    z ≤ j.there → ∀ x ∈ bz.par, x < r

theorem si_emit {g g' : Comp.Gen Map} {b : Blob} {o : Nat} (h : SI g) (E : EmitOK g b)
    (he : (emit b : CM Map Nat) g = some (o, g')) :
    SI g' ∧ o = g.bo ∧ g'.blocks = HoonMap.put g.blocks g.bo b ∧ g'.re = g.re ∧ g'.bo = g.bo + 1 := by
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hb : (g.emitted b).blocks = HoonMap.put g.blocks g.bo b := by simp [Gen.emitted, h.drop]
  have hl := h.none (Nat.le_refl g.bo)
  refine ⟨⟨by simp [Gen.emitted, h.drop], by simp [Gen.emitted], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, hb, rfl, rfl⟩ <;> rw [hb]
  · intro k b' hk
    rcases get_put_cases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · simp [Gen.emitted]
    · have := h.lab k b' hk; simp [Gen.emitted]; try omega
  · exact jdown_put h.jd E.jd
  · intro k b' hk
    rcases get_put_cases hk with ⟨-, rfl⟩ | ⟨-, hk⟩
    · exact E.regs
    · exact h.regs k b' hk
  · exact blkNodup_put h.nd E.nd
  · exact cross_put h.cr hl E.fresh
  · exact noTr_put h.tr E.tr
  · exact par1_put h.p1 E.p1
  · exact argsAbove_put h.aa h.jd h.lab fun j hj r hr => ⟨E.jd j hj, E.args j hj r hr⟩

/-- A block with no parameter, no argument on its jumps, and ops that define
fresh registers once. -/
theorem emitOK_of {g : Comp.Gen Map} {b : Blob} (hp : b.par = []) (ha : ∀ j ∈ getJmps b.fin, j.args = [])
    (hj : ∀ j ∈ getJmps b.fin, j.there < g.bo) (hr : RegsIn (· < g.re) b.body) (hf : FinIn (· < g.re) b.fin)
    (hn : (defsOf b.body).Nodup) (hfr : ∀ r ∈ defsOf b.body, ¬ Defd g.blocks r)
    (ht : ∀ op ∈ b.body, trOp op = false) : EmitOK g b where
  jd := hj
  regs := ⟨by rw [hp]; exact fun _ h => absurd h List.not_mem_nil, hr, hf⟩
  nd := by unfold blockDefs; rw [hp]; exact hn
  fresh := fun r hr' => hfr r (by unfold blockDefs at hr'; rw [hp] at hr'; exact hr')
  tr := ht
  p1 := by rw [hp]; exact Nat.zero_le _
  args := fun j hj' r hr' => by rw [ha j hj'] at hr'; cases hr'

/-- A block with no parameter, no body and a hop without arguments. -/
theorem emitOK_hop {g : Comp.Gen Map} {j : Jmp} (ha : j.args = []) (hj : j.there < g.bo) :
    EmitOK g ⟨[], [], Termin.hop j⟩ :=
  emitOK_of rfl (fun j' hj' => by simp [getJmps] at hj'; rw [hj']; exact ha)
    (fun j' hj' => by simp [getJmps] at hj'; rw [hj']; exact hj) (RegsIn.nil _)
    (fun x hx => by simp [ha] at hx) (by simp [defsOf]) (fun r hr => by simp [defsOf] at hr)
    (fun op h => absurd h List.not_mem_nil)

/-- What ops put in front of a block owe the invariant. -/
structure OpsOK (g : Comp.Gen Map) (A : List Pole) : Prop where
  regs : RegsIn (· < g.re) A
  nd : (defsOf A).Nodup
  fresh : ∀ r ∈ defsOf A, ¬ Defd g.blocks r
  tr : ∀ op ∈ A, trOp op = false

theorem si_addOps {g g' : Comp.Gen Map} {o : Nat} {A : List Pole} {u : Unit} (h : SI g) (P : OpsOK g A)
    (ha : addOps o A g = some (u, g')) :
    SI g' ∧ ∃ b, HoonMap.get g.blocks o = some b ∧ g'.blocks = HoonMap.put g.blocks o (pre A b) ∧
      g'.re = g.re ∧ g'.bo = g.bo := by
  obtain ⟨b, hb, rfl⟩ := addOps_spec ha h.drop
  refine ⟨⟨h.drop, h.bo1, ?_, jdown_prepend h.jd hb, ?_, blkNodup_prepend h.nd hb P.nd P.fresh,
    cross_prepend h.cr hb P.fresh, noTr_prepend h.tr hb P.tr, par1_prepend h.p1 hb, argsAbove_prepend h.aa hb⟩,
    b, hb, rfl, rfl, rfl⟩
  · intro k b' hk
    rcases get_put_cases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · exact h.lab k b hb
    · exact h.lab k b' hk
  · intro k b' hk
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have R := h.regs k b hb
      exact ⟨R.1, P.regs.append R.2.1, R.2.2⟩
    · exact h.regs k b' hk

theorem opsOK_nil (g : Comp.Gen Map) : OpsOK g [] :=
  ⟨RegsIn.nil _, by simp [defsOf], fun r h => by simp [defsOf] at h, fun _ h => absurd h List.not_mem_nil⟩

/-! ## The footprint bounds the definitions -/

theorem aliasDst_poleWr {op : Pole} {r : Nat} (h : aliasDst op = some r) : r ∈ poleWr op := by
  cases op <;> simp_all [aliasDst, poleWr]

theorem defd_of_wroteIn {Q : Nat → Prop} {g g' : Comp.Gen Map} (w : WroteIn Q g g') {r : Nat}
    (hd : Defd g'.blocks r) : Defd g.blocks r ∨ Q r := by
  obtain ⟨o, b', hb', hm⟩ := defd_iff.mp hd
  rcases w o b' hb' with ⟨b, A, hb, rfl, wA⟩ | wB
  · rcases mem_blockDefs_pre.mp hm with h | h
    · exact Or.inl (defd_iff.mpr ⟨o, b, hb, h⟩)
    · obtain ⟨op, hop, hdst⟩ := mem_defsOf.mp h
      exact Or.inr (wA op hop r (aliasDst_poleWr hdst))
  · rcases mem_blockDefs.mp hm with h | h
    · exact Or.inr (wB.1 r h)
    · obtain ⟨op, hop, hdst⟩ := mem_defsOf.mp h
      exact Or.inr (wB.2 op hop r (aliasDst_poleWr hdst))

/-! ## Goals -/

/-- The goal's jumps carry no arguments. -/
def GArgs : CGoal S → Prop
  | CGoal.next _ th => th.args = []
  | CGoal.pick z o => z.args = [] ∧ o.args = []
  | CGoal.done => True

/-- What a run for `goal` may leave live at its entry beyond its result's
need: registers live at the goal's continuation that the goal does not
name. -/
def GLive (bl : Map Blob) : CGoal S → Nat → Prop
  | CGoal.next laz th, r => Live bl th.there r ∧ ¬ NMem laz.ned r
  | CGoal.pick z o, r => Live bl z.there r ∨ Live bl o.there r
  | CGoal.done, _ => False

end Raw
end SkaModel
end Formalization
