import lemmas.Ska.CompRelCopy
import lemmas.Ska.CompFragX

/-!
# Two operands with the relaxed `sem`

README Gaps 12.2.  `binaryN_semR`: the relaxed `sem` (`SemGR`) of a run made
of two operand runs for fork-free `%next` goals, a `+copy` and the block
that combines the operands (`binaryN_ok` of `CompBinaryN.lean`), from the
relaxed `sem` of the two operand runs (`SemNR`).

The block lemma must keep the operand registers as well (`KeepB`): in
`[5 [0 1] [1 6]]` the input need of the whole may hold `rp`, the register of
the first operand, and `rp` must survive the `%eqq` block.  The input
registers are threaded as follows.  A register of the input need is, by the
relaxed hypothesis, at or above the end of the run, or below its start and
not named by its goal, or in the merged need of `+copy`.  The copy block
keeps the merged need (`copy_okR`) and every register outside the two
operands' needs.  The run of `p` is given the register as one of its own
sure need, as one below its start outside `lp` (when it lies in `q`'s sure
need, which `hpq` keeps apart from `lp`), or as one at or above its end.  The
run of `q` is given a register of `lp` as one below its start outside `lq`.

`n5Pre_okK`: the block of `%5` with the extended keep set, since under
`%pick` it returns the registers unchanged and under `%next` it stores only
into the collapse register and a fresh one.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The keep set of the block of a binary case**: `Keep` and the
registers of the two operands' needs. -/
def KeepB (g0 g' : Gen Map) (goal : CGoal S) (lp lq : Need) (r : Nat) : Prop :=
  Keep g0 g' goal r ∨ NMem lp r ∨ NMem lq r

/-- **Two operands with the relaxed `sem`**, from the relaxed `sem` of the
operands and a block that keeps the operand registers. -/
theorem binaryN_semR {lib : Lib} {nm p q : Nomm} {goal : CGoal S} {g0 g' g1 g2 g3 : Gen Map}
    {lp lq : Sure S} {o : Nat} {nexq nexp nex : NextL S} {f : Noun → Noun → Option Noun}
    (hev : ∀ s, pureEval nm s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => f x y)
    (hg : GoalOK g0 goal) (hpre : Ext g0 g')
    (hlp : ∀ r, NMem lp.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hq : RunOKN (Map := Map) lib q lq (jmp0 o) g' g1 nexq)
    (hp : RunOKN (Map := Map) lib p lp nexq.th g1 g2 nexp)
    (Sq : SemNR (Map := Map) lib q lq (jmp0 o) g' g1 nexq)
    (Sp : SemNR (Map := Map) lib p lp nexq.th g1 g2 nexp)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3)) (d0 : g0.drop = false)
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → f x y = none ∨ ∃ v, f x y = some v ∧ GNot goal v)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y → GoalSem lib O c gul st (KeepB g0 g' goal lp.ned lq.ned) regs t (jmp0 o) goal (f x y)) :
    SemGR (Map := Map) lib nm goal g0 g3 nex := by
  -- the labels of the two runs are apart
  have lq' : ∀ e ∈ entries nexq.laz, g'.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(hq.labs e he).1, Nat.lt_trans (hq.labs e he).2.1 hq.hi⟩
  have lp' : ∀ e ∈ entries nexp.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(hp.labs e he).1, Nat.lt_trans (hp.labs e he).2.1 hp.hi⟩
  have apF : ∀ e ∈ nexp.laz.fork, ∀ e' ∈ nexq.laz.fork, e.1.1 ≠ e'.1.1 := fun e he e' he' => by
    have a := lp' e.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he))
    have b := lq' e'.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he'))
    omega
  have apB : ∀ e ∈ nexp.laz.bond, ∀ e' ∈ nexq.laz.bond, e.1 ≠ e'.1 := fun e he e' he' => by
    have a := lp' e (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he))
    have b := lq' e' (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he'))
    omega
  obtain ⟨n, hcp, rfl⟩ := copyL_apart_some apF apB hc
  obtain ⟨EC, eth, bo3, CM, CS⟩ := copy_ok hcp
  have gm : ∀ r, GMem goal r → r < g0.re := fun r hr => by
    cases goal with
    | next laz th => exact hg.2 r hr
    | _ => exact hr.elim
  have lpl : ∀ r, NMem lp.ned r → r < g'.re := fun r hr => by
    rcases hlp r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have lql : ∀ r, NMem lq.ned r → r < g'.re := fun r hr => by
    rcases hlq r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have mp : ∀ r, NMem nexp.laz.sure.ned r → NMem lp.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := hp.regs
  have mq : ∀ r, NMem nexq.laz.sure.ned r → NMem lq.ned r ∨ (g'.re ≤ r ∧ r < g1.re) := hq.regs
  have l0 := hpre.1
  have l1 := hq.ext.1
  have l2 := hp.ext.1
  have l3 := EC.1
  have lowP : ∀ r, NMem nexp.laz.sure.ned r → r < g2.re := fun r hr => by
    rcases mp r hr with a | ⟨_, a⟩
    · have := lpl r a; omega
    · exact a
  have lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases mq r hr with a | ⟨_, a⟩
    · have := lql r a; omega
    · exact a
  have P : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · rcases mp r h1 with a | ⟨a, _⟩ <;> rcases mq r h2 with b | ⟨b, b'⟩
      · exact hpq r a b
      · have := lpl r a; omega
      · have := lql r b; omega
      · omega
    · rcases hr with h | h
      · exact lowP r h
      · have := lowQ r h; omega
  have d2 : g2.drop = false := hp.ext.2.2.1.trans (hq.ext.2.2.1.trans (hpre.2.2.1.trans d0))
  have Eq3 : Ext g1 g3 := hp.ext.trans EC
  have E'3 : Ext g' g3 := hq.ext.trans Eq3
  have bo01 := hpre.2.1
  have bo12 := hq.ext.2.1
  have bo23 := hp.ext.2.1
  have hp3 : Ext g2 g3 := EC
  -- the entries
  have memN : ∀ e, e ∈ entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork) (nexp.laz.bond ++ nexq.laz.bond)) ↔
      e ∈ entries nexp.laz ∨ e ∈ entries nexq.laz := fun e => by
    rw [(entries_side_perm _ _ _).mem_iff, List.mem_append]
  have labN : ∀ k, k ∈ (entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork)
      (nexp.laz.bond ++ nexq.laz.bond))).map Prod.fst → g'.bo ≤ k ∧ k < g2.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    rcases (memN e).mp he with a | a
    · have := lp' e a; omega
    · have := lq' e a; omega
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have hN : ∀ r, NMem ned r → g3.re ≤ r ∨ (r < g0.re ∧ ¬ GMem goal r) ∨ NMem n.laz.ned r := hned
  -- registers outside the merged need lie outside both operands' needs
  have outPQ : ∀ r, (g3.re ≤ r ∨ (r < g0.re ∧ ¬ GMem goal r)) →
      ¬ NMem nexp.laz.sure.ned r ∧ ¬ NMem nexq.laz.sure.ned r := by
    intro r hr
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · have := lowP r hm
      rcases hr with hr | ⟨hr, hr'⟩
      · omega
      · rcases mp r hm with a | ⟨a, _⟩
        · rcases hlp r a with b | ⟨b, _⟩
          · exact hr' b
          · omega
        · omega
    · have := lowQ r hm
      rcases hr with hr | ⟨hr, hr'⟩
      · omega
      · rcases mq r hm with a | ⟨a, _⟩
        · rcases hlq r a with b | ⟨b, _⟩
          · exact hr' b
          · omega
        · omega
  -- the copy block
  have agC : Agree c g2 g3 := fun k h0 h1 => ag.1 k (by omega) h1 (fun hm => by have := labN k hm; omega)
  obtain ⟨R1, hs1, hs1', u1, um, e1⟩ := copy_okR hcp P d2 c agC lib σ O st regs t gul s hh
  have keep1 : ∀ r, KeepI goal g0 ned r → SkaModel.read r R1 = SkaModel.read r regs := by
    intro r hr
    by_cases hm : NMem n.laz.ned r
    · exact um r hm
    · have hr' : g3.re ≤ r ∨ (r < g0.re ∧ ¬ GMem goal r) := by
        rcases hr with hr | hr
        · exact Or.inr hr
        · rcases hN r hr with e | e | e
          · exact Or.inl e
          · exact Or.inr e
          · exact absurd e hm
      exact u1 r (outPQ r hr').1 (outPQ r hr').2
  have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => keep1 r (Or.inr hr)) hn
  have agP : AgreeP lib O c gul st t ned g1 g2 nexp.laz s0 s :=
    ag.part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
      (fun k h0 h1 hm => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        rcases (memN e).mp he with a | a
        · exact List.mem_map_of_mem a
        · have := lq' e a; omega)
      (fun e he => (lp' e he).2)
  -- the hypothesis of `p`'s run
  have inP : ∀ r, NMem ned r → InR (CGoal.next lp nexq.th) g1 g2 nexp.laz.sure.ned r := by
    intro r hr
    show g2.re ≤ r ∨ (r < g1.re ∧ ¬ NMem lp.ned r) ∨ NMem nexp.laz.sure.ned r
    rcases hN r hr with e | ⟨e, e'⟩ | e
    · exact Or.inl (by omega)
    · refine Or.inr (Or.inl ⟨by omega, fun hm => ?_⟩)
      rcases hlp r hm with b | ⟨b, _⟩
      · exact e' b
      · omega
    · rcases CM r e with a | a | ⟨a, _⟩
      · exact Or.inr (Or.inr a)
      · refine Or.inr (Or.inl ⟨lowQ r a, fun hm => ?_⟩)
        rcases mq r a with b | ⟨b, _⟩
        · exact hpq r hm b
        · have := lpl r hm; omega
      · exact Or.inl a
  have Hp := Sp c ned σ O st t gul s0 s agP inP R1 hs1 hn1
  have agQ0 : Agree c g0 g' := fun k h0 h1 =>
    (ag.1 k h0 (by omega) (fun hm => by have := labN k hm; omega)).trans (E'3.2.2.2 k h1)
  rw [hev]
  cases ep : pureEval p s with
  | none =>
    rw [ep] at Hp
    exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans Hp)
  | some x =>
    rw [ep] at Hp
    simp only [Option.bind_some]
    by_cases fx : FitsS lp x
    · obtain ⟨R2, hl2, k2, e2⟩ := Hp.1 fx
      have hq2 : HoldsS nexq.laz.sure R2 s := by
        refine ⟨HoldsN.agree _ (fun r hr => k2 r (Or.inl ⟨lowQ r hr, ?_⟩)) hs1'.1, hs1'.2⟩
        intro hm
        rcases mq r hr with a | ⟨a, _⟩
        · exact hpq r hm a
        · have := lpl r hm; omega
      have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r (Or.inr hr)) hn1
      have agQ : AgreeP lib O c gul st t ned g' g1 nexq.laz s0 s :=
        ag.part bo01 Eq3 (fun e he => (memN e).mpr (Or.inr he))
          (fun k h0 h1 hm => by
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
            rcases (memN e).mp he with a | a
            · have := lp' e a; omega
            · exact List.mem_map_of_mem a)
          (fun e he => (lq' e he).2)
      -- the hypothesis of `q`'s run
      have inQ : ∀ r, NMem ned r → InR (CGoal.next lq (jmp0 o)) g' g1 nexq.laz.sure.ned r := by
        intro r hr
        show g1.re ≤ r ∨ (r < g'.re ∧ ¬ NMem lq.ned r) ∨ NMem nexq.laz.sure.ned r
        rcases hN r hr with e | ⟨e, e'⟩ | e
        · exact Or.inl (by omega)
        · refine Or.inr (Or.inl ⟨by omega, fun hm => ?_⟩)
          rcases hlq r hm with b | ⟨b, _⟩
          · exact e' b
          · omega
        · rcases CM r e with a | a | ⟨a, _⟩
          · rcases mp r a with b | ⟨b, _⟩
            · exact Or.inr (Or.inl ⟨lpl r b, hpq r b⟩)
            · exact Or.inl b
          · exact Or.inr (Or.inr a)
          · exact Or.inl (by omega)
      have Hq := Sq c ned σ O st t gul s0 s agQ inQ R2 hq2 hn2
      cases eq : pureEval q s with
      | none =>
        rw [eq] at Hq
        exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans Hq))
      | some y =>
        rw [eq] at Hq
        simp only [Option.bind_some]
        by_cases fy : FitsS lq y
        · obtain ⟨R3, hq3, k3, e3⟩ := Hq.1 fy
          have hl3 : HoldsN lp.ned R3 x :=
            HoldsN.agree _ (fun r hr => k3 r (Or.inl ⟨lpl r hr, hpq r hr⟩)) hl2
          have B := hblk c agQ0 σ O st R3 t gul x y fx fy hl3 hq3
          refine GoalSem.transfer (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans e3)) (fun r hk => ?_)
            (GoalSem.mono (fun r hk => ?_) B)
          · -- the registers kept across the copy block and the two runs
            have k3' : KeepI (CGoal.next lq (jmp0 o)) g' ned r := by
              rcases hk with ⟨e, e'⟩ | e
              · refine Or.inl ⟨by omega, fun hm => ?_⟩
                rcases hlq r hm with b | ⟨b, _⟩
                · exact e' b
                · omega
              · exact Or.inr e
            have k2' : KeepI (CGoal.next lp nexq.th) g1 ned r := by
              rcases hk with ⟨e, e'⟩ | e
              · refine Or.inl ⟨by omega, fun hm => ?_⟩
                rcases hlp r hm with b | ⟨b, _⟩
                · exact e' b
                · omega
              · exact Or.inr e
            rw [k3 r k3', k2 r k2', keep1 r hk]
          · -- the block keeps them
            show Keep g0 g' goal r ∨ NMem lp.ned r ∨ NMem lq.ned r
            have ngm : g'.re ≤ r → ¬ GMem goal r := fun h1 h2 => by have := gm r h2; omega
            rcases hk with ⟨e, e'⟩ | e
            · exact Or.inl ⟨Or.inl e, e'⟩
            · rcases hN r e with a | ⟨a, a'⟩ | a
              · exact Or.inl ⟨Or.inr (by omega), ngm (by omega)⟩
              · exact Or.inl ⟨Or.inl a, a'⟩
              · rcases CM r a with b | b | ⟨b, _⟩
                · rcases mp r b with c' | ⟨c', _⟩
                  · exact Or.inr (Or.inl c')
                  · exact Or.inl ⟨Or.inr (by omega), ngm (by omega)⟩
                · rcases mq r b with c' | ⟨c', _⟩
                  · exact Or.inr (Or.inr c')
                  · exact Or.inl ⟨Or.inr c', ngm c'⟩
                · exact Or.inl ⟨Or.inr (by omega), ngm (by omega)⟩
        · exact goalSem_crash_or (hnot x y (Or.inr fy))
            (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans (Hq.2 fy)))
    · have hc2 := Hp.2 fx
      cases eq : pureEval q s with
      | none => exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans hc2)
      | some y =>
        simp only [Option.bind_some]
        exact goalSem_crash_or (hnot x y (Or.inl fx)) (by rw [eth] at e1 ⊢; exact e1.trans hc2)

end Comp
end SkaModel
end Formalization
