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

/-- **The block of `%5` keeps the operand registers**: `n5Pre_ok` with the
keep set `KeepB`. -/
theorem n5Pre_okK {lib : Lib} {goal : CGoal S} {g0 g2 : Gen Map} {o : Nat}
    (h2 : n5Pre g0.re (g0.re + 1) goal { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } = some (o, g2))
    (hg : GoalOK g0 goal) (hj : GJ g0.bo goal) (b0 : 1 ≤ g0.bo) :
    Ext g0 g2 ∧ Grow g0 g2 ∧ g0.re + 2 ≤ g2.re ∧ 1 ≤ o ∧ o < g2.bo ∧
    ∀ (c : Straight Map), Agree c g0 g2 → g0.drop = false → ∀ (σ : Type) (O : Oracle σ) st regs t gul x y,
      SkaModel.read g0.re regs = some x → SkaModel.read (g0.re + 1) regs = some y →
      GoalSem lib O c gul st (KeepB g0 g2 goal (Need.this g0.re) (Need.this (g0.re + 1))) regs t (jmp0 o) goal
        (some (eqCode x y)) := by
  have G0 : Ext g0 { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } := (ext_re _).trans (ext_re _)
  have G0g : Grow g0 { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } := (grow_re _).trans (grow_re _)
  cases goal with
  | pick z o' =>
    simp only [n5Pre, emit_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine ⟨G0.trans (ext_emit _ _), G0g.trans (grow_emit (jumpsBelow_two rfl hj.1 hj.2)),
      by simp [emitted_re], b0, by simp [emitted_bo], fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
    have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    by_cases e : x = y
    · rw [if_pos e] at hj
      simp only [eqCode, if_pos e]
      exact ⟨regs, fun _ _ => rfl, hj⟩
    · rw [if_neg e] at hj
      simp only [eqCode, if_neg e]
      exact ⟨regs, fun _ _ => rfl, hj⟩
  | done =>
    simp only [n5Pre] at h2
    obtain ⟨⟨o0, o1⟩, g5, h5, h2⟩ := bind_some h2
    have B := doneBlocks_down h5 b0
    obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h5
    rw [emit_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine ⟨G0.trans (D.trans (ext_emit _ _)), G0g.trans (B.1.trans (grow_emit (jumpsBelow_two rfl B.2.1 B.2.2))),
      by simp only [emitted_re, er]; omega, Nat.le_trans b0 B.1.bo, by simp [emitted_bo],
      fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
    have hd5 : g5.drop = false := D.2.2.1.trans hd
    have hb := emitted_get' hd5 (hc _ (by simp only [eb]; omega) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    have DB' := DB c hd ((hc.right G0).left D (ext_emit _ _)) lib σ O st regs t gul
    show goJ lib O c gul st regs t (jmp0 g5.bo) = some (toneOf t (some (eqCode x y)), st)
    by_cases e : x = y
    · rw [if_pos e] at hj; simp only [eqCode, if_pos e]; exact hj.trans DB'.1
    · rw [if_neg e] at hj; simp only [eqCode, if_neg e]; exact hj.trans DB'.2
  | next laz th =>
    simp only [n5Pre] at h2
    obtain ⟨a, g5, h5, h2⟩ := bind_some h2
    obtain ⟨E5, ea, hnone, hsome⟩ := collapse_ok h5
    have C := collapse_down h5 hj.1 hj.2 b0
    have l5 := E5.1
    simp only at l5
    cases a with
    | none =>
      obtain ⟨hn, hl⟩ := hnone rfl
      simp only at h2
      rw [if_pos ea, emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      refine ⟨G0.trans (E5.trans (ext_emit _ _)),
        G0g.trans (C.1.trans (grow_emit (jumpsBelow_one rfl ⟨hj.1, Nat.lt_of_lt_of_le hj.2 C.1.bo⟩))),
        by simp only [emitted_re]; omega, Nat.le_trans b0 C.1.bo, by simp [emitted_bo],
        fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
      have hd5 : g5.drop = false := E5.2.2.1.trans hd
      have hb := emitted_get' hd5 (hc _ (by have := E5.2.1; simp at this; omega) (by simp [emitted_bo]))
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
      rw [show [Pole.equ g0.re (g0.re + 1)] = [Pole.equ g0.re (g0.re + 1)] ++ [] from rfl, runs_equ hx hy,
        execBlob_hop, jmp0_of_args ea] at hj
      exact ⟨fun _ => ⟨regs, by rw [hn]; trivial, fun _ _ => rfl, hj⟩,
        fun hf => absurd ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩ hf⟩
    | some ro =>
      obtain ⟨r, o''⟩ := ro
      obtain ⟨hmr, _, hs⟩ := hsome r o'' rfl
      have Co := C.2 r o'' rfl
      simp only at h2
      obtain ⟨⟨z, o'⟩, g6, h6, h2⟩ := bind_some h2
      have hr : r < g5.re := by
        rcases hmr with hm | ⟨_, h⟩
        · have := hg.2 r hm; omega
        · exact h
      have Fd := forl_down h6 Co.1 Co.2 (Nat.le_trans b0 C.1.bo)
      obtain ⟨E6, er6, eb6, F⟩ := forl_ok h6 hr
      rw [emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have Ep := ext_emit g6 ⟨[], [], Termin.eqq g0.re (g0.re + 1) (jmp0 z) (jmp0 o')⟩
      refine ⟨G0.trans (E5.trans (E6.trans Ep)),
        G0g.trans (C.1.trans (Fd.1.trans (grow_emit (jumpsBelow_two rfl Fd.2.1 Fd.2.2)))),
        by simp only [emitted_re, er6]; omega, Nat.le_trans b0 (Nat.le_trans C.1.bo Fd.1.bo), by simp [emitted_bo],
        fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
      have hd5 : g5.drop = false := E5.2.2.1.trans hd
      have hd6 : g6.drop = false := E6.2.2.1.trans hd5
      have hb := emitted_get' hd6 (hc _ (by have := E5.2.1; have := E6.2.1; simp at *; omega)
        (by simp [emitted_bo]))
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
      rw [execBlob_eqq, hx, hy] at hj
      simp only [Option.bind_some] at hj
      have F' := F hd5 c ((hc.right (G0.trans E5)).left E6 Ep) lib σ O st regs t gul
      have hagX := (hc.right G0).left E5 (E6.trans Ep)
      have keep : ∀ (v : Noun) (k rr : Nat), g5.re ≤ k → k < g5.re + 2 →
          KeepB g0 (g6.emitted ⟨[], [], Termin.eqq g0.re (g0.re + 1) (jmp0 z) (jmp0 o')⟩) (CGoal.next laz th)
            (Need.this g0.re) (Need.this (g0.re + 1)) rr →
          SkaModel.read rr (store r v (store k v regs)) = SkaModel.read rr regs := by
        intro v k rr hk hk' hK
        rcases hK with ⟨k1, k2⟩ | hK
        · simp only [emitted_re, er6] at k1
          have hne : rr ≠ r := fun e => by
            subst e
            rcases hmr with hm | ⟨hm, _⟩
            · exact k2 hm
            · simp at hm; omega
          rw [read_store_ne hne, read_store_ne (show rr ≠ k by omega)]
        · have hrr : rr = g0.re ∨ rr = g0.re + 1 := by
            simp only [NMem] at hK; exact hK
          have hne : rr ≠ r := fun e => by
            subst e
            rcases hmr with hm | ⟨hm, _⟩
            · have := hg.2 rr hm; omega
            · simp at hm; omega
          rw [read_store_ne hne, read_store_ne (show rr ≠ k by omega)]
      by_cases e : x = y
      · rw [if_pos e] at hj
        simp only [eqCode, if_pos e]
        exact GoalSem.transfer (hj.trans F'.1) (keep (A 0) g5.re · (Nat.le_refl _) (by omega))
          (hs hd c hagX lib σ O st _ t gul 0 (read_store_eq _ _ _))
      · rw [if_neg e] at hj
        simp only [eqCode, if_neg e]
        exact GoalSem.transfer (hj.trans F'.2) (keep (A 1) (g5.re + 1) · (Nat.le_succ _) (by omega))
          (hs hd c hagX lib σ O st _ t gul 1 (read_store_eq _ _ _))


/-- `SemGR` for `%done` and `%pick` gives `SemPR`. -/
theorem SemGR.toP {lib : Lib} {nm : Nomm} {goal : CGoal S} (hg : NotNext goal) {g0 g1 : Gen Map} {nex : NextL S}
    (h : SemGR (Map := Map) lib nm goal g0 g1 nex) : SemPR (Map := Map) lib nm goal g0 g1 nex :=
  fun c ned σ O st t gul s0 s ag hned regs hh hn =>
    goalSem_mono (fun r hr => hr.elim (fun e => Or.inl ⟨e, notNext_gmem hg r⟩) Or.inr) goal _
      (h c ned σ O st t gul s0 s ag hned regs hh hn)

/-- **`[5 p q]` for a fork-free goal with the relaxed `sem`**, from the
relaxed `sem` of the operands. -/
theorem runOKG_n5_semR (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (sp : OKNR (S := S) (Map := Map) lib p)
    (sq : OKNR (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q) (hpp : p.pure = true)
    {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hg : GoalOK g0 goal) (hj : GJ g0.bo goal) (hcount : sixCount (Nomm.n5 p q) ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n5 p q) (CGoal.toL goal) region g0 = some (nex, g1)) :
    SemGR (Map := Map) lib (Nomm.n5 p q) goal g0 g1 nex := by
  rw [runL_n5_toL] at h
  obtain ⟨rp, gA, hA, h⟩ := bind_some h
  obtain ⟨rq, gB, hB, h⟩ := bind_some h
  rw [re_apply] at hA hB
  simp only [Option.some.injEq, Prod.mk.injEq] at hA hB
  obtain ⟨rfl, rfl⟩ := hA
  obtain ⟨rfl, rfl⟩ := hB
  obtain ⟨o, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, G2, hre, o1, o2, _⟩ := n5Pre_ok (lib := lib) h2 hg hj b0
  obtain ⟨-, -, -, -, -, B⟩ := n5Pre_okK (lib := lib) h2 hg hj b0
  obtain ⟨nexq, g3, h3, h⟩ := bind_some h
  obtain ⟨nexq', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, g4, h4, hc⟩ := bind_some h
  rw [sixCount_n5] at hcount
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (G2.toU hu).up hu
  have c2 : Clear g2 := hcl0.growU (G2.toU hu)
  have Rq := hq (sur := lazyReg (g0.re + 1)) (th := jmp0 o) ⟨o1, o2⟩ rfl
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; omega⟩ trivial (by omega)
    (Nat.le_trans b0 G2.bo) d2 u2 h3
  have Sq := sq (sur := lazyReg (g0.re + 1)) (th := jmp0 o) ⟨o1, o2⟩ rfl
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; omega⟩ trivial (by omega)
    (Nat.le_trans b0 G2.bo) d2 u2 c2 h3
  have c3 : Clear g3 := c2.growU Rq.grow
  have Rp := hp (sur := lazyReg g0.re) (th := nexq.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; have := Rq.ext.1; omega⟩ trivial (by omega)
    (Nat.le_trans b0 (Nat.le_trans G2.bo Rq.grow.bo)) (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) h4
  have Sp := sp (sur := lazyReg g0.re) (th := nexq.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; have := Rq.ext.1; omega⟩ trivial (by omega)
    (Nat.le_trans b0 (Nat.le_trans G2.bo Rq.grow.bo)) (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) c3 h4
  exact binaryN_semR (pureEval_n5 p q) hg E2
    (fun r hr => by simp only [lazyReg, NMem] at hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r hr => by simp only [lazyReg, NMem] at hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r h1 h2 => by simp only [lazyReg, NMem] at h1 h2; omega) Rq Rp Sq Sp
    (cq (sur := lazyReg _) trivial h3) (cp (sur := lazyReg _) trivial h4) hc d0
    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_lazyReg _ x)) (fun a => a (fitsS_lazyReg _ y))) id)
    (fun c hc σ O st regs t gul x y _ _ hx hy => B c hc d0 σ O st regs t gul x y hx hy)

/-- **`+split` keeps the registers of the head and the tail**: the ops of
the split block write only registers of the goal's need outside both
(`wr_splitNeedS`). -/
theorem split_okK {laz : Sure S} {th : Jmp} {g g' : Gen Map} {hed tel : Sure S} {o : Nat}
    (h : Comp.split ⟨laz, th⟩ g = some ((hed, tel, o), g')) (hd : g.drop = false) (dn : Distinct laz.ned)
    (lo : ∀ y, NMem laz.ned y → y < g.re) :
    o = g.bo ∧ Ext g g' ∧ g'.bo = g.bo + 1 ∧
    (∀ y, NMem hed.ned y → NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (∀ y, NMem tel.ned y → NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (Distinct hed.ned ∧ Distinct tel.ned ∧ (∀ y, NMem hed.ned y → ¬ NMem tel.ned y)) ∧
    (∀ (c : Straight Map), Agree c g g' → ∀ (lib : Lib) (σ : Type) (O : Oracle σ) st t
        (R : Map (Option Noun)) a b gul, HoldsN hed.ned R a → HoldsN tel.ned R b →
        ∃ R', HoldsN laz.ned R' (C a b) ∧
          (∀ y, (¬ NMem laz.ned y ∨ NMem hed.ned y ∨ NMem tel.ned y) → SkaModel.read y R' = SkaModel.read y R) ∧
          goJ lib O c gul st R t (jmp0 o) = goJ lib O c gul st R' t th) := by
  have h0 := h
  simp only [Comp.split] at h
  obtain ⟨o', g0, h0', h⟩ := bind_some h
  rw [emit_apply] at h0'
  simp only [Option.some.injEq, Prod.mk.injEq] at h0'
  obtain ⟨rfl, rfl⟩ := h0'
  obtain ⟨⟨sh, st⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  obtain ⟨-, E, eb', M1', M2', SP⟩ := split_ok h0
  obtain ⟨Dh', Dt', Dht', -, -⟩ := SP dn lo
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨eb, ed, er, eo, M1, M2, D, SB⟩ := splitNeed_spec h3
  replace eb : g2.bo = g.bo + 1 := eb
  have hn : NB (g.emitted ⟨[], [], Termin.hop th⟩).re laz.ned := fun r hr => by
    simp only [emitted_re]; exact lo r hr
  have W := wr_splitNeedS dn hn h3
  refine ⟨rfl, E, eb', M1', M2', ⟨Dh', Dt', Dht'⟩, fun c hc lib σ O st' t R a b gul ha hb => ?_⟩
  obtain ⟨A, Fr, Sm⟩ := SB hd
  obtain ⟨R', r1, hl', u⟩ := Sm dn lo lib σ O c gul st' t R a b ha hb
  have hg1 : HoonMap.get (g.emitted ⟨[], [], Termin.hop th⟩).blocks g.bo = some ⟨[], [], Termin.hop th⟩ :=
    emitted_get g _ hd
  have hg2 : HoonMap.get g2.blocks g.bo = some ⟨[], A ++ [], Termin.hop th⟩ := Fr.blk _ _ hg1
  have hb0 : HoonMap.get c.blocks g.bo = some ⟨[], A ++ [], Termin.hop th⟩ := by
    rw [hc g.bo (Nat.le_refl _) (by rw [eb]; omega)]
    exact hg2
  have WA : OpsWr (fun y => NMem laz.ned y ∧ ¬ NMem nh y ∧ ¬ NMem nt y) A := by
    rcases W g.bo _ hg2 with ⟨b, A', hb1, eqb, WA⟩ | WB
    · rw [hg1] at hb1
      simp only [Option.some.injEq] at hb1
      subst hb1
      simp only [Blob.mk.injEq, List.append_nil, true_and] at eqb
      rw [eqb.1]; exact WA
    · have := WB.2; simpa using this
  refine ⟨R', hl', fun y hy => ?_, ?_⟩
  · by_cases hm : NMem laz.ned y
    · have hy' : NMem nh y ∨ NMem nt y := by
        rcases hy with hy | hy
        · exact absurd hm hy
        · exact hy
      exact runs_read WA (fun hq => hy'.elim hq.2.1 hq.2.2) r1 (holdsN_some _ hl' hm)
    · exact u y hm
  · rw [goJ_jmp0 _ _ _ _ hb0, r1, execBlob_hop]

/-- **Cons for a fork-free `%next` with the relaxed `sem`.** -/
theorem consN_semR (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (sp : OKNR (S := S) (Map := Map) lib p)
    (sq : OKNR (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (hcount : sixCount (Nomm.cons p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    SemNR (Map := Map) lib (Nomm.cons p q) sur th g0 g1 nex := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hqp, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok hs2
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hok.1 hok.2
  obtain ⟨G2, eo', lt2, _⟩ := split_down hs2 hj.1 hj.2 d0
  simp only at eo'
  subst eo
  have CS := clean_split hs2 hcl
  simp only at CS
  have c2 : g2.cond = g0.cond := (kc_split _).keep _ _ _ hs2
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (G2.toU hu).up hu
  have lt2' : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y a) E2.1
    · exact a
  simp only [sixCount] at hcount
  have Rq := hq (sur := tel) (th := jmp0 g0.bo) ⟨b0, by simp only [jmp0]; omega⟩ rfl ⟨Dt, lt2' _ Mt⟩ CS.2
    (by omega) (by omega) d2 u2 h3
  have cl2 : Clear g2 := hcl0.growU (G2.toU hu)
  have Sq := sq (sur := tel) (th := jmp0 g0.bo) ⟨b0, by simp only [jmp0]; omega⟩ rfl ⟨Dt, lt2' _ Mt⟩ CS.2
    (by omega) (by omega) d2 u2 cl2 h3
  have d3 : g3.drop = false := Rq.ext.2.2.1.trans d2
  have u3 : UpBelow g3 := Rq.grow.up u2
  have Rp := hp (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) Rq.ext.1⟩ CS.1 (by omega)
    (by have := Rq.lo; have := Rq.hi; omega) d3 u3 h4
  have Sp := sp (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) Rq.ext.1⟩ CS.1 (by omega)
    (by have := Rq.lo; have := Rq.hi; omega) d3 u3 (cl2.growU Rq.grow) h4
  obtain ⟨-, -, -, -, -, -, BK⟩ := split_okK hs2 d0 hok.1 hok.2
  refine binaryN_semR (pureEval_cons p q) hok E2 Mh Mt Dht Rq Rp Sq Sp (cq CS.2 h3) (cp CS.1 h4) hcp d0
    (fun x y hn => Or.inr ⟨C x y, rfl, fun hf => ?_⟩)
    (fun c hc σ O st regs t gul x y fx fy hx hy => ?_)
  · rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  · refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := BK c hc lib σ O st t regs x y gul hx hy
    refine ⟨R', hl, fun r hr => u r ?_, e⟩
    rcases hr with ⟨_, k⟩ | k | k
    · exact Or.inl k
    · exact Or.inr (Or.inl k)
    · exact Or.inr (Or.inr k)

/-- **A unary case for a fork-free `%next` with the relaxed `sem`**, from
the relaxed `sem` of `p` and a block that keeps the operand register `a`
besides `Keep`. -/
theorem unaryN_semR {lib : Lib} {nm p : Nomm} {sur : Sure S} {th : Jmp} {g0 g' g1 : Gen Map} {a o : Nat}
    {nexp : NextL S} {f : Noun → Option Noun} (hev : ∀ s, pureEval nm s = (pureEval p s).bind f)
    (hpre : Ext g0 g') (ha : g0.re ≤ a ∧ a < g'.re) (hsur : ∀ r, NMem sur.ned r → r < g0.re)
    (hp : RunOKN (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (Sp : SemNR (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (O : Oracle σ) st regs t gul x,
      SkaModel.read a regs = some x →
      GoalSem lib O c gul st (fun r => Keep g0 g' (CGoal.next sur th) r ∨ r = a) regs t (jmp0 o)
        (CGoal.next sur th) (f x)) :
    SemNR (Map := Map) lib nm sur th g0 g1 nexp := by
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have hN : ∀ r, NMem ned r → g1.re ≤ r ∨ (r < g0.re ∧ ¬ NMem sur.ned r) ∨ NMem nexp.laz.sure.ned r := hned
  have l0 := hpre.1
  have l1 := hp.ext.1
  have agP : AgreeP lib O c gul st t ned g' g1 nexp.laz s0 s :=
    ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
  have inP : ∀ r, NMem ned r → InR (CGoal.next (lazyReg a : Sure S) (jmp0 o)) g' g1 nexp.laz.sure.ned r := by
    intro r hr
    show g1.re ≤ r ∨ (r < g'.re ∧ ¬ NMem (Need.this a) r) ∨ NMem nexp.laz.sure.ned r
    rcases hN r hr with e | ⟨e, _⟩ | e
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨by omega, fun hm => by simp only [NMem] at hm; omega⟩)
    · exact Or.inr (Or.inr e)
  have Hp := Sp c ned σ O st t gul s0 s agP inP regs hh hn
  have agQ : Agree c g0 g' := fun o' h0 h1 => by
    rw [ag.1 o' h0 (Nat.lt_of_lt_of_le h1 hp.ext.2.1) (fun hm => ?_)]
    · exact hp.ext.2.2.2 o' h1
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := (hp.labs e he).1; omega
  rw [hev]
  cases e : pureEval p s with
  | none => rw [e] at Hp; exact goalSem_none _ Hp
  | some x =>
    rw [e] at Hp
    obtain ⟨R, hR, k, he⟩ := Hp.1 ⟨trivial, looks_empty x⟩
    refine goalSem_pre (fun r hr => k r ?_) he _ _
      (goalSem_mono (fun r hr => ?_) _ _ (hblk c agQ σ O st R t gul x hR))
    · show (r < g'.re ∧ ¬ NMem (Need.this a) r) ∨ NMem ned r
      rcases hr with ⟨h1, _⟩ | h1
      · exact Or.inl ⟨by omega, fun hm => by simp only [NMem] at hm; omega⟩
      · exact Or.inr h1
    · show Keep g0 g' (CGoal.next sur th) r ∨ r = a
      have ngm : g'.re ≤ r → ¬ NMem sur.ned r := fun h1 h2 => by have := hsur r h2; omega
      rcases hr with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · rcases hN r h1 with e | ⟨e, e'⟩ | e
        · exact Or.inl ⟨Or.inr (by omega), ngm (by omega)⟩
        · exact Or.inl ⟨Or.inl e, e'⟩
        · rcases hp.regs r e with b | ⟨b, _⟩
          · simp only [lazyReg, NMem] at b; exact Or.inr b
          · exact Or.inl ⟨Or.inr b, ngm b⟩

/-- **`[7 p q]` with `q` a leaf, for a fork-free `%next`, with the relaxed
`sem`**: the relaxed `sem` of `p` and the leaf conversion of `q`
(`leaf_keepK`), composed by the two keep sets alone. -/
theorem runOKN_n7_semR (lib : Lib) {p q : Nomm} {sur : Sure S} {th : Jmp} (hq : Frag q (CGoal.next sur th))
    (hp : NextOK (S := S) (Map := Map) lib p) (sp : OKNR (S := S) (Map := Map) lib p) {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n7 p q) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g2)) :
    SemNR (Map := Map) lib (Nomm.n7 p q) sur th g0 g2 nex := by
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [show (CGoalL.next (ofSure sur) th : CGoalL S) = CGoal.toL (CGoal.next sur th) from rfl, runL_frag hq] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have Rq := run_ok lib q _ g0 g' n hq hok hcl hr
  have Dq := run_down (S := S) (Map := Map) q _ g0 g' n hj b0 d0 hr
  have dg : g'.drop = false := Rq.ext.2.2.1.trans d0
  have fa : n.th.args = [] := by
    rcases Dq.entry with ⟨_, _, _, fa⟩ | e
    · exact fa
    · simp only [GoalJ] at e; rw [e]; exact hth
  have hcl' : Clean n.laz.ned := run_clean q (CGoal.next sur th) g0 g' n hcl hr
  have hok' : GoalOK g' (CGoal.next n.laz n.th) := ⟨Rq.dist, fun r hr => by
    rcases Rq.regs r hr with h' | h'
    · exact Nat.lt_of_lt_of_le (hok.2 r h') Rq.ext.1
    · exact h'.2⟩
  have GQ : GrowU g0 g' := Dq.grow.toU hu
  have Rp := hp (sur := n.laz) (th := n.th) (region := region) (g0 := g') (g1 := g2) (nex := nex)
    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) h2
  have l1 := Rq.ext.1
  have l2 := Rp.ext.1
  have Sp' := sp (sur := n.laz) (th := n.th) (region := region) (g0 := g') (g1 := g2) (nex := nex)
    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) (hcl0.growU GQ) h2
  have Fq := run_foot (S := S) (Map := Map) q (CGoal.next sur th) g0 g' n d0 ⟨hok.2, jmpIn_nil hth⟩ hok.1 hr
  have l1 := Rq.ext.1
  have l2 := Rp.ext.1
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have hN : ∀ r, NMem ned r → g2.re ≤ r ∨ (r < g0.re ∧ ¬ NMem sur.ned r) ∨ NMem nex.laz.sure.ned r := hned
  have nq : ∀ r, r < g0.re → ¬ NMem sur.ned r → ¬ NMem n.laz.ned r := fun r h1 h2 hm => by
    rcases Rq.regs r hm with h' | h'
    · exact h2 h'
    · omega
  have agP : AgreeP lib O c gul st t ned g' g2 nex.laz s0 s :=
    ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans Rq.ext.2.1 h0) h1 hnl, ag.2⟩
  have inP : ∀ r, NMem ned r → InR (CGoal.next n.laz n.th) g' g2 nex.laz.sure.ned r := by
    intro r hr
    show g2.re ≤ r ∨ (r < g'.re ∧ ¬ NMem n.laz.ned r) ∨ NMem nex.laz.sure.ned r
    rcases hN r hr with e | ⟨e, e'⟩ | e
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨by omega, nq r e e'⟩)
    · exact Or.inr (Or.inr e)
  have Sp := Sp' c ned σ O st t gul s0 s agP inP regs hh hn
  have agQ : Agree c g0 g' := fun o h0 h1 => by
    rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 Rp.ext.2.1) (fun hm => ?_)]
    · exact Rp.ext.2.2.2 o h1
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := (Rp.labs e he).1; omega
  show GoalSem lib O c gul st _ regs t nex.th (CGoal.next sur th) (pureEval (Nomm.n7 p q) s)
  cases ev : pureEval p s with
  | none =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 p q) s = none := by simp [pureEval, ev]
    rw [e7]; exact goalSem_none _ Sp
  | some v =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 p q) s = pureEval q v := by simp [pureEval, ev]
    rw [e7]
    by_cases f : FitsS n.laz v
    · obtain ⟨R, hR, kR, e⟩ := Sp.1 f
      have Sq := leaf_keepK (O := O) (gul := gul) Rq Dq.grow Fq hcl0 d0 ⟨hth, hj.2⟩
        (K := KeepI (CGoal.next sur th) g0 ned) (fun r hr => by
          rcases hr with ⟨e1, e2⟩ | e1
          · exact Or.inl ⟨e1, e2⟩
          · rcases hN r e1 with e | ⟨e, e'⟩ | e
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inl ⟨e, e'⟩
            · rcases Rp.regs r e with b | ⟨b, _⟩
              · exact Or.inr (Or.inr b)
              · exact Or.inr (Or.inl b)) c agQ st v R t ⟨hR, f.2⟩
      refine goalSem_pre (fun r hr => kR r ?_) e _ _ Sq
      show (r < g'.re ∧ ¬ NMem n.laz.ned r) ∨ NMem ned r
      rcases hr with ⟨e1, e2⟩ | e1
      · exact Or.inl ⟨by omega, nq r e1 e2⟩
      · exact Or.inr e1
    · rcases Rq.nec v f with e' | ⟨w, e', x⟩
      · rw [e']; exact goalSem_none _ (Sp.2 f)
      · rw [e']; exact ⟨fun fw => absurd fw x, fun _ => Sp.2 f⟩

end Comp
end SkaModel
end Formalization
