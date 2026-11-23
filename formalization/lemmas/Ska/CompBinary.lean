import lemmas.Ska.CompCopy

/-!
# Two operands: `%5` and cons

`binary_ok`: the shape of the cases `[5 p q]` and `[p q]` of `run`.  A block
`o` that takes the products of `p` and `q` from the registers of two needs
`lp` and `lq` and does for the goal what `f` of them asks; `q` compiled for
`[%next lq o]`, then `p` for `[%next lp then-of-q]`, then `+copy` of the two
needs of the subject.  At runtime the copy block fills both needs, the code
of `p` runs and keeps the registers of `q`'s need (they were allocated
before `p` was compiled and are not in `lp`), the code of `q` runs and keeps
those of `lp`, and the block `o` follows.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

/-- A crash where the value is none or has not what the goal asks. -/
theorem goalSem_crash_or {K : Nat → Prop} {regs : Map Noun} {t : Trace} {je : Jmp} {goal : CGoal S}
    {v : Option Noun} (hv : v = none ∨ ∃ w, v = some w ∧ GNot goal w)
    (h : goJ lib O c gul st regs t je = some (Tone.two t, st)) :
    GoalSem lib O c gul st K regs t je goal v := by
  rcases hv with rfl | ⟨w, rfl, hw⟩
  · exact goalSem_crash goal h
  · exact goalSem_not hw h

end

/-- **Two operands.** -/
theorem binary_ok {lib : Lib} {nm p q : Nomm} {goal : CGoal S} {g0 g' g1 g2 g3 : Gen Map}
    {lp lq : Sure S} {o : Nat} {nexq nexp nex : Next S} {f : Noun → Noun → Option Noun}
    (hev : ∀ s, pureEval nm s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => f x y)
    (hg : GoalOK g0 goal) (hpre : Ext g0 g')
    (hlp : ∀ r, NMem lp.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hq : RunOK lib q (CGoal.next lq (jmp0 o)) g' g1 nexq)
    (hp : RunOK lib p (CGoal.next lp nexq.th) g1 g2 nexp)
    (cq : Clean nexq.laz.ned) (cp : Clean nexp.laz.ned)
    (hc : copy nexp nexq.laz g2 = some (nex, g3))
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → f x y = none ∨ ∃ v, f x y = some v ∧ GNot goal v)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → g0.drop = false →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y → GoalSem lib O c gul st (Keep g0 goal) regs t (jmp0 o) goal (f x y)) :
    RunOK lib nm goal g0 g3 nex := by
  obtain ⟨EC, eth, _, CM, CS⟩ := copy_ok hc
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
  -- where the registers of the two needs of the subject are
  have mp : ∀ r, NMem nexp.laz.ned r → NMem lp.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := hp.regs
  have mq : ∀ r, NMem nexq.laz.ned r → NMem lq.ned r ∨ (g'.re ≤ r ∧ r < g1.re) := hq.regs
  have l1 := hq.ext.1
  have l2 := hp.ext.1
  have P : CopyPre nexp.laz.ned nexq.laz.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · rcases mp r h1 with a | ⟨a, _⟩ <;> rcases mq r h2 with b | ⟨b, b'⟩
      · exact hpq r a b
      · have := lpl r a; omega
      · have := lql r b; omega
      · omega
    · rcases hr with h | h
      · rcases mp r h with a | ⟨_, a⟩
        · have := lpl r a; omega
        · exact a
      · rcases mq r h with a | ⟨_, a⟩
        · have := lql r a; omega
        · omega
  obtain ⟨CD, CF, CB⟩ := CS P
  -- registers outside the goal and below `g0` are in neither need
  have outp : ∀ r, r < g0.re → ¬ GMem goal r → ¬ NMem lp.ned r := fun r h1 h2 hm => by
    rcases hlp r hm with h | ⟨h, _⟩
    · exact h2 h
    · omega
  have outq : ∀ r, r < g0.re → ¬ GMem goal r → ¬ NMem lq.ned r := fun r h1 h2 hm => by
    rcases hlq r hm with h | ⟨h, _⟩
    · exact h2 h
    · omega
  refine {
    ext := hpre.trans (hq.ext.trans (hp.ext.trans EC))
    regs := fun r hr => ?_
    nec := fun s hs => ?_
    dist := CD
    sem := fun hd c hag σ O st s regs t gul hh => ?_ }
  · have e3 := EC.1
    rcases CM r hr with h | h | ⟨h, h'⟩
    · rcases mp r h with a | ⟨a, a'⟩
      · rcases hlp r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by have := hpre.1; omega, by omega⟩
    · rcases mq r h with a | ⟨a, a'⟩
      · rcases hlq r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by have := hpre.1; omega, by omega⟩
    · exact Or.inr ⟨by have := hpre.1; omega, h'⟩
  · rw [hev]
    have hn : ¬ FitsS nexp.laz s ∨ ¬ FitsS nexq.laz s := by
      by_cases a : FitsS nexp.laz s
      · exact Or.inr fun b => hs ((CF s).mpr ⟨a, b⟩)
      · exact Or.inl a
    cases ep : pureEval p s with
    | none => exact Or.inl rfl
    | some x =>
      cases eq : pureEval q s with
      | none => exact Or.inl rfl
      | some y =>
        simp only [Option.bind_some]
        rcases hn with a | a
        · rcases hp.nec s a with e | ⟨x', e, hx⟩
          · rw [ep] at e; cases e
          · rw [ep] at e; cases e
            exact hnot x y (Or.inl hx)
        · rcases hq.nec s a with e | ⟨y', e, hy⟩
          · rw [eq] at e; cases e
          · rw [eq] at e; cases e
            exact hnot x y (Or.inr hy)
  · -- the copy block
    have hd2 : g2.drop = false := hp.ext.2.2.1.trans (hq.ext.2.2.1.trans (hpre.2.2.1.trans hd))
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB hd2 c (hag.right (hpre.trans (hq.ext.trans hp.ext))) lib σ O st
      regs t gul s hh
    have Hp := hp.sem (hq.ext.2.2.1.trans (hpre.2.2.1.trans hd)) c
      ((hag.right (hpre.trans hq.ext)).left hp.ext EC) σ O st s R1 t gul hs1
    -- the kept registers of the goal are in neither need of the subject
    have keep1 : ∀ r, Keep g0 goal r → SkaModel.read r R1 = SkaModel.read r regs := by
      intro r ⟨k1, k2⟩
      refine u1 r (fun hm => ?_) (fun hm => ?_)
      · rcases mp r hm with a | ⟨a, _⟩
        · exact outp r k1 k2 a
        · have := hpre.1; omega
      · rcases mq r hm with a | ⟨a, _⟩
        · exact outq r k1 k2 a
        · have := hpre.1; omega
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
        have hq2 : HoldsS nexq.laz R2 s := by
          refine ⟨HoldsN.agree _ (fun r hr => k2 r ⟨?_, ?_⟩) hs1'.1, hs1'.2⟩
          · rcases mq r hr with a | ⟨_, a⟩
            · have := lql r a; omega
            · exact a
          · intro hm
            rcases mq r hr with a | ⟨a, _⟩
            · exact hpq r hm a
            · have := lpl r hm; omega
        have Hq := hq.sem (hpre.2.2.1.trans hd) c ((hag.right hpre).left hq.ext (hp.ext.trans EC)) σ O st s R2
          t gul hq2
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
              HoldsN.agree _ (fun r hr => k3 r ⟨lpl r hr, hpq r hr⟩) hl2
            have B := hblk c (hag.left hpre (hq.ext.trans (hp.ext.trans EC))) hd σ O st R3 t gul x y fx fy hl3 hq3
            refine GoalSem.transfer (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans e3)) (fun r hk => ?_) B
            have ⟨k1, k2'⟩ := hk
            rw [k3 r ⟨Nat.lt_of_lt_of_le k1 hpre.1, outq r k1 k2'⟩,
              k2 r ⟨Nat.lt_of_lt_of_le k1 (Nat.le_trans hpre.1 hq.ext.1), outp r k1 k2'⟩, keep1 r hk]
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
