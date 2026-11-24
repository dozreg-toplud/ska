import lemmas.Ska.CompN5N
import lemmas.Ska.CompN10N

/-!
# `FragX`: `FragM` with cons, `%5` and `%10`

`FragX`: the nomms of `FragM`, and cons `[p q]`, `[5 p q]` and
`[10 [a v] q]` of nomms of `FragX`, nested in any order with `%3`, `%4`,
`[7 p q]` (`q` in `Frag`) and `%6`, in the tests of `%6` too.  For example
`[[6 [0 2] [0 3] [0 1]] [0 1]]`, `[5 [6 [0 2] [1 0] [1 1]] [0 3]]` and
`[6 [[0 2] [6 [0 2] [1 0] [1 1]]] [0 2] [0 3]]` (a cons as a test, which
crashes) are in `FragX`.  Every `%next` goal that a `%6` of such a nomm
meets is fork-free: each operand of cons, `%5` and `%10` runs for a goal
`%next` whose need is a part of a fork-free need (`+split`, `+into`) or one
fresh register.

`runX_clean`: on `FragX` the sure need of every run for a goal whose need
is clean is clean (`CleanA`), which `binaryN_ok` needs of the operands of a
cons, a `%5` and a `%10`.  `runX_ok`: the run relations on `FragX` (the
cases `%5` and `%10` are `runOKG_n5` of `CompN5N.lean` and `runOKN_n10`,
`runOKP_n10D`, `runOKP_n10P` of `CompN10N.lean`), and the top theorems
`finishLF_bellContractX` and `crash_iffX`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Clean needs -/

/-- **Every run of `nm` for a goal with a clean need returns a clean sure
need.** -/
abbrev CleanA (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GClean goal → runL nm (CGoal.toL goal) region g0 = some (nex, g1) → Clean nex.laz.sure.ned

theorem CleanA.toN {nm : Nomm} (h : CleanA S Map nm) : CleanN S Map nm :=
  fun hc hr => h (goal := CGoal.next _ _) hc hr

theorem clean_copyL {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (h : copyL first second g = some (nex, g')) (ha : Clean first.laz.sure.ned) (hb : Clean second.sure.ned) :
    Clean nex.laz.sure.ned := by
  rcases first with ⟨⟨s1, f1, b1⟩, th⟩
  unfold copyL at h
  obtain ⟨o, g0, _, h⟩ := bind_some h
  obtain ⟨laz, g1, h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [copyLazyL] at h1
  obtain ⟨⟨ned, ops⟩, g2, h2, h1⟩ := bind_some h1
  obtain ⟨_, g3, _, h1⟩ := bind_some h1
  obtain ⟨_, g4, _, h1⟩ := bind_some h1
  obtain ⟨_, g5, _, h1⟩ := bind_some h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact clean_copyNeed _ _ _ _ _ _ h2 ha hb

theorem clean_lazyShut {o : Nat} {lz l : Lazy S} {g g' : Gen Map} (h : lazyShut o lz g = some (l, g'))
    (hc : Clean lz.sure.ned) : Clean l.sure.ned := by
  unfold lazyShut at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hc
  · obtain ⟨r, g1, _, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial

/-- The tail of the case `%6`: `+copy` of the test's need with the fork,
after `+lazy-shut` when the fork is big. -/
theorem clean_sixTail {xc : NextL S} {lz : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (h : (if !(lazyBig (softLess noSoft lz)) then copyL xc lz else do
      let o ← emit ⟨[], [], Termin.hop xc.th⟩
      let lazy ← lazyShut o lz
      copyL ⟨xc.laz, jmp0 o⟩ lazy : CM Map (NextL S)) g = some (nex, g'))
    (hx : Clean xc.laz.sure.ned) (hl : Clean lz.sure.ned) : Clean nex.laz.sure.ned := by
  split at h
  · exact clean_copyL h hx hl
  · obtain ⟨o, g1, _, h⟩ := bind_some h
    obtain ⟨l, g2, h2, h⟩ := bind_some h
    exact clean_copyL h hx (clean_lazyShut h2 hl)

theorem sect_sure {nex0 nex1 : NextL S} {o0 o1 : Nat} {rb : List Nat} {c0 c1 : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat} (h : sect nex0 nex1 o0 o1 rb c0 c1 g = some ((lz, yes, nuh), g')) :
    lz.sure = Sure.bunt := by
  unfold sect at h
  split at h
  · cases h
  · obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    dsimp only at h
    have tail : ∀ {x : Gen Map} {a b : Prop} [Decidable a] [Decidable b] {F : List (ForkE S)} {y n : Nat},
        (if a then (fun _ => Option.none : CM Map (Lazy S × Nat × Nat)) else
          if b then (fun _ => Option.none) else (pure (mk Sure.bunt F [], y, n) : CM Map (Lazy S × Nat × Nat))) x = some ((lz, yes, nuh), g') →
        lz.sure = Sure.bunt := by
      intro x a b _ _ F y n h
      revert h; split
      · intro h; cases h
      split
      · intro h; cases h
      intro h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      rfl
    split at h
    · exact tail h
    · obtain ⟨_, _, _, h⟩ := bind_some h
      exact tail h

/-- The case `%6` for `%done` and `%pick` keeps clean needs. -/
theorem clean_sixBody {c a b : Nomm} (hcp : c.pure = true)
    (ihc : ∀ {z o : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
      runL c (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1) → Clean nex.laz.sure.ned)
    {goal : CGoal S} (hg : NotNext goal) {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g1)) : Clean nex.laz.sure.ned := by
  rw [runL_n6_body _ _ _ hg] at h
  simp only [sixBody] at h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  revert h; split
  · intro h; cases h
  split
  · intro h; cases h
  intro h
  obtain ⟨lz', gP, hP, h⟩ := bind_some h
  simp only [liftO, pastFork_pure _ _ hcp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨xc, gC, hC, h⟩ := bind_some h
  exact clean_sixTail h (ihc hC) trivial

theorem runL_cons_done (p q : Nomm) (region : List Nat) :
    (runL (Nomm.cons p q) CGoalL.done region : CM Map (NextL S)) = (do
      let r ← re
      let o ← emit ⟨[], [], Termin.don r⟩
      runL (Nomm.cons p q) (CGoalL.next (ofSure (lazyReg r)) (jmp0 o)) region) := by
  simp only [runL_cons_next]
  conv => lhs; unfold runL
  rfl

theorem runL_cons_pick (p q : Nomm) (z o : Jmp) (region : List Nat) :
    (runL (Nomm.cons p q) (CGoalL.pick z o) region : CM Map (NextL S)) = (do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      let nex2 ← runL q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
      copyL nex1 nex2.laz) := by
  conv => lhs; unfold runL
  rfl

/-! ## The fragment -/

/-- **`FragM` with cons.** -/
inductive FragX : Nomm → Prop
  | frag {nm : Nomm} : (∀ goal : CGoal S, Frag nm goal) → FragX nm
  | six {c a b : Nomm} : FragX c → FragX a → FragX b → FragX (Nomm.n6 c a b)
  | four {p : Nomm} : FragX p → FragX (Nomm.n4 p)
  | three {p : Nomm} : FragX p → FragX (Nomm.n3 p)
  | seven {p q : Nomm} : (∀ goal : CGoal S, Frag q goal) → FragX p → FragX (Nomm.n7 p q)
  | cons {p q : Nomm} : FragX p → FragX q → FragX (Nomm.cons p q)
  | five {p q : Nomm} : FragX p → FragX q → FragX (Nomm.n5 p q)
  | ten {a : Nat} {v q : Nomm} : FragX v → FragX q → FragX (Nomm.n10 a v q)

theorem fragX_pure {nm : Nomm} (h : FragX (S := S) nm) : nm.pure = true := by
  induction h with
  | frag hf => exact (frag_pure_noSix _ _ (hf CGoal.done)).1
  | six _ _ _ ihc iha ihb => simp only [Nomm.pure, ihc, iha, ihb, Bool.and_self]
  | four _ ih => simpa only [Nomm.pure] using ih
  | three _ ih => simpa only [Nomm.pure] using ih
  | seven hq _ ih => simp only [Nomm.pure, ih, (frag_pure_noSix _ _ (hq CGoal.done)).1, Bool.and_self]
  | cons _ _ ihp ihq => simp only [Nomm.pure, ihp, ihq, Bool.and_self]
  | five _ _ ihp ihq => simp only [Nomm.pure, ihp, ihq, Bool.and_self]
  | ten _ _ ihv ihq => simp only [Nomm.pure, ihv, ihq, Bool.and_self]

theorem fragX_of_fragM {nm : Nomm} (h : FragM (S := S) nm) : FragX (S := S) nm := by
  induction h with
  | frag hf => exact FragX.frag hf
  | six _ _ _ ihc iha ihb => exact FragX.six ihc iha ihb
  | four _ ih => exact FragX.four ih
  | three _ ih => exact FragX.three ih
  | seven hq _ ih => exact FragX.seven hq ih

/-- The body of cons for `%next` keeps clean needs. -/
theorem clean_consBody {p q : Nomm} (cp : CleanA S Map p) (cq : CleanA S Map q) (hpp : p.pure = true)
    (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcl : Clean sur.ned)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : Clean nex.laz.sure.ned := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  have CS := clean_split hs2 hcl
  simp only at CS
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
  exact clean_copyL hcp (cp (goal := CGoal.next hed _) CS.1 h4) (cq (goal := CGoal.next tel _) CS.2 h3)

/-- The body of `%10` after `+simple-next` keeps clean needs. -/
theorem clean_n10Body {a : Nat} {v q : Nomm} (cv : CleanA S Map v) (cq : CleanA S Map q) (hvp : v.pure = true)
    (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcl : Clean sur.ned) (h : n10Body a v q ⟨ofSure sur, th⟩ region g0 = some (nex, g1)) :
    Clean nex.laz.sure.ned := by
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  have CI := clean_into hs2 hcl
  simp only at h CI
  obtain ⟨nexR, g2', hpr, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hvp, pure_apply] at hpr
  simp only [Option.some.injEq, Prod.mk.injEq] at hpr
  obtain ⟨rfl, rfl⟩ := hpr
  obtain ⟨nexDon, g3, h3, h⟩ := bind_some h
  obtain ⟨nexDon', g3', hpd, h⟩ := bind_some h
  rw [pastL_pure _ _ hqp, pure_apply] at hpd
  simp only [Option.some.injEq, Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  obtain ⟨nexRec, g4, h4, hcp⟩ := bind_some h
  exact clean_copyL hcp (cq (goal := CGoal.next rec _) CI.2 h4) (cv (goal := CGoal.next don _) CI.1 h3)

/-- **On `FragX` every run for a goal with a clean need returns a clean
sure need.** -/
theorem runX_clean {nm : Nomm} (hf : FragX (S := S) nm) : CleanA S Map nm := by
  induction hf with
  | frag hf =>
    intro goal region g0 g1 nex hc h
    rw [runL_frag (hf goal)] at h
    obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact run_clean _ goal _ _ n hc hr
  | @six c a b hc' _ _ ihc _ _ =>
    have hcp := fragX_pure hc'
    intro goal region g0 g1 nex hc h
    cases goal with
    | next sur th =>
      simp only [CGoal.toL] at h
      rw [runL_n6_next, sixNextL_ofSure] at h
      simp only [sixNextSimple] at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨⟨lz, yes, nuh⟩, gS, hS, h⟩ := bind_some h
      obtain ⟨lz', gP, hP, h⟩ := bind_some h
      simp only [liftO, pastFork_pure _ _ hcp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
      obtain ⟨rfl, rfl⟩ := hP
      obtain ⟨xc, gC, hC, h⟩ := bind_some h
      exact clean_sixTail h (ihc (goal := CGoal.pick _ _) trivial hC) (by rw [sect_sure hS]; trivial)
    | done => exact clean_sixBody (goal := CGoal.done) hcp (fun hC => ihc (goal := CGoal.pick _ _) trivial hC) trivial h
    | pick z o =>
      exact clean_sixBody (goal := CGoal.pick z o) hcp (fun hC => ihc (goal := CGoal.pick _ _) trivial hC) trivial h
  | four _ ih =>
    intro goal region g0 g1 nex hc h
    cases goal with
    | next sur th =>
      simp only [CGoal.toL] at h
      unfold runL at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨arg, _, _, h⟩ := bind_some h
      obtain ⟨o, _, _, h⟩ := bind_some h
      exact ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) trivial h
    | done =>
      simp only [CGoal.toL] at h
      unfold runL at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨arg, _, _, h⟩ := bind_some h
      obtain ⟨o, _, _, h⟩ := bind_some h
      exact ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) trivial h
    | pick z o =>
      simp only [CGoal.toL] at h
      unfold runL at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨arg, _, _, h⟩ := bind_some h
      obtain ⟨o, _, _, h⟩ := bind_some h
      exact ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) trivial h
  | three _ ih =>
    intro goal region g0 g1 nex hc h
    cases goal with
    | next sur th =>
      simp only [CGoal.toL] at h
      unfold runL at h
      dsimp only at h
      revert h; split
      · exact fun h => ih (goal := CGoal.next sur th) hc h
      intro h
      obtain ⟨a, _, _, h⟩ := bind_some h
      rcases a with _ | ⟨r, o⟩
      · cases h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨r', _, _, h⟩ := bind_some h
      obtain ⟨oc, _, _, h⟩ := bind_some h
      exact ih (goal := CGoal.next (lazyReg r') (jmp0 oc)) trivial h
    | done =>
      simp only [CGoal.toL] at h
      unfold runL at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨r, _, _, h⟩ := bind_some h
      obtain ⟨oc, _, _, h⟩ := bind_some h
      exact ih (goal := CGoal.next (lazyReg r) (jmp0 oc)) trivial h
    | pick z o =>
      simp only [CGoal.toL] at h
      unfold runL at h
      obtain ⟨r, _, _, h⟩ := bind_some h
      obtain ⟨oc, _, _, h⟩ := bind_some h
      exact ih (goal := CGoal.next (lazyReg r) (jmp0 oc)) trivial h
  | seven hq _ ih =>
    intro goal region g0 g1 nex hc h
    rw [runL_n7] at h
    obtain ⟨nx, g, h1, h2⟩ := bind_some h
    rw [runL_frag (hq goal)] at h1
    obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ih (goal := CGoal.next n.laz n.th) (run_clean _ goal _ _ n hc hr) h2
  | @cons p q hp' hq' ihp ihq =>
    have hpp := fragX_pure hp'
    have hqp := fragX_pure hq'
    intro goal region g0 g1 nex hc h
    cases goal with
    | next sur th =>
      simp only [CGoal.toL] at h
      rw [runL_cons_next] at h
      exact clean_consBody ihp ihq hpp hqp hc h
    | done =>
      simp only [CGoal.toL] at h
      rw [runL_cons_done] at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, h⟩ := bind_some h
      rw [runL_cons_next] at h
      exact clean_consBody (sur := lazyReg _) ihp ihq hpp hqp trivial h
    | pick z o =>
      simp only [CGoal.toL] at h
      rw [runL_cons_pick] at h
      obtain ⟨_, _, _, h⟩ := bind_some h
      obtain ⟨nex2, _, h3, h⟩ := bind_some h
      obtain ⟨nex2', _, hp2, h⟩ := bind_some h
      rw [pastL_pure _ _ hpp, pure_apply] at hp2
      simp only [Option.some.injEq, Prod.mk.injEq] at hp2
      obtain ⟨rfl, rfl⟩ := hp2
      obtain ⟨nex1, _, h4, h⟩ := bind_some h
      exact clean_copyL h (ihp (goal := CGoal.next Sure.bunt _) trivial h4)
        (ihq (goal := CGoal.next Sure.bunt _) trivial h3)
  | @five p q hp' _ ihp ihq =>
    have hpp := fragX_pure hp'
    intro goal region g0 g1 nex _ h
    rw [runL_n5_toL] at h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨nexq, _, h3, h⟩ := bind_some h
    obtain ⟨nexq', _, hp2, h⟩ := bind_some h
    rw [pastL_pure _ _ hpp, pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nexp, _, h4, h⟩ := bind_some h
    exact clean_copyL h (ihp (goal := CGoal.next (lazyReg _) _) trivial h4)
      (ihq (goal := CGoal.next (lazyReg _) _) trivial h3)
  | @ten a v q hv' hq' ihv ihq =>
    have hvp := fragX_pure hv'
    have hqp := fragX_pure hq'
    intro goal region g0 g1 nex hc h
    rw [runL_n10_body] at h
    obtain ⟨next, gs, hs, h⟩ := bind_some h
    have hn : ∃ (sur : Sure S) (th : Jmp), next = ⟨ofSure sur, th⟩ ∧ Clean sur.ned := by
      cases goal with
      | next sur th =>
        simp only [CGoal.toL, simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
        exact ⟨sur, th, hs.1.symm, hc⟩
      | done =>
        simp only [CGoal.toL, simpleNextL, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
          Option.some.injEq, Prod.mk.injEq] at hs
        exact ⟨lazyReg _, _, hs.1.symm, trivial⟩
      | pick z o =>
        simp only [CGoal.toL, simpleNextL, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
          Option.some.injEq, Prod.mk.injEq] at hs
        exact ⟨lazyReg _, _, hs.1.symm, trivial⟩
    obtain ⟨sur, th, rfl, hcl⟩ := hn
    exact clean_n10Body ihv ihq hvp hqp hcl h

/-! ## The run relations and the top theorems on `FragX` -/

/-- **`runL` meets the relations on `FragX`.** -/
theorem runX_ok (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) :
    OKP (Map := Map) lib (CGoal.done : CGoal S) nm ∧ NextOK (S := S) (Map := Map) lib nm ∧
    ∀ z o : Jmp, z.args = [] → o.args = [] → OKP (Map := Map) lib (CGoal.pick z o : CGoal S) nm := by
  induction hf with
  | frag hf =>
    exact ⟨fun hg hj _ b0 d0 hu h => runOKP_frag lib (hf _) hg hj b0 d0 hu h,
      fun hj _ hok hcl _ b0 d0 hu h => runOKN_frag lib (hf _) hj b0 d0 hu hok hcl h,
      fun _ _ _ _ _ _ _ _ hg hj _ b0 d0 hu h => runOKP_frag lib (hf _) hg hj b0 d0 hu h⟩
  | @six c a b hc _ _ ihc iha ihb =>
    have hcp := fragX_pure hc
    exact ⟨sixP_ok lib hcp ihc.2.2 iha.1 ihb.1,
      fun hj hth hok hcl hcount b0 d0 hu h => sixNext_okN lib hcp
        (fun z o hz ho => ihc.2.2 z o hz ho trivial) iha.2.1 ihb.2.1 hj hth hok hcl hcount b0 d0 hu h,
      fun z o hz ho => sixP_ok lib hcp ihc.2.2 (iha.2.2 z o hz ho) (ihb.2.2 z o hz ho)⟩
  | four _ ih =>
    exact ⟨fun _ _ hcount b0 d0 hu h => runOKP_n4 lib ih.2.1 (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun hj _ _ _ hcount b0 d0 hu h => runOKN_n4 lib ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun _ _ _ _ _ _ _ _ _ hj hcount b0 d0 hu h =>
        runOKP_n4p lib ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu h⟩
  | three _ ih =>
    exact ⟨fun _ _ hcount b0 d0 hu h => runOKP_n3 lib ih.2.1 (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun hj hth hok hcl hcount b0 d0 hu h =>
        runOKN_n3 lib ih.2.1 hj hth hok hcl (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun _ _ _ _ _ _ _ _ _ hj hcount b0 d0 hu h =>
        runOKP_n3p lib ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu h⟩
  | seven hq _ ih =>
    exact ⟨fun _ _ hcount b0 d0 hu h => runOKP_n7 lib (hq _) ih.2.1 (by simp only [sixCount] at hcount; omega)
        b0 d0 hu h,
      fun hj hth hok hcl hcount b0 d0 hu h => runOKN_n7 lib (hq _) ih.2.1 hj hth hok hcl
        (by simp only [sixCount] at hcount; omega) b0 d0 hu h,
      fun z o hz ho _ _ _ _ hg hj hcount b0 d0 hu h => runOKP_n7g lib hg (hq _) ih.2.1
        (fun j e => by simp only [GoalJ] at e; rcases e with rfl | rfl <;> assumption) hj
        (by simp only [sixCount] at hcount; omega) b0 d0 hu h⟩
  | @cons p q hp hq ihp ihq =>
    have cp : CleanN S Map p := CleanA.toN (runX_clean hp)
    have cq : CleanN S Map q := CleanA.toN (runX_clean hq)
    exact ⟨runOKP_consD lib ihp.2.1 ihq.2.1 cp cq (fragX_pure hp) (fragX_pure hq),
      runOKN_cons lib ihp.2.1 ihq.2.1 cp cq (fragX_pure hp) (fragX_pure hq),
      fun z o _ _ => runOKP_consP lib ihp.2.1 ihq.2.1 cp cq (fragX_pure hp) (fragX_pure hq) z o⟩
  | @five p q hp hq ihp ihq =>
    have cp : CleanN S Map p := CleanA.toN (runX_clean hp)
    have cq : CleanN S Map q := CleanA.toN (runX_clean hq)
    have hpp := fragX_pure hp
    exact ⟨fun hg hj hcount b0 d0 hu h =>
        (runOKG_n5 lib ihp.2.1 ihq.2.1 cp cq hpp (goal := CGoal.done) trivial hj hcount b0 d0 hu h).toP hg,
      fun hj _ hok _ hcount b0 d0 hu h =>
        (runOKG_n5 lib ihp.2.1 ihq.2.1 cp cq hpp (goal := CGoal.next _ _) hok hj hcount b0 d0 hu h).toN,
      fun _ _ _ _ _ _ _ _ hg hj hcount b0 d0 hu h =>
        (runOKG_n5 lib ihp.2.1 ihq.2.1 cp cq hpp (goal := CGoal.pick _ _) trivial hj hcount b0 d0 hu h).toP hg⟩
  | @ten a v q hv hq ihv ihq =>
    have cv : CleanN S Map v := CleanA.toN (runX_clean hv)
    have cq : CleanN S Map q := CleanA.toN (runX_clean hq)
    exact ⟨runOKP_n10D lib ihv.2.1 ihq.2.1 cv cq (fragX_pure hv) (fragX_pure hq),
      runOKN_n10 lib ihv.2.1 ihq.2.1 cv cq (fragX_pure hv) (fragX_pure hq),
      fun z o _ _ => runOKP_n10P lib ihv.2.1 ihq.2.1 cv cq (fragX_pure hv) (fragX_pure hq) z o⟩

/-- A cons whose head is a `%6`: `[[6 [0 2] [0 3] [0 1]] [0 1]]`. -/
example : FragX (S := S) (Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1)) :=
  FragX.cons (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial))
    (FragX.frag fun _ => trivial)

/-- A `%5` over a `%6`: `[5 [6 [0 2] [1 0] [1 1]] [0 3]]`. -/
example : FragX (S := S) (Nomm.n5 (Nomm.n6 (Nomm.n0 2) (Nomm.n1 (A 0)) (Nomm.n1 (A 1))) (Nomm.n0 3)) :=
  FragX.five (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial))
    (FragX.frag fun _ => trivial)

/-- A `%10` whose donor is a `%6`: `[10 [2 [6 [0 6] [0 7] [1 0]]] [0 1]]`. -/
example : FragX (S := S) (Nomm.n10 2 (Nomm.n6 (Nomm.n0 6) (Nomm.n0 7) (Nomm.n1 (A 0))) (Nomm.n0 1)) :=
  FragX.ten (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial))
    (FragX.frag fun _ => trivial)

/-- **The final pass meets the contract on `FragX`**, when the nomm has at
most 255 `%6`, nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishLF_bellContractX {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragX (S := S) nm) (hcount : sixCount nm ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractR hok hp hA
    (fun h1 => (runX_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h1) hbl hn hbake h N

/-- **The compiled code of a nomm of `FragX` crashes exactly when the nomm
does.** -/
theorem crash_iffX (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) (hcount : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) nm ord less bake = some c') {σ : Type} (O : Oracle σ) (st : σ)
    (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval nm s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval nm s = some v :=
  crash_iffR lib (fun h1 => (runX_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h1)
    hbake h O st s args t gul hP hsp

end Comp
end SkaModel
end Formalization
