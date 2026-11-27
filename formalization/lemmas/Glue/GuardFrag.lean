import lemmas.Glue.GuardArms

/-!
# `BlocksOK` kept by `run`, the first fragment (track G, step 2 of `GuardMonoX`)

**`run_kp`**: every run of `run` (`CompModel.lean`, the model of the first
fragment) for a goal whose jumps pass no `~` (`GJK`) keeps `BlocksOK` and
returns a jump that passes no `~`.  The cases are those of track D's
`run_at` (`RawInvAT.lean`), each a chain of the arms of `GuardArms.lean`
with the runs of the sub-nomms for goals whose jump is a `jmp0` or the
result of an earlier run.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **What the induction proves of one nomm.** -/
def RK (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] (nm : Nomm) : Prop :=
  ∀ goal : CGoal S, GJK goal → KP (fun n : Next S => JOK n.th) (run nm goal : CM Map (Next S))

/-- The tail of `%5`: `q` into the block `o`, `p` into `q`'s code, the copy. -/
theorem kp_fiveTail {p q : Nomm} (ihp : RK S Map p) (ihq : RK S Map q) (rp rq o : Nat) :
    KP (fun n : Next S => JOK n.th) (do
      let nexq ← run q (CGoal.next (lazyReg rq) (jmp0 o))
      let nexq ← past noCode nexq p
      let nexp ← run p (CGoal.next (lazyReg rp) nexq.th)
      copy nexp nexq.laz : CM Map (Next S)) := by
  refine KP.bind' (ihq _ (jok_jmp0 o)) fun nq hq => KP.bind' (kp_past _ _ _) fun nq' e => ?_
  subst e
  exact KP.bind' (ihp _ hq) fun np hp => kp_copy hp _

/-- The body of cons for a goal `%next`. -/
theorem kp_consBody {p q : Nomm} (ihp : RK S Map p) (ihq : RK S Map q) {laz : Sure S} {th : Jmp} (hth : JOK th) :
    KP (fun n : Next S => JOK n.th) (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh ← past noCode ⟨hed, jmp0 o⟩ q
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex2 ← past noCode nex2 p
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) := by
  refine KP.bind' (kp_split hth) fun x _ => ?_
  obtain ⟨hed, tel, o⟩ := x
  refine KP.bind' (kp_past _ _ _) fun nexh e => ?_
  subst e
  refine KP.bind' (ihq _ (jok_jmp0 o)) fun nex2 h2 => ?_
  refine KP.bind' (kp_past _ _ _) fun nex2' e => ?_
  subst e
  exact KP.bind' (ihp _ h2) fun nex1 h1 => kp_copy h1 _

theorem rk_n0 {ax : Nat} : RK S Map (Nomm.n0 ax) := by
  intro goal hg
  simp only [run]
  split
  · exact kp_bomb _
  · refine KP.bind' (kp_simpleNext hg) fun nex hn => ?_
    split
    · exact KP.pure' hn
    · split
      · exact KP.pure' hn
      · exact KP.fail

theorem rk_n1 {k : Noun} : RK S Map (Nomm.n1 k) := by
  intro goal hg
  cases goal with
  | done => simp only [run]; kpb
  | pick z o =>
    simp only [GJK] at hg
    simp only [run]
    split
    · exact KP.pure' hg.1
    · split
      · exact KP.pure' hg.2
      · exact kp_bomb _
  | next laz th =>
    simp only [run]
    exact KP.bind' (kp_mede hg _ _) fun _ _ => KP.pure' (jok_jmp0 _)

theorem rk_n7 {p q : Nomm} (ihp : RK S Map p) (ihq : RK S Map q) : RK S Map (Nomm.n7 p q) := by
  intro goal hg
  simp only [run]
  exact KP.bind' (ihq goal hg) fun nex hn => ihp _ hn

theorem rk_n4 {p : Nomm} (ih : RK S Map p) : RK S Map (Nomm.n4 p) := by
  intro goal hg
  cases goal with
  | done =>
    simp only [run]
    exact KP.bind' KP.re' fun _ _ => KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      ih _ (jok_jmp0 o)
  | pick z o =>
    simp only [GJK] at hg
    obtain ⟨hz, ho⟩ := hg
    simp only [run]
    exact KP.bind' KP.re' fun _ _ => KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      ih _ (jok_jmp0 o)
  | next laz th =>
    simp only [run]
    refine KP.bind' (kp_collapseLazyAtom (nex := ⟨laz, th⟩) hg) fun a _ => ?_
    refine KP.bind' (P := fun _ => True) ?_ fun x _ => ?_
    · split
      · exact KP.pure' trivial
      · exact KP.bind' KP.re' fun r _ => KP.ite' _ (KP.pure' trivial) KP.fail
    · obtain ⟨pro, th'⟩ := x
      exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ => ih _ (jok_jmp0 o)

theorem rk_n3 {p : Nomm} (ih : RK S Map p) : RK S Map (Nomm.n3 p) := by
  intro goal hg
  cases goal with
  | done =>
    simp only [run]
    refine KP.bind' kp_doneBlocks fun x _ => ?_
    obtain ⟨o0, o1⟩ := x
    exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ => ih _ (jok_jmp0 o)
  | pick z o =>
    simp only [GJK] at hg
    obtain ⟨hz, ho⟩ := hg
    simp only [run]
    exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ => ih _ (jok_jmp0 o)
  | next laz th =>
    simp only [run]
    refine KP.ite' _ (ih _ hg) ?_
    refine KP.bind' (kp_collapseLazyAtom (nex := ⟨laz, th⟩) hg) fun a _ => ?_
    split
    · exact KP.fail
    · refine KP.bind' (kp_forl _ _) fun x _ => ?_
      obtain ⟨z, o'⟩ := x
      exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ => ih _ (jok_jmp0 o)

theorem rk_n5 {p q : Nomm} (ihp : RK S Map p) (ihq : RK S Map q) : RK S Map (Nomm.n5 p q) := by
  intro goal hg
  cases goal with
  | pick z o =>
    simp only [GJK] at hg
    obtain ⟨hz, ho⟩ := hg
    simp only [run]
    exact KP.bind' KP.re' fun rp _ => KP.bind' KP.re' fun rq _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      kp_fiveTail ihp ihq rp rq o
  | done =>
    simp only [run]
    refine KP.bind' KP.re' fun rp _ => KP.bind' KP.re' fun rq _ => KP.bind' (P := fun _ => True) ?_ fun o _ =>
      kp_fiveTail ihp ihq rp rq o
    refine KP.bind' kp_doneBlocks fun x _ => ?_
    obtain ⟨o0, o1⟩ := x
    exact KP.emit' (by kpblk)
  | next laz th =>
    simp only [run]
    refine KP.bind' KP.re' fun rp _ => KP.bind' KP.re' fun rq _ => KP.bind' (P := fun _ => True) ?_ fun o _ =>
      kp_fiveTail ihp ihq rp rq o
    refine KP.bind' (kp_collapseLazyAtom (nex := ⟨laz, th⟩) hg) fun a _ => ?_
    split
    · exact KP.ite' _ (KP.emit' (by kpblk)) KP.fail
    · refine KP.bind' (kp_forl _ _) fun x _ => ?_
      obtain ⟨z, o'⟩ := x
      exact KP.emit' (by kpblk)

theorem rk_cons {p q : Nomm} (ihp : RK S Map p) (ihq : RK S Map q) : RK S Map (Nomm.cons p q) := by
  intro goal hg
  cases goal with
  | done =>
    simp only [run, bind_assoc, pure_bind]
    exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ => kp_consBody ihp ihq (jok_jmp0 o)
  | next laz th =>
    simp only [run, pure_bind]
    exact kp_consBody ihp ihq hg
  | pick z o =>
    simp only [run, pure_bind]
    refine KP.bind' (KP.emit' (by kpblk)) fun o _ => ?_
    refine KP.bind' (ihq _ (jok_jmp0 o)) fun nex2 h2 => ?_
    refine KP.bind' (kp_past _ _ _) fun nex2' e => ?_
    subst e
    exact KP.bind' (ihp _ h2) fun nex1 h1 => kp_copy h1 _

theorem rk_n10 {a : Nat} {v q : Nomm} (ihv : RK S Map v) (ihq : RK S Map q) : RK S Map (Nomm.n10 a v q) := by
  intro goal hg
  simp only [run]
  refine KP.bind' (kp_simpleNext hg) fun nex hn => ?_
  refine KP.bind' (kp_into hn a) fun x _ => ?_
  obtain ⟨don, rec, o⟩ := x
  refine KP.bind' (kp_past _ _ _) fun nexR e => ?_
  subst e
  refine KP.bind' (ihv _ (jok_jmp0 o)) fun nexDon hd => ?_
  refine KP.bind' (kp_past _ _ _) fun nexDon' e => ?_
  subst e
  exact KP.bind' (ihq _ hd) fun nexRec hr => kp_copy hr _

/-- **Every run of `run` for a goal whose jumps pass no `~` keeps
`BlocksOK` and returns a jump that passes no `~`.** -/
theorem run_kp : ∀ (nm : Nomm), RK S Map nm := by
  intro nm
  induction nm with
  | n0 ax => exact rk_n0
  | n1 k => exact rk_n1
  | n7 p q ihp ihq => exact rk_n7 ihp ihq
  | n4 p ih => exact rk_n4 ih
  | n3 p ih => exact rk_n3 ih
  | n5 p q ihp ihq => exact rk_n5 ihp ihq
  | cons p q ihp ihq => exact rk_cons ihp ihq
  | n10 a v q ihv ihq => exact rk_n10 ihv ihq
  | n2 => intro goal _; simp only [run]; exact KP.fail
  | n6 => intro goal _; simp only [run]; exact KP.fail
  | n11s => intro goal _; simp only [run]; exact KP.fail
  | n11d => intro goal _; simp only [run]; exact KP.fail
  | n12 => intro goal _; simp only [run]; exact KP.fail
  | mean => intro goal _; simp only [run]; exact KP.fail

end Glue
end SkaModel
end Formalization
