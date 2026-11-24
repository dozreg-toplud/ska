import lemmas.Ska.CompRelUnary

/-!
# Cons under `%done` and `%pick`, and `[7 [0 axe] q]`, with the relaxed `sem`

README Gaps 12.2.  `consN_semRK`: cons under a fork-free `%next` in the form
`OKNR`.  `runOKP_consD_semR`: cons under `%done`, which first turns the goal
into `%next (lazyReg r)` of a fresh register `r` returned by a `%don` block,
through `unaryG_semR` with the identity as `f`.  `runOKP_consP_semR`: cons
under `%pick`, through `binaryN_semR` with the goal `%pick` and the block
`%bom` that crashes on a cell.  `semGR_from`, `semPR_from`: `[7 [0 axe] q]`
from the relaxed `sem` of `q`, as `runOKG_from` does for the strict one; the
sure need of the whole is `+from-sure` of `q`'s, whose registers are `q`'s
(`fromSure_spec`), so `InR` carries over.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Cons for a fork-free `%next` with the relaxed `sem`**, as `OKNR`. -/
theorem consN_semRK (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (sp : OKNR (S := S) (Map := Map) lib p)
    (sq : OKNR (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) : OKNR (S := S) (Map := Map) lib (Nomm.cons p q) :=
  fun hj _ hok hcl hcount b0 d0 hu hcl0 h => by
    rw [runL_cons_next] at h
    exact consN_semR lib hp hq sp sq cp cq hpp hqp hj hok hcl hcount b0 d0 hu hcl0 h

/-- **Cons for `%done` with the relaxed `sem`.** -/
theorem runOKP_consD_semR (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (sp : OKNR (S := S) (Map := Map) lib p)
    (sq : OKNR (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) :
    OKPR (Map := Map) lib (CGoal.done : CGoal S) (Nomm.cons p q) := by
  intro region g0 g1 nex _ _ _ hcount b0 d0 hu hcl0 h
  have e : (runL (Nomm.cons p q) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
      let r ← re
      let o ← emit ⟨[], [], Termin.don r⟩
      runL (Nomm.cons p q) (CGoalL.next (ofSure (lazyReg r)) (jmp0 o)) region) := by
    simp only [CGoal.toL, runL_cons_next]
    conv => lhs; unfold runL
    rfl
  rw [e] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G : Grow g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    (grow_re g0).trans (grow_emit (fun j hj => by simp [finJumps] at hj))
  have Hn := runOKN_cons lib hp hq cp cq hpp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)
    ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial hcount (by simp [emitted_bo])
    (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  have Sn := consN_semRK lib hp hq sp sq cp cq hpp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)
    ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial hcount (by simp [emitted_bo])
    (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) (hcl0.growU (G.toU hu)) h
  refine unaryG_semR (goal := CGoal.done) trivial (f := some) (fun s => by cases pureEval (Nomm.cons p q) s <;> rfl)
    ((ext_re _).trans (ext_emit _ _)) ⟨Nat.le_refl _, by simp [emitted_re]⟩ Hn Sn ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  show goJ lib O c gul st regs t (jmp0 _) = some (toneOf t (some x), st)
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_don', hx]; rfl

/-- **Cons for `%pick` with the relaxed `sem`**: a cell is no loobean, the
code crashes after both operands. -/
theorem runOKP_consP_semR (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (sp : OKNR (S := S) (Map := Map) lib p)
    (sq : OKNR (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (_hqp : q.pure = true) (z o : Jmp) :
    OKPR (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.cons p q) := by
  intro region g0 g1 nex _ hj _ hcount b0 d0 hu hcl0 h
  have e : (runL (Nomm.cons p q) (CGoal.toL (CGoal.pick z o : CGoal S)) region : CM Map (NextL S)) = (do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      let nex2 ← runL q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
      copyL nex1 nex2.laz) := by
    conv => lhs; unfold runL
    rfl
  rw [e] at h
  obtain ⟨o', g2, h2, h⟩ := bind_some h
  rw [emit_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  simp only [sixCount] at hcount
  have G : Grow g0 (g0.emitted ⟨[], [], Termin.bom Option.none⟩) := grow_emit (fun j hj => by simp [finJumps] at hj)
  have d2 : (g0.emitted ⟨[], [], Termin.bom Option.none⟩).drop = false := by simpa [emitted_drop] using d0
  have u2 := (G.toU hu).up hu
  have c2 : Clear (g0.emitted ⟨[], [], Termin.bom Option.none⟩) := hcl0.growU (G.toU hu)
  have Rq := hq (sur := Sure.bunt) (th := jmp0 g0.bo) ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by simp [emitted_bo]) d2 u2 h3
  have Sq := sq (sur := Sure.bunt) (th := jmp0 g0.bo) ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by simp [emitted_bo]) d2 u2 c2 h3
  have Rp := hp (sur := Sure.bunt) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by have := Rq.lo; have := Rq.hi; omega)
    (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) h4
  have Sp := sp (sur := Sure.bunt) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by have := Rq.lo; have := Rq.hi; omega)
    (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) (c2.growU Rq.grow) h4
  refine SemGR.toP (goal := CGoal.pick z o) trivial (binaryN_semR (goal := CGoal.pick z o) (pureEval_cons p q)
    trivial (ext_emit _ _)
    (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) Rq Rp Sq Sp
    (cq (sur := Sure.bunt) trivial h3) (cp (sur := Sure.bunt) trivial h4) h d0
    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_bunt x)) (fun a => a (fitsS_bunt y))) id) ?_)
  intro c hc σ O st regs t gul x y _ _ _ _
  have hb := emitted_get' d0 (hc _ (by simp) (by simp [emitted_bo]))
  show goJ lib O c gul st regs t (jmp0 g0.bo) = some (Tone.two t, st)
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_bom']

/-! ## `[7 [0 axe] q]` -/

/-- **`[7 [0 axe] q]` from `q` with the relaxed `sem`**, for any goal. -/
theorem semGR_from {lib : Lib} {axe : Nat} {q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nx : NextL S}
    {laz' : Lazy S} (hq : SemGR (Map := Map) lib q goal g0 g1 nx) (hf : fromL axe nx.laz = some laz') :
    SemGR (Map := Map) lib (Nomm.n7 (Nomm.n0 axe) q) goal g0 g1 ⟨laz', nx.th⟩ := by
  have hs := fromL_sure hf
  have E := fromL_ent axe _ _ hf
  obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hs
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
  have agQ : AgreeP lib O c gul st t ned g0 g1 nx.laz s0 s' := by
    refine ⟨fun o h0 h1 hnm => ag.1 o h0 h1 (by rw [E.map_fst]; exact hnm), fun e he => ?_⟩
    obtain ⟨l', hl', hm'⟩ := E.mem_left he
    obtain ⟨A, th, b1, b2, fs⟩ := ag.2 _ hm'
    exact ⟨A, th, b1, b2, fillSem_from (fromL_sure hl') hs1 fs⟩
  have H := hq c ned σ O st t gul s0 s' agQ (fun r hr => by
    rcases hned r hr with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (hmem r e))) regs hh' hn
  simp only [pureEval, hs1, Option.bind_some]
  exact H

/-- **`[7 [0 axe] q]` from `q` with the relaxed `sem`**, for `%done` and
`%pick`. -/
theorem semPR_from {lib : Lib} {axe : Nat} {q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nx : NextL S}
    {laz' : Lazy S} (hq : SemPR (Map := Map) lib q goal g0 g1 nx) (hf : fromL axe nx.laz = some laz') :
    SemPR (Map := Map) lib (Nomm.n7 (Nomm.n0 axe) q) goal g0 g1 ⟨laz', nx.th⟩ := by
  have hs := fromL_sure hf
  have E := fromL_ent axe _ _ hf
  obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hs
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
  have agQ : AgreeP lib O c gul st t ned g0 g1 nx.laz s0 s' := by
    refine ⟨fun o h0 h1 hnm => ag.1 o h0 h1 (by rw [E.map_fst]; exact hnm), fun e he => ?_⟩
    obtain ⟨l', hl', hm'⟩ := E.mem_left he
    obtain ⟨A, th, b1, b2, fs⟩ := ag.2 _ hm'
    exact ⟨A, th, b1, b2, fillSem_from (fromL_sure hl') hs1 fs⟩
  have H := hq c ned σ O st t gul s0 s' agQ (fun r hr => by
    rcases hned r hr with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (hmem r e))) regs hh' hn
  simp only [pureEval, hs1, Option.bind_some]
  exact H

end Comp
end SkaModel
end Formalization
