import lemmas.Ska.CompBinaryN

/-!
# Cons whose operands have `%6` in them

`runOKN_cons`, `runOKP_consD`, `runOKP_consP`: the case `[p q]` of `runL`
for a fork-free `%next` (after `+split`), for `%done` (which first turns the
goal into `%next` of a register that a `%don` block returns) and for `%pick`
(a cell as a loobean crashes, after both operands), from `NextOK` of `p` and
`q`, through `binaryN_ok`.  In every case both operands run for fork-free
`%next` goals whose jumps pass no arguments: `q` for the tail of the goal's
need and a fresh block, `p` for the head and the block `q` returns.

`binaryN_ok` needs the sure needs of the two runs clean (`CleanN`, which
`run_clean` gives for `run`); here it is a hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The sure need of a run for a fork-free `%next` with a clean need is
clean.** -/
abbrev CleanN (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean sur.ned → runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned

theorem nextArgs_nil {g : Gen Map} {sur : Sure S} {th j : Jmp} (h : Entry g (CGoal.next sur th) j)
    (hth : th.args = []) : j.args = [] := by
  rcases h with ⟨_, _, _, a⟩ | e
  · exact a
  · simp only [GoalJ] at e; rw [e]; exact hth

/-- **Cons for a fork-free `%next`**, the body after the goal is `%next`. -/
theorem consN_body (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (hcount : sixCount (Nomm.cons p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    RunOKN (Map := Map) lib (Nomm.cons p q) sur th g0 g1 nex := by
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
  have d3 : g3.drop = false := Rq.ext.2.2.1.trans d2
  have u3 : UpBelow g3 := Rq.grow.up u2
  have Rp := hp (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) Rq.ext.1⟩ CS.1 (by omega)
    (by have := Rq.lo; have := Rq.hi; omega) d3 u3 h4
  refine (binaryN_ok (pureEval_cons p q) hok E2 (G2.toU hu) c2 Mh Mt Dht Rq Rp (cq CS.2 h3) (cp CS.1 h4) hcp hu d0
    (by simp only [sixCount]; omega) (fun x y hn => Or.inr ⟨C x y, rfl, fun hf => ?_⟩)
    (fun c hc σ O st regs t gul x y fx fy hx hy => ?_)).toN
  · rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  · refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩

theorem runL_cons_next (p q : Nomm) (laz : Lazy S) (th : Jmp) (region : List Nat) :
    (runL (Nomm.cons p q) (CGoalL.next laz th) region : CM Map (NextL S)) = (do
      let (hed, tel, o) ← splitL ⟨laz, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz) := by
  conv => lhs; unfold runL
  rfl

/-- **Cons for a fork-free `%next`.** -/
theorem runOKN_cons (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) : NextOK (S := S) (Map := Map) lib (Nomm.cons p q) :=
  fun hj _ hok hcl hcount b0 d0 hu h => by
    rw [runL_cons_next] at h
    exact consN_body lib hp hq cp cq hpp hqp hj hok hcl hcount b0 d0 hu h

/-- **Cons for `%done`.** -/
theorem runOKP_consD (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) : OKP (Map := Map) lib (CGoal.done : CGoal S) (Nomm.cons p q) := by
  intro region g0 g1 nex _ _ hcount b0 d0 hu h
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
  refine unaryG_ok (goal := CGoal.done) trivial (f := some) (fun s => by cases pureEval (Nomm.cons p q) s <;> rfl)
    ((ext_re _).trans (ext_emit _ _)) (G.toU hu) rfl ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d0) rfl rfl) Hn rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  show goJ lib O c gul st regs t (jmp0 _) = some (toneOf t (some x), st)
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_don', hx]; rfl

/-- **Cons for `%pick`**: a cell is no loobean, the code crashes after both
operands. -/
theorem runOKP_consP (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (_hqp : q.pure = true) (z o : Jmp) :
    OKP (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.cons p q) := by
  intro region g0 g1 nex _ hj hcount b0 d0 hu h
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
  have Rq := hq (sur := Sure.bunt) (th := jmp0 g0.bo) ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by simp [emitted_bo]) d2 u2 h3
  have Rp := hp (sur := Sure.bunt) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by have := Rq.lo; have := Rq.hi; omega)
    (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) h4
  refine RunOKG.toP (goal := CGoal.pick z o) trivial (binaryN_ok (goal := CGoal.pick z o) (pureEval_cons p q)
    trivial (ext_emit _ _) (G.toU hu) rfl
    (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) Rq Rp
    (cq (sur := Sure.bunt) trivial h3) (cp (sur := Sure.bunt) trivial h4) h hu d0 (by simp only [sixCount]; omega)
    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_bunt x)) (fun a => a (fitsS_bunt y))) id) ?_)
  intro c hc σ O st regs t gul x y _ _ _ _
  have hb := emitted_get' d0 (hc _ (by simp) (by simp [emitted_bo]))
  show goJ lib O c gul st regs t (jmp0 g0.bo) = some (Tone.two t, st)
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_bom']

end Comp
end SkaModel
end Formalization
