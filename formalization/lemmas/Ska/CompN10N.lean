import lemmas.Ska.CompConsN
import lemmas.Ska.CompN10

/-!
# `[10 [a v] q]` whose operands have `%6` in them

`runOKN_n10`, `runOKP_n10D`, `runOKP_n10P`: the case `[10 [a v] q]` of
`runL` for a fork-free `%next`, for `%done` and for `%pick`, from `NextOK`
and `CleanN` of `v` and `q`, through `binaryN_ok`.  `+simple-next` makes a
`%done` or `%pick` goal `%next` of a register that a `%don` or `%brn` block
reads (`unaryG_ok`), `+into` splits the need of the edited noun into the
donor's and the recipient's (`into_ok`), the donor `v` is compiled first
into the `+into` block, then the recipient `q` into the block of `v`, then
`+copy`.  The code runs the recipient first, as `+mink` does.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The case `%10` of `runL` after `+simple-next`. -/
def n10Body (a : Nat) (v q : Nomm) (next : NextL S) (region : List Nat) : CM Map (NextL S) := do
  let (don, rec, o) ← intoL next a
  let nexR ← pastL noCode ⟨rec, jmp0 o⟩ v region
  let nexDon ← runL v (CGoalL.next don nexR.th) region
  let nexDon ← pastL noCode nexDon q region
  let nexRec ← runL q (CGoalL.next nexR.laz nexDon.th) region
  copyL nexRec nexDon.laz

theorem runL_n10_body (a : Nat) (v q : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runL (Nomm.n10 a v q) goal region : CM Map (NextL S)) = (do
      let next ← simpleNextL goal
      n10Body a v q next region) := by
  conv => lhs; unfold runL
  rfl

/-- **`%10` for a fork-free `%next`**, after `+simple-next`. -/
theorem n10N_body (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)
    (hq : NextOK (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)
    (hvp : v.pure = true) (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (hcount : sixCount (Nomm.n10 a v q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : n10Body a v q ⟨ofSure sur, th⟩ region g0 = some (nex, g1)) :
    RunOKN (Map := Map) lib (Nomm.n10 a v q) sur th g0 g1 nex := by
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
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
  have ID := into_down hs2 hj.1 hj.2 d0
  obtain ⟨a1, eo, E2, _, Md, Mr, Fe, SP⟩ := into_ok hs2
  subst eo
  obtain ⟨Dd, Dr, Ddr, F, B⟩ := SP hok.1 hok.2
  have CI := clean_into hs2 hcl
  have c2 : g2.cond = g0.cond := (kc_into _ _).keep _ _ _ hs2
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (ID.1.toU hu).up hu
  have lt2 : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with e | ⟨_, e⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y e) E2.1
    · exact e
  simp only [sixCount] at hcount
  have Rv := hv (sur := don) (th := jmp0 g0.bo) ⟨b0, by simp only [jmp0]; omega⟩ rfl ⟨Dd, lt2 _ Md⟩ CI.1
    (by omega) (by omega) d2 u2 h3
  have Rq := hq (sur := rec) (th := nexDon.th) ⟨Rv.lo, Rv.hi⟩ (nextArgs_nil Rv.ent rfl)
    ⟨Dr, fun y hy => Nat.lt_of_lt_of_le (lt2 _ Mr y hy) Rv.ext.1⟩ CI.2 (by omega)
    (by have := Rv.lo; have := Rv.hi; omega) (Rv.ext.2.2.1.trans d2) (Rv.grow.up u2) h4
  refine (binaryN_ok (pureEval_n10 (by omega) v q) hok E2 (ID.1.toU hu) c2 Mr Md (fun r hr hd => Ddr r hd hr)
    Rv Rq (cv CI.1 h3) (cq CI.2 h4) hcp hu d0 (by simp only [sixCount]; omega)
    (fun x y hn => ?_) (fun c hc σ O st regs t gul x y fx fy hx hy => ?_)).toN
  · cases e : edit? a y x with
    | none => exact Or.inl rfl
    | some n =>
      refine Or.inr ⟨n, rfl, fun hf => ?_⟩
      rcases hn with b | b
      · exact b ((F y x n e).mp hf).2
      · exact b ((F y x n e).mp hf).1
  · obtain ⟨n, e⟩ := Option.isSome_iff_exists.mp (Fe y x fx)
    rw [e]
    refine ⟨fun _ => ?_, fun hn => absurd ((F y x n e).mpr ⟨fy, fx⟩) hn⟩
    obtain ⟨R', hl, u, ej⟩ := B d0 c hc lib σ O st t regs y x n gul e hy hx
    exact ⟨R', hl, fun r ⟨k1, k2⟩ => u r k2 k1, ej⟩

/-- **`%10` for a fork-free `%next`.** -/
theorem runOKN_n10 (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)
    (hq : NextOK (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)
    (hvp : v.pure = true) (hqp : q.pure = true) : NextOK (S := S) (Map := Map) lib (Nomm.n10 a v q) :=
  fun hj _ hok hcl hcount b0 d0 hu h => by
    rw [runL_n10_body] at h
    obtain ⟨next, gs, hs, h⟩ := bind_some h
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact n10N_body lib hv hq cv cq hvp hqp hj hok hcl hcount b0 d0 hu h

/-- **`%10` for `%done`**: `%next` of a register that a `%don` block
returns. -/
theorem runOKP_n10D (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)
    (hq : NextOK (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)
    (hvp : v.pure = true) (hqp : q.pure = true) :
    OKP (Map := Map) lib (CGoal.done : CGoal S) (Nomm.n10 a v q) := by
  intro region g0 g1 nex _ _ hcount b0 d0 hu h
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  simp only [CGoal.toL, simpleNextL, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
    Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have G : Grow g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    (grow_re g0).trans (grow_emit (fun j hj => by simp [finJumps] at hj))
  have Hn := n10N_body lib hv hq cv cq hvp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)
    ⟨b0, by simp [jmp0, emitted_bo]⟩ ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial hcount (by simp [emitted_bo])
    (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  refine unaryG_ok (goal := CGoal.done) trivial (f := some) (fun s => by cases pureEval (Nomm.n10 a v q) s <;> rfl)
    ((ext_re _).trans (ext_emit _ _)) (G.toU hu) rfl ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d0) rfl rfl) Hn rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  show goJ lib O c gul st regs t (jmp0 _) = some (toneOf t (some x), st)
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_don', hx]; rfl

/-- **`%10` for `%pick`**: `%next` of a register that a `%brn` block
reads. -/
theorem runOKP_n10P (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)
    (hq : NextOK (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)
    (hvp : v.pure = true) (hqp : q.pure = true) (z o : Jmp) :
    OKP (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.n10 a v q) := by
  intro region g0 g1 nex _ hj hcount b0 d0 hu h
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  simp only [CGoal.toL, simpleNextL, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
    Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have G : Grow g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o⟩) :=
    (grow_re g0).trans (grow_emit (jumpsBelow_two rfl hj.1 hj.2))
  have Hn := n10N_body lib hv hq cv cq hvp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)
    ⟨b0, by simp [jmp0, emitted_bo]⟩ ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial hcount (by simp [emitted_bo])
    (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  refine unaryG_ok (goal := CGoal.pick z o) trivial (f := some)
    (fun s => by cases pureEval (Nomm.n10 a v q) s <;> rfl)
    ((ext_re _).trans (ext_emit _ _)) (G.toU hu) rfl ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d0) rfl rfl) Hn rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_brn, hx, Option.bind_some] at hj'
  by_cases x0 : x = A 0
  · subst x0
    exact ⟨regs, fun _ _ => rfl, by rw [hj']; simp⟩
  by_cases x1 : x = A 1
  · subst x1
    exact ⟨regs, fun _ _ => rfl, by rw [hj']; simp⟩
  exact goalSem_pick_other x0 x1 (by rw [hj']; simp [x0, x1])

end Comp
end SkaModel
end Formalization
