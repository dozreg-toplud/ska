import lemmas.Compiler.CompRunSoftLift
import lemmas.Compiler.CompRunTNClass

/-! # The soft-free class at a rest predicate `Q` (README Gaps 19 (g))

The parts that run after the corpus's soft tail call (`SoftFree`: cons, `%0`, `%1`, `%7`, `%10`)
as `PartRTQ` links at any rest predicate `Qs` kept along `Y`, given the two leaves at `Qs`
(`LeafQ`: the cases `%0` and `%1` on every goal with `GInv`, at every `msup`).  With `Qs x :=
x.soft = softMapNoun sm` and `crxts_of_q` / `runLCS_lift` this is the soft shape.

* `softFree_nd`; **`comp_run_n7TQ`** (the copy of `comp_run_n7TN`); `LeafQ`;
* **`comp_run_softFreeQ`**: every `SoftFree` nomm is a `PartRTQ`;
* **`crxts_softFree`**: the soft-shape link `CompRunAtXTS (runLCS env snd msup)` of a `SoftFree`
  nomm on every goal with `GInv`, at the soft map `gs.soft`, from `LeafQ` at
  `x.soft = softMapNoun gs.soft` with a `Y` that keeps `soft`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

theorem softFree_nd : ∀ (n : Nomm), SoftFree n = true → NoDirect n
  | Nomm.cons p q, h => by
    simp only [SoftFree, Bool.and_eq_true] at h; exact ⟨softFree_nd p h.1, softFree_nd q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n7 p q, h => by
    simp only [SoftFree, Bool.and_eq_true] at h; exact ⟨softFree_nd p h.1, softFree_nd q h.2⟩
  | Nomm.n10 _ v q, h => by
    simp only [SoftFree, Bool.and_eq_true] at h; exact ⟨softFree_nd v h.1.2, softFree_nd q h.2⟩
  | Nomm.n2 _ _ _, h => by simp [SoftFree] at h
  | Nomm.n3 _, h => by simp [SoftFree] at h
  | Nomm.n4 _, h => by simp [SoftFree] at h
  | Nomm.n5 _ _, h => by simp [SoftFree] at h
  | Nomm.n6 _ _ _, h => by simp [SoftFree] at h
  | Nomm.n11s _ _ _, h => by simp [SoftFree] at h
  | Nomm.n11d _ _ _ _, h => by simp [SoftFree] at h
  | Nomm.n12 _ _, h => by simp [SoftFree] at h
  | Nomm.mean _ _ _ _ _, h => by simp [SoftFree] at h

/-- **The case `%7` at the rest predicate `Qs`** (`comp_run_n7TN` with `YOkQ`). -/
theorem comp_run_n7TQ {Qs : GenRest → Prop} {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop}
    (hYk : YOkQ Qs X Y) (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) {Xq : GenRest → Noun → Noun → Prop}
    (hq : CompRunAtXQ Qs (runLCM env false (some p)) ctx Xq Y q goal region g)
    (hXq : ∀ x mono sup, X x mono sup → Xq x mono (C (A 0) p.toNoun))
    (hp : ∀ nex g1, runLCM env false (some p) q goal region g = some (nex, g1) →
      CompRunAtXQ Qs (runLCM env false msup) ctx X Y p nex.goal region g1) :
    CompRunAtXQ Qs (runLCM env false msup) ctx X Y (Nomm.n7 p q) goal region g := by
  intro x mono sup hx hX
  obtain ⟨x1, hy1, h1⟩ := hq x mono (C (A 0) p.toNoun) hx (hXq x mono sup hX)
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runLCM (S := CSet) (Map := TreapMap mugF) env false (some p) q goal region g with
  | none =>
    rw [e] at h1
    refine ⟨x1, hy1, ?_⟩
    simp only [compCore]
    generalize comp.door = Dr at h1 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, runLCM, e, bind, StateT.bind]
  | some r =>
    obtain ⟨nex, g1⟩ := r
    rw [e] at h1
    obtain ⟨x2, hy2, h2⟩ := hp nex g1 e x1 mono sup (hYk.soft hx hy1) (hYk.pres hX hy1)
    refine ⟨x2, hYk.trans hy1 hy2, ?_⟩
    simp only [crSubj, compCore] at h2 h1
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, h2, runLCM, e, bind, StateT.bind]

/-- **The two leaves at the rest predicate `Qs`**: `%0` and `%1` on every goal with `GInv`, at
every `sup` (track K: `comp_run_n0_nextS` and `comp_run_n1_nextF` give the `%next` goals, the
latter under `WalkP (mdPF x k)`). -/
structure LeafQ (Qs : GenRest → Prop) (env : CallEnv) (ctx : Noun) (X : Option Nomm → GenRest → Noun → Noun → Prop)
    (Y : GenRest → GenRest → Prop) : Prop where
  n0 : ∀ msup ax region goal (g : Gen (TreapMap mugF)), GInv g goal →
    CompRunAtXQ Qs (runLCM env false msup) ctx (X msup) Y (Nomm.n0 ax) goal region g
  n1 : ∀ msup k region goal (g : Gen (TreapMap mugF)), GInv g goal →
    CompRunAtXQ Qs (runLCM env false msup) ctx (X msup) Y (Nomm.n1 k) goal region g

/-- **The soft-free class at `Qs`**: every `SoftFree` nomm is a `PartRTQ` (link at `Qs`, result,
`+past`), given the leaves (`LeafQ`) and `X msup` for the `sup` of each part (`XN E msup`'s shape:
`hXs` moves `X msup` to `X (some p)` under the `%7`). -/
theorem comp_run_softFreeQ (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (Qs : GenRest → Prop) (X : Option Nomm → GenRest → Noun → Noun → Prop) (Y : GenRest → GenRest → Prop)
    (hY : ∀ msup, YOkQ Qs (X msup) Y) (hXs : ∀ msup p x mono sup, X msup x mono sup → X (some p) x mono (C (A 0) p.toNoun))
    (L : LeafQ Qs env ctx X Y) :
    ∀ (n : Nomm), SoftFree n = true → ∀ (msup : Option Nomm) (region : List Nat), PartRTQ Qs env msup ctx (X msup) Y n region
  | Nomm.cons p q, h, msup, region => by
    have hnd := softFree_nd _ h
    simp only [SoftFree, Bool.and_eq_true] at h
    have P := comp_run_softFreeQ h7 hcode env Qs X Y hY hXs L p h.1 msup region
    have Q := comp_run_softFreeQ h7 hcode env Qs X Y hY hXs L q h.2 msup region
    exact ⟨fun goal g hi => comp_run_consLRTQ (hY msup) h7 hcode env msup p q P Q goal g hi, res_consRN P.res Q.res,
      pastAt_nd h7 hcode env.cod hnd⟩
  | Nomm.n0 ax, _, msup, region =>
    ⟨fun goal g hi => L.n0 msup ax region goal g hi, resR_of_resN rfl (res_n0 env msup ax region),
      pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n1 k, _, msup, region =>
    ⟨fun goal g hi => L.n1 msup k region goal g hi, resR_of_resN rfl (res_n1 env msup k region),
      pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n7 p q, h, msup, region => by
    have hnd := softFree_nd _ h
    simp only [SoftFree, Bool.and_eq_true] at h
    have P := comp_run_softFreeQ h7 hcode env Qs X Y hY hXs L p h.1 msup region
    have Q := comp_run_softFreeQ h7 hcode env Qs X Y hY hXs L q h.2 (some p) region
    exact ⟨fun goal g hi => comp_run_n7TQ (hY msup) env msup p q goal region g (Q.link goal g hi)
        (fun x mono sup hX => hXs msup p x mono sup hX)
        (fun nex g1 e => P.link nex.goal g1 (Q.res goal g g1 nex hi e).2.2.1),
      res_n7RN Q.res P.res, pastAt_nd h7 hcode env.cod hnd⟩
  | Nomm.n10 a v q, h, msup, region => by
    have hnd := softFree_nd _ h
    simp only [SoftFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have V := comp_run_softFreeQ h7 hcode env Qs X Y hY hXs L v h.1.2 msup region
    have Q := comp_run_softFreeQ h7 hcode env Qs X Y hY hXs L q h.2 msup region
    exact ⟨fun goal g hi => comp_run_n10LRTQ (hY msup) h7 hcode env msup a h.1.1 v q V Q goal g hi,
      res_n10RN h.1.1 V.res Q.res, pastAt_nd h7 hcode env.cod hnd⟩
  | Nomm.n2 _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n3 _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n4 _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n5 _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n6 _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n11s _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n12 _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [SoftFree] at h

/-- **The soft-shape link of a soft-free part**: at the soft map `gs.soft`, from the soft-free
class at `x.soft = softMapNoun gs.soft` with `Y` keeping `soft` (`crxts_of_q`, `runLCS_lift`). -/
theorem crxts_softFree (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (X : Option Nomm → GenRest → Noun → Noun → Prop)
    (Y : GenRest → GenRest → Prop) (gs : GenSf (TreapMap mugF))
    (hY : ∀ msup, YOkQ (fun x => x.soft = softMapNoun gs.soft) (X msup) (fun a c => Y a c ∧ c.soft = a.soft))
    (hXs : ∀ msup p x mono sup, X msup x mono sup → X (some p) x mono (C (A 0) p.toNoun))
    (L : LeafQ (fun x => x.soft = softMapNoun gs.soft) env ctx X (fun a c => Y a c ∧ c.soft = a.soft))
    (n : Nomm) (hn : SoftFree n = true) (msup : Option Nomm) (region : List Nat) (goal : CGoalL CSet)
    (hi : GInv gs.g goal) :
    CompRunAtXTS (runLCS env snd msup) ctx (X msup) Y n goal region gs :=
  crxts_of_q (R := runLCM env false msup) (by rw [runLCS_lift env snd n hn msup])
    ((comp_run_softFreeQ h7 hcode env _ X _ hY hXs L n hn msup region).link goal gs.g hi)

end Compiler
end Formalization
