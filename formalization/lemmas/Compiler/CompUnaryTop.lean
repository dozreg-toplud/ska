import lemmas.Compiler.CompUnaryEnd
import lemmas.Compiler.TreapList
import lemmas.Ska.CompWhole
import lemmas.Ska.CompCond

/-!
# `+compile-unary` from the entry to `+to-straight`

`+to-straight` (door arm `6892`, `comp_ts_at`, about 49 kB of Nock in its
gate `tsBat`) is not linked.  `TsAt` states its link on the branch the
fragment takes (`cond` empty, so `proxies` is `|`; the input `this+sub` is
the run `[sub]`, so `run` is `&`): on `[%next [[this+sub ~] ~ ~] ~ o]` it
returns the noun of `toStraightF` (`Straight.toNoun`: `[need nargs
blocks]`, the Hoon's `straight`).  `cond` is empty after `+kerf`
(`cu_cond_empty`, from `kc_run` and `cu_kern_cond`).  `cu_finish`: given
`TsAt`, the three calls of the trap's end (`+run`,
`+kerf`, `+to-straight`), each fed the product of the one before, return
the noun of `finishLU`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The arm `+to-straight`, read from the pill. -/
noncomputable def tsArm : Noun := (slot? 6892 comp.door).getD (A 0)

/-- The battery of its gate. -/
noncomputable def tsBat : Noun := (slot? 109 tsArm).getD (A 0)

/-- The bunt of its sample `next-resolved`. -/
def tsBunt : Noun :=
  C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))

theorem comp_ts_at : slot? 6892 comp.door = some tsArm := by kernel_rfl

theorem ts_arm_eq : tsArm = C (A 7) (C (C (A 8) (C (C (A 1) tsBunt) (C (C (A 1) tsBat) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x74686769617274732d6f742d706d6f63)
      (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))) := by kernel_rfl

/-- The arm `to-straight` builds its gate. -/
theorem comp_ts_arm (d : Noun) : nock d tsArm = some (C tsBat (C tsBunt d)) := by
  rw [ts_arm_eq]; simp only [nock_exec]

/-- The sample `[%next [[this+sub ~] ~ ~] ~ o]` of `+to-straight` in the
trap, from the nouns `O` and `SUB` that `+kerf` returns. -/
def tsSample (O SUB : Noun) : Noun :=
  C (A 0x7478656e) (C (C (C (C (A 0x73696874) SUB) (A 0)) (C (A 0) (A 0))) (C (A 0) O))

/-- **The link of `+to-straight`** on the branch of the fragment, stated:
with `cond` empty, the gate on `[%next [[this+sub ~] ~ ~] ~ o]` returns the
noun of `toStraightF`.  Not proved. -/
def TsAt (ctx : Noun) : Prop :=
  ∀ (g : Gen (TreapMap mugF)) (x : GenRest) (sub o : Nat), (∀ k, HoonMap.get g.cond k = Option.none) →
    nock (C tsBat (C (tsSample (A o) (A sub)) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks (Need.this sub) o).map Straight.toNoun

/-- `kern o (ofSure s)` keeps `cond` (the walk is at `o` only, so no
`+proxy`). -/
theorem cu_kern_cond (o : Nat) (s : Sure CSet) (g g' : Gen (TreapMap mugF)) (r : Nat)
    (h : kern o (Lazy.ofSure s) g = some (r, g')) : g'.cond = g.cond := by
  rw [kern_ofSure] at h
  have hm : KC ((do
      let ned ← sureRequireLook s
      if ned = Need.none then pure () else do
      let ops ← kernNeed g.re ned
      addOps o ops : CM (TreapMap mugF) Unit)) :=
    KC.bind' (kc_sureRequireLook s) fun ned => KC.ite' _ (KC.pure' _)
      (KC.bind' (by unfold kernNeed; exact kc_kernLoop _ _ _) fun ops => KC.addOps' o ops)
  split at h
  · cases h; rfl
  · obtain ⟨⟨u, g2⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    cases h2
    exact hm.keep { g with re := g.re + 1 } _ _ h1

/-- **`cond` is empty after `+run` and `+kerf`** from the entry state, for a
pure nomm with no `%6` (`kc_run`, `cu_kern_cond`). -/
theorem cu_cond_empty (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (o sub : Nat)
    (g2 : Gen (TreapMap mugF))
    (h : ((runL n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind fun p => kerf p.1 p.2)
      = some ((o, sub), g2)) : ∀ k, HoonMap.get g2.cond k = Option.none := by
  rw [runL_toL n hpu h6] at h
  obtain ⟨⟨nex', g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  cases e : run (S := CSet) (Map := TreapMap mugF) n CGoal.done genEntry with
  | none => simp [e, Functor.map, StateT.map] at h1
  | some q =>
    obtain ⟨nex, g0⟩ := q
    simp [e, Functor.map, StateT.map] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hc1 : g0.cond = genEntry.cond := (kc_run n CGoal.done).keep _ _ _ e
    simp only [kerf, bind, StateT.bind] at h2
    rw [cf_emit_g] at h2
    simp only [Option.bind_some] at h2
    obtain ⟨⟨r, g3⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h4
    obtain ⟨-, rfl⟩ := h4
    have hc3 := cu_kern_cond _ _ _ _ _ h3
    intro k
    rw [hc3, show (cfEmitG ⟨[], [], Termin.hop (Next.toL nex).th⟩ g0).cond = g0.cond by
      unfold cfEmitG; split <;> rfl, hc1]
    exact gen0_cond_none k

/-- **The end of `+compile-unary` from its entry state**: `+run`, `+kerf` on
its product, `+to-straight` on the product of `+kerf`, is the noun of
`finishLU`, for a pure nomm with no `%6` and `tenOk`, given the link of
`+to-straight` (`TsAt`); `cond` is empty after `+kerf` (`cu_cond_empty`). -/
theorem cu_finish (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (cache mono sup : Noun) (hts : TsAt ctx) :
    ((nock (crSubj mono n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) sup
        (compCore genEntry (cuRest cache) ctx)) crDol).bind (fun R =>
      (slot? 2 R).bind fun N => (slot? 3 R).bind fun G =>
        nock (C kerfBat (C N (C comp.door (C G ctx)))) kerfBat)).bind (fun K =>
      (slot? 4 K).bind fun O => (slot? 5 K).bind fun SUB => (slot? 3 K).bind fun G2 =>
        nock (C tsBat (C (tsSample O SUB) (C comp.door (C G2 ctx)))) tsBat)
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map Straight.toNoun := by
  rw [cu_run_kerf h7 hcode n hpu h6 ht cache mono sup]
  have hf : finishLU (S := CSet) (Map := TreapMap mugF) n
      = ((runL n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind fun p => kerf p.1 p.2).bind
          fun q => toStraightF q.2.cond q.2.blocks (Need.this q.1.2) q.1.1 := by
    rw [Option.bind_assoc]; rfl
  rw [hf]
  cases e : ((runL n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind fun p => kerf p.1 p.2) with
  | none => rfl
  | some q =>
    obtain ⟨⟨o, sub⟩, g2⟩ := q
    have h := hts g2 (cuRest cache) sub o (cu_cond_empty n hpu h6 o sub g2 e)
    simp only [compCore] at h
    simp only [Option.map_some, Option.bind_some]
    simp only [nock_exec, Option.bind_some]
    exact h

end Compiler
end Formalization
