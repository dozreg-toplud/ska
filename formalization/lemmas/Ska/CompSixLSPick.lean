import lemmas.Ska.CompFourTop

/-!
# The test of `[6 c a b]` under `%pick`: the indirect call and `[0 axe]`

README Gaps 12.34, step 2.  Under `%done` and `%pick` the test of a `%6`
runs under `%pick (jmp0 yes) (jmp0 nuh)`.  The indirect call and `[0 axe]`
(`axe ≥ 1`) begin there with the block `[brn re z o]` of `+simple-next` and
run the rest under `%next (lazy-from-reg re)` into it (`runLC_pick_next`),
a flat goal with no entry, so their `LOKS` gives `RunOKGB` under `%pick`
(`runOKGB_pick`, the text of `runOKGB_done` with `goalSemCM_pick_of_next`;
`lokS_pick`, the text of `lokS_done`).

* `runLC_pick_next`, `runOKGB_pick`.
* `PickOK`: `DoneOK` for the goal `%pick z o`.
* `lokS_pick`: `LOKS` at that goal gives `PickOK`.
* `callTreeA_pickInd`, `callTreeA_pickN0`: the indirect call and `[0 axe]`
  (`axe ≥ 1`) of `CallTreeA` meet `PickOK`.
* `PickTree` (those two, and `[7 p q]` with `p` of index `true` in
  `CallTreeA` and `q` in `PickTree`), `pickTree_pick`: every test of
  `PickTree` meets `PickOK` under `%pick`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Under `%pick`, the indirect call and `[0 axe]` (`axe ≥ 1`) begin with
the block `[brn re z o]`**: the rest of the run is the run under `%next
(lazy-from-reg re)` into it. -/
theorem runLC_pick_next (env : CallEnv) (sup : Option Nomm) {nm : Nomm}
    (h : (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    (z o : Jmp) (region : List Nat) (g0 : Gen Map) :
    (runLC env sup nm (CGoalL.pick z o) region g0 : Option (NextL S × Gen Map)) =
      runLC env sup nm (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o⟩) := by
  rcases h with ⟨p, q, rfl⟩ | ⟨ax, ha, rfl⟩
  · simp only [runLC, callL, bind_apply]
    rw [simpleNextL_pick]
    simp only [Option.bind_some, simpleNextL, pure_apply]
  · have e : ax ≠ 0 := by omega
    simp only [runLC, e, if_false, bind_apply]
    rw [simpleNextL_pick]
    simp only [Option.bind_some, simpleNextL, pure_apply]

/-- The block `[brn re z o]` jumps below `bo`. -/
theorem jumpsBelow_brn {r bo : Nat} {z o : Jmp} (hj : GJ bo (CGoal.pick z o : CGoal S)) :
    JumpsBelow (Termin.brn r z o) bo := fun j hj' => by
  simp only [finJumps, List.mem_cons, List.mem_nil_iff, or_false] at hj'
  rcases hj' with rfl | rfl
  · exact hj.1
  · exact hj.2

/-- **`RunOKGB` under `%pick z o`** from the block `[brn re z o]` and the
run under `%next (lazy-from-reg re)` into it. -/
theorem runOKGB_pick {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {z o : Jmp} {g0 g' : Gen Map}
    {nex : NextL S} (hu : UpBelow g0) (hcb : CondBelow g0) (hj : GJ g0.bo (CGoal.pick z o : CGoal S))
    (ha : z.args = [] ∧ o.args = [])
    (hb : HoonMap.get g'.blocks g0.bo = some ⟨[], [], Termin.brn g0.re z o⟩)
    (R : RunOKGB lib N P f (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo))
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o⟩) g' nex) :
    RunOKGB lib N P f (CGoal.pick z o : CGoal S) g0 g' nex :=
  runOKGB_of_next (goal := CGoal.pick z o) trivial hu hcb (jumpsBelow_brn (S := S) hj) rfl hb
    (fun cf c0 => by
      simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0, renJmp_nil _ ha.1,
        renJmp_nil _ ha.2])
    (fun c σ O gul Inv ν K K' st regs t tm je r hK htr hbc H => goalSemCM_pick_of_next hK htr hbc H) R

/-- **What a run under `%pick z o` gives**: `DoneOK` for that goal. -/
structure PickOK (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (z o : Jmp) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop where
  run : RunOKGB lib N P f (CGoal.pick z o : CGoal S) g0 g1 nex
  nent : nex.th.there ∉ (entries nex.laz).map Prod.fst
  flat : Flat nex.laz
  clean : Clean nex.laz.sure.ned
  eclean : ∀ e ∈ entries nex.laz, Clean e.2.sure.ned

/-- **`LOKS` at the goal of `+simple-next` for `%pick`**: the run under
`%next (lazy-from-reg re)` into the block `[brn re z o]` meets every premise
of `LOKS.run` (a flat goal with no entry), so the run under `%pick z o` that
begins with that block meets `PickOK`. -/
theorem lokS_pick {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS (S := S) (Map := Map) x lib N env P f nm) (hcount : sixCount nm ≤ 255)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {z o : Jmp}
    (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (ha : z.args = [] ∧ o.args = [])
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup nm (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o⟩) = some (nex, g1)) :
    PickOK lib N P f z o g0 g1 nex := by
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.brn g0.re z o⟩)
      (jumpsBelow_brn (S := S) hj) hu
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := H.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 g0.bo)
    (region := region) hcount
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    b0 (by simp only [jmp0, Gen.emitted]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) hr
  have hb : HoonMap.get g1.blocks g0.bo = some ⟨[], [], Termin.brn g0.re z o⟩ := by
    rw [RS.keep _ (by simp only [Gen.emitted]; omega) (by rw [e0]; simp)]
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have RG := RS.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted]; omega)
  exact ⟨runOKGB_pick hu hcb hj ha hb RG, hne, hfl, H.clean (L := ofSure (lazyReg g0.re)) trivial hr, hec⟩

/-- **The indirect call of `CallTreeA` under `%pick` meets `PickOK`.** -/
theorem callTreeA_pickInd (lib : Lib) {N : Needs} (env : CallEnv) {b : Bool} {f : Noun} {p q : Nomm}
    (h : CallTreeA b f (Nomm.n2 p q Option.none)) (P : Noun → Prop)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {z o : Jmp}
    (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (ha : z.args = [] ∧ o.args = [])
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup (Nomm.n2 p q Option.none) (CGoalL.pick z o) region g0 = some (nex, g1)) :
    PickOK (S := S) (Map := Map) lib N P f z o g0 g1 nex := by
  cases h with
  | @ind b1 b2 b c p q hp hq =>
    have hc := CallTreeA.ind hp hq
    rw [runLC_pick_next env sup (Or.inl ⟨_, _, rfl⟩) z o region g0] at hr
    exact lokS_pick ((lokS_callTreeA (S := S) (Map := Map) lib (N := N) env hc P).2 rfl).1
      (by rw [hc.sixCount]; omega) hj ha b0 d0 hu hcl hcb hr

/-- **`[0 axe]` (`axe ≥ 1`) under `%pick` meets `PickOK`.** -/
theorem callTreeA_pickN0 (lib : Lib) {N : Needs} (env : CallEnv) {axe : Nat} (hax : 1 ≤ axe) (P : Noun → Prop)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {z o : Jmp}
    (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (ha : z.args = [] ∧ o.args = [])
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup (Nomm.n0 axe) (CGoalL.pick z o) region g0 = some (nex, g1)) :
    PickOK (S := S) (Map := Map) lib N P (slot axe) z o g0 g1 nex := by
  have hc := CallTreeA.n0 axe
  rw [runLC_pick_next env sup (Or.inr ⟨_, hax, rfl⟩) z o region g0] at hr
  exact lokS_pick ((lokS_callTreeA (S := S) (Map := Map) lib (N := N) env hc P).2 rfl).1
    (by rw [hc.sixCount]; omega) hj ha b0 d0 hu hcl hcb hr

/-- **The tests of the class that meet `PickOK`**: the indirect call and
`[0 axe]` (`axe ≥ 1`) of `CallTreeA`, and `[7 p q]` with `p` of index `true`
and `q` such a test. -/
inductive PickTree : Noun → Nomm → Prop
  | ind {b1 b2 : Bool} {b c : Noun} {p q : Nomm} : CallTreeA b1 b p → CallTreeA b2 c q →
      PickTree (n3 (A 2) b c) (Nomm.n2 p q Option.none)
  | n0 {axe : Nat} : 1 ≤ axe → PickTree (slot axe) (Nomm.n0 axe)
  | seven {b c : Noun} {p q : Nomm} : CallTreeA true b p → PickTree c q → PickTree (n3 (A 7) b c) (Nomm.n7 p q)

theorem PickTree.sixCount {f : Noun} {nm : Nomm} (h : PickTree f nm) : sixCount nm = 0 := by
  induction h with
  | ind hp hq => exact (CallTreeA.ind hp hq).sixCount
  | n0 _ => rfl
  | seven hp _ ihq => simp only [Comp.sixCount, hp.sixCount, ihq]

/-- **Every test of `PickTree` under `%pick z o` meets `PickOK`**: for `[7
p q]`, `q`'s `PickOK` (on the products of `p`) gives every premise of
`LOKS.run` for `p` at `q`'s result (the jump of `q` is a fresh block or `z`
or `o`, all without arguments), and `runOKGB_sevenL` composes, as in
`callTreeA_done`. -/
theorem pickTree_pick (lib : Lib) {N : Needs} (env : CallEnv) {f : Noun} {nm : Nomm} (h : PickTree f nm) :
    ∀ (P : Noun → Prop) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {z o : Jmp},
    GJ g0.bo (CGoal.pick z o : CGoal S) → z.args = [] ∧ o.args = [] →
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.pick z o) region g0 = some (nex, g1) → PickOK (S := S) (Map := Map) lib N P f z o g0 g1 nex := by
  induction h with
  | ind hp hq =>
    intro P sup region g0 g1 nex z o hj ha b0 d0 hu hcl hcb hr
    exact callTreeA_pickInd lib env (CallTreeA.ind hp hq) P hj ha b0 d0 hu hcl hcb hr
  | n0 hax =>
    intro P sup region g0 g1 nex z o hj ha b0 d0 hu hcl hcb hr
    exact callTreeA_pickN0 lib env hax P hj ha b0 d0 hu hcl hcb hr
  | @seven b c p q hp hq ihq =>
    intro P sup region g0 g1 nex z o hj ha b0 d0 hu hcl hcb hr
    rw [runLC_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ihq (Img lib P b) hj ha b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := ((lokS_callTreeA (S := S) (Map := Map) lib (N := N) env hp P).2 rfl).1
    have hjx : nx.th.args = [] := by
      rcases Rq.ent with ⟨_, _, _, ha'⟩ | e
      · exact ha'
      · rcases e with e | e
        · rw [e]; exact ha.1
        · rw [e]; exact ha.2
    obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
      (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
      (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hjx D.nent Rq.dist
      (fun x hx => ⟨by
        rcases Rq.regs x hx with e | e
        · exact e.elim
        · exact e.2, Rq.ncond x hx⟩)
      (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
      (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
      D.flat D.clean D.eclean h2
    exact ⟨runOKGB_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
      Lp.clean (L := nx.laz) D.clean h2, hec⟩

/-- `[7 [0 1] [2 [0 3] [0 2]]]`, an indirect call as the `q` of a `%7`, is a
test of `PickTree`; so is `[7 [2 [0 3] [0 2]] [0 2]]`. -/
example : PickTree (n3 (A 7) (slot 1) (n3 (A 2) (slot 3) (slot 2)))
    (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) :=
  PickTree.seven (CallTreeA.n0 1) (PickTree.ind (CallTreeA.n0 3) (CallTreeA.n0 2))
example : PickTree (n3 (A 7) (n3 (A 2) (slot 3) (slot 2)) (slot 2))
    (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2)) :=
  PickTree.seven (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2)) (PickTree.n0 (by omega))

end Comp
end SkaModel
end Formalization
