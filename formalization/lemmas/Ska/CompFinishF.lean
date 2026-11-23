import lemmas.Ska.CompCond
import lemmas.Ska.CompStraightMap
import lemmas.Ska.CompSix

/-!
# The final pass with the whole of `+to-straight`

`finishLF` is `finishL` with `toStraightF`, the model of `+to-straight` that
tests for proxy registers and has the map path.  When the run leaves `cond`
empty and nothing is baked, `+to-straight` takes its renaming path, so
`finishLF` is `finishL` (`finishLF_eq`).  On the fragment `Frag6` the run
leaves `cond` empty (`runL_cond_frag6`), so the theorems proved of
`finishL` hold of `finishLF` (`finishLF_bellContract6`,
`six_crash_iffF`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The final pass of `member` in `+compile-scc-in`** for a function
alone in its SCC, as `finishL`, ending with the whole of `+to-straight`
on the proxy map the run left. -/
def finishLF [HoonMapKeys Map] (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runL nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyL nedFinal less nex.th.there nex.laz g2).bind fun (_, g3) =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
          toStraightF g4.cond g4.blocks bak.1 nex.th.there

/-- **When the run leaves no proxy and nothing is baked, the final pass
is `finishL`.** -/
theorem finishLF_eq [HoonMapKeys Map] {nm : Nomm} {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    (hrun : ∀ nex g1, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g1) →
      g1.cond = (gen0 : Gen Map).cond) :
    finishLF (S := S) (Map := Map) nm ord less bake = finishL (S := S) nm ord less bake := by
  unfold finishLF finishL
  cases h1 : runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) with
  | none => rfl
  | some p =>
    obtain ⟨nex, g1⟩ := p
    simp only [Option.bind_some]
    have c1 := hrun nex g1 h1
    split
    · rfl
    cases h2 : needOrdAllocRegs ord g1 with
    | none => rfl
    | some q =>
      obtain ⟨nedF, g2⟩ := q
      simp only [Option.bind_some, hbake, List.map_nil]
      have c2 := (kc_needOrdAllocRegs ord).keep g1 nedF g2 h2
      have hr := isRun_needOrdAllocRegs h2
      cases h3 : coerceLazyL nedF less nex.th.there nex.laz g2 with
      | none => rfl
      | some r =>
        obtain ⟨u, g3⟩ := r
        simp only [Option.bind_some]
        have c3 := (kc_coerceLazyL nedF less _ _).keep g2 u g3 h3
        cases h4 : addOps nex.th.there [] g3 with
        | none => rfl
        | some w =>
          obtain ⟨u4, g4⟩ := w
          simp only [Option.bind_some]
          have c4 := (KC.addOps' _ _).keep g3 u4 g4 h4
          apply toStraightF_eq _ hr
          intro k; rw [c4, c3, c2, c1]; exact HoonMap.get_empty k

theorem tagged_cond (g : Gen Map) (o : Nat) (region : List Nat) : (g.tagged o region).cond = g.cond := by
  unfold Gen.tagged; split <;> rfl

theorem emitted_cond (g : Gen Map) (b : Blob) : (g.emitted b).cond = g.cond := rfl

/-- **On `Frag6` the run makes no proxy register.** -/
theorem runL_cond_frag6 {nm : Nomm} (hf : Frag6 (S := S) nm) {g0 : Gen Map} {nex : NextL S} {g1 : Gen Map}
    (h : runL nm (CGoalL.done : CGoalL S) [] g0 = some (nex, g1)) : g1.cond = g0.cond := by
  rcases hf with hf | ⟨c, a, b, rfl, hc, ha, hb⟩
  · rw [show (CGoalL.done : CGoalL S) = CGoal.toL CGoal.done from rfl, runL_frag hf] at h
    obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    exact (kc_run nm CGoal.done).keep g0 n g hr
  · obtain ⟨n1, n0, nc, g1', g2, g3, hrb, hra, _, _, hrc, hadd, _⟩ := runL_six_done hc ha hb h
    rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond, (kc_run c _).keep _ _ _ hrc]
    simp only [sixGen, tagged_cond, emitted_cond]
    rw [(kc_run a _).keep _ _ _ hra, (kc_run b _).keep _ _ _ hrb]

/-- **The final pass with the whole of `+to-straight` meets the contract on
`Frag6`**, under the hypotheses of `finishL_bellContract6`. -/
theorem finishLF_bellContract6 [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : Frag6 (S := S) nm) {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' := by
  rw [finishLF_eq hbake (fun _ _ h1 => runL_cond_frag6 hf h1)] at h
  exact finishL_bellContract6 hok hp hA hf hbl hn hbake h N

/-- **The compiled `[6 c a b]` crashes exactly when the nomm does**, with
the whole of `+to-straight`. -/
theorem six_crash_iffF [HoonMapKeys Map] (lib : Lib) {c a b : Nomm}
    (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S)) (ha : Frag a (CGoal.done : CGoal S))
    (hb : Frag b (CGoal.done : CGoal S)) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n6 c a b) ord less bake = some c') {σ : Type} (O : Oracle σ) (st : σ)
    (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval (Nomm.n6 c a b) s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval (Nomm.n6 c a b) s = some v := by
  rw [finishLF_eq hbake (fun _ _ h1 => runL_cond_frag6 (Or.inr ⟨c, a, b, rfl, hc, ha, hb⟩) h1)] at h
  exact six_crash_iff lib hc ha hb hbake h O st s args t gul hP hsp

end Comp
end SkaModel
end Formalization
