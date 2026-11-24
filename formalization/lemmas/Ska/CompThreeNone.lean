import lemmas.Ska.CompSevenSame

/-!
# `[7 [3 p] q]` when the lazy need of `q` is equivalent to `none`

README Gaps 12.2, the branch of `[3 p]` that `finishLF_bellContract73X`
excludes with `hq3`.  When the run of `q` for `%done` returns a lazy need
equivalent to `none`, `runL` of `[3 p]` for it is `runL` of `p`
(`runL_n3_next`), so `[7 [3 p] q]` compiles as `[7 p q]`.  The two compute the
same: the code of `q` then reads nothing of its subject, so `q` has one
product for every subject (`pureEval_const_of_noneEq`, from `RunOKP.sem` of
`q` on the program of its own blocks, whose lazy blocks need no op: every
entry's need is equivalent to `none`, `noneEq_entries`).  So
`pureEval q (wut x) = pureEval q x`, and `RunOKU` of `[7 p q]` carries over
(`runOKU_seven3F`).

`finishLF_bellContract73F` replaces `hq3` by the alternative `hq3` or
`FragX [7 p q]`.  The second holds for `p = [0 axe]` with `2 ≤ axe`
(`FragX.sevenFrom`), so every `[7 [3 [0 axe]] q]` with `q` in `FragX` is
covered with no hypothesis on the run, for example
`[7 [3 [0 3]] [6 [1 0] [1 5] [1 6]]]` (`finishLF_bellContract_threeNone`), whose
`q` returns a lazy need equivalent to `none`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- An oracle that answers nothing: the program the constancy lemma runs
makes no call. -/
def nullOracle : Oracle Unit := ⟨fun _ _ _ _ _ _ => Option.none, fun _ _ _ _ => Option.none⟩

theorem toneOf_inj {t : Trace} {a b : Option Noun} (h : toneOf t a = toneOf t b) : a = b := by
  cases a <;> cases b <;> simp_all [toneOf]

/-- **A run for `%done` whose lazy need is equivalent to `none` has one
product for every subject.**  `RunOKP.sem` on the program made of the run's
own blocks, with the input need `none`: the lazy blocks need no op, since
every entry's need is equivalent to `none`, and every subject holds the sure
need with any registers, so the code from the empty register file returns
the tone of `pureEval q v` for every `v`. -/
theorem pureEval_const_of_noneEq {lib : Lib} {q : Nomm} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKP lib q CGoal.done g0 g1 nex) (hne : noneEquivalentL nex.laz = true) (v w : Noun) :
    pureEval q v = pureEval q w := by
  obtain ⟨hs, hl⟩ := noneEq_sure hne
  let c : Straight Map := ⟨NeedOrd.none, 0, g1.blocks⟩
  have ag : ∀ u, AgreeP lib nullOracle c (A 0) () [] Need.none g0 g1 nex.laz u u := fun u => by
    refine ⟨fun o _ _ _ => rfl, fun e he => ?_⟩
    obtain ⟨_, _, th, hb⟩ := R.labs e he
    obtain ⟨es, el⟩ := noneEq_sure (noneEq_entries nex.laz hne e he)
    refine ⟨[], th, hb, hb, fun Rg _ => ⟨fun _ => ⟨Rg, Runs.nil Rg, ⟨by rw [es]; trivial, looks_one el _⟩,
      fun _ _ _ => rfl⟩, fun nf => absurd ⟨by rw [es]; trivial, looks_one el _⟩ nf⟩⟩
  have G : ∀ u, goJ lib nullOracle c (A 0) () HoonMap.empty [] nex.th = some (toneOf [] (pureEval q u), ()) :=
    fun u => R.sem c Need.none Unit nullOracle () [] (A 0) u u (ag u) (fun r hr => absurd hr (by simp [NMem]))
      HoonMap.empty ⟨by rw [hs]; trivial, looks_one hl u⟩ trivial
  have e := (G v).symm.trans (G w)
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at e
  exact toneOf_inj e

/-- **`[7 [3 p] q]` for `%done` from `gen0` meets `RunOKU`** for every `q` in
`FragX`, given `RunOKU` of `[7 p q]` for the runs whose `q` returns a lazy
need equivalent to `none`: in that case `[3 p]` compiles as `p` and `q` has
one product, otherwise `runOKU_seven3`. -/
theorem runOKU_seven3F (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n3 p) q) ≤ 255)
    (h7 : ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nx, g1) →
      noneEquivalentL nx.laz = true → ∀ {nex : NextL S} {g2 : Gen Map},
      runL (Nomm.n7 p q) (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g2) →
      RunOKU (Map := Map) lib (Nomm.n7 p q) CGoal.done gen0 g2 nex)
    {g2 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n7 (Nomm.n3 p) q) (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g2)) :
    RunOKU (Map := Map) lib (Nomm.n7 (Nomm.n3 p) q) CGoal.done gen0 g2 nex := by
  have h' := h
  rw [runL_n7] at h'
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h'
  cases hne : noneEquivalentL nx.laz with
  | false =>
    exact runOKU_seven3 lib hp sp kp ap hq hcount (fun {nx'} {g1'} h1' => by
      rw [h1] at h1'; cases h1'; exact hne) h
  | true =>
    have hc : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
    have Rq := (runX_ok (Map := Map) lib hq).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
    have h2' : runL p (CGoalL.next nx.laz nx.th) [] g1 = some (nex, g2) := by
      have := h2
      rw [show nx.goal = CGoalL.next nx.laz nx.th from rfl, runL_n3_next, if_pos hne] at this
      exact this
    have e : runL (Nomm.n7 p q) (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g2) := by
      rw [runL_n7, bind_apply, h1]
      exact h2'
    refine (h7 h1 hne e).congr (fun s => ?_) (by simp only [sixCount])
    show (pureEval (Nomm.n3 p) s).bind (pureEval q) = (pureEval p s).bind (pureEval q)
    rw [pureEval_n3]
    cases pureEval p s with
    | none => rfl
    | some x => exact pureEval_const_of_noneEq Rq hne (wut x) x

/-- **The final pass meets the contract on `[7 [3 p] q]`** with `p` and `q`
in `FragX`, at most 255 `%6`, nothing baked and a cape with no `[| |]`, when
`[7 p q]` is in `FragX` or the run of `q` returns a lazy need not equivalent
to `none` (`hq3`).  The first holds for every `p = [0 axe]` with `2 ≤ axe`. -/
theorem finishLF_bellContract73F {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {p q : Nomm} (hp : (Nomm.n7 (Nomm.n3 p) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n3 p) q))
    (hfp : FragX (S := S) p) (hfq : FragX (S := S) q)
    (hor : FragX (S := S) (Nomm.n7 p q) ∨
      ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nx, g1) →
        noneEquivalentL nx.laz = false)
    (hcount : sixCount (Nomm.n7 (Nomm.n3 p) q) ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n3 p) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' := by
  refine finishLF_bellContractU hok hp hA (fun h1 => runOKU_seven3F lib (runX_ok lib hfp).2.1
    (runX_semR lib hfp).2.1 (runX_keeps hfp) (aboveX_of_fragX hfp) hfq hcount ?_ h1) hbl hn hbake h N
  intro nx g1 hq1 hne nex g2 h7
  rcases hor with hf7 | hq3
  · exact ((runX_ok (Map := Map) lib hf7).1 trivial trivial (by simp only [sixCount] at hcount ⊢; omega)
      (by simp [gen0]) rfl upBelow_gen0 h7).toU gen0_cond_none
  · rw [hq3 hq1] at hne; cases hne

/-- **`[7 [3 [0 3]] [6 [1 0] [1 5] [1 6]]]` meets the contract**, not covered
before: its `q` returns a lazy need equivalent to `none` (the test `[1 0]` for
`%pick` needs nothing and neither do the branches), so `hq3` fails, and
`[7 [0 3] q]` is in `FragX`. -/
theorem finishLF_bellContract_threeNone {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n3 (Nomm.n0 3)) (Nomm.n6 (Nomm.n1 (A 0)) (Nomm.n1 (A 5)) (Nomm.n1 (A 6)))))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n3 (Nomm.n0 3)) (Nomm.n6 (Nomm.n1 (A 0)) (Nomm.n1 (A 5)) (Nomm.n1 (A 6))))
      ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  have hq : FragX (S := S) (Nomm.n6 (Nomm.n1 (A 0)) (Nomm.n1 (A 5)) (Nomm.n1 (A 6))) :=
    FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)
  finishLF_bellContract73F hok rfl hA (FragX.frag fun _ => trivial) hq (Or.inl (FragX.sevenFrom (by decide) hq))
    (by decide) hbl hn hbake h N

end Comp
end SkaModel
end Formalization
