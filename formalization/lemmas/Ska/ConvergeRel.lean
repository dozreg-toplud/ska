import lemmas.Ska.ConvergeGraph
import lemmas.Ska.FolRel

/-!
# Agreement with `+mink` when the answers change during a run

`ConvergeGraph.lean` with each entry's last run in `FolR (AnswersS G)` (its
answers come from `G`, and the same call can be answered differently within
the run) instead of a run of the fixed-table model.  `ConvergedGraph` is the
special case (`ConvergedGraph.toR`), and so is `agree_poke`
(`agree_poke_of_fixed`).  The writes `GStepR` are `GStep` with a run whose
answers change; every write keeps the construction invariant (`GStepR.wf`).
-/

namespace Formalization
namespace SkaModel

open Nock

/-- **The entry written by the last run on its identity**, a run with
answers in `P`: its nomm and code requirement are the run's, and its product
is the merge of the run's with some older one. -/
def RunEntryR (P : Sock → Noun → TabEntry → Prop) (e : Entry) : Prop :=
  ∃ n out gen' moved old, FolTopR P n e.more e.fol out gen' ∧
    e.d.nomm = out.nomm ∧ e.d.less = Ca.app gen'.want e.more ∧
    (⟨e.d.prod, e.d.map⟩ : Anno) = mergeProd moved out.prod old

/-- **What the final graph gives**, with runs whose answers change: every
entry of `G` was written by a run whose every answer comes from `G`. -/
def ConvergedGraphR (G : Entry → Prop) : Prop := ∀ e, G e → RunEntryR (AnswersS G) e

theorem RunEntryM.toR {P : Sock → Noun → TabEntry → Prop} {tab : Tab} {e : Entry}
    (ht : TabIn P tab) (h : RunEntryM tab e) : RunEntryR P e := by
  obtain ⟨n, out, gen', moved, old, h1, h2, h3, h4⟩ := h
  exact ⟨n, out, gen', moved, old, folLoopF_folR ht n _ _ _ _ _ _ _ _ h1, h2, h3, h4⟩

/-- `ConvergedGraph` is the special case of runs with one table each. -/
theorem ConvergedGraph.toR {G : Entry → Prop} (h : ConvergedGraph G) : ConvergedGraphR G := by
  intro e he
  obtain ⟨tab, hans, hm⟩ := h e he
  exact hm.toR hans

theorem lessRel_of_graphR {G : Entry → Prop} (hG : ConvergedGraphR G) : LessRel G := by
  intro e lc dl he hl y hy
  obtain ⟨_, _, gen', _, _, _, _, hle, _⟩ := hG e he
  rw [hle] at hl ⊢
  exact app_cape_fits gen'.want e.more lc dl (some y) hl hy

theorem prodRelN_of_graphR {lib : Lib} {G : Entry → Prop} (hG : ConvergedGraphR G)
    (hwf : ∀ e, G e → WellFormed e.more) : ∀ K, ProdRelN lib G K := by
  have hL := lessRel_of_graphR hG
  intro K
  induction K with
  | zero => intro e _ y gul p _ hm; simp [minkF] at hm
  | succ K ih =>
    intro e he y gul p hy hm
    obtain ⟨n, out, gen', moved, old, h, _, hl, hpm⟩ := hG e he
    rw [hl] at hy
    have R := mergeProd_rel moved out.prod old
      (folTopR_relProdN (fun tab ht => rtabL_of_answers hL (answers_of_S ht))
        (fun tab ht => rtabP_of_answers ih (answers_of_S ht)) (hwf e he) h hy hm)
    rw [← hpm] at R
    exact R

theorem prodRel_of_graphR {lib : Lib} {G : Entry → Prop} (hG : ConvergedGraphR G)
    (hwf : ∀ e, G e → WellFormed e.more) : ProdRel lib G := by
  intro e he y gul p hy hm
  obtain ⟨n, hm⟩ := hm
  exact prodRelN_of_graphR hG hwf n e he y gul p hy hm

theorem codeOK_of_graphR {lib : Lib} {code : Bell → Option Nomm} {G : Entry → Prop}
    (hG : ConvergedGraphR G) (hc : CodeIs code G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more) : CodeOK lib code := by
  have hL := lessRel_of_graphR hG
  have hP := prodRel_of_graphR (lib := lib) hG hwf
  refine codeOK_of_entries hc fun e he => ?_
  obtain ⟨n, out, gen', _, _, h, hn, hl, _⟩ := hG e he
  rw [hn, hl]
  exact folTopR_wantSound (fun tab ht => rtab_of_answers hL hP hhas (answers_of_S ht)) (hwf e he) h

/-- **Agreement from the final graph, with runs whose answers change.** -/
theorem agree_converged_graphR {lib : Lib} {code : Bell → Option Nomm} {G : Entry → Prop}
    (hG : ConvergedGraphR G) (hc : CodeIs code G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more) {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x)
    (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r := by
  have hok := codeOK_of_graphR (lib := lib) hG hc hhas hwf
  obtain ⟨n, out, gen', _, _, h, hn, hl, _⟩ := hG e he
  have hL := lessRel_of_graphR hG
  have hP := prodRel_of_graphR (lib := lib) hG hwf
  rw [hl] at hx
  rw [hn]
  exact nomm_agree lib gul code hok
    (folTopR_wantSound (fun tab ht => rtab_of_answers hL hP hhas (answers_of_S ht)) (hwf e he) h) hx t r

/-! ## The writes, with runs whose answers change -/

/-- `GStep` with the run of `+run` in `FolR P`, for answers `P` with
well-formed products at well-formed subject socks. -/
inductive GStepR : Graph → Graph → Prop where
  | start {g : Graph} {i : Sock × Noun} : WellFormed i.1 → GStepR g (g.put i Datum.bunt)
  | run {g : Graph} {i : Sock × Noun} {P : Sock → Noun → TabEntry → Prop} {n : Nat} {out : FolOut}
      {gen' : Gen} {moved : Bool} {old : Datum} :
      (∀ tab, TabIn P tab → TabWF tab) → FolTopR P n i.1 i.2 out gen' → g i = some old →
      GStepR g (g.put i (runDatum moved i.1 out gen' old).1)
  | pop {g : Graph} {i : Sock × Noun} {d : Datum} : g i = some d →
      GStepR g (g.put i (if d.prod = Sock.void then { d with prod := Sock.dunno } else d))
  | cull {g : Graph} {i : Sock × Noun} : GStepR g (g.del i)
  | memo {g : Graph} {i : Sock × Noun} {d : Datum} : WellFormed i.1 → WellFormed d.prod →
      GStepR g (g.put i (patchDatum d i.1))

theorem gStepR_run_of_fixed {g : Graph} {i : Sock × Noun} {tab : Tab} {n : Nat} {out : FolOut}
    {gen' : Gen} {moved : Bool} {old : Datum} (htab : TabWF tab)
    (h : folLoopTop tab n i.1 i.2 = some (out, gen')) (ho : g i = some old) :
    GStepR g (g.put i (runDatum moved i.1 out gen' old).1) :=
  GStepR.run (P := fun s f a => tab s f = some a) (fun _ ht s f a hs h' => htab s f a hs (ht s f a h'))
    (folLoopF_folR (fun _ _ _ h => h) n _ _ _ _ _ _ _ _ h) ho

theorem GStep.toR {g g' : Graph} (h : GStep g g') : GStepR g g' := by
  cases h with
  | start hi => exact GStepR.start hi
  | run htab h ho => exact gStepR_run_of_fixed htab h ho
  | pop ho => exact GStepR.pop ho
  | cull => exact GStepR.cull
  | memo hi hd => exact GStepR.memo hi hd

/-- **Every write keeps the construction invariant.** -/
theorem GStepR.wf {g g' : Graph} (hs : GStepR g g') (hg : GraphWF g) : GraphWF g' := by
  cases hs with
  | start hi => exact graphWF_put hg hi wf_void
  | run htab h ho =>
    obtain ⟨hi, hd⟩ := hg _ _ ho
    exact graphWF_put hg hi (runDatum_wf (folTopR_wf htab hi h) hd)
  | pop ho =>
    obtain ⟨hi, hd⟩ := hg _ _ ho
    refine graphWF_put hg hi ?_
    split
    · exact wf_dunno
    · exact hd
  | cull =>
    intro j e hj
    unfold Graph.del at hj
    split at hj
    · cases hj
    · exact hg j e hj
  | memo hi hd => exact graphWF_put hg hi (wf_patchDatum hd hi)

/-- A sequence of writes. -/
inductive GStepsR : Graph → Graph → Prop where
  | refl (g : Graph) : GStepsR g g
  | tail {g g' g'' : Graph} : GStepsR g g' → GStepR g' g'' → GStepsR g g''

theorem graphWF_stepsR {g g' : Graph} (hs : GStepsR g g') (hg : GraphWF g) : GraphWF g' := by
  induction hs with
  | refl => exact hg
  | tail _ h ih => exact h.wf ih

theorem GSteps.toR {g g' : Graph} (h : GSteps g g') : GStepsR g g' := by
  induction h with
  | refl => exact GStepsR.refl _
  | tail _ h ih => exact ih.tail h.toR

/-- **Agreement for a poke, with runs whose answers change.**  As
`agree_poke`, with `ConvergedGraphR` and `GStepsR`. -/
theorem agree_pokeR {lib : Lib} {g : Graph} {G : Entry → Prop} {es : List Entry}
    (hs : GStepsR (fun _ => none) g) (hin : ∀ e, G e → ∃ d, g (e.more, e.fol) = some d)
    (hG : ConvergedGraphR G) (hes : ∀ e ∈ es, G e)
    (hbell : ∀ e, G e → ∃ e' ∈ es, e'.d.less = e.d.less ∧ e'.fol = e.fol)
    {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul (codeOf es) m t x e.d.nomm = some r := by
  have hgw := graphWF_stepsR hs graphWF_empty
  have hwf : ∀ e, G e → WellFormed e.more := fun e he => by
    obtain ⟨d, hd⟩ := hin e he
    exact (hgw _ _ hd).1
  have hc : CodeIs (codeOf es) G := fun bl nb h => by
    obtain ⟨e', he', hb, hn⟩ := codeOf_is es bl nb h
    exact ⟨e', hes e' he', hb, hn⟩
  have hhas : CodeHas (codeOf es) G := fun e he => by
    obtain ⟨e', he', hl, hf⟩ := hbell e he
    have := codeOf_has es e' he'
    rw [hl, hf] at this
    exact this
  exact agree_converged_graphR hG hc hhas hwf he hx gul t r

/-- `agree_poke` is the special case of runs with one table each. -/
theorem agree_poke_of_fixed {lib : Lib} {g : Graph} {G : Entry → Prop} {es : List Entry}
    (hs : GSteps (fun _ => none) g) (hin : ∀ e, G e → ∃ d, g (e.more, e.fol) = some d)
    (hG : ConvergedGraph G) (hes : ∀ e ∈ es, G e)
    (hbell : ∀ e, G e → ∃ e' ∈ es, e'.d.less = e.d.less ∧ e'.fol = e.fol)
    {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul (codeOf es) m t x e.d.nomm = some r :=
  agree_pokeR hs.toR hin hG.toR hes hbell he hx gul t r

end SkaModel
end Formalization
