import lemmas.Ska.RunStep

/-!
# Agreement with `+mink` from the final graph of a poke

`agree_converged_graph`: `agree_at_convergence` with each entry's last run
taking its own table (the Hoon's runs read the graph at different times),
from `ConvergedGraph`.  `agree_poke` then takes the code table as
`+ska-poke` builds it (`codeOf`) and well-formed subject socks from the
construction invariant (`graphWF_steps`): its assumptions are convergence
(`ConvergedGraph`), that the entries of `G` are identities of the final
graph made by the writes of `+ska-callgraph` from the empty graph, and that
the code list holds the graph's bells.
-/

namespace Formalization
namespace SkaModel

open Nock

theorem lessRel_of_graph {G : Entry → Prop} (hG : ConvergedGraph G) : LessRel G := by
  intro e lc dl he hl y hy
  obtain ⟨_, _, _, _, gen', _, _, _, _, ⟨w, hle⟩, _⟩ := hG e he
  rw [hle] at hl ⊢
  exact app_cape_fits (Ca.uni gen'.want w) e.more lc dl (some y) hl hy

theorem answers_of_S {G : Entry → Prop} {tab : Tab}
    (hans : ∀ s f a, tab s f = some a → AnswersS G s f a) :
    ∀ s f a, tab s f = some a → Answers G s f a :=
  fun s f a h => (hans s f a h).toAnswers

/-- **`ProdRelN K` for every fuel `K`, from the final graph.** -/
theorem prodRelN_of_graph {lib : Lib} {G : Entry → Prop} (hG : ConvergedGraph G)
    (hwf : ∀ e, G e → WellFormed e.more) : ∀ K, ProdRelN lib G K := by
  have hL := lessRel_of_graph hG
  intro K
  induction K with
  | zero => intro e _ y gul p _ hm; simp [minkF] at hm
  | succ K ih =>
    intro e he y gul p hy hm
    obtain ⟨tab, hans, n, out, gen', moved, old, h, _, ⟨w, hl⟩, hpm⟩ := hG e he
    have hans' := answers_of_S hans
    rw [hl] at hy
    have R := mergeProd_rel moved out.prod old
      (folLoop_relProdN (rtabL_of_answers hL hans') (rtabP_of_answers ih hans') (hwf e he) h
        (fits_app_uni (hwf e he) hy) hm)
    rw [← hpm] at R
    exact R

theorem prodRel_of_graph {lib : Lib} {G : Entry → Prop} (hG : ConvergedGraph G)
    (hwf : ∀ e, G e → WellFormed e.more) : ProdRel lib G := by
  intro e he y gul p hy hm
  obtain ⟨n, hm⟩ := hm
  exact prodRelN_of_graph hG hwf n e he y gul p hy hm

/-- **`CodeOK` from the final graph.** -/
theorem codeOK_of_graph {lib : Lib} {code : Bell → Option Nomm} {G : Entry → Prop}
    (hG : ConvergedGraph G) (hc : CodeIs code G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more) : CodeOK lib code := by
  have hL := lessRel_of_graph hG
  have hP := prodRel_of_graph (lib := lib) hG hwf
  refine codeOK_of_entries hc fun e he => ?_
  obtain ⟨tab, hans, n, out, gen', _, _, h, hn, ⟨w, hl⟩, _⟩ := hG e he
  rw [hn, hl]
  exact (folLoop_wantSound (rtab_of_answers hL hP hhas (answers_of_S hans)) (hwf e he) h).mono
    (fun x hx => fits_app_uni (hwf e he) hx)

/-- **The analysis output of every entry of the final graph agrees with
`+mink` on every subject of its code requirement**, given convergence on
the graph (`hG`), the code table of the graph (`hc`, `hhas`), and
well-formed subject socks (`hwf`). -/
theorem agree_converged_graph {lib : Lib} {code : Bell → Option Nomm} {G : Entry → Prop}
    (hG : ConvergedGraph G) (hc : CodeIs code G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more) {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x)
    (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r := by
  have hok := codeOK_of_graph (lib := lib) hG hc hhas hwf
  obtain ⟨tab, hans, n, out, gen', _, _, h, hn, ⟨w, hl⟩, _⟩ := hG e he
  have hT := rtab_of_answers (lib := lib) (code := code) (lessRel_of_graph hG)
    (prodRel_of_graph hG hwf) hhas (answers_of_S hans)
  rw [hl] at hx
  rw [hn]
  exact nomm_agree lib gul code hok (folLoop_wantSound hT (hwf e he) h) (fits_app_uni (hwf e he) hx) t r

/-- **Agreement for a poke.**  The final graph `g` is made by the writes of
`+ska-callgraph` from the empty graph (`hs`), every entry of `G` is an
identity of `g` (`hin`), `G` is converged (`hG`), and the code table is
`codeOf es` for a list `es` of entries of `G` that has every bell of `G`
(`hes`, `hbell`).  Well-formedness of the subject socks is not assumed: it
is the construction invariant. -/
theorem agree_poke {lib : Lib} {g : Graph} {G : Entry → Prop} {es : List Entry}
    (hs : GSteps (fun _ => none) g) (hin : ∀ e, G e → ∃ d, g (e.more, e.fol) = some d)
    (hG : ConvergedGraph G) (hes : ∀ e ∈ es, G e)
    (hbell : ∀ e, G e → ∃ e' ∈ es, e'.d.less = e.d.less ∧ e'.fol = e.fol)
    {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul (codeOf es) m t x e.d.nomm = some r := by
  have hgw := graphWF_steps hs graphWF_empty
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
  exact agree_converged_graph hG hc hhas hwf he hx gul t r

end SkaModel
end Formalization
