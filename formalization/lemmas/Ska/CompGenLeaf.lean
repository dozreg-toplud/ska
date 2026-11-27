import lemmas.Ska.CompGenTop

/-!
# The leaf `[0 axe]` in `RunOKGen`, at any lazy goal

README Gaps 12.39, item 6.  `[0 axe]` under `%next L th` puts no op and no
block: `+from` moves every entry's need under the axis at its own label
(`fromL_ent`, over the whole tree), and the run jumps to `th`.  At a goal
with repeated labels (`GoalG`: `LabDisj`, the entries' blocks
`[[] B [hop _]]`) the result keeps `LabDisj` (`FromEnt.labDisj`), and the
front of a label is the empty one: the fill of the conjunction of the moved
needs is the fill of the conjunction of the goal's (`fillSemL_from`).

* `FromEnt.pairsAt`, `FromEnt.labDisj`, `fillSemL_from`.
* `runOKGen_n0`: `RunOKGen` of `[0 axe]` at any `GoalG` goal whose
  registers are no keys of `cond`, with `pureWit`, `x = false`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The needs at one label, before and after `+from`**, paired. -/
theorem FromEnt.pairsAt {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) (o : Nat) :
    ∃ ps : List (Sure S × Sure S), ps.map Prod.fst = atL a o ∧ ps.map Prod.snd = atL b o ∧
      ∀ p ∈ ps, fromSure axe p.1 = some p.2 := by
  induction h with
  | nil => exact ⟨[], by simp [atL], by simp [atL], fun _ h => by simp at h⟩
  | @cons o' l l' a b hl _ ih =>
    obtain ⟨ps, h1, h2, h3⟩ := ih
    by_cases e : o' = o
    · refine ⟨(l.sure, l'.sure) :: ps, ?_, ?_, fun p hp => ?_⟩
      · simp only [List.map_cons, h1, atL, List.filter_cons, e, decide_true, ↓reduceIte]
      · simp only [List.map_cons, h2, atL, List.filter_cons, e, decide_true, ↓reduceIte]
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact fromL_sure hl
        · exact h3 p hp
    · refine ⟨ps, ?_, ?_, h3⟩
      · simp only [h1, atL, List.filter_cons, e, decide_false, Bool.false_eq_true, ↓reduceIte]
      · simp only [h2, atL, List.filter_cons, e, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- **`+from` keeps `LabDisj`**: the moved needs have fewer registers. -/
theorem FromEnt.labDisj {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b)
    (hfm : ∀ {s s' : Sure S}, fromSure axe s = some s' → ∀ r, NMem s'.ned r → NMem s.ned r)
    (hd : a.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r) :
    b.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons o l l' a b hl hab ih =>
    rw [List.pairwise_cons] at hd ⊢
    refine ⟨fun e' he' heq r h1 h2 => ?_, ih hd.2⟩
    obtain ⟨l0, hl0, hm0⟩ := hab.mem_right he'
    exact hd.1 (e'.1, l0) hm0 heq r (hfm (fromL_sure hl) r h1) (hfm (fromL_sure hl0) r h2)

/-- **The fill of the moved needs at a label is the fill of the needs**
(`fillSem_from` for a conjunction). -/
theorem fillSemL_from {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {lo axe : Nat} {ps : List (Sure S × Sure S)} {A : List Pole} {s0 s s' : Noun}
    (hp : ∀ p ∈ ps, fromSure axe p.1 = some p.2) (hs : slot? axe s = some s')
    (h : FillSemL lib O c gul st t ned lo (ps.map Prod.snd) A s0 s) :
    FillSemL lib O c gul st t ned lo (ps.map Prod.fst) A s0 s' := by
  intro R hR
  refine ⟨fun fL => ?_, fun ⟨L, hL, nL⟩ => (h R hR).2 ?_⟩
  · obtain ⟨R', r, hh, k⟩ := (h R hR).1 (fun L' hL' => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL'
      obtain ⟨_, _, hfit, _⟩ := fromSure_spec (Map := Map) (hp p hp')
      exact hfit s s' hs (fL p.1 (List.mem_map.mpr ⟨p, hp', rfl⟩)))
    refine ⟨R', r, fun L hL => ?_, fun x hx hn => k x hx (fun L' hL' hm => ?_)⟩
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL
      obtain ⟨_, hhold, _, _⟩ := fromSure_spec (Map := Map) (hp p hp')
      obtain ⟨q, hq, hh'⟩ := hhold R' s (hh p.2 (List.mem_map.mpr ⟨p, hp', rfl⟩))
      rw [hs] at hq; cases hq; exact hh'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL'
      obtain ⟨_, _, _, hmem⟩ := fromSure_spec (Map := Map) (hp p hp')
      exact hn p.1 (List.mem_map.mpr ⟨p, hp', rfl⟩) (hmem x hm)
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL
    refine ⟨p.2, List.mem_map.mpr ⟨p, hp', rfl⟩, fun f => nL ?_⟩
    obtain ⟨q, hq, fq⟩ := fromSure_fits (hp p hp') s f
    rw [hs] at hq; cases hq; exact fq

/-- **`[0 axe]` in `RunOKGen`, at any lazy goal** (forks, bonds, repeated
labels): no op, no block, every entry moved under the axis at its label. -/
theorem runOKGen_n0 (lib : Lib) {N : Needs} {P : Noun → Prop} {f : Noun} {axe : Nat} (M : MinkEq lib P f (Nomm.n0 axe))
    {L L' : Lazy S} {th : Jmp} {g : Gen Map} (hf : fromL axe L = some L') (G : GoalG (Map := Map) L th g)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g.cond r = Option.none) (W : Noun → Noun) :
    RunOKGen lib N P f L th (pureWit (Nomm.n0 axe) (fun _ => Need.none) W) false g g ⟨L', th⟩ := by
  have hs := fromL_sure hf
  have E := fromL_ent axe _ _ hf
  obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hs
  refine { re := Nat.le_refl _, bo := Nat.le_refl _, drop := rfl, keep := fun _ _ _ => rfl,
           grow := (GrowU.refl g).toG, cfr := CondFresh.refl g, lo := G.jmp.1, hi := G.jmp.2, ent := Or.inr rfl,
           regs := fun r hr => Or.inl (hmem r hr), dist := fromSure_dist hs G.dist,
           eregs := fun e he => ?_, labs := fun e he => ?_, labDisj := E.labDisj (fun h => (fromSure_spec (Map := Map) h).2.2.2) G.labDisj,
           dreg := fun s v d w r hq hr => ?_, ncond := fun r hr => hnc r (hmem r hr),
           econd := fun e he r hr => ?_, fronts := fun e he => Or.inl ⟨[], fun B fin hb => by simpa using hb⟩,
           nec := fun s hs' hf' => necC_of_pure M hs' ?_, front := ?_, sem := ?_, semB := ?_ }
  · obtain ⟨l, hl, hm⟩ := E.mem_right he
    have hls := fromL_sure hl
    obtain ⟨_, _, _, hmem'⟩ := fromSure_spec (Map := Map) hls
    exact ⟨fromSure_dist hls (G.eregs _ hm).1, fun r hr => Or.inl ⟨_, hm, hmem' r hr⟩⟩
  · obtain ⟨l, _, hm⟩ := E.mem_right he
    obtain ⟨_, _, blk⟩ := G.lab _ hm
    exact ⟨Or.inl (List.mem_map.mpr ⟨_, hm, rfl⟩), blk⟩
  · obtain ⟨_, rfl, _⟩ := hq
    exact hr.elim
  · obtain ⟨l, hl, hm⟩ := E.mem_right he
    obtain ⟨_, _, _, hmem'⟩ := fromSure_spec (Map := Map) (fromL_sure hl)
    exact hec _ hm r (hmem' r hr)
  · show pureEval (Nomm.n0 axe) s = none ∨ ∃ p, pureEval (Nomm.n0 axe) s = some p ∧ ¬ FitsS L.sure p
    simp only [pureEval]
    cases e : slot? axe s with
    | none => exact Or.inl rfl
    | some s' => exact Or.inr ⟨s', rfl, fun f => hf' (hfit s s' e f)⟩
  · intro a ha
    refine Or.inl ⟨[], fun B fin hb => by simpa using hb, fun cf _ => ?_⟩
    intro lib σ O c gul st t ned A s0 s v d w hn hq hA
    obtain ⟨hv, rfl, rfl⟩ := hq
    simp only [pureEval] at hv
    obtain ⟨ps, h1, h2, h3⟩ := E.pairsAt a
    have hA' : FillSemL lib O c gul st t ned g.re (ps.map Prod.snd) A s0 s := by rw [h2]; exact hA
    have F := fillSemL_from h3 hv hA'
    rw [h1] at F
    simp only [List.map_nil, List.append_nil]
    refine FillSemL.conv F (fun R hR => hR.1.1) (fun z hz => ?_)
    rcases hz with (hz | hz) | hz
    · exact Or.inl hz
    · exact hz.elim
    · exact hz.elim
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs' hm ag hned regs hh hn
    rw [(M s hs' gul tm r).mp ⟨n, hm⟩]
    refine goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩) ?_
    obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
    show GoalSemD lib O c gul st _ regs t th L.sure th Need.none (W s) (pureEval (Nomm.n0 axe) s)
    simp only [pureEval, hs1]
    exact ⟨fun _ => ⟨regs, hh'.1, trivial, fun _ _ => rfl, rfl⟩, fun nf => absurd (fitsS_of_holdsS hh') nf⟩
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs' ag hned regs hh hn res hres
    refine ⟨_, (M s hs' gul tm _).mpr rfl, goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩) ?_⟩
    obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
    show GoalSemD lib O c gul st _ regs t th L.sure th Need.none (W s) (pureEval (Nomm.n0 axe) s)
    simp only [pureEval, hs1]
    exact ⟨fun _ => ⟨regs, hh'.1, trivial, fun _ _ => rfl, rfl⟩, fun nf => absurd (fitsS_of_holdsS hh') nf⟩

end Comp
end SkaModel
end Formalization
