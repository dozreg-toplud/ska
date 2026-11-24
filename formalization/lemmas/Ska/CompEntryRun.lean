import lemmas.Ska.CompEntryGoal

/-!
# Runs for a goal whose need has entries: `%0` and `[7 p q]`

`RunOKE` (`CompEntryGoal.lean`) pairs each entry of the goal with the entry
of the result at the same label.  Here:

* `runOKE_n0`: the run of `[0 axe]` (`2 ≤ axe`) for such a goal is `+from`,
  which puts no op anywhere and moves each entry's need under `axe`
  (`FromEnt`), so every goal entry is paired with its moved self and `F = []`.
* `runOKG_sevenE`: `[7 p q]` from `RunOKG` of `q` (any fork-free goal) and
  `RunOKE` of `p` for the goal that the run of `q` returns, when `p` puts no
  op at the goal entries that stay in its result (`nf`).  The entries that
  `p` consumes may get ops (`F` alone fills them).
* `runOKG_from'`: `runOKG_from` of `CompFromRun.lean`, again, as the
  composition of the two.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`[0 axe]` for a goal with entries** (`2 ≤ axe`): `+from`, no op. -/
theorem runOKE_n0 (lib : Lib) {axe : Nat} {laz laz' : Lazy S} {th : Jmp} {g : Gen Map}
    (hf : fromL axe laz = some laz') (h1 : 1 ≤ th.there) (h2 : th.there < g.bo) (hd : Distinct laz.sure.ned)
    (hed : ∀ e ∈ entries laz, Distinct e.2.sure.ned) (hnd : ((entries laz).map Prod.fst).Nodup) :
    RunOKE (Map := Map) lib (Nomm.n0 axe) laz th g g ⟨laz', th⟩ := by
  have hs := fromL_sure hf
  have E := fromL_ent axe _ _ hf
  obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hs
  refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ _ => rfl, GrowU.refl g, rfl, h1, h2, Nat.le_refl _,
    Or.inr rfl, fun r hr => Or.inl (hmem r hr), fromSure_dist hs hd, fun e he => ?_, fun e he => ?_, ?_, ?_,
    fun e he => ?_, fun s hs' => ?_, fun c ned σ O st t gul s0 s _ _ regs hh _ => ?_⟩
  · obtain ⟨l, hl, hm⟩ := E.mem_right he
    have hls := fromL_sure hl
    obtain ⟨_, _, _, hmem'⟩ := fromSure_spec (Map := Map) hls
    exact ⟨fromSure_dist hls (hed _ hm), fun r hr => Or.inl ⟨_, hm, hmem' r hr⟩⟩
  · obtain ⟨l, _, hm⟩ := E.mem_right he
    exact Or.inl (List.mem_map.mpr ⟨_, hm, rfl⟩)
  · show ((entries laz').map Prod.fst).Nodup
    rw [E.map_fst]; exact hnd
  · show (entries laz').length ≤ (entries laz).length + 2 * sixCount (Nomm.n0 axe)
    rw [E.length_eq]; omega
  · obtain ⟨l', hl', hm'⟩ := E.mem_left he
    refine ⟨[], fun B fin hb => by simpa using hb, Or.inl ⟨l', hm', ?_⟩⟩
    intro lib σ O c gul st t ned A s0 s v _ hev hfill
    simp only [pureEval] at hev
    rw [List.append_nil]
    exact fillSem_from (fromL_sure hl') hev hfill
  · show pureEval (Nomm.n0 axe) s = none ∨ ∃ p, pureEval (Nomm.n0 axe) s = some p ∧ ¬ FitsS laz.sure p
    simp only [pureEval]
    cases e : slot? axe s with
    | none => exact Or.inl rfl
    | some s' => exact Or.inr ⟨s', rfl, fun f => hs' (hfit s s' e f)⟩
  · obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
    show GoalSem lib O c gul st _ regs t th (CGoal.next laz.sure th) (pureEval (Nomm.n0 axe) s)
    simp only [pureEval, hs1]
    exact ⟨fun _ => ⟨regs, hh'.1, fun _ _ => rfl, rfl⟩, fun nf => absurd (fitsS_of_holdsS hh') nf⟩

/-- The empty fill of the bunt. -/
theorem fillSem_bunt_nil {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {ned : Need} {lo : Nat} {s0 s : Noun} :
    FillSem (Map := Map) lib O c gul st t ned lo (Sure.bunt : Sure S) [] s0 s := fun R _ =>
  ⟨fun _ => ⟨R, Runs.nil R, holdsS_bunt R s, fun _ _ _ => rfl⟩, fun nf => absurd (fitsS_bunt s) nf⟩

/-- A product that misses the goal, after code that crashed. -/
theorem goalSem_gnot {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {K : Nat → Prop} {regs : Map (Option Noun)} {je : Jmp} :
    ∀ (goal : CGoal S) {w : Noun}, GNot goal w → goJ lib O c gul st regs t je = some (Tone.two t, st) →
      GoalSem lib O c gul st K regs t je goal (some w)
  | CGoal.next _ _, _, x, hc => ⟨fun h => absurd h x, fun _ => hc⟩
  | CGoal.pick _ _, _, x, _ => x.elim
  | CGoal.done, _, x, _ => x.elim

/-- **`[7 p q]` when `p` runs for a goal with entries**: `RunOKG` of `q` and
`RunOKE` of `p` for the goal the run of `q` returns give `RunOKG` of the
whole, when `p` leaves the blocks of the goal entries that stay in its
result as they were (`nf`).  `hgm`: the goal's registers were allocated
before the run (`GoalOK`). -/
theorem runOKG_sevenE {lib : Lib} {p q : Nomm} {goal : CGoal S} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (hq : RunOKG (Map := Map) lib q goal g0 g1 nx) (hp : RunOKE (Map := Map) lib p nx.laz nx.th g1 g2 nex)
    (hgm : ∀ r, GMem goal r → r < g0.re)
    (nf : ∀ e ∈ entries nx.laz, e.1 ∈ (entries nex.laz).map Prod.fst →
      HoonMap.get g2.blocks e.1 = HoonMap.get g1.blocks e.1) :
    RunOKG (Map := Map) lib (Nomm.n7 p q) goal g0 g2 nex := by
  have qlab : ∀ o, o ∈ (entries nx.laz).map Prod.fst → g0.bo ≤ o ∧ o < nx.th.there := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    exact ⟨(hq.labs e he).1, (hq.labs e he).2.1⟩
  have q1 := hq.ext.1
  have q2 := hq.ext.2.1
  have qhi := hq.hi
  refine ⟨⟨Nat.le_trans hq.ext.1 hp.re, Nat.le_trans hq.ext.2.1 hp.bo, hp.drop.trans hq.ext.2.2.1,
      fun o ho => ?_⟩, hq.grow.trans hp.grow, hp.cnd.trans hq.cnd, hp.lo, hp.hi, ?_, fun r hr => ?_, hp.dist,
    fun e he => ?_, fun e he => ?_, hp.nodup, ?_, fun s hs => ?_, ?_⟩
  · rw [hp.keep o (by omega) (fun hm => by have := (qlab o hm).1; omega)]
    exact hq.ext.2.2.2 o ho
  · rcases hp.ent with f | e
    · exact Or.inl f
    · rw [e]
      rcases hq.ent with f | e'
      · exact Or.inl (f.growU hq.hi hp.grow)
      · exact Or.inr e'
  · have := hp.re
    rcases hp.regs r hr with h | h
    · rcases hq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · refine ⟨(hp.eregs e he).1, fun r hr => ?_⟩
    have := hp.re
    rcases (hp.eregs e he).2 r hr with ⟨e0, he0, hm⟩ | h
    · have := (hq.eregs e0 he0).2 r hm; omega
    · omega
  · rcases hp.labs e he with hm | ⟨a, b, c⟩
    · obtain ⟨e0, he0, h0⟩ := List.mem_map.mp hm
      obtain ⟨x, y, th, hb⟩ := hq.labs e0 he0
      have := hp.thle
      refine ⟨by omega, by omega, th, ?_⟩
      rw [← h0, nf e0 he0 (by rw [h0]; exact List.mem_map.mpr ⟨e, he, rfl⟩), hb]
    · exact ⟨by have := hp.bo; omega, b, c⟩
  · show (entries nex.laz).length ≤ 2 * sixCount (Nomm.n7 p q)
    simp only [sixCount]; have := hp.size; have := hq.size; omega
  · rcases hp.nec s hs with e | ⟨v, e, nfv⟩
    · exact Or.inl (by simp [pureEval, e])
    · rcases hq.nec v nfv with e' | ⟨w, e'', x⟩
      · exact Or.inl (by simp [pureEval, e, e'])
      · exact Or.inr ⟨w, by simp [pureEval, e, e''], x⟩
  · intro c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeP lib O c gul st t ned g1 g2 nex.laz s0 s :=
      ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans q2 h0) h1 hnl, ag.2⟩
    have Sp := hp.sem c ned σ O st t gul s0 s agP hned regs hh hn
    show GoalSem lib O c gul st _ regs t nex.th goal (pureEval (Nomm.n7 p q) s)
    cases ev : pureEval p s with
    | none =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = none := by simp [pureEval, ev]
      rw [e7]; exact goalSem_none goal Sp
    | some v =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = pureEval q v := by simp [pureEval, ev]
      rw [e7]
      -- the relation of `q` holds for the subject `v`
      have agQ : AgreeP lib O c gul st t ned g0 g1 nx.laz s0 v := by
        refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
        · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', rfl⟩ := List.mem_map.mp hm
            rcases hp.labs e' he' with h | ⟨a, _, _⟩
            · exact hnl h
            · omega
          rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 hp.bo) hn2, hp.keep o h1 hnl]
        · obtain ⟨x, y, th, hb⟩ := hq.labs e he
          obtain ⟨F, hF, hFS⟩ := hp.front e he
          have hb2 := hF [] (Termin.hop th) hb
          rw [List.append_nil] at hb2
          rcases hFS with ⟨L', hm', fs⟩ | ⟨hnm, fs⟩
          · obtain ⟨A, th', h4, h9, sA⟩ := ag.2 _ hm'
            rw [hb2] at h4
            simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h4
            obtain ⟨rfl, rfl⟩ := h4
            refine ⟨A, th, hb, h9, ?_⟩
            have := fs lib σ O c gul st t ned A s0 s v hned ev sA
            rwa [List.append_nil] at this
          · refine ⟨F, th, hb, ?_, ?_⟩
            · rw [ag.1 e.1 x (by have := hp.bo; omega) hnm, hb2]
            · have := fs lib σ O c gul st t ned [] s0 s v hned ev fillSem_bunt_nil
              rwa [List.nil_append] at this
      by_cases f : FitsS nx.laz.sure v
      · obtain ⟨R, hR, kR, e⟩ := Sp.1 f
        have disj : ∀ r, NMem ned r → ¬ NMem nx.laz.sure.ned r := fun r hr hm => by
          have := hned r hr; have := hp.re
          rcases hq.regs r hm with h | h
          · have := hgm r h; omega
          · omega
        have hnR : HoldsN ned R s0 :=
          HoldsN.agree ned (fun r hr => kR r ⟨Or.inr hr, disj r hr⟩) hn
        have Sq := hq.sem c ned σ O st t gul s0 v agQ (fun r hr => Nat.le_trans hp.re (hned r hr)) R ⟨hR, f.2⟩ hnR
        refine goalSem_pre (fun r hr => kR r ⟨?_, ?_⟩) e goal _ Sq
        · rcases hr.1 with h | h
          · exact Or.inl (by omega)
          · exact Or.inr h
        · intro hm
          rcases hq.regs r hm with h | h
          · exact hr.2 h
          · rcases hr.1 with h' | h'
            · omega
            · have := hned r h'; have := hp.re; omega
      · rcases hq.nec v f with e' | ⟨w, e'', x⟩
        · rw [e']; exact goalSem_none goal (Sp.2 f)
        · rw [e'']; exact goalSem_gnot goal x (Sp.2 f)

/-- **`runOKG_from` again, as `[7 [0 axe] q]` through `RunOKE`.** -/
theorem runOKG_from' {lib : Lib} {axe : Nat} {q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nx : NextL S}
    {laz' : Lazy S} (hq : RunOKG (Map := Map) lib q goal g0 g1 nx) (hf : fromL axe nx.laz = some laz')
    (hgm : ∀ r, GMem goal r → r < g0.re) :
    RunOKG (Map := Map) lib (Nomm.n7 (Nomm.n0 axe) q) goal g0 g1 ⟨laz', nx.th⟩ :=
  runOKG_sevenE hq (runOKE_n0 lib hf hq.lo hq.hi hq.dist (fun e he => (hq.eregs e he).1) hq.nodup) hgm
    (fun _ _ _ => rfl)

end Comp
end SkaModel
end Formalization
