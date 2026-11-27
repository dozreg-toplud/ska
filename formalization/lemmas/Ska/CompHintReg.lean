import lemmas.Ska.CompHintSpot

/-!
# Kept hints under `%next (lazy-from-reg r)`, nested (README Gaps 24.17)

* `RunOKGBT.bound`: **the block of `+lazy-bound` behind a run with
  `RunOKGBT`**, for any result `nex` (bonds and forks of `nex.laz` kept
  inside the one new bond).  The entries of `mk bunt [] [(o, L)]` are
  `(o, L) :: entries L` (`entries_bound1`), and the relation reads an entry
  through its label and its sure need only, so no congruence with `+past`'s
  shape is needed.
* `runOKGBT_of_next`, `runOKGBT_done`: the texts of `runOKGB_of_next`,
  `runOKGB_done` (`CompCallTreeTop.lean`) for `RunOKGBT`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The entries of the result of `+lazy-bound`. -/
theorem entries_bound1 (s : Sure S) (o : Nat) (l : Lazy S) :
    entries (mk s [] [(o, l)]) = (o, l) :: entries l := by
  simp [entries, bondEntries, forkEntries]

/-- **The block of `+lazy-bound` behind a run with `RunOKGBT`** under
`%next sur th0` (the goal's registers below `g0.re`): the result `nex` is
parked whole in one bond behind a new block `g1.bo` whose code is
`hop nex.th`; at run time the program's block there is the fill `A` of
`nex.laz.sure`, then the jump.  `nex.laz` may have bonds and forks: they
are entries of the new result too. -/
theorem RunOKGBT.bound {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th0 : Jmp}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKGBT lib N P f (CGoal.next sur th0) g0 g1 nex)
    (hgl : ∀ r, NMem sur.ned r → r < g0.re) (thn : nex.th.args = []) (d1 : g1.drop = false)
    (u1 : UpBelow g1) (region : List Nat) :
    RunOKGBT lib N P f (CGoal.next sur th0) g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
      ⟨Lazy.mk Sure.bunt [] [(g1.bo, nex.laz)], jmp0 g1.bo⟩ := by
  have hb : ∀ k, HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [tagged_blocks, Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G1 : GrowU g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩) (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨R.lo, R.hi⟩) u1).trans (growU_tagged _ _ _)
  have hent := entries_bound1 (Sure.bunt : Sure S) g1.bo nex.laz
  have mem : ∀ e, e ∈ entries (Lazy.mk (Sure.bunt : Sure S) [] [(g1.bo, nex.laz)]) ↔
      e = (g1.bo, nex.laz) ∨ e ∈ entries nex.laz := fun e => by
    rw [hent, List.mem_cons]
  have lt1 : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => (R.labs e he).2.1
  have re1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re = g1.re := by
    simp [Gen.emitted]
  have bo1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).bo = g1.bo + 1 := by
    simp [Gen.emitted]
  have cd1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond = g1.cond := by
    rw [tagged_cond]; rfl
  have E1 : Ext g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (ext_emit _ _).trans (ext_tagged _ _ _)
  have hcfE : ∀ (cf : Map (Nat × List Nat)),
      (∀ k, k < ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re →
        HoonMap.get cf k = HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond k) →
      ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun cf hcf k hk => by
    rw [hcf k (by rw [re1]; exact hk), cd1]
  -- the block of `+lazy-bound`, the agreement of the run's result
  have core : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun),
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0
        ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
        (Lazy.mk (Sure.bunt : Sure S) [] [(g1.bo, nex.laz)]) s0 s) →
      (∀ x, NMem ned x → ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re ≤ x) →
      ∀ (st : σ) (regs : Map (Option Noun)), HoldsN ned regs s0 →
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) ∧ (∀ x, NMem ned x → g1.re ≤ x) ∧
      (FitsS nex.laz.sure s → ∃ R', HoldsS nex.laz.sure R' s ∧ HoldsN ned R' s0 ∧
        (∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th0) x) → SkaModel.read x R' = SkaModel.read x regs) ∧
        goJ lib O c gul st regs t (jmp0 g1.bo) = goJ lib O c gul st R' t nex.th) ∧
      (¬ FitsS nex.laz.sure s → goJ lib O c gul st regs t (jmp0 g1.bo) = some (Tone.two t, st)) := by
    intro cf c ned σ O gul t s0 s ag hned st regs hn
    obtain ⟨A, B, th', h1, h2, F⟩ := (ag st t).2 _ ((mem _).mpr (Or.inl rfl))
    rw [hb, if_pos rfl] at h1
    simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [List.map_nil] at h2
    rw [renJmp_nil _ thn] at h2
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; rwa [re1] at this
    refine ⟨fun st' t' => ⟨fun o h0 h1' hm => ?_, fun e he => ?_⟩, hned1, fun fs => ?_, fun fs => ?_⟩
    · rw [(ag st' t').1 o h0 (by rw [bo1]; omega) (fun hm' => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
          rcases (mem e).mp he with rfl | a
          · simp at h1'
          · exact hm (List.mem_map_of_mem a)), hb, if_neg (by omega)]
    · obtain ⟨A', B', th'', k1, k2, k3⟩ := (ag st' t').2 e ((mem e).mpr (Or.inr he))
      rw [hb, if_neg (by have := lt1 e he; omega)] at k1
      exact ⟨A', B', th'', k1, k2, by rw [re1] at k3; exact k3⟩
    · obtain ⟨F1, F2⟩ := F regs hn
      obtain ⟨R', hr, hh, hk⟩ := F1 fs
      have e1 := hr [] (Termin.hop nex.th)
      have nsur : ∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th0) x) → ¬ NMem nex.laz.sure.ned x :=
        fun x ⟨k1, k2⟩ hm => by
          rcases R.regs x hm with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned1 x k1; omega
      refine ⟨R', hh, HoldsN.agree _ (fun x hx => hk x (Or.inl hx) (fun hm => by
        have := hned1 x hx
        rcases R.regs x hm with b | ⟨_, b⟩
        · have := hgl x b; have := R.ext.1; omega
        · omega)) hn, fun r hr => hk r (hr.1.elim (fun h => Or.inr (by rw [re1]; have := R.ext.1; omega)) Or.inl)
          (nsur r hr), by rw [goJ_jmp0 _ _ _ _ h2, e1, execBlob_hop]⟩
    · have e2 := (F regs hn).2 fs [] (Termin.hop nex.th)
      rw [goJ_jmp0 _ _ _ _ h2, e2]
  refine ⟨R.ext.trans E1, R.grow.trans G1, R.cfr.trans (condFresh_of_eq (by rw [re1]; exact Nat.le_refl _) cd1),
    by simp only [jmp0]; have := R.lo; have := R.hi; omega, by simp [jmp0, Gen.emitted],
    Or.inl ⟨⟨[], [], Termin.hop nex.th⟩, by rw [hb]; simp [jmp0], rfl, rfl⟩,
    fun r hr => by simp [Sure.bunt, NMem] at hr, trivial, fun e he => ?_, fun e he => ?_, ?_,
    fun s _ hs => absurd (fitsS_bunt s) hs, fun r hr => by simp [Sure.bunt, NMem] at hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases (mem e).mp he with rfl | a
    · refine ⟨R.dist, fun r hr => ?_⟩
      rw [re1]
      rcases R.regs r hr with b | b
      · exact ⟨Or.inl b, by have := hgl r b; have := R.ext.1; omega⟩
      · exact ⟨Or.inr b.1, b.2⟩
    · refine ⟨(R.eregs e a).1, fun r hr => ?_⟩
      rw [re1]; exact (R.eregs e a).2 r hr
  · rcases (mem e).mp he with rfl | a
    · exact ⟨R.ext.2.1, by rw [bo1]; omega, [], _, by rw [hb, if_pos rfl]⟩
    · obtain ⟨x1, x2, B, th', z⟩ := R.labs e a
      exact ⟨x1, by rw [bo1]; omega, B, th', by rw [hb, if_neg (by omega)]; exact z⟩
  · rw [hent, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lt1 e he; simp at e1; omega, R.nodup⟩
  · rw [cd1]
    rcases (mem e).mp he with rfl | a
    · exact R.ncond r hr
    · exact R.econd e a r hr
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs _ hn
    obtain ⟨ag1, hned1, F1, F2⟩ := core cf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      exact goalSemCM_step (Needs.le_refl _) hk e1 _ _
        (R.sem cf (hcfE cf hcf) c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag1 hned1 R' hh hn')
    · exact goalSemCM_of_badC ((R.nec s hs fs).1 gul n tm r hm)
        ⟨Tone.two t, st, hI, Needs.le_refl _, F2 fs, ToneRel.two htr⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs _ hn res hres
    obtain ⟨ag1, hned1, F1, F2⟩ := core cf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      obtain ⟨r, hm, G⟩ := R.semB cf (hcfE cf hcf) c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag1 hned1 R'
        hh hn' res (by rw [← e1]; exact hres)
      exact ⟨r, hm, goalSemCM_step (Needs.le_refl _) hk e1 _ _ G⟩
    · obtain ⟨r, hm, hbad⟩ := (R.nec s hs fs).2 gul tm
      exact ⟨r, hm, goalSemCM_of_badC hbad ⟨Tone.two t, st, hI, Needs.le_refl _, F2 fs, ToneRel.two htr⟩⟩

end Comp
end SkaModel
end Formalization
