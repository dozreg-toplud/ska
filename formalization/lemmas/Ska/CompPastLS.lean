import lemmas.Ska.CompConsLSRun
import lemmas.Ska.CompTailGC
import lemmas.Ska.CompConsCall

/-!
# `+past` behind a run under a lazy goal: `RunOKLS.past`

README Gaps 12.25.  `tailGC_past` (`CompTailGC.lean`) for `RunOKLS`: when
the head of a cons calls, `+past` parks the tail's result `nex` in a bond
behind a new block `g1.bo` whose code is `hop nex.th`; the result is
`⟨mk bunt [] ((g1.bo, mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond),
jmp0 g1.bo⟩`.  The goal's blocks, the fronts and the witness relation do
not change; the new entry's block has an empty body, and at run time the
program's block there is the fill `A` of the parked need (`AgreeLB`), then
the jump to `nex.th`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A run under a lazy goal, with its block of `+past`** (see the header). -/
theorem RunOKLS.past {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit} {x : Bool}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKLS (Map := Map) lib P f L th Q x g0 g1 nex)
    (hsur : ∀ r, NMem L.sure.ned r → r < g0.re) (hLb : ∀ e ∈ entries L, e.1 < g0.bo)
    (hta : th.args = []) (d1 : g1.drop = false) (u1 : UpBelow g1) (region : List Nat) :
    RunOKLS (Map := Map) lib P f L th Q x g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
      ⟨Lazy.mk Sure.bunt [] ((g1.bo, Lazy.mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond), jmp0 g1.bo⟩ := by
  have hb : ∀ k, HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [tagged_blocks, Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G1 : GrowU g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩) (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨R.lo, R.hi⟩) u1).trans (growU_tagged _ _ _)
  have mem : ∀ e, e ∈ entries (Lazy.mk (Sure.bunt : Sure S) [] ((g1.bo, Lazy.mk nex.laz.sure nex.laz.fork []) ::
      nex.laz.bond)) ↔ e = (g1.bo, Lazy.mk nex.laz.sure nex.laz.fork []) ∨ e ∈ entries nex.laz := fun e => by
    rw [(entries_past _ _ _).mem_iff, List.mem_cons]
  have lt1 : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => by
    rcases (R.labs e he).1 with a | a
    · obtain ⟨e0, h0, ee⟩ := List.mem_map.mp a
      have := hLb e0 h0; have := R.bo; omega
    · exact a.2
  have re1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re = g1.re := by
    simp [Gen.emitted]
  have bo1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).bo = g1.bo + 1 := by
    simp [Gen.emitted]
  have cd1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond = g1.cond := by
    rw [tagged_cond]; rfl
  have thn : nex.th.args = [] := nextArgs_nil R.ent hta
  have hcfE : ∀ (cf : Map (Nat × List Nat)),
      (∀ k, k < ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re →
        HoonMap.get cf k = HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond k) →
      ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun cf hcf k hk => by
    rw [hcf k (by rw [re1]; exact hk), cd1]
  -- the shared part of the two `sem` clauses: the block of `+past`
  have core : ∀ (cf : Map (Nat × List Nat)),
      (∀ k, k < ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re →
        HoonMap.get cf k = HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (t : Trace) (s0 s : Noun),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
        (Lazy.mk (Sure.bunt : Sure S) [] ((g1.bo, Lazy.mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond)) s0 s) →
      (∀ x, NMem ned x → ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re ≤ x) →
      ∀ (st : σ) (regs : Map (Option Noun)), HoldsN ned regs s0 →
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) ∧ (∀ x, NMem ned x → g1.re ≤ x) ∧
      (FitsS nex.laz.sure s → ∃ R', HoldsS nex.laz.sure R' s ∧ HoldsN ned R' s0 ∧
        (∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) → SkaModel.read x R' = SkaModel.read x regs) ∧
        goJ lib O c gul st regs t (jmp0 g1.bo) = goJ lib O c gul st R' t nex.th) ∧
      (¬ FitsS nex.laz.sure s → goJ lib O c gul st regs t (jmp0 g1.bo) = some (Tone.two t, st)) := by
    intro cf hcf c ned σ O gul t s0 s ag hned st regs hn
    obtain ⟨A, B, th', h1, h2, F⟩ := (ag st).2 _ ((mem _).mpr (Or.inl rfl)) (by simpa using R.bo)
    rw [hb, if_pos rfl] at h1
    simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [List.map_nil] at h2
    rw [renJmp_nil _ thn] at h2
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; rwa [re1] at this
    refine ⟨fun st' => ⟨fun o h0 h1' hm => ?_, fun e he l => ?_⟩, hned1, fun fs => ?_, fun fs => ?_⟩
    · rw [(ag st').1 o h0 (by rw [bo1]; omega) (fun hm' => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
          rcases (mem e).mp he with rfl | a
          · simp at h1'
          · exact hm (List.mem_map_of_mem a)), hb, if_neg (by omega)]
    · obtain ⟨A', B', th'', k1, k2, k3⟩ := (ag st').2 e ((mem e).mpr (Or.inr he)) l
      rw [hb, if_neg (by have := lt1 e he; omega)] at k1
      exact ⟨A', B', th'', k1, k2, by rw [re1] at k3; exact k3⟩
    · obtain ⟨F1, F2⟩ := F regs hn
      obtain ⟨R', hr, hh, hk⟩ := F1 fs
      have e1 := hr [] (Termin.hop nex.th)
      refine ⟨R', hh, HoldsN.agree _ (fun x hx => hk x (Or.inl hx) (fun hm => by
        have := hned1 x hx
        rcases R.regs x hm with b | ⟨_, b⟩
        · have := hsur x b; have := R.re; omega
        · omega)) hn, fun r ⟨k1, k2⟩ => ?_, by rw [goJ_jmp0 _ _ _ _ h2, e1, execBlob_hop]⟩
      refine hk r (k1.elim (fun h => Or.inr (by rw [re1]; have := R.re; omega)) Or.inl) fun hm => ?_
      rcases R.regs r hm with b | ⟨b, b'⟩
      · exact k2 b
      · rcases k1 with k1 | k1
        · omega
        · have := hned1 r k1; omega
    · have e2 := (F regs hn).2 fs [] (Termin.hop nex.th)
      rw [goJ_jmp0 _ _ _ _ h2, e2]
  have FR : ∀ e ∈ entries L, ∀ F : List Pole,
      (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) →
      ∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ →
        HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).blocks e.1 =
          some ⟨[], F ++ B, fin⟩ := fun e he F hF B fin h => by
    rw [hb, if_neg (by have := hLb e he; have := R.bo; omega)]; exact hF B fin h
  have NE : ∀ e ∈ entries L, e.1 ∉ (entries nex.laz).map Prod.fst →
      e.1 ∉ (entries (Lazy.mk (Sure.bunt : Sure S) [] ((g1.bo, Lazy.mk nex.laz.sure nex.laz.fork []) ::
        nex.laz.bond))).map Prod.fst := fun e he hn hm => by
    obtain ⟨e', he', ee⟩ := List.mem_map.mp hm
    rcases (mem e').mp he' with rfl | a
    · have := hLb e he; have := R.bo; simp at ee; omega
    · exact hn (ee ▸ List.mem_map_of_mem a)
  refine ⟨{
    re := by rw [re1]; exact R.re
    bo := by rw [bo1]; have := R.bo; omega
    drop := by rw [← R.drop]; simp [Gen.emitted, d1]
    keep := fun o ho hn => by rw [hb, if_neg (by have := R.bo; omega)]; exact R.keep o ho hn
    grow := R.grow.trans G1
    cfr := R.cfr.trans (condFresh_of_eq (by rw [re1]; exact Nat.le_refl _) cd1)
    lo := by simp only [jmp0]; have := R.lo; have := R.hi; omega
    hi := by simp [jmp0, Gen.emitted]
    ent := Or.inl ⟨⟨[], [], Termin.hop nex.th⟩, by rw [hb]; simp [jmp0], rfl, rfl⟩
    regs := fun r hr => by simp [Sure.bunt, NMem] at hr
    dist := trivial
    eregs := fun e he => ?_
    labs := fun e he => ?_
    nodup := ?_
    dreg := fun s v d w r hq hr => by rw [re1]; exact R.dreg s v d w r hq hr
    nec := fun s _ hs => absurd (fitsS_bunt s) hs
    ncond := fun r hr => by simp [Sure.bunt, NMem] at hr
    econd := fun e he r hr => ?_
    front := fun e he => ?_
    sem := ?_
    semB := ?_ }, fun e he => ?_⟩
  · rcases (mem e).mp he with rfl | a
    · refine ⟨R.dist, fun r hr => ?_⟩
      rw [re1]
      rcases R.regs r hr with b | b
      · exact Or.inr (Or.inl b)
      · exact Or.inr (Or.inr b)
    · refine ⟨(R.eregs e a).1, fun r hr => ?_⟩
      rw [re1]; exact (R.eregs e a).2 r hr
  · rcases (mem e).mp he with rfl | a
    · exact ⟨Or.inr ⟨R.bo, by rw [bo1]; omega⟩, [], _, by rw [hb, if_pos rfl]⟩
    · obtain ⟨x1, B, th', z⟩ := R.labs e a
      have := lt1 e a
      refine ⟨x1.imp id (fun h => ⟨h.1, by rw [bo1]; omega⟩), B, th', by rw [hb, if_neg (by omega)]; exact z⟩
  · rw [((entries_past _ _ _).map Prod.fst).nodup_iff, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lt1 e he; omega, R.nodup⟩
  · rw [cd1]
    rcases (mem e).mp he with rfl | a
    · exact R.ncond r hr
    · exact R.econd e a r hr
  · obtain ⟨F, hF, H⟩ := R.front e he
    refine ⟨F, FR e he F hF, fun cf hcf => ?_⟩
    rcases H cf (hcfE cf hcf) with ⟨L', h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨L', (mem _).mpr (Or.inr h1), by rw [re1]; exact h2⟩
    · exact Or.inr ⟨NE e he h1, by rw [re1]; exact h2⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs _ hn
    obtain ⟨ag1, hned1, F1, F2⟩ := core cf hcf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      exact goalSemCMD_step (Needs.le_refl _) hk e1
        (R.sem cf (hcfE cf hcf) c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag1 hned1 R' hh hn')
    · have ec := F2 fs
      rcases (R.nec s hs fs).1 gul n tm r hm with e | ⟨v, rfl, hv⟩
      · subst e; exact ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩
      · exact ⟨fun f => absurd f hv, fun _ => ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs _ hn res hres
    obtain ⟨ag1, hned1, F1, F2⟩ := core cf hcf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      obtain ⟨r, hm, G⟩ := R.semB cf (hcfE cf hcf) c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag1 hned1 R'
        hh hn' res (by rw [← e1]; exact hres)
      exact ⟨r, hm, goalSemCMD_step (Needs.le_refl _) hk e1 G⟩
    · have ec := F2 fs
      obtain ⟨r, hm, hbad⟩ := (R.nec s hs fs).2 gul tm
      refine ⟨r, hm, ?_⟩
      rcases hbad with e | ⟨v, rfl, hv⟩
      · subst e; exact ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩
      · exact ⟨fun f => absurd f hv, fun _ => ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩⟩
  · -- the fronts at the state level
    obtain ⟨F, hF, H⟩ := R.fs e he
    refine ⟨F, FR e he F hF, fun cf hcf => ?_⟩
    rcases H cf (hcfE cf hcf) with ⟨L', h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨L', (mem _).mpr (Or.inr h1), by rw [re1]; exact h2⟩
    · exact Or.inr ⟨NE e he h1, by rw [re1]; exact h2⟩

end Comp
end SkaModel
end Formalization
