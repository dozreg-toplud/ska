import lemmas.Ska.CompRunOKLCSeven

/-!
# The second part of a pair behind its `+past`: `TailGC`

README Gaps 12.20.  When the first part of a pair (the head of a cons, the
subject part of an indirect call) calls, `+past` parks the second part's
need in a bond behind a new block `[hop th]` whose label is the second
part's new jump: at run time the first part's code jumps there, the ops the
parent put at that block fill the second part's need from the subject, and
the second part's code runs.  The run together with its block of `+past`
meets `RunOKGC` except that this block is both an entry and the jump
(`labs` with `≤`): `TailGC`, the counterpart of `TailNV` (`CompConsCall.lean`)
for a second part that may call.

* `TailGC`, `TailGC.ofRun` (no block of `+past`).
* `tailGC_past`: the run with its block of `+past` (both `sem` clauses: the
  block's ops fill the need, or crash where the subject does not fit it,
  which the second part's `NecC` makes its own failure).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`RunOKGC` under `%next sur th` with an entry at the jump allowed**
(`labs` with `≤`), what the second part of a pair meets behind its block of
`+past`. -/
structure TailGC (lib : Lib) (P : Noun → Prop) (f : Noun) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 (CGoal.next sur th) nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem sur.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (NMem sur.ned r ∨ g0.re ≤ r) ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 ≤ nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f (CGoal.next sur th) s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemGC lib P f (CGoal.next sur th) g0 g1 nex
  semB : SemGCB lib P f (CGoal.next sur th) g0 g1 nex

theorem TailGC.ofRun {lib : Lib} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKGC (Map := Map) lib P f (CGoal.next sur th) g0 g1 nex) :
    TailGC lib P f sur th g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs,
    fun e he => ⟨(R.labs e he).1, Nat.le_of_lt (R.labs e he).2.1, (R.labs e he).2.2⟩,
    R.nodup, R.nec, R.ncond, R.econd, R.sem, R.semB⟩

/-- **The second part with its block of `+past` meets `TailGC`**: the
bond's block fills the part's need from the subject (`FillSem` of
`AgreeU`), or crashes where the subject does not fit it, which the part's
`NecC` makes the part's crash or a value that does not fit the goal. -/
theorem tailGC_past {lib : Lib} {P : Noun → Prop} {f : Noun} {sur : Sure S} {o : Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKGC (Map := Map) lib P f (CGoal.next sur (jmp0 o)) g0 g1 nex)
    (hsur : ∀ r, NMem sur.ned r → r < g0.re) (d1 : g1.drop = false) (u1 : UpBelow g1)
    (region : List Nat) :
    TailGC lib P f sur (jmp0 o) g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
      ⟨mk Sure.bunt [] ((g1.bo, mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond), jmp0 g1.bo⟩ := by
  have hb : ∀ k, HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [tagged_blocks, Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have E1 : Ext g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (ext_emit g1 _).trans (ext_tagged _ _ _)
  have G1 : GrowU g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩) (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨R.lo, R.hi⟩) u1).trans (growU_tagged _ _ _)
  have mem : ∀ e, e ∈ entries (mk (Sure.bunt : Sure S) [] ((g1.bo, mk nex.laz.sure nex.laz.fork []) ::
      nex.laz.bond)) ↔ e = (g1.bo, mk nex.laz.sure nex.laz.fork []) ∨ e ∈ entries nex.laz := fun e => by
    rw [(entries_past _ _ _).mem_iff, List.mem_cons]
  have lt1 : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => Nat.lt_trans (R.labs e he).2.1 R.hi
  have l01 := R.ext.1
  have thn : nex.th.args = [] := nextArgs_nil R.ent rfl
  -- the shared part of the two `sem` clauses: the block of `+past`
  have core : ∀ (cf : Map (Nat × List Nat)),
      (∀ k, k < ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re →
        HoonMap.get cf k = HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (t : Trace) (s0 s : Noun),
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
        (mk (Sure.bunt : Sure S) [] ((g1.bo, mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond)) s0 s) →
      (∀ x, NMem ned x → ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re ≤ x) →
      ∀ (st : σ) (regs : Map (Option Noun)), HoldsN ned regs s0 →
      (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) ∧
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g1 nex.laz s0 s) ∧ (∀ x, NMem ned x → g1.re ≤ x) ∧
      (FitsS nex.laz.sure s → ∃ R', HoldsS nex.laz.sure R' s ∧ HoldsN ned R' s0 ∧
        (∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ NMem sur.ned x) → SkaModel.read x R' = SkaModel.read x regs) ∧
        goJ lib O c gul st regs t (jmp0 g1.bo) = goJ lib O c gul st R' t nex.th) ∧
      (¬ FitsS nex.laz.sure s → goJ lib O c gul st regs t (jmp0 g1.bo) = some (Tone.two t, st)) := by
    intro cf hcf c ned σ O gul t s0 s ag hned st regs hn
    obtain ⟨A, th', h1, h2, F⟩ := (ag st).2 _ ((mem _).mpr (Or.inl rfl))
    rw [hb, if_pos rfl] at h1
    cases h1
    rw [renJmp_nil _ thn] at h2
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk => by
      rw [hcf k (by simp [Gen.emitted]; omega), tagged_cond]; rfl
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; simpa [Gen.emitted] using this
    refine ⟨hcf1, fun st' => (ag st').part (Nat.le_refl _) E1 (fun e he => (mem e).mpr (Or.inr he))
        (fun k _ h1' hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (mem e).mp he with rfl | a
          · simp at h1'
          · exact List.mem_map_of_mem a) lt1, hned1, fun fs => ?_, fun fs => ?_⟩
    · obtain ⟨F1, F2⟩ := F regs hn
      obtain ⟨R', hr, hh, hk⟩ := F1 fs
      have e1 := hr [] (Termin.hop nex.th)
      simp only [List.append_nil] at e1
      refine ⟨R', hh, HoldsN.agree _ (fun x hx => hk x (Or.inl hx) (fun hm => by
        have := hned1 x hx
        rcases R.regs x hm with b | ⟨_, b⟩
        · have := hsur x b; omega
        · omega)) hn, fun r ⟨k1, k2⟩ => ?_, by rw [goJ_jmp0 _ _ _ _ h2, e1, execBlob_hop]⟩
      refine hk r (k1.elim (fun h => Or.inr (by rw [tagged_re]; simp only [Gen.emitted]; omega)) Or.inl)
        fun hm => ?_
      rcases R.regs r hm with b | ⟨b, _⟩
      · exact k2 b
      · rcases k1 with k1 | k1
        · omega
        · have := hned1 r k1; omega
    · have e2 := (F regs hn).2 fs [] (Termin.hop nex.th)
      simp only [List.append_nil] at e2
      rw [goJ_jmp0 _ _ _ _ h2, e2]
  refine ⟨R.ext.trans E1, R.grow.trans G1, R.cfr.trans (condFresh_of_eq (by simp [Gen.emitted]) (by
      rw [tagged_cond]; rfl)), by simp only [jmp0]; have := R.lo; have := R.hi; omega,
    by simp [jmp0, Gen.emitted], Or.inl ⟨⟨[], [], Termin.hop nex.th⟩, by rw [hb]; simp [jmp0], rfl, rfl⟩,
    fun r hr => by simp [Sure.bunt, NMem] at hr, trivial, fun e he => ?_, fun e he => ?_, ?_,
    fun s _ hs => absurd (fitsS_bunt s) hs, fun r hr => by simp [Sure.bunt, NMem] at hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases (mem e).mp he with rfl | a
    · refine ⟨R.dist, fun r hr => ?_⟩
      simp only [Gen.emitted, tagged_re]
      rcases R.regs r hr with b | ⟨b, b'⟩
      · exact ⟨Or.inl b, by have := hsur r b; omega⟩
      · exact ⟨Or.inr (by omega), by omega⟩
    · refine ⟨(R.eregs e a).1, fun r hr => ?_⟩
      have := (R.eregs e a).2 r hr
      simp only [Gen.emitted, tagged_re]
      exact ⟨this.1, by omega⟩
  · rcases (mem e).mp he with rfl | a
    · exact ⟨R.ext.2.1, by simp [jmp0], _, by rw [hb, if_pos rfl]⟩
    · obtain ⟨x, -, th', z⟩ := R.labs e a
      have := lt1 e a
      exact ⟨x, by simp only [jmp0]; omega, th', by rw [hb, if_neg (by omega)]; exact z⟩
  · rw [((entries_past _ _ _).map Prod.fst).nodup_iff, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lt1 e he; omega, R.nodup⟩
  · rw [tagged_cond]
    rcases (mem e).mp he with rfl | a
    · exact R.ncond r hr
    · exact R.econd e a r hr
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs _ hn
    obtain ⟨hcf1, ag1, hned1, F1, F2⟩ := core cf hcf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      exact goalSemCM_step (Needs.le_refl _) hk e1 _ _
        (R.sem cf hcf1 c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag1 hned1 R' hh hn')
    · have ec := F2 fs
      rcases (R.nec s hs fs).1 gul n tm r hm with e | ⟨v, rfl, hv⟩
      · subst e; exact ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩
      · exact ⟨fun f => absurd f hv, fun _ => ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs _ hn res hres
    obtain ⟨hcf1, ag1, hned1, F1, F2⟩ := core cf hcf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      obtain ⟨r, hm, G⟩ := R.semB cf hcf1 c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag1 hned1 R' hh hn'
        res (by rw [← e1]; exact hres)
      exact ⟨r, hm, goalSemCM_step (Needs.le_refl _) hk e1 _ _ G⟩
    · have ec := F2 fs
      obtain ⟨r, hm, hbad⟩ := (R.nec s hs fs).2 gul tm
      refine ⟨r, hm, ?_⟩
      rcases hbad with e | ⟨v, rfl, hv⟩
      · subst e; exact ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩
      · exact ⟨fun f => absurd f hv, fun _ => ⟨Tone.two t, st, hI, Needs.le_refl _, ec, ToneRel.two htr⟩⟩

end Comp
end SkaModel
end Formalization
