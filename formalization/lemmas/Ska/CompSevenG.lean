import lemmas.Ska.CompRunOKLCSeven
import lemmas.Ska.CompCallC

/-!
# `[7 p q]` with calls, for any goal: `runOKGC_sevenG`

README Gaps 12.21.  `runOKLC_seven` (`CompRunOKLCSeven.lean`) composes two
`RunOKLC` under `%next`; `UOKC` also asks `%done`, where `q` runs under
`%done` itself.  When `q`'s run returns a need without entries (no fork, no
bond: `NoEnt`), `p` runs under a goal without entries, `UOKC` of `p` gives
its run, and the two compose for any goal (`runOKGC_sevenG`): `p` runs
first (it may move the oracle's state), then `q` from `p`'s jump with the
registers that `p` left.

The formula is abstract (`MinkC7`): `+mink` on `f` runs `fb`, and on a
product `u` of it runs `fc` on `u` (the `n7` form `[7 b c]` itself,
`minkC7_seven`; the other forms of the nomm `[7 p q]` are in
`CompSevenMink.lean`).

* `MinkC7`, `minkC7_seven`, `goalSemCM_of_badC`.
* `runOKGC_sevenG`: both `sem` clauses for any goal.
* `runLC_n7`, `NoEnt`, `noEnt_of_uok` (a call-free nomm without `%6`),
  `okc_sevenC`, `uokc_sevenC`, `noEnt_sevenC`.
* `JNew` (the jump of a run is its goal's or a new block), `jNew_n0`,
  `jNew_n1`, `jNew_of_entNew`, `entNew_sevenC`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+mink` on a composition -/

/-- **`+mink` on `f` is the composition of `fb` and `fc`**: `fb` runs with
no more fuel; a tone of it that is no product is the whole's, and on a
product `u` the formula `fc` runs on `u` with no more fuel (`fwd`);
backward, runs of the parts give one of `f` (`bwd`). -/
structure MinkC7 (lib : Lib) (P : Noun → Prop) (f fb fc : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    ∃ n1, n1 ≤ n ∧ ∃ rb, minkF lib gul n1 tm s fb = some rb ∧
      (((∀ q, rb ≠ Tone.zero q) ∧ r = rb) ∨
        ∃ u, rb = Tone.zero u ∧ ∃ n2, n2 ≤ n ∧ minkF lib gul n2 tm u fc = some r)
  bwd : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb →
    ((∀ q, rb ≠ Tone.zero q) → Mink lib gul tm s f rb) ∧
    ∀ u r, rb = Tone.zero u → Mink lib gul tm u fc r → Mink lib gul tm s f r

/-- `[7 b c]` itself (`minkF_sevenC`, `mink_sevenC_bwd`). -/
theorem minkC7_seven (lib : Lib) (P : Noun → Prop) (b c : Noun) : MinkC7 lib P (n3 (A 7) b c) b c where
  fwd := fun {s gul n tm r} _ h => by
    obtain ⟨n', hn, rb, hb, h | ⟨u, rfl, hc⟩⟩ := minkF_sevenC h
    · exact ⟨n', Nat.le_of_lt hn, rb, hb, Or.inl h⟩
    · exact ⟨n', Nat.le_of_lt hn, _, hb, Or.inr ⟨u, rfl, n', Nat.le_of_lt hn, hc⟩⟩
  bwd := fun {s gul tm rb} _ hb => mink_sevenC_bwd hb

/-- `MinkC7` on fewer subjects. -/
theorem MinkC7.mono {lib : Lib} {P P' : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    (h : ∀ s, P' s → P s) : MinkC7 lib P' f fb fc :=
  ⟨fun hs hm => M.fwd (h _ hs) hm, fun hs hb => M.bwd (h _ hs) hb⟩

/-! ## The composition for any goal -/

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop}
  {ν : σ → Needs}

/-- **A tone that a goal sees as a failure** meets `GoalSemCM` where the
code returns a crash with the trace as it is. -/
theorem goalSemCM_of_badC {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {goal : CGoal S} {r : Tone} (hb : BadC goal tm r)
    (H : ReturnsC lib O c gul Inv ν st regs t je (Tone.two tm)) :
    GoalSemCM lib O c gul Inv ν K st regs t tm je goal r := by
  rcases hb with e | ⟨p, e, hp⟩
  · subst e; exact goalSemCM_ret goal _ (fun _ e => by cases e) H
  · subst e
    cases goal with
    | next laz th => exact ⟨fun f => absurd f hp, fun _ => H⟩
    | pick z o => exact hp.elim
    | done => exact hp.elim

end

/-- **`[7 p q]` for any goal, when `q`'s run returns a need without
entries**: `RunOKGC` of `q` under the goal (its subjects the products of
`fb`), and of `p` under `q`'s result goal (without entries), give `RunOKGC`
of the whole for any formula `f` with `MinkC7`.  `hg`: the goal's registers
were allocated before the run.  Forward, `p`'s tone is from `M.fwd` and
`q`'s from its `sem`; backward, both from the `semB` clauses and the whole's
`+mink` run by `M.bwd`. -/
theorem runOKGC_sevenG {lib : Lib} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    {goal : CGoal S} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGC (Map := Map) lib (Img lib P fb) fc goal g0 g1 nx) (hnx : entries nx.laz = [])
    (Rp : RunOKGC (Map := Map) lib P fb (CGoal.next nx.laz.sure nx.th) g1 g2 nex)
    (hg : ∀ r, GMem goal r → r < g0.re) :
    RunOKGC lib P f goal g0 g2 nex := by
  have q1 := Rq.ext.1
  have q2 := Rq.ext.2.1
  have p1 := Rp.ext.1
  have p2 := Rp.ext.2.1
  have nxL : ∀ r, NMem nx.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases Rq.regs r hr with h | h
    · have := hg r h; omega
    · exact h.2
  have plab : ∀ e ∈ entries nex.laz, g1.bo ≤ e.1 := fun e he => (Rp.labs e he).1
  -- the `AgreeU` of the parts from the whole's
  have agP : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), AgreeU lib O c gul st t cf ned g0 g2 nex.laz s0 s →
      AgreeU lib O c gul st t cf ned g1 g2 nex.laz s0 s :=
    fun cf c σ O gul st t ned s0 s ag => AgreeU.part ag q2 (Ext.refl g2) (fun e he => he) (fun k _ _ hk => hk)
      (fun e he => Nat.lt_trans (Rp.labs e he).2.1 Rp.hi)
  have agQ : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st st' : σ)
      (t : Trace) (ned : Need) (s0 s u : Noun), AgreeU lib O c gul st t cf ned g0 g2 nex.laz s0 s →
      AgreeU lib O c gul st' t cf ned g0 g1 nx.laz s0 u := by
    intro cf c σ O gul st st' t ned s0 s u ag
    refine ⟨fun o h0 h1 _ => ?_, fun e he => by rw [hnx] at he; cases he⟩
    rw [ag.1 o h0 (by omega) (fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := plab e he; omega), Rp.ext.2.2.2 o h1]
  -- the registers that `p`'s goal keeps include the whole's
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g2.re ≤ x) → ∀ x,
      ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) →
      ((x < g1.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next nx.laz.sure nx.th) x) := fun ned hned x hx => by
    refine ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hm => ?_⟩
    rcases Rq.regs x hm with h | h
    · exact hx.2 h
    · rcases hx.1 with h' | h'
      · omega
      · have := hned x h'; omega
  refine ⟨Rq.ext.trans Rp.ext, Rq.grow.trans Rp.grow, Rq.cfr.trans Rp.cfr, Rp.lo, Rp.hi, ?_, fun r hr => ?_,
    Rp.dist, fun e he => ⟨(Rp.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ⟨by have := (Rp.labs e he).1; omega, (Rp.labs e he).2⟩, Rp.nodup, fun s hs hf => ?_, Rp.ncond,
    Rp.econd, ?_, ?_⟩
  · -- ent
    rcases Rp.ent with fr | e
    · exact Or.inl fr
    · have e' : nex.th = nx.th := e
      rw [e']
      rcases Rq.ent with fr | e2
      · exact Or.inl (fr.growU Rq.hi Rp.grow)
      · exact Or.inr e2
  · -- regs
    rcases Rp.regs r hr with h | h
    · rcases Rq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · -- eregs
    obtain ⟨h1, h2⟩ := (Rp.eregs e he).2 r hr
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · rcases Rq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.1
    · exact Or.inr (by omega)
  · -- nec
    obtain ⟨N1, N2⟩ := Rp.nec s hs hf
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n1, _, rb, hb, h | ⟨u, rfl, n2, _, hc⟩⟩ := M.fwd hs hm
      · obtain ⟨hn, hr⟩ := h
        rw [hr]
        rcases N1 gul n1 tm rb hb with e | ⟨q, e, _⟩
        · exact Or.inl e
        · exact absurd e (hn q)
      · rcases N1 gul n1 tm _ hb with e | ⟨q, e, hq⟩
        · cases e
        · cases e
          exact (Rq.nec u (img_of hs hb) hq).1 gul n2 tm r hc
    · obtain ⟨rb, hb, hbad⟩ := N2 gul tm
      rcases hbad with e | ⟨u, rfl, hq⟩
      · subst e
        exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e), Or.inl rfl⟩
      · obtain ⟨r, hr, hbr⟩ := (Rq.nec u ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩ hq).2 gul tm
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, hbr⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨n1, h1, rb, hb, hr⟩ := M.fwd hs hm
    have Gp := Rp.sem cf hcf c ned σ Inv ν O n1 gul hS (oracleFwd_le hF h1) st t tm s0 s rb hI htr hs hb
      (fun st' => agP cf c σ O gul st' t ned s0 s (ag st')) hned regs hh hn
    rcases hr with ⟨hnz, rfl⟩ | ⟨u, rfl, n2, h2, hc⟩
    · exact goalSemCM_ret goal _ hnz (returnsC_of_goalSemCM _ _ hnz Gp)
    by_cases fit : FitsS nx.laz.sure u
    · obtain ⟨st', R1, hI', hν, h1', k1, e1⟩ := Gp.1 fit
      have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
        have := nxL x hm; have := hned x hx; omega⟩) hn
      have Gq := Rq.sem cf hcf1 c ned σ Inv ν O n2 gul hS (oracleFwd_le hF h2) st' t tm s0 u r hI'
        (frames_mono hν htr) (img_of hs hb) hc (fun st'' => agQ cf c σ O gul st st'' t ned s0 s u (ag st))
        (fun x hx => by have := hned x hx; omega) R1 ⟨h1', fit.2⟩ hn1
      exact goalSemCM_step hν (fun x hx => k1 x (hK ned hned x hx)) e1 goal r Gq
    · exact goalSemCM_of_badC ((Rq.nec u (img_of hs hb) fit).1 gul n2 tm r hc) (Gp.2 fit)
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨rb, hb, Gp⟩ := Rp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (fun st' => agP cf c σ O gul st' t ned s0 s (ag st')) hned regs hh hn res hres
    cases rb with
    | one q =>
      exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e),
        goalSemCM_ret goal _ (fun _ e => by cases e) (returnsC_of_goalSemCM _ _ (fun _ e => by cases e) Gp)⟩
    | two t' =>
      exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e),
        goalSemCM_ret goal _ (fun _ e => by cases e) (returnsC_of_goalSemCM _ _ (fun _ e => by cases e) Gp)⟩
    | zero u =>
      have hu : Img lib P fb u := ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩
      by_cases fit : FitsS nx.laz.sure u
      · obtain ⟨st', R1, hI', hν, h1', k1, e1⟩ := Gp.1 fit
        have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
          have := nxL x hm; have := hned x hx; omega⟩) hn
        obtain ⟨r, hr, Gq⟩ := Rq.semB cf hcf1 c ned σ Inv ν O gul hS hB st' t tm s0 u hI' (frames_mono hν htr) hu
          (fun st'' => agQ cf c σ O gul st st'' t ned s0 s u (ag st)) (fun x hx => by have := hned x hx; omega)
          R1 ⟨h1', fit.2⟩ hn1 res (by rw [← e1]; exact hres)
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, goalSemCM_step hν (fun x hx => k1 x (hK ned hned x hx)) e1 goal r Gq⟩
      · obtain ⟨r, hr, hbad⟩ := (Rq.nec u hu fit).2 gul tm
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, goalSemCM_of_badC hbad (Gp.2 fit)⟩

/-! ## Runs whose need has no entries -/

theorem runLC_n7 (env : CallEnv) (sup : Option Nomm) (p q : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runLC env sup (Nomm.n7 p q) goal region : CM Map (NextL S)) =
      (runLC env (some p) q goal region >>= fun nx => runLC env sup p nx.goal region) := by
  cases goal <;> simp only [runLC]

/-- A lazy need without entries has no fork and no bond. -/
theorem eq_ofSure_of_entries {l : Lazy S} (h : entries l = []) : l = ofSure l.sure := by
  apply eq_ofSure
  cases l with
  | mk s f b =>
    simp only [entries, List.append_eq_nil_iff] at h
    refine ⟨?_, ?_⟩
    · cases f with
      | nil => rfl
      | cons x rest =>
        obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := x
        simp [forkEntries] at h
    · cases b with
      | nil => rfl
      | cons x rest =>
        obtain ⟨o, l'⟩ := x
        simp [bondEntries] at h

/-- **The run of `nm` for a fork-free goal returns a need without entries**
(no fork, no bond), from any state. -/
def NoEnt (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    NoPick goal → runLC env sup nm (CGoal.toL goal) region g0 = some (nex, g1) → entries nex.laz = []

/-- **A call-free nomm without `%6` meets `NoEnt`**: its run is `run`'s
(`runL_toL`), whose need is fork-free. -/
theorem noEnt_pure (env : CallEnv) {nm : Nomm} (hp : nm.pure = true) (h6 : noSix nm = true) :
    NoEnt (S := S) (Map := Map) env nm := by
  intro sup goal region g0 g1 nex _ h
  rw [runLC_eq env nm (Nomm.noCall_of_pure nm hp), runL_toL nm hp h6 goal region, map_apply] at h
  obtain ⟨⟨n, g'⟩, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact entries_ofSure _

/-- **`[7 p q]` meets `NoEnt` when both parts do.** -/
theorem noEnt_sevenC {env : CallEnv} {p q : Nomm} (Np : NoEnt (S := S) (Map := Map) env p)
    (Nq : NoEnt (S := S) (Map := Map) env q) : NoEnt (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup goal region g0 g2 nex hnp h
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have ex := eq_ofSure_of_entries (Nq hnp hq)
  have hp' : runLC env sup p (CGoal.toL (CGoal.next nx.laz.sure nx.th)) region g1 = some (nex, g2) := by
    simp only [CGoal.toL]; rw [← ex]; exact hp
  exact Np (goal := CGoal.next nx.laz.sure nx.th) trivial hp'

/-! ## `UOKC` of `[7 p q]` -/

/-- The jump of a run is argless. -/
theorem entry_args {g : Gen Map} {goal : CGoal S} {j : Jmp} (h : Entry g goal j) (ha : GArgs goal)
    (hnp : NoPick goal) : j.args = [] := by
  rcases h with ⟨_, _, _, a⟩ | e
  · exact a
  · cases goal with
    | next sur th => simp only [GoalJ] at e; rw [e]; exact ha
    | done => exact e.elim
    | pick z o => exact hnp.elim

/-- **The pieces of the run of `[7 p q]`** with `q`'s run under the goal
(`RunOKGC` from `UOKC`), its need without entries (`NoEnt`), and the
hypotheses of `OKCN` for `p`'s run under `q`'s result goal. -/
theorem sevenC_parts {lib : Lib} {env : CallEnv} {p q : Nomm} {Pq : Noun → Prop} {fc : Noun}
    (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q) (Nq : NoEnt (S := S) (Map := Map) env q)
    {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (hnp : NoPick goal) (ha : GArgs goal) (hj : GJ g0.bo goal) (hok : GoalOK g0 goal) (hcl : GClean goal)
    (hcount : sixCount (Nomm.n7 p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (hkg : ∀ r, GMem goal r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n7 p q) (CGoal.toL goal) region g0 = some (nex, g2)) :
    ∃ (nx : NextL S) (g1 : Gen Map), RunOKGC lib Pq fc goal g0 g1 nx ∧ entries nx.laz = [] ∧
      runLC env (some p) q (CGoal.toL goal) region g0 = some (nx, g1) ∧
      runLC env sup p (CGoal.toL (CGoal.next nx.laz.sure nx.th)) region g1 = some (nex, g2) ∧
      (∀ r, GMem goal r → r < g0.re) ∧
      GArgs (CGoal.next nx.laz.sure nx.th : CGoal S) ∧ GJ g1.bo (CGoal.next nx.laz.sure nx.th : CGoal S) ∧
      GoalOK g1 (CGoal.next nx.laz.sure nx.th : CGoal S) ∧ GClean (CGoal.next nx.laz.sure nx.th : CGoal S) ∧
      sixCount p ≤ 255 ∧ 1 ≤ g1.bo ∧ g1.drop = false ∧ UpBelow g1 ∧ Clear g1 ∧ CondBelow g1 ∧
      (∀ r, GMem (CGoal.next nx.laz.sure nx.th : CGoal S) r → HoonMap.get g1.cond r = Option.none) := by
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have Rq := Uq.run hnp ha hj hok hcl hc.2 b0 d0 hu hcl0 hcb hkg hq
  have E := Nq hnp hq
  have ex := eq_ofSure_of_entries E
  have hg : ∀ r, GMem goal r → r < g0.re := fun r hr => by
    cases goal with
    | next sur th => exact hok.2 r hr
    | done => exact hr.elim
    | pick z o => exact hr.elim
  refine ⟨nx, g1, Rq, E, hq, by simp only [CGoal.toL]; rw [← ex]; exact hp, hg, entry_args Rq.ent ha hnp,
    ⟨Rq.lo, Rq.hi⟩, ⟨Rq.dist, fun r hr => ?_⟩, Uq.clean hnp hcl hq, hc.1, by have := Rq.ext.2.1; omega,
    Rq.ext.2.2.1.trans d0, Rq.grow.up hu, hcl0.growU Rq.grow, Rq.cfr.below hcb, Rq.ncond⟩
  rcases Rq.regs r hr with h' | h'
  · have := hg r h'; have := Rq.ext.1; omega
  · exact h'.2

/-- **`[7 p q]` whose parts meet `UOKC` meets `OKCN`** for a formula with
`MinkC7`, when `q`'s run returns a need without entries (`runOKGC_sevenG`). -/
theorem okc_sevenC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p)
    (Uq : UOKC (S := S) (Map := Map) lib env (Img lib P fb) fc q) (Nq : NoEnt (S := S) (Map := Map) env q)
    (M : MinkC7 lib P f fb fc) : OKCN (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  intro sup goal region g0 g2 nex hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  obtain ⟨nx, g1, Rq, E, -, hp, hg, a1, j1, o1, c1, n1, b1, d1, u1, l1, cb1, k1⟩ :=
    sevenC_parts Uq Nq hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  exact runOKGC_sevenG M Rq E (Up.run trivial a1 j1 o1 c1 n1 b1 d1 u1 l1 cb1 k1 hp) hg

/-- **The sure need of `[7 p q]`'s run is clean** (`UOKC.clean` of `p` under
`q`'s result goal, without entries by `NoEnt`). -/
theorem sevenC_clean {lib : Lib} {env : CallEnv} {p q : Nomm} {P Pq : Noun → Prop} {fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q)
    (Nq : NoEnt (S := S) (Map := Map) env q) {sup : Option Nomm} {goal : CGoal S} {region : List Nat}
    {g0 g2 : Gen Map} {nex : NextL S} (hnp : NoPick goal) (hcl : GClean goal)
    (h : runLC env sup (Nomm.n7 p q) (CGoal.toL goal) region g0 = some (nex, g2)) : Clean nex.laz.sure.ned := by
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have ex := eq_ofSure_of_entries (Nq hnp hq)
  have hp' : runLC env sup p (CGoal.toL (CGoal.next nx.laz.sure nx.th)) region g1 = some (nex, g2) := by
    simp only [CGoal.toL]; rw [← ex]; exact hp
  exact Up.clean (goal := CGoal.next nx.laz.sure nx.th) trivial (Uq.clean hnp hcl hq) hp'

/-- **`[7 p q]` whose parts meet `UOKC` meets `UOKC`** when it is hinted
and `q`'s run returns a need without entries. -/
theorem uokc_sevenC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p)
    (Uq : UOKC (S := S) (Map := Map) lib env (Img lib P fb) fc q) (Nq : NoEnt (S := S) (Map := Map) env q)
    (M : MinkC7 lib P f fb fc) (hh : hinted env.cod (Nomm.n7 p q) = some true) :
    UOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) :=
  ⟨Or.inr hh, fun hnp hcl h => sevenC_clean Up Uq Nq hnp hcl h, okc_sevenC lib env Up Uq Nq M⟩

/-! ## `EntNew` of `[7 p q]` -/

/-- **The jump of a run under a fork-free `%next` is the goal's or a new
block** (`EntNew` with the goal's jump allowed). -/
def JNew (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    (∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none) →
    runLC env sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) → nex.th = th ∨ g0.bo ≤ nex.th.there

theorem jNew_of_entNew {env : CallEnv} {nm : Nomm} (h : EntNew (S := S) (Map := Map) env nm) :
    JNew (S := S) (Map := Map) env nm :=
  fun hj hth hok hcl hc b0 d0 hu hcl0 hcb hkg hr => Or.inr (h hj hth hok hcl hc b0 d0 hu hcl0 hcb hkg hr)

/-- **`[0 axe]` meets `JNew`**: its jump is the goal's, or the block of
`+bomb` for `[0 0]`. -/
theorem jNew_n0 (env : CallEnv) (axe : Nat) : JNew (S := S) (Map := Map) env (Nomm.n0 axe) := by
  intro sup sur th region g0 g1 nex _ _ _ _ _ _ _ _ _ _ _ h
  simp only [runLC] at h
  by_cases h0 : axe = 0
  · rw [if_pos h0] at h
    simp only [bombL, bind_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Nat.le_refl _)
  · rw [if_neg h0] at h
    obtain ⟨nx, g', h1, h⟩ := bind_some h
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    by_cases h1 : axe = 1
    · rw [if_pos h1] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl rfl
    · rw [if_neg h1] at h
      revert h
      cases fromL axe (ofSure sur) with
      | none => intro h; cases h
      | some laz =>
        intro h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl rfl

/-- **`[1 k]` meets `JNew`**: its jump is the block of `+mede`. -/
theorem jNew_n1 (env : CallEnv) (k : Noun) : JNew (S := S) (Map := Map) env (Nomm.n1 k) := by
  intro sup sur th region g0 g1 nex _ _ _ _ _ _ _ _ _ _ _ h
  simp only [runLC] at h
  obtain ⟨o, g', h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  unfold medeL at h1
  obtain ⟨o', ge, he, h1⟩ := bind_some h1
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨gg, gx, hg, h1⟩ := bind_some h1
  split at h1
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr (Nat.le_refl _)
  · obtain ⟨u, gy, _, h1⟩ := bind_some h1
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr (Nat.le_refl _)

/-- **`[7 p q]` meets `EntNew`** when `p` does, or when `p`'s jump is its
goal's or new (`JNew`) and `q` meets `EntNew`. -/
theorem entNew_sevenC {lib : Lib} {env : CallEnv} {p q : Nomm} {Pq : Noun → Prop} {fc : Noun}
    (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q) (Nq : NoEnt (S := S) (Map := Map) env q)
    (E : EntNew (S := S) (Map := Map) env p ∨ (JNew (S := S) (Map := Map) env p ∧ EntNew (S := S) (Map := Map) env q)) :
    EntNew (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup sur th region g0 g2 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  obtain ⟨nx, g1, Rq, _, hq, hp, _, a1, j1, o1, c1, n1, b1, d1, u1, l1, cb1, k1⟩ :=
    sevenC_parts (goal := CGoal.next sur th) Uq Nq trivial hth hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have q2 := Rq.ext.2.1
  rcases E with Ep | ⟨Jp, Eq⟩
  · have := Ep j1 a1 o1 c1 n1 b1 d1 u1 l1 cb1 k1 hp; omega
  · rcases Jp j1 a1 o1 c1 n1 b1 d1 u1 l1 cb1 k1 hp with e | e
    · rw [e]
      have hc : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
      exact Eq hj hth hok hcl hc b0 d0 hu hcl0 hcb hkg hq
    · omega

end Comp
end SkaModel
end Formalization
