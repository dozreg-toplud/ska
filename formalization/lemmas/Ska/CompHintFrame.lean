import lemmas.Ska.CompHintKeep

/-!
# The kept dynamic `stopTag` hint (`%spot`, `%hunk`, `%mean`) at the top (README Gaps 24.15)

`+run` on `[11 [tag h] q]` with `hint-dynamic` of `tag` under `%done`
(`runLCH`, the case `n11d`): the block `[don r]`, `+past-if` (nothing,
since `+sound` of `%this` holds), a fresh register `toke`, the epilogue
`[hde tag toke f] hop don`, `q` under `%next (lazy-from-reg r)` to it,
`+lazy-bound` (a block `o` holding `q`'s need as one bond), the prologue
`[hdp tag toke f] hop o`, the clue `h` under `%next (lazy-from-reg toke)`
to the prologue, `+copy` with the bond.

At run time: the clue's code, the copy block, the prologue (pushes
`(tag, v)`, `v` in `toke`), the bond block (fills `q`'s need from the
entry subject, at the pushed trace), `q`'s code, the epilogue (pops), the
`don` block.  The fill of the bond runs at the pushed trace, so the
agreement of the program with the run's blocks (`AgreeUB`) is needed at a
trace other than the entry's: `RunOKGBT` is `RunOKGB` whose `sem` clauses
are handed the agreement at every trace, as the top gives it
(`finishTop_genBT`: `finishTop_genB`'s `ag` holds at every trace).

* `RunOKGBT`, `RunOKGB.toT`; `finishTop_genBT`, `finishLUCH_contractGBT`
  (the copies of `finishTop_genB`, `finishLUCH_contractGB` for it).
* `FrameOK`: the frame part as a relation of its own (the code from the
  prologue, `toke` holding `v`, to the goal, against `+mink` of `q` at the
  trace `(tag, v) :: tm`), `frameOK_done` from `q`'s `RunOKGB` with the bond.
* `n11dKept_done`: **`RunOKGBT` of a kept dynamic `stopTag` hint under
  `%done`**, the clue with `LOKSFH` and `NoBondH`, the formula with
  `LOKSFH`, `NoBondH` and `+sound` of `%this`.
* `finishLUCH_contractN11dKept`, `finishLUCH_contractN11dKeptHU`: both
  halves of the contract at the top, traces included.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `RunOKGB` handed the agreement at every trace -/

/-- `SemGB` with the agreement at every trace. -/
def SemGBT (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- `SemGBB` with the agreement at every trace. -/
def SemGBBT (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **`RunOKGB` whose `sem` clauses are handed the agreement at every
trace**: what a run whose code runs a part at a trace of its own (the
frame of a kept dynamic hint) meets. -/
structure RunOKGBT (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (GMem goal r ∨ g0.re ≤ r) ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f goal s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemGBT lib N P f goal g0 g1 nex
  semB : SemGBBT lib N P f goal g0 g1 nex

/-- `RunOKGB` is `RunOKGBT` (the agreement used at the entry trace). -/
theorem RunOKGB.toT {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {goal : CGoal S} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKGB lib N P f goal g0 g1 nex) : RunOKGBT lib N P f goal g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup, R.nec, R.ncond, R.econd,
    fun cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag =>
      R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm (fun st' => ag st' t),
    fun cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag =>
      R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs (fun st' => ag st' t)⟩

/-! ## The top, the agreement at every trace -/

/-- (The text of `finishTop_genB`, `CompLBDone.lean`, its `ag` at every
trace.) -/
theorem finishTop_genBT (lib : Lib) {g1 : Gen Map} {nex : NextL S} (R : TopSB g1 nex)
    (Φ : (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop)
    (hsem : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned gen0 g1 nex.laz s s) → (∀ r, NMem ned r → g1.re ≤ r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
      Φ σ O st t gul s (goJ lib O c gul st regs t nex.th))
    (hnec : ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → Φ σ O st t gul s (some (Tone.two t, st)))
    {o sub : Nat} {g3 : Gen Map} (h2 : kerf nex g1 = some ((o, sub), g3))
    {c' : Straight Map} (hts : toStraightF g3.cond g3.blocks (Need.this sub) o = some c') :
    c'.need = NeedOrd.this ∧ ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (t : Trace) (gul : Noun),
      Φ σ O st t gul s (execEntry lib O st c' [s] t gul) := by
  have d1 : g1.drop = false := R.ext.2.2.1
  have cb1 : CondBelow g1 := R.cfr.below condBelow_gen0
  -- `+kerf`: the hop block, then `+kern`
  unfold kerf at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, g4, h3, h4⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have lt0 : nex.th.there < g1.bo := R.hi
  have hlab : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => (R.labs e he).2.1
  have hn : (((g1.bo, nex.laz) :: entries nex.laz).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := hlab e he; omega, R.nodup⟩
  have cbe : CondBelow (g1.emitted ⟨[], [], Termin.hop nex.th⟩) := cb1
  obtain ⟨hr, W⟩ := kern_spec h3 d1 cbe hn
  simp only [Gen.emitted] at hr
  subst hr
  have eblk : ∀ k, HoonMap.get (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  -- the blocks after `+kern`
  obtain ⟨A0, hA0, P0⟩ := W.at_ (g1.bo, nex.laz) List.mem_cons_self
  have hB0 : HoonMap.get g4.blocks g1.bo = some ⟨[], A0, Termin.hop nex.th⟩ := by
    have := hA0 [] (Termin.hop nex.th) (by simp only [eblk]; simp)
    simpa using this
  have hE : ∀ e ∈ entries nex.laz, ∃ A B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩ ∧
      HoonMap.get g4.blocks e.1 = some ⟨[], A ++ B, Termin.hop th⟩ ∧
      KernP g1.re g4.cond (g1.re + 1) g4.re e.1 e.2.sure A := by
    intro e he
    obtain ⟨_, _, B, th, hth⟩ := R.labs e he
    obtain ⟨A, hA, P⟩ := W.at_ e (List.mem_cons_of_mem _ he)
    refine ⟨A, B, th, hth, ?_, P⟩
    have := hA B (Termin.hop th) (by
      have ne : e.1 ≠ g1.bo := by have := hlab e he; omega
      simp only [eblk, ne, ↓reduceIte]; exact hth)
    simpa using this
  have hO : ∀ k, k ≠ g1.bo → k ∉ (entries nex.laz).map Prod.fst → HoonMap.get g4.blocks k = HoonMap.get g1.blocks k := by
    intro k k1 k2
    rw [W.other k (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨k1, k2⟩)]
    simp only [eblk, k1, ↓reduceIte]
  -- the program: the blocks unproxied
  let c1 : Straight Map := ⟨NeedOrd.none, 0, mapVals (unproxyBlob g4.cond) g4.blocks⟩
  have hag : ∀ k, HoonMap.get c1.blocks k = (HoonMap.get g4.blocks k).map (unproxyBlob g4.cond) :=
    fun k => get_mapVals _ _ k
  have D1 := downRk_gen0 (R.grow.trans (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩)
    (fun j hj => by simp [finJumps] at hj; subst hj; exact ⟨R.lo, lt0⟩) (upBelow_of_growU R.grow)))
  have D4 := downRk_of_fins D1 (bs' := g4.blocks) fun k b' hk => by
    by_cases e1 : k = g1.bo
    · subst e1; rw [hB0] at hk; cases hk; exact ⟨⟨[], [], Termin.hop nex.th⟩, by rw [eblk]; simp, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e2
      obtain ⟨A, B, th, h1', h4', _⟩ := hE e he
      rw [h4'] at hk; cases hk
      exact ⟨⟨[], B, Termin.hop th⟩, by rw [eblk, if_neg e1]; exact h1', rfl⟩
    · rw [hO k e1 e2] at hk; exact ⟨b', by rw [eblk, if_neg e1]; exact hk, rfl⟩
  have Dc : DownRk (upRk (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks) c1.blocks := by
    intro k b hk
    rw [hag k] at hk
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact downRk_unproxy _ (D4 k b0 hb0)
  obtain ⟨hneed, start, hst, hent⟩ := toStraightF_entryU hts (by simp [flattenNeed, isRun]) D4 Dc
    (fun k _ => hag k)
  rw [hB0] at hst; cases hst
  refine ⟨hneed, fun σ O st s t gul => ?_⟩
  obtain ⟨R0, hR0, he⟩ := hent lib O st s [s] t gul (by rw [hneed]; rfl)
  rw [he]
  have ag4 : ∀ k, k < g1.re + 1 → HoonMap.get g4.cond k = HoonMap.get g1.cond k := fun k hk => W.cnd.1.get_lt hk
  have u4r : HoonMap.get g4.cond g1.re = Option.none := by
    rw [ag4 _ (Nat.lt_succ_self _)]; exact condBelow_none cb1 (Nat.le_refl _)
  have regs1 : ∀ x, NMem nex.laz.sure.ned x → x < g1.re := fun x hx => (R.regs x hx).2
  have hj : nex.th.args = [] := R.args
  have hrj : renJmp (unproxy g4.cond) nex.th = nex.th := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hj; simp only at hj; subst hj; rfl
  -- the agreement of the program with the run's blocks
  have ag : ∀ (st' : σ) (t' : Trace), AgreeUB lib O c1 gul st' t' g4.cond (Need.this g1.re) gen0 g1 nex.laz s s :=
      fun st' t' => by
    refine ⟨fun o' _ u hnl => ?_, fun e he => ?_⟩
    · rw [hag o', hO o' (by omega) hnl]
    · obtain ⟨A, B, th, h1', h4', P⟩ := hE e he
      refine ⟨A.map (renPole (unproxy g4.cond)), B, th, h1', ?_, ?_⟩
      · rw [hag, h4']; simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, List.map_append]
      · obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P
        have l0' : g1.re + 1 ≤ lo0 := l0
        have regsE : ∀ x, NMem e.2.sure.ned x → x < g1.re := fun x hx => ((R.eregs e he).2 x hx).2
        have KS := sem (by omega) (R.eregs e he).1 regsE (unproxy g4.cond) (unproxy_none u4r)
          (fun x hx => unproxy_none (by rw [ag4 x (by have := regsE x hx; omega)]; exact R.econd e he x hx))
          (fun _ _ => rfl)
        intro R hR
        obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st' t' R s hR
        refine ⟨fun f => ?_, S2⟩
        obtain ⟨R', a, b, k⟩ := S1 f
        exact ⟨R', a, b, fun x hx hn => k x (by
          rcases hx with hx | hx
          · simp only [NMem] at hx; omega
          · omega) hn⟩
  -- the ops at the hop block, then the run
  obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P0
  have l0' : g1.re + 1 ≤ lo0 := l0
  have KS := sem (by omega) R.dist regs1 (unproxy g4.cond) (unproxy_none u4r)
    (fun x hx => unproxy_none (by rw [ag4 x (by have := regs1 x hx; omega)]; exact R.ncond x hx))
    (fun _ _ => rfl)
  obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st t R0 s hR0
  simp only [unproxyBlob, renBlob, List.map_nil, renFin, hrj]
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := S1 fo
    have e1 := hr1 [] (Termin.hop nex.th)
    simp only [List.append_nil] at e1
    rw [e1, execBlob_hop]
    have hn1 : HoldsN (Need.this g1.re) R1 s := by
      show SkaModel.read g1.re R1 = some s
      rw [kr1 g1.re (by omega) (fun hm => by have := regs1 _ hm; omega)]; exact hR0
    exact hsem g4.cond (fun k hk => ag4 k (by omega)) c1 (Need.this g1.re) σ O st t gul s ag
      (fun x hx => by simp only [NMem] at hx; omega) R1 hh1 hn1
  · have e2 := S2 fo [] (Termin.hop nex.th)
    simp only [List.append_nil] at e2
    rw [e2]; exact hnec σ O st t gul s fo

/-- **`+copy` of a result with no fork and no bond into one bond**: one hop
block to the result's jump; the sure need is the result's (its `lok` joined
with the empty set), the bond the second's. -/
theorem copyL_bond1 {first : NextL S} {o : Nat} {L : Lazy S} {g g' : Gen Map} {nex : NextL S} (hd : g.drop = false)
    (hf : first.laz.fork = []) (hb : first.laz.bond = [])
    (h : copyL first (mk Sure.bunt [] [(o, L)]) g = some (nex, g')) :
    nex = ⟨mk ⟨first.laz.sure.ned, HoonSet.uni first.laz.sure.lok HoonSet.empty⟩ [] [(o, L)], jmp0 g.bo⟩ ∧
      g'.re = g.re ∧ g'.bo = g.bo + 1 ∧ g'.drop = false ∧ g'.cond = g.cond ∧
      ∀ k, HoonMap.get g'.blocks k = HoonMap.get (g.emitted ⟨[], [], Termin.hop first.th⟩).blocks k := by
  unfold copyL at h
  obtain ⟨oc, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨laz, gf, hc, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rcases first with ⟨⟨s1, f1, b1⟩, th1⟩
  simp only [fork_mk, bond_mk] at hf hb
  subst hf hb
  have e : (copyLazyL (S := S) (Map := Map) g.bo (mk s1 [] []) (mk Sure.bunt [] [(o, L)]) : CM Map (Lazy S)) =
      fun g2 => (addOps g.bo [] g2).bind fun x => some (mk ⟨s1.ned, HoonSet.uni s1.lok HoonSet.empty⟩ [] [(o, L)], x.2) := by
    funext g2
    simp only [copyLazyL, copyNeed_none_r, bind_apply, pure_apply, Option.bind_some, Sure.bunt, fork_mk,
      bond_mk, sure_mk, List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [e] at hc
  obtain ⟨⟨u, gu⟩, hu, hc⟩ := Option.bind_eq_some_iff.mp hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨bk, hbk, rfl⟩ := addOps_spec hu (by simp only [emitted_drop, hd])
  refine ⟨rfl, rfl, rfl, hd, rfl, fun k => ?_⟩
  simp only [HoonMap.get_put, List.nil_append]
  split
  · rename_i e; subst e; rw [hbk]
  · rfl

/-! ## The frame -/

section Frame
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}

/-- **The frame of a kept dynamic `stopTag` hint in the program**: the
prologue `prol` pushes `(tag, toke)` and goes to `o` (where the formula's
code is entered, its need taken from the subject), the epilogue `epil`
pops and goes to `th`. -/
def FrameOK (c : Straight Map) (tag toke : Nat) (body : Noun) (prol o epil : Nat) (th : Jmp) : Prop :=
  stopTag tag = true ∧
  HoonMap.get c.blocks prol = some ⟨[], [Pole.hdp tag toke body], Termin.hop (jmp0 o)⟩ ∧
  HoonMap.get c.blocks epil = some ⟨[], [Pole.hde tag toke body], Termin.hop th⟩

/-- **The frame part**: the formula's code from `o`, run at the trace
`(tag, v) :: t` against `+mink` at `(tag, v) :: tm` under `%next sur` to
the epilogue, is the code from the prologue at `t` against `tm` under
`%next sur` to the epilogue's jump, the tone the same, when `toke` holds `v`
and every product fits `sur` (what `+past-if` makes sure of: under `%done`
`sur` is `lazy-from-reg`). -/
theorem frameOK_goes {tag toke : Nat} {body : Noun} {prol o epil : Nat} {th : Jmp} (F : FrameOK c tag toke body prol o epil th)
    {sur : Sure S} (hfit : ∀ p, FitsS sur p) {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {v : Noun}
    (hv : SkaModel.read toke regs = some v) {t tm : Trace} {r : Tone}
    (G : GoalSemCM lib O c gul Inv ν K st regs ((tag, v) :: t) ((tag, v) :: tm) (jmp0 o) (CGoal.next sur (jmp0 epil)) r) :
    GoalSemCM lib O c gul Inv ν K st regs t tm (jmp0 prol) (CGoal.next sur th) r := by
  have epush : ∀ st regs, SkaModel.read toke regs = some v →
      goJ lib O c gul st regs t (jmp0 prol) = goJ lib O c gul st regs ((tag, v) :: t) (jmp0 o) :=
    fun st regs h => goJ_push F.1 F.2.1 st regs h t
  have epop : ∀ st regs, goJ lib O c gul st regs ((tag, v) :: t) (jmp0 epil) = goJ lib O c gul st regs t th :=
    fun st regs => goJ_pop F.1 F.2.2 st regs (tag, v) t
  cases r with
  | zero p =>
    refine ⟨fun hf => ?_, fun hf => absurd (hfit p) hf⟩
    obtain ⟨st', regs', hI, hle, hh, hk, e⟩ := G.1 hf
    exact ⟨st', regs', hI, hle, hh, hk, by rw [epush st regs hv, e, epop]⟩
  | one b =>
    obtain ⟨ton, st', hI, hle, e, hrel⟩ := G
    exact ⟨ton, st', hI, hle, by rw [epush st regs hv]; exact e, hrel⟩
  | two tr =>
    obtain ⟨ton, st', hI, hle, e, hrel⟩ := G
    exact ⟨ton, st', hI, hle, by rw [epush st regs hv]; exact e, hrel⟩

end Frame

/-! ## `+mink` on the hint -/

theorem tbind_zero_id (x : Option Tone) : tbind x (fun p => some (Tone.zero p)) = x := by
  rcases x with _ | (_ | _ | _) <;> rfl

/-- `+mink` on a kept dynamic `stopTag` hint: the clue, then the formula at
the pushed trace, its tone the hint's. -/
theorem minkF_n11d_stop (lib : Lib) (gul : Noun) (n : Nat) (tm : Trace) (s : Noun) {tag : Nat} (hst : stopTag tag = true)
    (fh f : Noun) :
    minkF lib gul (n + 1) tm s (n3 (A 11) (C (A tag) fh) f) =
      tbind (minkF lib gul n tm s fh) fun c => minkF lib gul n ((tag, c) :: tm) s f := by
  rw [minkF_n11d_any]; simp only [hst, if_true, tbind_zero_id]

theorem minkF_zero_fuel (lib : Lib) (gul : Noun) (tm : Trace) (s f : Noun) : minkF lib gul 0 tm s f = none := rfl

/-- **`Mink` of the hint from its parts**: the clue's product `v`, then the
formula at `(tag, v) :: tm`. -/
theorem mink_n11d_stop {lib : Lib} {gul : Noun} {tm : Trace} {s : Noun} {tag : Nat} (hst : stopTag tag = true)
    {fh f : Noun} {v : Noun} {r : Tone} (hh : Mink lib gul tm s fh (Tone.zero v))
    (hf : Mink lib gul ((tag, v) :: tm) s f r) : Mink lib gul tm s (n3 (A 11) (C (A tag) fh) f) r := by
  obtain ⟨n1, e1⟩ := hh
  obtain ⟨n2, e2⟩ := hf
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_n11d_stop lib gul _ tm s hst, minkF_le lib gul (Nat.le_max_left n1 n2) _ _ _ _ e1]
  exact minkF_le lib gul (Nat.le_max_right n1 n2) _ _ _ _ e2

/-- A clue that does not return a product is the hint's tone. -/
theorem mink_n11d_clue {lib : Lib} {gul : Noun} {tm : Trace} {s : Noun} {tag : Nat} (hst : stopTag tag = true)
    {fh f : Noun} {r : Tone} (hh : Mink lib gul tm s fh r) (hr : ∀ q, r ≠ Tone.zero q) :
    Mink lib gul tm s (n3 (A 11) (C (A tag) fh) f) r := by
  obtain ⟨n1, e1⟩ := hh
  refine ⟨n1 + 1, ?_⟩
  rw [minkF_n11d_stop lib gul _ tm s hst, e1]
  rcases r with q | b | tr
  · exact absurd rfl (hr q)
  · rfl
  · rfl

section
variable {snd : Nomm → NeedOrd → Bool}

/-- (The text of `finishLUCH_contractGB`, `CompHintLSCons.lean`, for `RunOKGBT`.) -/
theorem finishLUCH_contractGBT (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLCH env snd true Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → RunOKGBT lib N P f (CGoal.done : CGoal S) gen0 gE nex)
    {c : Straight Map} (h : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  unfold finishLUCH at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  have R : RunOKGBT lib N P f (CGoal.done : CGoal S) gen0 gE nex := hR hr
  have T : TopSB gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTop_genBT lib T (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) hk hts
  have B := finishTop_genBT lib T (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs => ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩⟩
  · exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr
  · exact B.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

/-! ## The run, step by step -/

/-- The state after the `don` block, `toke` and the epilogue. -/
def genA (g0 : Gen Map) (tag : Nat) (body : Noun) : Gen Map :=
  ({ ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) with re := g0.re + 2 }).emitted
    ⟨[], [Pole.hde tag (g0.re + 1) body], Termin.hop (jmp0 g0.bo)⟩

/-- **The run of a kept dynamic hint under `%done`, step by step**, when
`+sound` of `%this` holds for the formula. -/
theorem runLCH_n11d_kept_done {env : CallEnv} {tag : Nat} (hs : hintDynamic tag = true) {h q : Nomm} {body : Noun}
    (hsnd : snd q NeedOrd.this = true) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hr : runLCH env snd true sup (Nomm.n11d tag h q body) CGoalL.done region g0 = some (nex, g1)) :
    ∃ nq gc nh gh, runLCH env snd true sup q (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 (g0.bo + 1))) region
        (genA g0 tag body) = some (nq, gc) ∧
      nq.th.args = [] ∧
      runLCH env snd true sup h (CGoalL.next (ofSure (lazyReg (g0.re + 1))) (jmp0 (gc.bo + 1))) region
        (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
          ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) = some (nh, gh) ∧
      copyL nh (mk Sure.bunt [] [(gc.bo, nq.laz)]) gh = some (nex, g1) := by
  simp only [runLCH, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
  obtain ⟨n0, ga, h0, hr⟩ := bind_some hr
  rw [simpleNextL_done] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨n1, gb, h1, hr⟩ := bind_some hr
  have hp : HoonSet.small (ofSure (lazyReg g0.re) : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure (lazyReg g0.re) : Lazy S).sure.ned) = true :=
    ⟨(HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x), hsnd⟩
  unfold pastIfL at h1
  rw [if_pos hp] at h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨tk, gt, ht, hr⟩ := bind_some hr
  rw [re_apply] at ht
  simp only [Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl⟩ := ht
  obtain ⟨ep, gb', h2, hr⟩ := bind_some hr
  rw [emit_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨nq, gc, h3, hr⟩ := bind_some hr
  obtain ⟨nb, gd, h4, hr⟩ := bind_some hr
  have hta : nq.th.args = [] := by
    cases hne : nq.th.args with
    | nil => rfl
    | cons a l =>
      unfold lazyBound at h4
      simp [bind_apply, emit_apply, setTag_apply, hne] at h4
  rw [lazyBound_apply hta] at h4
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨rfl, rfl⟩ := h4
  obtain ⟨pr, ge, h5, hr⟩ := bind_some hr
  rw [emit_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨nh, gh, h6, hr⟩ := bind_some hr
  refine ⟨nq, gc, nh, gh, ?_, hta, ?_, hr⟩
  · simpa only [genA, Gen.emitted, Nat.add_assoc] using h3
  · simpa only [Gen.emitted, tagged_bo] using h6

/-- Under `%next (lazy-from-reg r)`, a bad tone is a crash with `+mink`'s trace. -/
theorem badC_lazyReg {r : Nat} {th : Jmp} {tm : Trace} {x : Tone} (h : BadC (CGoal.next (lazyReg r : Sure S) th) tm x) :
    x = Tone.two tm := by
  rcases h with e | ⟨p, _, hp⟩
  · exact e
  · exact absurd (fitsS_lazyReg r p) hp

theorem growU_re (g : Gen Map) (r : Nat) : GrowU g { g with re := r } :=
  ⟨Nat.le_refl _, rfl, fun _ b _ hb => ⟨b, hb, rfl, rfl⟩, fun _ b hb => Or.inl ⟨b, hb, rfl, rfl⟩⟩

/-- **`RunOKGBT` of a kept dynamic `stopTag` hint under `%done`** (`%spot`,
`%hunk`, `%hand`, `%lose`, `%mean` with a safe clue): the clue `h` and the
formula `q` with `LOKSFH` (every member of `CallTreeHU`) and `NoBondH`, and
`+sound` of `%this` for `q` (so `+past-if` emits nothing).  The trace: the
clue's code runs at the entry trace (a crash there carries no frame, as
`+mink`'s clue); the prologue pushes `(tag, v)` and the formula's code, the
fill of its bond first, runs at `(tag, v) :: t` against `+mink`'s formula
at `(tag, v) :: tm` (`FrameRel.same`); the epilogue pops (`frameOK_goes`). -/
theorem n11dKept_done {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fh fq : Noun} {h q : Nomm}
    (Hq : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fq q) (hcq : sixCount q ≤ 255)
    (hnq : NoBondH (S := S) (Map := Map) snd env q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = true) (body : Noun)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH env snd true sup (Nomm.n11d tag h q body) CGoalL.done region g0 = some (nex, g1)) :
    RunOKGBT lib N P (n3 (A 11) (C (A tag) fh) fq) (CGoal.done : CGoal S) g0 g1 nex := by
  obtain ⟨nq, gc, nh, gh, h3, hta, h6, h7⟩ := runLCH_n11d_kept_done hs hsnd hr
  have e0 : ∀ r, entries (ofSure (lazyReg r : Sure S)) = [] := fun r => entries_ofSure _
  -- the state after `don`, `toke` and the epilogue
  have dA : (genA g0 tag body).drop = false := d0
  have reA : (genA g0 tag body).re = g0.re + 2 := rfl
  have boA : (genA g0 tag body).bo = g0.bo + 2 := rfl
  have bA : ∀ k, HoonMap.get (genA g0 tag body).blocks k =
      if k = g0.bo + 1 then some ⟨[], [Pole.hde tag (g0.re + 1) body], Termin.hop (jmp0 g0.bo)⟩
      else if k = g0.bo then some ⟨[], [], Termin.don g0.re⟩ else HoonMap.get g0.blocks k := by
    intro k; simp only [genA, Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have ua : UpBelow ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩ : Gen Map) := G1.up hu
  have G2 : GrowU ({ ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) with re := g0.re + 2 } : Gen Map)
      (genA g0 tag body) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, Gen.emitted]; omega) ua
  have GA : GrowU g0 (genA g0 tag body) := (growU_re g0 _).trans (G1.trans ((growU_re _ _).trans G2))
  have uA : UpBelow (genA g0 tag body) := GA.up hu
  have clA : Clear (genA g0 tag body) := hcl.growU GA
  have cbA : CondBelow (genA g0 tag body) := fun k hk => by
    have := hcb k hk; simp only [genA, Gen.emitted] at this ⊢; omega
  have extA : Ext g0 (genA g0 tag body) := ⟨by rw [reA]; omega, by rw [boA]; omega, dA.trans d0.symm, fun o ho => by
    rw [bA, if_neg (by omega), if_neg (by omega)]⟩
  have ctoke : HoonMap.get g0.cond (g0.re + 1) = Option.none := condBelow_none hcb (by omega)
  -- the formula, its bond
  obtain ⟨⟨Q, RS⟩, -, -, hfl, -⟩ := Hq.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 (g0.bo + 1))
    (region := region) (Or.inr (e0 _)) hcq (by rw [boA]; omega) dA uA clA cbA
    (by simp only [jmp0]; omega) (by simp only [jmp0]; rw [boA]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by rw [reA]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h3
  have hb0 := (hnq h3).2
  have hq : nq.laz = ofSure nq.laz.sure := lazy_eq_ofSure hfl.1 hb0
  have dc : gc.drop = false := RS.drop.trans dA
  have uc : UpBelow gc := RS.grow.up uA
  have RP := RS.past (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr; rw [reA]; omega)
    (fun e he => by rw [e0] at he; cases he) rfl dc uc region
  have eL : (mk Sure.bunt [] ((gc.bo, mk nq.laz.sure nq.laz.fork []) :: nq.laz.bond) : Lazy S) =
      mk Sure.bunt [] [(gc.bo, nq.laz)] := by
    rw [hb0, hfl.1, ← hfl.1, ← hb0, Lazy.eta]
  rw [eL] at RP
  have RG := RP.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; rw [reA]; omega)
  have boD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).bo = gc.bo + 1 := by
    simp only [tagged_bo, Gen.emitted]
  have dD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).drop = false := by
    simp only [tagged_drop, Gen.emitted]; exact dc
  have rcA : g0.re + 2 ≤ gc.re := by have := RG.ext.1; simp only [reA, tagged_re, Gen.emitted] at this; exact this
  have bcA : g0.bo + 2 ≤ gc.bo := by have := RS.bo; rw [boA] at this; exact this
  -- the prologue
  have GE : GrowU ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
      (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, boD]; omega) (RG.grow.up uA)
  have uE := GE.up (RG.grow.up uA)
  have clE := (clA.growU RG.grow).growU GE
  have cbE : CondBelow (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) := RG.cfr.below cbA
  have ctD : HoonMap.get ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).cond (g0.re + 1) = Option.none := by
    rw [RG.cfr.get_lt (by rw [reA]; omega)]; exact ctoke
  -- the clue
  obtain ⟨⟨Qh, RSh⟩, -, -, hflh, -⟩ := Hh.run (sup := sup) (L := ofSure (lazyReg (g0.re + 1))) (th := jmp0 (gc.bo + 1))
    (region := region) (Or.inr (e0 _)) hch (by simp only [Gen.emitted, boD]; omega) (by simp only [emitted_drop]; exact dD)
    uE clE cbE (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted, tagged_bo]; omega) rfl
    (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted, tagged_re]; omega, ctD⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h6
  have RGh := RSh.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted, tagged_re]; omega)
  obtain ⟨hfh, hbh⟩ := hnh h6
  have dh : gh.drop = false := RSh.drop.trans (by simp only [emitted_drop]; exact dD)
  obtain ⟨rfl, r1, b1, d1, c1, k1⟩ := copyL_bond1 dh hfh hbh h7
  -- the copy block, the facts of the states
  have hb1 : ∀ k, HoonMap.get g1.blocks k =
      if k = gh.bo then some ⟨[], [], Termin.hop nh.th⟩ else HoonMap.get gh.blocks k := by
    intro k; rw [k1 k]; simp [Gen.emitted, dh, HoonMap.get_put]
  have hargs : nh.th.args = [] := nextArgs_nil RGh.ent rfl
  have boh : gc.bo + 2 ≤ gh.bo := by have := RGh.ext.2.1; simp only [Gen.emitted, tagged_bo] at this; omega
  have reh : gc.re ≤ gh.re := by have := RGh.ext.1; simp only [Gen.emitted, tagged_re] at this; omega
  have E1 : Ext gh g1 := ⟨by omega, by omega, by rw [d1, dh], fun o ho => by rw [hb1, if_neg (by omega)]⟩
  have EE1 : Ext (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
      ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) g1 := RGh.ext.trans E1
  have ED1 : Ext ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 := (ext_emit _ _).trans EE1
  have EA1 : Ext (genA g0 tag body) g1 := RG.ext.trans ED1
  have CF1 : CondFresh ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 :=
    (condFresh_of_eq (Nat.le_refl _) rfl).trans (RGh.cfr.trans (condFresh_of_eq (by omega) c1))
  have CFA1 : CondFresh (genA g0 tag body) g1 := RG.cfr.trans CF1
  have GG : Grow gh g1 := Grow.congr_right (grow_emit (g := gh) (b := ⟨[], [], Termin.hop nh.th⟩) (fun j hj => by
    simp [finJumps] at hj; subst hj; exact ⟨RGh.lo, RGh.hi⟩)) b1 (by rw [d1, emitted_drop, dh]) k1
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = [(gc.bo, nq.laz)] := by
    rw [hq]; simp [entries, bondEntries, forkEntries, ofSure]
  have hent' : entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) = [(gc.bo, nq.laz)] := by
    rw [hq]; simp [entries, bondEntries, forkEntries, ofSure]
  have hentN : entries nh.laz = [] := by rw [entries_flat hflh, hbh]
  have hmem : ∀ e, e ∈ entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) → e ∈ entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) := fun e he => by
    rw [hent]; rw [hent'] at he; exact he
  -- the blocks in the program
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      HoonMap.get c.blocks gh.bo = some ⟨[], [], Termin.hop nh.th⟩ ∧
      FrameOK c tag (g0.re + 1) body (gc.bo + 1) gc.bo (g0.bo + 1) (jmp0 g0.bo) ∧
      HoonMap.get c.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    intro cf hcf c ned σ O gul st t s0 s ag
    have hnot : ∀ o, o ≠ gc.bo → o ∉ (entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ []
        [(gc.bo, nq.laz)] : Lazy S)).map Prod.fst := fun o ho => by rw [hent']; simpa using ho
    have ct : HoonMap.get cf (g0.re + 1) = Option.none := by
      rw [hcf _ (by omega), CFA1.get_lt (by rw [reA]; omega)]; exact ctoke
    have cr : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by omega), CFA1.get_lt (by rw [reA]; omega)]; exact condBelow_none hcb (Nat.le_refl _)
    have bE : HoonMap.get g1.blocks (gc.bo + 1) =
        some ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩ := by
      rw [EE1.2.2.2 _ (by simp only [Gen.emitted, tagged_bo]; omega), ← boD]; exact hk_emitted_self dD _
    refine ⟨?_, ⟨hst, ?_, ?_⟩, ?_⟩
    · rw [ag.1 gh.bo (by omega) (by omega) (hnot _ (by omega)), hb1, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp_nil _ hargs]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega)), bE]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp, jmp0, unproxy_none ct]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega)), EA1.2.2.2 _ (by rw [boA]; omega), bA, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp, jmp0, unproxy_none ct]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega)), EA1.2.2.2 _ (by rw [boA]; omega), bA, if_neg (by omega),
        if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, unproxy_none cr]
  have agh : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) gh nh.laz s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      simp only [Gen.emitted, tagged_bo] at h0
      rw [ag.1 o (by omega) (by omega) (by rw [hent']; simp; omega), hb1, if_neg (by omega)],
     fun e he => by rw [hentN] at he; cases he⟩
  have agq : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (genA g0 tag body) ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
        (mk Sure.bunt [] [(gc.bo, nq.laz)]) s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      rw [ag.1 o (by rw [boA] at h0; omega) (by have := ED1.2.1; omega) (by rw [hent']; rw [hent] at hn; exact hn),
        ED1.2.2.2 o h1],
     fun e he => by
      obtain ⟨A, B, th', a1, a2, a3⟩ := ag.2 e (by rw [hent']; rw [hent] at he; exact he)
      have l2 := (RG.labs e he).2.1
      exact ⟨A, B, th', by rw [← ED1.2.2.2 e.1 l2]; exact a1, a2, a3.mono (by have := ED1.1; omega)⟩⟩
  refine ⟨extA.trans EA1, GA.trans (RG.grow.trans (GE.trans (RGh.grow.trans (GG.toU (RGh.grow.up uE))))),
    (condFresh_of_eq (g0 := g0) (g1 := genA g0 tag body) (by rw [reA]; omega) rfl).trans CFA1,
    by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨_, by simp only [jmp0]; rw [hb1, if_pos rfl], rfl, rfl⟩,
    fun r hr => Or.inr ?_, RGh.dist, fun e he => ?_, fun e he => ?_, by rw [hent']; simp, fun s hs hf => ?_,
    fun r hr => by rw [c1]; exact RGh.ncond r hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases RGh.regs r hr with h | h
    · simp only [GMem, lazyReg, NMem] at h; subst h; constructor <;> omega
    · simp only [Gen.emitted, tagged_re] at h; constructor <;> omega
  · have he' := hmem e he
    refine ⟨(RG.eregs e he').1, fun r hr => ?_⟩
    have := (RG.eregs e he').2 r hr
    refine ⟨Or.inr ?_, ?_⟩
    · rcases this.1 with h | h
      · simp only [GMem, lazyReg, NMem] at h; omega
      · rw [reA] at h; omega
    · have := this.2; simp only [tagged_re, Gen.emitted] at this; omega
  · have he' := hmem e he
    obtain ⟨l1, l2, B, th', hB⟩ := RG.labs e he'
    exact ⟨by rw [boA] at l1; omega, by have := ED1.2.1; omega, B, th', by rw [ED1.2.2.2 e.1 l2]; exact hB⟩
  · have hf' : ¬ FitsS nh.laz.sure s := fun hf2 => hf ⟨hf2.1, (looks_uni _ _ _).mpr ⟨hf2.2, looks_empty _⟩⟩
    have NC := RGh.nec s hs hf'
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · cases n with
      | zero => rw [minkF_zero_fuel] at hm; cases hm
      | succ m =>
        rw [minkF_n11d_stop lib gul m tm s hst] at hm
        cases hmh : minkF lib gul m tm s fh with
        | none => rw [hmh] at hm; cases hm
        | some rh =>
          have := badC_lazyReg (NC.1 gul m tm rh hmh); subst this
          rw [hmh] at hm; simp only [tbind] at hm; cases hm
          exact Or.inl rfl
    · obtain ⟨rh, hm, hb⟩ := NC.2 gul tm
      have := badC_lazyReg hb; subst this
      exact ⟨_, mink_n11d_clue hst hm (fun q => by simp), Or.inl rfl⟩
  · have he' := hmem e he
    rw [CF1.get_lt ((RG.eregs e he').2 r hr).2]; exact RG.econd e he' r hr
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hcp, F, hdn⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th := fun st regs => by
      rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop]
    cases n with
    | zero => rw [minkF_zero_fuel] at hm; cases hm
    | succ m =>
      rw [minkF_n11d_stop lib gul m tm s hst] at hm
      cases hmh : minkF lib gul m tm s fh with
      | none => rw [hmh] at hm; cases hm
      | some rh =>
        rw [hmh] at hm
        have Gh := RGh.sem cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O m gul hN hS (oracleFwd_le hF (Nat.le_succ m)) st t tm s0 s rh
          hI htr hs hmh (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
          ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn
        cases rh with
        | zero v =>
          simp only [tbind] at hm
          obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_lazyReg _ v)
          have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
            simp only [GMem, lazyReg, NMem] at hg; have := hned x hx; omega⟩)
          have Gq := RG.sem cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν O m gul hN hS
            (oracleFwd_le hF (Nat.le_succ m)) st1 ((tag, v) :: t) ((tag, v) :: tm) s0 s r hI1
            (Forall2.cons (FrameRel.same hst) (frames_mono hle1 htr)) hs hm (fun st' => agq (ag st' ((tag, v) :: t)))
            (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := returnsC_done hdn (frameOK_goes F (fitsS_lazyReg g0.re) hh1 Gq)
          exact ⟨ton, st2, hI2, Needs.le_trans hle1 hle2, by rw [ecopy, e1]; exact e2, hrel⟩
        | one b =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
        | two tr =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hcp, F, hdn⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th := fun st regs => by
      rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop]
    rw [ecopy] at hres
    obtain ⟨rh, hmh, Gh⟩ := RGh.semB cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O gul hN hS hB
      st t tm s0 s hI htr hs (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn res hres
    cases rh with
    | zero v =>
      obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_lazyReg _ v)
      have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
        simp only [GMem, lazyReg, NMem] at hg; have := hned x hx; omega⟩)
      rw [e1, goJ_push hst F.2.1 st1 regs1 hh1 t] at hres
      obtain ⟨r, hmq, Gq⟩ := RG.semB cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν O gul
        hN hS hB st1 ((tag, v) :: t) ((tag, v) :: tm) s0 s hI1
        (Forall2.cons (FrameRel.same hst) (frames_mono hle1 htr)) hs (fun st' => agq (ag st' ((tag, v) :: t)))
        (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
        res hres
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := returnsC_done hdn (frameOK_goes F (fitsS_lazyReg g0.re) hh1 Gq)
      exact ⟨r, mink_n11d_stop hst hmh hmq, ton, st2, hI2, Needs.le_trans hle1 hle2, by rw [ecopy, e1]; exact e2, hrel⟩
    | one b =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | two tr =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩

end

end Comp
end SkaModel
end Formalization
