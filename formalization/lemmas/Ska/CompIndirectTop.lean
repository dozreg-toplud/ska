import lemmas.Ska.CompIndirectRun

/-!
# The whole-subject code at its entry, for any run

README Gaps 12.11 (fifteenth session).  `finishLU_compDone` (`CompWholeTop.lean`)
takes the run for `%done` from `gen0` with `RunOKV`, whose `sem` is the
value of a pure nomm.  `finishTop_gen` is its proof with the run's facts
apart: the fields of `RunOKV` that are about the state (`TopS`), and the
`sem` as any property `Φ` of what the code does from the run's jump, on
every program that agrees with the run's blocks.  The code of a call meets
it with `Φ` the forward contract against the oracle.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The fields of `RunOKV` for `%done` from `gen0` that are about the state:
all but `sem`, `nec` and `size`, with `ent` as the jump having no arguments. -/
structure TopS (g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext gen0 g1
  grow : GrowU gen0 g1
  cfr : CondFresh gen0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  args : nex.th.args = []
  regs : ∀ r, NMem nex.laz.sure.ned r → (gen0 : Gen Map).re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (gen0 : Gen Map).re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, (gen0 : Gen Map).bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none

/-- **The whole-subject code at its entry, for any run with `TopS`**: the
input need is `this`, and entered on the subject whole the code does what
the run's code does from its jump, for any property `Φ` that the run's
code has on every program agreeing with its blocks (`hsem`) and that a
crash with the caller's trace has where the subject does not fit the run's
need (`hnec`). -/
theorem finishTop_gen (lib : Lib) {g1 : Gen Map} {nex : NextL S} (R : TopS g1 nex)
    (Φ : (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop)
    (hsem : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      AgreeU lib O c gul st t cf ned gen0 g1 nex.laz s s → (∀ r, NMem ned r → g1.re ≤ r) →
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
  have hlab : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => Nat.lt_trans (R.labs e he).2.1 lt0
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
  have hE : ∀ e ∈ entries nex.laz, ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
      HoonMap.get g4.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧
      KernP g1.re g4.cond (g1.re + 1) g4.re e.1 e.2.sure A := by
    intro e he
    obtain ⟨_, _, th, hth⟩ := R.labs e he
    obtain ⟨A, hA, P⟩ := W.at_ e (List.mem_cons_of_mem _ he)
    refine ⟨A, th, hth, ?_, P⟩
    have := hA [] (Termin.hop th) (by
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
      obtain ⟨A, th, h1', h4', _⟩ := hE e he
      rw [h4'] at hk; cases hk
      exact ⟨⟨[], [], Termin.hop th⟩, by rw [eblk, if_neg e1]; exact h1', rfl⟩
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
  have ag : AgreeU lib O c1 gul st t g4.cond (Need.this g1.re) gen0 g1 nex.laz s s := by
    refine ⟨fun o' _ u hnl => ?_, fun e he => ?_⟩
    · rw [hag o', hO o' (by omega) hnl]
    · obtain ⟨A, th, h1', h4', P⟩ := hE e he
      refine ⟨A.map (renPole (unproxy g4.cond)), th, h1', ?_, ?_⟩
      · rw [hag, h4']; simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin]
      · obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P
        have l0' : g1.re + 1 ≤ lo0 := l0
        have regsE : ∀ x, NMem e.2.sure.ned x → x < g1.re := fun x hx => ((R.eregs e he).2 x hx).2
        have KS := sem (by omega) (R.eregs e he).1 regsE (unproxy g4.cond) (unproxy_none u4r)
          (fun x hx => unproxy_none (by rw [ag4 x (by have := regsE x hx; omega)]; exact R.econd e he x hx))
          (fun _ _ => rfl)
        intro R hR
        obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st t R s hR
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

/-! ## The blocks before the runs of the indirect call -/

/-- **The blocks of the indirect call before its two runs, from `gen0`**:
`+simple-next` emits `[%don 0]` at `1`, `+kerf` the hop at `2` to it with
the move of the product register `1` into `0`, and the `%nok` block at `3`
reads the subject from `2`, the formula from `3` and puts the product in
`1`. -/
theorem indirect_prefix {nex0 : NextL S} {g1 g2 g3 : Gen Map} {out pro o : Nat}
    (h1 : simpleNextL (CGoalL.done : CGoalL S) (gen0 : Gen Map) = some (nex0, g1))
    (h2 : kerf nex0 g1 = some ((out, pro), g2))
    (h3 : emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3)) :
    out = 2 ∧ pro = 1 ∧ o = 3 ∧ g2.re = 2 ∧ g3.re = 4 ∧ g3.bo = 4 ∧ g3.drop = false ∧
    (∀ k, HoonMap.get g3.cond k = Option.none) ∧
    HoonMap.get g3.blocks 1 = some ⟨[], [], Termin.don 0⟩ ∧
    HoonMap.get g3.blocks 2 = some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩ ∧
    HoonMap.get g3.blocks 3 = some ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩ ∧
    GrowU gen0 g3 ∧ Clear g3 := by
  simp only [simpleNextL] at h1
  obtain ⟨r, ga, ha, h1⟩ := bind_some h1
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨od, gb, hb, h1⟩ := bind_some h1
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  unfold kerf at h2
  obtain ⟨o', gc, hc, h2⟩ := bind_some h2
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨r', gd, hd, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
  simp only [kern] at hd
  obtain ⟨r1, ge, he, hd⟩ := bind_some hd
  rw [re_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have te : HoonSet.toList (HoonSet.empty : S) = [] := List.eq_nil_iff_forall_not_mem.mpr HoonSet.mem_empty
  simp [Gen.emitted, gen0, get, getThe, MonadStateOf.get, walkLazy_ofSure] at hd
  obtain ⟨gx, gy, hx, hd⟩ := bind_some hd
  simp only [StateT.get, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  simp only [Bool.false_eq_true, ↓reduceIte, sureRequireLook, te, List.foldl_nil] at hd
  obtain ⟨u, gz, hz, hd⟩ := bind_some hd
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  rw [map_apply] at hd
  simp [noSoft, kernNeed, kernLoop, addOps, HoonMap.get_put, bind_some] at hd
  obtain ⟨rfl, rfl⟩ := hd
  rw [emit_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have gb : ∀ k, HoonMap.get (HoonMap.put (HoonMap.put (HoonMap.put (HoonMap.put (HoonMap.empty : Map Blob) 1
      (⟨[], [], Termin.don 0⟩ : Blob)) 2 ⟨[], [], Termin.hop (jmp0 1)⟩) 2 ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩) 3
      ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩) k =
      if k = 3 then some ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩ else
      if k = 2 then some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩ else
      if k = 1 then some ⟨[], [], Termin.don 0⟩ else Option.none := fun k => by
    simp only [HoonMap.get_put, HoonMap.get_empty]
    by_cases e3 : k = 3 <;> by_cases e2 : k = 2 <;> simp [e3, e2]
  simp only [Gen.emitted, gen0, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, true_and]
  refine ⟨fun k => HoonMap.get_empty k, by rw [gb]; rfl, by rw [gb]; rfl, by rw [gb]; rfl, ?_,
    fun k hk => by rw [gb, if_neg (by simp only at hk; omega), if_neg (by simp only at hk; omega),
      if_neg (by simp only at hk; omega)]⟩
  refine ⟨by simp, rfl, fun k b _ hk => by simp [HoonMap.get_empty] at hk, fun k b' hb' => Or.inr ?_⟩
  rw [gb] at hb'
  simp only
  by_cases e3 : k = 3
  · subst e3; simp at hb'; subst hb'
    refine ⟨by omega, by omega, fun j hj => ?_⟩
    simp only [finJumps, List.mem_singleton] at hj; subst hj
    refine ⟨by simp [jmp0], Or.inl ⟨by simp [jmp0], fun t ⟨b, j, hb, hf, ht, hlt⟩ => ?_⟩⟩
    have hb2 : some b = some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩ := by rw [← hb, gb]; rfl
    cases hb2
    simp only [Termin.hop.injEq] at hf; subst hf; simp [jmp0] at ht; omega
  by_cases e2 : k = 2
  · subst e2; simp at hb'; subst hb'
    refine ⟨by omega, by omega, fun j hj => ?_⟩
    simp only [finJumps, List.mem_singleton] at hj; subst hj
    refine ⟨by simp [jmp0], Or.inl ⟨by simp [jmp0], fun t ⟨b, j, hb, hf, ht, hlt⟩ => ?_⟩⟩
    have hb2 : some b = some ⟨[], [], Termin.don 0⟩ := by rw [← hb, gb]; rfl
    cases hb2
    simp at hf
  by_cases e1 : k = 1
  · subst e1; simp at hb'; subst hb'
    exact ⟨by omega, by omega, fun j hj => by simp [finJumps] at hj⟩
  · simp [e3, e2, e1] at hb'

end Comp
end SkaModel
end Formalization
