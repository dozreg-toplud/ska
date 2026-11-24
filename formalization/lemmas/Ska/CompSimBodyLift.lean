import lemmas.Ska.CompSimBody

/-!
# Existing results move to goals whose entries have bodies: `LOKB`

README Gaps 12.23.  `SimB` (`CompSimBody.lean`) relates a state with extra
bodies to the stripped state; `simM_runLC` gives, for a nomm of `PlainN`,
the stripped run of every real run.  This file moves the relations along.

* `SimB` keeps every fact that reads only the labels, parameters and
  terminators of the blocks: `simB_upAt`, `SimB.upBelow`, `SimB.clear`,
  `SimB.condBelow`, `SimB.growU`, `SimB.entry`, `SimB.condFresh`.
* `RunOKLB.ofSim`: `RunOKLB` of the stripped run is `RunOKLB` of the real
  one, when the extra bodies sit at goal entries.  Nothing in the relation
  but `keep`, `labs`, `front` mentions a goal entry's body, and those take
  the extra body along (`front`'s `F ++ B`); `AgreeLB` and the `sem` clauses
  look only at the blocks the run made, where the bodies agree.
* `stripBl`, `stripG`, `simB_strip`: the stripped state of a real one, with
  the bodies at a list of labels removed.
* `LOKB x`: `LOKC` with bodies at the goal entries and `RunOKLB x`.
  `LOKC.toB`: every nomm of `PlainN` with `LOKC` meets `LOKB false`.
  `LOKB.up`, `LOKB.wrap`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## What `SimB` keeps -/

section Keep
variable {bd : Nat → List Pole}

theorem simB_get {g g' : Gen Map} (h : SimB bd g g') (k : Nat) :
    ∀ b', HoonMap.get g'.blocks k = some b' → HoonMap.get g.blocks k = some (addBody (bd k) b') := fun b' hb => by
  rw [h.blocks k, hb]; rfl

theorem simB_get' {g g' : Gen Map} (h : SimB bd g g') (k : Nat) :
    ∀ b, HoonMap.get g.blocks k = some b → ∃ b', HoonMap.get g'.blocks k = some b' ∧ b = addBody (bd k) b' :=
  fun b hb => by
    rw [h.blocks k] at hb
    obtain ⟨b', hb', e⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨b', hb', e.symm⟩

theorem simB_none {g g' : Gen Map} (h : SimB bd g g') (k : Nat) :
    HoonMap.get g.blocks k = Option.none ↔ HoonMap.get g'.blocks k = Option.none := by
  rw [h.blocks k]; simp

theorem simB_upAt {g g' : Gen Map} (h : SimB bd g g') (u t : Nat) : UpAt g.blocks u t ↔ UpAt g'.blocks u t := by
  constructor
  · rintro ⟨b, j, hb, hf, ht, hl⟩
    obtain ⟨b', hb', rfl⟩ := simB_get' h u b hb
    exact ⟨b', j, hb', hf, ht, hl⟩
  · rintro ⟨b', j, hb', hf, ht, hl⟩
    exact ⟨addBody (bd u) b', j, simB_get h u b' hb', hf, ht, hl⟩

theorem SimB.upBelow {g g' : Gen Map} (h : SimB bd g g') : UpBelow g ↔ UpBelow g' := by
  constructor
  · intro H u t hu; rw [← h.bo]; exact H u t ((simB_upAt h u t).mpr hu)
  · intro H u t hu; rw [h.bo]; exact H u t ((simB_upAt h u t).mp hu)

theorem SimB.clear {g g' : Gen Map} (h : SimB bd g g') : Clear g ↔ Clear g' := by
  constructor
  · intro H k hk; exact (simB_none h k).mp (H k (h.bo ▸ hk))
  · intro H k hk; exact (simB_none h k).mpr (H k (h.bo.symm ▸ hk))

theorem SimB.condBelow {g g' : Gen Map} (h : SimB bd g g') : CondBelow g ↔ CondBelow g' := by
  unfold CondBelow; rw [h.cond, h.re]

theorem SimB.condFresh {g0 g0' g1 g1' : Gen Map} (h0 : SimB bd g0 g0') (h1 : SimB bd g1 g1')
    (h : CondFresh g0' g1') : CondFresh g0 g1 := by
  unfold CondFresh at h ⊢; rw [h0.cond, h0.re, h1.cond, h1.re]; exact h

theorem SimB.fresh {g g' : Gen Map} (h : SimB bd g g') {j : Jmp} : Fresh g' j → Fresh g j := by
  rintro ⟨b', hb', hp, ha⟩
  exact ⟨addBody (bd j.there) b', simB_get h _ b' hb', hp, ha⟩

theorem SimB.entry {g g' : Gen Map} (h : SimB bd g g') {goal : CGoal S} {j : Jmp} :
    Entry g' goal j → Entry g goal j := fun e => e.imp (h.fresh) (fun x => x)

theorem SimB.jumpsU {g g' : Gen Map} (h : SimB bd g g') {k : Nat} {fin : Termin} :
    JumpsU g'.blocks g'.bo k fin → JumpsU g.blocks g.bo k fin := by
  intro H j hj
  obtain ⟨h1, h2⟩ := H j hj
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨a, b⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨a, fun t ht => b t ((simB_upAt h _ t).mp ht)⟩
  · exact Or.inr ⟨a, b, h.bo ▸ c, fun t ht => d t ((simB_upAt h _ t).mp ht)⟩

theorem SimB.growU {g0 g0' g1 g1' : Gen Map} (h0 : SimB bd g0 g0') (h1 : SimB bd g1 g1')
    (G : GrowU g0' g1') : GrowU g0 g1 := by
  refine ⟨by rw [h0.bo, h1.bo]; exact G.bo, by rw [h0.drop, h1.drop]; exact G.drop, fun k b hk hb => ?_,
    fun k b hb => ?_⟩
  · obtain ⟨b0', hb0', rfl⟩ := simB_get' h0 k b hb
    obtain ⟨b1', hb1', hp, hf⟩ := G.keep k b0' (h0.bo ▸ hk) hb0'
    exact ⟨addBody (bd k) b1', simB_get h1 k b1' hb1', hp, hf⟩
  · obtain ⟨b1', hb1', rfl⟩ := simB_get' h1 k b hb
    rcases G.new k b1' hb1' with ⟨b0', hb0', hp, hf⟩ | ⟨a, c, J⟩
    · exact Or.inl ⟨addBody (bd k) b0', simB_get h0 k b0' hb0', hp, hf⟩
    · exact Or.inr ⟨h0.bo ▸ a, h1.bo ▸ c, h1.jumpsU J⟩

end Keep

theorem map_addBody_nil (x : Option Blob) : x.map (addBody []) = x := by cases x <;> simp

/-! ## The relation moves to the real run -/

/-- **`RunOKLB` of the stripped run is `RunOKLB` of the real run**, when
the extra bodies sit at the goal's entries. -/
theorem RunOKLB.ofSim {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit} {x : Bool}
    {bd : Nat → List Pole} {g0 g0' g1 g1' : Gen Map} {nex : NextL S} (s0 : SimB bd g0 g0') (s1 : SimB bd g1 g1')
    (hX : ∀ o, o ∉ (entries L).map Prod.fst → bd o = [])
    (R : RunOKLB (Map := Map) lib P f L th Q x g0' g1' nex) : RunOKLB (Map := Map) lib P f L th Q x g0 g1 nex := by
  have e0r := s0.re
  have e0b := s0.bo
  have e1r := s1.re
  have e1b := s1.bo
  have r1 := R.re
  have r2 := R.bo
  have r3 := R.hi
  have hcf : ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ k, k < g1'.re → HoonMap.get cf k = HoonMap.get g1'.cond k := fun cf h k hk => by
    rw [← s1.cond]; exact h k (by omega)
  have agB : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cond : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeLB lib O c gul st t cond ned g0 g1 nex.laz s0 s → AgreeLB lib O c gul st t cond ned g0' g1' nex.laz s0 s :=
    fun {σ O c gul st t cond ned s0' s} ag => by
      refine ⟨fun o l u hn => ?_, fun e he l => ?_⟩
      · rw [ag.1 o (by omega) (by omega) hn, s1.blocks o, s0.above o (by omega), map_addBody_nil]
      · obtain ⟨A, B, th', h1, h2, h3⟩ := ag.2 e he (by omega)
        refine ⟨A, B, th', ?_, h2, by rw [← e1r]; exact h3⟩
        rw [s1.blocks, s0.above _ (by omega), map_addBody_nil] at h1
        exact h1
  refine ⟨by omega, by omega, by rw [s1.drop, s0.drop]; exact R.drop, fun o ho hn => ?_,
    s0.growU s1 R.grow, s0.condFresh s1 R.cfr, R.lo, by omega, s1.entry R.ent,
    fun r hr => by rw [e0r, e1r]; exact R.regs r hr, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => by rw [e0r, e1r]; exact (R.eregs e he).2 r hr⟩,
    fun e he => ?_, R.nodup, fun s v d w r hq hr => by rw [e0r, e1r]; exact R.dreg s v d w r hq hr, R.nec,
    fun r hr => by rw [s1.cond]; exact R.ncond r hr, fun e he r hr => by rw [s1.cond]; exact R.econd e he r hr,
    fun e he => ?_, ?_, ?_⟩
  · rw [s1.blocks o, R.keep o (by omega) hn, ← s0.blocks o]
  · obtain ⟨hl, B, th', hb⟩ := R.labs e he
    exact ⟨by rw [e0b, e1b]; exact hl, B ++ bd e.1, th', by rw [s1.blocks, hb]; rfl⟩
  · obtain ⟨F, hb, hf⟩ := R.front e he
    refine ⟨F, fun B fin h0 => ?_, fun cf h => ?_⟩
    · obtain ⟨b', hb', e'⟩ := simB_get' s0 e.1 _ h0
      rcases b' with ⟨p', B', f'⟩
      simp only [addBody, Blob.mk.injEq] at e'
      obtain ⟨rfl, rfl, rfl⟩ := e'
      have := hb B' fin (by simpa using hb')
      rw [s1.blocks, this]
      simp [addBody]
    · rw [e0r, e1r]; exact hf cf (hcf cf h)
  · intro cf h c ned σ Inv ν O n gul hS hF st t tm s0' s r hI htr hs hm ag hned regs hh hn
    rw [e0r]
    exact R.sem cf (hcf cf h) c ned σ Inv ν O n gul hS hF st t tm s0' s r hI htr hs hm (fun st' => agB (ag st'))
      (fun z hz => by rw [← e1r]; exact hned z hz) regs hh hn
  · intro cf h c ned σ Inv ν O gul hS hB st t tm s0' s hI htr hs ag hned regs hh hn res hres
    rw [e0r]
    exact R.semB cf (hcf cf h) c ned σ Inv ν O gul hS hB st t tm s0' s hI htr hs (fun st' => agB (ag st'))
      (fun z hz => by rw [← e1r]; exact hned z hz) regs hh hn res hres

/-! ## The stripped state -/

/-- The block `b` with its body removed. -/
def stripB (b : Blob) : Blob := ⟨b.par, [], b.fin⟩

/-- One step of the stripping, reading the original map `bl`. -/
def stripStep (bl : Map Blob) (m : Map Blob) (o : Nat) : Map Blob :=
  match HoonMap.get bl o with
  | some b => HoonMap.put m o (stripB b)
  | Option.none => m

/-- The blocks `bl` with the bodies at the labels `X` removed. -/
def stripBl (X : List Nat) (bl : Map Blob) : Map Blob := X.foldl (stripStep bl) bl

theorem get_foldl_stripStep (bl : Map Blob) : ∀ (X : List Nat) (acc : Map Blob) (k : Nat),
    HoonMap.get (X.foldl (stripStep bl) acc) k =
      if k ∈ X ∧ (HoonMap.get bl k).isSome then (HoonMap.get bl k).map stripB else HoonMap.get acc k
  | [], acc, k => by simp
  | o :: X, acc, k => by
    rw [List.foldl_cons, get_foldl_stripStep bl X]
    unfold stripStep
    by_cases hk : k ∈ X ∧ (HoonMap.get bl k).isSome
    · rw [if_pos hk, if_pos ⟨List.mem_cons_of_mem _ hk.1, hk.2⟩]
    · rw [if_neg hk]
      by_cases e : k = o
      · subst e
        cases hb : HoonMap.get bl k with
        | none => simp [hb]
        | some b => simp [HoonMap.get_put]
      · have hk' : ¬ (k ∈ o :: X ∧ (HoonMap.get bl k).isSome) := by
          rintro ⟨h1, h2⟩
          rcases List.mem_cons.mp h1 with h1 | h1
          · exact e h1
          · exact hk ⟨h1, h2⟩
        rw [if_neg hk']
        cases HoonMap.get bl o with
        | none => rfl
        | some b => simp [HoonMap.get_put, e]

theorem get_stripBl (X : List Nat) (bl : Map Blob) (k : Nat) :
    HoonMap.get (stripBl X bl) k = if k ∈ X then (HoonMap.get bl k).map stripB else HoonMap.get bl k := by
  rw [stripBl, get_foldl_stripStep]
  by_cases hk : k ∈ X
  · cases hb : HoonMap.get bl k with
    | none => simp [hk, hb]
    | some b => simp [hk, hb]
  · simp [hk]

/-- The stripped state. -/
def stripG (X : List Nat) (g : Gen Map) : Gen Map := { g with blocks := stripBl X g.blocks }

/-- The bodies removed. -/
def stripBd (X : List Nat) (g : Gen Map) (k : Nat) : List Pole :=
  if k ∈ X then ((HoonMap.get g.blocks k).map Blob.body).getD [] else []

theorem simB_strip {X : List Nat} {g : Gen Map} (hX : ∀ o ∈ X, o < g.bo) : SimB (stripBd X g) g (stripG X g) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun k => ?_, fun k hk => ?_⟩
  · simp only [stripG, get_stripBl, stripBd]
    by_cases h : k ∈ X
    · rw [if_pos h, if_pos h]
      cases hb : HoonMap.get g.blocks k with
      | none => rfl
      | some b => cases b; simp [stripB, addBody]
    · rw [if_neg h, if_neg h, map_addBody_nil]
  · simp only [stripBd]
    rw [if_neg (fun h => by have := hX k h; omega)]

theorem stripG_get_mem {X : List Nat} {g : Gen Map} {k : Nat} (hk : k ∈ X) {B : List Pole} {fin : Termin}
    (hb : HoonMap.get g.blocks k = some ⟨[], B, fin⟩) : HoonMap.get (stripG X g).blocks k = some ⟨[], [], fin⟩ := by
  simp [stripG, get_stripBl, hk, hb, stripB]

theorem stripBd_out {X : List Nat} {g : Gen Map} {k : Nat} (hk : k ∉ X) : stripBd X g k = [] := by
  simp [stripBd, hk]

/-! ## Runs under a lazy goal with bodies -/

/-- **`LOKC` with bodies at the goal entries and `RunOKLB x`**, from a state
where the goal's jump is at none of its entries, and the result's jump at
none of the result's entries. -/
structure LOKB (x : Bool) (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLB (Map := Map) lib P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst

/-- **`LOKC` of a nomm of `PlainN` gives `LOKB false`**: strip the goal
entries' bodies (`simB_strip`), run from the stripped state
(`simM_runLC`), take `LOKC` there, lift (`RunOKLC.toB`) and move the
relation back (`RunOKLB.ofSim`). -/
theorem LOKC.toB {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (hp : PlainN nm)
    (h : LOKC (S := S) (Map := Map) lib env P f nm) : LOKB (S := S) (Map := Map) false lib env P f nm := by
  refine ⟨h.clean, fun {sup L th region g0 g1 nex} hc b0 d0 hu hcl hcb h1 h2 ha ht hsd hsl hlab hnd hed hr => ?_⟩
  let X := (entries L).map Prod.fst
  have hX : ∀ o ∈ X, o < g0.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    exact (hlab e he).1
  have s0 := simB_strip (Map := Map) hX
  obtain ⟨g1', hr', s1⟩ := (simM_runLC env nm hp sup (CGoalL.next L th) region).sim _ _ _ _ _ s0 hr
  have L0 := h.run (g0 := stripG X g0) (g1 := g1') hc b0 d0 (s0.upBelow.mp hu) (s0.clear.mp hcl) (s0.condBelow.mp hcb) h1 h2 ha hsd hsl
    (fun e he => by
      obtain ⟨hlt, B, th', hb⟩ := hlab e he
      exact ⟨hlt, th', stripG_get_mem (List.mem_map_of_mem he) hb⟩) hnd hed hr'
  obtain ⟨⟨Q, R⟩, j⟩ := L0
  have RB := RunOKLB.ofSim s0 s1 (fun o ho => stripBd_out ho) R.toB
  refine ⟨⟨Q, RB⟩, fun hm => ?_⟩
  obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
  rcases (R.labs e he).1 with h | h
  · obtain ⟨e0, he0, e2⟩ := List.mem_map.mp h
    have := (hlab e0 he0).1
    rcases j with j | j
    · exact ht (by rw [← j, ← e1, ← e2]; exact List.mem_map_of_mem he0)
    · have : g0.bo ≤ e0.1 := by rw [e2, e1]; exact j
      omega
  · omega

/-- **The weakening of `x`.** -/
theorem LOKB.up {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : LOKB (S := S) (Map := Map) false lib env P f nm) (x : Bool) : LOKB (S := S) (Map := Map) x lib env P f nm :=
  ⟨h.clean, fun hc b0 d0 hu hcl hcb h1 h2 ha ht hsd hsl hlab hnd hed hr => by
    obtain ⟨⟨Q, R⟩, j⟩ := h.run hc b0 d0 hu hcl hcb h1 h2 ha ht hsd hsl hlab hnd hed hr
    exact ⟨⟨Q, R.up (fun r hr => (hsl r hr).1) x⟩, j⟩⟩

theorem LOKB.wrap {x : Bool} {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f f' : Noun} {nm : Nomm}
    (W : WrapRel lib P f f') (B : LOKB (S := S) (Map := Map) x lib env P f nm) :
    LOKB (S := S) (Map := Map) x lib env P f' nm :=
  ⟨B.clean, fun hc b0 d0 hu hcl hcb h1 h2 ha ht hsd hsl hlab hnd hed h => by
    obtain ⟨⟨Q, R⟩, j⟩ := B.run hc b0 d0 hu hcl hcb h1 h2 ha ht hsd hsl hlab hnd hed h
    exact ⟨⟨Q, R.wrap W⟩, j⟩⟩

end Comp
end SkaModel
end Formalization
