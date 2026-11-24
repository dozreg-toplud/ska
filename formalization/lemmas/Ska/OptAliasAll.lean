import lemmas.Ska.OptAliasInv
import lemmas.Ska.OptMiddleWalk

/-!
# The walk invariant of `+alias` over executions

The induction over `topo` that assembles the pieces of `OptAliasInv.lean`
along executions of the code before.  **`AWInv`** is the invariant at the
point `pre` of the walk with state `g`: `ARev`, `OldW`, every edge of a block
not walked yet still listed in `rev` (`pend`), and at the end of every walked
jumping block `q` that an execution from the entry reaches, **`EndOK`**: the
facts, immediates and block after of `q` are stored, the registers the end
after reads are in `DefW bl pre`, `AOK` and `ABInv` hold with the global `old`
of `g` and `Done` = `DoneE bl pre p bq` for the path `p` the execution took
(`epath`), and the jump the end before takes is listed in `rev` and is taken
by the end after, to the same block, with arguments of the same values.

* **`awa_steps_last`**, **`awa_inblock_passed`**: an execution from the entry
  either stays in block `0`, or ends with a jump into the block it stands in
  and then runs its pass and a prefix of its ops (`OpsRun`, through `as_sem`).
* **`awa_start_entry`**, **`awa_start_jump`**: `AOK` and `ABInv` at the start
  of the block, from `entryInfo` or from `EndOK` at the predecessor taken
  (`aedge_aok`, `aedge_abinv`, `awi_edge_side`, `aedge_pass`).
* **`awa_end`**: `EndOK` at the end of the block just walked (`awi_bodyOK`,
  `as_body`, `afn_jump`).
* **`awa_rebase`**: `EndOK` at a block walked before survives one more block
  of the walk (`awi_frame_step`, `awi_old_step`, `awi_self`).
* **`awa_step`**, **`awa_walk`**, **`alias_walk_inv`**: the induction.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-! ## Small facts on bodies, `rev` and ends -/

theorem awa_bodyDone_base {Cl : Nat → Prop} : ∀ (l : List Pole) (D : Nat → Prop) (x : Nat), D x → bodyDone Cl l D x
  | [], _, _, h => h
  | _ :: l, _, x, h => awa_bodyDone_base l _ x (Or.inl h)

theorem awa_bodyDone_dst {Cl : Nat → Prop} : ∀ (l : List Pole) (D : Nat → Prop) (x : Nat),
    x ∈ l.filterMap aliasDst → Cl x → bodyDone Cl l D x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | op :: l, D, x, h, hc => by
    simp only [bodyDone]
    rw [List.filterMap_cons] at h
    split at h
    · exact awa_bodyDone_dst l _ x h hc
    · rename_i e heq
      rcases List.mem_cons.mp h with rfl | h
      · exact awa_bodyDone_base l _ _ (Or.inr ⟨heq, hc⟩)
      · exact awa_bodyDone_dst l _ x h hc

theorem awa_bodyDef_cases : ∀ (l : List Pole) (D : Nat → Prop) (x : Nat), bodyDef l D x →
    D x ∨ x ∈ l.filterMap aliasDst
  | [], _, _, h => Or.inl h
  | op :: l, D, x, h => by
    rcases awa_bodyDef_cases l _ x h with (h | h) | h
    · exact Or.inl h
    · right; rw [List.filterMap_cons, h]; exact List.mem_cons_self
    · right; rw [List.filterMap_cons]; split
      · exact h
      · exact List.mem_cons_of_mem _ h

theorem awa_abinv_mono {st : ABody} {Def Def' Done Done' Cl : Nat → Prop} (hi : ABInv st Def Done Cl)
    (hD : ∀ x, Def x → Def' x) (hDo : ∀ x, Done' x → Done x) : ABInv st Def' Done' Cl :=
  ⟨fun n r hr => hD r (hi.imm n r hr), ab_loc_mono hi.loc hD, fun d hd => hD _ (hi.old d (hDo d hd)),
    fun d hd => hD d (hi.done d (hDo d hd)), fun d hn hc => hi.self d (fun h => hn (hD d h)) hc⟩

theorem awa_del_keep {rev : Nat → List Nat} {k o x p : Nat} (hp : p ∈ rev x) (hne : p ≠ o) :
    p ∈ delJu rev k o x := by
  unfold delJu updA
  split
  · rename_i e; subst e; exact (List.mem_erase_of_ne hne).mpr hp
  · exact hp

theorem awa_drop_keep {o p x : Nat} (hne : p ≠ o) : ∀ (js : List Jmp) (rev : Nat → List Nat), p ∈ rev x →
    p ∈ (js.foldl (fun acc j => delJu acc j.there o) rev) x
  | [], _, hp => hp
  | _ :: js, _, hp => awa_drop_keep hne js _ (awa_del_keep hp hne)

/-- `aliasFin` deletes from `rev` only the block it ends. -/
theorem awa_fin_keep {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r) {x p : Nat}
    (hp : p ∈ rev x) (hne : p ≠ o) : p ∈ r.2.1 x := by
  have fold : ∀ go cut, p ∈ (aliasFold rev o go cut).2.1 x := by
    intro go cut; unfold aliasFold; split
    · exact hp
    · exact awa_del_keep hp hne
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact fold _ _
      · split at e
        · subst e; exact fold _ _
        · subst e; exact hp
  | eqq l r' z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; exact hp
      · cases h; exact fold _ _
  | brn s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · subst e; exact hp
        · subst e; exact hp
      · subst e; exact fold _ _
      · subst e; exact fold _ _
      · subst e; exact awa_del_keep (awa_del_keep hp hne) hne
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact hp
      · subst e; exact fold _ _
      · subst e; exact fold _ _
  | hop t => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp
  | lti => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hp

/-- **A block of the walk deletes from `rev` only itself.** -/
theorem awa_rev_keep {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') {x p : Nat} (hp : p ∈ g.rev x) (hne : p ≠ o) : p ∈ g'.rev x := by
  unfold aliasBlock at h
  dsimp only at h
  split at h
  · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact awa_drop_keep hne _ _ hp
  · obtain ⟨info, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨imms, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨edges, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨loc0, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rb, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rf, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    exact awa_fin_keep hf hp hne

/-- **The registers the end after reads are `old` of those the end before
reads.** -/
theorem awa_fin_reads {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r)
    (hnl : ∀ n s z o', fin ≠ Termin.lti n s z o') : ∀ x ∈ Path.finReads r.1, ∃ y ∈ Path.finReads fin, x = old y := by
  have fold : ∀ go cut, ∀ x ∈ Path.finReads (aliasFold rev o go cut).1, ∃ y ∈ Path.finReads fin, x = old y := by
    intro go cut x hx; simp [aliasFold, Path.finReads] at hx
  have one : ∀ s, s ∈ Path.finReads fin → ∀ x ∈ [old s], ∃ y ∈ Path.finReads fin, x = old y := by
    intro s hs x hx; exact ⟨s, hs, List.mem_singleton.mp hx⟩
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact fold _ _
      · split at e
        · subst e; exact fold _ _
        · subst e; exact one s (by simp [Path.finReads])
  | eqq l r' z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h
        intro x hx
        simp only [Path.finReads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨l, by simp [Path.finReads], rfl⟩
        · exact ⟨r', by simp [Path.finReads], rfl⟩
      · cases h; exact fold _ _
  | brn s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · subst e; exact one s (by simp [Path.finReads])
        · subst e; exact one s (by simp [Path.finReads])
      · subst e; exact fold _ _
      · subst e; exact fold _ _
      · subst e; intro x hx; simp [Path.finReads] at hx
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact one s (by simp [Path.finReads])
      · subst e; exact fold _ _
      · subst e; exact fold _ _
  | hop t =>
    simp only [aliasFin, Option.some.injEq] at h; subst h; intro x hx; simp [Path.finReads] at hx
  | jmp a v =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx
    simp only [Path.finReads, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  | jmf a v n =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx
    simp only [Path.finReads, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  | jsp a s => simp only [aliasFin, Option.some.injEq] at h; subst h; exact one s (by simp [Path.finReads])
  | jsf a s n => simp only [aliasFin, Option.some.injEq] at h; subst h; exact one s (by simp [Path.finReads])
  | don s => simp only [aliasFin, Option.some.injEq] at h; subst h; exact one s (by simp [Path.finReads])
  | bom u => simp only [aliasFin, Option.some.injEq] at h; subst h; intro x hx; simp [Path.finReads] at hx
  | lti n s z o' => exact absurd rfl (hnl n s z o')

/-- The value an argument passes (`~` and a missing argument pass none). -/
def argV (R : Nat → Option Noun) (a : Option (Option Nat)) : Option Noun := a.bind fun a => a.bind R

theorem awa_argV (R : Nat → Option Noun) (a : Option (Option Nat)) :
    (match a with | some (some u) => R u | _ => none) = argV R a := by
  rcases a with _ | _ | u <;> rfl

theorem awa_pass_nil {par : List Nat} {regs R : Map (Option Noun)} (h : evalPass [] par regs = some R) :
    par = [] ∧ R = regs := by
  unfold evalPass at h
  split at h
  · simp only [evalPassLoop] at h
    split at h
    · rename_i e; exact ⟨e, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem awa_pass_empty (regs : Map (Option Noun)) : evalPass [] [] regs = some regs := by
  simp [evalPass, evalPassLoop]

/-! ## Executions: the path taken, the last jump, the steps inside a block -/

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- The path of blocks an execution with edges `es` took, the last block
left first. -/
def epath (es : List (Nat × Nat)) : List Nat := (es.map Prod.fst).reverse

theorem awa_epath_snoc (es : List (Nat × Nat)) (a b : Nat) : epath (es ++ [(a, b)]) = a :: epath es := by
  simp [epath]

theorem awa_steps_at {x y : Path.Cfg σ Map} {es : List (Nat × Nat)} (h : Path.Steps lib O c gul x es y) :
    ∀ {p : List Nat}, ACfgAt c.blocks x p → ACfgAt c.blocks y (epath es ++ p) := by
  induction h with
  | refl => intro p hx; simpa [epath] using hx
  | step s _ ih =>
    intro p hx
    rcases awi_step_at s hx with ⟨rfl, -, hy⟩ | ⟨rfl, hy, -⟩
    · simpa [epath] using ih hy
    · simpa [epath] using ih hy

/-- **The path of an execution from the entry** is `epath` of its edges. -/
theorem awa_entry_at {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map}
    (h : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y) :
    ACfgAt c.blocks y (epath es) := by
  obtain ⟨b0, hb0, hs⟩ := h
  simpa using awa_steps_at hs ⟨BPath.start, b0, 0, hb0, rfl, (List.drop_zero).symm, Or.inl rfl⟩

/-- **The last jump of an execution**: none, or a jump from a configuration
at the end of a block, followed by steps inside the block jumped to. -/
theorem awa_steps_last {x y : Path.Cfg σ Map} {es : List (Nat × Nat)} (h : Path.Steps lib O c gul x es y) :
    es = [] ∨ ∃ (es1 : List (Nat × Nat)) (x' : Path.Cfg σ Map) (j : Jmp) (b' : Blob),
      es = es1 ++ [(x'.lab, j.there)] ∧ Path.Steps lib O c gul x es1 x' ∧ x'.params = [] ∧ x'.b.par = [] ∧
      x'.b.body = [] ∧ Path.taken x'.regs x'.b.fin = some j ∧ HoonMap.get c.blocks j.there = some b' ∧
      Path.Steps lib O c gul ⟨j.there, b', j.args, x'.regs, x'.t, x'.st⟩ [] y := by
  induction h with
  | refl => exact Or.inl rfl
  | step s rest ih =>
    rcases ih with e | ⟨es1, x', j, b', e, h1, h2⟩
    · subst e
      cases s with
      | pass _ _ => exact Or.inl rfl
      | op _ _ _ _ => exact Or.inl rfl
      | @jump j b' hp hq hb ht hb' =>
        exact Or.inr ⟨[], _, j, b', rfl, Path.Steps.refl _, hp, hq, hb, ht, hb', rest⟩
    · subst e
      exact Or.inr ⟨_ ++ es1, x', j, b', by rw [List.append_assoc], Path.Steps.step s h1, h2⟩

/-- **The steps inside a block**: none yet, or the pass and a prefix of the
ops, whose values meet `OpsRun`. -/
theorem awa_inblock {z y : Path.Cfg σ Map} {es : List (Nat × Nat)} (h : Path.Steps lib O c gul z es y)
    (he : es = []) :
    y.lab = z.lab ∧ y.b.fin = z.b.fin ∧
      ((y.params = z.params ∧ y.b.par = z.b.par ∧ y.b.body = z.b.body ∧ y.regs = z.regs) ∨
       (y.params = [] ∧ y.b.par = [] ∧ ∃ k R', evalPass z.params z.b.par z.regs = some R' ∧
          y.b.body = z.b.body.drop k ∧
          OpsRun (z.b.body.take k) (fun x => read x R') (fun x => read x y.regs))) := by
  induction h with
  | refl => exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  | @step x w y e es s rest ih =>
    obtain ⟨he1, he2⟩ := List.append_eq_nil_iff.mp he
    obtain ⟨i1, i2, i3⟩ := ih he2
    cases s with
    | @pass R hne hR =>
      refine ⟨i1, i2, Or.inr ?_⟩
      rcases i3 with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, k, R', a3, a4, a5⟩
      · refine ⟨a1, a2, 0, R, hR, by simpa using a3, ?_⟩
        rw [List.take_zero, a4]; exact OpsRun.nil _
      · rw [awa_pass_empty] at a3
        cases a3
        exact ⟨a1, a2, k, _, hR, a4, a5⟩
    | @op p rest' n R t' st' hp hq hb hpole =>
      refine ⟨i1, i2, Or.inr ?_⟩
      have hsem := as_sem hpole
      rcases i3 with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, k, R', a3, a4, a5⟩
      · refine ⟨a1.trans hp, a2.trans hq, 1, x.regs, by rw [hp, hq]; exact awa_pass_empty _, ?_, ?_⟩
        · rw [hb, a3]; rfl
        · rw [hb, a4]; exact OpsRun.cons hsem (OpsRun.nil _)
      · simp only [hp, hq] at a3
        rw [awa_pass_empty] at a3
        cases a3
        refine ⟨a1, a2, k + 1, x.regs, by rw [hp, hq]; exact awa_pass_empty _, ?_, ?_⟩
        · rw [hb, a4]; rfl
        · rw [hb]; exact OpsRun.cons hsem a5
    | jump _ _ _ _ _ => simp at he1

/-- The steps inside a block up to a configuration that passed. -/
theorem awa_inblock_passed {z y : Path.Cfg σ Map} (h : Path.Steps lib O c gul z [] y) (hp : y.params = [])
    (hq : y.b.par = []) :
    y.lab = z.lab ∧ y.b.fin = z.b.fin ∧ ∃ k R', evalPass z.params z.b.par z.regs = some R' ∧
      y.b.body = z.b.body.drop k ∧ OpsRun (z.b.body.take k) (fun x => read x R') (fun x => read x y.regs) := by
  obtain ⟨i1, i2, i3⟩ := awa_inblock h rfl
  refine ⟨i1, i2, ?_⟩
  rcases i3 with ⟨a1, a2, a3, a4⟩ | ⟨-, -, r⟩
  · refine ⟨0, z.regs, by rw [← a1, ← a2, hp, hq]; exact awa_pass_empty _, by rw [a3]; rfl, ?_⟩
    rw [List.take_zero, a4]; exact OpsRun.nil _
  · exact r

end

/-! ## The invariant at the end of a walked block -/

section
variable [MapKeys Map]

/-- **The walk invariant at the end of a walked jumping block** `q` (block
`bq` before), reached along the path `p` with the values `R`, at the point
`pre` of the walk with state `g`. -/
def EndOK (bl : Map Blob) (pre : List Nat) (g : AGen Map) (q : Nat) (p : List Nat) (bq : Blob)
    (R : Nat → Option Noun) : Prop :=
  ∃ lq mq pb, g.info q = some lq ∧ g.imms q = some mq ∧ HoonMap.get g.new q = some pb ∧
    (∀ x ∈ Path.finReads pb.fin, DefW bl pre x) ∧
    AOK ⟨g.old, lq, mq⟩ R (DoneE bl pre p bq) ∧
    ABInv ⟨g.old, lq, mq⟩ (DefW bl pre) (DoneE bl pre p bq) (ClR bl) ∧
    ∀ j, takenR R bq.fin = some j → q ∈ g.rev j.there ∧
      ∃ j', takenR R pb.fin = some j' ∧ j'.there = j.there ∧ ∀ k : Nat, argV R j'.args[k]? = argV R j.args[k]?

/-- **`AOK` and `ABInv` at the start of block `0`** at the entry. -/
theorem awa_start_entry {bl : Map Blob} (hS : AliasSSAB bl) {pre l : List Nat} (ht : TopoOK bl (pre ++ l))
    {g : AGen Map} (hw : OldW bl pre g) (nargs : Nat) {b0 : Blob} (hpar : b0.par = []) (R : Nat → Option Noun) :
    AOK ⟨g.old, entryInfo nargs, fun _ => []⟩ R (DoneS bl pre [] b0) ∧
      ABInv ⟨g.old, entryInfo nargs, fun _ => []⟩ (fun x => DefW bl pre x ∨ x ∈ b0.par) (DoneS bl pre [] b0)
        (ClR bl) := by
  have hfix : ∀ d, d ∉ allDefs bl → g.old d = d := fun d hd => Classical.byContradiction fun hne => by
    obtain ⟨o, -, -, b, hb, hm⟩ := hw d hne
    exact hd (bdef_allDefs hb (List.mem_append_right _ hm))
  have hD : ∀ d, DoneS bl pre [] b0 d → d ∉ allDefs bl := fun d hd => by
    rcases hd.1 with h | h | ⟨o', ho', -⟩
    · exact h
    · rw [hpar] at h; cases h
    · cases ho'
  refine ⟨⟨fun n r hr => absurd hr List.not_mem_nil, ast_entry nargs, fun d hd => ?_⟩,
    ⟨fun n r hr => absurd hr List.not_mem_nil, ⟨fun r i x hr hx => ?_, fun r i hr => ?_⟩,
      fun d hd => ?_, fun d hd => Or.inl (Or.inl (hD d hd)),
      fun d hn hc => awi_self hS ht hw hc (fun h => hn (Or.inl h))⟩⟩
  · show R (g.old d) = R d
    rw [hfix d (hD d hd)]
  · simp only [entryInfo] at hr
    split at hr
    · cases hr; exact absurd hx ab_nm_empty
    · cases hr
  · simp only [entryInfo] at hr
    split at hr
    · cases hr; exact Or.inl rfl
    · cases hr
  · show DefW bl pre (g.old d) ∨ g.old d ∈ b0.par
    rw [hfix d (hD d hd)]; exact Or.inl (Or.inl (hD d hd))

/-- **`AOK` and `ABInv` at the start of a block entered by a jump**, from
`EndOK` at the end of the block left. -/
theorem awa_start_jump {bl : Map Blob} (hS : AliasSSAB bl) (hpn : ParNodup bl) {pre l : List Nat}
    (ht : TopoOK bl (pre ++ l)) {g : AGen Map} (hw : OldW bl pre g) {o q : Nat} {p : List Nat} {bo bq : Blob}
    (hRo : Reach bl o) (hbo : HoonMap.get bl o = some bo) (hopre : o ∉ pre) (hbq : HoonMap.get bl q = some bq)
    {regs Rp : Map (Option Noun)} {lq : AInfo} {mq : AImms} {pb : Blob}
    (hlq : g.info q = some lq) (hmq : g.imms q = some mq) (hpb : HoonMap.get g.new q = some pb)
    (hfr : ∀ x ∈ Path.finReads pb.fin, DefW bl pre x)
    (hok : AOK ⟨g.old, lq, mq⟩ (fun x => read x regs) (DoneE bl pre p bq))
    (hab : ABInv ⟨g.old, lq, mq⟩ (DefW bl pre) (DoneE bl pre p bq) (ClR bl))
    (hq : q ∈ g.rev o) {j j' : Jmp} (hj' : takenR (fun x => read x regs) pb.fin = some j') (hjo : j'.there = o)
    (hargs : ∀ k : Nat, argV (fun x => read x regs) j'.args[k]? = argV (fun x => read x regs) j.args[k]?)
    (hpass : evalPass j.args bo.par regs = some Rp)
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : aliasStart g o (g.rev o) = some info) (him : aliasStartImms g (g.rev o) = some imms)
    (hed : aliasEdges g o (g.rev o) = some edges) (hpa : aliasPars g bo.par edges info = some loc0) :
    AOK ⟨g.old, loc0, imms⟩ (fun x => read x Rp) (DoneS bl pre (q :: p) bo) ∧
      ABInv ⟨g.old, loc0, imms⟩ (fun x => DefW bl pre x ∨ x ∈ bo.par) (DoneS bl pre (q :: p) bo) (ClR bl) := by
  obtain ⟨hno, hloop⟩ := evalPass_check hpass
  obtain ⟨hnm, hnmi, hDo, hself⟩ := awi_edge_side hS ht hw hRo hbo hopre hbq hab
  have hpar : ∀ (k x : Nat), bo.par[k]? = some x → (fun x => read x Rp) x =
      match j'.args[k]? with | some (some u) => (fun x => read x regs) u | _ => none := by
    intro k x hk
    rw [awa_argV, hargs k, ← awa_argV]
    exact aedge_pass j.args bo.par regs Rp (fun u hu => hno _ hu u rfl) (hpn o bo hbo) hloop k x hk
  have hoff : ∀ x, x ∉ bo.par → (fun x => read x Rp) x = (fun x => read x regs) x := by
    intro x hx
    simp only [read]
    rw [Comp.evalPass_frame hpass x hx]
  exact ⟨aedge_aok hst him hed hpa hq hlq hmq hpb hok hj' hjo hpar hoff hnm hnmi hDo,
    aedge_abinv hst him hed hpa hq hlq hmq hpb hab (aedge_taken_mem hj') hjo (fun x h => Or.inl h)
      (fun x h => Or.inr h) hfr (fun x hx => (hDo x hx).imp (fun h => ⟨h.1, h.2.1⟩) id) hself⟩

/-- **`EndOK` at the end of the block just walked**, from `AOK` and `ABInv` at
its start and the run of its ops. -/
theorem awa_end {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {bl : Map Blob}
    (hS : AliasSSAB bl) (hA : Acyclic bl) (hnl : NoLti bl) {pre : List Nat} {g : AGen Map} {o : Nat}
    {p : List Nat} {bo : Blob} (hπ : BPath bl (o :: p)) (hbo : HoonMap.get bl o = some bo) {j0 : Jmp}
    (hj0 : j0 ∈ getJmps bo.fin) (hopre : o ∉ pre) (hpend : ∀ j ∈ getJmps bo.fin, o ∈ g.rev j.there)
    {loc0 : AInfo} {imms : AImms} {R Ry : Nat → Option Noun}
    (hok : AOK ⟨g.old, loc0, imms⟩ R (DoneS bl pre p bo))
    (hab : ABInv ⟨g.old, loc0, imms⟩ (fun x => DefW bl pre x ∨ x ∈ bo.par) (DoneS bl pre p bo) (ClR bl))
    {rb : List Pole × ABody} (hbody : aliasBody pick bo.body ⟨g.old, loc0, imms⟩ = some rb)
    {rf : Termin × (Nat → List Nat) × Bool} (hfin : aliasFin rb.2.old rb.2.loc g.rev g.folded o bo.fin = some rf)
    (hrun : OpsRun bo.body R Ry) :
    EndOK bl (pre ++ [o])
      { new := HoonMap.put g.new o { par := bo.par, body := rb.1, fin := rf.1 }, old := rb.2.old,
        info := updA g.info o (some rb.2.loc), imms := updA g.imms o (some rb.2.imml), rev := rf.2.1,
        folded := rf.2.2 } o p bo Ry := by
  have hR : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hnodf : ∀ k r, k < bo.body.length → ¬ DeadFill bl r o k := fun k r _ hdf => by
    obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
    rw [hbo] at hb3; cases hb3; rw [hu] at hj0; simp [getJmps] at hj0
  have hBO := awi_bodyOK hS hA hπ hbo hnodf hopre (awi_doneS_body hopre)
  rw [List.take_length] at hBO
  obtain ⟨hok1, hab1⟩ := as_body hpick bo.body _ R _ _ rb.1 rb.2 Ry hbody hok hab hBO hrun
  have hoo : o ∈ pre ++ [o] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hsubD : ∀ x, DoneE bl (pre ++ [o]) p bo x → bodyDone (ClR bl) bo.body (DoneS bl pre p bo) x := by
    rintro x ⟨h1, h2, h3⟩
    rcases h1 with h1 | h1
    · exact awa_bodyDone_base _ _ _ ⟨h1, h2, fun o' i hd ho' => h3 o' i hd (List.mem_append_left _ ho')⟩
    · exact awa_bodyDone_dst _ _ _ h1 h2
  have hsubF : ∀ x, bodyDef bo.body (fun x => DefW bl pre x ∨ x ∈ bo.par) x → DefW bl (pre ++ [o]) x := by
    intro x hx
    rcases awa_bodyDef_cases _ _ x hx with (h | h) | h
    · exact DefW.mono (fun a ha => List.mem_append_left _ ha) h
    · exact Or.inr ⟨(o, none), awi_par_live hR hbo h, hoo⟩
    · obtain ⟨i, op, hi, he⟩ := bdef_idx h
      exact Or.inr ⟨(o, some i), awi_jump_live hR hbo hj0 hi he, hoo⟩
  have hok2 : AOK rb.2 Ry (DoneE bl (pre ++ [o]) p bo) := aok_mono hok1 hsubD
  have hab2 : ABInv rb.2 (DefW bl (pre ++ [o])) (DoneE bl (pre ++ [o]) p bo) (ClR bl) :=
    awa_abinv_mono hab1 hsubF hsubD
  have hfd : ∀ x, x ∈ finRegs bo.fin → DoneE bl (pre ++ [o]) p bo x := fun x hx => awi_fin_done hS hπ hbo hj0 hx
  refine ⟨rb.2.loc, rb.2.imml, { par := bo.par, body := rb.1, fin := rf.1 }, as_upd_self _ _ _, as_upd_self _ _ _,
    by simp only [HoonMap.get_put, if_true],
    ?_, hok2, hab2, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := awa_fin_reads hfin (hnl o bo hbo) x hx
    exact hab2.old y (hfd y (awk_finReads_sub hy))
  · intro j hj
    obtain ⟨j', h1, h2, h3, h4⟩ := afn_jump hfin hok2.info (fun x hx => hok2.old x (hfd x (awk_finReads_sub hx)))
      (hnl o bo hbo) hj
    refine ⟨h4 (hpend j (aedge_taken_mem hj)), j', h1, h2, fun k => ?_⟩
    rw [h3, List.getElem?_map]
    cases hk : j.args[k]? with
    | none => rfl
    | some a =>
      cases a with
      | none => rfl
      | some u =>
        simp only [Option.map_some, argV, Option.bind_some]
        exact hok2.old u (hfd u (jmp_finRegs (aedge_taken_mem hj) (List.mem_of_getElem? hk)))

/-- `Done` at the end of a block walked before is safe from the next block. -/
theorem awa_stable1 {bl : Map Blob} (hS : AliasSSAB bl) {pre l : List Nat} {o : Nat}
    (ht : TopoOK bl (pre ++ o :: l)) {q : Nat} {p : List Nat} {b : Blob} {j : Jmp} (hπ : BPath bl (q :: p))
    (hb : HoonMap.get bl q = some b) (hj : j ∈ getJmps b.fin) (hq : q ∈ pre) {x : Nat}
    (hx : DoneE bl (pre ++ [o]) p b x) :
    Reach bl o → ∀ b', HoonMap.get bl o = some b' → x ∉ b'.body.filterMap aliasDst := by
  intro hR b' hb' hm
  have hdisj : ∀ a ∈ pre, a ≠ o := fun a ha e => (List.nodup_append.mp ht.1).2.2 a ha o List.mem_cons_self e
  have hoo : o ∈ pre ++ [o] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hRq : Reach bl q := ssk_bpath_reach hπ q List.mem_cons_self
  obtain ⟨k, op, hk, he⟩ := bdef_idx hm
  have hlive : LiveDef bl x (o, some k) := ⟨hR, ⟨b', op, hb', hk, he⟩, fun i hi hdf => by
    cases hi; exact hx.2.2 o k hdf hoo⟩
  rcases hx.1 with (hd | hd | ⟨o', ho', b2, hb2, hd⟩) | hd
  · exact hd (bdef_allDefs hb' (List.mem_append_right _ hm))
  · have e := hS.1 x _ _ hlive (awi_par_live hRq hb hd); simp at e
  · have hR' := ssk_bpath_reach hπ o' (List.mem_cons_of_mem _ ho')
    have ho'pre := awi_path_pre ht hπ hq o' ho'
    obtain ⟨b3, j3, hb3, hj3⟩ := bdef_jumps hπ rfl o' ho'
    rw [hb2] at hb3; cases hb3
    rcases List.mem_append.mp hd with hd | hd
    · have e := hS.1 x _ _ hlive (awi_par_live hR' hb2 hd); simp at e
    · obtain ⟨i, op', hi, he'⟩ := bdef_idx hd
      have e := hS.1 x _ _ hlive (awi_jump_live hR' hb2 hj3 hi he')
      simp only [Prod.mk.injEq] at e
      exact hdisj o' ho'pre e.1.symm
  · obtain ⟨i, op', hi, he'⟩ := bdef_idx hd
    have e := hS.1 x _ _ hlive (awi_jump_live hRq hb hj hi he')
    simp only [Prod.mk.injEq] at e
    exact hdisj q hq e.1.symm

/-- **`awi_end_later` for one block** of a walk over the whole `topo`. -/
theorem awa_end_step {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} (hS : AliasSSAB bl) {pre l : List Nat}
    {o : Nat} {g g' : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hi : ARev bl (pre ++ o :: l) pre g)
    (hw : OldW bl pre g) (h : aliasBlock pick nargs bl g o = some g') {q : Nat} {p : List Nat} {b : Blob}
    {j : Jmp} (hπ : BPath bl (q :: p)) (hb : HoonMap.get bl q = some b) (hj : j ∈ getJmps b.fin) (hq : q ∈ pre)
    {lq : AInfo} {mq : AImms} {R : Nat → Option Noun}
    (hok : AOK ⟨g.old, lq, mq⟩ R (DoneE bl pre p b))
    (hab : ABInv ⟨g.old, lq, mq⟩ (DefW bl pre) (DoneE bl pre p b) (ClR bl)) :
    AOK ⟨g'.old, lq, mq⟩ R (DoneE bl (pre ++ [o]) p b) ∧
      ABInv ⟨g'.old, lq, mq⟩ (DefW bl (pre ++ [o])) (DoneE bl (pre ++ [o]) p b) (ClR bl) := by
  have hsub : ∀ x, DoneE bl (pre ++ [o]) p b x → DoneE bl pre p b x :=
    fun x hx => ⟨hx.1, hx.2.1, fun o' i hd ho' => hx.2.2 o' i hd (List.mem_append_left _ ho')⟩
  have hold : ∀ x, DoneE bl (pre ++ [o]) p b x → g'.old x = g.old x :=
    fun x hx => awi_frame_step ht hi h (awa_stable1 hS ht hπ hb hj hq hx)
  have hmono : ∀ x, DefW bl pre x → DefW bl (pre ++ [o]) x :=
    fun x => DefW.mono fun o h => List.mem_append_left _ h
  have hw' := awi_old_step ht hi hw h
  have ht' : TopoOK bl ((pre ++ [o]) ++ l) := by rw [List.append_assoc]; exact ht
  refine ⟨⟨hok.imm, hok.info, fun d hd => ?_⟩, ⟨fun n r hr => hmono r (hab.imm n r hr),
    ⟨fun r i x hr hx => hmono x (hab.loc.1 r i x hr hx), fun r i hr => (hab.loc.2 r i hr).imp_right (hmono r)⟩,
    fun d hd => ?_, fun d hd => hmono d (hab.done d (hsub d hd)), fun d hn hc => awi_self hS ht' hw' hc hn⟩⟩
  · show R (g'.old d) = R d
    rw [hold d hd]; exact hok.old d (hsub d hd)
  · show DefW bl (pre ++ [o]) (g'.old d)
    rw [hold d hd]; exact hmono _ (hab.old d (hsub d hd))

/-- **`EndOK` at a block walked before survives the next block.** -/
theorem awa_rebase {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} (hS : AliasSSAB bl) {pre l : List Nat}
    {o : Nat} {g g' : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hi : ARev bl (pre ++ o :: l) pre g)
    (hw : OldW bl pre g) (h : aliasBlock pick nargs bl g o = some g') {q : Nat} {p : List Nat} {b : Blob}
    {j : Jmp} (hπ : BPath bl (q :: p)) (hb : HoonMap.get bl q = some b) (hj : j ∈ getJmps b.fin) (hq : q ∈ pre)
    (hqo : q ≠ o) {R : Nat → Option Noun} (hE : EndOK bl pre g q p b R) : EndOK bl (pre ++ [o]) g' q p b R := by
  obtain ⟨lq, mq, pb, hlq, hmq, hpb, hfr, hok, hab, htk⟩ := hE
  obtain ⟨e1, e2, e3⟩ := (awk_block h).2 q hqo
  obtain ⟨hok', hab'⟩ := awa_end_step hS ht hi hw h hπ hb hj hq hok hab
  refine ⟨lq, mq, pb, e1.trans hlq, e2.trans hmq, e3.trans hpb,
    fun x hx => DefW.mono (fun a ha => List.mem_append_left _ ha) (hfr x hx), hok', hab', fun j' hj' => ?_⟩
  obtain ⟨h1, h2⟩ := htk j' hj'
  exact ⟨awa_rev_keep h h1 hqo, h2⟩

end

/-! ## The induction over `topo` -/

section
variable [MapKeys Map]

/-- The parts of a block of the walk that is not dropped. -/
theorem awa_block_parts {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (hne : ¬ (g.rev o = [] ∧ o ≠ 0)) :
    ∃ info imms b edges loc0 rb rf,
      (if g.rev o = [] then some (entryInfo nargs) else aliasStart g o (g.rev o)) = some info ∧
      aliasStartImms g (g.rev o) = some imms ∧ HoonMap.get bl o = some b ∧
      aliasEdges g o (g.rev o) = some edges ∧ aliasPars g b.par edges info = some loc0 ∧
      aliasBody pick b.body ⟨g.old, loc0, imms⟩ = some rb ∧
      aliasFin rb.2.old rb.2.loc g.rev g.folded o b.fin = some rf ∧
      g' = AGen.mk (HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }) rb.2.old
        (updA g.info o (some rb.2.loc)) (updA g.imms o (some rb.2.imml)) rf.2.1 rf.2.2 := by
  unfold aliasBlock at h
  dsimp only at h
  rw [if_neg hne] at h
  obtain ⟨info, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨imms, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨edges, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨loc0, h5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rb, h6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rf, h7, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨info, imms, b, edges, loc0, rb, rf, h1, h2, h3, h4, h5, h6, h7, rfl⟩

/-- No block of `topo` jumps to `0`, so `rev` lists nothing for it. -/
theorem awa_rev_zero {bl : Map Blob} {T pre : List Nat} {g : AGen Map} (ht : TopoOK bl T) (hi : ARev bl T pre g) :
    g.rev 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨hpT, b, j, hb, hj, he⟩ := hi.sound 0 p hp
  have hlt := (awi_fwd ht hpT hb hj).2
  rw [he] at hlt
  obtain ⟨-, h0, -⟩ := ht
  cases T with
  | nil => cases h0
  | cons a T =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp [List.idxOf_cons_self] at hlt

variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **The walk invariant** at the point `pre` of the walk over `topo` with
state `g`: `ARev`, `OldW`, the edges of the blocks not walked yet still listed,
and `EndOK` at the end of every walked jumping block an execution from the
entry stands at, along the path it took. -/
structure AWInv (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (topo pre : List Nat) (g : AGen Map) :
    Prop where
  rev : ARev c.blocks topo pre g
  oldw : OldW c.blocks pre g
  pend : ∀ q b j, q ∈ topo → q ∉ pre → HoonMap.get c.blocks q = some b → j ∈ getJmps b.fin → q ∈ g.rev j.there
  ends : ∀ (st : σ) (vals : List Noun) (t : Trace) (es : List (Nat × Nat)) (y : Path.Cfg σ Map) (b : Blob) (j : Jmp),
    Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y →
    y.params = [] → y.b.par = [] → y.b.body = [] → y.lab ∈ pre → HoonMap.get c.blocks y.lab = some b →
    j ∈ getJmps b.fin → EndOK c.blocks pre g y.lab (epath es) b (fun x => read x y.regs)

/-- **The start of the block just walked**, for an execution from the entry
standing in it with its parameters passed: the parts of the walk of the
block, `AOK` and `ABInv` at its start on the values after the pass (from
`entryInfo` at block `0`, from `EndOK` at the predecessor taken otherwise),
and the run of the ops done so far. -/
theorem awa_start {pick : List Nat → Nat} {nargs : Nat}
    (hD : DInvS c.blocks) {pre l : List Nat} {o : Nat} {g g' : AGen Map}
    (ht : TopoOK c.blocks (pre ++ o :: l)) (hI : AWInv lib O c gul (pre ++ o :: l) pre g)
    (h : aliasBlock pick nargs c.blocks g o = some g') {st : σ} {vals : List Noun} {t : Trace}
    {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hyo : y.lab = o) (hb : HoonMap.get c.blocks o = some b) :
    ∃ (loc0 : AInfo) (imms : AImms) (rb : List Pole × ABody) (rf : Termin × (Nat → List Nat) × Bool) (k : Nat)
      (Rp : Nat → Option Noun),
      BPath c.blocks (o :: epath es) ∧ aliasBody pick b.body ⟨g.old, loc0, imms⟩ = some rb ∧
      aliasFin rb.2.old rb.2.loc g.rev g.folded o b.fin = some rf ∧
      g' = AGen.mk (HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }) rb.2.old
        (updA g.info o (some rb.2.loc)) (updA g.imms o (some rb.2.imml)) rf.2.1 rf.2.2 ∧
      AOK ⟨g.old, loc0, imms⟩ Rp (DoneS c.blocks pre (epath es) b) ∧
      ABInv ⟨g.old, loc0, imms⟩ (fun x => DefW c.blocks pre x ∨ x ∈ b.par) (DoneS c.blocks pre (epath es) b)
        (ClR c.blocks) ∧
      y.b.body = b.body.drop k ∧ OpsRun (b.body.take k) Rp (fun x => read x y.regs) := by
  have hS : AliasSSAB c.blocks := hD.2.1
  have hpn : ParNodup c.blocks := hD.1.1.1.1
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hat := awa_entry_at hfe
  obtain ⟨b0, hb0, hs⟩ := hfe
  rcases awa_steps_last hs with rfl | ⟨es1, x', j0, b', rfl, h1, hp', hq', hbody', ht0, hb', h2⟩
  · -- the execution stayed in block `0`
    obtain ⟨hlab, -, k, R', hpass, hdrop, hrun⟩ := awa_inblock_passed hs hp hq
    dsimp only at hlab hpass hdrop hrun
    have ho0 : o = 0 := hyo.symm.trans hlab
    subst ho0
    have e : b = b0 := Option.some.inj (hb.symm.trans hb0)
    subst e
    obtain ⟨hpar0, -⟩ := awa_pass_nil hpass
    have hrev0 : g.rev 0 = [] := awa_rev_zero ht hI.rev
    obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
      awa_block_parts h (fun e => e.2 rfl)
    have e : b = b1 := Option.some.inj (hb.symm.trans e3)
    subst e
    rw [if_pos hrev0] at e1
    cases e1
    rw [hrev0] at e2 e4
    simp only [aliasStartImms, Option.some.injEq] at e2
    subst e2
    simp [aliasEdges] at e4
    subst e4
    rw [hpar0] at e5
    simp only [aliasPars, Option.some.injEq] at e5
    subst e5
    obtain ⟨hok, hab⟩ := awa_start_entry hS ht hI.oldw nargs hpar0 (fun x => read x R')
    exact ⟨_, _, rb, rf, k, _, BPath.start, e6, e7, e8, hok, hab, hdrop, hrun⟩
  · -- the last jump, from `x'` at the end of `x'.lab`
    obtain ⟨hlab, -, k, Rp, hpass, hdrop, hrun⟩ := awa_inblock_passed h2 hp hq
    dsimp only at hlab hpass hdrop hrun
    have hjo : j0.there = o := hlab.symm.trans hyo
    have e : b = b' := Option.some.inj (hb.symm.trans (hjo ▸ hb'))
    subst e
    have hfe1 : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es1 x' := ⟨b0, hb0, h1⟩
    obtain ⟨hπ1, B, k1, hB, hfB, -, -⟩ := awa_entry_at hfe1
    have hj0B : j0 ∈ getJmps B.fin := hfB ▸ taken_mem ht0
    have hRq : Reach c.blocks x'.lab := ssk_bpath_reach hπ1 _ List.mem_cons_self
    have hqpre : x'.lab ∈ pre := awr_pre ht (ht.2.2.2.1 _ hRq) hB hj0B hjo
    have htk : takenR (fun x => read x x'.regs) B.fin = some j0 := by rw [← afn_taken, ← hfB]; exact ht0
    obtain ⟨lq, mq, pb, hlq, hmq, hpb, hfr, hok, hab, htake⟩ :=
      hI.ends st vals t es1 x' B j0 hfe1 hp' hq' hbody' hqpre hB hj0B
    obtain ⟨hqrev, j', hj', hj'o, hargs⟩ := htake j0 htk
    rw [hjo] at hqrev
    have hne : g.rev o ≠ [] := List.ne_nil_of_mem hqrev
    obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
      awa_block_parts h (fun e => hne e.1)
    have e : b = b1 := Option.some.inj (hb.symm.trans e3)
    subst e
    rw [if_neg hne] at e1
    have hπ : BPath c.blocks (o :: epath (es1 ++ [(x'.lab, j0.there)])) := hyo ▸ hat.1
    have hRo : Reach c.blocks o := ssk_bpath_reach hπ o List.mem_cons_self
    obtain ⟨hokS, habS⟩ := awa_start_jump hS hpn ht hI.oldw hRo hb hopre hB hlq hmq hpb hfr hok hab hqrev hj'
      (hj'o.trans hjo) hargs hpass e1 e2 e4 e5
    rw [awa_epath_snoc] at hπ ⊢
    exact ⟨loc0, imms, rb, rf, k, _, hπ, e6, e7, e8, hokS, habS, hdrop, hrun⟩

/-- **The block just walked**: `EndOK` at its end, for every execution from
the entry, through the entry or the jump it came by. -/
theorem awa_new {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {pre l : List Nat} {o : Nat} {g g' : AGen Map}
    (ht : TopoOK c.blocks (pre ++ o :: l)) (hI : AWInv lib O c gul (pre ++ o :: l) pre g)
    (h : aliasBlock pick nargs c.blocks g o = some g') {st : σ} {vals : List Noun} {t : Trace}
    {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob} {j : Jmp}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hbody : y.b.body = []) (hyo : y.lab = o)
    (hb : HoonMap.get c.blocks o = some b) (hj : j ∈ getJmps b.fin) :
    EndOK c.blocks (pre ++ [o]) g' o (epath es) b (fun x => read x y.regs) := by
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hoT : o ∈ pre ++ o :: l := List.mem_append_right _ List.mem_cons_self
  have hpend : ∀ j ∈ getJmps b.fin, o ∈ g.rev j.there := fun j hj => hI.pend o b j hoT hopre hb hj
  obtain ⟨loc0, imms, rb, rf, k, Rp, hπ, e6, e7, rfl, hok, hab, hdrop, hrun⟩ :=
    awa_start hD ht hI h hfe hp hq hyo hb
  have htk : b.body.take k = b.body := List.take_of_length_le (List.drop_eq_nil_iff.mp (hdrop.symm.trans hbody))
  rw [htk] at hrun
  exact awa_end hpick hD.2.1 hD.1.1.2.1 hD.2.2 hπ hb hj hopre hpend hok hab e6 e7 hrun

/-- **One block of the walk keeps `AWInv`.** -/
theorem awa_step {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {pre l : List Nat} {o : Nat} {g g' : AGen Map}
    (ht : TopoOK c.blocks (pre ++ o :: l)) (hI : AWInv lib O c gul (pre ++ o :: l) pre g)
    (h : aliasBlock pick nargs c.blocks g o = some g') : AWInv lib O c gul (pre ++ o :: l) (pre ++ [o]) g' := by
  have hS : AliasSSAB c.blocks := hD.2.1
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  refine ⟨(arev_step ht hI.rev h).1, awi_old_step ht hI.rev hI.oldw h, ?_, ?_⟩
  · intro q b j hq hqp hb hj
    have hqo : q ≠ o := fun e => hqp (by rw [e]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact awa_rev_keep h (hI.pend q b j hq (fun h' => hqp (List.mem_append_left _ h')) hb hj) hqo
  · intro st vals t es y b j hfe hp hq hbody hy hb hj
    rcases List.mem_append.mp hy with hy | hy
    · have hyo : y.lab ≠ o := fun e => hopre (e ▸ hy)
      exact awa_rebase hS ht hI.rev hI.oldw h (awa_entry_at hfe).1 hb hj hy hyo
        (hI.ends st vals t es y b j hfe hp hq hbody hy hb hj)
    · have hyo : y.lab = o := List.mem_singleton.mp hy
      rw [hyo] at hb ⊢
      exact awa_new hpick hD ht hI h hfe hp hq hbody hyo hb hj

/-- `AWInv` at the start of the walk. -/
theorem awa_init {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev) :
    AWInv lib O c gul topo [] (aliasInit rev) where
  rev := arev_init hT.2
  oldw := fun _ hd => (hd rfl).elim
  pend := fun q b j hq _ hb hj => awr_dedup_mem.mpr (hT.1.2 q b j hq hb hj)
  ends := by
    intro _ _ _ _ _ _ _ _ _ _ _ hy
    exact absurd hy List.not_mem_nil

/-- **`AWInv` along the walk.** -/
theorem awa_walk {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) : ∀ (l pre : List Nat) (g g' : AGen Map), TopoOK c.blocks (pre ++ l) →
      AWInv lib O c gul (pre ++ l) pre g → aliasWalk pick nargs c.blocks l g = some g' →
      AWInv lib O c gul (pre ++ l) (pre ++ l) g'
  | [], pre, g, g', _, hI, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    simpa using hI
  | o :: l, pre, g, g', ht, hI, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hI1 := awa_step hpick hD ht hI h1
    have ht' : TopoOK c.blocks ((pre ++ [o]) ++ l) := by rw [List.append_assoc]; exact ht
    have hI1' : AWInv lib O c gul ((pre ++ [o]) ++ l) (pre ++ [o]) g1 := by rw [List.append_assoc]; exact hI1
    have := awa_walk hpick hD l (pre ++ [o]) g1 g' ht' hI1' h
    rwa [List.append_assoc] at this

/-- **`EndOK` after the whole walk**: at every configuration of an execution
from the entry that stands at the end of a jumping block. -/
theorem alias_walk_endOK {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob} {j : Jmp}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hbody : y.b.body = [])
    (hb : HoonMap.get c.blocks y.lab = some b) (hj : j ∈ getJmps b.fin) :
    EndOK c.blocks topo g y.lab (epath es) b (fun x => read x y.regs) := by
  have hW := awa_walk (lib := lib) (O := O) (gul := gul) hpick hD topo [] _ g (by simpa using hT.1.1)
    (by simpa using awa_init (lib := lib) (O := O) (gul := gul) hT) h
  simp only [List.nil_append] at hW
  have hy : y.lab ∈ topo := hT.1.1.2.2.2.1 _ (ssk_bpath_reach (awa_entry_at hfe).1 _ List.mem_cons_self)
  exact hW.ends st vals t es y b j hfe hp hq hbody hy hb hj

/-- **The walk invariant of `+alias` over executions**: under `DInvS` and
`TopoInvR`, at every configuration of an execution from the entry of the code
before that stands at the end of the body of a jumping block `q` (its
parameters passed), `AOK` and `ABInv` hold with the final `old` and the facts
and immediates stored for `q`, with `Done` the registers of `DoneE` along the
path the execution took. -/
theorem alias_walk_inv {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob} {j : Jmp}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hbody : y.b.body = [])
    (hb : HoonMap.get c.blocks y.lab = some b) (hj : j ∈ getJmps b.fin) :
    ∃ lq mq, g.info y.lab = some lq ∧ g.imms y.lab = some mq ∧
      AOK ⟨g.old, lq, mq⟩ (fun x => read x y.regs) (DoneE c.blocks topo (epath es) b) ∧
      ABInv ⟨g.old, lq, mq⟩ (DefW c.blocks topo) (DoneE c.blocks topo (epath es) b) (ClR c.blocks) := by
  obtain ⟨lq, mq, -, hlq, hmq, -, -, hok, hab, -⟩ := alias_walk_endOK hpick hD hT h hfe hp hq hbody hb hj
  exact ⟨lq, mq, hlq, hmq, hok, hab⟩

end

/-! ## Inside a body: the corollary the simulation reads -/

section
variable [MapKeys Map] {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

theorem awa_walk_append {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} : ∀ (a b : List Nat) (g : AGen Map),
    aliasWalk pick nargs bl (a ++ b) g = (aliasWalk pick nargs bl a g).bind (aliasWalk pick nargs bl b)
  | [], b, g => by simp [aliasWalk]
  | o :: a, b, g => by
    simp only [List.cons_append, aliasWalk]
    cases aliasBlock pick nargs bl g o with
    | none => rfl
    | some g1 => simp only [Option.bind_some]; exact awa_walk_append a b g1

/-- **`AWInv` along a part of the walk.** -/
theorem awa_walk_part {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) : ∀ (l pre r : List Nat) (g g' : AGen Map), TopoOK c.blocks (pre ++ l ++ r) →
      AWInv lib O c gul (pre ++ l ++ r) pre g → aliasWalk pick nargs c.blocks l g = some g' →
      AWInv lib O c gul (pre ++ l ++ r) (pre ++ l) g'
  | [], pre, r, g, g', _, hI, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    simpa using hI
  | o :: l, pre, r, g, g', ht, hI, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have ht0 : TopoOK c.blocks (pre ++ o :: (l ++ r)) := by simpa using ht
    have hI0 : AWInv lib O c gul (pre ++ o :: (l ++ r)) pre g := by simpa using hI
    have hI1 := awa_step hpick hD ht0 hI0 h1
    have ht' : TopoOK c.blocks ((pre ++ [o]) ++ l ++ r) := by simpa using ht
    have hI1' : AWInv lib O c gul ((pre ++ [o]) ++ l ++ r) (pre ++ [o]) g1 := by simpa using hI1
    have := awa_walk_part hpick hD l (pre ++ [o]) r g1 g' ht' hI1' h
    simpa using this

/-- A register read at place `k` of a block at the end of a path is done there
(`DefFirst`). -/
theorem awa_read_done {bl : Map Blob} (hS : AliasSSAB bl) {o : Nat} {p pre : List Nat} {b : Blob}
    (hπ : BPath bl (o :: p)) (hb : HoonMap.get bl o = some b) (hopre : o ∉ pre) {k x : Nat}
    (hread : ReadAt b k x) : bodyDone (ClR bl) (b.body.take k) (DoneS bl pre p b) x := by
  have hR : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hcl : ClR bl x := Or.inr ⟨o, b, k, hR, hb, hread⟩
  have hdf : ∀ o' i, DeadFill bl x o' i → o' = o := fun o' i ⟨_, _, _, _, _, hreads⟩ =>
    (hreads o b k hR hb hread).1.symm
  have hdone : PathDef bl p b x → bodyDone (ClR bl) (b.body.take k) (DoneS bl pre p b) x :=
    fun h => awa_bodyDone_base _ _ _ (awi_doneS_body hopre x h hcl hdf)
  by_cases hx' : x ∈ allDefs bl
  · rcases hS.2 o p b hπ hb k x hread hx' with h | h | h
    · exact hdone (Or.inr (Or.inl h))
    · exact awa_bodyDone_dst _ _ _ h hcl
    · exact hdone (Or.inr (Or.inr h))
  · exact hdone (Or.inl hx')

/-- **The walk state at every place of a body, over executions**: under
`DInvS` and `TopoInvR`, at every configuration of an execution from the entry
of the code before that passed the parameters of its block `o` and runs its
body from place `k`, the block after is `o`'s parameters, the ops `aliasBody`
keeps from a start state `st0` (`outa` for the first `k` ops, reaching the
state `sta`, then `outb`) and the end `aliasFin` makes at the state `st'`,
whose facts and immediates are stored for `o`; and if no op before `k` is a
dead fill, the facts and immediates of `sta` hold on the values, and every
register the next op reads, or the end when the body is done, reads through
the `old` of `sta` the value it holds. -/
theorem alias_walk_at {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hb : HoonMap.get c.blocks y.lab = some b) :
    ∃ (k : Nat) (st0 sta st' : ABody) (outa outb : List Pole) (rf : Termin × (Nat → List Nat) × Bool)
      (rv : Nat → List Nat) (f : Bool),
      y.b.body = b.body.drop k ∧
      HoonMap.get g.new y.lab = some { par := b.par, body := outa ++ outb, fin := rf.1 } ∧
      g.info y.lab = some st'.loc ∧ g.imms y.lab = some st'.imml ∧
      aliasBody pick (b.body.take k) st0 = some (outa, sta) ∧ aliasBody pick (b.body.drop k) sta = some (outb, st') ∧
      aliasFin st'.old st'.loc rv f y.lab b.fin = some rf ∧
      ((∀ i r, i < k → ¬ DeadFill c.blocks r y.lab i) →
        FactsOK (fun x => read x y.regs) sta.loc ∧ ImmsOK (fun x => read x y.regs) sta.imml ∧
        (∀ op, b.body[k]? = some op → ∀ x ∈ aliasReads op, read (sta.old x) y.regs = read x y.regs) ∧
        (b.body.length ≤ k → ∀ x ∈ finRegs b.fin, read (sta.old x) y.regs = read x y.regs)) := by
  have hS : AliasSSAB c.blocks := hD.2.1
  have hA : Acyclic c.blocks := hD.1.1.2.1
  have hTo := hT.1.1
  have hoT : y.lab ∈ topo := hTo.2.2.2.1 _ (ssk_bpath_reach (awa_entry_at hfe).1 _ List.mem_cons_self)
  obtain ⟨pre, l, rfl⟩ := List.append_of_mem hoT
  rw [awa_walk_append] at h
  obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [aliasWalk] at h
  obtain ⟨g2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
  have hI : AWInv lib O c gul (pre ++ y.lab :: l) pre g1 := by
    have := awa_walk_part (lib := lib) (O := O) (gul := gul) hpick hD pre [] (y.lab :: l) _ g1 (by simpa using hTo)
      (by simpa using awa_init (lib := lib) (O := O) (gul := gul) hT) h1
    simpa using this
  have hopre : y.lab ∉ pre := fun h' => (List.nodup_append.mp hTo.1).2.2 _ h' _ List.mem_cons_self rfl
  have hol : y.lab ∉ l := fun h' => ((List.nodup_append.mp hTo.1).2.1 |> List.nodup_cons.mp).1 h'
  obtain ⟨loc0, imms, rb, rf, k, Rp, hπ, e6, e7, e8, hok, hab, hdrop, hrun⟩ :=
    awa_start hD hTo hI h2 hfe hp hq rfl hb
  obtain ⟨n1, n2, n3⟩ := (awk_walk l g2 g h3).2 _ hol
  rw [← List.take_append_drop k b.body, aliasBody_append] at e6
  obtain ⟨⟨outa, sta⟩, ha, e6⟩ := Option.bind_eq_some_iff.mp e6
  obtain ⟨⟨outb, st'⟩, hb2, e6⟩ := Option.map_eq_some_iff.mp e6
  subst e6
  subst e8
  refine ⟨k, _, sta, st', outa, outb, rf, g1.rev, g1.folded, hdrop, ?_, ?_, ?_, ha, hb2, e7, fun hnd => ?_⟩
  · rw [n3]; simp only [HoonMap.get_put, if_true]
  · rw [n1]; exact as_upd_self _ _ _
  · rw [n2]; exact as_upd_self _ _ _
  · have hBO := awi_bodyOK hS hA hπ hb hnd hopre (awi_doneS_body hopre)
    obtain ⟨hok1, -⟩ := as_body hpick _ _ Rp _ _ outa sta _ ha hok hab hBO hrun
    refine ⟨hok1.info, hok1.imm, fun op hk x hx => hok1.old x (awa_read_done hS hπ hb hopre
      (Or.inl (by rw [List.head?_drop, hk]; exact hx))), fun hk x hx => ?_⟩
    have e := awa_read_done (k := b.body.length) hS hπ hb hopre (x := x) (Or.inr ⟨rfl, hx⟩)
    rw [List.take_length, ← List.take_of_length_le hk] at e
    exact hok1.old x e

end

/-! ## Ends that leave the function, over executions -/

section
variable [MapKeys Map] {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **An end that leaves the function returns the same after**, at every
configuration of an execution from the entry that stands at the end of a
block with its parameters passed, on the values of the code before (given
that the test of a `%brn` holds a value). -/
theorem alias_walk_end {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hbody : y.b.body = []) (hb : HoonMap.get c.blocks y.lab = some b)
    (hval : ∀ s z o', b.fin = Termin.brn s z o' → (read s y.regs).isSome) :
    ∃ pb, HoonMap.get g.new y.lab = some pb ∧ pb.par = b.par ∧
      endR O gul (fun x => read x y.regs) y.st y.t pb.fin = endR O gul (fun x => read x y.regs) y.st y.t b.fin := by
  obtain ⟨k, st0, sta, st', outa, outb, rf, rv, f, hdrop, hnew, -, -, -, hb2, e7, hfacts⟩ :=
    alias_walk_at hpick hD hT h hfe hp hq hb
  refine ⟨_, hnew, rfl, ?_⟩
  have hk : b.body.length ≤ k := List.drop_eq_nil_iff.mp (hdrop.symm.trans hbody)
  rw [List.drop_eq_nil_iff.mpr hk] at hb2
  simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at hb2
  obtain ⟨-, rfl⟩ := hb2
  by_cases hbom : ∃ u, b.fin = Termin.bom u
  · obtain ⟨u, hu⟩ := hbom
    rw [hu] at e7 ⊢
    simp only [aliasFin, Option.some.injEq] at e7
    subst e7; rfl
  · have hnd : ∀ i r, i < k → ¬ DeadFill c.blocks r y.lab i := fun i r _ hdf => by
      obtain ⟨b3, hb3, hu, -⟩ := hdf
      rw [hb] at hb3; cases hb3; exact hbom hu
    obtain ⟨hf, -, -, hend⟩ := hfacts hnd
    exact afn_end O gul y.st y.t e7 hf (fun x hx => hend hk x (awk_finReads_sub hx)) (hD.2.2 _ b hb) hval

end

end Opt
end SkaModel
end Formalization
