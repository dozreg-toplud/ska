import lemmas.Ska.OptAliasFrame

/-!
# Toward the walk invariant of `+alias`: `Def` independent of the path

The walk invariant at the end of a walked block `q` must survive the blocks
walked after `q`, and the start of a block `o` must take it from whichever
predecessor the execution came from, so the set `Def` of `ABInv` cannot be
`PathDef` (a register defined and renamed in a walked block off the path
breaks the `self` clause).  **`DefW bl pre`** is the path-independent set: the
registers no block defines and every register with a definition that counts
(`LiveDef`) in a block of `pre`, the part of `topo` walked so far.

* **`awi_bodyOK_mono`**: `BodyOK` holds for a larger `Done` and for any `Def`
  that adds no destination of the body.
* **`awi_par_notDefW`**, **`awi_dst_notDefW`**: on `DefOnceB`, a parameter of
  a reachable block `o` outside `pre`, and the destination of one of its ops
  before the first dead fill, are outside `DefW bl pre` (a definition that
  counts is the only one).  This gives `hnm`, `hnmi` and the `Do` clause of
  `aedge_aok` once the facts at `q`'s end name only `DefW` registers.
* **`awi_bodyOK`**: `bodyOK_ssa` with `Def` widened to `DefW bl pre` and the
  parameters of `o`, for `o` outside `pre`.
* **`ACfgAt`**, **`awi_step_at`**, **`awi_steps_at`**, **`awi_entry_at`**: a
  configuration reached from the entry runs a suffix of the body of the block
  at its label, with that block's end, at the end of a path of blocks from `0`
  (`BPath`) that a jump step extends by the block it leaves.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- **`BodyOK` is monotone**: a larger `Done`, and a `Def` that adds no
destination of the body. -/
theorem awi_bodyOK_mono {Cl : Nat → Prop} : ∀ (ops : List Pole) (Def Def' Done Done' : Nat → Prop),
    BodyOK Cl ops Def Done → (∀ e ∈ ops.filterMap aliasDst, Def' e → Def e) → (∀ x, Done x → Done' x) →
    BodyOK Cl ops Def' Done'
  | [], _, _, _, _, _, _, _ => trivial
  | op :: l, Def, Def', Done, Done', ⟨hs, hd, hb⟩, hD, hDo => by
    refine ⟨fun x hx => hDo x (hs x hx),
      fun e he hde => hd e he (hD e (List.mem_filterMap.mpr ⟨op, List.mem_cons_self, he⟩) hde), ?_⟩
    refine awi_bodyOK_mono l _ _ _ _ hb (fun e he hde => ?_) (fun x hx => Or.imp_left (hDo x) hx)
    rcases hde with hde | hde
    · obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp he
      exact Or.inl (hD e (List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem _ ha, hfa⟩) hde)
    · exact Or.inr hde

section
variable [MapKeys Map]

/-- **`Def` at a block start, independent of the path**: the registers no
block defines, and every register with a definition that counts in a block of
`pre` (the part of `topo` walked so far). -/
def DefW (bl : Map Blob) (pre : List Nat) (x : Nat) : Prop :=
  x ∉ allDefs bl ∨ ∃ s, LiveDef bl x s ∧ s.1 ∈ pre

theorem DefW.mono {bl : Map Blob} {pre pre' : List Nat} (h : ∀ o ∈ pre, o ∈ pre') {x : Nat}
    (hx : DefW bl pre x) : DefW bl pre' x := by
  rcases hx with hx | ⟨s, hs, hp⟩
  · exact Or.inl hx
  · exact Or.inr ⟨s, hs, h _ hp⟩

/-- A parameter of a reachable block is a definition that counts. -/
theorem awi_par_live {bl : Map Blob} {o x : Nat} {b : Blob} (hR : Reach bl o) (hb : HoonMap.get bl o = some b)
    (hx : x ∈ b.par) : LiveDef bl x (o, none) :=
  ⟨hR, ⟨b, hb, hx⟩, fun i hi => by cases hi⟩

/-- **A parameter of a reachable block outside `pre` is outside `DefW`.** -/
theorem awi_par_notDefW {bl : Map Blob} (hS1 : DefOnceB bl) {o x : Nat} {b : Blob} (hR : Reach bl o)
    (hb : HoonMap.get bl o = some b) (hx : x ∈ b.par) {pre : List Nat} (hpre : o ∉ pre) : ¬ DefW bl pre x := by
  rintro (hd | ⟨s, hs, hsp⟩)
  · exact hd (bdef_allDefs hb (List.mem_append_left _ hx))
  · have e := hS1 x _ _ (awi_par_live hR hb hx) hs
    rw [← e] at hsp; exact hpre hsp

/-- **A destination of an op before the first dead fill of a reachable block
outside `pre`** is outside `DefW` and is no parameter of the block. -/
theorem awi_dst_notDefW {bl : Map Blob} (hS1 : DefOnceB bl) {o k e : Nat} {b : Blob} {op : Pole}
    (hR : Reach bl o) (hb : HoonMap.get bl o = some b) (hk : b.body[k]? = some op) (he : aliasDst op = some e)
    (hnf : ¬ DeadFill bl e o k) {pre : List Nat} (hpre : o ∉ pre) : ¬ DefW bl pre e ∧ e ∉ b.par := by
  have hlive : LiveDef bl e (o, some k) := ⟨hR, ⟨b, op, hb, hk, he⟩, fun i hi => by cases hi; exact hnf⟩
  refine ⟨?_, fun hp => ?_⟩
  · rintro (hd | ⟨s, hs, hsp⟩)
    · exact hd (bdef_allDefs hb (List.mem_append_right _ (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hk, he⟩)))
    · have e' := hS1 e _ _ hlive hs
      rw [← e'] at hsp; exact hpre hsp
  · have e' := hS1 e _ _ hlive (awi_par_live hR hb hp)
    simp at e'

/-- **`bodyOK_ssa` with the path-independent `Def`**: at the end `o` of a
path from `0`, `o` outside `pre`, `BodyOK` holds with `Def` = `DefW bl pre`
and the parameters of `o`, up to the first dead fill. -/
theorem awi_bodyOK {bl : Map Blob} (hS : AliasSSAB bl) (hA : Acyclic bl) {o : Nat} {p : List Nat} {b : Blob}
    (hπ : BPath bl (o :: p)) (hb : HoonMap.get bl o = some b) {m : Nat} (hm : ∀ k r, k < m → ¬ DeadFill bl r o k)
    {pre : List Nat} (hpre : o ∉ pre) {Done : Nat → Prop}
    (hD : ∀ x, PathDef bl p b x → ClR bl x → (∀ o' i, DeadFill bl x o' i → o' = o) → Done x) :
    BodyOK (ClR bl) (b.body.take m) (fun x => DefW bl pre x ∨ x ∈ b.par) Done := by
  have hR : Reach bl o := ssk_bpath_reach hπ o (List.mem_cons_self ..)
  refine awi_bodyOK_mono _ _ _ _ _ (bodyOK_ssa hS hA hπ hb hm hD) (fun e he hde => ?_) (fun _ h => h)
  obtain ⟨k, op, hk, hdst⟩ := bdef_idx he
  rw [List.getElem?_take] at hk
  split at hk
  · rename_i hkm
    obtain ⟨n1, n2⟩ := awi_dst_notDefW hS.1 hR hb hk hdst (hm k e hkm) hpre
    rcases hde with h | h
    · exact absurd h n1
    · exact absurd h n2
  · cases hk

end

/-! ## Where an execution is -/

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **A configuration at the end of a path**: the label ends a path of
blocks from `0` (`p` before it), and the configuration runs a suffix of the
body of the block at its label, with that block's end, its parameters still to
pass or passed. -/
def ACfgAt (bl : Map Blob) (x : Path.Cfg σ Map) (p : List Nat) : Prop :=
  BPath bl (x.lab :: p) ∧ ∃ B k, HoonMap.get bl x.lab = some B ∧ x.b.fin = B.fin ∧
    x.b.body = B.body.drop k ∧ (x.b.par = B.par ∨ x.b.par = [])

theorem awi_drop_succ {α : Type} {l rest : List α} {a : α} {k : Nat} (h : l.drop k = a :: rest) :
    l.drop (k + 1) = rest := by
  rw [← List.drop_drop, h]; rfl

/-- **A step stays in the block or jumps along an edge**, extending the path
by the block it leaves. -/
theorem awi_step_at {x y : Path.Cfg σ Map} {e : List (Nat × Nat)} (h : Path.Step lib O c gul x e y)
    {p : List Nat} (hx : ACfgAt c.blocks x p) :
    (e = [] ∧ y.lab = x.lab ∧ ACfgAt c.blocks y p) ∨
      (e = [(x.lab, y.lab)] ∧ ACfgAt c.blocks y (x.lab :: p) ∧
        ∃ B j, HoonMap.get c.blocks x.lab = some B ∧ j ∈ getJmps B.fin ∧ j.there = y.lab ∧
          x.b.body = [] ∧ Path.taken x.regs x.b.fin = some j) := by
  obtain ⟨hπ, B, k, hB, hf, hbody, hpar⟩ := hx
  cases h with
  | pass _ _ => exact Or.inl ⟨rfl, rfl, hπ, B, k, hB, hf, hbody, Or.inr rfl⟩
  | op _ _ hb _ =>
    rw [hb] at hbody
    exact Or.inl ⟨rfl, rfl, hπ, B, k + 1, hB, hf, (awi_drop_succ hbody.symm).symm, hpar⟩
  | @jump j b' _ _ hb ht hb' =>
    have hj : j ∈ getJmps B.fin := hf ▸ taken_mem ht
    exact Or.inr ⟨rfl, ⟨BPath.step hπ hB hj, b', 0, hb', rfl, (List.drop_zero).symm, Or.inl rfl⟩,
      B, j, hB, hj, rfl, hb, ht⟩

theorem awi_steps_at {x y : Path.Cfg σ Map} {es : List (Nat × Nat)} (h : Path.Steps lib O c gul x es y) :
    ∀ {p : List Nat}, ACfgAt c.blocks x p → ∃ p', ACfgAt c.blocks y p' := by
  induction h with
  | refl => exact fun hx => ⟨_, hx⟩
  | step s _ ih =>
    intro p hx
    rcases awi_step_at s hx with ⟨-, -, hy⟩ | ⟨-, hy, -⟩
    · exact ih hy
    · exact ih hy

/-- **A configuration reached from the entry** ends a path of blocks from `0`. -/
theorem awi_entry_at {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map}
    (h : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y) : ∃ p, ACfgAt c.blocks y p := by
  obtain ⟨b0, hb0, hs⟩ := h
  exact awi_steps_at hs ⟨BPath.start, b0, 0, hb0, rfl, (List.drop_zero).symm, Or.inl rfl⟩

end

end Opt
end SkaModel
end Formalization
