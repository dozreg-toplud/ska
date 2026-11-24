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

/-! ## The global `old` of the walk -/

section
variable [MapKeys Map]

theorem awi_reach_bpath {bl : Map Blob} {o : Nat} (h : Reach bl o) : ∃ p, BPath bl (o :: p) := by
  induction h with
  | zero => exact ⟨[], BPath.start⟩
  | jump _ hb hj ih => obtain ⟨p, hp⟩ := ih; exact ⟨_, BPath.step hp hb hj⟩

/-- A jump of a member of `topo` goes to a later member. -/
theorem awi_fwd {bl : Map Blob} {T : List Nat} (ht : TopoOK bl T) {p : Nat} (hp : p ∈ T) {b : Blob} {j : Jmp}
    (hb : HoonMap.get bl p = some b) (hj : j ∈ getJmps b.fin) : j.there ∈ T ∧ T.idxOf p < T.idxOf j.there := by
  obtain ⟨hnd, -, -, -, hf⟩ := ht
  have hl : T.idxOf p < T.length := List.idxOf_lt_length_of_mem hp
  have hx : T[T.idxOf p]? = some p := by rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]
  obtain ⟨k, hk, hk'⟩ := hf _ p b j hx hb hj
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk'
  have hko : T.idxOf j.there = k := by rw [← hkv, hnd.idxOf_getElem k hkl]
  refine ⟨?_, by omega⟩
  rw [← hkv]; exact List.getElem_mem hkl

/-- The blocks of a path from `0` are members of `topo`, each before the last. -/
theorem awi_bpath_idx {bl : Map Blob} {T : List Nat} (ht : TopoOK bl T) : ∀ {L : List Nat}, BPath bl L →
    ∀ {o p}, L = o :: p → o ∈ T ∧ ∀ o' ∈ p, T.idxOf o' < T.idxOf o
  | _, BPath.start, o, p, e => by
    cases e
    refine ⟨?_, fun o' h => absurd h List.not_mem_nil⟩
    obtain ⟨-, h0, -⟩ := ht
    exact List.mem_of_mem_head? h0
  | _, BPath.step hp hb hj, o, p, e => by
    cases e
    obtain ⟨hoT, ih⟩ := awi_bpath_idx ht hp rfl
    obtain ⟨hjT, hlt⟩ := awi_fwd ht hoT hb hj
    refine ⟨hjT, fun o' h => ?_⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact hlt
    · exact Nat.lt_trans (ih o' h) hlt

/-- **A path to a walked block runs through walked blocks.** -/
theorem awi_path_pre {bl : Map Blob} {pre l : List Nat} (ht : TopoOK bl (pre ++ l)) {o : Nat} {p : List Nat}
    (hπ : BPath bl (o :: p)) (ho : o ∈ pre) : ∀ o' ∈ p, o' ∈ pre := by
  intro o' h
  have hlt := (awi_bpath_idx ht hπ rfl).2 o' h
  apply mem_pre_of_idx (l := l)
  have hnd := ht.1
  have hi : pre.idxOf o < pre.length := List.idxOf_lt_length_of_mem ho
  have hg : (pre ++ l)[pre.idxOf o]'(by rw [List.length_append]; omega) = o := by
    rw [List.getElem_append_left hi, List.getElem_idxOf hi]
  have : (pre ++ l).idxOf o = pre.idxOf o := by
    conv => lhs; rw [← hg]
    exact hnd.idxOf_getElem _ _
  omega

/-- **`old` renames only destinations of ops of walked blocks** of `pre`. -/
def OldW (bl : Map Blob) (pre : List Nat) (g : AGen Map) : Prop :=
  ∀ d, g.old d ≠ d → ∃ o ∈ pre, Reach bl o ∧ ∃ b, HoonMap.get bl o = some b ∧ d ∈ b.body.filterMap aliasDst

theorem awi_block_drop {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (h0 : g.rev o = []) (ho : o ≠ 0) : g'.old = g.old := by
  unfold aliasBlock at h
  dsimp only at h
  rw [if_pos ⟨h0, ho⟩] at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

theorem awi_old_step {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {pre l : List Nat} {o : Nat}
    {g g' : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hi : ARev bl (pre ++ o :: l) pre g) (hw : OldW bl pre g)
    (h : aliasBlock pick nargs bl g o = some g') : OldW bl (pre ++ [o]) g' := by
  intro d hd
  have back : g.old d ≠ d → ∃ o' ∈ pre ++ [o], Reach bl o' ∧ ∃ b, HoonMap.get bl o' = some b ∧
      d ∈ b.body.filterMap aliasDst := fun hd => by
    obtain ⟨o', ho', r⟩ := hw d hd
    exact ⟨o', List.mem_append_left _ ho', r⟩
  rcases (arev_step ht hi h).2 with ⟨h0, ho, -⟩ | ⟨hR, -⟩
  · rw [awi_block_drop h h0 ho] at hd; exact back hd
  · cases hb : HoonMap.get bl o with
    | none =>
      rw [(awk_block h).1 d (fun b e => by rw [hb] at e; cases e)] at hd; exact back hd
    | some b =>
      by_cases hm : d ∈ b.body.filterMap aliasDst
      · exact ⟨o, List.mem_append_right _ (List.mem_singleton.mpr rfl), hR, b, hb, hm⟩
      · rw [(awk_block h).1 d (fun b' e => by rw [hb] at e; cases e; exact hm)] at hd; exact back hd

/-- **`OldW` along the walk.** -/
theorem awi_old_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} :
    ∀ (l pre : List Nat) (g g' : AGen Map), TopoOK bl (pre ++ l) → ARev bl (pre ++ l) pre g → OldW bl pre g →
      aliasWalk pick nargs bl l g = some g' → OldW bl (pre ++ l) g'
  | [], pre, g, g', _, _, hw, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    simpa using hw
  | o :: l, pre, g, g', ht, hi, hw, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hw1 := awi_old_step ht hi hw h1
    have hi1 := (arev_step ht hi h1).1
    have ht' : TopoOK bl ((pre ++ [o]) ++ l) := by rw [List.append_assoc]; exact ht
    have hi1' : ARev bl ((pre ++ [o]) ++ l) (pre ++ [o]) g1 := by rw [List.append_assoc]; exact hi1
    have := awi_old_walk l (pre ++ [o]) g1 g' ht' hi1' hw1 h
    rwa [List.append_assoc] at this

/-- **The `self` clause for the global `old`**: at any point of the walk, a
register of `ClR` outside `DefW bl pre` keeps its own name.  A walked op that
renamed it is a definition that counts (so the register is in `DefW`), or a
dead fill; then `ClR` gives a reachable read before the fill in its block, and
`DefFirst` a definition before that read, a parameter, an earlier op that is
no dead fill, or a definition in a block of the path, which jumps and is
walked. -/
theorem awi_self {bl : Map Blob} (hS : AliasSSAB bl) {pre l : List Nat} (ht : TopoOK bl (pre ++ l))
    {g : AGen Map} (hw : OldW bl pre g) {d : Nat} (hc : ClR bl d) (hn : ¬ DefW bl pre d) : g.old d = d := by
  apply Classical.byContradiction; intro hd
  obtain ⟨o, ho, hR, b, hb, hm⟩ := hw d hd
  obtain ⟨k, op, hk, he⟩ := bdef_idx hm
  by_cases hf : DeadFill bl d o k
  · rcases hc with hc | ⟨o2, b2, j, hR2, hb2, hrd⟩
    · exact hc o k hf
    · obtain ⟨-, -, -, -, -, hreads⟩ := hf
      obtain ⟨e2, -⟩ := hreads o2 b2 j hR2 hb2 hrd
      subst e2
      rw [hb] at hb2; cases hb2
      obtain ⟨p, hπ⟩ := awi_reach_bpath hR
      have hall : d ∈ allDefs bl := bdef_allDefs hb (List.mem_append_right _ hm)
      rcases hS.2 o2 p b hπ hb j d hrd hall with h | h | ⟨o', ho', b', hb', h⟩
      · exact hn (Or.inr ⟨(o2, none), awi_par_live hR hb h, ho⟩)
      · obtain ⟨i, op', hi, he'⟩ := bdef_idx h
        rw [List.getElem?_take] at hi
        split at hi
        · rename_i hij
          refine hn (Or.inr ⟨(o2, some i), ⟨hR, ⟨b, op', hb, hi, he'⟩, fun i' hi' hdf => ?_⟩, ho⟩)
          cases hi'
          obtain ⟨-, -, -, -, -, hr2⟩ := hdf
          have := (hr2 o2 b j hR hb hrd).2
          omega
        · cases hi
      · have ho'pre := awi_path_pre ht hπ ho o' ho'
        have hR' := ssk_bpath_reach hπ o' (List.mem_cons_of_mem _ ho')
        obtain ⟨b'', j', hb'', hj'⟩ := bdef_jumps hπ rfl o' ho'
        rw [hb'] at hb''; cases hb''
        rcases List.mem_append.mp h with h | h
        · exact hn (Or.inr ⟨(o', none), awi_par_live hR' hb' h, ho'pre⟩)
        · obtain ⟨i, op', hi, he'⟩ := bdef_idx h
          refine hn (Or.inr ⟨(o', some i), ⟨hR', ⟨b', op', hb', hi, he'⟩, fun i' _ hdf => ?_⟩, ho'pre⟩)
          obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
          rw [hb'] at hb3; cases hb3; rw [hu] at hj'; simp [getJmps] at hj'
  · exact hn (Or.inr ⟨(o, some k), ⟨hR, ⟨b, op, hb, hk, he⟩, fun i hi => by cases hi; exact hf⟩, ho⟩)

end

/-! ## `Done` at the end of a walked block, through the rest of the walk -/

section
variable [MapKeys Map]

/-- **`Done` at the end of a walked block** `b` reached along the path `p`,
at the point `pre` of the walk: defined on the path or by an op of the block,
in `ClR`, with no dead fill in a block of `pre`. -/
def DoneE (bl : Map Blob) (pre p : List Nat) (b : Blob) (x : Nat) : Prop :=
  (PathDef bl p b x ∨ x ∈ b.body.filterMap aliasDst) ∧ ClR bl x ∧ ∀ o' i, DeadFill bl x o' i → o' ∉ pre

/-- An op of a reachable block that jumps is a definition that counts. -/
theorem awi_jump_live {bl : Map Blob} {o i x : Nat} {b : Blob} {op : Pole} {j : Jmp} (hR : Reach bl o)
    (hb : HoonMap.get bl o = some b) (hj : j ∈ getJmps b.fin) (hk : b.body[i]? = some op)
    (he : aliasDst op = some x) : LiveDef bl x (o, some i) :=
  ⟨hR, ⟨b, op, hb, hk, he⟩, fun i' _ hdf => by
    obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
    rw [hb] at hb3; cases hb3; rw [hu] at hj; simp [getJmps] at hj⟩

/-- A block of the walk changes `old` only at destinations of its ops, and
only if it is walked (reachable). -/
theorem awi_frame_step {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {pre l : List Nat} {o : Nat}
    {g g' : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hi : ARev bl (pre ++ o :: l) pre g)
    (h : aliasBlock pick nargs bl g o = some g') {x : Nat}
    (hx : Reach bl o → ∀ b, HoonMap.get bl o = some b → x ∉ b.body.filterMap aliasDst) : g'.old x = g.old x := by
  rcases (arev_step ht hi h).2 with ⟨h0, ho, -⟩ | ⟨hR, -⟩
  · rw [awi_block_drop h h0 ho]
  · exact (awk_block h).1 x (hx hR)

/-- **A part of `topo` walked changes `old` only at destinations of ops of
its reachable blocks.** -/
theorem awi_frame_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} :
    ∀ (l pre : List Nat) (g g' : AGen Map), TopoOK bl (pre ++ l) → ARev bl (pre ++ l) pre g →
      aliasWalk pick nargs bl l g = some g' →
      ∀ x, (∀ o ∈ l, Reach bl o → ∀ b, HoonMap.get bl o = some b → x ∉ b.body.filterMap aliasDst) →
        g'.old x = g.old x
  | [], pre, g, g', _, _, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    exact fun _ _ => rfl
  | o :: l, pre, g, g', ht, hi, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hi1 := (arev_step ht hi h1).1
    have ht' : TopoOK bl ((pre ++ [o]) ++ l) := by rw [List.append_assoc]; exact ht
    have hi1' : ARev bl ((pre ++ [o]) ++ l) (pre ++ [o]) g1 := by rw [List.append_assoc]; exact hi1
    intro x hx
    rw [awi_frame_walk l (pre ++ [o]) g1 g' ht' hi1' h x (fun o' ho' => hx o' (List.mem_cons_of_mem _ ho')),
      awi_frame_step ht hi h1 (hx o List.mem_cons_self)]

/-- **`Done` at the end of a walked jumping block is safe from the rest of
the walk**: no reachable block walked later writes a register of it (a
definition that counts there would be a second one, by `DefOnceB`, and a dead
fill there is excluded by `DoneE`). -/
theorem awi_done_stable {bl : Map Blob} (hS : AliasSSAB bl) {pre l : List Nat} (ht : TopoOK bl (pre ++ l))
    {q : Nat} {p : List Nat} {b : Blob} {j : Jmp} (hπ : BPath bl (q :: p)) (hb : HoonMap.get bl q = some b)
    (hj : j ∈ getJmps b.fin) (hq : q ∈ pre) {x : Nat} (hx : DoneE bl (pre ++ l) p b x) :
    ∀ o ∈ l, Reach bl o → ∀ b', HoonMap.get bl o = some b' → x ∉ b'.body.filterMap aliasDst := by
  intro o ho hR b' hb' hm
  have hdisj : ∀ a ∈ pre, a ≠ o := fun a ha e => (List.nodup_append.mp ht.1).2.2 a ha o ho e
  have hRq : Reach bl q := ssk_bpath_reach hπ q List.mem_cons_self
  obtain ⟨k, op, hk, he⟩ := bdef_idx hm
  have hlive : LiveDef bl x (o, some k) := ⟨hR, ⟨b', op, hb', hk, he⟩, fun i hi hdf => by
    cases hi; exact hx.2.2 o k hdf (List.mem_append_right _ ho)⟩
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

/-- **The invariant at a block's end survives the rest of the walk**: `AOK`
and `ABInv` with `DefW` and `DoneE` at the point `pre` give them at
`pre ++ l` with the `old` of the later state. -/
theorem awi_end_later {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} (hS : AliasSSAB bl)
    {pre l : List Nat} {g g' : AGen Map} (ht : TopoOK bl (pre ++ l)) (hi : ARev bl (pre ++ l) pre g)
    (hw : OldW bl pre g) (h : aliasWalk pick nargs bl l g = some g')
    {q : Nat} {p : List Nat} {b : Blob} {j : Jmp} (hπ : BPath bl (q :: p)) (hb : HoonMap.get bl q = some b)
    (hj : j ∈ getJmps b.fin) (hq : q ∈ pre) {lq : AInfo} {mq : AImms} {R : Nat → Option Noun}
    (hok : AOK ⟨g.old, lq, mq⟩ R (DoneE bl pre p b))
    (hab : ABInv ⟨g.old, lq, mq⟩ (DefW bl pre) (DoneE bl pre p b) (ClR bl)) :
    AOK ⟨g'.old, lq, mq⟩ R (DoneE bl (pre ++ l) p b) ∧
      ABInv ⟨g'.old, lq, mq⟩ (DefW bl (pre ++ l)) (DoneE bl (pre ++ l) p b) (ClR bl) := by
  have hsub : ∀ x, DoneE bl (pre ++ l) p b x → DoneE bl pre p b x :=
    fun x hx => ⟨hx.1, hx.2.1, fun o' i hd ho' => hx.2.2 o' i hd (List.mem_append_left _ ho')⟩
  have hold : ∀ x, DoneE bl (pre ++ l) p b x → g'.old x = g.old x :=
    fun x hx => awi_frame_walk l pre g g' ht hi h x (awi_done_stable hS ht hπ hb hj hq hx)
  have hmono : ∀ x, DefW bl pre x → DefW bl (pre ++ l) x := fun x => DefW.mono fun o h => List.mem_append_left _ h
  have hw' := awi_old_walk l pre g g' ht hi hw h
  refine ⟨⟨hok.imm, hok.info, fun d hd => ?_⟩, ⟨fun n r hr => hmono r (hab.imm n r hr),
    ⟨fun r i x hr hx => hmono x (hab.loc.1 r i x hr hx), fun r i hr => (hab.loc.2 r i hr).imp_right (hmono r)⟩,
    fun d hd => ?_, fun d hd => hmono d (hab.done d (hsub d hd)), fun d hn hc => awi_self hS (l := []) (by simpa using ht) hw' hc hn⟩⟩
  · show R (g'.old d) = R d
    rw [hold d hd]; exact hok.old d (hsub d hd)
  · show DefW bl (pre ++ l) (g'.old d)
    rw [hold d hd]; exact hmono _ (hab.old d (hsub d hd))

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
