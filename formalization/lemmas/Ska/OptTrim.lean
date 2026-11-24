import lemmas.Ska.OptTopo

/-!
# `+trim-trace-hints`

The pass (`nock-compilation.hoon`, about line 8902) drops trace hints whose
frame nothing can observe.  Line by line:

1. `key` and `trace` (`TKey`, `traceKey`): a `%hdp` or `%hde` with the tag
   `%spot` or `%mean` has the key `[%clue n p]`, a `%hmp` or `%hme` the key
   `[%defer a v f]`, a `%hcp` or `%hce` the key `[%konst n f]`; the `p`, `m`,
   `c` ops open their key, the `e` ops close it.  Other ops have no key (a
   `%hdp` of another tag among them).
2. `unsafe` (`trimWalk`, `trimBody`): a walk over `topo` with a map `out`
   from each walked block to the keys open at its end.  At a block, the keys
   open at its start are the union of `out` over its predecessors in `rev`
   (`+roll` over `(~(get ja rev) o)`, `~(get ju out) p`, empty for a
   predecessor not walked yet).  Along the body an opening op puts its key,
   a closing op deletes it, and any other op that is not
   `pole-not-crashing` (`%imm %mov %con %hed %tal %hsp %hse %hdp %hde %hmp
   %hme %hcp %hce %equ`) makes every open key unsafe.  At the end, a
   terminator that is not `%clq`, `%eqq`, `%brz`, `%hop` makes every open key
   unsafe.  Then `out` of the block is the keys open at its end.
3. `opened` (`trimOpened`): the keys that some op of some block opens
   (`+rep:by`, a union, so its order does not matter).
4. The result (`trimTraceHints`): `+run:by` over the blocks, each body
   without the hint ops whose key is not unsafe and is opened.  Every block
   is kept with its parameters and end.

The model returns `none` where the Hoon crashes (`got` of a label of `topo`
that is not a block).  Sets are lists here; only membership is used.

## What preservation needs

`TrimKeeps` states it in the form `Keeps`, on a `topo` with `TopoOK` and its
`+rev-cfg`, which is how `+optimize-once` calls it (after `+alias`, with
`topo` filtered by the blocks that remain).  **It is false on real compiler
output** (`tools/hoon/trimbug.hoon`, 2026-11-24): on the subject `0` the
formula `[11 [%spot 0 1] [11 [%spot 0 1] 1 5] 0 0]` gives `+mock`
`[%2 ~[leaf+"mook.spot"]]` and `+eval-top` with `+eval-mook` `[%2 ~]`.  Raw
`+comp` output moves the clue `[0 1]` into two fresh registers (`0v2` for
the outer hint, `0v5` for the inner); `+alias` renames both to `0v0`, so both
hints have the key `[%clue %spot 0v0]`, the inner epilogue deletes it from
the open set, the `%bom` of `[0 0]` inside the outer hint sees no open key,
and all four hint ops are dropped: the outer frame is lost from the trace.
The key `[%clue hint reg]` lacks the hinted formula that the keys `%defer`
and `%konst` carry to tell nested hints apart.  The same with `%mean` for
both hints; with `%mean` outside and `%spot` inside the keys differ and the
traces agree.

`TrimBr` is the property a proof needs and the pass lacks: a stack of open
frames `K o` at the start of every reachable block (`brOp`, `brBody`: the
keyed pushes and pops of `traceKey`, and the frames without key of a `%hdp`
or `%hde` of `%hunk`, `%hand`, `%lose`), empty at block `0`, which every body
pops only on top with the key it pushed, never pushes a key already open, and
hands alike to every jump target.  It held on the raw code of all 143 cases
of `optcheck.hoon` and of the 51 formulas of `trimcheck.hoon` (8 compiles
each), and at every call of `+trim-trace-hints` there but in the witness's
case, where `+alias` breaks it.  `TrimKeepsBr` is the statement under it
(not proved).  With `TrimBr`, the frames the code before has on its trace
past those of the code after are those of dropped keys; such a key is open
in the walk wherever its frame is on the stack (`trimBody_open`, with
`KNodup`, the keys of the stack distinct), and an op that may crash or an end
that may leave makes every open key unsafe (`trimBody_uns`), so at every
crash point the two traces are equal.  `ReadsOK` covers the reads of a
dropped `%hdp` or `%hmp`; a dropped pop finds its frame on top.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- `key` of `+trim-trace-hints`. -/
inductive TKey
  | clue (hint : Nat) (reg : Nat)
  | defer (a : Bell) (v : List Nat) (f : Noun)
  | konst (n : Noun) (f : Noun)
  deriving DecidableEq

/-- `trace`: the key of a trace hint op, and whether it opens the hint. -/
def traceKey : Pole → Option (Bool × TKey)
  | Pole.hdp n p _ => if n = Tag.spot ∨ n = Tag.mean then some (true, TKey.clue n p) else none
  | Pole.hde n p _ => if n = Tag.spot ∨ n = Tag.mean then some (false, TKey.clue n p) else none
  | Pole.hmp a v f => some (true, TKey.defer a v f)
  | Pole.hme a v f => some (false, TKey.defer a v f)
  | Pole.hcp n f => some (true, TKey.konst n f)
  | Pole.hce n f => some (false, TKey.konst n f)
  | _ => none

/-- `pole-not-crashing`. -/
def notCrashing : Pole → Bool
  | Pole.imm _ _ | Pole.mov _ _ | Pole.con _ _ _ | Pole.hed _ _ | Pole.tal _ _ | Pole.hsp _ _
  | Pole.hse _ _ | Pole.hdp _ _ _ | Pole.hde _ _ _ | Pole.hmp _ _ _ | Pole.hme _ _ _ | Pole.hcp _ _
  | Pole.hce _ _ | Pole.equ _ _ => true
  | _ => false

/-- The terminators after which open keys stay safe: `?(%clq %eqq %brz %hop)`. -/
def finQuiet : Termin → Bool
  | Termin.clq _ _ _ | Termin.eqq _ _ _ _ | Termin.brz _ _ _ | Termin.hop _ => true
  | _ => false

/-- The inner `|-` over the body: the keys open and the unsafe keys. -/
def trimBody : List Pole → List TKey → List TKey → List TKey × List TKey
  | [], opn, uns => (opn, uns)
  | op :: body, opn, uns =>
    match traceKey op with
    | some (true, k) => trimBody body (k :: opn) uns
    | some (false, k) => trimBody body (opn.filter (· ≠ k)) uns
    | none => if notCrashing op then trimBody body opn uns else trimBody body opn (opn ++ uns)

/-- The keys open at the start of `o`: the union of `out` over its
predecessors. -/
def trimOpen (rev : Map (List Nat)) (out : Map (List TKey)) (o : Nat) : List TKey :=
  (getJa rev o).foldl (fun acc p => acc ++ (HoonMap.get out p).getD []) []

/-- The walk over `topo` that makes `unsafe`. -/
def trimWalk (bl : Map Blob) (rev : Map (List Nat)) : List Nat → Map (List TKey) → List TKey → Option (List TKey)
  | [], _, uns => some uns
  | o :: topo, out, uns => (HoonMap.get bl o).bind fun b =>
      let r := trimBody b.body (trimOpen rev out o) uns
      trimWalk bl rev topo (HoonMap.put out o r.1) (if finQuiet b.fin then r.2 else r.1 ++ r.2)

/-- `opened`: the keys some op of some block opens. -/
def trimOpened [MapKeys Map] (bl : Map Blob) : List TKey :=
  (MapKeys.keys bl).foldl (fun acc o =>
    match HoonMap.get bl o with
    | some b => b.body.foldl (fun acc op =>
        match traceKey op with
        | some (true, k) => k :: acc
        | _ => acc) acc
    | none => acc) []

/-- The test of the `+skip`: a hint op whose key is not unsafe and is
opened. -/
def trimDrop (uns opened : List TKey) (op : Pole) : Bool :=
  match traceKey op with
  | some (_, k) => decide (k ∉ uns) && decide (k ∈ opened)
  | none => false

/-- `+run:by`: every block with the body skipped. -/
def trimRun [MapKeys Map] (bl : Map Blob) (uns opened : List TKey) : Map Blob :=
  (MapKeys.keys bl).foldl (fun acc o =>
    match HoonMap.get bl o with
    | some b => HoonMap.put acc o { b with body := b.body.filter fun op => !trimDrop uns opened op }
    | none => acc) bl

/-- `+trim-trace-hints`. -/
def trimTraceHints [MapKeys Map] (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Option (Map Blob) :=
  (trimWalk bl rev topo HoonMap.empty []).map fun uns => trimRun bl uns (trimOpened bl)

/-- **The preservation statement of `+trim-trace-hints`** (open): `Keeps`,
on a `topo` with `TopoOK` and its `+rev-cfg`. -/
def TrimKeeps [MapKeys Map] : Prop :=
  ∀ (c : Straight Map) topo bl', TopoOK c.blocks topo →
    trimTraceHints c.blocks topo (revCfg c.blocks topo) = some bl' → Keeps c (withBlocks c bl')

/-! ## Bracketed trace hints -/

/-- The action of an op on the stack of the frames this function pushed,
`none` where it breaks the bracketing: a keyed push of a key not open, a
keyed pop of the key on top, a push or pop of a frame without key
(`%hdp`/`%hde` of a tag that `stopTag` keeps, other than `%spot`, `%mean`). -/
def brOp (g : List (Option TKey)) (op : Pole) : Option (List (Option TKey)) :=
  match traceKey op with
  | some (true, k) => if some k ∈ g then none else some (some k :: g)
  | some (false, k) =>
    match g with
    | some k' :: g0 => if k' = k then some g0 else none
    | _ => none
  | none =>
    match op with
    | Pole.hdp n _ _ => if stopTag n then some (none :: g) else some g
    | Pole.hde n _ _ =>
      if stopTag n then
        match g with
        | none :: g0 => some g0
        | _ => none
      else some g
    | _ => some g

/-- `brOp` along a body. -/
def brBody : List (Option TKey) → List Pole → Option (List (Option TKey))
  | g, [] => some g
  | g, op :: l => (brOp g op).bind fun g' => brBody g' l

/-- **Trace hints bracketed**: a stack of open frames at the start of every
reachable block, empty at block `0`, that the body takes to the stack of every
jump target. -/
def TrimBr (bl : Map Blob) (K : Nat → List (Option TKey)) : Prop :=
  K 0 = [] ∧ ∀ o b, Reach bl o → HoonMap.get bl o = some b →
    ∃ g, brBody (K o) b.body = some g ∧ ∀ j ∈ getJmps b.fin, K j.there = g

/-- The preservation statement of `+trim-trace-hints` under `TrimBr`
(open; `TrimKeeps` without it is false, see the header). -/
def TrimKeepsBr [MapKeys Map] : Prop :=
  ∀ (c : Straight Map) topo bl' K, TopoOK c.blocks topo → TrimBr c.blocks K →
    trimTraceHints c.blocks topo (revCfg c.blocks topo) = some bl' → Keeps c (withBlocks c bl')

/-- The keys of a stack are distinct. -/
def KNodup (g : List (Option TKey)) : Prop := (g.filterMap id).Nodup

/-- The walk of a body only adds to the unsafe keys. -/
theorem trimBody_uns_mono : ∀ (l : List Pole) (opn uns : List TKey), ∀ k ∈ uns, k ∈ (trimBody l opn uns).2
  | [], _, _, _, hk => hk
  | op :: l, opn, uns, k, hk => by
    unfold trimBody
    split
    · exact trimBody_uns_mono l _ _ k hk
    · exact trimBody_uns_mono l _ _ k hk
    · split
      · exact trimBody_uns_mono l _ _ k hk
      · exact trimBody_uns_mono l _ _ k (List.mem_append_right _ hk)

/-- An op without key keeps the keys of the stack. -/
theorem brOp_none {op : Pole} {g g1 : List (Option TKey)} (e : traceKey op = none) (h : brOp g op = some g1) :
    g1.filterMap id = g.filterMap id := by
  unfold brOp at h
  rw [e] at h
  simp only at h
  cases op with
  | hdp n p f =>
    simp only at h
    split at h <;> (cases h; simp)
  | hde n p f =>
    simp only at h
    split at h
    · split at h
      · cases h; simp
      · cases h
    · cases h; rfl
  | _ => cases h; rfl

/-- **The walk of a body keeps the keys of the bracketed stack open**: if
the keys of the stack at the start are open, so are those at the end. -/
theorem trimBody_open : ∀ (l : List Pole) (g g' : List (Option TKey)) (opn uns : List TKey),
    brBody g l = some g' → KNodup g → (∀ k, some k ∈ g → k ∈ opn) →
      KNodup g' ∧ ∀ k, some k ∈ g' → k ∈ (trimBody l opn uns).1
  | [], g, g', opn, uns, h, hn, ho => by
    simp only [brBody, Option.some.injEq] at h
    subst h
    exact ⟨hn, ho⟩
  | op :: l, g, g', opn, uns, h, hn, ho => by
    simp only [brBody, Option.bind_eq_some_iff] at h
    obtain ⟨g1, h1, h2⟩ := h
    unfold trimBody
    cases e : traceKey op with
    | none =>
      have hk := brOp_none e h1
      have hn1 : KNodup g1 := by unfold KNodup; rw [hk]; exact hn
      have ho1 : ∀ k, some k ∈ g1 → k ∈ opn := fun k hm => by
        have : k ∈ g1.filterMap id := List.mem_filterMap.mpr ⟨some k, hm, rfl⟩
        rw [hk] at this
        obtain ⟨a, ha, hak⟩ := List.mem_filterMap.mp this
        cases a with
        | none => cases hak
        | some a => cases hak; exact ho _ ha
      simp only
      split
      · exact trimBody_open l g1 g' opn _ h2 hn1 ho1
      · exact trimBody_open l g1 g' opn _ h2 hn1 ho1
    | some p =>
      obtain ⟨b, k0⟩ := p
      unfold brOp at h1
      rw [e] at h1
      cases b with
      | true =>
        simp only at h1 ⊢
        split at h1
        · cases h1
        · rename_i hni
          cases h1
          refine trimBody_open l _ g' _ uns h2 ?_ ?_
          · unfold KNodup
            simp only [List.filterMap_cons, id]
            refine List.nodup_cons.mpr ⟨fun hm => hni ?_, hn⟩
            obtain ⟨a, ha, hak⟩ := List.mem_filterMap.mp hm
            cases a with
            | none => cases hak
            | some a => cases hak; exact ha
          · intro k hm
            rcases List.mem_cons.mp hm with hm | hm
            · cases hm; exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ho k hm)
      | false =>
        simp only at h1 ⊢
        match g, h1, hn, ho with
        | some k' :: g0, h1, hn, ho =>
          simp only at h1
          split at h1
          · rename_i hk'
            simp only [Option.some.injEq] at h1
            subst h1 hk'
            have hn' : (k' :: g0.filterMap id).Nodup := by
              unfold KNodup at hn; simpa [List.filterMap_cons] using hn
            obtain ⟨hnot, hn0⟩ := List.nodup_cons.mp hn'
            refine trimBody_open l g0 g' _ uns h2 hn0 ?_
            intro k hm
            refine List.mem_filter.mpr ⟨ho k (List.mem_cons_of_mem _ hm), ?_⟩
            have : k ≠ k' := fun hkk => hnot (by subst hkk; exact List.mem_filterMap.mpr ⟨some k, hm, rfl⟩)
            simpa using this
          · cases h1
        | none :: g0, h1, _, _ => simp at h1
        | [], h1, _, _ => simp at h1

/-- The walk of a body, split. -/
theorem trimBody_append : ∀ (l1 l2 : List Pole) (opn uns : List TKey),
    trimBody (l1 ++ l2) opn uns = trimBody l2 (trimBody l1 opn uns).1 (trimBody l1 opn uns).2
  | [], _, _, _ => rfl
  | op :: l1, l2, opn, uns => by
    cases e : traceKey op with
    | none =>
      cases h : notCrashing op <;> simp only [List.cons_append, trimBody, e, h] <;>
        exact trimBody_append l1 l2 _ _
    | some p =>
      obtain ⟨b, k⟩ := p
      cases b <;> simp only [List.cons_append, trimBody, e] <;> exact trimBody_append l1 l2 _ _

/-- **At an op that may crash the open keys of the bracketed stack are
unsafe**: the keys of the stack there end in the unsafe keys of the body. -/
theorem trimBody_crash (pre : List Pole) (op : Pole) (post : List Pole) {g gm : List (Option TKey)}
    {opn uns : List TKey} (h : brBody g pre = some gm) (hn : KNodup g) (ho : ∀ k, some k ∈ g → k ∈ opn)
    (e : traceKey op = none) (hc : notCrashing op = false) :
    ∀ k, some k ∈ gm → k ∈ (trimBody (pre ++ op :: post) opn uns).2 := by
  intro k hk
  rw [trimBody_append]
  have hk' := (trimBody_open pre g gm opn uns h hn ho).2 k hk
  simp only [trimBody, e, hc]
  exact trimBody_uns_mono post _ _ k (List.mem_append_left _ hk')

end Opt
end SkaModel
end Formalization
