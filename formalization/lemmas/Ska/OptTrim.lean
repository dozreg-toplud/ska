import lemmas.Ska.OptTopo

/-!
# `+trim-trace-hints`

The pass (`nock-compilation.hoon`, about line 8902, with the counts of commit
753abe9) drops trace hints whose frame nothing can observe.  Line by line:

1. `key` and `trace` (`TKey`, `traceKey`): a `%hdp` or `%hde` with the tag
   `%spot` or `%mean` has the key `[%clue n p]`, a `%hmp` or `%hme` the key
   `[%defer a v f]`, a `%hcp` or `%hce` the key `[%konst n f]`; the `p`, `m`,
   `c` ops open their key, the `e` ops close it.  Other ops have no key (a
   `%hdp` of another tag among them).
2. `unsafe` (`trimWalk`, `trimBody`): a walk over `topo` with a map `out`
   from each walked block to the open keys at its end, counted: the Hoon's
   `(map key @ud)` is a `Cnt`, a function to `Nat` where a key absent from
   the map counts `0` (the map never holds `0`, since an epilogue at count
   `1` or less deletes the key, so `~(key by open)` is the keys of positive
   count).  At a block, the counts at its start are the `+uno:by` with `max`
   of `out` over its predecessors in `rev` (`Cnt.join`, a pointwise `max`;
   `~(gut by out) p` is empty for a predecessor not walked yet).  Along the
   body an opening op adds one to its key, a closing op deletes its key at
   count `1` or less and takes one off otherwise, and any other op that is
   not `pole-not-crashing` (`%imm %mov %con %hed %tal %hsp %hse %hdp %hde
   %hmp %hme %hcp %hce %equ`) makes every key of positive count unsafe
   (`Uns.add`; the unsafe set is a test `Uns`).  At the end, a terminator
   that is not `%clq`, `%eqq`, `%brz`, `%hop` makes every key of positive
   count unsafe.  Then `out` of the block is the counts at its end.
3. `opened` (`trimOpened`): the keys that some op of some block opens
   (`+rep:by`, a union, so its order does not matter).
4. The result (`trimTraceHints`): `+run:by` over the blocks, each body
   without the hint ops whose key is not unsafe and is opened.  Every block
   is kept with its parameters and end.

The model returns `none` where the Hoon crashes (`got` of a label of `topo`
that is not a block).  Checked on the real compiler
(`tools/hoon/trimcheck.hoon`, the model written again in Hoon with maps and
a hand-folded `max`): equal to the pass at every call over 408 compiles
(`mis=0`), and 714 runs of the optimized code agree with `+mock` (`bad=0`,
2026-11-24).

## What preservation needs

`TrimKeeps` states it in the form `Keeps`, on a `topo` with `TopoOK` and its
`+rev-cfg`, which is how `+optimize-once` calls it (after `+alias`, with
`topo` filtered by the blocks that remain).  Without a bracketing of the hint
ops it is false of any walk of this shape: the interpreter's epilogues pop
the top frame whatever its key, so in `push A, push B, pop A, crash, pop B`
the key `A` is never open at the crash, its two ops are dropped, and the
trace at the crash changes from `A`'s frame to `B`'s.  `+comp` never emits
that, so the statement takes `TrimBr`.

`TrimBr` is the bracketing: a stack of open frames `K o` at the start of
every reachable block (`brOp`, `brBody`: the keyed pushes and pops of
`traceKey`, and the frames without key of a `%hdp` or `%hde` of `%hunk`,
`%hand`, `%lose`), empty at block `0`, which every body pops only on top with
the key it pushed and hands alike to every jump target.  Unlike the version
for the old pass, a key may be pushed while it is open: `+alias` can give two
nested hints one clue register (`tools/hoon/trimbug.hoon`), and the counts
handle that.  This `TrimBr` held at every call of the pass in
`trimcheck.hoon` (408 compiles, the witness of `trimbug.hoon` included) and
on raw code.  `TrimKeepsBr` is the statement under it, proved in
`OptTrimSim.lean` (`trimKeepsBr`).  With
`TrimBr`, every key has at least as many frames on the stack as its count in
the walk (`CntLe`, kept along a body: `trimBody_open`), so a key with a frame
on the stack is open, and an op that may crash makes it unsafe
(`trimBody_crash`).  So the frames the code before has on its trace past
those of the code after are those of dropped keys, which no crash point
sees.  `ReadsOK` covers the reads of a dropped `%hdp` or `%hmp`; a dropped
pop finds its frame on top.
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

/-- The open keys of the walk, counted: the Hoon's `(map key @ud)`, a key
absent from the map counting `0`. -/
abbrev Cnt := TKey → Nat

/-- The empty map. -/
def Cnt.empty : Cnt := fun _ => 0

/-- `put` of a count, `del` at `0`. -/
def Cnt.set (m : Cnt) (k : TKey) (n : Nat) : Cnt := fun k' => if k' = k then n else m k'

/-- `(~(uno by a) b)` with the gate `max`. -/
def Cnt.join (a b : Cnt) : Cnt := fun k => max (a k) (b k)

/-- The unsafe keys, as a test. -/
abbrev Uns := TKey → Bool

/-- `(~(uni in uns) ~(key by m))`: the keys of positive count added. -/
def Uns.add (u : Uns) (m : Cnt) : Uns := fun k => u k || decide (0 < m k)

/-- The inner `|-` over the body: the counts of the open keys and the unsafe
keys. -/
def trimBody : List Pole → Cnt → Uns → Cnt × Uns
  | [], opn, uns => (opn, uns)
  | op :: body, opn, uns =>
    match traceKey op with
    | some (true, k) => trimBody body (opn.set k (opn k + 1)) uns
    | some (false, k) => trimBody body (if opn k ≤ 1 then opn.set k 0 else opn.set k (opn k - 1)) uns
    | none => if notCrashing op then trimBody body opn uns else trimBody body opn (uns.add opn)

/-- The counts at the start of `o`: the join of `out` over its
predecessors. -/
def trimOpen (rev : Map (List Nat)) (out : Map Cnt) (o : Nat) : Cnt :=
  (getJa rev o).foldl (fun acc p => acc.join ((HoonMap.get out p).getD Cnt.empty)) Cnt.empty

/-- The walk over `topo` that makes `unsafe`. -/
def trimWalk (bl : Map Blob) (rev : Map (List Nat)) : List Nat → Map Cnt → Uns → Option Uns
  | [], _, uns => some uns
  | o :: topo, out, uns => (HoonMap.get bl o).bind fun b =>
      let r := trimBody b.body (trimOpen rev out o) uns
      trimWalk bl rev topo (HoonMap.put out o r.1) (if finQuiet b.fin then r.2 else r.2.add r.1)

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
def trimDrop (uns : Uns) (opened : List TKey) (op : Pole) : Bool :=
  match traceKey op with
  | some (_, k) => !uns k && decide (k ∈ opened)
  | none => false

/-- `+run:by`: every block with the body skipped. -/
def trimRun [MapKeys Map] (bl : Map Blob) (uns : Uns) (opened : List TKey) : Map Blob :=
  (MapKeys.keys bl).foldl (fun acc o =>
    match HoonMap.get bl o with
    | some b => HoonMap.put acc o { b with body := b.body.filter fun op => !trimDrop uns opened op }
    | none => acc) bl

/-- `+trim-trace-hints`. -/
def trimTraceHints [MapKeys Map] (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Option (Map Blob) :=
  (trimWalk bl rev topo HoonMap.empty fun _ => false).map fun uns => trimRun bl uns (trimOpened bl)

/-- **The preservation statement of `+trim-trace-hints`** without a
bracketing: `Keeps`, on a `topo` with `TopoOK` and its `+rev-cfg`.  False of
any walk of this shape on code that is not bracketed (the header); the
statement to prove is `TrimKeepsBr`. -/
def TrimKeeps [MapKeys Map] : Prop :=
  ∀ (c : Straight Map) topo bl', TopoOK c.blocks topo →
    trimTraceHints c.blocks topo (revCfg c.blocks topo) = some bl' → Keeps c (withBlocks c bl')

/-! ## Bracketed trace hints -/

/-- The action of an op on the stack of the frames this function pushed,
`none` where it breaks the bracketing: a keyed push (of any key, open or
not), a keyed pop of the key on top, a push or pop of a frame without key
(`%hdp`/`%hde` of a tag that `stopTag` keeps, other than `%spot`, `%mean`). -/
def brOp (g : List (Option TKey)) (op : Pole) : Option (List (Option TKey)) :=
  match traceKey op with
  | some (true, k) => some (some k :: g)
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
(proved: `trimKeepsBr`, `OptTrimSim.lean`; `TrimKeeps` without a bracketing
is false, see the header). -/
def TrimKeepsBr [MapKeys Map] : Prop :=
  ∀ (c : Straight Map) topo bl' K, TopoOK c.blocks topo → TrimBr c.blocks K →
    trimTraceHints c.blocks topo (revCfg c.blocks topo) = some bl' → Keeps c (withBlocks c bl')

/-- The frames of key `k` on a stack. -/
def frameCount (k : TKey) : List (Option TKey) → Nat
  | [] => 0
  | f :: g => (if f = some k then 1 else 0) + frameCount k g

/-- Every key has at most as many frames on the stack as its count. -/
def CntLe (g : List (Option TKey)) (opn : Cnt) : Prop := ∀ k, frameCount k g ≤ opn k

theorem frameCount_pos {k : TKey} : ∀ {g : List (Option TKey)}, some k ∈ g → 0 < frameCount k g
  | [], h => absurd h List.not_mem_nil
  | f :: g, h => by
    unfold frameCount
    rcases List.mem_cons.mp h with h | h
    · subst h; simp only [if_true]; omega
    · have := frameCount_pos h; omega

/-- **A key with a frame on the stack is open.** -/
theorem CntLe.pos {g : List (Option TKey)} {opn : Cnt} (h : CntLe g opn) {k : TKey} (hk : some k ∈ g) :
    0 < opn k :=
  Nat.lt_of_lt_of_le (frameCount_pos hk) (h k)

/-- The walk of a body only adds to the unsafe keys. -/
theorem trimBody_uns_mono : ∀ (l : List Pole) (opn : Cnt) (uns : Uns) (k : TKey), uns k = true →
    (trimBody l opn uns).2 k = true
  | [], _, _, _, hk => hk
  | op :: l, opn, uns, k, hk => by
    unfold trimBody
    split
    · exact trimBody_uns_mono l _ _ k hk
    · exact trimBody_uns_mono l _ _ k hk
    · split
      · exact trimBody_uns_mono l _ _ k hk
      · exact trimBody_uns_mono l _ _ k (by simp [Uns.add, hk])

/-- An op without key keeps the frames of every key. -/
theorem brOp_none {op : Pole} {g g1 : List (Option TKey)} (e : traceKey op = none) (h : brOp g op = some g1) :
    ∀ k, frameCount k g1 = frameCount k g := by
  intro k
  unfold brOp at h
  rw [e] at h
  simp only at h
  cases op with
  | hdp n p f =>
    simp only at h
    split at h <;> (cases h; simp [frameCount])
  | hde n p f =>
    simp only at h
    split at h
    · split at h
      · cases h; simp [frameCount]
      · cases h
    · cases h; rfl
  | _ => cases h; rfl

/-- **The walk of a body keeps the count of every key at least its frames
on the bracketed stack.** -/
theorem trimBody_open : ∀ (l : List Pole) (g g' : List (Option TKey)) (opn : Cnt) (uns : Uns),
    brBody g l = some g' → CntLe g opn → CntLe g' (trimBody l opn uns).1
  | [], g, g', opn, uns, h, ho => by
    simp only [brBody, Option.some.injEq] at h
    subst h
    exact ho
  | op :: l, g, g', opn, uns, h, ho => by
    simp only [brBody, Option.bind_eq_some_iff] at h
    obtain ⟨g1, h1, h2⟩ := h
    unfold trimBody
    cases e : traceKey op with
    | none =>
      have hk := brOp_none e h1
      have ho1 : CntLe g1 opn := fun k => by rw [hk]; exact ho k
      simp only
      split
      · exact trimBody_open l g1 g' opn _ h2 ho1
      · exact trimBody_open l g1 g' opn _ h2 ho1
    | some p =>
      obtain ⟨b, k0⟩ := p
      unfold brOp at h1
      rw [e] at h1
      cases b with
      | true =>
        simp only [Option.some.injEq] at h1 ⊢
        subst h1
        refine trimBody_open l _ g' _ uns h2 fun k => ?_
        have := ho k
        simp only [frameCount, Cnt.set]
        by_cases hk : k = k0
        · subst hk; simp; omega
        · have : (some k0 = some k) = False := by simp; exact fun h => hk h.symm
          simp [hk, this]; omega
      | false =>
        simp only at h1 ⊢
        match g, h1, ho with
        | some k' :: g0, h1, ho =>
          simp only at h1
          split at h1
          · rename_i hk'
            simp only [Option.some.injEq] at h1
            subst h1 hk'
            refine trimBody_open l g0 g' _ uns h2 fun k => ?_
            have := ho k
            simp only [frameCount] at this
            by_cases hk : k = k'
            · subst hk
              simp only [if_true] at this
              split <;> simp [Cnt.set] <;> omega
            · have hne : (some k' = some k) = False := by simp; exact fun h => hk h.symm
              simp only [hne, if_false] at this
              split <;> simp [Cnt.set, hk] <;> omega
          · cases h1
        | none :: g0, h1, _ => simp at h1
        | [], h1, _ => simp at h1

/-- The walk of a body, split. -/
theorem trimBody_append : ∀ (l1 l2 : List Pole) (opn : Cnt) (uns : Uns),
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

/-- **At an op that may crash, every key with a frame on the bracketed stack
is unsafe**: the keys of the stack there end in the unsafe keys of the
body. -/
theorem trimBody_crash (pre : List Pole) (op : Pole) (post : List Pole) {g gm : List (Option TKey)}
    {opn : Cnt} {uns : Uns} (h : brBody g pre = some gm) (ho : CntLe g opn)
    (e : traceKey op = none) (hc : notCrashing op = false) :
    ∀ k, some k ∈ gm → (trimBody (pre ++ op :: post) opn uns).2 k = true := by
  intro k hk
  rw [trimBody_append]
  have hpos := (trimBody_open pre g gm opn uns h ho).pos hk
  simp only [trimBody, e, hc]
  exact trimBody_uns_mono post _ _ k (by simp [Uns.add, hpos])

/-! ## The join at a block's start -/

theorem trimOpen_fold_ge (out : Map Cnt) : ∀ (l : List Nat) (acc : Cnt) (k : TKey),
    acc k ≤ (l.foldl (fun acc p => acc.join ((HoonMap.get out p).getD Cnt.empty)) acc) k
  | [], _, _ => Nat.le_refl _
  | q :: l, acc, k => by
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (trimOpen_fold_ge out l _ k)
    exact Nat.le_max_left (acc k) _

theorem trimOpen_fold_mem (out : Map Cnt) {p : Nat} {c : Cnt} (hc : HoonMap.get out p = some c) :
    ∀ (l : List Nat) (acc : Cnt), p ∈ l → ∀ k,
      c k ≤ (l.foldl (fun acc p => acc.join ((HoonMap.get out p).getD Cnt.empty)) acc) k
  | [], _, h, _ => absurd h List.not_mem_nil
  | q :: l, acc, h, k => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [List.foldl_cons]
      refine Nat.le_trans ?_ (trimOpen_fold_ge out l _ k)
      simp only [Cnt.join, hc, Option.getD_some]
      exact Nat.le_max_right _ _
    · exact trimOpen_fold_mem out hc l _ h k

theorem CntLe.mono {g : List (Option TKey)} {a b : Cnt} (h : CntLe g a) (hab : ∀ k, a k ≤ b k) : CntLe g b :=
  fun k => Nat.le_trans (h k) (hab k)

/-- **The counts at a block's start cover the stack of each walked
predecessor**: if a predecessor `p` in `rev` has counts `c` in `out` at
least its frames on a stack `g`, so do the counts the walk starts `o` with
(the `max` join of `+uno:by`). -/
theorem trimOpen_cntLe {rev : Map (List Nat)} {out : Map Cnt} {o p : Nat} {c : Cnt} {g : List (Option TKey)}
    (hp : p ∈ getJa rev o) (hc : HoonMap.get out p = some c) (hg : CntLe g c) : CntLe g (trimOpen rev out o) :=
  hg.mono (trimOpen_fold_mem out hc _ _ hp)

/-- The stack at block `0` is empty, so any counts cover it. -/
theorem cntLe_nil (opn : Cnt) : CntLe [] opn := fun _ => Nat.zero_le _

end Opt
end SkaModel
end Formalization
