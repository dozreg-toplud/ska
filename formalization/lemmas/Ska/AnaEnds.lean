import lemmas.Ska.PokeHalt
import lemmas.Ska.AnaFuel
import lemmas.Ska.GraphClose

/-!
# The analysis ends: the argument of the Hoon, the pieces, what is proved

`AnaEnds` of `PokeHalt.lean` asks that the model's `skaPoke` return, at the
fuel the model of `+poke` gives it, on every root identity `[&+s f]` from a
state with `InvB`.  The model is fuelled and `none` is a crash or too little
fuel, so `AnaEnds` says two things of the Hoon: no branch that crashes is
taken, and the recursion of the analysis is finite.

## 1. The termination argument of the Hoon, loop by loop

1. `fol-loop` within one run.  It recurses on the parts of the formula.
   `%8` and `%9` are rewritten into `%7` forms whose parts are parts of the
   formula and small fixed formulas, so a weight that counts `%8` and `%9`
   above `%7` decreases.  The rest leaves the formula: `%11 %bare` analyses
   only `[0 1]` and `[1 fol]` and then makes an indirect call (`bare-call`),
   `%11 %memo` and `%mean` make direct calls (never inlined, as `memo-key` or
   `defer` is set), and an inlined call analyses a formula that
   `+inlineable` accepts, which has no `%2` and no `%9`, so an inlined
   formula inlines nothing.  Every other exit of `fol-loop` is a direct call
   through `resolve`.  Proved for the formulas that do not inline, with the direct calls
   fixed: `folLoopR_stable` of `FolWeight.lean` (the result is the same at
   every fuel from `folW fol` on).
2. The `resolve` loop.  Its only turn that loops is `%he`: the identity
   `[a f]` becomes `[(msg-sock a b) f]` for the subject sock `b` of a frame of
   `f` on the stack with `(he-sock a b)`.  When `a = b` the identity is that
   frame's, which is in the graph, so the first branch (exact match) ends the
   loop before `+recursive-call`.  When `a ≠ b`, `(msg-sock a b)` is not `a`:
   it equals `a` only if `b` refines `a` (every leaf `|` of `a` replaced by a
   subtree), and then `+he-sock` fails, because the embedding never shrinks
   the cape (`cape-size`), so `b` would have to replace leaves `|` by leaves
   `&` only, and a leaf `|` embeds no leaf `&`.  `+msg-sock` only cuts
   subtrees of `a` down to `|+~`, so `cape-size` plus the number of leaves
   `&` strictly decreases at each `%he` turn.  For example `a = [[& |] [5 ~]]`
   and `b = &+[5 6]` give `|+~`.  Proved: `msgSock_he_lt` of `HeTurn.lean`,
   and `resolve_he_bound` of `HeBound.lean` (at most `heMeasure` of the
   subject sock turns `%he` in a row, given `SInv`, which puts the stack in
   the graph).  On the real compiler a `%he` turn was never followed by
   another (item 2 of section 2).
3. The stack of functions in progress.  A new frame is pushed only for an
   identity that is not in the graph, not a memo hit, not `%rec` and not
   `%he`.  The formulas of frames are callable formulas: a direct call needs
   a formula sock whose cape is exactly `&` (`=(& cape.sock.prod.f)`).  Such
   socks come from the root subject `&+s` and its parts (`+pull:so`,
   `+hed:so`, `+tel:so`), from literals `[1 p]`, from the value of a constant
   formula (the cons of two `saf` operands), from products of memo hits and
   the `+pull:so` of `+patch-prod`.  `+knit:so` never makes the cape `&` (it
   makes `[& &]`, `+con:ca` does not normalize), so a formula consed at run
   time is called indirectly.  So the callable formulas lie in the closure of
   `s`, the root formula and the memo's constants under parts and values of
   constant formulas, whose nouns are no larger than the largest of these and
   whose atoms are theirs: a finite set.  An infinite stack would then hold
   infinitely many frames of one formula `f`.  Past `he-threshold` (32)
   frames of `f`, every new frame of `f` has a subject that embeds the
   subject of no earlier frame of `f` (else `%he` or `%rec`).  The leaves of
   these socks (a leaf `|`, a leaf `&` holding a noun of the finite set
   above) are finitely many, and `+he-sock` is the homeomorphic embedding of
   binary trees over them (couple, or a part of the bigger one), a well
   quasi order by Kruskal's theorem.  So such a sequence of subjects is
   finite and the stack is finite.  It is not bounded in advance: Kruskal
   gives no bound, and the Hoon's comment at `+recursive-call` says so.  Not
   proved in Lean.
4. The member loop runs once over a finite list (the `+sweep` of the
   component).  Structural.
5. The pass loop at the root of a component.  It goes on while a pass found
   a new function (`next` moved) or changed an entry
   (`[less-code prod map indi seek]`).  What decreases is not settled.  The
   product and its map only lose knowledge across runs (`+double-int` with the
   old entry, then `+msg-anno` once `moved`), and `kap` of
   `BakeMeasure.lean` drops on a strict loss of nouns of a normal sock.
   `indi` and `seek` are merged by `+msg-ca` only when the rest is equal, and
   then only grow.  `less-code` is `(app:ca want bus)` of the last run and is
   not merged: it shrinks when a callee's product loses the formula of a
   call, but nothing in the Hoon forbids it from growing back, and the
   functions found by a pass can be culled by a later one and found again.
   No measure for the pass loop is known.  On the real compiler the largest
   number of passes of one loop was 6 (section 2).
   There is none: the loop does not end on the poke of
   `tools/hoon/swaploop.hoon`, where `less-code` cycles through a swap of the
   sample (`PassLoop.lean`), so `CgHalts` below is false of the Hoon.
6. The inner loops `+sweep`, `+cull` (its loop over the queue) and
   `+prune-callgraph` end on a finite graph.  Proved here for
   `+prune-callgraph` (`pruneLoop_ends`), given that the graph is closed under
   callees.

## 2. What can crash, and a gap in the invariant

The model returns `none` on a crash too.  Besides fuel, the analysis can
crash on `+above` and `+pop` of an identity not on the stack, `got:by` of
`order` in the member loop and the `%rec` branch, the `?>` on a void code
requirement, `+huge:so` and `+msg-sock` on socks that are not well formed,
and `+prune-callgraph` on a callee that is not in the graph.  The last needs
the final graph to be closed under callees.  A memo hit of an earlier poke
puts its datum in the graph with its callees, and `InvB` says nothing of the
callees of the memo's entries (`Entry` does not keep them), so `AnaEnds` as
stated may be false: an `InvB` state whose memo has an entry with a callee
that the root hits makes `+prune-callgraph` crash.  Every memo the Hoon makes
has entries with no callees (`+memo-final-entry` clears them, and the memo
starts empty), which `memoNoCallees_skaPoke` proves of the model.  So the
pieces below take `MemoNoCallees` of the memo as a hypothesis, and
`anaEnds_of_N` gives `AnaEnds` for an invariant that implies it; `InvB`
should gain that field (`PokeBake.lean` is frozen this session).

Measured on the real compiler (an instrumented copy of the library, the 19
pokes of `he2.hoon`, `sitesmeet4.hoon` and `voidscc.hoon`, 2026-11-24, no
timeout): the largest pass loop took 6 passes (`(ream '(add 1 2)')`, 1094
functions, 2309 runs), the stack was at most 331 deep, at most 32 frames of
one formula were on the stack (the three pokes of `he2.hoon`, exactly
`he-threshold`), and a `resolve` loop took at most one `%he` turn.

## 3. The pieces

* `CgHalts`: `+ska-callgraph` returns at some fuel.  Not proved.  It holds
  when items 1, 2, 3 and 5 of section 1 hold and nothing crashes.
* `GraphClosed`: the graph it returns holds the root and is closed under
  callees.  Not proved.  True of the Hoon by the argument of `+cull` (a
  popped component calls no frame below it, a culled member is called only
  by culled members), and every poke checked returned through
  `+prune-callgraph`.  On the 26 pokes of `sitesmeet4.hoon`, `he2.hoon`,
  `voidscc.hoon` and `prodsame.hoon` every callee of the returned graph was
  an entry (1760 entries, 4052 edges).  The arm pieces are in
  `GraphClose.lean` (`cull_closed` and the puts).
* `pruneLoop_ends`, proved: the loop of `+prune-callgraph` ends on a graph
  closed under callees, within one more than the queue's length plus, for
  each entry not visited, one more than its number of callees.
* `anaHalts_of`: `CgHalts` and `GraphClosed` give `AnaHalts`, the analysis
  part of `+ska-poke` returns at some fuel.  `anaEndsN_of_halts`: it returns
  at the fuel `anaFuel`, and `anaEndsN_mono` at every larger fuel.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## The memo's entries have no callees -/

theorem memoNoCallees_empty : MemoNoCallees (Treap.empty : Memo M) := by
  intro f ms s e c h
  simp [Treap.get_empty] at h

theorem memoNoCallees_putMi {m : Memo M} {i : Ident} {d : FDatum M} (hm : MemoNoCallees m)
    (hd : ∀ c, Treap.get d.callees c = none) : MemoNoCallees (putMi m i d) := by
  intro f ms s e c h1 h2
  rcases putMi_get h1 h2 with ⟨ms', h1', h2'⟩ | ⟨rfl, -⟩
  · exact hm f ms' s e c h1' h2'
  · exact hd c

/-- The memo of `pokeMemo` keeps `MemoNoCallees`. -/
theorem memoNoCallees_pokeMemo (pruned : Callgraph M) {memo : Memo M} (hm : MemoNoCallees memo) :
    MemoNoCallees (pokeMemo pruned memo).2 := by
  have key : ∀ (l : List (Ident × FDatum M)) (a : M Bell (FDatum M)) (mm : Memo M), MemoNoCallees mm →
      MemoNoCallees (l.foldl (fun acc e => (Treap.put acc.1 (⟨e.2.less, e.1.2⟩ : Bell) e.2,
        putMi acc.2 (memoFinalEntry e.1 e.2).1 (memoFinalEntry e.1 e.2).2)) (a, mm)).2 := by
    intro l
    induction l with
    | nil => intro a mm h; exact h
    | cons e l ih =>
      intro a mm h
      exact ih _ _ (memoNoCallees_putMi h (fun c => by simp [memoFinalEntry, Treap.get_empty]))
  exact key _ _ _ hm

/-- **Every memo the analysis part of `+ska-poke` makes has entries with no
callees**, from a memo that has none. -/
theorem memoNoCallees_skaPoke {env : Env R} {n : Nat} {root : Ident} {memo memo' : Memo M} {reg reg' : R}
    {pruned : Callgraph M} {dats : M Bell (FDatum M)} {rd : FDatum M} (hm : MemoNoCallees memo)
    (h : skaPoke env n root memo reg = some (pruned, dats, memo', rd, reg')) : MemoNoCallees memo' := by
  unfold skaPoke at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨gr, -, pr, -, rd', -, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, -, rfl, -, -⟩ := he
  exact memoNoCallees_pokeMemo _ hm

/-! ## The loop of `+prune-callgraph` ends -/

/-- The callees of a datum, as `+prune-callgraph` queues them. -/
def calleeIds (d : FDatum M) : List Ident := (Treap.tap d.callees).map (·.1.id)

/-- The part of the potential of one listed entry. -/
def pruneTerm (out : Callgraph M) (e : Ident × FDatum M) : Nat :=
  if Treap.has out e.1 = true then 0 else 1 + (Treap.tap e.2.callees).length

/-- What is left to visit: for each entry of `g` not in `out`, one more than
its number of callees. -/
def pruneLeft (g out : Callgraph M) : Nat := ((Treap.tap g).map (pruneTerm out)).sum

theorem has_put_ident (out : Callgraph M) (i k : Ident) (d : FDatum M) :
    Treap.has (Treap.put out i d) k = if k = i then true else Treap.has out k := by
  unfold Treap.has
  rw [Treap.get_put]
  split <;> simp

theorem pruneTerm_put_le {out : Callgraph M} {i : Ident} {d : FDatum M} (e : Ident × FDatum M) :
    pruneTerm (Treap.put out i d) e ≤ pruneTerm out e := by
  unfold pruneTerm
  rw [has_put_ident]
  split
  · simp
  · exact Nat.le_refl _

theorem pruneSum_put_le {out : Callgraph M} {i : Ident} {d : FDatum M} :
    ∀ l : List (Ident × FDatum M), (l.map (pruneTerm (Treap.put out i d))).sum ≤ (l.map (pruneTerm out)).sum
  | [] => Nat.le_refl _
  | e :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (pruneTerm_put_le e) (pruneSum_put_le l)

theorem pruneSum_put_lt {out : Callgraph M} {i : Ident} {d : FDatum M} (hi : ¬ Treap.has out i = true) :
    ∀ l : List (Ident × FDatum M), (i, d) ∈ l →
      (l.map (pruneTerm (Treap.put out i d))).sum + (1 + (Treap.tap d.callees).length) ≤
        (l.map (pruneTerm out)).sum
  | [], h => by simp at h
  | e :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have h1 : pruneTerm (Treap.put out i d) (i, d) = 0 := by
        unfold pruneTerm; rw [has_put_ident]; simp
      have h2 : pruneTerm out (i, d) = 1 + (Treap.tap d.callees).length := by
        unfold pruneTerm; simp [hi]
      have := pruneSum_put_le (out := out) (i := i) (d := d) l
      omega
    · have := pruneSum_put_lt hi l h
      have := pruneTerm_put_le (out := out) (i := i) (d := d) e
      omega

/-- Visiting a new entry lowers `pruneLeft` by one more than its number of
callees. -/
theorem pruneLeft_put {g out : Callgraph M} {i : Ident} {d : FDatum M} (hi : ¬ Treap.has out i = true)
    (hd : Treap.get g i = some d) :
    pruneLeft g (Treap.put out i d) + (1 + (Treap.tap d.callees).length) ≤ pruneLeft g out :=
  pruneSum_put_lt hi _ ((Treap.mem_tap g i d).mpr hd)

/-- **The loop of `+prune-callgraph` ends** on a graph closed under callees,
when every identity of the queue is in the graph, within one more than the
queue's length plus `pruneLeft`. -/
theorem pruneLoop_ends (g : Callgraph M)
    (hcl : ∀ i d, Treap.get g i = some d → ∀ c ∈ calleeIds d, Treap.get g c ≠ none) :
    ∀ (n : Nat) (q : List Ident) (out : Callgraph M), q.length + pruneLeft g out < n →
      (∀ c ∈ q, Treap.get g c ≠ none) → ∃ out', pruneLoop g n q out = some out'
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, [], out, _, _ => ⟨out, by simp [pruneLoop]⟩
  | n + 1, i :: q, out, hn, hq => by
    simp only [pruneLoop]
    by_cases hc : Treap.has out i = true
    · rw [if_pos hc]
      refine pruneLoop_ends g hcl n q out ?_ (fun c hc' => hq c (List.mem_cons_of_mem _ hc'))
      simp only [List.length_cons] at hn
      omega
    · rw [if_neg hc]
      cases hd : Treap.get g i with
      | none => exact absurd hd (hq i (by simp))
      | some d =>
        simp only [Option.bind_some]
        have hle := pruneLeft_put hc hd
        refine pruneLoop_ends g hcl n _ _ ?_ ?_
        · simp only [List.length_append, List.length_map, List.length_cons] at hn ⊢
          omega
        · intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hq c (List.mem_cons_of_mem _ h)
          · exact hcl i d hd c h

/-- **`+prune-callgraph` returns** on a graph that holds the root and is
closed under callees. -/
theorem pruneCallgraph_ends {g : Callgraph M} {root : Ident} (hr : Treap.get g root ≠ none)
    (hcl : ∀ i d, Treap.get g i = some d → ∀ c ∈ calleeIds d, Treap.get g c ≠ none) :
    ∃ pruned, pruneCallgraph (2 + pruneLeft g Treap.empty) g root = some pruned :=
  pruneLoop_ends g hcl _ [root] Treap.empty (by simp only [List.length_cons, List.length_nil]; omega)
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact hr)

end Ana

namespace PokeM

open Ana Bake

variable {M : Type → Type → Type} [Treap M] {J R : Type}

/-- **`+ska-callgraph` returns at some fuel** on every root identity of a
poke from a state with `InvB` whose memo has no callees.  Not proved. -/
def CgHalts (lib : Lib) (env : Env R) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j, InvB lib L → MemoNoCallees L.memo →
    ∃ n g reg', skaCallgraph env n (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (g, reg')

/-- **The final graph holds the root and is closed under callees.**  Proved:
`graphClosed`. -/
def GraphClosed (lib : Lib) (env : Env R) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j n g reg', InvB lib L → MemoNoCallees L.memo →
    skaCallgraph env n (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (g, reg') →
    Treap.get g (Sock.mk Cape.yes s, f) ≠ none ∧
    ∀ i d, Treap.get g i = some d → ∀ c ∈ calleeIds d, Treap.get g c ≠ none

/-- **The analysis part of `+ska-poke` returns at some fuel.** -/
def AnaHalts (lib : Lib) (env : Env R) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j, InvB lib L → MemoNoCallees L.memo →
    ∃ n r, skaPoke env n (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r

/-- `AnaEnds` with the memo's lack of callees as a hypothesis. -/
def AnaEndsN (lib : Lib) (env : Env R) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j, InvB lib L → MemoNoCallees L.memo →
    ∃ r, skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r

theorem inCallees_of_calleeIds {d : FDatum M} {c : Ident} (h : c ∈ calleeIds d) : InCallees d.callees c := by
  unfold calleeIds at h
  obtain ⟨⟨ce, v⟩, hm, rfl⟩ := List.mem_map.mp h
  refine ⟨ce.seat, ?_⟩
  show Treap.has d.callees ce = true
  simp [Treap.has, (Treap.mem_tap _ _ _).mp hm]

/-- **`GraphClosed` holds**: under `InvB` (for the memo's well-formed and
normal products) and `MemoNoCallees`, the final graph holds the root and is
closed under callees (`skaCallgraph_closed`, `GraphClose.lean`). -/
theorem graphClosed (lib : Lib) (env : Env R) (regOf : J → R) : GraphClosed (M := M) lib env regOf := by
  intro s f L j n g reg' hI hm h
  obtain ⟨code, hp⟩ := hI.ghost
  obtain ⟨hr, hc⟩ := skaCallgraph_closed env L.memo hp.wf hp.memoNorm hm (wf_root s) (normSock_yes s)
    (fun e => Sock.noConfusion e) h
  exact ⟨hr, fun i d hd c hcm => hc i d hd c (inCallees_of_calleeIds hcm)⟩

/-- **`AnaHalts` from the two pieces.** -/
theorem anaHalts_of {lib : Lib} {env : Env R} {regOf : J → R}
    (hc : CgHalts (M := M) lib env regOf) (hg : GraphClosed (M := M) lib env regOf) :
    AnaHalts (M := M) lib env regOf := by
  intro s f L j hI hm
  obtain ⟨n, g, reg', h1⟩ := hc s f L j hI hm
  obtain ⟨hr, hcl⟩ := hg s f L j n g reg' hI hm h1
  obtain ⟨pruned, h2⟩ := pruneCallgraph_ends hr hcl
  have hroot := (pruneCallgraph_spec h2).2.1
  obtain ⟨rd, hrd⟩ : ∃ rd, Treap.get pruned (Sock.mk Cape.yes s, f) = some rd := by
    unfold Treap.has at hroot
    exact Option.isSome_iff_exists.mp hroot
  have h1' := skaCallgraph_fuel_le env (Nat.le_max_left n (2 + pruneLeft g Treap.empty)) _ _ _ _ h1
  have h2' := pruneCallgraph_fuel_le (Nat.le_max_right n (2 + pruneLeft g Treap.empty)) _ _ _ h2
  refine ⟨max n (2 + pruneLeft g Treap.empty), (pruned, (pokeMemo pruned L.memo).1, (pokeMemo pruned L.memo).2, rd, reg'), ?_⟩
  simp only [skaPoke, h1', h2', hrd, Option.bind_some, Option.map_some]

/-- **`AnaHalts` from `CgHalts` alone.** -/
theorem anaHalts_of_cgHalts {lib : Lib} {env : Env R} {regOf : J → R}
    (hc : CgHalts (M := M) lib env regOf) : AnaHalts (M := M) lib env regOf :=
  anaHalts_of hc (graphClosed lib env regOf)

/-- A fuel at which the analysis returns, when there is one. -/
noncomputable def anaFuel (env : Env R) (regOf : J → R) (s f : Noun) (L : LongB M) (j : J) : Nat := by
  classical
  exact if h : ∃ n r, skaPoke env n (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r then
    Classical.choose h else 0

/-- **The analysis returns at `anaFuel`.** -/
theorem anaEndsN_of_halts {lib : Lib} {env : Env R} {regOf : J → R} (h : AnaHalts (M := M) lib env regOf) :
    AnaEndsN (M := M) lib env (anaFuel env regOf) regOf := by
  intro s f L j hI hm
  have hx := h s f L j hI hm
  unfold anaFuel
  rw [dif_pos hx]
  exact Classical.choose_spec hx

/-- **More fuel does no harm.** -/
theorem anaEndsN_mono {lib : Lib} {env : Env R} {regOf : J → R} {fuel fuel' : Noun → Noun → LongB M → J → Nat}
    (h : AnaEndsN lib env fuel regOf) (hle : ∀ s f L j, fuel s f L j ≤ fuel' s f L j) :
    AnaEndsN lib env fuel' regOf := by
  intro s f L j hI hm
  obtain ⟨r, hr⟩ := h s f L j hI hm
  exact ⟨r, skaPoke_fuel_le env (hle s f L j) _ _ _ _ hr⟩

/-- **`AnaEnds` of `PokeHalt.lean`** from `AnaEndsN`, for an invariant
under which the memo has no callees. -/
theorem anaEnds_of_N {lib : Lib} {env : Env R} {regOf : J → R} {fuel : Noun → Noun → LongB M → J → Nat}
    (h : AnaEndsN lib env fuel regOf) (hm : ∀ L : LongB M, InvB lib L → MemoNoCallees L.memo) :
    AnaEnds lib env fuel regOf :=
  fun s f L j hI => h s f L j hI (hm L hI)

end PokeM

end SkaModel
end Formalization
