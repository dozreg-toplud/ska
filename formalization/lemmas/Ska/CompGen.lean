import lemmas.Ska.CompSixNxRel

/-!
# `RunOKGen`: one relation on runs at an arbitrary lazy goal

README Gaps 12.39.  `RunOKLS` (`CompFrontS.lean`) asks of a run under
`%next L th` that its result's entries have DISTINCT labels, and every
parent lemma reads `Flat` of the needs.  A `%6` result is a fork, its
calling test wraps the fork sides at their own labels (`+past-fork`), a kept
hint makes a bond inside a bond (`+lazy-bound`), and `+fork` (phase F of a
`%6`) re-points the goal entries' blocks.  `RunOKGen` is stated for an
ARBITRARY lazy goal `L` and an ARBITRARY lazy result `nex.laz` (forks and
bonds to any depth, labels possibly repeated), with the frame and the
semantic core apart:

* `FrameG`, every clause that is not semantic: the clauses of `RunOKLB`
  that never read flatness (`re` ... `econd`, over `entries`, which ranges
  over the whole tree), `nodup` replaced by `LabDisj` (the entries at one
  label have pairwise apart registers), `GrowU` replaced by `GrowG` (an old
  block keeps its parameters, and its `fin` unless it is a goal entry's
  block that `+fork` re-pointed: `RepointG`), and `fronts`: every goal
  entry's block got ops in front (same `fin`) or was re-pointed;
* `SemCoreG`, the semantic core: `nec`, the fronts' semantics `FrontsG`
  (the ops in front of a goal entry's block fill its need after ANY ops that
  fill the CONJUNCTION of the result's needs at that label, `FillSemL`), and
  `sem`/`semB` assuming `AgreeG`: the result's fresh lazy blocks hold, in
  front of the run's body, ops that fill the conjunction of the needs of
  ALL the entries at that label (`suresAt`, any depth).  Two entries at one
  label are filled by the same block, so they need not have one need (that
  candidate fails: `CompGenCheck.lean`), only fills that do not clobber each
  other, which `LabDisj` gives the final pass.

Checked before any proof (`CompGenCheck.lean`, `CompGenCheckB.lean`): no
clause of `FrameG` fails on 308,850 runs; the semantic clause at the top on
109,728 runs.  `RunOKLS.toGen`: the old tower feeds the new relation.

A re-pointed goal entry (`RepointG`, phase F) has no semantic clause here:
its fill goes through a branch on the test's register (`+fork`'s
`[brz proxy kid0 kid1]`), so it is not a list of ops in front of the block,
and its semantics needs a precondition on registers other than the inputs
(the register of the test), which `FillSem` cannot state.  That is the
first clause of the general relation that is not yet stated (Gaps 12.39).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Entries at one label -/

/-- The sure needs of the entries at the label `o`, at any depth, in the
order of `entries`. -/
def suresAt (laz : Lazy S) (o : Nat) : List (Sure S) :=
  ((entries laz).filter fun e => decide (e.1 = o)).map fun e => e.2.sure

theorem filter_fst_nil {α : Type} (l : List (Nat × α)) (o : Nat) (h : o ∉ l.map Prod.fst) :
    l.filter (fun x => decide (x.1 = o)) = [] :=
  List.filter_eq_nil_iff.mpr fun x hx hd => h (List.mem_map.mpr ⟨x, hx, of_decide_eq_true hd⟩)

theorem filter_fst_single {α : Type} : ∀ (l : List (Nat × α)) (e : Nat × α), (l.map Prod.fst).Nodup → e ∈ l →
    l.filter (fun x => decide (x.1 = e.1)) = [e]
  | [], _, _, he => by simp at he
  | x :: xs, e, hnd, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | he'
    · rw [List.filter_cons_of_pos (by simp), filter_fst_nil xs _ hnd.1]
    · have hx : x.1 ≠ e.1 := fun h => hnd.1 (by rw [h]; exact List.mem_map.mpr ⟨e, he', rfl⟩)
      rw [List.filter_cons_of_neg (by simpa using hx)]
      exact filter_fst_single xs e hnd.2 he'

theorem suresAt_single {laz : Lazy S} {e : Nat × Lazy S} (hnd : ((entries laz).map Prod.fst).Nodup)
    (he : e ∈ entries laz) : suresAt laz e.1 = [e.2.sure] := by
  simp only [suresAt, filter_fst_single _ e hnd he, List.map_cons, List.map_nil]

theorem suresAt_nil {laz : Lazy S} {o : Nat} (h : o ∉ (entries laz).map Prod.fst) : suresAt laz o = [] := by
  simp only [suresAt, filter_fst_nil _ o h, List.map_nil]

/-- **The fill of a conjunction**: from registers holding `s0` as `ned`
asks, the ops `A` fill every need of `Ls` for `s` and keep the input
registers and every register below `lo` outside them, or crash when `s` has
not the shape and looks of one of them.  `FillSem` is the case `[L]`. -/
def FillSemL (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (lo : Nat) (Ls : List (Sure S)) (A : List Pole) (s0 s : Noun) : Prop :=
  ∀ R : Map (Option Noun), HoldsN ned R s0 →
    ((∀ L ∈ Ls, FitsS L s) → ∃ R', Runs lib O c gul st t A R R' ∧ (∀ L ∈ Ls, HoldsS L R' s) ∧
      ∀ x, (NMem ned x ∨ x < lo) → (∀ L ∈ Ls, ¬ NMem L.ned x) → SkaModel.read x R' = SkaModel.read x R) ∧
    ((∃ L ∈ Ls, ¬ FitsS L s) → Crashes lib O c gul st t A R)

section Fill
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
  {ned : Need} {lo : Nat} {A : List Pole} {s0 s : Noun}

theorem FillSemL.single {L : Sure S} (h : FillSemL lib O c gul st t ned lo [L] A s0 s) :
    FillSem lib O c gul st t ned lo L A s0 s := by
  intro R hR
  refine ⟨fun f => ?_, fun nf => (h R hR).2 ⟨L, (by simp), nf⟩⟩
  obtain ⟨R', r, hh, k⟩ := (h R hR).1 (fun L' hL' => by rw [List.mem_singleton.mp hL']; exact f)
  exact ⟨R', r, hh L ((by simp)),
    fun x hx hn => k x hx (fun L' hL' => by rw [List.mem_singleton.mp hL']; exact hn)⟩

theorem FillSem.toL {L : Sure S} (h : FillSem lib O c gul st t ned lo L A s0 s) :
    FillSemL lib O c gul st t ned lo [L] A s0 s := by
  intro R hR
  refine ⟨fun f => ?_, fun ⟨L', hL', nf⟩ => (h R hR).2 (by rw [List.mem_singleton.mp hL'] at nf; exact nf)⟩
  obtain ⟨R', r, hh, k⟩ := (h R hR).1 (f L ((by simp)))
  exact ⟨R', r, fun L' hL' => by rw [List.mem_singleton.mp hL']; exact hh,
    fun x hx hn => k x hx (hn L ((by simp)))⟩

theorem FillSemL.nil (h : FillSemL (S := S) lib O c gul st t ned lo [] A s0 s) :
    FillSem lib O c gul st t ned lo (Sure.bunt : Sure S) A s0 s := by
  intro R hR
  refine ⟨fun _ => ?_, fun nf => absurd (fitsS_bunt s) nf⟩
  obtain ⟨R', r, _, k⟩ := (h R hR).1 (fun _ h => by simp at h)
  exact ⟨R', r, holdsS_bunt R' s, fun x hx _ => k x hx (fun _ h => by simp at h)⟩

/-- **Fills at one label compose** (the final pass puts the fill of each
entry at a label in front of the block): with the registers of `L1` below
`lo` and apart from those of `Ls`, and the input registers from `lo`. -/
theorem FillSemL.cons {L1 : Sure S} {Ls : List (Sure S)} {A1 A2 : List Pole}
    (h1 : FillSem lib O c gul st t ned lo L1 A1 s0 s) (h2 : FillSemL lib O c gul st t ned lo Ls A2 s0 s)
    (hl : ∀ x, NMem L1.ned x → x < lo) (hn : ∀ x, NMem ned x → lo ≤ x)
    (hap : ∀ L ∈ Ls, ∀ x, NMem L1.ned x → ¬ NMem L.ned x) :
    FillSemL lib O c gul st t ned lo (L1 :: Ls) (A1 ++ A2) s0 s := by
  intro R hR
  have nd : ∀ x, NMem ned x → ¬ NMem L1.ned x := fun x hx hm => by have := hl x hm; have := hn x hx; omega
  refine ⟨fun f => ?_, fun ⟨L, hL, nf⟩ => ?_⟩
  · obtain ⟨R1, r1, hh1, k1⟩ := (h1 R hR).1 (f L1 (by simp))
    have hR1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x (Or.inl hx) (nd x hx)) hR
    obtain ⟨R2, r2, hh2, k2⟩ := (h2 R1 hR1).1 (fun L hL => f L (by simp [hL]))
    refine ⟨R2, r1.append r2, fun L hL => ?_, fun x hx hno => ?_⟩
    · rcases List.mem_cons.mp hL with h | hL'
      · subst h
        exact ⟨HoldsN.agree _ (fun x hx => k2 x (Or.inr (hl x hx)) (fun L' hL' => hap L' hL' x hx)) hh1.1, hh1.2⟩
      · exact hh2 L hL'
    · rw [k2 x hx (fun L hL => hno L (by simp [hL])), k1 x hx (hno L1 (by simp))]
  · by_cases f1 : FitsS L1 s
    · obtain ⟨R1, r1, _, k1⟩ := (h1 R hR).1 f1
      have hR1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x (Or.inl hx) (nd x hx)) hR
      rcases List.mem_cons.mp hL with h | hL'
      · subst h; exact absurd f1 nf
      · exact Crashes.append_right r1 ((h2 R1 hR1).2 ⟨L, hL', nf⟩)
    · exact Crashes.append_left ((h1 R hR).2 f1)

end Fill

/-- **`AgreeLB` per label**: the result's fresh lazy blocks hold, in front of
the run's body, ops that fill the needs of ALL the entries at that label. -/
def AgreeG (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (cond : Map (Nat × List Nat)) (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cond)) ∧
  ∀ o ∈ (entries laz).map Prod.fst, g0.bo ≤ o → ∃ A B th, HoonMap.get g1.blocks o = some ⟨[], B, Termin.hop th⟩ ∧
    HoonMap.get c.blocks o = some ⟨[], A ++ B.map (renPole (unproxy cond)), Termin.hop (renJmp (unproxy cond) th)⟩ ∧
    FillSemL lib O c gul st t ned g1.re (suresAt laz o) A s0 s

/-! ## The entry semantics (README Gaps 12.39, item 4) -/

/-- **A jump into a lazy block runs as a fill and then the block's old
body**: for the input `x` that `N` holds, some ops `A` fill every need of
`Ls` for `s` (`FillSemL`), and from EVERY registers where `N` holds `x` a
jump into `a` is `A ++ B` then `fin`.  The ops `A` may depend on the input
`x` (which branch a `+fork` takes is read from a register of `N`) but not on
the other registers.  A block `A ++ B` meets it (`EntA.ofBlock`); a goal
entry's block that `+fork` re-pointed meets it through `[brz p k0 k1]`, the
kid's fill and front, the join's parameters and the old body, with `A` the
path the test's value in `N` selects.  Fronts in this form compose with the
fronts `FrontLG` of an earlier part by `++`, with no lemma on register maps. -/
def EntA (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (N : Need) (lo : Nat) (Ls : List (Sure S)) (a : Nat) (B : List Pole) (fin : Termin) (x s : Noun) : Prop :=
  ∃ A : List Pole, FillSemL lib O c gul st t N lo Ls A x s ∧
    ∀ R : Map (Option Noun), HoldsN N R x →
      goJ lib O c gul st R t (jmp0 a) = execBlob lib O c gul st R t ⟨[], A ++ B, fin⟩ []

section EntA
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
  {N : Need} {lo : Nat} {Ls : List (Sure S)} {a : Nat} {A B : List Pole} {fin : Termin} {x s : Noun}

/-- **A block that is a fill in front of a body** has the entry semantics. -/
theorem EntA.ofBlock (hb : HoonMap.get c.blocks a = some ⟨[], A ++ B, fin⟩)
    (h : FillSemL lib O c gul st t N lo Ls A x s) : EntA lib O c gul st t N lo Ls a B fin x s :=
  ⟨A, h, fun R _ => goJ_jmp0 R t a _ hb⟩

/-- **The fill, as a jump**: from registers where `N` holds `x`, a jump
into `a` goes on to the body with the needs filled, or crashes. -/
theorem EntA.goes (h : EntA lib O c gul st t N lo Ls a B fin x s) {R : Map (Option Noun)} (hR : HoldsN N R x) :
    ((∀ L ∈ Ls, FitsS L s) → ∃ R', goJ lib O c gul st R t (jmp0 a) = execBlob lib O c gul st R' t ⟨[], B, fin⟩ [] ∧
      (∀ L ∈ Ls, HoldsS L R' s) ∧
      ∀ y, (NMem N y ∨ y < lo) → (∀ L ∈ Ls, ¬ NMem L.ned y) → SkaModel.read y R' = SkaModel.read y R) ∧
    ((∃ L ∈ Ls, ¬ FitsS L s) → goJ lib O c gul st R t (jmp0 a) = some (Tone.two t, st)) := by
  obtain ⟨A, hf, hj⟩ := h
  refine ⟨fun f => ?_, fun nf => ?_⟩
  · obtain ⟨R', r, hh, k⟩ := (hf R hR).1 f
    exact ⟨R', by rw [hj R hR]; exact r B fin, hh, k⟩
  · rw [hj R hR]; exact (hf R hR).2 nf B fin

/-- **An earlier part's front composes** with the entry semantics: a front
`F` of the later part in front of `B` turns `Ls'` into `Ls`. -/
theorem EntA.front {Ls' : List (Sure S)} {F : List Pole} {N' : Need} {lo' : Nat} {x' s' : Noun}
    (h : EntA lib O c gul st t N lo Ls' a (F ++ B) fin x s)
    (hF : ∀ A, FillSemL lib O c gul st t N lo Ls' A x s → FillSemL lib O c gul st t N' lo' Ls (A ++ F) x' s')
    (hN : ∀ R : Map (Option Noun), HoldsN N' R x' → HoldsN N R x) :
    EntA lib O c gul st t N' lo' Ls a B fin x' s' := by
  obtain ⟨A, hf, hj⟩ := h
  exact ⟨A ++ F, hF A hf, fun R hR => by rw [hj R (hN R hR), List.append_assoc]⟩

end EntA

/-- **`AgreeG` with the entry semantics** at the fresh lazy blocks: a jump
into one runs as a fill of the needs of all the entries at its label and
then its body in the final state.  `AgreeG` gives it (`AgreeG.toA`); it is
what a part whose own fresh lazy block a later part re-pointed gets (the
`q` of `[7 p q]` with `p` in phase F, `agreeGA_seven` in
`CompGenSeven.lean`).  `sem` still takes `AgreeG`, which the old tower's
`sem` clauses read (`RunOKLS.toGen`); handing `sem` this form instead is a
port of the clauses that jump into their own fresh lazy blocks (Gaps
12.39, item 8). -/
def AgreeGA (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (cond : Map (Nat × List Nat)) (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cond)) ∧
  ∀ o ∈ (entries laz).map Prod.fst, g0.bo ≤ o → ∃ B th, HoonMap.get g1.blocks o = some ⟨[], B, Termin.hop th⟩ ∧
    EntA lib O c gul st t ned g1.re (suresAt laz o) o (B.map (renPole (unproxy cond)))
      (Termin.hop (renJmp (unproxy cond) th)) s0 s

theorem AgreeG.toA {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeG lib O c gul st t cond ned g0 g1 laz s0 s) : AgreeGA lib O c gul st t cond ned g0 g1 laz s0 s :=
  ⟨h.1, fun o ho l => let ⟨A, B, th, h1, h2, h3⟩ := h.2 o ho l; ⟨B, th, h1, EntA.ofBlock h2 h3⟩⟩

/-- **The semantics of a goal entry's block that `+fork` re-pointed** (phase
F of a `%6`, and L into F): for every program that agrees with the run's
final state at every state and trace (`AgreeGA`, so a jump into a kid
runs as its fill and its body) and where a jump into `a` runs as a fill of
the result's needs at `a` and then `g1`'s block (no fill when `a` is no
result entry; it IS one on 270 runs of famA, L into F), a jump into `a` from the input
need, the run's witness `d` and the goal's sure registers `E` (holding `s0`,
`w` and the product `v`) runs as a fill of the needs of ALL the goal's
entries at `a` and then `a`'s old body.  The precondition on a register that
is not an input (the test's register, which `brz` reads) is the witness:
`Q s v d w` with `d` fresh (`FrameG.dreg`) and held where the goal's jump is
reached (`GoalSemCMD`).  Checked on the interpreter: `CompGenFCheck.lean`. -/
def FrontRG (Q : Wit) (E : Need) (g0 g1 : Gen Map) (nex : NextL S) (a : Nat) (Ls : List (Sure S)) : Prop :=
  ∃ B fin, HoonMap.get g0.blocks a = some ⟨[], B, fin⟩ ∧
  ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (ned : Need) (s0 s v : Noun) (d : Need)
    (w : Noun), (∀ r, NMem ned r → g1.re ≤ r) → Q s v d w →
    (∀ (st' : σ) (t' : Trace), AgreeGA lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) →
    (∀ (st' : σ) (t' : Trace), ∃ b, HoonMap.get g1.blocks a = some b ∧
      EntA lib O c gul st' t' ned g1.re (suresAt nex.laz a) a (unproxyBlob cf b).body (unproxyBlob cf b).fin s0 s) →
    ∀ (st : σ) (t : Trace), EntA lib O c gul st t (Need.pair (Need.pair ned d) E) g0.re Ls a
      (unproxyBlob cf ⟨[], B, fin⟩).body (unproxyBlob cf ⟨[], B, fin⟩).fin (C (C s0 w) v) v

/-- With distinct labels `AgreeG` is `AgreeLB`. -/
theorem AgreeG.toLB {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeG lib O c gul st t cond ned g0 g1 laz s0 s) (hnd : ((entries laz).map Prod.fst).Nodup) :
    AgreeLB lib O c gul st t cond ned g0 g1 laz s0 s := by
  refine ⟨h.1, fun e he l => ?_⟩
  obtain ⟨A, B, th, h1, h2, h3⟩ := h.2 e.1 (List.mem_map.mpr ⟨e, he, rfl⟩) l
  rw [suresAt_single hnd he] at h3
  exact ⟨A, B, th, h1, h2, h3.single⟩

/-! ## The frame -/

/-- **A goal entry's block re-pointed by `+fork`** (`insertHop`): ops `F`
and a hop without arguments to a fresh block, the old body (ops in front of
it allowed) and `fin` at another fresh block. -/
def RepointG (g0 g1 : Gen Map) (a : Nat) : Prop :=
  ∃ B fin F o1 o2 F2, HoonMap.get g0.blocks a = some ⟨[], B, fin⟩ ∧
    HoonMap.get g1.blocks a = some ⟨[], F, Termin.hop ⟨[], o1⟩⟩ ∧ g0.bo ≤ o1 ∧ o1 < g1.bo ∧
    g0.bo ≤ o2 ∧ o2 < g1.bo ∧ HoonMap.get g1.blocks o2 = some ⟨[], F2 ++ B, fin⟩

/-- **A goal entry's block with ops in front**, the same `fin`. -/
def FrontBlk (g0 g1 : Gen Map) (a : Nat) (F : List Pole) : Prop :=
  ∀ B fin, HoonMap.get g0.blocks a = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks a = some ⟨[], F ++ B, fin⟩

/-- **`GrowU` with re-pointed goal entries.** -/
structure GrowG (L : Lazy S) (g g' : Gen Map) : Prop where
  keep : ∀ k b, k < g.bo → HoonMap.get g.blocks k = some b →
    ∃ b', HoonMap.get g'.blocks k = some b' ∧ b'.par = b.par ∧
      (b'.fin = b.fin ∨ (k ∈ (entries L).map Prod.fst ∧ RepointG g g' k))
  new : ∀ k b', HoonMap.get g'.blocks k = some b' →
    (∃ b, HoonMap.get g.blocks k = some b ∧ b'.par = b.par) ∨ (g.bo ≤ k ∧ k < g'.bo)

theorem GrowU.toG {L : Lazy S} {g g' : Gen Map} (h : GrowU g g') : GrowG L g g' :=
  ⟨fun k b hk hb => by
    obtain ⟨b', h1, h2, h3⟩ := h.keep k b hk hb
    exact ⟨b', h1, h2, Or.inl h3⟩,
   fun k b' hb => (h.new k b' hb).imp (fun ⟨b, h1, h2, _⟩ => ⟨b, h1, h2⟩) (fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩)⟩

/-- **The entries at one label have pairwise apart registers.** -/
def LabDisj (laz : Lazy S) : Prop :=
  (entries laz).Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r

theorem labDisj_of_nodup {laz : Lazy S} (h : ((entries laz).map Prod.fst).Nodup) : LabDisj laz :=
  (List.pairwise_map.mp h).imp fun hne heq => absurd heq hne

/-- **The frame of a run at any lazy goal**: every clause that is not
semantic (`oneG` of `CompGenCheck.lean` evaluates each). -/
structure FrameG (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  re : g0.re ≤ g1.re
  bo : g0.bo ≤ g1.bo
  drop : g1.drop = g0.drop
  keep : ∀ o, o < g0.bo → o ∉ (entries L).map Prod.fst → HoonMap.get g1.blocks o = HoonMap.get g0.blocks o
  grow : GrowG L g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 (CGoal.next L.sure th) nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r →
    (∃ e0 ∈ entries L, NMem e0.2.sure.ned r) ∨ NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  labs : ∀ e ∈ entries nex.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < g1.bo)) ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  labDisj : LabDisj nex.laz
  dreg : ∀ s v d w r, Q s v d w → NMem d r → g0.re ≤ r ∧ r < g1.re
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  fronts : ∀ e ∈ entries L, (∃ F, FrontBlk g0 g1 e.1 F) ∨ RepointG g0 g1 e.1

/-- **The goal side of `FrameG`** (`goalOK` of `CompGenCheck.lean`, true of
every result there): the goal's jump and every entry's block below `bo`, the
entries' blocks `[[] B [hop _]]`, the registers below `re`, distinct, apart
within a label.  The jump must be to a block of the goal: at `genAtH 10 3`
the jump `3` is the run's own first block (`CompGenFCheck.lean`). -/
structure GoalG (L : Lazy S) (th : Jmp) (g0 : Gen Map) : Prop where
  bo : 1 ≤ g0.bo
  jmp : 1 ≤ th.there ∧ th.there < g0.bo
  lab : ∀ e ∈ entries L, 1 ≤ e.1 ∧ e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩
  eregs : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → r < g0.re
  labDisj : LabDisj L
  dist : Distinct L.sure.ned
  sregs : ∀ r, NMem L.sure.ned r → r < g0.re

/-- **A run's frame gives its parent's next part a goal**: the result at the
run's final state meets `GoalG`. -/
theorem FrameG.goalOut {L : Lazy S} {th : Jmp} {Q : Wit} {g0 g1 : Gen Map} {nex : NextL S}
    (F : FrameG (Map := Map) L th Q g0 g1 nex) (G : GoalG (Map := Map) L th g0) : GoalG (Map := Map) nex.laz nex.th g1 := by
  have hre := F.re
  have hbo := F.bo
  refine ⟨by have := G.bo; omega, ⟨F.lo, F.hi⟩, fun e he => ?_, fun e he => ⟨(F.eregs e he).1, fun r hr => ?_⟩,
    F.labDisj, F.dist, fun r hr => ?_⟩
  · obtain ⟨h, blk⟩ := F.labs e he
    rcases h with h | h
    · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
      have := G.lab e0 he0
      exact ⟨by rw [← e1]; exact this.1, by rw [← e1]; omega, blk⟩
    · exact ⟨by have := G.bo; omega, h.2, blk⟩
  · rcases (F.eregs e he).2 r hr with ⟨e0, he0, h0⟩ | h | h
    · have := (G.eregs e0 he0).2 r h0; omega
    · have := G.sregs r h; omega
    · exact h.2
  · rcases F.regs r hr with h | h
    · have := G.sregs r h; omega
    · exact h.2

/-! ## The semantic core -/

/-- **`FrontLB` between conjunctions**: after any ops `A` that fill the
needs `Ls'` of the result's entries at the label (none: `A` only keeps), the
ops `F` fill the needs `Ls` of ALL the goal's entries at that label.  Per
goal entry (`FillSem` of one need) it would be false at a goal whose label
holds two needs: for `[0 1]` (`F = []`) the fill `A` crashes when the
subject fits one of them and not the other. -/
def FrontLG (Q : Wit) (E : Need) (lo0 lo : Nat) (Ls' : List (Sure S)) (F : List Pole) (Ls : List (Sure S)) :
    Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace) (ned : Need)
    (A : List Pole) (s0 s v : Noun) (d : Need) (w : Noun), (∀ r, NMem ned r → lo ≤ r) → Q s v d w →
    FillSemL (Map := Map) lib O c gul st t ned lo Ls' A s0 s →
    FillSemL lib O c gul st t (Need.pair (Need.pair ned d) E) lo0 Ls (A ++ F) (C (C s0 w) v) v

/-- **The fronts' semantics**: a goal entry's block got ops in front that
fill its need from the result's entries at its label, or it was re-pointed
and a jump into it runs as a fill of its need and then
its old body (`FrontRG`, the precondition of the test's register carried by
the witness). -/
def FrontsG (Q : Wit) (x : Bool) (g0 g1 : Gen Map) (L : Lazy S) (nex : NextL S) : Prop :=
  ∀ a ∈ (entries L).map Prod.fst,
    (∃ F : List Pole, FrontBlk g0 g1 a F ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
        FrontLG (Map := Map) Q (gsE x L) g0.re g1.re (suresAt nex.laz a) (F.map (renPole (unproxy cf)))
          (suresAt L a)) ∨
    (RepointG g0 g1 a ∧ FrontRG (Map := Map) Q (gsE x L) g0 g1 nex a (suresAt L a))

/-- **The forward `sem`** (`SemLB` with `AgreeG`), the agreement handed at
EVERY state and trace: a kept dynamic hint runs its bond block's fill after
the push, at `(tag, v) :: t` (track J, `RunOKGBT`), and the top builds the
agreement for any trace. -/
def SemG (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
      L.sure th (Q s) r

/-- **The backward `sem`** (`SemLBB` with `AgreeG`). -/
def SemGW (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm
        nex.th L.sure th (Q s) r

/-- **The semantic core of a run at any lazy goal.** -/
structure SemCoreG (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (x : Bool)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f (CGoal.next L.sure th) s
  front : FrontsG (Map := Map) Q x g0 g1 L nex
  sem : SemG lib N P f L th Q g0 g1 nex
  semB : SemGW lib N P f L th Q g0 g1 nex

/-- **`RunOKGen`: one run under `%next L th`, for any lazy goal `L` and any
lazy result**: the frame and the semantic core. -/
structure RunOKGen (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (x : Bool)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop extends FrameG (Map := Map) L th Q g0 g1 nex,
    SemCoreG lib N P f L th Q x g0 g1 nex

/-- **What a class lemma adds** (`LOKT.run`'s clauses, checked as
`jumpNoEnt`, `jumpGoalNew`): the jump at no entry, the goal's or new. -/
structure OutG (L : Lazy S) (th : Jmp) (g0 : Gen Map) (nex : NextL S) : Prop where
  jne : nex.th.there ∉ (entries nex.laz).map Prod.fst
  jgn : nex.th = th ∨ g0.bo ≤ nex.th.there

/-! ## The old tower feeds the new relation -/

/-- **`RunOKLS` is `RunOKGen`** at a goal with distinct labels (the premise
`Nodup` of `LOKS.run`): `nodup` gives `LabDisj` and turns `AgreeG` into
`AgreeLB`, `GrowU` is `GrowG`, and the fronts read one need per label. -/
theorem RunOKLS.toGen {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit}
    {x : Bool} {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex)
    (hg : ((entries L).map Prod.fst).Nodup) :
    RunOKGen lib N P f L th Q x g0 g1 nex := by
  have hnd := R.nodup
  refine { re := R.re, bo := R.bo, drop := R.drop, keep := R.keep, grow := R.grow.toG, cfr := R.cfr, lo := R.lo,
           hi := R.hi, ent := R.ent, regs := R.regs, dist := R.dist, eregs := R.eregs, labs := R.labs,
           labDisj := labDisj_of_nodup hnd, dreg := R.dreg, ncond := R.ncond, econd := R.econd,
           fronts := fun e he => Or.inl (let ⟨F, hb, _⟩ := R.front e he; ⟨F, hb⟩),
           nec := R.nec, front := ?_, sem := ?_, semB := ?_ }
  · intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨F, hb, hf⟩ := R.front e he
    refine Or.inl ⟨F, hb, fun cf hcf => ?_⟩
    rw [suresAt_single hg he]
    rcases hf cf hcf with ⟨L', hm, fs⟩ | ⟨hn, fs⟩
    · rw [show e.1 = (e.1, L').1 from rfl, suresAt_single hnd hm]
      intro lib σ O c gul st t ned A s0 s v d w hn hq hA
      exact (fs lib σ O c gul st t ned A s0 s v d w hn hq hA.single).toL
    · rw [suresAt_nil hn]
      intro lib σ O c gul st t ned A s0 s v d w hn' hq hA
      exact (fs lib σ O c gul st t ned A s0 s v d w hn' hq hA.nil).toL
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm (fun st' => (ag st' t).toLB hnd)
      hned regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs (fun st' => (ag st' t).toLB hnd)
      hned regs hh hn res hres

end Comp
end SkaModel
end Formalization
