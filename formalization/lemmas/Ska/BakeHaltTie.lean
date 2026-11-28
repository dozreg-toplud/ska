import lemmas.Ska.BakeHalt

/-!
# Ties of `+bake-graph`: the measure with ties allowed (track Q, README Gaps 31)

`BakeDrops` (`BakeHalt.lean`) asks, in its part (a), that no change of a bake
in a worklist be a TIE (old and new bake with the same nouns).  That does
not hold of the real compiler: `tools/hoon/bakehalt-tie.hoon` makes one bell
tie three times in one poke from a state reached by a poke (its code
requirement `less.c` has the cape `[& &]` where the normal form has `&`; it
goes from `norm-sock(less.c)` back to the raw `less.c` when its only
informer's site is picked by an earlier variant, and back when a new caller
informs it).  The steps are a function of the state, so the set `Rs` of
`BakeDrops` holds the state of that step, whose fold is not `FoldOK`.

This file states what is left with ties allowed.  A tie never raises the
first two parts of the measure (`put_le`, `touchStep_le`, `touchFold_le`,
`bakeStep_le`: under `FoldW`, which is `FoldOK` without "not a tie"), so a
worklist ends when a potential `β` of the states pays for its ties: every
step is `FoldW`, and either it is `FoldOK` and `β` does not grow, or `β`
drops (`bakeStep_drop4`, measure `bakeMeasure4` = (bells with no bake, sum
of `kapXS`, `β`, length of the queue)).  `BakeDropsT` asks this per poke,
`bakeDropsT_of_drops` (`β = 0`) shows it is weaker than `BakeDrops`, and
`bakeEnds_of_dropsT` gives the leaf `BakeEnds` at `bakeFuel` from it.

On the real compiler each tie seen was paid by an event of a caller of the
bell (a loss of nouns or a first bake: README Gaps 31), so `β` would count
the ties those events can still cause.  No such `β` is defined here.
-/

namespace Formalization
namespace SkaModel

open Nock Ana Bake

namespace Bake

section Loop

variable {M : Type → Type → Type} [Treap M]

/-- **A worklist whose every step returns and lowers a measure in a
well-founded relation ends** (`bakeLoop_halts_of_drop` for any relation). -/
theorem bakeLoop_halts_of_wf {α : Type} (r : α → α → Prop) (hwf : WellFounded r) (E : BEnv M)
    (μ : List Bell → BSt M → α) (R : List Bell → M Bell Unit → BSt M → Prop)
    (hstep : ∀ cur rest qs st, R (cur :: rest) qs st → ∃ q' qs' st',
      bakeStep E cur rest qs st = some (q', qs', st') ∧ R q' qs' st' ∧ r (μ q' st') (μ (cur :: rest) st)) :
    ∀ q qs st, R q qs st → ∃ n st', bakeLoop E n q qs st = some st' := by
  intro q qs st
  suffices ∀ m, ∀ q qs st, μ q st = m → R q qs st → ∃ n st', bakeLoop E n q qs st = some st' from
    this _ q qs st rfl
  intro m
  induction m using hwf.induction with
  | _ m ih =>
    intro q qs st hm hR
    cases q with
    | nil => exact ⟨1, st, rfl⟩
    | cons cur rest =>
      obtain ⟨q', qs', st', h1, hR', hlt⟩ := hstep cur rest qs st hR
      obtain ⟨n, st'', h2⟩ := ih _ (hm ▸ hlt) q' qs' st' rfl hR'
      exact ⟨n + 1, st'', by simp only [bakeLoop, h1, Option.bind_some, h2]⟩

/-- The lexicographic order on four parts. -/
def LexLt4 (a b : Nat × Nat × Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))) a b

theorem lexLt4_wf : WellFounded LexLt4 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))).wf

theorem lex4_of {a1 a2 a3 a4 b1 b2 b3 b4 : Nat}
    (h : a1 < b1 ∨ (a1 = b1 ∧ (a2 < b2 ∨ (a2 = b2 ∧ (a3 < b3 ∨ (a3 = b3 ∧ a4 < b4)))))) :
    LexLt4 (a1, a2, a3, a4) (b1, b2, b3, b4) := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h | ⟨rfl, h⟩⟩⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ h))
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ h))

/-! ### A tie never raises the first two parts -/

/-- A new bake of a bell of `U` that had none, or that keeps at most the
nouns of an old bake with a noun (a loss or a tie): the first two parts of
the measure do not grow. -/
theorem put_le {U : List Bell} {st st' : BSt M} {c : Bell} {s : Sock} (hc : c ∈ U)
    (hbak : st'.bak = Treap.put st.bak c s)
    (hcase : Treap.get st.bak c = none ∨ ∃ o, Treap.get st.bak c = some o ∧ (∃ x, Fits o x) ∧ Sub o s) :
    LexLe2 (meas2 U st') (meas2 U st) := by
  by_cases ht : ∃ o, Treap.get st.bak c = some o ∧ Sub s o
  · right
    obtain ⟨o, ho, hso⟩ := ht
    rcases hcase with hn | ⟨o', ho', ⟨x, hx⟩, hos⟩
    · rw [hn] at ho; cases ho
    · obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
      have hget : ∀ c', Treap.get st'.bak c' = if c' = c then some s else Treap.get st.bak c' := by
        intro c'; rw [hbak, Treap.get_put]
      have hk : kapXS s = kapXS o :=
        Nat.le_antisymm (kapXS_le ⟨x, hx⟩ hos) (kapXS_le ⟨x, hos x hx⟩ hso)
      unfold meas2 unbaked kapSum
      congr 1
      · congr 1
        refine List.filter_congr fun c' _ => ?_
        by_cases e : c' = c
        · subst e; simp [hget, ho]
        · simp only [hget, if_neg e]
      · congr 1
        refine List.map_congr_left fun c' _ => ?_
        by_cases e : c' = c
        · subst e; simp only [hget, if_true, ho, hk]
        · simp only [hget, if_neg e]
  · left
    refine put_drop hc hbak ?_
    rcases hcase with hn | ⟨o, ho, hx, hos⟩
    · exact Or.inl hn
    · exact Or.inr ⟨o, ho, hx, hos, fun h => ht ⟨o, ho, h⟩⟩

/-- `TouchOK` without "not a tie": a touched callee whose bake changes is a
bell of `U`, and it had no bake or a bake with a noun. -/
def TouchW (E : BEnv M) (U : List Bell) (cur : Bell) (new : M Bell (List Sock)) (st : BSt M) (c : Bell) : Prop :=
  ∀ ch ch' st', touchStep E cur new (some (ch, st)) c = some (ch', st') → ch' ≠ ch →
    c ∈ U ∧ (Treap.get st.bak c = none ∨ ∃ o, Treap.get st.bak c = some o ∧ ∃ x, Fits o x)

/-- `TouchW` at every callee of a fold of `touchStep`. -/
def FoldW (E : BEnv M) (U : List Bell) (cur : Bell) (new : M Bell (List Sock)) :
    List Bell → List Bell × BSt M → Prop
  | [], _ => True
  | c :: l, (ch, st) => TouchW E U cur new st c ∧
      ∀ r, touchStep E cur new (some (ch, st)) c = some r → FoldW E U cur new l r

theorem foldW_of_ok {E : BEnv M} {U : List Bell} {cur : Bell} {new : M Bell (List Sock)} :
    ∀ (l : List Bell) (p : List Bell × BSt M), FoldOK E U cur new l p → FoldW E U cur new l p
  | [], _, _ => trivial
  | _ :: l, (_, _), ⟨h1, h2⟩ =>
    ⟨fun ch ch' st' h hne =>
      let ⟨hU, ho⟩ := h1 ch ch' st' h hne
      ⟨hU, ho.imp id fun ⟨o, ho, hx, _⟩ => ⟨o, ho, hx⟩⟩,
     fun r hr => foldW_of_ok l r (h2 r hr)⟩

theorem touchStep_le {E : BEnv M} {U : List Bell} {cur : Bell} {new : M Bell (List Sock)} {c : Bell}
    {ch ch' : List Bell} {st st' : BSt M} (h : touchStep E cur new (some (ch, st)) c = some (ch', st'))
    (hok : TouchW E U cur new st c) : LexLe2 (meas2 U st') (meas2 U st) := by
  obtain ⟨_, hcase⟩ := touchStep_cases h
  rcases hcase with ⟨_, hbak, _⟩ | ⟨_, fixed, bake, bake', g, g', _, hre, hcase⟩
  · right; unfold meas2 unbaked kapSum; rw [hbak]
  · rcases hcase with ⟨_, hbak, _⟩ | ⟨hbak, hch⟩
    · right; unfold meas2 unbaked kapSum; rw [hbak]
    · have hne : ch' ≠ ch := by rw [hch]; exact fun e => by simpa using congrArg List.length e
      obtain ⟨hU, hold⟩ := hok ch ch' st' h hne
      refine put_le hU hbak ?_
      rcases hold with hn | ⟨o, ho, hx⟩
      · exact Or.inl hn
      · refine Or.inr ⟨o, ho, hx, ?_⟩
        rw [ho] at hre
        exact rebakeG_grows hre

theorem touchFold_le (E : BEnv M) (U : List Bell) (cur : Bell) (new : M Bell (List Sock)) :
    ∀ (l : List Bell) (ch0 ch1 : List Bell) (st0 st1 : BSt M),
      l.foldl (touchStep E cur new) (some (ch0, st0)) = some (ch1, st1) → FoldW E U cur new l (ch0, st0) →
      LexLe2 (meas2 U st1) (meas2 U st0)
  | [], _, _, _, _, h, _ => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr rfl
  | c :: l, ch0, ch1, st0, st1, h, hok => by
    simp only [List.foldl_cons] at h
    cases h1 : touchStep E cur new (some (ch0, st0)) c with
    | none => rw [h1, touchFold_none] at h; cases h
    | some p =>
      obtain ⟨chm, stm⟩ := p
      rw [h1] at h
      exact lexLe2_trans (touchFold_le E U cur new l chm ch1 stm st1 h (hok.2 _ h1)) (touchStep_le h1 hok.1)

/-- The fold of a step from `st` at `cur` satisfies `P` (`FoldOK E U cur` or
`FoldW E U cur`), for the sites and the `new` it computes. -/
def StepFold (P : M Bell (List Sock) → List Bell → List Bell × BSt M → Prop) (E : BEnv M) (cur : Bell)
    (st : BSt M) : Prop :=
  ∀ sites new, sitesOf E st cur = some sites → sites.foldl (newStep E.vars) (some Treap.empty) = some new →
    P new ((Treap.tap (uniIn (Treap.gut st.out cur Treap.empty) (keySet new))).map Prod.fst)
      ([], { st with evals := st.evals + 1, out := Treap.put st.out cur (keySet new) })

/-- **A step with ties allowed does not raise the first two parts.** -/
theorem bakeStep_le {E : BEnv M} {U : List Bell} {cur : Bell} {rest q' : List Bell} {qs qs' : M Bell Unit}
    {st st' : BSt M} (h : bakeStep E cur rest qs st = some (q', qs', st'))
    (hok : StepFold (FoldW E U cur) E cur st) : LexLe2 (meas2 U st') (meas2 U st) := by
  simp only [bakeStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sites, hs, new, hn, ⟨changed, st3⟩, hfold, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  have hd := touchFold_le E U cur new _ [] changed
    { st with evals := st.evals + 1, out := Treap.put st.out cur (keySet new) } st3 hfold (hok sites new hs hn)
  exact hd

/-! ### The measure with a potential for ties -/

/-- **The measure with ties paid**: the bells of `U` with no bake, the sum
of `kapXS` of the bakes, a potential `β`, the length of the queue. -/
def bakeMeasure4 (U : List Bell) (β : List Bell → BSt M → Nat) (q : List Bell) (st : BSt M) :
    Nat × Nat × Nat × Nat :=
  (unbaked U st, kapSum U st, β q st, q.length)

/-- **One step lowers the measure with ties paid**: its fold is `FoldW`, and
either it is `FoldOK` and `β` does not grow, or `β` drops. -/
theorem bakeStep_drop4 {E : BEnv M} {U : List Bell} {β : List Bell → BSt M → Nat} {cur : Bell}
    {rest q' : List Bell} {qs qs' : M Bell Unit} {st st' : BSt M}
    (h : bakeStep E cur rest qs st = some (q', qs', st'))
    (hw : StepFold (FoldW E U cur) E cur st)
    (hβ : (StepFold (FoldOK E U cur) E cur st ∧ β q' st' ≤ β (cur :: rest) st) ∨ β q' st' < β (cur :: rest) st) :
    LexLt4 (bakeMeasure4 U β q' st') (bakeMeasure4 U β (cur :: rest) st) := by
  show LexLt4 (unbaked U st', kapSum U st', β q' st', q'.length)
    (unbaked U st, kapSum U st, β (cur :: rest) st, (cur :: rest).length)
  apply lex4_of
  rcases hβ with ⟨hok, hle⟩ | hlt
  · have d3 := bakeStep_drop h hok
    simp only [LexLt, bakeMeasure, Prod.lex_def] at d3
    omega
  · have d2 := bakeStep_le h hw
    simp only [LexLe2, meas2, Prod.lex_def, Prod.mk.injEq] at d2
    omega

/-- **The worklist ends when a potential pays for its ties.** -/
theorem bakeLoop_halts4 (E : BEnv M) (U : List Bell) (β : List Bell → BSt M → Nat)
    (R : List Bell → M Bell Unit → BSt M → Prop)
    (h0 : R [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E))
    (hstep : ∀ cur rest qs st, R (cur :: rest) qs st → ∃ q' qs' st',
      bakeStep E cur rest qs st = some (q', qs', st') ∧ R q' qs' st' ∧
        StepFold (FoldW E U cur) E cur st ∧
        ((StepFold (FoldOK E U cur) E cur st ∧ β q' st' ≤ β (cur :: rest) st) ∨ β q' st' < β (cur :: rest) st)) :
    ∃ n st, bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st :=
  bakeLoop_halts_of_wf LexLt4 lexLt4_wf E (fun q st => bakeMeasure4 U β q st) R
    (fun cur rest qs st hR =>
      let ⟨q', qs', st', h1, hR', hw, hβ⟩ := hstep cur rest qs st hR
      ⟨q', qs', st', h1, hR', bakeStep_drop4 h1 hw hβ⟩) _ _ _ h0

end Loop

end Bake

namespace PokeM

variable {M : Type → Type → Type} [Treap M] {J H R : Type}

/-- **What is left of `BakeEnds` with ties allowed**: `BakeDrops` with its
part (a) (no tie, refuted on the real compiler by `bakehalt-tie.hoon`)
replaced by a potential `β` that pays for the ties: every step is `FoldW`
(touched bells in `U`, no change from a bake with no noun), and is `FoldOK`
without raising `β`, or lowers `β`. -/
def BakeDropsT (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    let E := anaEnv jet fold frozen s f L j hot dats memo' rd reg'
    ∃ (U : List Bell) (β : List Bell → BSt M → Nat) (Rs : List Bell → M Bell Unit → BSt M → Prop),
      Rs [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) ∧
      ∀ cur rest qs st, Rs (cur :: rest) qs st → ∃ q' qs' st',
        bakeStep E cur rest qs st = some (q', qs', st') ∧ Rs q' qs' st' ∧
        Bake.StepFold (Bake.FoldW E U cur) E cur st ∧
        ((Bake.StepFold (FoldOK E U cur) E cur st ∧ β q' st' ≤ β (cur :: rest) st) ∨
          β q' st' < β (cur :: rest) st)

/-- `BakeDrops` gives `BakeDropsT` (with `β = 0`). -/
theorem bakeDropsT_of_drops {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : BakeDrops lib env jet fold frozen fuel regOf) : BakeDropsT lib env jet fold frozen fuel regOf := by
  intro s f L j hot pr dats memo' rd reg' hI hp
  obtain ⟨U, Rs, h0, hs⟩ := h s f L j hot pr dats memo' rd reg' hI hp
  refine ⟨U, fun _ _ => 0, Rs, h0, fun cur rest qs st hR => ?_⟩
  obtain ⟨q', qs', st', h1, hR', hok⟩ := hs cur rest qs st hR
  exact ⟨q', qs', st', h1, hR', fun sites new hs hn => Bake.foldW_of_ok _ _ (hok sites new hs hn),
    Or.inl ⟨hok, Nat.le_refl _⟩⟩

/-- **`BakeHalts` from the measure with ties paid.** -/
theorem bakeHalts_of_dropsT {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : BakeDropsT lib env jet fold frozen fuel regOf) : BakeHalts lib env jet fold frozen fuel regOf := by
  intro s f L j hot pr dats memo' rd reg' hI hp
  obtain ⟨U, β, Rs, h0, hs⟩ := h s f L j hot pr dats memo' rd reg' hI hp
  exact Bake.bakeLoop_halts4 _ U β Rs h0 hs

/-- **The leaf H2 of `HaltLeaves13`** at the fuel `bakeFuel`, with ties paid. -/
theorem bakeEnds_of_dropsT {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : BakeDropsT lib env jet fold frozen fuel regOf) : BakeEnds lib env jet fold frozen fuel bakeFuel regOf :=
  bakeEnds_of_halts (bakeHalts_of_dropsT h)

end PokeM

end SkaModel
end Formalization
