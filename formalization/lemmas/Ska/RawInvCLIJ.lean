import lemmas.Ska.RawInvCLSpec
import lemmas.Ska.RawInvKernX

/-!
# The run-level liveness with calls: the pre- and postcondition, the walks

README Gaps 14 (b), track D.  The pair `I` / `J` of `LiveRun` (checked at
every sub-run of every run of `PlainN` in `enumCX` by `RawInvCLCheckIJ.lean`)
and the parts every arm that walks a goal's lazy need uses.

* `GRegL goal r`: `r` is a register of a sure need of the goal's lazy tree.
* `GoalL g goal`: the goal's jumps are `Fresh`; every entry of its lazy tree
  (the root included) has a block with no parameter, and its sure need's
  registers are below `re` and defined by no block; the sure needs of the
  tree are pairwise apart (`NeedsApart`) and each is `Distinct`.
* **`IL K goal g`**: `ATS g`, every block's registers below `re`, every key
  of `cond` below `re`, defined by no block, no goal register, standing for
  a register below `re` that is no key; `KVan K g.bo`; `GoalL g goal`.
  **`JL K nex g`** is `IL K nex.goal g`, so `JL` gives `IL` of the next run
  (`jl_il`, the hypothesis `hJ` of `liveRun_seven`).
* `AddSt g g'`: a step that only adds ops and proxies (same `bo`, `drop`,
  `tags`; `re` grows; `cond` grows by keys from `g.re` on).
* **`walkLazy_prepG`**: a walk whose gate only puts ops in front of the
  entry's block (`GStep`: ops that define the entry's sure need and read
  first only what `R` allows) puts ops `P` in front of the blocks
  (`WalkP`), nonempty only at entries, under any `cond`: the form of
  `kernList_prep` without `KI`.
* **`unpM_prepG`**: the unproxied blocks after such a walk are the old
  unproxied ones with the ops, unproxied by the NEW `cond`, in front (old
  blocks mention only registers below the old `re`, under which `cond` did
  not change).
* `medeLoop_step`, `medeGate_step`, `medeL_walk`: `+mede` as such a walk
  with ops that read nothing; **`liveC_medeL`**: the case `%1` under
  `%next` of the liveness spec.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The pair -/

/-- `r` is a register of a sure need of the goal's lazy tree. -/
def GRegL : CGoalL S → Nat → Prop
  | CGoalL.next laz th, r => ∃ e ∈ (th.there, laz) :: entries laz, NMem e.2.sure.ned r
  | _, _ => False

/-- What the goal asks of the state. -/
def GoalL (g : Comp.Gen Map) : CGoalL S → Prop
  | CGoalL.next laz th => Fresh g th ∧ NeedsApart ((th.there, laz) :: entries laz) ∧
      ∀ e ∈ (th.there, laz) :: entries laz, (∃ b, HoonMap.get g.blocks e.1 = some b ∧ b.par = []) ∧
        Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → r < g.re ∧ ¬ Defd g.blocks r
  | CGoalL.pick z o => Fresh g z ∧ Fresh g o
  | CGoalL.done => True

/-- **The precondition of a run with calls.** -/
structure IL (K : Nat → Nat → Prop) (goal : CGoalL S) (g : Comp.Gen Map) : Prop where
  ats : ATS g
  regs : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b
  cond : ∀ k v, HoonMap.get g.cond k = some v →
    k < g.re ∧ ¬ Defd g.blocks k ∧ ¬ GRegL goal k ∧ v.1 < g.re ∧ HoonMap.get g.cond v.1 = Option.none
  kvan : KVan K g.bo
  goal : GoalL g goal

/-- **The postcondition**: the precondition of a run for the result. -/
def JL (K : Nat → Nat → Prop) (nex : NextL S) (g : Comp.Gen Map) : Prop := IL K nex.goal g

theorem jl_il {K : Nat → Nat → Prop} {nex : NextL S} {g : Comp.Gen Map} (h : JL K nex g) : IL K nex.goal g := h

/-! ## Steps that only add ops and proxies -/

/-- Same `bo`, `drop`, `tags`; `re` grows; `cond` grows by keys from `g.re` on. -/
def AddSt (g g' : Comp.Gen Map) : Prop :=
  g'.bo = g.bo ∧ g'.drop = g.drop ∧ g'.tags = g.tags ∧ g.re ≤ g'.re ∧
    (∀ k v, HoonMap.get g.cond k = some v → HoonMap.get g'.cond k = some v) ∧
    ∀ k v, HoonMap.get g'.cond k = some v → HoonMap.get g.cond k = some v ∨ g.re ≤ k

theorem AddSt.refl (g : Comp.Gen Map) : AddSt g g :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, fun _ _ h => h, fun _ _ h => Or.inl h⟩

theorem AddSt.trans {a b c : Comp.Gen Map} (h1 : AddSt a b) (h2 : AddSt b c) : AddSt a c := by
  obtain ⟨b1, d1, t1, r1, c1, n1⟩ := h1
  obtain ⟨b2, d2, t2, r2, c2, n2⟩ := h2
  refine ⟨b2.trans b1, d2.trans d1, t2.trans t1, Nat.le_trans r1 r2, fun k v h => c2 k v (c1 k v h),
    fun k v h => ?_⟩
  rcases n2 k v h with h | h
  · rcases n1 k v h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inr (Nat.le_trans r1 h)

/-- **`cond` below the old `re` is the old one** after an `AddSt` step. -/
theorem AddSt.cond_below {g g' : Comp.Gen Map} (h : AddSt g g') {x : Nat} (hx : x < g.re) :
    HoonMap.get g'.cond x = HoonMap.get g.cond x := by
  obtain ⟨-, -, -, -, c, n⟩ := h
  cases e : HoonMap.get g.cond x with
  | some v => exact c x v e
  | none =>
    cases e' : HoonMap.get g'.cond x with
    | none => rfl
    | some v =>
      rcases n x v e' with h | h
      · rw [e] at h; cases h
      · omega

/-! ## Walks whose gate only puts ops in front -/

/-- What one gate does at `x` for the sure need `s`: ops `A` in front of the
block at `x` that define the need and read first only what `R` allows. -/
def GStep (R : Comp.Gen Map → Nat → Prop) (x : Nat) (s : Sure S) (g g' : Comp.Gen Map) : Prop :=
  ∃ A, Prep (fun k => if k = x then A else []) g.blocks g'.blocks ∧ (∀ r, NMem s.ned r → r ∈ defsOf A) ∧
    ∀ y, OpsRF A y → R g' y

/-- What a walk over the entries `es` does. -/
def WalkP (R : Comp.Gen Map → Nat → Prop) (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map) : Prop :=
  ∃ P, Prep P g.blocks g'.blocks ∧ (∀ e ∈ es, ∀ r, NMem e.2.sure.ned r → r ∈ defsOf (P e.1)) ∧
    (∀ k y, OpsRF (P k) y → R g' y) ∧ ∀ k, P k ≠ [] → ∃ e ∈ es, e.1 = k

/-- **A walk over a list of entries whose gate only puts ops in front.** -/
theorem walkList_prepG {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {g0 : Comp.Gen Map}
    (hf : ∀ x s g g', St g0 g → f x s g = some ((), g') → St g g' ∧ GStep R x s g g') :
    ∀ (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map), St g0 g → walkList f es g = some ((), g') →
      St g g' ∧ WalkP R es g g'
  | [], g, g', _, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hrf g, fun _ => [], prep_nil _, fun e he => absurd he List.not_mem_nil, fun _ _ h => h.elim,
      fun _ h => absurd rfl h⟩
  | (x, l) :: rest, g, g', h0, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨s1, A, pA, kA, rA⟩ := hf x l.sure g g1 h0 h1
    obtain ⟨s2, Q, pQ, kQ, rQ, eQ⟩ := walkList_prepG hrf htr hR hf rest g1 g' (htr _ _ _ h0 s1) h2
    refine ⟨htr _ _ _ s1 s2, _, prep_trans pA pQ, fun e he r hr => ?_, fun k y hy => ?_, fun k hk => ?_⟩
    · rw [defsOf_append, List.mem_append]
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr (by simp only [if_pos rfl]; exact kA r hr)
      · exact Or.inl (kQ e he r hr)
    · rcases opsRF_append.mp hy with h | ⟨-, h⟩
      · exact rQ k y h
      · by_cases e : k = x
        · rw [if_pos e] at h
          exact hR _ _ _ s2 (rA y h)
        · rw [if_neg e] at h; exact h.elim
    · by_cases e : k = x
      · exact ⟨(x, l), List.mem_cons_self, e.symm⟩
      · have : Q k ≠ [] := by
          intro hq; apply hk; simp [hq, e]
        obtain ⟨e', he', ee⟩ := eQ k this
        exact ⟨e', List.mem_cons_of_mem _ he', ee⟩

/-- **A walk of the lazy tree whose gate only puts ops in front**: ops in
front of the root's and the entries' blocks, each defining the sure needs
of the entries at its label, nonempty only at the tree's labels. -/
theorem walkLazy_prepG {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {g0 : Comp.Gen Map}
    (hf : ∀ x s g g', St g0 g → f x s g = some ((), g') → St g g' ∧ GStep R x s g g')
    {o : Nat} {l : Lazy S} {g' : Comp.Gen Map} (h : walkLazy f o l g0 = some ((), g')) :
    St g0 g' ∧ WalkP R ((o, l) :: entries l) g0 g' := by
  have e : (walkLazy f o l : CM Map Unit) = walkList f ((o, l) :: wentries l) := by
    rw [walkLazy_flat]; rfl
  rw [e] at h
  obtain ⟨s, P, pP, kP, rP, eP⟩ := walkList_prepG hrf htr hR hf _ g0 g' (hrf g0) h
  have hm : ∀ e, e ∈ (o, l) :: entries l ↔ e ∈ (o, l) :: wentries l := fun e =>
    ((wentries_perm l).cons (o, l)).mem_iff.symm
  refine ⟨s, P, pP, fun e he => kP e ((hm e).mp he), rP, fun k hk => ?_⟩
  obtain ⟨e, he, ee⟩ := eP k hk
  exact ⟨e, (hm e).mpr he, ee⟩

/-! ## The unproxied blocks after a walk -/

/-- **The unproxied blocks after ops in front, `cond` grown above the old
`re`**: the old unproxied blocks with the ops, unproxied by the new `cond`,
in front. -/
theorem unpM_prepG {P : Nat → List Pole} {g g' : Comp.Gen Map} (hP : Prep P g.blocks g'.blocks)
    (hc : ∀ x, x < g.re → HoonMap.get g'.cond x = HoonMap.get g.cond x)
    (hR : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b) :
    Prep (fun k => (P k).map (renPole (unproxy g'.cond))) (unpM g) (unpM g') := by
  intro k
  unfold unpM
  rw [get_mapVals, get_mapVals, hP k]
  cases hb : HoonMap.get g.blocks k with
  | none => rfl
  | some b =>
    show some (renBlob (unproxy g'.cond) (pre (P k) b)) = some (pre _ (renBlob (unproxy g.cond) b))
    rw [renBlob_pre, renBlob_unproxy_grow hc (hR k b hb)]

/-- The jumps of a renamed end. -/
theorem getJmps_renFin (u : Nat → Nat) (t : Termin) : getJmps (renFin u t) = (getJmps t).map (renJmp u) := by
  cases t <;> rfl

/-- **Renaming keeps jumping down.** -/
theorem jdown_mapVals {bl : Map Blob} (h : JDown bl) (u : Nat → Nat) : JDown (mapVals (renBlob u) bl) := by
  intro k b hb j hj
  rw [get_mapVals] at hb
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
  simp only [renBlob, getJmps_renFin, List.mem_map] at hj
  obtain ⟨j0, hj0, rfl⟩ := hj
  exact h k b0 h0 j0 hj0

/-- `ATS` gives that the blocks jump down. -/
theorem ATS.jdown {g : Comp.Gen Map} (h : ATS g) : JDown g.blocks := fun k b hb j hj =>
  (h.2.2 k b hb).2.2.2 j (by rw [← getJmps_eq]; exact hj)

/-- The unproxied blocks of an `IL` state jump down below `bo`. -/
theorem IL.downU {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K goal g) :
    DownBelowP (unpM g) g.bo :=
  (jdown_mapVals h.ats.jdown _).belowP _

/-- A label with a block in an `IL` state is below `bo`. -/
theorem IL.lab {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K goal g) {k : Nat} {b : Blob}
    (hb : HoonMap.get g.blocks k = some b) : k < g.bo :=
  (h.ats.2.2 k b hb).1

/-- A goal register is no proxy. -/
theorem IL.unproxy_greg {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K goal g) {r : Nat}
    (hr : GRegL goal r) : unproxy g.cond r = r := by
  unfold unproxy
  cases e : HoonMap.get g.cond r with
  | none => rfl
  | some v => exact absurd hr (h.cond r v e).2.2.1

/-! ## `+add-ops` and the loop of `+mede` -/

theorem addOps_step {o : Nat} {A : List Pole} {g g' : Comp.Gen Map} (hd : g.drop = false)
    (h : addOps o A g = some ((), g')) :
    AddSt g g' ∧ g'.cond = g.cond ∧ Prep (fun k => if k = o then A else []) g.blocks g'.blocks := by
  simp only [addOps, hd, Bool.false_eq_true, if_false] at h
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  exact ⟨⟨rfl, hd.symm, rfl, Nat.le_refl _, fun _ _ h => h, fun _ _ h => Or.inl h⟩, rfl, prep_put hb⟩

/-- What the loop of `+mede` does at `o`: ops in front that define the need
and read nothing first. -/
def MedeS (o : Nat) (ned : Need) (g g' : Comp.Gen Map) : Prop :=
  AddSt g g' ∧ g'.cond = g.cond ∧ ∃ A, Prep (fun k => if k = o then A else []) g.blocks g'.blocks ∧
    (∀ r, NMem ned r → r ∈ defsOf A) ∧ ∀ y, ¬ OpsRF A y

theorem medeS_trans {o : Nat} {n1 n2 n : Need} {a b c : Comp.Gen Map} (h1 : MedeS o n1 a b) (h2 : MedeS o n2 b c)
    (hn : ∀ r, NMem n r → NMem n1 r ∨ NMem n2 r) : MedeS o n a c := by
  obtain ⟨s1, c1, A, pA, kA, rA⟩ := h1
  obtain ⟨s2, c2, B, pB, kB, rB⟩ := h2
  refine ⟨s1.trans s2, c2.trans c1, B ++ A, fun k => ?_, fun r hr => ?_, fun y hy => ?_⟩
  · rw [pB k, pA k]
    by_cases e : k = o
    · subst e; cases HoonMap.get a.blocks k <;> simp [pre, List.append_assoc]
    · cases HoonMap.get a.blocks k <;> simp [pre, e]
  · rw [defsOf_append, List.mem_append]
    rcases hn r hr with h | h
    · exact Or.inr (kA r h)
    · exact Or.inl (kB r h)
  · rcases opsRF_append.mp hy with h | ⟨-, h⟩
    · exact rB y h
    · exact rA y h

theorem medeS_imm {o : Nat} {som : Noun} {r : Nat} {ned : Need} {g g' : Comp.Gen Map} (hd : g.drop = false)
    (hn : ∀ y, NMem ned y → y = r) (h : addOps o [Pole.imm som r] g = some ((), g')) : MedeS o ned g g' := by
  obtain ⟨s, c, p⟩ := addOps_step hd h
  refine ⟨s, c, _, p, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hn y hy]; simp [defsOf, aliasDst]
  · rcases hy with hy | ⟨-, hy⟩
    · simp [aliasReads, aliasDst, Opt.poleRegs] at hy
    · exact hy

theorem medeS_crash {o n : Nat} {ned : Need} {g g' : Comp.Gen Map} (hd : g.drop = false)
    (h : crashNeed o (Sum.inl n) ned g = some ((), g')) : MedeS o ned g g' := by
  simp only [crashNeed] at h
  obtain ⟨r, g1, h1, h2⟩ := bind_some h
  rw [re_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨⟨b1, d1, t1, r1, c1, n1⟩, c, p⟩ := addOps_step (by simpa using hd) h2
  refine ⟨⟨b1, d1, t1, Nat.le_trans (Nat.le_succ _) r1, c1, fun k v hv => (n1 k v hv).imp id
      fun h => Nat.le_trans (Nat.le_succ _) h⟩, c, _, p, fun y hy => ?_, fun y hy => ?_⟩
  · simp only [defsOf_cons, aliasDst, Option.toList_some, Option.toList_none, List.nil_append, defsOf_fill]
    exact List.mem_cons_of_mem _ ((mem_flatten ned y).mpr hy)
  · rcases hy with hy | ⟨hne, hy⟩
    · simp [aliasReads, aliasDst, Opt.poleRegs] at hy
    · rcases hy with hy | ⟨-, hy⟩
      · rw [reads_cel] at hy; subst hy; exact hne rfl
      · exact opsRF_fill _ hy

/-- **The loop of `+mede`.** -/
theorem medeLoop_step {o : Nat} : ∀ (ned : Need) (som : Noun) (g g' : Comp.Gen Map),
    g.drop = false → medeLoop o som ned g = some ((), g') → MedeS o ned g g'
  | Need.none, som, g, g', _, h => by
    have e : g' = g := by cases som <;> simp_all [medeLoop, pure_apply]
    subst e
    exact ⟨AddSt.refl _, rfl, [], prep_same, fun r hr => hr.elim, fun y hy => hy⟩
  | Need.this r, som, g, g', hd, h => by
    unfold medeLoop at h; exact medeS_imm hd (fun y hy => hy) h
  | Need.pair p q, Noun.atom n, g, g', hd, h => by unfold medeLoop at h; exact medeS_crash hd h
  | Need.both r p q, Noun.atom n, g, g', hd, h => by unfold medeLoop at h; exact medeS_crash hd h
  | Need.pair p q, Noun.cell a b, g, g', hd, h => by
    simp only [medeLoop] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    have s1 := medeLoop_step p a g g1 hd h1
    have s2 := medeLoop_step q b g1 g' (s1.1.2.1.trans hd) h2
    exact medeS_trans s1 s2 fun r hr => hr
  | Need.both r p q, Noun.cell a b, g, g', hd, h => by
    simp only [medeLoop] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨u', g2, h2, h3⟩ := bind_some h2
    have s1 : MedeS o (Need.this r) g g1 := medeS_imm hd (fun y hy => hy) h1
    have s2 := medeLoop_step p a g1 g2 (s1.1.2.1.trans hd) h2
    have s3 := medeLoop_step q b g2 g' (s2.1.2.1.trans (s1.1.2.1.trans hd)) h3
    exact medeS_trans (medeS_trans s1 s2 (n := Need.pair (Need.this r) p) fun y hy => hy) s3
      fun y hy => by
        rcases hy with hy | hy | hy
        · exact Or.inl (Or.inl hy)
        · exact Or.inl (Or.inr hy)
        · exact Or.inr hy

/-- The step of the walk of `+mede`: same `cond`. -/
def MSt (a b : Comp.Gen Map) : Prop := AddSt a b ∧ b.cond = a.cond

/-- **The gate of `+mede` only puts ops in front**, reading nothing first. -/
theorem medeGate_step {som : Noun} {g0 : Comp.Gen Map} (hd : g0.drop = false) (x : Nat) (s : Sure S)
    (g g' : Comp.Gen Map) (h0 : MSt g0 g)
    (h : (do let ned ← sureRequireLook s; medeLoop x som ned : CM Map Unit) g = some ((), g')) :
    MSt g g' ∧ GStep (fun _ _ => False) x s g g' := by
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨k, rfl⟩ := L.gen
  have hd1 : ({ g with re := k } : Comp.Gen Map).drop = false := h0.1.2.1.trans hd
  obtain ⟨⟨b2, d2, t2, r2, c2, n2⟩, c, A, pA, kA, rA⟩ := medeLoop_step ned som _ g' hd1 h2
  refine ⟨⟨⟨b2, d2, t2, Nat.le_trans L.le r2, c2, fun k v hv => (n2 k v hv).imp id
      fun h => Nat.le_trans L.le h⟩, c⟩, A, pA, fun r hr => kA r (sureRequireLook_keeps h1 hr), fun y hy => rA y hy⟩

/-- **`+mede` is a hop block and a walk that only puts ops in front.** -/
theorem medeL_walk {th : Jmp} {som : Noun} {laz : Lazy S} {g0 g1 : Comp.Gen Map} {o : Nat}
    (hd : g0.drop = false) (h : medeL th som laz g0 = some (o, g1)) :
    o = g0.bo ∧ MSt (g0.emitted ⟨[], [], Termin.hop th⟩) g1 ∧
      WalkP (fun _ _ => False) ((o, laz) :: entries laz) (g0.emitted ⟨[], [], Termin.hop th⟩) g1 := by
  simp only [medeL] at h
  obtain ⟨o', ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨g', gg, hg, h⟩ := bind_some h
  rw [get_apply] at hg
  simp only [Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  have hde : (g0.emitted ⟨[], [], Termin.hop th⟩).drop = false := hd
  simp only [hde, Bool.false_eq_true, if_false] at h
  obtain ⟨u, g2, h2, h3⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hrf : ∀ a : Comp.Gen Map, MSt a a := fun a => ⟨AddSt.refl a, rfl⟩
  have htr : ∀ a b c : Comp.Gen Map, MSt a b → MSt b c → MSt a c := fun a b c h1 h2 =>
    ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩
  obtain ⟨s, w⟩ := walkLazy_prepG hrf htr (R := fun _ _ => False) (fun _ _ _ _ h => h)
    (fun x sur g g' h0 h => medeGate_step hde x sur g g' h0 h) h2
  exact ⟨rfl, s, w⟩

/-! ## The case `%1` under `%next` -/

/-- **`%1` under `%next`**: `+mede`'s hop block to the goal, with ops in
front of the goal's lazy blocks that define their needs and read nothing:
a register live at the hop block is live at the goal's continuation once
the goal's lazy tree defines its needs. -/
theorem liveC_medeL {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {som : Noun} {g0 g1 : Comp.Gen Map}
    {o : Nat} (hI : IL K (CGoalL.next laz th) g0) (h : medeL th som laz g0 = some (o, g1)) :
    LiveC K (CGoalL.next laz th) g0 g1 ⟨ofSure Sure.bunt, jmp0 o⟩ := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨rfl, ⟨hst, hcond⟩, P, pP, kP, rP, -⟩ := medeL_walk hd h
  obtain ⟨⟨tb, htb, -, targs⟩, -, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  have hgeb : (g0.emitted ⟨[], [], Termin.hop th⟩).blocks = HoonMap.put g0.blocks g0.bo ⟨[], [], Termin.hop th⟩ := by
    simp [Gen.emitted, hd]
  have hR : ∀ k b, HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks k = some b →
      BlobIn (· < (g0.emitted ⟨[], [], Termin.hop th⟩).re) b := by
    intro k b hb
    rw [hgeb] at hb
    by_cases e : k = g0.bo
    · subst e; rw [get_put_self] at hb; cases hb
      refine ⟨fun x hx => absurd hx List.not_mem_nil, RegsIn.nil _, ?_⟩
      show JmpIn _ th
      intro x hx; rw [targs] at hx; exact absurd hx List.not_mem_nil
    · rw [get_put_ne e] at hb; exact hI.regs k b hb
  have pU := unpM_prepG pP (fun x _ => by rw [hcond]) hR
  intro r hl
  have hl0 := hl.mono (K' := K) fun x y h => Or.inl h
  have hl1 := (liveK_prepK pU (K' := fun x y => y ∈ defsOf ((P x).map (renPole (unproxy g1.cond))))
    (fun _ _ h => h) hl0).resolve_right fun ⟨k', hk'⟩ => by
      obtain ⟨x, -, hx⟩ := opsRF_ren_back _ hk'
      exact rP k' x hx
  -- the goal's kills are among the ops' definitions
  have hgreg : ∀ e ∈ (g0.bo, laz) :: entries laz, ∀ y, NMem e.2.sure.ned y → GRegL (CGoalL.next laz th) y := by
    intro e he y hy
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨(th.there, laz), List.mem_cons_self, hy⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, hy⟩
  have hl2 : LiveK (unpM (g0.emitted ⟨[], [], Termin.hop th⟩)) (fun x y => K x y ∨ lazK g0.bo laz x y) g0.bo r := by
    refine hl1.mono fun x y hk => hk.imp id fun ⟨e, he, ex, hy⟩ => ?_
    subst ex
    rw [defsOf_ren, List.mem_map]
    refine ⟨y, kP e he y hy, ?_⟩
    rw [hcond]
    exact hI.unproxy_greg (hgreg e he y hy)
  have hlab : ∀ e ∈ (th.there, laz) :: entries laz, e.1 < g0.bo := fun e he => by
    obtain ⟨⟨b, hb, -⟩, -⟩ := hent e he
    exact hI.lab hb
  have hbo : HoonMap.get (unpM (g0.emitted ⟨[], [], Termin.hop th⟩)) g0.bo = some ⟨[], [], Termin.hop th⟩ := by
    unfold unpM
    rw [get_mapVals, hgeb, get_put_self]
    simp [renBlob, renFin, renJmp_nil _ targs]
  have hl3 := liveK_hop_root hbo targs (fun y hk => hI.kvan.van _ _ (Nat.le_refl _) hk)
    (fun e he ee => by have := hlab e (List.mem_cons_of_mem _ he); omega)
    (by have := hlab _ List.mem_cons_self; simp only at this; omega) hl2
  have hthere : th.there < g0.bo := hlab _ List.mem_cons_self
  refine (liveK_frameP hI.downU (fun x hx => ?_) hthere).mp hl3
  unfold unpM
  rw [get_mapVals, get_mapVals, hgeb, get_put_ne (Nat.ne_of_lt hx)]
  rfl

/-! ## `%0` and `%1` under every goal -/

/-- **`+from` on the result keeps the spec**: its kills are only more. -/
theorem LiveC.fromL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (h : LiveC K goal g0 g1 nex) {axe : Nat} {laz' : Lazy S} (hf : fromL axe nex.laz = some laz') :
    LiveC K goal g0 g1 ⟨laz', nex.th⟩ :=
  fun r hl => h r (hl.mono fun _ _ hk => hk.imp id (lazK_fromL hf))

/-- The block of a fresh emit, read through `unproxy`. -/
theorem unpM_emitted_self {g : Comp.Gen Map} (hd : g.drop = false) (b : Blob) :
    HoonMap.get (unpM (g.emitted b)) g.bo = some (renBlob (unproxy g.cond) b) := by
  unfold unpM
  rw [get_mapVals]
  simp only [Gen.emitted, hd, Bool.false_eq_true, if_false]
  rw [get_put_self]
  rfl

theorem unpM_emitted_ne {g : Comp.Gen Map} (hd : g.drop = false) (b : Blob) {x : Nat} (hx : x ≠ g.bo) :
    HoonMap.get (unpM (g.emitted b)) x = HoonMap.get (unpM g) x := by
  unfold unpM
  rw [get_mapVals, get_mapVals]
  simp only [Gen.emitted, hd, Bool.false_eq_true, if_false]
  rw [get_put_ne hx]

/-- A run that ends at a fresh block with no reads and no jumps: nothing is
live at its entry. -/
theorem liveC_dead {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hb : ∃ b, HoonMap.get (unpM g1) nex.th.there = some b ∧ (∀ r, ¬ BlockRF b r) ∧ getJmps b.fin = []) :
    LiveC K goal g0 g1 nex := by
  obtain ⟨b, hb, hr, hj⟩ := hb
  intro r hl
  cases hl with
  | here hb' hr' _ => rw [hb] at hb'; cases hb'; exact (hr r hr').elim
  | next hb' hj' _ _ _ => rw [hb] at hb'; cases hb'; rw [hj] at hj'; exact absurd hj' List.not_mem_nil

/-- **`+bomb` under every goal**: nothing is live at the `%bom` block. -/
theorem liveC_bombL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    {miss : Option Nat} (hd : g0.drop = false) (h : (bombL miss : CM Map (NextL S)) g0 = some (nex, g1)) :
    LiveC K goal g0 g1 nex := by
  simp only [bombL] at h
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine liveC_dead ⟨_, unpM_emitted_self hd _, fun r hr => ?_, rfl⟩
  obtain ⟨-, hr | ⟨-, hr⟩⟩ := hr
  · exact hr
  · simp [renBlob, renFin, finRegs] at hr

/-- A register that `IL` makes no proxy: every key of `cond` is below `re`. -/
theorem IL.cond_re {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K goal g) :
    HoonMap.get g.cond g.re = Option.none := by
  cases e : HoonMap.get g.cond g.re with
  | none => rfl
  | some v => exact absurd (h.cond _ v e).1 (Nat.lt_irrefl _)

/-- **`+simple-next` under `%pick`**: the `%brn` block reads only the fresh
register of its result's need; past it, the targets' liveness, framed. -/
theorem liveC_simpleNextL_pick {K : Nat → Nat → Prop} {z o : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : (simpleNextL (CGoalL.pick z o : CGoalL S) : CM Map (NextL S)) g0 = some (nex, g1)) :
    LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨⟨bz, hbz, -, az⟩, ⟨bo', hbo, -, ao⟩⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  simp only [simpleNextL] at h
  obtain ⟨r, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o', gb, hb, h⟩ := bind_some h
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hu : unproxy g0.cond g0.re = g0.re := unproxy_none hI.cond_re
  have hget : HoonMap.get (unpM (({ g0 with re := g0.re + 1 } : Comp.Gen Map).emitted
      ⟨[], [], Termin.brn g0.re z o⟩)) g0.bo = some ⟨[], [], Termin.brn g0.re z o⟩ := by
    rw [unpM_emitted_self (g := { g0 with re := g0.re + 1 }) hd]
    simp [renBlob, renFin, renJmp_nil _ az, renJmp_nil _ ao, hu]
  have hzl : z.there < g0.bo := hI.lab hbz
  have hol : o.there < g0.bo := hI.lab hbo
  have hfr : ∀ j : Jmp, j.there < g0.bo → ∀ y, LiveK (unpM (({ g0 with re := g0.re + 1 } : Comp.Gen Map).emitted
      ⟨[], [], Termin.brn g0.re z o⟩)) (fun x y => K x y ∨ lazK g0.bo (ofSure (⟨Need.this g0.re, HoonSet.empty⟩ : Sure S)) x y)
      j.there y → LiveK (unpM g0) K j.there y := fun j hj y hl =>
    (liveK_frameP hI.downU (fun x hx => (unpM_emitted_ne (g := { g0 with re := g0.re + 1 }) hd _
      (Nat.ne_of_lt hx)).trans rfl) hj).mp (hl.mono fun _ _ hk => Or.inl hk)
  intro y hl
  cases hl with
  | here hb' hr hk =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨-, hr⟩ := hr
    rcases hr with hr | ⟨-, hr⟩
    · exact hr.elim
    · simp only [finRegs, jmpRegs, az, ao, List.filterMap_nil, List.append_nil, List.mem_singleton] at hr
      subst hr
      exact (hk (Or.inr (lazK_ofSure.mpr ⟨rfl, rfl⟩))).elim
  | next hb' hj hl _ _ =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Or.inl (hfr _ hzl y hl)
    · exact Or.inr (hfr _ hol y hl)

/-- **`%0` under every goal.** -/
theorem liveC_n0 (env : CallEnv) (sup : Option Nomm) {ax : Nat} {K : Nat → Nat → Prop} {goal : CGoalL S}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K goal g0)
    (h : runLC env sup (Nomm.n0 ax) goal region g0 = some (nex, g1)) : LiveC K goal g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  simp only [runLC] at h
  split at h
  · exact liveC_bombL hd h
  obtain ⟨nx, ga, ha, h⟩ := bind_some h
  have L : LiveC K goal g0 ga nx := by
    cases goal with
    | next laz th =>
      simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact liveC_refl
    | pick z o => exact liveC_simpleNextL_pick hI ha
    | done => exact liveC_simpleNextL_done hd hI.cond_re ha
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact L
  · cases hf : fromL ax nx.laz with
    | none => simp only [hf] at h; cases h
    | some laz' =>
      simp only [hf, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact L.fromL hf

/-- **`%1` under every goal.** -/
theorem liveC_n1 (env : CallEnv) (sup : Option Nomm) {k : Noun} {K : Nat → Nat → Prop} {goal : CGoalL S}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K goal g0)
    (h : runLC env sup (Nomm.n1 k) goal region g0 = some (nex, g1)) : LiveC K goal g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    rw [re_apply] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨o, gb, hb, h⟩ := bind_some h
    rw [emit_apply] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hu : unproxy g0.cond g0.re = g0.re := unproxy_none hI.cond_re
    refine liveC_dead ⟨_, unpM_emitted_self (g := { g0 with re := g0.re + 1 }) hd _, fun r hr => ?_, rfl⟩
    obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
    · rcases hr with hr | ⟨-, hr⟩ <;> simp [renPole, aliasReads, aliasDst, Opt.poleRegs, OpsRF] at hr
    · have e1 : r = g0.re := by simpa [renBlob, renFin, finRegs, hu] using hr
      exact hnd (by simp [renBlob, renPole, defsOf, aliasDst, hu, e1])
  | pick z o =>
    simp only [runLC] at h
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact liveC_pick_z
    · split at h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact liveC_pick_o
      · exact liveC_bombL hd h
  | next laz th =>
    simp only [runLC] at h
    obtain ⟨o, ga, ha, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact liveC_medeL hI ha

end Raw
end SkaModel
end Formalization
