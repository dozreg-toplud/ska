import lemmas.Glue.GuardCallsMono

/-!
# `KPA`: steps that keep `InvA`, with the label bookkeeping (track G, ninth pass)

LEDGER 2.c, toward `GuardMonoC`.  The old `KP` (`Glue/GuardStep.lean`)
carries `BlocksOK`, false once a split block of `+mono-try-call` exists, so
each arm is redone here over `InvA K g` (`Glue/GuardCallsMono.lean`).

* **Labels.**  `FL K b o`: the label `o` is below `b` and has no
  annotation.  A STAGE is a triple `(K, bo, re)`; `XB K b r K' b' r'`: the
  stage `(K', b', r')` extends `(K, b, r)` (`bo`, `re` grow, `K'` agrees
  with `K` below `b`).  `FL` is kept along `XB` (`FL.up`), so a label that is
  fresh at one stage is fresh at every later one.
* **`KPA K0 b0 r0 P m`**: every run of `m` from `InvA K g`, at a stage that
  extends the base `(K0, b0, r0)`, ends in `InvA K' g'` at a stage that
  extends the start, with a result in `P K' g'.bo g'.re`.  Inputs are stated
  at the base (`FL K0 b0 o`, `r < r0`) and stay true (`FL.up`); results are
  stated at the end stage, which is the base of what runs next
  (`KPA.bind'`).
* **The lifting lemmas**: `KPA.emit'` (`+emit` of a block that meets
  `BlockOK`, the old side condition, whose jumps go to `FL` labels: `K`
  unchanged), `KPA.addOps'` (`+add-ops` of a guarded list at an `FL` label:
  the block is not a split block, so its splits are `%cel`-guarded and the
  ops in front keep them, and a `CellOut` by a `%cel` survives),
  `KPA.same` (blocks, `drop`, `bo` unchanged), `KPA.re'`, `KPA.mtc`
  (`+mono-try-call`, from `mtl_kpa`).
* `kpa_simpleNextL`, **`kpa_monoBlocks`**: the call blocks of the direct
  call, for every goal whose jumps are `FL` (`GFL`), given what `+kerf`
  returns under a `%next` goal (`KerfA`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-! ## Labels and stages -/

/-- **A label a new block may jump to**: below `b`, with no annotation. -/
def FL (K : Nat → Nat → Prop) (b o : Nat) : Prop := o < b ∧ ∀ s, ¬ K o s

/-- **The stage `(K', b', r')` extends `(K, b, r)`.** -/
def XB (K : Nat → Nat → Prop) (b r : Nat) (K' : Nat → Nat → Prop) (b' r' : Nat) : Prop :=
  b ≤ b' ∧ r ≤ r' ∧ ∀ l s, l < b → (K' l s ↔ K l s)

theorem XB.refl (K : Nat → Nat → Prop) (b r : Nat) : XB K b r K b r :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => Iff.rfl⟩

theorem XB.trans {K1 K2 K3 : Nat → Nat → Prop} {b1 b2 b3 r1 r2 r3 : Nat} (h1 : XB K1 b1 r1 K2 b2 r2)
    (h2 : XB K2 b2 r2 K3 b3 r3) : XB K1 b1 r1 K3 b3 r3 :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2.1 h2.2.1,
    fun l s hl => (h2.2.2 l s (Nat.lt_of_lt_of_le hl h1.1)).trans (h1.2.2 l s hl)⟩

theorem FL.up {K K' : Nat → Nat → Prop} {b r b' r' o : Nat} (h : FL K b o) (x : XB K b r K' b' r') :
    FL K' b' o :=
  ⟨Nat.lt_of_lt_of_le h.1 x.1, fun s hk => h.2 s ((x.2.2 o s h.1).mp hk)⟩

theorem lt_up {K K' : Nat → Nat → Prop} {b r b' r' x : Nat} (h : x < r) (X : XB K b r K' b' r') : x < r' :=
  Nat.lt_of_lt_of_le h X.2.1

/-- **Every label of a lazy need meets `P`** (the fork and bond blocks,
recursively). -/
inductive LzL (P : Nat → Prop) : Lazy S → Prop
  | mk {s : Sure S} {fork : List ((Nat × Lazy S) × (Nat × Lazy S))} {bond : List (Nat × Lazy S)} :
      (∀ e ∈ fork, P e.1.1) → (∀ e ∈ fork, LzL P e.1.2) → (∀ e ∈ fork, P e.2.1) → (∀ e ∈ fork, LzL P e.2.2) →
      (∀ e ∈ bond, P e.1) → (∀ e ∈ bond, LzL P e.2) → LzL P (Lazy.mk s fork bond)

theorem LzL.imp {P Q : Nat → Prop} (hpq : ∀ o, P o → Q o) {l : Lazy S} (h : LzL P l) : LzL Q l := by
  induction h with
  | mk h1 _ h3 _ h5 _ i2 i4 i6 =>
    exact LzL.mk (fun e he => hpq _ (h1 e he)) i2 (fun e he => hpq _ (h3 e he)) i4 (fun e he => hpq _ (h5 e he)) i6

theorem LzL.up {K K' : Nat → Nat → Prop} {b r b' r' : Nat} {l : Lazy S} (h : LzL (FL K b) l)
    (x : XB K b r K' b' r') : LzL (FL K' b') l := h.imp fun _ ho => ho.up x

theorem lzL_ofSure (P : Nat → Prop) (s : Sure S) : LzL P (Lazy.ofSure s) :=
  LzL.mk (fun e he => absurd he List.not_mem_nil) (fun e he => absurd he List.not_mem_nil)
    (fun e he => absurd he List.not_mem_nil) (fun e he => absurd he List.not_mem_nil)
    (fun e he => absurd he List.not_mem_nil) (fun e he => absurd he List.not_mem_nil)

/-- The goal's jumps go to `FL` labels and pass no `~`; so do the labels of
a `%next` goal's lazy need. -/
def GFL (K : Nat → Nat → Prop) (b : Nat) : CGoalL S → Prop
  | CGoalL.next laz th => FL K b th.there ∧ JOK th ∧ LzL (FL K b) laz
  | CGoalL.pick z o => FL K b z.there ∧ JOK z ∧ FL K b o.there ∧ JOK o
  | CGoalL.done => True

theorem GFL.up {K K' : Nat → Nat → Prop} {b r b' r' : Nat} {goal : CGoalL S} (h : GFL K b goal)
    (x : XB K b r K' b' r') : GFL K' b' goal := by
  cases goal with
  | next _ th => exact ⟨h.1.up x, h.2.1, h.2.2.up x⟩
  | pick z o => exact ⟨h.1.up x, h.2.1, h.2.2.1.up x, h.2.2.2⟩
  | done => trivial

theorem invA_congr {K K' : Nat → Nat → Prop} {g : Comp.Gen Map} (h : InvA K g) (e : ∀ l s, K l s ↔ K' l s) :
    InvA K' g := by
  have : K = K' := funext fun l => funext fun s => propext (e l s)
  subst this; exact h

/-! ## `KPA` -/

/-- **Every run of `m` from a stage extending the base keeps `InvA`.** -/
structure KPA {α : Type} (K0 : Nat → Nat → Prop) (b0 r0 : Nat)
    (P : (Nat → Nat → Prop) → Nat → Nat → α → Prop) (m : CM Map α) : Prop where
  k : ∀ K g x g', InvA K g → 0 < g.bo → XB K0 b0 r0 K g.bo g.re → m g = some (x, g') →
    ∃ K', InvA K' g' ∧ XB K g.bo g.re K' g'.bo g'.re ∧ P K' g'.bo g'.re x

namespace KPA

variable {K0 : Nat → Nat → Prop} {b0 r0 : Nat}

theorem pure' {α : Type} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop} {a : α}
    (h : ∀ K b r, XB K0 b0 r0 K b r → P K b r a) : KPA K0 b0 r0 P (pure a : CM Map α) := by
  constructor; intro K g x g' hI _ hX e; cases e
  exact ⟨K, hI, XB.refl _ _ _, h _ _ _ hX⟩

theorem bind' {α β : Type} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop}
    {Q : (Nat → Nat → Prop) → Nat → Nat → β → Prop} {m : CM Map α} {f : α → CM Map β}
    (hm : KPA K0 b0 r0 P m)
    (hf : ∀ a K1 b1 r1, XB K0 b0 r0 K1 b1 r1 → P K1 b1 r1 a → KPA K1 b1 r1 Q (f a)) :
    KPA K0 b0 r0 Q (m >>= f) := by
  constructor
  intro K g x g' hI h0 hX e
  obtain ⟨a, g1, e1, e2⟩ := bind_some e
  obtain ⟨K1, hI1, X1, p1⟩ := hm.k K g a g1 hI h0 hX e1
  have h01 : 0 < g1.bo := Nat.lt_of_lt_of_le h0 X1.1
  obtain ⟨K2, hI2, X2, q2⟩ := (hf a K1 g1.bo g1.re (hX.trans X1) p1).k K1 g1 x g' hI1 h01 (XB.refl _ _ _) e2
  exact ⟨K2, hI2, X1.trans X2, q2⟩

theorem mono {α : Type} {P Q : (Nat → Nat → Prop) → Nat → Nat → α → Prop} {m : CM Map α}
    (h : KPA K0 b0 r0 P m) (hpq : ∀ K b r a, P K b r a → Q K b r a) : KPA K0 b0 r0 Q m := by
  constructor
  intro K g x g' hI h0 hX e
  obtain ⟨K', hI', X, p⟩ := h.k K g x g' hI h0 hX e
  exact ⟨K', hI', X, hpq _ _ _ _ p⟩

theorem fail {α : Type} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop} :
    KPA K0 b0 r0 P (fun _ => Option.none : CM Map α) := by
  constructor; intro K g x g' _ _ _ h; cases h

theorem crash {α : Type} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop} :
    KPA K0 b0 r0 P (crashM : CM Map α) := fail

theorem ite' {α : Type} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop} (c : Prop) [Decidable c]
    {a b : CM Map α} (ha : c → KPA K0 b0 r0 P a) (hb : ¬ c → KPA K0 b0 r0 P b) :
    KPA K0 b0 r0 P (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- **A step that leaves the blocks, `drop` and `bo` alone.** -/
theorem same {α : Type} {m : CM Map α}
    (h : ∀ g x g', m g = some (x, g') → g'.blocks = g.blocks ∧ g'.drop = g.drop ∧ g'.bo = g.bo ∧ g.re ≤ g'.re) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) m := by
  constructor
  intro K g x g' hI h0 hX e
  obtain ⟨e1, e2, e3, e4⟩ := h g x g' e
  refine ⟨K, ⟨?_, ?_, ?_, ?_⟩, ⟨by rw [e3]; exact Nat.le_refl _, e4, fun _ _ _ => Iff.rfl⟩, trivial⟩
  · rw [e1]; exact hI.ok
  · rw [e2]; exact hI.drop
  · intro o b hb; rw [e1] at hb; rw [e3]; exact hI.below o b hb
  · intro o s hk; rw [e3]; exact hI.kin o s hk

/-- **`+re`**: a register at least the base's `re`, below the end's. -/
theorem re' : KPA K0 b0 r0 (fun _ _ r x => r0 ≤ x ∧ x < r) (re : CM Map Nat) := by
  constructor
  intro K g x g' hI h0 hX e
  rw [re_apply] at e; cases e
  exact ⟨K, invA_re hI, ⟨Nat.le_refl _, Nat.le_succ _, fun _ _ _ => Iff.rfl⟩, hX.2.1, Nat.lt_succ_self _⟩

/-- **The lifting lemma for `+emit`**: a block that meets `BlockOK` (no `~`,
every split guarded by a `%cel` of its body) and jumps to `FL` labels keeps
`InvA` with the same annotation; the new label is `FL`. -/
theorem emit' {b : Blob} (hb : BlockOK b) (hj : ∀ j ∈ getJmps b.fin, FL K0 b0 j.there) :
    KPA K0 b0 r0 (fun K bo _ o => FL K bo o) (emit b : CM Map Nat) := by
  constructor
  intro K g x g' hI h0 hX e
  rw [emit_apply] at e; cases e
  have hj' : ∀ j ∈ getJmps b.fin, FL K g.bo j.there := fun j hm => (hj j hm).up hX
  have H := emitA hI h0 (fun _ => False) (fun _ h => h.elim)
    (fun j hm => ⟨(hj' j hm).1, hb.1 j hm⟩) (fun j hm s hk => absurd hk ((hj' j hm).2 s))
    (fun i p s hp hs => Or.inl (hb.2 i p s hp hs))
  refine ⟨K, invA_congr H (fun l s => by simp), ⟨by simp [Gen.emitted], Nat.le_refl _, fun _ _ _ => Iff.rfl⟩,
    by simp [Gen.emitted], fun s hk => Nat.lt_irrefl _ (hI.kin _ s hk)⟩

/-- **The lifting lemma for `+add-ops`**: a guarded list in front of the block
at an `FL` label (not a split block) keeps `InvA`. -/
theorem addOps' {o : Nat} {ops : List Pole} (hops : GuardedBody ops) (ho : FL K0 b0 o) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (addOps o ops : CM Map Unit) := by
  constructor
  intro K g x g' hI h0 hX e
  have hoK : ∀ s, ¬ K o s := (ho.up hX).2
  unfold addOps at e
  split at e
  · cases e; exact ⟨K, hI, XB.refl _ _ _, trivial⟩
  rename_i hd
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp e
  cases e
  have hget : ∀ o', HoonMap.get (HoonMap.put g.blocks o { b with body := ops ++ b.body }) o' =
      if o' = o then some { b with body := ops ++ b.body } else HoonMap.get g.blocks o' := by
    intro o'; rw [HoonMap.get_put]
  have hgb : GuardedBody b.body := by
    intro i p s hp hs
    rcases hI.ok.split o b hb i p s hp hs with h | ⟨hk, -⟩
    · exact h
    · exact absurd hk (hoK s)
  refine ⟨K, ⟨⟨?_, ?_, hI.ok.zero, ?_, ?_⟩, hI.drop, ?_, hI.kin⟩, XB.refl _ _ _, trivial⟩
  · intro o' b' hb' j hjm
    rw [hget] at hb'; split at hb'
    · cases hb'; exact hI.ok.noNone o b hb j hjm
    · exact hI.ok.noNone o' b' hb' j hjm
  · intro o' b' s hb' hk
    rw [hget] at hb'; split at hb'
    · rename_i eo; subst eo; exact absurd hk (hoK s)
    · exact hI.ok.par o' b' s hb' hk
  · intro o' b' j s hb' hjm hk
    rw [hget] at hb'; split at hb'
    · rename_i eo; subst eo; cases hb'
      rcases hI.ok.edge o' b j s hb hjm hk with h | h
      · exact Or.inl h
      · right
        rcases h with ⟨hk', -⟩ | ⟨j', hj1, hj2, hj3⟩
        · exact absurd hk' (hoK s)
        · right
          refine ⟨ops.length + j', by simp; omega, ?_, ?_⟩
          · simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hj2
          · intro l hl1 hl2 q hq
            have hl : ops.length ≤ l := by omega
            rw [List.getElem?_append_right hl] at hq
            exact hj3 (l - ops.length) (by omega) (by simp at hl2; omega) q hq
    · exact hI.ok.edge o' b' j s hb' hjm hk
  · intro o' b' hb' i p s hp hs
    rw [hget] at hb'; split at hb'
    · cases hb'; exact Or.inl (guardedBody_append hops hgb i p s hp hs)
    · exact hI.ok.split o' b' hb' i p s hp hs
  · intro o' b' hb'
    rw [hget] at hb'; split at hb'
    · rename_i eo; subst eo; cases hb'; exact hI.below o' b hb
    · exact hI.below o' b' hb'

/-- **`+mono-try-call`** (`mtl_kpa`): the register to take apart below the
base's `re`, the two exits `FL` at the base. -/
theorem mtc {ned : Need} {opt sub pes : Nat} (hs : sub < r0) (ho : FL K0 b0 opt) (hp : FL K0 b0 pes) :
    KPA K0 b0 r0 (fun K bo _ x => FL K bo x) (monoTryCall ned opt sub pes : CM Map Nat) := by
  constructor
  intro K g x g' hI h0 hX e
  have ho' := ho.up hX
  have hp' := hp.up hX
  obtain ⟨K', hI', hx, hkx, hag, hbo, hre⟩ :=
    mtl_kpa pes ned sub opt K g x g' hI e (Nat.lt_of_lt_of_le hs hX.2.1) ho'.1 hp'.1 ho'.2 hp'.2
  exact ⟨K', hI', ⟨hbo, hre, hag⟩, hx, hkx⟩

end KPA

/-! ## The call blocks -/

theorem blockOK_nil (fin : Termin) (par : List Nat) (hj : ∀ j ∈ getJmps fin, JOK j) : BlockOK ⟨par, [], fin⟩ :=
  ⟨hj, fun i p s h => by simp at h⟩

theorem blockOK_one (fin : Termin) (par : List Nat) (p : Pole) (hp : splitReg p = Option.none)
    (hj : ∀ j ∈ getJmps fin, JOK j) : BlockOK ⟨par, [p], fin⟩ :=
  ⟨hj, guardedBody_of_noSplit (noSplit_cons hp noSplit_nil)⟩

/-- **`+simple-next`** under a goal with `FL` jumps: the result jump is `FL`
and passes no `~`. -/
theorem kpa_simpleNextL {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {goal : CGoalL S} (hg : GFL K0 b0 goal) :
    KPA K0 b0 r0 (fun K bo _ (n : NextL S) => FL K bo n.th.there ∧ JOK n.th ∧ LzL (FL K bo) n.laz)
      (simpleNextL goal : CM Map (NextL S)) := by
  cases goal with
  | next laz th => exact KPA.pure' fun K b r X => ⟨hg.1.up X, hg.2.1, hg.2.2.up X⟩
  | done =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 _ => KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps]))
      (by simp [getJmps])) fun o K2 b2 r2 X2 ho => KPA.pure' fun K b r X => ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _⟩
  | pick z o =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 _ => KPA.bind' (KPA.emit' (blockOK_nil _ _ ?_) ?_)
      fun o' K2 b2 r2 X2 ho => KPA.pure' fun K b r X => ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _⟩
    · intro j hj; simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hg.2.1
      · exact hg.2.2.2
    · intro j hj; simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hg.1.up X1
      · exact hg.2.2.1.up X1

/-- **What `+kerf` must give in the middle of a run** (OPEN: `+kern`'s
`+add-ops` at the lazy's labels need track D's `KI` there): from a `nex`
whose jump and lazy labels are `FL` and whose jump passes no `~`, `+kerf`
keeps `InvA` and returns an `FL` block.  `KPA.addOps'` is the step at each
label, once `+kern-need`'s output is guarded (`kernNeed_guarded`). -/
def KerfA (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] : Prop :=
  ∀ K0 b0 r0 (nex : NextL S), FL K0 b0 nex.th.there → JOK nex.th → LzL (FL K0 b0) nex.laz →
    KPA K0 b0 r0 (fun K bo _ (x : Nat × Nat) => FL K bo x.1) (kerf nex : CM Map (Nat × Nat))

/-- **The call blocks of the direct call keep `InvA`**: for a goal with `FL`
jumps, the block `+mono-try-call` returns is `FL`.  Under `%done` no
`+kerf` runs; under another goal `+kerf` of `+simple-next`'s result is
`KerfA`. -/
theorem kpa_monoBlocks (hk : KerfA S Map) {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (bl : Bell) (subNed : Need) {goal : CGoalL S} (hg : GFL K0 b0 goal) :
    KPA K0 b0 r0 (fun K bo _ (x : Nat × Nat) => FL K bo x.2) (monoBlocks bl subNed goal : CM Map (Nat × Nat)) := by
  have hdone : KPA K0 b0 r0 (fun K bo _ (x : Nat × Nat) => FL K bo x.2)
      (do
        let subPes ← re
        let opt ← emit ⟨[], [], Termin.jmp bl (flattenNeed subNed)⟩
        let pes ← emit ⟨[], [], Termin.jsp bl subPes⟩
        let o ← monoTryCall subNed opt subPes pes
        pure (subPes, o) : CM Map (Nat × Nat)) := by
    refine KPA.bind' KPA.re' fun sp K1 b1 r1 X1 hsp => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun opt K2 b2 r2 X2 hopt => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun pes K3 b3 r3 X3 hpes => ?_
    refine KPA.bind' (KPA.mtc (lt_up (lt_up hsp.2 X2) X3) (hopt.up X3) hpes) fun o K4 b4 r4 X4 ho => ?_
    exact KPA.pure' fun K b r X => ho.up X
  unfold monoBlocks
  cases goal with
  | done => exact hdone
  | next laz th =>
    refine KPA.bind' (kpa_simpleNextL hg) fun nex K1 b1 r1 X1 hn => ?_
    refine KPA.bind' (hk K1 b1 r1 nex hn.1 hn.2.1 hn.2.2) fun op K2 b2 r2 X2 hop => ?_
    rcases op with ⟨out, pro⟩
    refine KPA.bind' KPA.re' fun merged K3 b3 r3 X3 hm => ?_
    refine KPA.bind' KPA.re' fun sp K4 b4 r4 X4 hsp => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) ?_)
      fun merge K5 b5 r5 X5 hmerge => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hop.up X3).up X4
    refine KPA.bind' KPA.re' fun po K6 b6 r6 X6 _ => ?_
    refine KPA.bind' KPA.re' fun pp K7 b7 r7 X7 _ => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun opt K8 b8 r8 X8 hopt => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hmerge.up X6).up X7
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun pes K9 b9 r9 X9 hpes => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact ((hmerge.up X6).up X7).up X8
    refine KPA.bind' (KPA.mtc (lt_up (lt_up (lt_up (lt_up (lt_up hsp.2 X5) X6) X7) X8) X9) (hopt.up X9) hpes)
      fun o K10 b10 r10 X10 ho => ?_
    exact KPA.pure' fun K b r X => ho.up X
  | pick z o =>
    refine KPA.bind' (kpa_simpleNextL hg) fun nex K1 b1 r1 X1 hn => ?_
    refine KPA.bind' (hk K1 b1 r1 nex hn.1 hn.2.1 hn.2.2) fun op K2 b2 r2 X2 hop => ?_
    rcases op with ⟨out, pro⟩
    refine KPA.bind' KPA.re' fun merged K3 b3 r3 X3 hm => ?_
    refine KPA.bind' KPA.re' fun sp K4 b4 r4 X4 hsp => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) ?_)
      fun merge K5 b5 r5 X5 hmerge => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hop.up X3).up X4
    refine KPA.bind' KPA.re' fun po K6 b6 r6 X6 _ => ?_
    refine KPA.bind' KPA.re' fun pp K7 b7 r7 X7 _ => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun opt K8 b8 r8 X8 hopt => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hmerge.up X6).up X7
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun pes K9 b9 r9 X9 hpes => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact ((hmerge.up X6).up X7).up X8
    refine KPA.bind' (KPA.mtc (lt_up (lt_up (lt_up (lt_up (lt_up hsp.2 X5) X6) X7) X8) X9) (hopt.up X9) hpes)
      fun o K10 b10 r10 X10 ho => ?_
    exact KPA.pure' fun K b r X => ho.up X

end Glue
end SkaModel
end Formalization
