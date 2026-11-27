import lemmas.Glue.GuardCallsB
import lemmas.Ska.RawInvCLPair
import lemmas.Ska.CompFromRun

/-!
# The lazy arms keep `InvA` (track G, tenth pass)

LEDGER 2.c, toward `GuardMonoC`, over `KPA` (`Glue/GuardCallsA.lean`,
`Glue/GuardCallsB.lean`).  The ports of `Glue/GuardArms.lean`: every
`+add-ops` of these arms puts a list with no split at an `FL` label (the
arm's new block, or a fork or bond label of the lazy, `LzL`), every emitted
block meets `BlockOK` and jumps to `FL` labels.

* `kpa_doneBlocks`, `kpa_forl`, `kpa_bombL`;
* `kpa_crashNeed`, `kpa_medeLoop`, **`kpa_medeL`**; `kpa_collapseGate`,
  **`kpa_collapseLazyAtomL`** (the block it returns is `FL`);
* **`kpa_splitL`**, **`kpa_intoL`**: the two halves' labels are those of the
  lazy (`lzL_lazyPrune`), the new block is `FL`;
* `lzL_fromL`, `lzS_fromL`: `+from` keeps the labels and the `DN` entries;
* `rs_pastL`: `+past` keeps the `DN` entries.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## Blocks -/

section
variable {K0 : Nat → Nat → Prop} {b0 r0 : Nat}

theorem kpa_doneBlocks :
    KPA K0 b0 r0 (fun K bo _ (x : Nat × Nat) => FL K bo x.1 ∧ FL K bo x.2) (doneBlocks : CM Map (Nat × Nat)) := by
  unfold doneBlocks
  refine KPA.bind' KPA.re' fun _ K1 b1 r1 X1 _ => KPA.bind' KPA.re' fun _ K2 b2 r2 X2 _ => ?_
  refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps])) (by simp [getJmps]))
    fun o0 K3 b3 r3 X3 h0 => ?_
  refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps])) (by simp [getJmps]))
    fun o1 K4 b4 r4 X4 h1 => ?_
  exact KPA.pure' fun K b r X => ⟨(h0.up X4).up X, h1.up X⟩

theorem kpa_forl (r o : Nat) (ho : FL K0 b0 o) :
    KPA K0 b0 r0 (fun K bo _ (x : Nat × Nat) => FL K bo x.1 ∧ FL K bo x.2) (forl r o : CM Map (Nat × Nat)) := by
  unfold forl
  refine KPA.bind' KPA.re' fun _ K1 b1 r1 X1 _ => KPA.bind' KPA.re' fun _ K2 b2 r2 X2 _ => ?_
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps, jok_jmp0])) ?_) fun barg K3 b3 r3 X3 hbarg => ?_
  · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (ho.up X1).up X2
  refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun if0 K4 b4 r4 X4 h0 => ?_
  · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact hbarg
  refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun if1 K5 b5 r5 X5 h1 => ?_
  · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact hbarg.up X4
  exact KPA.pure' fun K b r X => ⟨(h0.up X5).up X, h1.up X⟩

theorem kpa_bombL (miss : Option Nat) : KPA K0 b0 r0 RN (bombL miss : CM Map (NextL S)) := by
  unfold bombL
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun o K1 b1 r1 X1 ho => ?_
  exact KPA.pure' fun K b r X => ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _⟩

/-! ## The needs -/

theorem kpa_must (ned : Need) : KPA K0 b0 r0 (fun _ _ _ _ => True) (must ned : CM Map (Nat × Need)) := by
  unfold must
  split <;> first
    | exact KPA.pure' fun _ _ _ _ => trivial
    | exact KPA.bind' KPA.re' fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => trivial

theorem kpa_splitNeed (ned : Need) (o : Nat) (ho : FL K0 b0 o) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · exact KPA.pure' fun _ _ _ _ => trivial
  · exact KPA.pure' fun _ _ _ _ => trivial
  · exact KPA.bind' KPA.re' fun _ K1 b1 r1 X1 _ => KPA.bind' KPA.re' fun _ K2 b2 r2 X2 _ =>
      KPA.bind' (KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl noSplit_nil)) ((ho.up X1).up X2))
        fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => trivial
  · exact KPA.bind' (kpa_must _) fun _ K1 b1 r1 X1 _ => KPA.bind' (kpa_must _) fun _ K2 b2 r2 X2 _ =>
      KPA.bind' (KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl noSplit_nil)) ((ho.up X1).up X2))
        fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => trivial

theorem kpa_splitSure (sur : Sure S) (o : Nat) (ho : FL K0 b0 o) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro K g x g1 hI h0 hX h
  unfold splitSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨K', hI', X', -⟩ := (kpa_splitNeed sur.ned o ho).k K g y g2 hI h0 hX h1
  exact ⟨K', hI', X', trivial⟩

end

theorem kpa_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole)
    (K0 : Nat → Nat → Prop) (b0 r0 : Nat), FL K0 b0 o → NoSplit ops →
    KPA K0 b0 r0 (fun _ _ _ _ => True) (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops K0 b0 r0 ho hops
    rw [intoLoop]
    split
    · exact KPA.bind' (KPA.addOps' (guardedBody_of_noSplit hops) ho) fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => trivial
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _ _ _ _ ho hops
      · exact KPA.bind' KPA.re' fun _ K1 b1 r1 X1 _ => KPA.bind' KPA.re' fun _ K2 b2 r2 X2 _ =>
          ih _ hl _ _ _ _ _ _ ((ho.up X1).up X2) (noSplit_cons rfl hops)
      · exact ih _ hl _ _ _ _ _ _ ho hops
      · exact KPA.bind' (kpa_must _) fun _ K1 b1 r1 X1 _ => KPA.bind' (kpa_must _) fun _ K2 b2 r2 X2 _ =>
          ih _ hl _ _ _ _ _ _ ((ho.up X1).up X2) (noSplit_cons rfl hops)

section
variable {K0 : Nat → Nat → Prop} {b0 r0 : Nat}

theorem kpa_intoNeed (axe : Nat) (ned : Need) (o : Nat) (ho : FL K0 b0 o) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KPA.ite' _ (fun _ => KPA.fail) fun _ => KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial)
    fun _ => kpa_intoLoop _ _ _ _ _ _ _ _ ho noSplit_nil

theorem kpa_intoSure (axe : Nat) (sur : Sure S) (o : Nat) (ho : FL K0 b0 o) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro K g x g1 hI h0 hX h
  unfold intoSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨K', hI', X', -⟩ := (kpa_intoNeed axe sur.ned o ho).k K g y g2 hI h0 hX h1
  exact ⟨K', hI', X', trivial⟩

theorem kpa_crashNeed (o : Nat) (ho : FL K0 b0 o) (atom : Sum Nat Nat) (ned : Need) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed
  split
  · exact KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl (noSplit_imms _ _))) ho
  · exact KPA.bind' KPA.re' fun _ K1 b1 r1 X1 _ =>
      KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl (noSplit_cons rfl (noSplit_imms _ _)))) (ho.up X1)

end

theorem kpa_medeLoop {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (o : Nat) : ∀ (som : Noun) (ned : Need), FL K0 b0 o →
    KPA K0 b0 r0 (fun _ _ _ _ => True) (medeLoop o som ned : CM Map Unit)
  | _, Need.none, ho => by rw [medeLoop]; exact KPA.pure' fun _ _ _ _ => trivial
  | _, Need.this _, ho => by
    rw [medeLoop]; exact KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl noSplit_nil)) ho
  | Noun.atom _, Need.pair _ _, ho => by rw [medeLoop]; exact kpa_crashNeed _ ho _ _
  | Noun.cell a b, Need.pair p q, ho => by
    rw [medeLoop]; exact KPA.bind' (kpa_medeLoop o a p ho) fun _ K1 b1 r1 X1 _ => kpa_medeLoop o b q (ho.up X1)
  | Noun.atom _, Need.both _ _ _, ho => by rw [medeLoop]; exact kpa_crashNeed _ ho _ _
  | Noun.cell a b, Need.both _ h t, ho => by
    rw [medeLoop]
    exact KPA.bind' (KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl noSplit_nil)) ho) fun _ K1 b1 r1 X1 _ =>
      KPA.bind' (kpa_medeLoop o a h (ho.up X1)) fun _ K2 b2 r2 X2 _ => kpa_medeLoop o b t ((ho.up X1).up X2)

/-! ## `+mede`, `+collapse-lazy-atom` -/

section
variable {K0 : Nat → Nat → Prop} {b0 r0 : Nat}

/-- **`+mede`**: the block it returns is `FL`. -/
theorem kpa_medeL {th : Jmp} (h1 : FL K0 b0 th.there) (h2 : JOK th) (som : Noun) {laz : Lazy S}
    (hl : LzL (FL K0 b0) laz) : KPA K0 b0 r0 (fun K bo _ o => FL K bo o) (medeL th som laz : CM Map Nat) := by
  unfold medeL
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simpa [getJmps] using h2)) (by simpa [getJmps] using h1))
    fun o K1 b1 r1 X1 ho => ?_
  refine KPA.bind' KPA.get' fun g K2 b2 r2 X2 _ => ?_
  refine KPA.ite' _ (fun _ => KPA.pure' fun K b r X => (ho.up X2).up X) fun _ => ?_
  refine KPA.bind' (kpa_walkLazyT (fun K0' b0' r0' o' s ho' => KPA.bind' (KPA.sureRequireLook' _)
    fun ned K3 b3 r3 X3 _ => kpa_medeLoop o' som ned (ho'.up X3)) o laz (ho.up X2) ((hl.up X1).up X2))
    fun _ K3 b3 r3 X3 _ => ?_
  exact KPA.pure' fun K b r X => ((ho.up X2).up X3).up X

theorem kpa_collapseGate (r o oLaz : Nat) (ho : FL K0 b0 oLaz) (sur : Sure S) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (collapseGate r o oLaz sur : CM Map Unit) := by
  unfold collapseGate
  refine KPA.bind' (KPA.sureRequireLook' _) fun ned K1 b1 r1 X1 _ => ?_
  have ho1 := ho.up X1
  split
  · exact KPA.pure' fun _ _ _ _ => trivial
  · refine KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial) fun _ => ?_
    refine KPA.bind' (P := fun _ _ _ _ => True)
      (KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial) fun _ => KPA.proxy' _ _) fun src K2 b2 r2 X2 _ => ?_
    exact KPA.addOps' (guardedBody_of_noSplit (noSplit_cons rfl noSplit_nil)) (ho1.up X2)
  · refine KPA.bind' (P := fun _ _ _ _ => True)
      (KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial) fun _ => KPA.proxy' _ _) fun src K2 b2 r2 X2 _ => ?_
    exact kpa_crashNeed _ (ho1.up X2) _ _

theorem lzL_resure {P : Nat → Prop} {l : Lazy S} (s' : Sure S) (h : LzL P l) : LzL P (Lazy.mk s' l.fork l.bond) := by
  cases h with
  | mk h1 h2 h3 h4 h5 h6 => exact LzL.mk h1 h2 h3 h4 h5 h6

/-- **`+collapse-lazy-atom`**: the block it returns is `FL`. -/
theorem kpa_collapseLazyAtomL {nex : NextL S} (h : RN K0 b0 r0 nex) :
    KPA K0 b0 r0 (fun K bo _ (a : Option (Nat × Nat)) => ∀ x, a = some x → FL K bo x.2)
      (collapseLazyAtomL nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtomL
  refine KPA.ite' _ (fun _ => KPA.fail) fun _ => ?_
  refine KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ x hx => by cases hx) fun _ => ?_
  refine KPA.bind' (KPA.sureRequireLook' _) fun ned K1 b1 r1 X1 _ => ?_
  refine KPA.bind' (P := fun K bo _ (x : Nat × Nat) => FL K bo x.2) ?_ fun x K2 b2 r2 X2 hx => ?_
  · split
    · exact KPA.pure' fun K b r X => h.1.up (X1.trans X)
    · exact KPA.bind' KPA.re' fun _ K2 b2 r2 X2 _ => KPA.pure' fun K b r X => h.1.up ((X1.trans X2).trans X)
    · exact KPA.bind' KPA.re' fun _ _ _ _ _ _ =>
        KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun o K3 b3 r3 X3 ho =>
          KPA.pure' fun K b r X => ho.up X
    · exact KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun o K3 b3 r3 X3 ho =>
        KPA.pure' fun K b r X => ho.up X
  rcases x with ⟨r, there⟩
  refine KPA.bind' KPA.get' fun g K3 b3 r3 X3 _ => ?_
  refine KPA.ite' _ (fun _ => KPA.pure' fun K b r' X x e => by cases e; exact (hx.up X3).up X) fun _ => ?_
  refine KPA.bind' (kpa_walkLazyT (fun K0' b0' r0' o s ho' => kpa_collapseGate r there o ho' s) there _
    (hx.up X3) (lzL_resure _ ((h.2.2.up (X1.trans X2)).up X3))) fun _ K4 b4 r4 X4 _ => ?_
  exact KPA.pure' fun K b r' X x e => by cases e; exact ((hx.up X3).up X4).up X

end

/-! ## `+split`, `+into` -/

theorem lzL_lazyPrune {P : Nat → Prop} {l : Lazy S} (h : LzL P l) : LzL P (lazyPrune l) := by
  cases h with
  | mk h1 h2 h3 h4 h5 h6 =>
    unfold lazyPrune
    exact LzL.mk (forall_filter _ h1) (forall_filter _ h2) (forall_filter _ h3) (forall_filter _ h4)
      (forall_filter _ h5) (forall_filter _ h6)

/-- What a walk over forks returns: the two lists of forks are `FL`. -/
def FkP (K : Nat → Nat → Prop) (bo : Nat) (x : List (ForkE S) × List (ForkE S)) : Prop :=
  (∀ e ∈ x.1, FkL K bo e) ∧ ∀ e ∈ x.2, FkL K bo e

/-- What a walk over bonds returns: the two lists of bonds are `FL`. -/
def BdP (K : Nat → Nat → Prop) (bo : Nat) (x : List (Nat × Lazy S) × List (Nat × Lazy S)) : Prop :=
  (∀ e ∈ x.1, BdL K bo e) ∧ ∀ e ∈ x.2, BdL K bo e

theorem FkP.up {K K' : Nat → Nat → Prop} {b r b' r' : Nat} {x : List (ForkE S) × List (ForkE S)} (h : FkP K b x)
    (X : XB K b r K' b' r') : FkP K' b' x := ⟨fun e he => (h.1 e he).up X, fun e he => (h.2 e he).up X⟩

theorem BdP.up {K K' : Nat → Nat → Prop} {b r b' r' : Nat} {x : List (Nat × Lazy S) × List (Nat × Lazy S)}
    (h : BdP K b x) (X : XB K b r K' b' r') : BdP K' b' x :=
  ⟨fun e he => (h.1 e he).up X, fun e he => (h.2 e he).up X⟩

mutual
theorem kpa_splitLoop {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (l : Lazy S) (o : Nat), FL K0 b0 o →
    LzL (FL K0 b0) l →
    KPA K0 b0 r0 (fun K bo _ (x : Lazy S × Lazy S) => LzL (FL K bo) x.1 ∧ LzL (FL K bo) x.2)
      (splitLoop l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o, ho, hl => by
    rw [splitLoop]
    obtain ⟨hf, hb⟩ := lzL_parts hl
    refine KPA.bind' (kpa_splitSure s o ho) fun x K1 b1 r1 X1 _ => ?_
    rcases x with ⟨sh, st⟩
    refine KPA.ite' _ (fun _ => KPA.pure' fun K bb r X => ⟨lzL_ofSure _ _, lzL_ofSure _ _⟩) fun _ => ?_
    refine KPA.bind' (kpa_splitForks f (fun e he => (hf e he).up X1)) fun y K2 b2 r2 X2 hy => ?_
    rcases y with ⟨fh, ft⟩
    refine KPA.bind' (kpa_splitBonds b (fun e he => (hb e he).up (X1.trans X2))) fun z K3 b3 r3 X3 hz => ?_
    rcases z with ⟨bh, bt⟩
    have hy3 := (FkP.up hy X3)
    exact KPA.pure' fun K bb r X =>
      ⟨lzL_lazyPrune (lzL_of_parts (fun e he => (hy3.1 e he).up X) fun e he => (hz.1 e he).up X),
        lzL_lazyPrune (lzL_of_parts (fun e he => (hy3.2 e he).up X) fun e he => (hz.2 e he).up X)⟩

theorem kpa_splitForks {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (f : List (ForkE S)), (∀ e ∈ f, FkL K0 b0 e) →
    KPA K0 b0 r0 (fun K bo _ x => FkP K bo x) (splitForks f : CM Map (List (ForkE S) × List (ForkE S)))
  | [], _ => by
    rw [splitForks]
    exact KPA.pure' fun _ _ _ _ => ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, hl => by
    rw [splitForks]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (kpa_splitLoop y oy h0.1 h0.2.1) fun a K1 b1 r1 X1 ha => ?_
    rcases a with ⟨yh, yt⟩
    refine KPA.bind' (kpa_splitLoop n on (h0.2.2.1.up X1) (h0.2.2.2.up X1)) fun c K2 b2 r2 X2 hc => ?_
    rcases c with ⟨nh, nt⟩
    refine KPA.bind' (kpa_splitForks rest (fun e he => (hl e (List.mem_cons_of_mem _ he)).up (X1.trans X2)))
      fun d K3 b3 r3 X3 hd => ?_
    rcases d with ⟨rh, rt⟩
    have X13 := (X1.trans X2).trans X3
    exact KPA.pure' fun K bb r X =>
      ⟨fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X13).up X, ((ha.1.up X2).up X3).up X, (h0.2.2.1.up X13).up X, (hc.1.up X3).up X⟩
        · exact (hd.1 e he).up X,
       fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X13).up X, ((ha.2.up X2).up X3).up X, (h0.2.2.1.up X13).up X, (hc.2.up X3).up X⟩
        · exact (hd.2 e he).up X⟩

theorem kpa_splitBonds {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (b : List (Nat × Lazy S)), (∀ e ∈ b, BdL K0 b0 e) →
    KPA K0 b0 r0 (fun K bo _ x => BdP K bo x) (splitBonds b : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [], _ => by
    rw [splitBonds]
    exact KPA.pure' fun _ _ _ _ => ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | (o, l) :: rest, hl => by
    rw [splitBonds]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (kpa_splitLoop l o h0.1 h0.2) fun a K1 b1 r1 X1 ha => ?_
    rcases a with ⟨lh, lt⟩
    refine KPA.bind' (kpa_splitBonds rest (fun e he => (hl e (List.mem_cons_of_mem _ he)).up X1))
      fun d K2 b2 r2 X2 hd => ?_
    rcases d with ⟨rh, rt⟩
    have X12 := X1.trans X2
    exact KPA.pure' fun K bb r X =>
      ⟨fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X12).up X, (ha.1.up X2).up X⟩
        · exact (hd.1 e he).up X,
       fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X12).up X, (ha.2.up X2).up X⟩
        · exact (hd.2 e he).up X⟩
end

mutual
theorem kpa_intoLoopL {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (axe : Nat) : ∀ (l : Lazy S) (o : Nat), FL K0 b0 o →
    LzL (FL K0 b0) l →
    KPA K0 b0 r0 (fun K bo _ (x : Lazy S × Lazy S) => LzL (FL K bo) x.1 ∧ LzL (FL K bo) x.2)
      (intoLoopL axe l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o, ho, hl => by
    rw [intoLoopL]
    obtain ⟨hf, hb⟩ := lzL_parts hl
    refine KPA.bind' (kpa_intoSure axe s o ho) fun x K1 b1 r1 X1 _ => ?_
    rcases x with ⟨sd, sr⟩
    refine KPA.ite' _ (fun _ => KPA.pure' fun K bb r X => ⟨lzL_ofSure _ _, lzL_ofSure _ _⟩) fun _ => ?_
    refine KPA.bind' (kpa_intoForks axe f (fun e he => (hf e he).up X1)) fun y K2 b2 r2 X2 hy => ?_
    rcases y with ⟨fd, fr⟩
    refine KPA.bind' (kpa_intoBonds axe b (fun e he => (hb e he).up (X1.trans X2))) fun z K3 b3 r3 X3 hz => ?_
    rcases z with ⟨bd, br⟩
    have hy3 := (FkP.up hy X3)
    exact KPA.pure' fun K bb r X =>
      ⟨lzL_lazyPrune (lzL_of_parts (fun e he => (hy3.1 e he).up X) fun e he => (hz.1 e he).up X),
        lzL_lazyPrune (lzL_of_parts (fun e he => (hy3.2 e he).up X) fun e he => (hz.2 e he).up X)⟩

theorem kpa_intoForks {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (axe : Nat) : ∀ (f : List (ForkE S)),
    (∀ e ∈ f, FkL K0 b0 e) →
    KPA K0 b0 r0 (fun K bo _ x => FkP K bo x) (intoForks axe f : CM Map (List (ForkE S) × List (ForkE S)))
  | [], _ => by
    rw [intoForks]
    exact KPA.pure' fun _ _ _ _ => ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, hl => by
    rw [intoForks]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (kpa_intoLoopL axe y oy h0.1 h0.2.1) fun a K1 b1 r1 X1 ha => ?_
    rcases a with ⟨yh, yt⟩
    refine KPA.bind' (kpa_intoLoopL axe n on (h0.2.2.1.up X1) (h0.2.2.2.up X1)) fun c K2 b2 r2 X2 hc => ?_
    rcases c with ⟨nh, nt⟩
    refine KPA.bind' (kpa_intoForks axe rest (fun e he => (hl e (List.mem_cons_of_mem _ he)).up (X1.trans X2)))
      fun d K3 b3 r3 X3 hd => ?_
    rcases d with ⟨rh, rt⟩
    have X13 := (X1.trans X2).trans X3
    exact KPA.pure' fun K bb r X =>
      ⟨fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X13).up X, ((ha.1.up X2).up X3).up X, (h0.2.2.1.up X13).up X, (hc.1.up X3).up X⟩
        · exact (hd.1 e he).up X,
       fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X13).up X, ((ha.2.up X2).up X3).up X, (h0.2.2.1.up X13).up X, (hc.2.up X3).up X⟩
        · exact (hd.2 e he).up X⟩

theorem kpa_intoBonds {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (axe : Nat) : ∀ (b : List (Nat × Lazy S)),
    (∀ e ∈ b, BdL K0 b0 e) →
    KPA K0 b0 r0 (fun K bo _ x => BdP K bo x) (intoBonds axe b : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [], _ => by
    rw [intoBonds]
    exact KPA.pure' fun _ _ _ _ => ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | (o, l) :: rest, hl => by
    rw [intoBonds]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (kpa_intoLoopL axe l o h0.1 h0.2) fun a K1 b1 r1 X1 ha => ?_
    rcases a with ⟨lh, lt⟩
    refine KPA.bind' (kpa_intoBonds axe rest (fun e he => (hl e (List.mem_cons_of_mem _ he)).up X1))
      fun d K2 b2 r2 X2 hd => ?_
    rcases d with ⟨rh, rt⟩
    have X12 := X1.trans X2
    exact KPA.pure' fun K bb r X =>
      ⟨fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X12).up X, (ha.1.up X2).up X⟩
        · exact (hd.1 e he).up X,
       fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨(h0.1.up X12).up X, (ha.2.up X2).up X⟩
        · exact (hd.2 e he).up X⟩
end

section
variable {K0 : Nat → Nat → Prop} {b0 r0 : Nat}

/-- **`+split`**: the two halves' labels and the new block are `FL`. -/
theorem kpa_splitL {nex : NextL S} (h : RN K0 b0 r0 nex) :
    KPA K0 b0 r0 (fun K bo _ (x : Lazy S × Lazy S × Nat) => LzL (FL K bo) x.1 ∧ LzL (FL K bo) x.2.1 ∧ FL K bo x.2.2)
      (splitL nex : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold splitL
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simpa [getJmps] using h.2.1)) (by simpa [getJmps] using h.1))
    fun o K1 b1 r1 X1 ho => ?_
  refine KPA.bind' (kpa_splitLoop nex.laz o ho (h.2.2.up X1)) fun x K2 b2 r2 X2 hx => ?_
  rcases x with ⟨hd, tl⟩
  exact KPA.pure' fun K b r X => ⟨hx.1.up X, hx.2.up X, (ho.up X2).up X⟩

/-- **`+into`**: the two halves' labels and the new block are `FL`. -/
theorem kpa_intoL {nex : NextL S} (h : RN K0 b0 r0 nex) (axe : Nat) :
    KPA K0 b0 r0 (fun K bo _ (x : Lazy S × Lazy S × Nat) => LzL (FL K bo) x.1 ∧ LzL (FL K bo) x.2.1 ∧ FL K bo x.2.2)
      (intoL nex axe : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold intoL
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simpa [getJmps] using h.2.1)) (by simpa [getJmps] using h.1))
    fun o K1 b1 r1 X1 ho => ?_
  refine KPA.bind' (kpa_intoLoopL axe nex.laz o ho (h.2.2.up X1)) fun x K2 b2 r2 X2 hx => ?_
  rcases x with ⟨d, rr⟩
  exact KPA.pure' fun K b r X => ⟨hx.1.up X, hx.2.up X, (ho.up X2).up X⟩

end

/-! ## `+from` -/

mutual
theorem lzL_fromL' {P : Nat → Prop} {axe : Nat} : ∀ (l l' : Lazy S), fromL axe l = some l' → LzL P l → LzL P l'
  | mk s f b, l', h, hl => by
    rw [fromL] at h
    cases hl with
    | mk h1 h2 h3 h4 h5 h6 =>
    split at h
    · obtain ⟨s', _, rfl⟩ := Option.map_eq_some_iff.mp h; exact lzL_ofSure _ _
    · obtain ⟨s', _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f', hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨g1, g2, g3, g4⟩ := lzL_fromForks f f' hf h1 h2 h3 h4
      obtain ⟨k1, k2⟩ := lzL_fromBonds b b' hb h5 h6
      exact LzL.mk g1 g2 g3 g4 k1 k2

theorem lzL_fromForks {P : Nat → Prop} {axe : Nat} : ∀ (f f' : List (ForkE S)), fromForks axe f = some f' →
    (∀ e ∈ f, P e.1.1) → (∀ e ∈ f, LzL P e.1.2) → (∀ e ∈ f, P e.2.1) → (∀ e ∈ f, LzL P e.2.2) →
    (∀ e ∈ f', P e.1.1) ∧ (∀ e ∈ f', LzL P e.1.2) ∧ (∀ e ∈ f', P e.2.1) ∧ (∀ e ∈ f', LzL P e.2.2)
  | [], f', h, _, _, _, _ => by
    rw [fromForks] at h; cases h
    exact ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil,
      fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, f', h, h1, h2, h3, h4 => by
    rw [fromForks] at h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n', hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨i1, i2, i3, i4⟩ := lzL_fromForks rest r hr (fun e he => h1 e (List.mem_cons_of_mem _ he))
      (fun e he => h2 e (List.mem_cons_of_mem _ he)) (fun e he => h3 e (List.mem_cons_of_mem _ he))
      (fun e he => h4 e (List.mem_cons_of_mem _ he))
    have ly := lzL_fromL' y y' hy (h2 _ List.mem_cons_self)
    have ln := lzL_fromL' n n' hn (h4 _ List.mem_cons_self)
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_⟩ <;>
      rcases List.mem_cons.mp he with rfl | he
    · exact h1 ((oy, y), (on, n)) List.mem_cons_self
    · exact i1 e he
    · exact ly
    · exact i2 e he
    · exact h3 ((oy, y), (on, n)) List.mem_cons_self
    · exact i3 e he
    · exact ln
    · exact i4 e he

theorem lzL_fromBonds {P : Nat → Prop} {axe : Nat} : ∀ (b b' : List (Nat × Lazy S)), fromBonds axe b = some b' →
    (∀ e ∈ b, P e.1) → (∀ e ∈ b, LzL P e.2) → (∀ e ∈ b', P e.1) ∧ (∀ e ∈ b', LzL P e.2)
  | [], b', h, _, _ => by
    rw [fromBonds] at h; cases h
    exact ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | (o, l) :: rest, b', h, h1, h2 => by
    rw [fromBonds] at h
    obtain ⟨l', hl', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨i1, i2⟩ := lzL_fromBonds rest r hr (fun e he => h1 e (List.mem_cons_of_mem _ he))
      (fun e he => h2 e (List.mem_cons_of_mem _ he))
    have ll := lzL_fromL' l l' hl' (h2 _ List.mem_cons_self)
    refine ⟨fun e he => ?_, fun e he => ?_⟩ <;> rcases List.mem_cons.mp he with rfl | he
    · exact h1 (o, l) List.mem_cons_self
    · exact i1 e he
    · exact ll
    · exact i2 e he
end

theorem dn_fromSure {r axe : Nat} {s s' : Sure S} (h : fromSure axe s = some s') (hs : DN r s) : DN r s' :=
  ⟨fromSure_dist h hs.1, fun x hx => hs.2 x (Raw.fromSure_nmem_back h hx)⟩

mutual
theorem lzS_fromL' {r axe : Nat} : ∀ (l l' : Lazy S), fromL axe l = some l' → LzS (DN r) l → LzS (DN r) l'
  | mk s f b, l', h, hl => by
    rw [fromL] at h
    cases hl with
    | mk h1 h2 h3 h4 =>
    split at h
    · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h; exact lzS_ofSure (dn_fromSure hs' h1)
    · obtain ⟨s', hs', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f', hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨g2, g4⟩ := lzS_fromForks f f' hf h2 h3
      exact LzS.mk (dn_fromSure hs' h1) g2 g4 (lzS_fromBonds b b' hb h4)

theorem lzS_fromForks {r axe : Nat} : ∀ (f f' : List (ForkE S)), fromForks axe f = some f' →
    (∀ e ∈ f, LzS (DN r) e.1.2) → (∀ e ∈ f, LzS (DN r) e.2.2) →
    (∀ e ∈ f', LzS (DN r) e.1.2) ∧ (∀ e ∈ f', LzS (DN r) e.2.2)
  | [], f', h, _, _ => by
    rw [fromForks] at h; cases h
    exact ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, f', h, h2, h4 => by
    rw [fromForks] at h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n', hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rr, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨i2, i4⟩ := lzS_fromForks rest rr hr (fun e he => h2 e (List.mem_cons_of_mem _ he))
      (fun e he => h4 e (List.mem_cons_of_mem _ he))
    have ly := lzS_fromL' y y' hy (h2 _ List.mem_cons_self)
    have ln := lzS_fromL' n n' hn (h4 _ List.mem_cons_self)
    refine ⟨fun e he => ?_, fun e he => ?_⟩ <;> rcases List.mem_cons.mp he with rfl | he
    · exact ly
    · exact i2 e he
    · exact ln
    · exact i4 e he

theorem lzS_fromBonds {r axe : Nat} : ∀ (b b' : List (Nat × Lazy S)), fromBonds axe b = some b' →
    (∀ e ∈ b, LzS (DN r) e.2) → ∀ e ∈ b', LzS (DN r) e.2
  | [], b', h, _ => by
    rw [fromBonds] at h; cases h
    exact fun e he => absurd he List.not_mem_nil
  | (o, l) :: rest, b', h, h2 => by
    rw [fromBonds] at h
    obtain ⟨l', hl', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rr, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    have i2 := lzS_fromBonds rest rr hr (fun e he => h2 e (List.mem_cons_of_mem _ he))
    have ll := lzS_fromL' l l' hl' (h2 _ List.mem_cons_self)
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ll
    · exact i2 e he
end

/-- **`+from` keeps the labels.** (The statement with implicit lazies.) -/
theorem lzL_fromL {P : Nat → Prop} {axe : Nat} {l l' : Lazy S} (h : fromL axe l = some l') (hl : LzL P l) :
    LzL P l' := lzL_fromL' l l' h hl

/-- **`+from` keeps the `DN` entries.** -/
theorem lzS_fromL {r axe : Nat} {l l' : Lazy S} (h : fromL axe l = some l') (hl : LzS (DN r) l) : LzS (DN r) l' :=
  lzS_fromL' l l' h hl

/-! ## `+past` -/

theorem setTag_re {o : Nat} {region : List Nat} {g g' : Comp.Gen Map} {u : Unit}
    (h : (setTag o region : CM Map Unit) g = some (u, g')) : g'.re = g.re := by
  unfold setTag at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; split <;> rfl

/-- **`+past` keeps the `DN` entries.** -/
theorem rs_pastL (cod : Bell → Option Bool) {nex : NextL S} {r0 : Nat} (h : LzS (DN r0) nex.laz) (nom : Nomm)
    (region : List Nat) :
    RS r0 (fun r (n : NextL S) => LzS (DN r) n.laz) (pastL cod nex nom region : CM Map (NextL S)) := by
  rcases nex with ⟨laz, th⟩
  intro g x g' hr e
  unfold pastL at e
  split at e
  · cases e; exact h.upD hr
  rcases hh : hinted cod nom with _ | bb
  · rw [hh] at e; cases e
  cases bb
  · rw [hh] at e; cases e; exact h.upD hr
  · rw [hh] at e
    obtain ⟨o, g1, e1, e⟩ := bind_some e
    rw [emit_apply] at e1; cases e1
    obtain ⟨u, g2, e2, e⟩ := bind_some e
    cases e
    have hre : g'.re = g.re := (setTag_re e2).trans rfl
    have hr' : r0 ≤ g'.re := by rw [hre]; exact hr
    cases h with
    | mk hs hy hn hb =>
    refine LzS.mk (dn_bunt _) (fun e he => absurd he List.not_mem_nil) (fun e he => absurd he List.not_mem_nil)
      fun e he => ?_
    rcases List.mem_cons.mp he with rfl | he
    · exact LzS.mk (hs.up hr') (fun e he => (hy e he).upD hr') (fun e he => (hn e he).upD hr')
        (fun e he => absurd he List.not_mem_nil)
    · exact (hb e he).upD hr'

end Glue
end SkaModel
end Formalization
