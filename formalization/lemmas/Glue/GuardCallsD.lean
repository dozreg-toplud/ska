import lemmas.Glue.GuardCallsA
import lemmas.Ska.RawInvCLFrameCopy

/-!
# The direct call keeps `InvA` (track G, ninth pass)

LEDGER 2.c, toward `GuardMonoC`, over `KPA` (`Glue/GuardCallsA.lean`).

* `kpa_copyNeed`: the old `kp_copyNeed` (`Glue/GuardArms.lean`) ported by
  script with asserted replacements (`KP` to `KPA`, the continuations take
  the stage).
* `kpa_copyLazyL`, `kpa_mergeForks`, `kpa_mergeBonds`, `kpa_copyL`:
  `+copy` of lazy needs whose labels are `FL`; the `+add-ops` of the
  moves goes to the copy block or to a fork or bond label of the first
  lazy, all `FL` (`KPA.addOps'`), and every label of the result is one of
  the two lazies'.
* `kpa_pastL`: `+past` (the bond block is `FL`).
* `kpa_needOrd`: `+need-ord-alloc-regs` takes registers only.
* **`kpa_callDM`**: the direct call with `mono` `&` keeps `InvA` and
  returns a `RN` result (jump and lazy labels `FL`, no `~`), for every
  goal meeting `GFL`, given the same of the runs of its two parts
  (`RunA`) and of `+kerf` (`KerfA`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

theorem kpa_copyNeed {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (a b : Need) (ops : List Pole), NoSplit ops →
    KPA K0 b0 r0 (fun _ _ _ (x : Need × List Pole) => NoSplit x.2) (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _, h => by rw [copyNeed]; exact KPA.pure' fun _ _ _ _ => h
  | Need.this _, Need.none, _, h => by rw [copyNeed] <;> first | exact KPA.pure' fun _ _ _ _ => h | nofun
  | Need.pair _ _, Need.none, _, h => by rw [copyNeed] <;> first | exact KPA.pure' fun _ _ _ _ => h | nofun
  | Need.both _ _ _, Need.none, _, h => by rw [copyNeed] <;> first | exact KPA.pure' fun _ _ _ _ => h | nofun
  | Need.this _, Need.this _, _, h => by rw [copyNeed]; exact KPA.pure' fun _ _ _ _ => noSplit_cons rfl h
  | Need.this _, Need.both _ _ _, _, h => by rw [copyNeed]; exact KPA.pure' fun _ _ _ _ => noSplit_cons rfl h
  | Need.this _, Need.pair _ _, _, h => by
    rw [copyNeed]; exact KPA.bind' KPA.re' fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => noSplit_cons rfl h
  | Need.both _ _ _, Need.this _, _, h => by rw [copyNeed]; exact KPA.pure' fun _ _ _ _ => noSplit_cons rfl h
  | Need.pair _ _, Need.this _, _, h => by
    rw [copyNeed]; exact KPA.bind' KPA.re' fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => noSplit_cons rfl h
  | Need.both _ hl tl, Need.both _ hr tr, _, h => by
    rw [copyNeed]
    exact KPA.bind' (kpa_copyNeed hl hr _ (noSplit_cons rfl h)) fun x _ _ _ _ hx =>
      KPA.bind' (kpa_copyNeed tl tr _ hx) fun y _ _ _ _ hy => KPA.pure' fun _ _ _ _ => hy
  | Need.both _ hl tl, Need.pair p q, _, h => by
    rw [copyNeed]
    exact KPA.bind' KPA.re' fun _ _ _ _ _ _ => KPA.bind' (kpa_copyNeed hl p _ (noSplit_cons rfl h)) fun x _ _ _ _ hx =>
      KPA.bind' (kpa_copyNeed tl q _ hx) fun y _ _ _ _ hy => KPA.pure' fun _ _ _ _ => hy
  | Need.pair pl ql, Need.pair pr qr, _, h => by
    rw [copyNeed]
    exact KPA.bind' (kpa_copyNeed pl pr _ h) fun x _ _ _ _ hx => KPA.bind' (kpa_copyNeed ql qr _ hx) fun y _ _ _ _ hy => KPA.pure' fun _ _ _ _ => hy
  | Need.pair pl ql, Need.both _ h' t, _, h => by
    rw [copyNeed]
    exact KPA.bind' (kpa_copyNeed pl h' _ h) fun x _ _ _ _ hx => KPA.bind' (kpa_copyNeed ql t _ hx) fun y _ _ _ _ hy => KPA.pure' fun _ _ _ _ => hy

/-! ## Lazy labels -/

/-- A fork entry whose two labels and lazies are `FL`. -/
def FkL (K : Nat → Nat → Prop) (b : Nat) (e : ForkE S) : Prop :=
  FL K b e.1.1 ∧ LzL (FL K b) e.1.2 ∧ FL K b e.2.1 ∧ LzL (FL K b) e.2.2

/-- A bond entry whose label and lazy are `FL`. -/
def BdL (K : Nat → Nat → Prop) (b : Nat) (e : Nat × Lazy S) : Prop := FL K b e.1 ∧ LzL (FL K b) e.2

theorem FkL.up {K K' : Nat → Nat → Prop} {b r b' r' : Nat} {e : ForkE S} (h : FkL K b e)
    (x : XB K b r K' b' r') : FkL K' b' e := ⟨h.1.up x, h.2.1.up x, h.2.2.1.up x, h.2.2.2.up x⟩

theorem BdL.up {K K' : Nat → Nat → Prop} {b r b' r' : Nat} {e : Nat × Lazy S} (h : BdL K b e)
    (x : XB K b r K' b' r') : BdL K' b' e := ⟨h.1.up x, h.2.up x⟩

theorem lzL_parts {K : Nat → Nat → Prop} {b : Nat} {s : Sure S} {fork : List (ForkE S)} {bond : List (Nat × Lazy S)}
    (h : LzL (FL K b) (Lazy.mk s fork bond)) : (∀ e ∈ fork, FkL K b e) ∧ ∀ e ∈ bond, BdL K b e := by
  cases h with
  | mk h1 h2 h3 h4 h5 h6 => exact ⟨fun e he => ⟨h1 e he, h2 e he, h3 e he, h4 e he⟩, fun e he => ⟨h5 e he, h6 e he⟩⟩

theorem lzL_of_parts {K : Nat → Nat → Prop} {b : Nat} {s : Sure S} {fork : List (ForkE S)}
    {bond : List (Nat × Lazy S)} (hf : ∀ e ∈ fork, FkL K b e) (hb : ∀ e ∈ bond, BdL K b e) :
    LzL (FL K b) (Lazy.mk s fork bond) :=
  LzL.mk (fun e he => (hf e he).1) (fun e he => (hf e he).2.1) (fun e he => (hf e he).2.2.1)
    (fun e he => (hf e he).2.2.2) (fun e he => (hb e he).1) (fun e he => (hb e he).2)

theorem forall_filter {α : Type} {P : α → Prop} {l : List α} (q : α → Bool) (h : ∀ e ∈ l, P e) :
    ∀ e ∈ l.filter q, P e := fun e he => h e (List.mem_filter.mp he).1

theorem forall_append {α : Type} {P : α → Prop} {l1 l2 : List α} (h1 : ∀ e ∈ l1, P e) (h2 : ∀ e ∈ l2, P e) :
    ∀ e ∈ l1 ++ l2, P e := fun e he => (List.mem_append.mp he).elim (h1 e) (h2 e)

/-! ## `+copy` -/

mutual
theorem kpa_copyLazyL {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (o : Nat) : ∀ (a c : Lazy S), FL K0 b0 o →
    LzL (FL K0 b0) a → LzL (FL K0 b0) c →
    KPA K0 b0 r0 (fun K bo _ (l : Lazy S) => LzL (FL K bo) l) (copyLazyL o a c : CM Map (Lazy S))
  | mk s1 f1 b1, mk s2 f2 b2, ho, ha, hc => by
    rw [copyLazyL]
    obtain ⟨af, ab⟩ := lzL_parts ha
    obtain ⟨cf, cb⟩ := lzL_parts hc
    refine KPA.bind' (kpa_copyNeed _ _ _ noSplit_nil) fun x K1 bb1 r1 X1 hx => ?_
    rcases x with ⟨ned, ops⟩
    refine KPA.bind' (KPA.addOps' (guardedBody_of_noSplit hx) (ho.up X1)) fun _ K2 bb2 r2 X2 _ => ?_
    refine KPA.bind' (P := fun K bo _ (fk : List (ForkE S)) => ∀ e ∈ fk, FkL K bo e) ?_
      fun fk K3 bb3 r3 X3 hfk => ?_
    · have X12 := X1.trans X2
      split
      · exact KPA.pure' fun K b r X e he => (af e he).up (X12.trans X)
      · split
        · exact KPA.pure' fun K b r X e he => (cf e he).up (X12.trans X)
        · refine KPA.bind' (kpa_mergeForks _ f1 (fun k v hv => (cf v (Raw.fc_index_mem _ hv)).up X12)
            (fun e he => (af e he).up X12)) fun mg K4 bb4 r4 X4 hmg => ?_
          exact KPA.pure' fun K b r X => forall_append (fun e he => (hmg e he).up X)
            (forall_filter _ fun e he => (cf e he).up ((X12.trans X4).trans X))
    refine KPA.bind' (P := fun K bo _ (bd : List (Nat × Lazy S)) => ∀ e ∈ bd, BdL K bo e) ?_
      fun bd K4 bb4 r4 X4 hbd => ?_
    · have X13 := (X1.trans X2).trans X3
      split
      · exact KPA.pure' fun K b r X e he => (ab e he).up (X13.trans X)
      · split
        · exact KPA.pure' fun K b r X e he => (cb e he).up (X13.trans X)
        · refine KPA.bind' (kpa_mergeBonds _ b1 (fun k v hv => (cb v (Raw.fc_index_mem _ hv)).up X13)
            (fun e he => (ab e he).up X13)) fun mg K5 bb5 r5 X5 hmg => ?_
          exact KPA.pure' fun K b r X => forall_append (fun e he => (hmg e he).up X)
            (forall_filter _ fun e he => (cb e he).up ((X13.trans X5).trans X))
    exact KPA.pure' fun K b r X => lzL_of_parts (fun e he => ((hfk e he).up X4).up X) (fun e he => (hbd e he).up X)

theorem kpa_mergeForks {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    (∀ k v, HoonMap.get idx k = some v → FkL K0 b0 v) → (∀ e ∈ l, FkL K0 b0 e) →
    KPA K0 b0 r0 (fun K bo _ (r : List (ForkE S)) => ∀ e ∈ r, FkL K bo e) (mergeForks idx l : CM Map (List (ForkE S)))
  | [], _, _ => by rw [mergeForks]; exact KPA.pure' fun _ _ _ _ e he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, hi, hl => by
    rw [mergeForks]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (P := fun K bo _ (e : ForkE S) => FkL K bo e) ?_ fun e K1 bb1 r1 X1 he => ?_
    · split
      · exact KPA.pure' fun K b r X => h0.up X
      · rename_i v my mon mn hv
        have hm := hi _ _ hv
        split
        · refine KPA.bind' (kpa_copyLazyL oy y my h0.1 h0.2.1 hm.2.1) fun y' K1 bb1 r1 X1 hy => ?_
          refine KPA.bind' (kpa_copyLazyL on n mn (h0.2.2.1.up X1) (h0.2.2.2.up X1) (hm.2.2.2.up X1))
            fun n' K2 bb2 r2 X2 hn => ?_
          exact KPA.pure' fun K b r X => ⟨(h0.1.up (X1.trans X2)).up X, (hy.up X2).up X,
            (h0.2.2.1.up (X1.trans X2)).up X, hn.up X⟩
        · exact KPA.fail
    refine KPA.bind' (kpa_mergeForks idx rest (fun k v hv => (hi k v hv).up X1)
      (fun e' he' => (hl e' (List.mem_cons_of_mem _ he')).up X1)) fun r K2 bb2 r2 X2 hr => ?_
    exact KPA.pure' fun K b r' X e' he' => by
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (he.up X2).up X
      · exact (hr e' he').up X

theorem kpa_mergeBonds {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    (∀ k v, HoonMap.get idx k = some v → BdL K0 b0 v) → (∀ e ∈ l, BdL K0 b0 e) →
    KPA K0 b0 r0 (fun K bo _ (r : List (Nat × Lazy S)) => ∀ e ∈ r, BdL K bo e)
      (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [], _, _ => by rw [mergeBonds]; exact KPA.pure' fun _ _ _ _ e he => absurd he List.not_mem_nil
  | (ob, l) :: rest, hi, hl => by
    rw [mergeBonds]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (P := fun K bo _ (e : Nat × Lazy S) => BdL K bo e) ?_ fun e K1 bb1 r1 X1 he => ?_
    · split
      · exact KPA.pure' fun K b r X => h0.up X
      · rename_i v m hv
        have hm := hi _ _ hv
        refine KPA.bind' (kpa_copyLazyL ob l m h0.1 h0.2 hm.2) fun l' K1 bb1 r1 X1 hl' => ?_
        exact KPA.pure' fun K b r X => ⟨(h0.1.up X1).up X, hl'.up X⟩
    refine KPA.bind' (kpa_mergeBonds idx rest (fun k v hv => (hi k v hv).up X1)
      (fun e' he' => (hl e' (List.mem_cons_of_mem _ he')).up X1)) fun r K2 bb2 r2 X2 hr => ?_
    exact KPA.pure' fun K b r' X e' he' => by
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (he.up X2).up X
      · exact (hr e' he').up X
end

/-- What a run returns: its jump and lazy labels are `FL`, its jump passes no `~`. -/
def RN (K : Nat → Nat → Prop) (bo : Nat) (_ : Nat) (n : NextL S) : Prop :=
  FL K bo n.th.there ∧ JOK n.th ∧ LzL (FL K bo) n.laz

theorem RN.up {K K' : Nat → Nat → Prop} {b r b' r' rr : Nat} {n : NextL S} (h : RN K b rr n)
    (x : XB K b r K' b' r') (rr' : Nat) : RN K' b' rr' n := ⟨h.1.up x, h.2.1, h.2.2.up x⟩

/-- **`+copy`.** -/
theorem kpa_copyL {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {first : NextL S} {second : Lazy S} (h1 : RN K0 b0 r0 first)
    (h2 : LzL (FL K0 b0) second) : KPA K0 b0 r0 RN (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simpa [getJmps] using h1.2.1)) (by simpa [getJmps] using h1.1))
    fun o K1 bb1 r1 X1 ho => ?_
  refine KPA.bind' (kpa_copyLazyL o _ _ ho (h1.2.2.up X1) (h2.up X1)) fun l K2 bb2 r2 X2 hl => ?_
  exact KPA.pure' fun K b r X => ⟨(ho.up X2).up X, jok_jmp0 _, hl.up X⟩

theorem kpa_setTag {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (o : Nat) (region : List Nat) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (setTag o region : CM Map Unit) :=
  KPA.same fun g x g' h => by
    cases h
    split <;> exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩

/-- **`+past`.** -/
theorem kpa_pastL {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (cod : Bell → Option Bool) {nex : NextL S}
    (h : RN K0 b0 r0 nex) (nom : Nomm) (region : List Nat) :
    KPA K0 b0 r0 RN (pastL cod nex nom region : CM Map (NextL S)) := by
  unfold pastL
  split
  · exact KPA.pure' fun K b r X => h.up X r
  split
  · exact KPA.fail
  · exact KPA.pure' fun K b r X => h.up X r
  · refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simpa [getJmps] using h.2.1)) (by simpa [getJmps] using h.1))
      fun o K1 bb1 r1 X1 ho => ?_
    refine KPA.bind' (kpa_setTag _ _) fun _ K2 bb2 r2 X2 _ => ?_
    refine KPA.pure' fun K b r X => ⟨(ho.up X2).up X, jok_jmp0 _, ?_⟩
    rcases hl : nex.laz with ⟨s, f, bd⟩
    have hz := h.2.2; rw [hl] at hz
    obtain ⟨hf, hb⟩ := lzL_parts hz
    have XX := X1.trans (X2.trans X)
    refine lzL_of_parts (fun e he => absurd he List.not_mem_nil) fun e he => ?_
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨(ho.up X2).up X, lzL_of_parts (fun e he => (hf e he).up XX) fun e he => absurd he List.not_mem_nil⟩
    · exact (hb e he).up XX

/-- **`+need-ord-alloc-regs`** takes registers only. -/
theorem kpa_needOrd {K0 : Nat → Nat → Prop} {b0 r0 : Nat} :
    ∀ ord : NeedOrd, KPA K0 b0 r0 (fun _ _ _ _ => True) (needOrdAllocRegs ord : CM Map Need)
  | NeedOrd.none => by rw [needOrdAllocRegs]; exact KPA.pure' fun _ _ _ _ => trivial
  | NeedOrd.this => by
    rw [needOrdAllocRegs]; exact KPA.bind' KPA.re' fun _ _ _ _ _ _ => KPA.pure' fun _ _ _ _ => trivial
  | NeedOrd.pair p q => by
    rw [needOrdAllocRegs]
    exact KPA.bind' (kpa_needOrd p) fun _ _ _ _ _ _ => KPA.bind' (kpa_needOrd q) fun _ _ _ _ _ _ =>
      KPA.ite' _ (fun _ => KPA.crash) fun _ => KPA.pure' fun _ _ _ _ => trivial
  | NeedOrd.both p q => by
    rw [needOrdAllocRegs]
    exact KPA.bind' KPA.re' fun _ _ _ _ _ _ => KPA.bind' (kpa_needOrd p) fun _ _ _ _ _ _ =>
      KPA.bind' (kpa_needOrd q) fun _ _ _ _ _ _ => KPA.ite' _ (fun _ => KPA.crash) fun _ => KPA.pure' fun _ _ _ _ => trivial

/-! ## The direct call -/

/-- **A run keeps `InvA` and returns `RN`** for every goal meeting `GFL`. -/
def RunA (run : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (K0 : Nat → Nat → Prop) b0 r0 (goal : CGoalL S) region, GFL K0 b0 goal → KPA K0 b0 r0 RN (run goal region)

theorem gfl_next {K : Nat → Nat → Prop} {b : Nat} {laz : Lazy S} {th : Jmp} (h1 : FL K b th.there) (h2 : JOK th)
    (h3 : LzL (FL K b) laz) : GFL K b (CGoalL.next laz th) := ⟨h1, h2, h3⟩

/-- The tail of the direct call: the formula part, `+past`, the subject part,
`+copy`. -/
theorem kpa_callTail {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (cod : Bell → Option Bool)
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (hp : RunA rp) (hq : RunA rq) (p q : Nomm) (region : List Nat)
    (laz : Lazy S) (th : Jmp) (hth : FL K0 b0 th.there) (hj : JOK th) (hl : LzL (FL K0 b0) laz) :
    KPA K0 b0 r0 RN (do
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      let nexFol ← pastL cod nexFol p region
      let nexSub ← rp (CGoalL.next laz nexFol.th) region
      copyL nexSub nexFol.laz : CM Map (NextL S)) := by
  refine KPA.bind' (P := RN) ?_ fun n1 K1 bb1 r1 X1 h1 => ?_
  · split
    · exact KPA.pure' fun K b r X => ⟨hth.up X, hj, lzL_ofSure _ _⟩
    · exact hq _ _ _ _ _ (gfl_next hth hj (lzL_ofSure _ _))
  refine KPA.bind' (kpa_pastL cod h1 p region) fun n2 K2 bb2 r2 X2 h2 => ?_
  refine KPA.bind' (hp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (hl.up (X1.trans X2)))) fun n3 K3 bb3 r3 X3 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X3)

/-- **The direct call with `mono` `&` keeps `InvA`**, given its two parts'
runs and `+kerf`. -/
theorem kpa_callDM (hk : KerfA S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : RunA rp) (hq : RunA rq) (p q : Nomm) (bl : Bell) (key : Option Noun) {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    {goal : CGoalL S} (hg : GFL K0 b0 goal) (region : List Nat) :
    KPA K0 b0 r0 RN (callDM env rp rq p q bl key goal region : CM Map (NextL S)) := by
  have hnone : KPA K0 b0 r0 RN (match key, env.ring bl, env.need bl with
      | Option.none, Option.none, some bNed => do
        let subNed ← needOrdAllocRegs bNed
        let (subPes, callBlock) ← monoBlocks bl subNed goal
        let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
        copyL nexSub nexFol.laz
      | _, _, _ => fun _ => Option.none : CM Map (NextL S)) := by
    split
    · refine KPA.bind' (kpa_needOrd _) fun subNed K1 bb1 r1 X1 _ => ?_
      refine KPA.bind' (kpa_monoBlocks hk bl subNed (hg.up X1)) fun x K2 bb2 r2 X2 hx => ?_
      rcases x with ⟨sp, cb⟩
      exact kpa_callTail env.cod hp hq p q region _ (jmp0 cb) hx (jok_jmp0 _) (lzL_ofSure _ _)
    · exact KPA.fail
  unfold callDM
  cases goal with
  | next laz th =>
    by_cases hc : (env.pure bl && noneEquivalentL laz) = true
    · simp only [hc, ↓reduceIte]
      exact kpa_callTail env.cod hp hq p q region _ th hg.1 hg.2.1 (lzL_ofSure _ _)
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact hnone
  | pick z o => exact hnone
  | done => exact hnone

/-! ## The top of a run -/

/-- **The empty state meets `InvA` with no annotation.** -/
theorem invA_gen0 : InvA (fun _ _ => False) (gen0 : Comp.Gen Map) where
  ok := ⟨fun o b hb => by simp [gen0, HoonMap.get_empty] at hb, fun _ _ _ _ hk => hk.elim, fun _ hk => hk,
    fun _ _ _ _ _ _ hk => hk.elim, fun o b hb => by simp [gen0, HoonMap.get_empty] at hb⟩
  drop := rfl
  below := fun o b hb => by simp [gen0, HoonMap.get_empty] at hb
  kin := fun _ _ hk => hk.elim

/-- **What `RunA` gives of the top run** (`finishLUCM` runs `runLCM env true`
under `%done` from `gen0`): an annotation `K` with `InvA K` at its end and a
result jump at an `FL` label. -/
theorem runA_top {run : CGoalL S → List Nat → CM Map (NextL S)} (h : RunA run) {nex : NextL S}
    {g1 : Comp.Gen Map} (e : run CGoalL.done [] gen0 = some (nex, g1)) : ∃ K, InvA K g1 ∧ RN K g1.bo g1.re nex := by
  obtain ⟨K', hI, -, hR⟩ := (h (fun _ _ => False) 1 0 CGoalL.done [] trivial).k _ gen0 nex g1 invA_gen0
    (by simp [gen0]) (XB.refl _ _ _) e
  exact ⟨K', hI, hR⟩

end Glue
end SkaModel
end Formalization
