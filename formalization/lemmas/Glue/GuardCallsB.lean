import lemmas.Glue.GuardCallsD
import lemmas.Ska.CompWholeKern

/-!
# The base of the run-level guard with calls (track G, tenth pass)

LEDGER 2.c, toward `GuardMonoC`.  The ninth pass's `KerfA` asks `+kerf` to
keep `InvA` for EVERY `nex` whose labels are `FL`; that is false as stated
(`+kern-need` of a need with a register twice can put a `%hed` after a write
of the register it splits, so the split is not guarded).  What `+kern` needs
of the lazy it meets is that every sure need in it (the root and every fork
and bond entry) has DISTINCT registers, all below `re` (`LzS (DN re)`): then
each gate's `+kern-need` output is guarded (`kernNeed_guarded`).

* `NoSixC`: no `%6` anywhere (the class of this pass; `%11`, `%12` and the
  rest fail in `runLCM`).
* `LzS Q`: every sure need of a lazy meets `Q`; `DN r`: distinct registers,
  all below `r`; `GD r goal`: a `%next` goal's lazy meets `LzS (DN r)`.
* `RS r0 Q m`: every run of `m` from `re ≥ r0` grows `re` and returns a
  result in `Q re'` (a fact on registers only); `KPA.andR` puts it beside a
  `KPA`.
* `RunG run`: `RunA` with `GD` on the goal: every run for a goal with `FL`
  jumps and `DN` entries keeps `InvA` and returns `RN`.
* `KerfG`: `+kerf` keeps `InvA` for a `nex` with `FL` labels and `DN`
  entries, and returns an `FL` block and a register below `re`.
* **`KIMid`** (the mid-run fact owed by track D, a named hypothesis): runs
  of the class, `+split` and `+into` keep `LzS (DN re)`.
* The `KPA` steps that leave the blocks alone: `get`, `proxy`,
  `+sure-require-look`; and `kpa_walkLazy`: `+walk-lazy` of a gate that
  keeps `InvA` at every `FL` label whose sure need meets `Q`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-! ## The class -/

/-- **No `%6` anywhere in the nomm** (calls included). -/
def NoSixC : Nomm → Prop
  | Nomm.n6 _ _ _ => False
  | Nomm.cons p q => NoSixC p ∧ NoSixC q
  | Nomm.n2 p q _ => NoSixC p ∧ NoSixC q
  | Nomm.n3 p => NoSixC p
  | Nomm.n4 p => NoSixC p
  | Nomm.n5 p q => NoSixC p ∧ NoSixC q
  | Nomm.n7 p q => NoSixC p ∧ NoSixC q
  | Nomm.n10 _ v q => NoSixC v ∧ NoSixC q
  | _ => True

/-- **The class of this pass**: raw whole-subject code with no `%6`. -/
def NoSixM : MonoClass := fun _ _ _ nm => NoSixC nm

/-! ## Sure needs of a lazy -/

/-- **Every sure need of a lazy meets `Q`** (the root, and the fork and
bond lazies, recursively). -/
inductive LzS (Q : Sure S → Prop) : Lazy S → Prop
  | mk {s : Sure S} {fork : List ((Nat × Lazy S) × (Nat × Lazy S))} {bond : List (Nat × Lazy S)} :
      Q s → (∀ e ∈ fork, LzS Q e.1.2) → (∀ e ∈ fork, LzS Q e.2.2) → (∀ e ∈ bond, LzS Q e.2) →
      LzS Q (Lazy.mk s fork bond)

theorem LzS.imp {P Q : Sure S → Prop} (hpq : ∀ s, P s → Q s) {l : Lazy S} (h : LzS P l) : LzS Q l := by
  induction h with
  | mk h1 _ _ _ i2 i3 i4 => exact LzS.mk (hpq _ h1) i2 i3 i4

theorem LzS.root {Q : Sure S → Prop} {l : Lazy S} (h : LzS Q l) : Q l.sure := by
  cases h with
  | mk h1 _ _ _ => exact h1

theorem lzS_ofSure {Q : Sure S → Prop} {s : Sure S} (h : Q s) : LzS Q (Lazy.ofSure s) :=
  LzS.mk h (fun e he => absurd he List.not_mem_nil) (fun e he => absurd he List.not_mem_nil)
    (fun e he => absurd he List.not_mem_nil)

/-- **Distinct registers, all below `r`.** -/
def DN (r : Nat) (s : Sure S) : Prop := Distinct s.ned ∧ NB r s.ned

theorem DN.up {r r' : Nat} {s : Sure S} (h : DN r s) (hr : r ≤ r') : DN r' s :=
  ⟨h.1, fun x hx => Nat.lt_of_lt_of_le (h.2 x hx) hr⟩

theorem LzS.upD {r r' : Nat} {l : Lazy S} (h : LzS (DN r) l) (hr : r ≤ r') : LzS (DN r') l :=
  h.imp fun _ hs => hs.up hr

theorem dn_bunt (r : Nat) : DN r (Sure.bunt : Sure S) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show Distinct Need.none; trivial
  · exact (show NMem Need.none x from hx).elim

theorem dn_reg {r x : Nat} (h : x < r) : DN r (lazyReg x : Sure S) :=
  ⟨trivial, fun y hy => by simp only [lazyReg, NMem] at hy; omega⟩

theorem dn_this {r x : Nat} (h : x < r) : DN r (⟨Need.this x, HoonSet.empty⟩ : Sure S) :=
  ⟨trivial, fun y hy => by simp only [NMem] at hy; omega⟩

theorem lzS_bunt (r : Nat) : LzS (DN r) (Lazy.ofSure (Sure.bunt : Sure S)) := lzS_ofSure (dn_bunt r)

theorem lzS_reg {r x : Nat} (h : x < r) : LzS (DN r) (Lazy.ofSure (lazyReg x : Sure S)) := lzS_ofSure (dn_reg h)

/-- A `%next` goal's lazy meets `LzS (DN r)`. -/
def GD (r : Nat) : CGoalL S → Prop
  | CGoalL.next laz _ => LzS (DN r) laz
  | _ => True

theorem GD.up {r r' : Nat} {goal : CGoalL S} (h : GD r goal) (hr : r ≤ r') : GD r' goal := by
  cases goal with
  | next laz th => exact LzS.upD h hr
  | pick => trivial
  | done => trivial

/-! ## Facts on registers beside `KPA` -/

/-- **Every run of `m` from `re ≥ r0` grows `re` and returns a result in
`Q re'`.** -/
def RS {α : Type} (r0 : Nat) (Q : Nat → α → Prop) (m : CM Map α) : Prop :=
  ∀ (g : Comp.Gen Map) x g', r0 ≤ g.re → m g = some (x, g') → Q g'.re x

theorem KPA.andR {α : Type} {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop}
    {Q : Nat → α → Prop} {m : CM Map α} (h : KPA K0 b0 r0 P m) (hq : RS r0 Q m) :
    KPA K0 b0 r0 (fun K b r x => P K b r x ∧ Q r x) m := by
  constructor
  intro K g x g' hI h0 hX e
  obtain ⟨K', hI', X, p⟩ := h.k K g x g' hI h0 hX e
  exact ⟨K', hI', X, p, hq g x g' hX.2.1 e⟩

/-! ## Runs, `+kerf`, the mid-run fact -/

/-- **A run keeps `InvA` and returns `RN`** for every goal with `FL` jumps
whose lazy has `DN` entries. -/
def RunG (run : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (K0 : Nat → Nat → Prop) b0 r0 (goal : CGoalL S) region, GFL K0 b0 goal → GD r0 goal →
    KPA K0 b0 r0 RN (run goal region)

/-- **`+kerf` in the middle of a run**, for a `nex` with `FL` labels and
`DN` entries: it keeps `InvA` and returns an `FL` block and a register
below `re`. -/
def KerfG (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] : Prop :=
  ∀ K0 b0 r0 (nex : NextL S), FL K0 b0 nex.th.there → JOK nex.th → LzL (FL K0 b0) nex.laz →
    LzS (DN r0) nex.laz →
    KPA K0 b0 r0 (fun K bo r (x : Nat × Nat) => FL K bo x.1 ∧ x.2 < r) (kerf nex : CM Map (Nat × Nat))

/-- **The mid-run fact (owed by track D)**: a run of the class from a goal
whose lazy has `DN` entries at `re` returns such a lazy at its end; so do
`+split` and `+into` with their two halves. -/
structure KIMid (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop where
  run : ∀ nm sup, NoSixC nm → ∀ (goal : CGoalL S) region (g g' : Comp.Gen Map) (x : NextL S), GD g.re goal →
    runLCM env true sup nm goal region g = some (x, g') → LzS (DN g'.re) x.laz
  split : ∀ (nex : NextL S) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat), LzS (DN g.re) nex.laz →
    splitL nex g = some (x, g') → LzS (DN g'.re) x.1 ∧ LzS (DN g'.re) x.2.1
  into : ∀ (nex : NextL S) (axe : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat), LzS (DN g.re) nex.laz →
    intoL nex axe g = some (x, g') → LzS (DN g'.re) x.1 ∧ LzS (DN g'.re) x.2.1

/-! ## Steps that leave the blocks alone -/

namespace KPA

variable {K0 : Nat → Nat → Prop} {b0 r0 : Nat}

theorem get' : KPA K0 b0 r0 (fun _ _ _ _ => True) (get : CM Map (Comp.Gen Map)) :=
  same fun g x g' h => by rw [get_apply] at h; cases h; exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩

theorem proxy' (r o : Nat) : KPA K0 b0 r0 (fun _ _ _ _ => True) (proxy r o : CM Map Nat) :=
  same fun g x g' h => by
    unfold proxy at h
    simp only at h
    split at h
    · cases h; exact ⟨rfl, rfl, rfl, Nat.le_succ _⟩
    · obtain ⟨tag, _, e⟩ := Option.map_eq_some_iff.mp h
      cases e; exact ⟨rfl, rfl, rfl, Nat.le_succ _⟩

theorem sureRequireLook' (sur : Sure S) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (sureRequireLook sur : CM Map Need) :=
  same fun g x g' h => by
    obtain ⟨k, e⟩ := (sureRequireLook_spec h).gen
    have hl := (sureRequireLook_spec h).le
    subst e
    exact ⟨rfl, rfl, rfl, hl⟩

end KPA

/-! ## `+walk-lazy` -/

mutual
/-- **`+walk-lazy` of a gate that keeps `InvA` at every `FL` label whose
sure need meets `Q`** (`Q` kept as `re` grows). -/
theorem kpa_walkLazy {Q : Nat → Sure S → Prop} (hQ : ∀ r r' s, r ≤ r' → Q r s → Q r' s)
    {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ (K0 : Nat → Nat → Prop) b0 r0 o s, FL K0 b0 o → Q r0 s → KPA K0 b0 r0 (fun _ _ _ _ => True) (f o s))
    {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (o : Nat) (l : Lazy S), FL K0 b0 o → LzL (FL K0 b0) l →
    LzS (Q r0) l → KPA K0 b0 r0 (fun _ _ _ _ => True) (walkLazy f o l : CM Map Unit)
  | o, mk s fk bd, ho, hl, hs => by
    rw [walkLazy]
    obtain ⟨hlf, hlb⟩ := lzL_parts hl
    cases hs with
    | mk hs0 hsy hsn hsb =>
    refine KPA.bind' (hf K0 b0 r0 o s ho hs0) fun _ K1 b1 r1 X1 _ => ?_
    refine KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial) fun _ => ?_
    refine KPA.bind' (kpa_walkForks hQ hf fk (fun e he => (hlf e he).up X1)
      (fun e he => (hsy e he).imp fun s h => hQ _ _ s X1.2.1 h)
      (fun e he => (hsn e he).imp fun s h => hQ _ _ s X1.2.1 h)) fun _ K2 b2 r2 X2 _ => ?_
    exact kpa_walkBonds hQ hf bd (fun e he => (hlb e he).up (X1.trans X2))
      (fun e he => (hsb e he).imp fun s h => hQ _ _ s (X1.trans X2).2.1 h)

theorem kpa_walkForks {Q : Nat → Sure S → Prop} (hQ : ∀ r r' s, r ≤ r' → Q r s → Q r' s)
    {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ (K0 : Nat → Nat → Prop) b0 r0 o s, FL K0 b0 o → Q r0 s → KPA K0 b0 r0 (fun _ _ _ _ => True) (f o s))
    {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (fk : List (ForkE S)), (∀ e ∈ fk, FkL K0 b0 e) →
    (∀ e ∈ fk, LzS (Q r0) e.1.2) → (∀ e ∈ fk, LzS (Q r0) e.2.2) →
    KPA K0 b0 r0 (fun _ _ _ _ => True) (walkForks f fk : CM Map Unit)
  | [], _, _, _ => by rw [walkForks]; exact KPA.pure' fun _ _ _ _ => trivial
  | ((oy, y), (on, n)) :: rest, hl, hy, hn => by
    rw [walkForks]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (kpa_walkLazy hQ hf oy y h0.1 h0.2.1 (hy _ List.mem_cons_self)) fun _ K1 b1 r1 X1 _ => ?_
    refine KPA.bind' (kpa_walkLazy hQ hf on n (h0.2.2.1.up X1) (h0.2.2.2.up X1)
      ((hn _ List.mem_cons_self).imp fun s h => hQ _ _ s X1.2.1 h)) fun _ K2 b2 r2 X2 _ => ?_
    have X12 := X1.trans X2
    exact kpa_walkForks hQ hf rest (fun e he => (hl e (List.mem_cons_of_mem _ he)).up X12)
      (fun e he => (hy e (List.mem_cons_of_mem _ he)).imp fun s h => hQ _ _ s X12.2.1 h)
      (fun e he => (hn e (List.mem_cons_of_mem _ he)).imp fun s h => hQ _ _ s X12.2.1 h)

theorem kpa_walkBonds {Q : Nat → Sure S → Prop} (hQ : ∀ r r' s, r ≤ r' → Q r s → Q r' s)
    {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ (K0 : Nat → Nat → Prop) b0 r0 o s, FL K0 b0 o → Q r0 s → KPA K0 b0 r0 (fun _ _ _ _ => True) (f o s))
    {K0 : Nat → Nat → Prop} {b0 r0 : Nat} : ∀ (bd : List (Nat × Lazy S)), (∀ e ∈ bd, BdL K0 b0 e) →
    (∀ e ∈ bd, LzS (Q r0) e.2) → KPA K0 b0 r0 (fun _ _ _ _ => True) (walkBonds f bd : CM Map Unit)
  | [], _, _ => by rw [walkBonds]; exact KPA.pure' fun _ _ _ _ => trivial
  | (o, l) :: rest, hl, hs => by
    rw [walkBonds]
    have h0 := hl _ List.mem_cons_self
    refine KPA.bind' (kpa_walkLazy hQ hf o l h0.1 h0.2 (hs _ List.mem_cons_self)) fun _ K1 b1 r1 X1 _ => ?_
    exact kpa_walkBonds hQ hf rest (fun e he => (hl e (List.mem_cons_of_mem _ he)).up X1)
      (fun e he => (hs e (List.mem_cons_of_mem _ he)).imp fun s h => hQ _ _ s X1.2.1 h)
end

mutual
theorem lzS_true : ∀ l : Lazy S, LzS (fun _ => True) l
  | mk s fk bd => LzS.mk trivial (fun e he => (lzS_trueF fk e he).1) (fun e he => (lzS_trueF fk e he).2)
      (lzS_trueB bd)

theorem lzS_trueF : ∀ (fk : List (ForkE S)), ∀ e ∈ fk, LzS (fun _ => True) e.1.2 ∧ LzS (fun _ => True) e.2.2
  | [] => fun e he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest => fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨lzS_true y, lzS_true n⟩
    · exact lzS_trueF rest e he

theorem lzS_trueB : ∀ (bd : List (Nat × Lazy S)), ∀ e ∈ bd, LzS (fun _ => True) e.2
  | [] => fun e he => absurd he List.not_mem_nil
  | (o, l) :: rest => fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact lzS_true l
    · exact lzS_trueB rest e he
end

/-- `+walk-lazy` of a gate that keeps `InvA` at every `FL` label (no
condition on the sure need). -/
theorem kpa_walkLazyT {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ (K0 : Nat → Nat → Prop) b0 r0 o s, FL K0 b0 o → KPA K0 b0 r0 (fun _ _ _ _ => True) (f o s))
    {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (o : Nat) (l : Lazy S) (ho : FL K0 b0 o) (hl : LzL (FL K0 b0) l) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (walkLazy f o l : CM Map Unit) :=
  kpa_walkLazy (Q := fun _ _ => True) (fun _ _ _ _ h => h) (fun K0 b0 r0 o s ho _ => hf K0 b0 r0 o s ho)
    o l ho hl (lzS_true l)

end Glue
end SkaModel
end Formalization
