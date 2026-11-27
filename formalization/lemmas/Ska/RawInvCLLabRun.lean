import lemmas.Ska.RawInvCLLab

/-!
# `LabUniq` at run level: the induction on `PlainN`

README Gaps 14 (b), track D.  Every run of `runLC` on `PlainN` from a
`Fresh` goal whose tree is `LabUniq` with its entries below `bo` (`LG`)
ends with a `Fresh` result with the same clause (`HRL`), by the induction
and the `HT` skeleton of `ht_runLC` (`RawInvCAT.lean`) with the label
clause added at each step.

* `LabSteps`: the five local facts it rests on (`+split`, `+into`, `+from`,
  `+copy` keep `LabUniq` and the entries' labels; `+past` adds a bond at
  the fresh label `bo`).
* `LL l g`: the tree `l` is `LabUniq` with its entries below `g.bo`;
  `stab_ll`, `ll_ofSure`.
* `HT.withR`: an `HT` with one more pre- and postcondition read off the run
  and `KP`.
* The steps with labels: `htl_simpleNextL`, `htl_bombL`, `htl_splitL`,
  `htl_intoL`, `htl_pastL`, `htl_copyL`, `htl_tail`, `htl_bin` (run q,
  `+past`, run p, `+copy`), `htl_callL`.
* **`labRun_plainOf`**: `HRL (runLC env sup nm)` on all of `PlainN`, from
  `LabSteps`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The local facts on labels** the induction rests on. -/
structure LabSteps (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop where
  split : ∀ {Q : Nat → Prop} {nex : NextL S} {g g' : Comp.Gen Map} {hed tel : Lazy S} {o : Nat},
    splitL nex g = some ((hed, tel, o), g') → LabUniq nex.laz → (∀ e ∈ entries nex.laz, Q e.1) →
    LabUniq hed ∧ LabUniq tel ∧ (∀ e ∈ entries hed, Q e.1) ∧ ∀ e ∈ entries tel, Q e.1
  into : ∀ {Q : Nat → Prop} {nex : NextL S} {axe : Nat} {g g' : Comp.Gen Map} {d r : Lazy S} {o : Nat},
    intoL nex axe g = some ((d, r, o), g') → LabUniq nex.laz → (∀ e ∈ entries nex.laz, Q e.1) →
    LabUniq d ∧ LabUniq r ∧ (∀ e ∈ entries d, Q e.1) ∧ ∀ e ∈ entries r, Q e.1
  fromL : ∀ {Q : Nat → Prop} {axe : Nat} {L L' : Lazy S}, Lazy.fromL axe L = some L' → LabUniq L →
    (∀ e ∈ entries L, Q e.1) → LabUniq L' ∧ ∀ e ∈ entries L', Q e.1
  copy : ∀ {Q : Nat → Prop} {first : NextL S} {second : Lazy S} {g g' : Comp.Gen Map} {nex : NextL S},
    copyL first second g = some (nex, g') → LabUniq first.laz → LabUniq second →
    (∀ e ∈ entries first.laz, Q e.1) → (∀ e ∈ entries second, Q e.1) →
    LabUniq nex.laz ∧ ∀ e ∈ entries nex.laz, Q e.1
  past : ∀ {cod : Bell → Option Bool} {nex : NextL S} {nom : Nomm} {region : List Nat} {g g' : Comp.Gen Map}
    {nex' : NextL S}, pastL cod nex nom region g = some (nex', g') → LabUniq nex.laz →
    (∀ e ∈ entries nex.laz, e.1 < g.bo) → LabUniq nex'.laz ∧ ∀ e ∈ entries nex'.laz, e.1 < g'.bo

/-- The label clause of a tree. -/
def LL (l : Lazy S) (g : Comp.Gen Map) : Prop := LabUniq l ∧ ∀ e ∈ entries l, e.1 < g.bo

theorem stab_ll (l : Lazy S) : Stab (Map := Map) (LL l) :=
  fun _ _ k h => ⟨h.1, fun e he => Nat.lt_of_lt_of_le (h.2 e he) k.2.1⟩

theorem ll_ofSure (s : Sure S) (g : Comp.Gen Map) : LL (ofSure s) g := lg_ofSure s (jmp0 0) g

/-- An `HT` with one more pre- and postcondition read off the run and `KP`. -/
theorem HT.withR {α : Type} {P P2 : Comp.Gen Map → Prop} {Q Q2 : α → Comp.Gen Map → Prop} {m : CM Map α}
    (h : HT P m Q) (hr : ∀ g x g', P2 g → m g = some (x, g') → KP g g' → Q2 x g') :
    HT (fun g => P g ∧ P2 g) m (fun x g => Q x g ∧ Q2 x g) := by
  constructor
  intro g x g' A p e
  obtain ⟨A1, K1, q1⟩ := h.run g x g' A p.1 e
  exact ⟨A1, K1, q1, hr g x g' p.2 e K1⟩

/-! ## The steps with labels -/

theorem htl_simpleNextL (goal : CGoalL S) :
    HT (fun g => GFL (Map := Map) goal g ∧ LG goal g) (simpleNextL goal : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  unfold simpleNextL
  cases goal with
  | next laz th => exact HT.pure' fun g h => h
  | done =>
    refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
    exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
      HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩
  | pick z o =>
    refine HT.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
    exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun r =>
      HT.bind' (ht_emitJ rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o))) fun o' =>
        HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩

theorem htl_bombL {P : Comp.Gen Map → Prop} (miss : Option Nat) :
    HT P (bombL miss : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  unfold bombL
  exact HT.conseq (HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o =>
    HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩) (fun _ _ => trivial) (fun _ _ h => h)

theorem htl_splitL (L : LabSteps S Map) (nex : NextL S) :
    HT (fun g => Fresh g nex.th ∧ LL nex.laz g) (splitL nex : CM Map (Lazy S × Lazy S × Nat))
      (fun x g => Fresh g (jmp0 x.2.2) ∧ (LL x.1 g ∧ LL x.2.1 g)) := by
  refine HT.withR (ht_splitL nex) fun g x g' hl hm k => ?_
  rcases x with ⟨hed, tel, o⟩
  obtain ⟨a, b, c, d⟩ := L.split (Q := fun n => n < g.bo) hm hl.1 hl.2
  exact ⟨⟨a, fun e he => Nat.lt_of_lt_of_le (c e he) k.2.1⟩, ⟨b, fun e he => Nat.lt_of_lt_of_le (d e he) k.2.1⟩⟩

theorem htl_intoL (L : LabSteps S Map) (nex : NextL S) (axe : Nat) :
    HT (fun g => Fresh g nex.th ∧ LL nex.laz g) (intoL nex axe : CM Map (Lazy S × Lazy S × Nat))
      (fun x g => Fresh g (jmp0 x.2.2) ∧ (LL x.1 g ∧ LL x.2.1 g)) := by
  refine HT.withR (ht_intoL nex axe) fun g x g' hl hm k => ?_
  rcases x with ⟨d, r, o⟩
  obtain ⟨a, b, c, e⟩ := L.into (Q := fun n => n < g.bo) hm hl.1 hl.2
  exact ⟨⟨a, fun y hy => Nat.lt_of_lt_of_le (c y hy) k.2.1⟩, ⟨b, fun y hy => Nat.lt_of_lt_of_le (e y hy) k.2.1⟩⟩

theorem htl_pastL (L : LabSteps S Map) (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm)
    (region : List Nat) :
    HT (fun g => Fresh g nex.th ∧ LL nex.laz g) (pastL cod nex nom region : CM Map (NextL S))
      (fun x g => Fresh g x.th ∧ LL x.laz g) :=
  HT.withR (ht_pastL cod nex nom region) fun _ _ _ hl hm _ => L.past hm hl.1 hl.2

theorem htl_copyL (L : LabSteps S Map) (first : NextL S) (second : Lazy S) :
    HT (fun g => Fresh g first.th ∧ (LL first.laz g ∧ LL second g)) (copyL first second : CM Map (NextL S))
      (fun x g => Fresh g x.th ∧ LL x.laz g) :=
  HT.withR (ht_copyL first second) fun g _ _ hl hm k => by
    obtain ⟨a, b⟩ := L.copy (Q := fun n => n < g.bo) hm hl.1.1 hl.2.1 hl.1.2 hl.2.2
    exact ⟨a, fun e he => Nat.lt_of_lt_of_le (b e he) k.2.1⟩

/-- A run for an `ofSure` goal at a block just emitted. -/
theorem htl_tail {P : Comp.Gen Map → Prop} {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (h : HRL (Map := Map) rp) {b : Blob} (hpar : b.par = []) (hb : ∀ g, P g → ∀ j ∈ finJumps b.fin, Fresh g j)
    (hP : Stab P) (s : Nat → Sure S) (region : List Nat) :
    HT P (do let o ← emit b; rp (CGoalL.next (ofSure (s o)) (jmp0 o)) region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) :=
  HT.bind' (ht_emitJ hpar hb hP) fun _ => HT.weak (h _ _) fun _ h => ⟨h.2, lg_ofSure _ _ _⟩

/-- **The tail of the binary cases with labels**: run `q` for `lq`, `+past`,
run `p` for `lp`, `+copy`. -/
theorem htl_bin (L : LabSteps S Map) (cod : Bell → Option Bool) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p : Nomm) (hp : HRL (Map := Map) rp) (hq : HRL (Map := Map) rq) (lq lp : Lazy S) (th : Jmp)
    (region : List Nat) :
    HT (fun g => Fresh g th ∧ LL lq g ∧ LL lp g) (do
      let nex2 ← rq (CGoalL.next lq th) region
      let nex2 ← pastL cod nex2 p region
      let nex1 ← rp (CGoalL.next lp nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  refine HT.bind' (HT.weak (HT.frame (hq (CGoalL.next lq th) region) (stab_ll lp))
    fun g h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun nex2 => ?_
  refine HT.bind' (HT.weak (HT.frame (htl_pastL L cod nex2 p region) (stab_ll lp))
    fun g h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩) fun nex2' => ?_
  refine HT.bind' (HT.weak (HT.frame (hp (CGoalL.next lp nex2'.th) region) (stab_ll nex2'.laz))
    fun g h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) fun nex1 => ?_
  exact HT.conseq (htl_copyL L nex1 nex2'.laz) (fun g h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h)

/-- **The indirect call with labels.** -/
theorem htl_callL (L : LabSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (sup : Option Nomm) (hp : HRL (Map := Map) rp) (hq : HRL (Map := Map) rq) (goal : CGoalL S)
    (region : List Nat) :
    HT (fun g => GFL (Map := Map) goal g ∧ LG goal g)
      (callL env rp rq p q Option.none sup goal region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  unfold callL
  refine HT.weak (P := GFL (Map := Map) goal) ?_ (fun _ h => h.1)
  refine HT.bind' (ht_simpleNextL _) fun nex => HT.bind' (ht_kerf _) fun a => ?_
  rcases a with ⟨out, pro⟩
  exact HT.bind' (ht_qf QM.re' _) fun _ => HT.bind' (ht_qf QM.re' _) fun _ =>
    HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.weak (htl_bin L env.cod p hp hq _ _ _ _) fun g h => ⟨h.2, ll_ofSure _ _, ll_ofSure _ _⟩

/-! ## The induction -/

/-- **`LabUniq` at run level on `PlainN`**, from `LabSteps`: a `Fresh` goal
whose tree is `LabUniq` with its entries below `bo` gives a `Fresh` result
with the same clause. -/
theorem labRun_plainOf (env : CallEnv) (L : LabSteps S Map) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm),
    HRL (Map := Map) (runLC (S := S) env sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := labRun_plainOf env L p h.1 sup
    have ihq := labRun_plainOf env L q h.2 sup
    unfold runLC
    refine HT.bind' (Q := fun (nex : NextL S) (g : Comp.Gen Map) => Fresh g nex.th ∧ LG nex.goal g)
      (R := fun (goal' : CGoalL S) (g : Comp.Gen Map) => GFL goal' g ∧ LG goal' g) ?_ fun goal' => ?_
    · cases goal with
      | done =>
        refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
        exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
          HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩
      | next laz th => exact HT.pure' fun g h => h
      | pick z o => exact HT.pure' fun g h => h
    · cases goal' with
      | pick z o =>
        exact HT.bind' (HT.conseq (ht_emitJ rfl (js_nil rfl) stab_true) (fun _ _ => trivial) (fun _ _ h => h))
          fun o => HT.weak (htl_bin L env.cod p ihp ihq _ _ _ _) fun g h => ⟨h.2, ll_ofSure _ _, ll_ofSure _ _⟩
      | done => exact HT.fail
      | next laz th =>
        refine HT.bind' (HT.weak (htl_splitL L ⟨laz, th⟩) fun g h => h) fun a => ?_
        rcases a with ⟨hed, tel, o⟩
        refine HT.bind' (HT.weak (HT.frame (htl_pastL L env.cod ⟨hed, jmp0 o⟩ q region) (stab_ll tel))
          fun g h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun nexh => ?_
        exact HT.weak (htl_bin L env.cod p ihp ihq tel nexh.laz nexh.th region) fun g h => ⟨h.1.1, h.2, h.1.2⟩
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLC
    refine HT.ite' _ (htl_bombL _) (HT.bind' (htl_simpleNextL _) fun nex => HT.ite' _ (HT.pure' fun g h => h) ?_)
    cases hf : Lazy.fromL ax nex.laz with
    | none => exact HT.fail
    | some laz => exact HT.pure' fun g h => ⟨h.1, L.fromL (Q := fun n => n < g.bo) hf h.2.1 h.2.2⟩
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLC
    cases goal with
    | done =>
      refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
      exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
        HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩
    | pick z o =>
      exact HT.ite' _ (HT.pure' fun g h => ⟨h.1.1, lg_ofSure _ _ _⟩)
        (HT.ite' _ (HT.pure' fun g h => ⟨h.1.2, lg_ofSure _ _ _⟩) (htl_bombL _))
    | next laz th =>
      exact HT.bind' (HT.weak (ht_medeL _ _ _) fun _ h => h.1) fun o => HT.pure' fun g h => ⟨h, lg_ofSure _ _ _⟩
  | Nomm.n3 p, h, sup, goal, region => by
    have ih := labRun_plainOf env L p h sup
    unfold runLC
    cases goal with
    | pick z o =>
      refine HT.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
      exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun r =>
        htl_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (fun _ => lazyReg r) _
    | done =>
      refine HT.bind' (HT.conseq ht_doneBlocks (fun _ _ => trivial) (fun _ _ h => h)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun r =>
        htl_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)) (fun _ => lazyReg r) _
    | next laz th =>
      refine HT.ite' _ (ih _ _) (HT.bind' (HT.weak (ht_collapse ⟨laz, th⟩) fun _ h => h.1) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact HT.fail
      · refine HT.bind' (HT.conseq (ht_forl r o) (fun _ h => h r o rfl) (fun _ _ h => h)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun r' =>
          htl_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)) (fun _ => lazyReg r') _
  | Nomm.n4 p, h, sup, goal, region => by
    have ih := labRun_plainOf env L p h sup
    unfold runLC
    cases goal with
    | done =>
      refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
      exact HT.bind' (HT.quiet QM.re' stab_true) fun _ => HT.bind' (HT.quiet QM.re' stab_true) fun arg =>
        htl_tail ih rfl (js_nil rfl) stab_true (fun _ => lazyReg arg) _
    | pick z o =>
      refine HT.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
      exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun _ =>
        HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun arg =>
          htl_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (fun _ => lazyReg arg) _
    | next laz th =>
      refine HT.bind' (HT.weak (HT.frame (ht_collapse ⟨laz, th⟩) (stab_fresh th)) fun _ h => ⟨h.1, h.1⟩)
        fun a => ?_
      refine HT.bind' (Q := fun (nex : NextL S) (g : Comp.Gen Map) => Fresh g nex.th ∧ LG nex.goal g)
        (R := fun (x : Nat × Nat) (g : Comp.Gen Map) => Fresh g (jmp0 x.2)) ?_ fun x => ?_
      · cases a with
        | some x => exact HT.pure' fun g h => h.1 x.1 x.2 rfl
        | none =>
          refine HT.bind' (HT.conseq (ht_qf QM.re' th) (fun _ h => h.2) (fun _ _ h => h)) fun r => ?_
          exact HT.ite' _ (HT.pure' fun g h => fresh_jmp0 h) HT.fail
      · rcases x with ⟨pro, th'⟩
        exact HT.bind' (ht_qf QM.re' _) fun arg =>
          htl_tail ih rfl (js_hop fun g h => h) (stab_fresh _) (fun _ => lazyReg arg) _
  | Nomm.n5 p q, h, sup, goal, region => by
    have ihp := labRun_plainOf env L p h.1 sup
    have ihq := labRun_plainOf env L q h.2 sup
    unfold runLC
    refine HT.weak (P := GFL (Map := Map) goal) ?_ (fun _ h => h.1)
    refine HT.bind' (HT.quiet QM.re' (stab_gfl goal)) fun rp => HT.bind' (HT.quiet QM.re' (stab_gfl goal)) fun rq =>
      HT.bind' (R := fun (o : Nat) (g : Comp.Gen Map) => Fresh g (jmp0 o)) ?_ fun o =>
        HT.weak (htl_bin L env.cod p ihp ihq _ _ _ _) fun g h => ⟨h, ll_ofSure _ _, ll_ofSure _ _⟩
    cases goal with
    | pick z o =>
      exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o))) (fun _ h => h)
        (fun _ _ h => h.2)
    | done =>
      refine HT.bind' (HT.conseq ht_doneBlocks (fun _ _ => trivial) (fun _ _ h => h)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)))
        (fun _ h => h) (fun _ _ h => h.2)
    | next laz th =>
      refine HT.bind' (HT.weak (HT.frame (ht_collapse ⟨laz, th⟩) (stab_fresh th)) fun _ h => ⟨h, h⟩) fun a => ?_
      cases a with
      | none =>
        refine HT.ite' _ ?_ HT.fail
        exact HT.conseq (ht_emitJ rfl (js_hop fun g h => fresh_jmp0 h) (stab_fresh th)) (fun _ h => h.2)
          (fun _ _ h => h.2)
      | some x =>
        rcases x with ⟨r, o⟩
        refine HT.bind' (HT.conseq (ht_forl r o) (fun _ h => h.1 r o rfl) (fun _ _ h => h)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)))
          (fun _ h => h) (fun _ _ h => h.2)
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLC
    exact HT.bind' (labRun_plainOf env L q h.2 (some p) goal region) fun nex =>
      HT.weak (labRun_plainOf env L p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := labRun_plainOf env L v h.1 sup
    have ihq := labRun_plainOf env L q h.2 sup
    unfold runLC
    refine HT.bind' (htl_simpleNextL _) fun next => HT.bind' (HT.weak (htl_intoL L _ _) fun g h => h) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine HT.bind' (HT.weak (HT.frame (htl_pastL L env.cod ⟨rec, jmp0 o⟩ v region) (stab_ll don))
      fun g h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) fun nexR => ?_
    exact HT.weak (htl_bin L env.cod q ihq ihv don nexR.laz nexR.th region) fun g h => ⟨h.1.1, h.2, h.1.2⟩
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLC
    exact htl_callL L env p q sup (labRun_plainOf env L p h.1 sup) (labRun_plainOf env L q h.2 sup) goal region

end Raw
end SkaModel
end Formalization
