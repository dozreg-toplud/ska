import lemmas.Ska.RawInvCLKUBase

/-!
# The mid-run count with no state: the induction on `PlainN`

README Gaps 14 (b), track D.  `kuRun_plainOf`: every run of `runLC` on
`PlainN` meets `KURun` (`RawInvCLKUBase.lean`: from an `LG` goal an `LG`
result, `re` and `bo` grow, and the count from `sarG goal` to the result's
tree), from the local steps `KUSteps`, with no precondition on the state.
The skeleton is that of `labRun_plainOf` (`RawInvCLLabRun.lean`) with the
triple `kurT` in place of `HT`.

* `kurT P ri m Q ro`: from a state meeting `P`, a run of `m` grows `re` and
  `bo`, has the count from `ri` to `ro x`, and ends in `Q x`; `kur_bind`,
  `kur_pure`, `kur_ku`, `kur_rb`, `kur_conseq`, `kur_frame`, `kur_fail`,
  `kur_ite`; `kurR rp` (`KURun` as a triple, `kur_ofR`, `kur_toR`).
* The steps: `kur_simpleNextL`, `kur_bombL`, `kur_splitL`, `kur_intoL`,
  `kur_pastL`, `kur_copyL`, `kur_tail` (a block, then a sub-run for an
  `ofSure` goal), `kur_bin` (run q, `+past`, run p, `+copy`), `kur_callL`.
* **`kuRun_plainOf`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The triple -/

/-- **A step with the count and a post-condition**, from a state meeting
`P`. -/
def kurT {α : Type} (P : Comp.Gen Map → Prop) (ri : List Nat) (m : CM Map α) (Q : α → Comp.Gen Map → Prop)
    (ro : α → List Nat) : Prop :=
  ∀ (g : Comp.Gen Map) x g', P g → m g = some (x, g') → g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧
    (∀ y, (ro x).count y ≤ ri.count y + fr g.re g'.re y) ∧ Q x g'

theorem kur_bind {α β : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α}
    {R : α → Comp.Gen Map → Prop} {r1 : α → List Nat} {f : α → CM Map β} {Q : β → Comp.Gen Map → Prop}
    {ro : β → List Nat} (hm : kurT P ri m R r1) (hf : ∀ a, kurT (R a) (r1 a) (f a) Q ro) :
    kurT P ri (m >>= f) Q ro := by
  intro g x g' p h
  obtain ⟨a, g1, h1, h2⟩ := bind_some h
  obtain ⟨l1, b1, c1, q1⟩ := hm g a g1 p h1
  obtain ⟨l2, b2, c2, q2⟩ := hf a g1 x g' q1 h2
  refine ⟨Nat.le_trans l1 l2, Nat.le_trans b1 b2, fun y => ?_, q2⟩
  have := c1 y; have := c2 y; have := fr_add l1 l2 y
  omega

theorem kur_pure {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} {a : α} (hq : ∀ g, P g → Q a g) (hc : ∀ y, (ro a).count y ≤ ri.count y) :
    kurT P ri (pure a : CM Map α) Q ro := by
  intro g x g' p e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Nat.le_refl _, Nat.le_refl _, fun y => by have := hc y; omega, hq g p⟩

theorem kur_ku {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (h : KUC (Map := Map) ri m ro)
    (hq : ∀ g x g', P g → m g = some (x, g') → g.bo ≤ g'.bo → Q x g') : kurT P ri m Q ro := by
  intro g x g' p e
  obtain ⟨l, b, c⟩ := h g x g' e
  exact ⟨l, b, c, hq g x g' p e b⟩

theorem kur_rb {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (h : RB (Map := Map) m) (hc : ∀ x y, (ro x).count y ≤ ri.count y)
    (hq : ∀ g x g', P g → m g = some (x, g') → g.bo ≤ g'.bo → Q x g') : kurT P ri m Q ro := by
  intro g x g' p e
  obtain ⟨l, b⟩ := h g x g' e
  exact ⟨l, b, fun y => by have := hc x y; omega, hq g x g' p e b⟩

theorem kur_conseq {α : Type} {P P' : Comp.Gen Map → Prop} {ri ri' : List Nat} {m : CM Map α}
    {Q Q' : α → Comp.Gen Map → Prop} {ro ro' : α → List Nat} (h : kurT P ri m Q ro) (hp : ∀ g, P' g → P g)
    (hq : ∀ x g, Q x g → Q' x g) (hi : ∀ y, ri.count y ≤ ri'.count y) (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y) :
    kurT P' ri' m Q' ro' := by
  intro g x g' p e
  obtain ⟨l, b, c, q⟩ := h g x g' (hp g p) e
  exact ⟨l, b, fun y => by have := c y; have := hi y; have := ho x y; omega, hq x g' q⟩

theorem kur_frame {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (h : kurT P ri m Q ro) (extra : List Nat) {F : Comp.Gen Map → Prop}
    (hF : ∀ g g' : Comp.Gen Map, g.bo ≤ g'.bo → F g → F g') :
    kurT (fun g => P g ∧ F g) (ri ++ extra) m (fun x g => Q x g ∧ F g) (fun x => ro x ++ extra) := by
  intro g x g' p e
  obtain ⟨l, b, c, q⟩ := h g x g' p.1 e
  refine ⟨l, b, fun y => ?_, q, hF g g' b p.2⟩
  have := c y
  simp only [List.count_append]
  omega

theorem kur_fail {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} : kurT P ri (fun _ => Option.none : CM Map α) Q ro :=
  fun _ _ _ _ e => by cases e

theorem kur_ite {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (c : Prop) [Decidable c] {a b : CM Map α} (ha : kurT P ri a Q ro) (hb : kurT P ri b Q ro) :
    kurT P ri (if c then a else b) Q ro := by
  split
  · exact ha
  · exact hb

/-- `KURun` as a triple. -/
abbrev kurR (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (goal : CGoalL S) region, kurT (Map := Map) (LG goal) (sarG goal) (rp goal region)
    (fun x g => LG x.goal g) (fun x => sarR x.laz)

theorem kur_ofR {rp : CGoalL S → List Nat → CM Map (NextL S)} (h : KURun (Map := Map) rp) : kurR (Map := Map) rp :=
  fun goal region g x g' p e => by
    obtain ⟨a, b, c, d⟩ := h goal region g g' x p e
    exact ⟨b, c, d, a⟩

theorem kur_toR {rp : CGoalL S → List Nat → CM Map (NextL S)} (h : kurR (Map := Map) rp) : KURun (Map := Map) rp :=
  fun goal region g g' x p e => by
    obtain ⟨a, b, c, d⟩ := h goal region g x g' p e
    exact ⟨d, a, b, c⟩

/-! ## Small facts -/

theorem kur_ll_up {l : Lazy S} : ∀ g g' : Comp.Gen Map, g.bo ≤ g'.bo → LL l g → LL l g' :=
  fun _ _ k h => ⟨h.1, fun e he => Nat.lt_of_lt_of_le (h.2 e he) k⟩

theorem kur_sarR_this (r : Nat) : sarR (ofSure (⟨Need.this r, HoonSet.empty⟩ : Sure S)) = [r] := by
  rw [sarR_ofSure]; rfl

theorem kur_sarR_reg (r : Nat) : sarR (ofSure (lazyReg (S := S) r)) = [r] := by
  rw [sarR_ofSure]; rfl

theorem kur_sarR_bunt : sarR (ofSure (Sure.bunt : Sure S)) = [] := by
  rw [sarR_ofSure]; rfl

theorem kur_cnt0 (ri : List Nat) (y : Nat) : ([] : List Nat).count y ≤ ri.count y := by simp

/-! ## The steps -/

theorem kur_simpleNextL (goal : CGoalL S) :
    kurT (Map := Map) (LG goal) (sarG goal) (simpleNextL goal) (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  unfold simpleNextL
  cases goal with
  | next laz th => exact kur_pure (fun g h => h) (fun y => Nat.le_refl _)
  | done =>
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
    refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
    rw [kur_sarR_this]; simp
  | pick z o =>
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
    refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
    rw [kur_sarR_this]; simp [sarG]

theorem kur_bombL {P : Comp.Gen Map → Prop} (ri : List Nat) (miss : Option Nat) :
    kurT (Map := Map) P ri (bombL miss : CM Map (NextL S)) (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  unfold bombL
  refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit ri _) fun _ _ _ _ _ _ => trivial) fun o => ?_
  refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
  rw [kur_sarR_bunt]; exact kur_cnt0 ri y

theorem kur_splitL (St : KUSteps S Map) (nex : NextL S) :
    kurT (Map := Map) (LL nex.laz) (sarR nex.laz) (splitL nex) (fun x g => LL x.1 g ∧ LL x.2.1 g)
      (fun x => sarR x.1 ++ sarR x.2.1) := by
  refine kur_ku (St.split nex) fun g x g' hl e k => ?_
  rcases x with ⟨hed, tel, o⟩
  obtain ⟨a, b, c, d⟩ := lab_splitL (Q := fun n => n < g.bo) e hl.1 hl.2
  exact ⟨⟨a, fun y hy => Nat.lt_of_lt_of_le (c y hy) k⟩, ⟨b, fun y hy => Nat.lt_of_lt_of_le (d y hy) k⟩⟩

theorem kur_intoL (St : KUSteps S Map) (nex : NextL S) (axe : Nat) :
    kurT (Map := Map) (LL nex.laz) (sarR nex.laz) (intoL nex axe) (fun x g => LL x.1 g ∧ LL x.2.1 g)
      (fun x => sarR x.1 ++ sarR x.2.1) := by
  refine kur_ku (St.into nex axe) fun g x g' hl e k => ?_
  rcases x with ⟨d, r, o⟩
  obtain ⟨a, b, c, f⟩ := lab_intoL (Q := fun n => n < g.bo) e hl.1 hl.2
  exact ⟨⟨a, fun y hy => Nat.lt_of_lt_of_le (c y hy) k⟩, ⟨b, fun y hy => Nat.lt_of_lt_of_le (f y hy) k⟩⟩

theorem kur_pastL (St : KUSteps S Map) (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    kurT (Map := Map) (LL nex.laz) (sarR nex.laz) (pastL cod nex nom region) (fun x g => LL x.laz g)
      (fun x => sarR x.laz) :=
  kur_ku (St.past cod nex nom region) fun g x g' hl e k => lab_pastL e hl.1 hl.2

theorem kur_copyL (St : KUSteps S Map) (first : NextL S) (second : Lazy S) :
    kurT (Map := Map) (fun g => LL first.laz g ∧ LL second g) (sarR first.laz ++ sarR second) (copyL first second)
      (fun x g => LG x.goal g) (fun x => sarR x.laz) := by
  intro g x g' p e
  obtain ⟨l, b, c⟩ := St.copy first second p.1.1 p.2.1 g x g' e
  obtain ⟨a, b'⟩ := lab_copyL (Q := fun n => n < g.bo) e p.1.1 p.2.1 p.1.2 p.2.2
  exact ⟨l, b, c, a, fun y hy => Nat.lt_of_lt_of_le (b' y hy) b⟩

/-- **A block, then a sub-run for an `ofSure` goal at it.** -/
theorem kur_tail {P : Comp.Gen Map → Prop} {ri : List Nat} {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (h : kurR (Map := Map) rp) (b : Blob) (s : Nat → Sure S) (region : List Nat)
    (hc : ∀ o y, (flattenNeed (s o).ned).count y ≤ ri.count y) :
    kurT (Map := Map) P ri (do let o ← emit b; rp (CGoalL.next (ofSure (s o)) (jmp0 o)) region)
      (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit ri b) fun _ _ _ _ _ _ => trivial) fun o => ?_
  refine kur_conseq (h _ region) (fun g _ => lg_ofSure _ _ _) (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
  rw [sarG_next, sarR_ofSure]; exact hc o y

/-- **The tail of the binary cases**: run `q` for `lq`, `+past`, run `p`
for `lp`, `+copy`. -/
theorem kur_bin (St : KUSteps S Map) (cod : Bell → Option Bool) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p : Nomm) (hp : kurR (Map := Map) rp) (hq : kurR (Map := Map) rq) (lq lp : Lazy S) (th : Jmp)
    (region : List Nat) :
    kurT (Map := Map) (fun g => LL lq g ∧ LL lp g) (sarR lq ++ sarR lp) (do
      let nex2 ← rq (CGoalL.next lq th) region
      let nex2 ← pastL cod nex2 p region
      let nex1 ← rp (CGoalL.next lp nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  refine kur_bind (kur_frame (hq (CGoalL.next lq th) region) (sarR lp) (F := LL lp) kur_ll_up) fun nex2 => ?_
  refine kur_bind (kur_conseq (kur_frame (kur_pastL St cod nex2 p region) (sarR lp) (F := LL lp) kur_ll_up)
    (fun g h => h) (fun _ _ h => h) (fun y => Nat.le_refl _) (fun _ _ => Nat.le_refl _)) fun nex2' => ?_
  refine kur_bind (kur_conseq (kur_frame (hp (CGoalL.next lp nex2'.th) region) (sarR nex2'.laz)
    (F := LL nex2'.laz) kur_ll_up) (fun g h => ⟨h.2, h.1⟩) (fun _ _ h => h) (fun y => by
      simp only [sarG_next, List.count_append]; omega) (fun _ _ => Nat.le_refl _)) fun nex1 => ?_
  exact kur_copyL St nex1 nex2'.laz

/-- **The indirect call.** -/
theorem kur_callL (St : KUSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (sup : Option Nomm) (hp : kurR (Map := Map) rp) (hq : kurR (Map := Map) rq) (goal : CGoalL S)
    (region : List Nat) :
    kurT (Map := Map) (LG goal) (sarG goal) (callL env rp rq p q Option.none sup goal region)
      (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  unfold callL
  refine kur_bind (kur_simpleNextL goal) fun nex => ?_
  refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.kerf nex) (fun _ y => kur_cnt0 _ y)
    fun _ _ _ _ _ _ => trivial) fun a => ?_
  rcases a with ⟨out, pro⟩
  refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun rSub => ?_
  refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun rFol => ?_
  refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
  refine kur_conseq (kur_bin St env.cod p hp hq _ _ _ region) (fun g _ => ⟨ll_ofSure _ _, ll_ofSure _ _⟩)
    (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
  rw [kur_sarR_reg, kur_sarR_reg]; simp only [List.count_append]; omega

/-! ## The induction -/

theorem kur_run (env : CallEnv) (St : KUSteps S Map) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm),
    kurR (Map := Map) (runLC (S := S) env sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := kur_run env St p h.1 sup
    have ihq := kur_run env St q h.2 sup
    unfold runLC
    refine kur_bind (R := fun (goal' : CGoalL S) (g : Comp.Gen Map) => LG goal' g) (r1 := fun goal' => sarG goal')
      ?_ fun goal' => ?_
    · cases goal with
      | done =>
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
        refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
        rw [sarG_next, kur_sarR_reg]; simp
      | next laz th => exact kur_pure (fun g h => h) (fun y => Nat.le_refl _)
      | pick z o => exact kur_pure (fun g h => h) (fun y => Nat.le_refl _)
    · cases goal' with
      | pick z o =>
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
        refine kur_conseq (kur_bin St env.cod p ihp ihq _ _ _ region) (fun g _ => ⟨ll_ofSure _ _, ll_ofSure _ _⟩)
          (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
        rw [kur_sarR_bunt]; exact kur_cnt0 _ y
      | done => exact kur_fail
      | next laz th =>
        refine kur_bind (kur_splitL St ⟨laz, th⟩) fun a => ?_
        rcases a with ⟨hed, tel, o⟩
        refine kur_bind (kur_frame (kur_pastL St env.cod ⟨hed, jmp0 o⟩ q region) (sarR tel) (F := LL tel)
          kur_ll_up) fun nexh => ?_
        exact kur_conseq (kur_bin St env.cod p ihp ihq tel nexh.laz nexh.th region) (fun g h => ⟨h.2, h.1⟩)
          (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega) (fun _ _ => Nat.le_refl _)
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLC
    refine kur_ite _ (kur_bombL _ _) (kur_bind (kur_simpleNextL _) fun nex => kur_ite _
      (kur_pure (fun g h => h) (fun y => Nat.le_refl _)) ?_)
    cases hf : Lazy.fromL ax nex.laz with
    | none => exact kur_fail
    | some laz =>
      refine kur_pure (fun g h => lab_fromL (Q := fun n => n < g.bo) hf h.1 h.2) fun y => ?_
      rw [sar_fromL hf]; exact Nat.le_refl _
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLC
    cases goal with
    | done =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
      refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
      rw [kur_sarR_bunt]; exact kur_cnt0 _ y
    | pick z o =>
      refine kur_ite _ (kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_)
        (kur_ite _ (kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_) (kur_bombL _ _))
      · rw [kur_sarR_bunt]; exact kur_cnt0 _ y
      · rw [kur_sarR_bunt]; exact kur_cnt0 _ y
    | next laz th =>
      refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.mede th k laz) (fun _ y => kur_cnt0 _ y)
        fun _ _ _ _ _ _ => trivial) fun o => ?_
      refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
      rw [kur_sarR_bunt]; exact Nat.le_refl _
  | Nomm.n3 p, h, sup, goal, region => by
    have ih := kur_run env St p h sup
    unfold runLC
    cases goal with
    | pick z o =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
      exact kur_tail ih _ (fun _ => lazyReg r) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | done =>
      refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) St.doneBlocks (fun _ y => kur_cnt0 _ y)
        fun _ _ _ _ _ _ => trivial) fun a => ?_
      rcases a with ⟨o0, o1⟩
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
      exact kur_tail ih _ (fun _ => lazyReg r) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | next laz th =>
      refine kur_ite _ (ih _ _) (kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => [])
        (St.collapse ⟨laz, th⟩) (fun _ y => kur_cnt0 _ y) fun _ _ _ _ _ _ => trivial) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact kur_fail
      · refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.forl r o) (fun _ y => kur_cnt0 _ y)
          fun _ _ _ _ _ _ => trivial) fun x => ?_
        rcases x with ⟨z, o'⟩
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r' => ?_
        exact kur_tail ih _ (fun _ => lazyReg r') region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
  | Nomm.n4 p, h, sup, goal, region => by
    have ih := kur_run env St p h sup
    unfold runLC
    cases goal with
    | done =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun _ => ?_
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun arg => ?_
      exact kur_tail ih _ (fun _ => lazyReg arg) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | pick z o =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun _ => ?_
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun arg => ?_
      exact kur_tail ih _ (fun _ => lazyReg arg) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | next laz th =>
      refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.collapse ⟨laz, th⟩)
        (fun _ y => kur_cnt0 _ y) fun _ _ _ _ _ _ => trivial) fun a => ?_
      refine kur_bind (R := fun _ _ => True) (r1 := fun _ => []) ?_ fun x => ?_
      · cases a with
        | some x => exact kur_pure (fun _ _ => trivial) (fun y => Nat.le_refl _)
        | none =>
          refine kur_bind (kur_ku (Q := fun _ _ => True) (ro := fun _ => []) (ku_mono (ku_re []) (fun y => Nat.le_refl _)
            (fun _ y => by simp)) fun _ _ _ _ _ _ => trivial) fun r => ?_
          exact kur_ite _ (kur_pure (fun _ _ => trivial) (fun y => Nat.le_refl _)) kur_fail
      · rcases x with ⟨pro, th'⟩
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun arg => ?_
        exact kur_tail ih _ (fun _ => lazyReg arg) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
  | Nomm.n5 p q, h, sup, goal, region => by
    have ihp := kur_run env St p h.1 sup
    have ihq := kur_run env St q h.2 sup
    unfold runLC
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun rp => ?_
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun rq => ?_
    refine kur_bind (R := fun _ _ => True) (r1 := fun _ => [rq] ++ [rp]) ?_ fun o => ?_
    · have hc : ∀ (x : Nat) y, ([rq] ++ [rp]).count y ≤ (sarG goal ++ [rp] ++ [rq]).count y := fun _ y => by
        simp only [List.count_append]; omega
      cases goal with
      | pick z o => exact kur_rb (rb_emit _) hc fun _ _ _ _ _ _ => trivial
      | done =>
        exact kur_rb (rb_bind St.doneBlocks fun a => match a with | (o0, o1) => rb_emit _) hc
          fun _ _ _ _ _ _ => trivial
      | next laz th =>
        refine kur_rb (rb_bind (St.collapse ⟨laz, th⟩) fun a => ?_) hc fun _ _ _ _ _ _ => trivial
        cases a with
        | none => exact rb_ite _ (rb_emit _) rb_fail
        | some x =>
          rcases x with ⟨r, o⟩
          exact rb_bind (St.forl r o) fun x => match x with | (z, o') => rb_emit _
    · refine kur_conseq (kur_bin St env.cod p ihp ihq _ _ _ region) (fun g _ => ⟨ll_ofSure _ _, ll_ofSure _ _⟩)
        (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
      rw [kur_sarR_reg, kur_sarR_reg]; exact Nat.le_refl _
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLC
    exact kur_bind (kur_run env St q h.2 (some p) goal region) fun nex =>
      kur_conseq (kur_run env St p h.1 sup nex.goal region) (fun _ h => h) (fun _ _ h => h)
        (fun y => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := kur_run env St v h.1 sup
    have ihq := kur_run env St q h.2 sup
    unfold runLC
    refine kur_bind (kur_simpleNextL _) fun next => ?_
    refine kur_bind (kur_conseq (kur_intoL St next a) (fun _ h => h) (fun _ _ h => h) (fun y => Nat.le_refl _)
      (fun _ _ => Nat.le_refl _)) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine kur_bind (kur_conseq (kur_frame (kur_pastL St env.cod ⟨rec, jmp0 o⟩ v region) (sarR don) (F := LL don)
      kur_ll_up) (fun g h => ⟨h.2, h.1⟩) (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega)
      (fun _ _ => Nat.le_refl _)) fun nexR => ?_
    exact kur_conseq (kur_bin St env.cod q ihq ihv don nexR.laz nexR.th region) (fun g h => ⟨h.2, h.1⟩)
      (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega) (fun _ _ => Nat.le_refl _)
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLC
    exact kur_callL St env p q sup (kur_run env St p h.1 sup) (kur_run env St q h.2 sup) goal region
  | Nomm.n2 _ _ (some _), h, _, _, _ => h.elim
  | Nomm.n6 _ _ _, h, _, _, _ => h.elim
  | Nomm.n11s _ _ _, h, _, _, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _, _, _ => h.elim
  | Nomm.n12 _ _, h, _, _, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _, _, _ => h.elim

/-- **Every run of `runLC` on `PlainN` meets `KURun`**, from the local
steps `KUSteps`, with no precondition on the state. -/
theorem kuRun_plainOf (env : CallEnv) (St : KUSteps S Map) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm),
    KURun (runLC (S := S) (Map := Map) env sup nm) :=
  fun nm h sup => kur_toR (kur_run env St nm h sup)

end Raw
end SkaModel
end Formalization
