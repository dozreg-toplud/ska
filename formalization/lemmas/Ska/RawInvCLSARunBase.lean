import lemmas.Ska.RawInvCLSABase
import lemmas.Ska.RawInvCLLabAll

/-!
# Single assignment with calls: the counting frame

README Gaps 14 (b), track D.  `SAB` of the raw blocks (every register
defined at most once in the whole map, no trace op, every jump argument
defined by its own block) is carried through a run by a LINEAR count, with
no precondition on registers: for every register `y`,

  (definitions of `y` after) + (occurrences of `y` in the result's tree)
    ≤ (definitions of `y` before) + (occurrences of `y` in the goal's tree)
      + (1 if `y` was allocated by the run).

The goal's tree holds the registers the code built so far still waits for,
so the count composes along a run with no frame reasoning (parked trees
ride along in the lists).  At the top (`gen0`, `%done`) it gives at most one
definition per register.  The one step that needs a hypothesis is `+copy`:
with two bonds at one label it defines a register twice (checked: under
`goalDup` 144 of the 2,856 `PlainN` runs break the count, under the four
`LabUniq` goals none does), so it asks `LabUniq` of both trees, which the
`HT` frame of `labRun_plain` supplies.

* `sarDc` (the definitions of `y` in the whole map), `sar_dc_put`,
  `sar_dc_emit`, `sar_dc_addOps`, `sarDc_gen0`, `sar_sab` (`SAB` from the
  count at most one).
* `SarSt` (the state clause: `drop`, labels below `bo`, `NoTr`, jump
  arguments defined in their block), `sarR` (the registers of a tree with
  repetitions), `sarG`.
* `SCR ri m ro`: the count for a step with no other hypothesis; `sc_bind`,
  `sc_pure`, `sc_re`, `sc_emit`, `sc_addOps`, `sc_setTag`, `sc_mono`.
* `HC P ri m Q ro`: an `HT` with the count (its hypothesis `P` may be used);
  `HC.bind'`, `HC.frame`, `HC.conseq`, `HC.pure'`, `HC.fail`, `HC.ite'`,
  `HC.of`, `hc_re`, `hc_emit`.
* `SarSteps`: the walks' counts (`+split`, `+into`, `+copy`, `+mede`,
  `+collapse-lazy-atom`, `+kerf`, `+from`), the named hypotheses of the
  induction; `sc_pastL`, `sc_forl`, `sc_doneBlocks`, `sc_simpleNextL`,
  `sc_bombL` are proved.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-! ## Counting the definitions of a map -/

/-- The definitions of `y` in the whole map. -/
def sarDc (bl : Map Blob) (y : Nat) : Nat := (allDefs bl).count y

/-- The definitions of one label (`[]` when it holds no block). -/
def sarF (bl : Map Blob) (o : Nat) : List Nat := ((HoonMap.get bl o).map blockDefs).getD []

theorem sar_allDefs (bl : Map Blob) : allDefs bl = (MapKeys.keys bl).flatMap (sarF bl) := rfl

theorem sar_keys_put (bl : Map Blob) (k : Nat) (b : Blob) :
    (MapKeys.keys (HoonMap.put bl k b)).Perm (k :: (MapKeys.keys bl).erase k) := by
  have nd := MapKeys.nodup bl
  refine (List.perm_ext_iff_of_nodup (MapKeys.nodup _) ?_).mpr fun x => ?_
  · exact List.nodup_cons.mpr ⟨fun h => (List.Nodup.mem_erase_iff nd).mp h |>.1 rfl, nd.erase k⟩
  · rw [MapKeys.mem_keys, List.mem_cons, List.Nodup.mem_erase_iff nd, MapKeys.mem_keys]
    by_cases e : x = k
    · subst e; simp [get_put_self]
    · rw [get_put_ne e]; simp [e]

theorem sar_count_erase (bl : Map Blob) (k : Nat) (y : Nat) :
    (allDefs bl).count y = (sarF bl k).count y + (((MapKeys.keys bl).erase k).flatMap (sarF bl)).count y := by
  by_cases hk : k ∈ MapKeys.keys bl
  · rw [sar_allDefs, ((List.perm_cons_erase hk).flatMap_right (sarF bl)).count_eq y, List.flatMap_cons,
      List.count_append]
  · have hn : HoonMap.get bl k = none := by
      cases h : HoonMap.get bl k with
      | none => rfl
      | some _ => exact absurd ((MapKeys.mem_keys bl k).mpr (by rw [h]; rfl)) hk
    rw [List.erase_of_not_mem hk, sar_allDefs]
    simp [sarF, hn]

/-- **The definitions after a `put`.** -/
theorem sar_dc_put (bl : Map Blob) (k : Nat) (b : Blob) (y : Nat) :
    sarDc (HoonMap.put bl k b) y + (sarF bl k).count y = sarDc bl y + (blockDefs b).count y := by
  unfold sarDc
  have h1 : (allDefs (HoonMap.put bl k b)).count y = (blockDefs b).count y +
      (((MapKeys.keys bl).erase k).flatMap (sarF (HoonMap.put bl k b))).count y := by
    rw [sar_allDefs, ((sar_keys_put bl k b).flatMap_right _).count_eq y, List.flatMap_cons, List.count_append]
    simp [sarF, get_put_self]
  have h2 : ((MapKeys.keys bl).erase k).flatMap (sarF (HoonMap.put bl k b)) =
      ((MapKeys.keys bl).erase k).flatMap (sarF bl) := by
    have hL : ∀ o ∈ (MapKeys.keys bl).erase k, o ≠ k := fun o ho e => by
      subst e; exact (List.Nodup.mem_erase_iff (MapKeys.nodup bl)).mp ho |>.1 rfl
    generalize (MapKeys.keys bl).erase k = L at hL ⊢
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [List.flatMap_cons]
      rw [ih (fun o ho => hL o (List.mem_cons_of_mem _ ho))]
      simp [sarF, get_put_ne (hL a List.mem_cons_self)]
  rw [h1, h2, sar_count_erase bl k y]
  omega

theorem sar_count_le_dc {bl : Map Blob} {o : Nat} {b : Blob} (hb : HoonMap.get bl o = some b) (y : Nat) :
    (blockDefs b).count y ≤ sarDc bl y := by
  unfold sarDc
  rw [sar_count_erase bl o y]
  simp [sarF, hb]

theorem sar_count_two {bl : Map Blob} {o o' : Nat} {b b' : Blob} (hb : HoonMap.get bl o = some b)
    (hb' : HoonMap.get bl o' = some b') (ne : o ≠ o') (y : Nat) :
    (blockDefs b).count y + (blockDefs b').count y ≤ sarDc bl y := by
  unfold sarDc
  rw [sar_count_erase bl o y]
  have hm : o' ∈ (MapKeys.keys bl).erase o :=
    (List.Nodup.mem_erase_iff (MapKeys.nodup bl)).mpr ⟨fun e => ne e.symm, (MapKeys.mem_keys bl o').mpr (by
      rw [hb']; rfl)⟩
  rw [((List.perm_cons_erase hm).flatMap_right (sarF bl)).count_eq y, List.flatMap_cons, List.count_append]
  simp only [sarF, hb, hb', Option.map_some, Option.getD_some]
  omega

theorem sarDc_empty (y : Nat) : sarDc (HoonMap.empty : Map Blob) y = 0 := by
  have : MapKeys.keys (HoonMap.empty : Map Blob) = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    have := (MapKeys.mem_keys _ x).mp hx
    simp [HoonMap.get_empty] at this
  simp [sarDc, sar_allDefs, this]

/-- `emit` at a free label adds the block's definitions. -/
theorem sar_dc_new {bl : Map Blob} {k : Nat} (hk : HoonMap.get bl k = none) (b : Blob) (y : Nat) :
    sarDc (HoonMap.put bl k b) y = sarDc bl y + (blockDefs b).count y := by
  have := sar_dc_put bl k b y
  simp [sarF, hk] at this
  omega

theorem blockDefs_ops (A : List Pole) (b : Blob) :
    blockDefs { b with body := A ++ b.body } = b.par ++ (defsOf A ++ b.body.filterMap aliasDst) := by
  simp [blockDefs, defsOf, List.filterMap_append]

/-- `addOps` at a block adds the ops' definitions. -/
theorem sar_dc_ops {bl : Map Blob} {k : Nat} {b : Blob} (hk : HoonMap.get bl k = some b) (A : List Pole)
    (y : Nat) : sarDc (HoonMap.put bl k { b with body := A ++ b.body }) y = sarDc bl y + (defsOf A).count y := by
  have := sar_dc_put bl k { b with body := A ++ b.body } y
  simp only [sarF, hk, Option.map_some, Option.getD_some, blockDefs_ops, List.count_append] at this
  simp only [blockDefs, List.count_append] at this
  omega

/-! ## The state clause -/

/-- Every jump argument is defined by its own block. -/
def SarArgs (bl : Map Blob) : Prop :=
  ∀ k b j a, HoonMap.get bl k = some b → j ∈ getJmps b.fin → some a ∈ j.args → a ∈ blockDefs b

/-- **The state clause** carried by every step. -/
structure SarSt (g : Comp.Gen Map) : Prop where
  drop : g.drop = false
  lab : ∀ k b, HoonMap.get g.blocks k = some b → k < g.bo
  tr : NoTr g.blocks
  args : SarArgs g.blocks

theorem sarSt_gen0 : SarSt (gen0 : Comp.Gen Map) :=
  ⟨rfl, fun k b h => by simp [gen0, HoonMap.get_empty] at h, fun k b h => by simp [gen0, HoonMap.get_empty] at h,
    fun k b j a h => by simp [gen0, HoonMap.get_empty] at h⟩

theorem sarDc_gen0 (y : Nat) : sarDc (gen0 : Comp.Gen Map).blocks y = 0 := sarDc_empty y

/-- **`SAB` from the count**: at most one definition per register. -/
theorem sar_sab {g : Comp.Gen Map} (hs : SarSt g) (hc : ∀ y, sarDc g.blocks y ≤ 1) : SAB g.blocks where
  nd o b hb := nodup_of_count fun y => Nat.le_trans (sar_count_le_dc hb y) (hc y)
  cr o o' b b' r hb hb' ne hr hr' := by
    have := sar_count_two hb hb' ne r
    have h1 := List.count_pos_iff.mpr hr
    have h2 := List.count_pos_iff.mpr hr'
    have := hc r
    omega
  tr := hs.tr
  args := hs.args

/-! ## The registers of a tree -/

/-- The registers of a lazy tree, with repetitions. -/
def sarR (l : Lazy S) : List Nat := flattenNeed l.sure.ned ++ regsL (entries l)

/-- The registers of a goal's tree. -/
def sarG : CGoalL S → List Nat
  | CGoalL.next laz _ => sarR laz
  | _ => []

theorem sarG_next (laz : Lazy S) (th : Jmp) : sarG (CGoalL.next laz th) = sarR laz := rfl

theorem sarR_ofSure (s : Sure S) : sarR (ofSure s) = flattenNeed s.ned := by
  rw [sarR, entries_ofSure, regsL_nil, List.append_nil]; rfl

theorem cnt_app_le {a b c : List Nat} (h : a ++ b = c) (y : Nat) : a.count y + b.count y ≤ c.count y := by
  rw [← h, List.count_append]; exact Nat.le_refl _

theorem cnt_perm_le {a b c : List Nat} (h : (a ++ b).Perm c) (y : Nat) : a.count y + b.count y ≤ c.count y := by
  rw [← List.count_append]; exact Nat.le_of_eq (h.count_eq y)

/-! ## Steps with no hypothesis -/

/-- **The count for a step**, with no hypothesis but the state clause. -/
def SCR {α : Type} (ri : List Nat) (m : CM Map α) (ro : α → List Nat) : Prop :=
  ∀ g x g', SarSt g → m g = some (x, g') → SarSt g' ∧ g.re ≤ g'.re ∧
    ∀ y, sarDc g'.blocks y + (ro x).count y ≤ sarDc g.blocks y + ri.count y + fr g.re g'.re y

theorem sc_bind {α β : Type} {ri : List Nat} {r1 : α → List Nat} {ro : β → List Nat} {m : CM Map α}
    {f : α → CM Map β} (hm : SCR (Map := Map) ri m r1) (hf : ∀ a, SCR (Map := Map) (r1 a) (f a) ro) :
    SCR (Map := Map) ri (m >>= f) ro := by
  intro g x g' s h
  obtain ⟨a, g1, h1, h2⟩ := bind_some h
  obtain ⟨s1, l1, c1⟩ := hm g a g1 s h1
  obtain ⟨s2, l2, c2⟩ := hf a g1 x g' s1 h2
  refine ⟨s2, Nat.le_trans l1 l2, fun y => ?_⟩
  have := c1 y; have := c2 y; have := fr_add l1 l2 y
  omega

theorem sc_pure {α : Type} {ri : List Nat} {ro : α → List Nat} {a : α} (h : ∀ y, (ro a).count y ≤ ri.count y) :
    SCR (Map := Map) ri (pure a : CM Map α) ro := by
  intro g x g' s e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨s, Nat.le_refl _, fun y => by have := h y; omega⟩

theorem sc_mono {α : Type} {ri ri' : List Nat} {ro ro' : α → List Nat} {m : CM Map α} (h : SCR (Map := Map) ri m ro)
    (hi : ∀ y, ri.count y ≤ ri'.count y) (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y) :
    SCR (Map := Map) ri' m ro' := by
  intro g x g' s e
  obtain ⟨s1, l1, c1⟩ := h g x g' s e
  exact ⟨s1, l1, fun y => by have := c1 y; have := hi y; have := ho x y; omega⟩

theorem sc_re (ri : List Nat) : SCR (Map := Map) ri (re : CM Map Nat) (fun r => ri ++ [r]) := by
  intro g x g' s e
  rw [re_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨⟨s.drop, s.lab, s.tr, s.args⟩, Nat.le_succ _, fun y => ?_⟩
  simp only [List.count_append, List.count_singleton, fr]
  by_cases e : g.re = y
  · subst e; simp; omega
  · have : ¬ (g.re ≤ y ∧ y < g.re + 1) := fun h => e (by omega)
    simp [e, this]

theorem sc_ite {α : Type} {ri : List Nat} {ro : α → List Nat} (c : Prop) [Decidable c] {a b : CM Map α}
    (ha : SCR (Map := Map) ri a ro) (hb : SCR (Map := Map) ri b ro) : SCR (Map := Map) ri (if c then a else b) ro := by
  split
  · exact ha
  · exact hb

theorem sc_fail {α : Type} {ri : List Nat} {ro : α → List Nat} : SCR (Map := Map) ri (fun _ => Option.none : CM Map α) ro :=
  fun _ _ _ _ e => by cases e

/-- **A new block.** -/
theorem sc_emit {b : Blob} {ri ro : List Nat} (htr : ∀ op ∈ b.body, trOp op = false)
    (har : ∀ j ∈ getJmps b.fin, ∀ a, some a ∈ j.args → a ∈ blockDefs b)
    (hc : ∀ y, (blockDefs b).count y + ro.count y ≤ ri.count y) : SCR (Map := Map) ri (emit b) (fun _ => ro) := by
  intro g x g' s e
  rw [emit_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hb : (g.emitted b).blocks = HoonMap.put g.blocks g.bo b := by simp [Gen.emitted, s.drop]
  have hn : HoonMap.get g.blocks g.bo = none := by
    cases h : HoonMap.get g.blocks g.bo with
    | none => rfl
    | some b' => exact absurd (s.lab _ _ h) (Nat.lt_irrefl _)
  refine ⟨⟨by simp [Gen.emitted, s.drop], fun k b' hk => ?_, ?_, fun k b' j a hk hj ha => ?_⟩, Nat.le_refl _,
    fun y => ?_⟩
  · rw [hb] at hk
    rcases get_put_cases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · simp [Gen.emitted]
    · have := s.lab k b' hk; simp [Gen.emitted]; omega
  · rw [hb]; exact noTr_put s.tr htr
  · rw [hb] at hk
    rcases get_put_cases hk with ⟨-, rfl⟩ | ⟨-, hk⟩
    · exact har j hj a ha
    · exact s.args k b' j a hk hj ha
  · rw [hb, sar_dc_new hn]
    have := hc y
    have : fr g.re g.re y = 0 := by simp [fr]
    show _ ≤ _ + _ + fr g.re (g.emitted b).re y
    simp only [Gen.emitted]
    omega

/-- **Ops in front of a block.** -/
theorem sc_addOps {o : Nat} {A : List Pole} {ri ro : List Nat} (htr : ∀ op ∈ A, trOp op = false)
    (hc : ∀ y, (defsOf A).count y + ro.count y ≤ ri.count y) : SCR (Map := Map) ri (addOps o A) (fun _ => ro) := by
  intro g x g' s e
  obtain ⟨b, hb, rfl⟩ := addOps_spec e s.drop
  refine ⟨⟨s.drop, fun k b' hk => ?_, noTr_prepend s.tr hb htr, fun k b' j a hk hj ha => ?_⟩, Nat.le_refl _,
    fun y => ?_⟩
  · rcases get_put_cases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · exact s.lab k b hb
    · exact s.lab k b' hk
  · rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have := s.args k b j a hb hj ha
      rw [blockDefs_ops]
      simp only [blockDefs, List.mem_append] at this ⊢
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact s.args k b' j a hk hj ha
  · show sarDc (HoonMap.put g.blocks o { b with body := A ++ b.body }) y + ro.count y ≤
      sarDc g.blocks y + ri.count y + fr g.re g.re y
    rw [sar_dc_ops hb]
    have := hc y
    have : fr g.re g.re y = 0 := by simp [fr]
    omega

theorem sc_setTag {o : Nat} {region : List Nat} (ri : List Nat) :
    SCR (Map := Map) ri (setTag o region) (fun _ => ri) := by
  intro g x g' s e
  unfold setTag at e
  rw [if_neg (by simp [s.drop])] at e
  cases e
  exact ⟨⟨s.drop, s.lab, s.tr, s.args⟩, Nat.le_refl _, fun y => by simp [fr]⟩

theorem fresh_args {g : Comp.Gen Map} {j : Jmp} (h : Fresh g j) : j.args = [] := by
  obtain ⟨_, _, _, h⟩ := h; exact h

/-! ## Steps with an `HT` hypothesis -/

/-- **An `HT` with the count**; the count may use the precondition. -/
structure HC {α : Type} (P : Comp.Gen Map → Prop) (ri : List Nat) (m : CM Map α) (Q : α → Comp.Gen Map → Prop)
    (ro : α → List Nat) : Prop where
  ht : HT P m Q
  sc : ∀ g x g', ATS g → P g → SarSt g → m g = some (x, g') → SarSt g' ∧ g.re ≤ g'.re ∧
    ∀ y, sarDc g'.blocks y + (ro x).count y ≤ sarDc g.blocks y + ri.count y + fr g.re g'.re y

theorem HC.of {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (h : HT P m Q) (s : SCR (Map := Map) ri m ro) : HC P ri m Q ro :=
  ⟨h, fun g x g' _ _ hs e => s g x g' hs e⟩

theorem HC.ofC {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} {C : Prop} (h : HT P m Q) (hc : ∀ g, P g → C) (s : C → SCR (Map := Map) ri m ro) :
    HC P ri m Q ro :=
  ⟨h, fun g x g' _ p hs e => s (hc g p) g x g' hs e⟩

theorem HC.bind' {α β : Type} {P : Comp.Gen Map → Prop} {R : α → Comp.Gen Map → Prop} {Q : β → Comp.Gen Map → Prop}
    {ri : List Nat} {r1 : α → List Nat} {ro : β → List Nat} {m : CM Map α} {f : α → CM Map β}
    (hm : HC P ri m R r1) (hf : ∀ a, HC (R a) (r1 a) (f a) Q ro) : HC P ri (m >>= f) Q ro where
  ht := HT.bind' hm.ht fun a => (hf a).ht
  sc g x g' A p s h := by
    obtain ⟨a, g1, h1, h2⟩ := bind_some h
    obtain ⟨A1, -, q1⟩ := hm.ht.run g a g1 A p h1
    obtain ⟨s1, l1, c1⟩ := hm.sc g a g1 A p s h1
    obtain ⟨s2, l2, c2⟩ := (hf a).sc g1 x g' A1 q1 s1 h2
    refine ⟨s2, Nat.le_trans l1 l2, fun y => ?_⟩
    have := c1 y; have := c2 y; have := fr_add l1 l2 y
    omega

theorem HC.frame {α : Type} {P F : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (h : HC P ri m Q ro) (hF : Stab F) (L : List Nat) :
    HC (fun g => P g ∧ F g) (ri ++ L) m (fun x g => Q x g ∧ F g) (fun x => ro x ++ L) where
  ht := HT.frame h.ht hF
  sc g x g' A p s e := by
    obtain ⟨s1, l1, c1⟩ := h.sc g x g' A p.1 s e
    exact ⟨s1, l1, fun y => by have := c1 y; simp only [List.count_append]; omega⟩

theorem HC.frame0 {α : Type} {P F : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (h : HC P ri m Q ro) (hF : Stab F) :
    HC (fun g => P g ∧ F g) ri m (fun x g => Q x g ∧ F g) ro where
  ht := HT.frame h.ht hF
  sc g x g' A p s e := h.sc g x g' A p.1 s e

theorem HC.conseq {α : Type} {P P' : Comp.Gen Map → Prop} {ri ri' : List Nat} {m : CM Map α}
    {Q Q' : α → Comp.Gen Map → Prop} {ro ro' : α → List Nat} (h : HC P ri m Q ro) (hp : ∀ g, P' g → P g)
    (hq : ∀ x g, Q x g → Q' x g) (hi : ∀ y, ri.count y ≤ ri'.count y) (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y) :
    HC P' ri' m Q' ro' where
  ht := HT.conseq h.ht hp hq
  sc g x g' A p s e := by
    obtain ⟨s1, l1, c1⟩ := h.sc g x g' A (hp g p) s e
    exact ⟨s1, l1, fun y => by have := c1 y; have := hi y; have := ho x y; omega⟩

theorem HC.weak {α : Type} {P P' : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α}
    {Q : α → Comp.Gen Map → Prop} {ro : α → List Nat} (h : HC P ri m Q ro) (hp : ∀ g, P' g → P g) :
    HC P' ri m Q ro :=
  h.conseq hp (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

theorem HC.pure' {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} {a : α} (h : ∀ g, P g → Q a g) (hc : ∀ y, (ro a).count y ≤ ri.count y) :
    HC P ri (pure a : CM Map α) Q ro :=
  HC.of (HT.pure' h) (sc_pure hc)

theorem HC.fail {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} : HC P ri (fun _ => Option.none : CM Map α) Q ro :=
  HC.of HT.fail sc_fail

theorem HC.ite' {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {Q : α → Comp.Gen Map → Prop}
    {ro : α → List Nat} (c : Prop) [Decidable c] {a b : CM Map α} (ha : HC P ri a Q ro) (hb : HC P ri b Q ro) :
    HC P ri (if c then a else b) Q ro := by
  split
  · exact ha
  · exact hb

theorem hc_re {P : Comp.Gen Map → Prop} (hP : Stab P) (ri : List Nat) :
    HC P ri (re : CM Map Nat) (fun _ => P) (fun r => ri ++ [r]) :=
  HC.of (HT.quiet QM.re' hP) (sc_re ri)

theorem hc_emit {P : Comp.Gen Map → Prop} {b : Blob} {ri ro : List Nat} (hp : b.par = [])
    (hb : ∀ g, P g → ∀ j ∈ finJumps b.fin, Fresh g j) (hP : Stab P) (htr : ∀ op ∈ b.body, trOp op = false)
    (hc : ∀ y, (blockDefs b).count y + ro.count y ≤ ri.count y) :
    HC P ri (emit b : CM Map Nat) (fun o g => P g ∧ Fresh g (jmp0 o)) (fun _ => ro) :=
  HC.ofC (ht_emitJ hp hb hP) (fun g p j hj a ha => by
    rw [getJmps_eq] at hj
    rw [fresh_args (hb g p j hj)] at ha
    cases ha) fun har => sc_emit htr har hc

/-! ## The steps that only emit -/

theorem sc_pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat)
    (ha : nex.th.args = []) :
    SCR (Map := Map) (sarR nex.laz) (pastL cod nex nom region) (fun x => sarR x.laz) := by
  unfold pastL
  refine sc_ite _ (sc_pure fun _ => Nat.le_refl _) ?_
  split
  · exact sc_fail
  · exact sc_pure fun _ => Nat.le_refl _
  · refine sc_bind (sc_emit (ri := sarR nex.laz) (ro := sarR nex.laz) (by simp) (by simp [getJmps, ha])
      (fun y => by simp [blockDefs])) fun o => sc_bind (sc_setTag _) fun _ => sc_pure fun y => ?_
    obtain ⟨s, f, b⟩ := nex.laz
    simp [sarR, entries, bondEntries, forkEntries, regsL_append, regsL_cons, regsL_nil, List.count_append,
      Sure.bunt, flattenNeed]
    omega

theorem sc_forl (r o : Nat) : SCR (Map := Map) [r] (forl r o) (fun _ => []) := by
  unfold forl
  refine sc_bind (sc_re _) fun r0 => sc_bind (sc_re _) fun r1 => ?_
  refine sc_bind (sc_emit (ro := [r0, r1]) (by simp) (by simp [getJmps, jmp0])
    (cnt_app_le (by simp [blockDefs]))) fun barg => ?_
  refine sc_bind (sc_emit (ro := [r1]) (by simp [trOp]) (by simp [getJmps, blockDefs, aliasDst])
    (cnt_app_le (by simp [blockDefs, aliasDst]))) fun if0 => ?_
  exact sc_bind (sc_emit (ro := []) (by simp [trOp]) (by simp [getJmps, blockDefs, aliasDst])
    (cnt_app_le (by simp [blockDefs, aliasDst]))) fun if1 => sc_pure fun _ => by simp

theorem sc_doneBlocks (ri : List Nat) : SCR (Map := Map) ri doneBlocks (fun _ => ri) := by
  unfold doneBlocks
  refine sc_bind (sc_re _) fun r0 => sc_bind (sc_re _) fun r1 => ?_
  refine sc_bind (sc_emit (ro := ri ++ [r1]) (by simp [trOp]) (by simp [getJmps])
    (cnt_perm_le (by simp [blockDefs, aliasDst]; exact List.perm_middle.symm))) fun o0 => ?_
  exact sc_bind (sc_emit (ro := ri) (by simp [trOp]) (by simp [getJmps])
    (cnt_perm_le (by simp [blockDefs, aliasDst]; exact (List.perm_append_comm : ([r1] ++ ri).Perm _)))) fun o1 =>
    sc_pure fun _ => Nat.le_refl _

/-- The goal's jumps pass no argument (`Fresh` gives it). -/
def SarGA : CGoalL S → Prop
  | CGoalL.next _ th => th.args = []
  | CGoalL.pick z o => z.args = [] ∧ o.args = []
  | CGoalL.done => True

theorem sarGA_of {goal : CGoalL S} {g : Comp.Gen Map} (h : GFL goal g) : SarGA goal := by
  cases goal with
  | next laz th => obtain ⟨_, _, _, h⟩ := h; exact h
  | pick z o => obtain ⟨⟨_, _, _, h1⟩, ⟨_, _, _, h2⟩⟩ := h; exact ⟨h1, h2⟩
  | done => trivial

theorem sc_simpleNextL (goal : CGoalL S) (ha : SarGA goal) :
    SCR (Map := Map) (sarG goal) (simpleNextL goal) (fun x => sarR x.laz) := by
  unfold simpleNextL
  cases goal with
  | next laz th => exact sc_pure fun _ => Nat.le_refl _
  | done =>
    refine sc_bind (sc_re _) fun r => sc_bind (sc_emit (ro := [r]) (by simp) (by simp [getJmps])
      (cnt_app_le (by simp [blockDefs, sarG]))) fun o => sc_pure fun y => ?_
    simp [sarR_ofSure, flattenNeed]
  | pick z o =>
    refine sc_bind (sc_re _) fun r => sc_bind (sc_emit (ro := [r]) (by simp)
      (by simp only [SarGA] at ha; simp [getJmps, ha.1, ha.2]) (cnt_app_le (by simp [blockDefs, sarG])))
      fun o' => sc_pure fun y => ?_
    simp [sarR_ofSure, flattenNeed]

theorem sc_bombL (ri : List Nat) (miss : Option Nat) :
    SCR (Map := Map) ri (bombL miss : CM Map (NextL S)) (fun x => sarR x.laz) := by
  unfold bombL
  refine sc_bind (sc_emit (ro := []) (by simp) (by simp [getJmps]) fun y => by simp [blockDefs]) fun o =>
    sc_pure fun y => ?_
  simp [sarR_ofSure, Sure.bunt, flattenNeed]

/-! ## The walks: the named hypotheses -/

/-- **The counts of the walks**, the open steps of the induction. -/
structure SarSteps (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] [MapKeys Map] :
    Prop where
  split : ∀ (nex : NextL S), nex.th.args = [] → SCR (Map := Map) (sarR nex.laz) (splitL nex) (fun x => sarR x.1 ++ sarR x.2.1)
  into : ∀ (nex : NextL S) (axe : Nat), nex.th.args = [] →
    SCR (Map := Map) (sarR nex.laz) (intoL nex axe) (fun x => sarR x.1 ++ sarR x.2.1)
  copy : ∀ (first : NextL S) (second : Lazy S), first.th.args = [] → LabUniq first.laz → LabUniq second →
    SCR (Map := Map) (sarR first.laz ++ sarR second) (copyL first second) (fun x => sarR x.laz)
  mede : ∀ (th : Jmp) (k : Noun) (laz : Lazy S), th.args = [] → SCR (Map := Map) (sarR laz) (medeL th k laz) (fun _ => [])
  collapse : ∀ (nex : NextL S), SCR (Map := Map) (sarR nex.laz) (collapseLazyAtomL nex)
    (fun a => match a with | some x => [x.1] | Option.none => [])
  kerf : ∀ (nex : NextL S), nex.th.args = [] → SCR (Map := Map) (sarR nex.laz) (kerf nex) (fun x => [x.2])
  fromL : ∀ (ax : Nat) (l l' : Lazy S), Lazy.fromL ax l = some l' → ∀ y, (sarR l').count y ≤ (sarR l).count y

end Raw
end SkaModel
end Formalization
