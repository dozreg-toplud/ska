import lemmas.Ska.RawInvCLCopySpec

/-!
# The run-level liveness with calls: the `IL` half of `+copy`

README Gaps 14 (b), track D.  The first conjunct of `CopySpecL`
(`RawInvCLCopy.lean`): the merged goal holds `IL`.

* `regsL L`: the registers of the sure needs of the entries `L`, as a list
  with repetitions; `fr a b y`: `1` when `y` is fresh in `[a, b)`.
* `cn_count`: the registers of the merged need of `+copy-need-make-ops` and
  the destinations of its moves, counted, are at most those of the two needs
  and one per fresh register.
* `CR La Lc g g'`: the same count for a merge of the entries `La` into the
  entries `Lc`, the destinations `D` bounding what the merge defines;
  **`cr_copyLazyL`** (mutual with `cr_mergeForks`, `cr_mergeBonds`), when
  both trees are `LabUniq` (each entry of `second` is merged at most once).
* So when the registers of the inputs are pairwise distinct (`IL` of both
  goals, `TreesApart`), those of the result and the destinations are
  (`nodup_of_count`): the merged needs are `Distinct`, pairwise apart and
  defined by no move.
* **`copyL_il`**, **`copyL_spec : CopySpecL S Map`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Counting registers -/

/-- The registers of the sure needs of a list of entries. -/
def regsL (L : List (Nat × Lazy S)) : List Nat := L.flatMap fun e => flattenNeed e.2.sure.ned

/-- `1` when `y` is fresh in `[a, b)`. -/
def fr (a b y : Nat) : Nat := if a ≤ y ∧ y < b then 1 else 0

theorem fr_add {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) (y : Nat) : fr a b y + fr b c y = fr a c y := by
  unfold fr; split <;> split <;> split <;> omega

theorem fr_le_one (a b y : Nat) : fr a b y ≤ 1 := by unfold fr; split <;> omega

theorem fr_mono {a b c : Nat} (hbc : b ≤ c) (y : Nat) : fr a b y ≤ fr a c y := by
  unfold fr; split <;> split <;> omega

theorem fr_pos {a b y : Nat} (h : 1 ≤ fr a b y) : a ≤ y ∧ y < b := by
  unfold fr at h; split at h
  · assumption
  · omega

theorem regsL_append (L1 L2 : List (Nat × Lazy S)) : regsL (L1 ++ L2) = regsL L1 ++ regsL L2 := by
  simp [regsL, List.flatMap_append]

theorem regsL_cons (e : Nat × Lazy S) (L : List (Nat × Lazy S)) :
    regsL (e :: L) = flattenNeed e.2.sure.ned ++ regsL L := by
  simp [regsL]

theorem regsL_nil : regsL ([] : List (Nat × Lazy S)) = [] := rfl

theorem mem_regsL {L : List (Nat × Lazy S)} {y : Nat} : y ∈ regsL L ↔ ∃ e ∈ L, NMem e.2.sure.ned y := by
  simp [regsL, List.mem_flatMap, mem_flatten]

theorem regsL_perm {L L' : List (Nat × Lazy S)} (h : L.Perm L') : (regsL L).Perm (regsL L') :=
  List.Perm.flatMap_right _ h

theorem count_le_one_of_nodup : ∀ {l : List Nat}, l.Nodup → ∀ y, List.count y l ≤ 1
  | [], _, y => by simp
  | x :: l, h, y => by
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp h
    rw [List.count_cons]
    by_cases e : x = y
    · subst e
      have : List.count x l = 0 := List.count_eq_zero.mpr hx
      simp [this]
    · have := count_le_one_of_nodup hl y
      simp [e, this]

theorem nodup_of_count : ∀ {l : List Nat}, (∀ y, List.count y l ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_count fun y => ?_⟩
    · have h1 := h x
      rw [List.count_cons] at h1
      have : 0 < List.count x l := List.count_pos_iff.mpr hm
      simp at h1; omega
    · have h1 := h y
      have := List.count_le_count_cons (a := y) (b := x) (l := l)
      omega

/-- A need whose flattening has no repetition is `Distinct`. -/
theorem distinct_of_nodup : ∀ {n : Need}, (flattenNeed n).Nodup → Distinct n
  | Need.none, _ => trivial
  | Need.this _, _ => trivial
  | Need.pair p q, h => by
    simp only [flattenNeed] at h
    obtain ⟨hp, hq, hd⟩ := List.nodup_append.mp h
    exact ⟨distinct_of_nodup hp, distinct_of_nodup hq, fun x hx hx' =>
      hd x ((mem_flatten p x).mpr hx) x ((mem_flatten q x).mpr hx') rfl⟩
  | Need.both r p q, h => by
    simp only [flattenNeed] at h
    obtain ⟨hr, h⟩ := List.nodup_cons.mp h
    obtain ⟨hp, hq, hd⟩ := List.nodup_append.mp h
    exact ⟨distinct_of_nodup hp, distinct_of_nodup hq, fun x hx hx' =>
      hd x ((mem_flatten p x).mpr hx) x ((mem_flatten q x).mpr hx') rfl,
      fun hm => hr (List.mem_append_left _ ((mem_flatten p r).mpr hm)),
      fun hm => hr (List.mem_append_right _ ((mem_flatten q r).mpr hm))⟩

/-- The registers of entries pairwise apart and each distinct have no
repetition, and conversely. -/
theorem nodup_regsL_iff : ∀ {L : List (Nat × Lazy S)},
    (regsL L).Nodup ↔ NeedsApart L ∧ ∀ e ∈ L, Distinct e.2.sure.ned
  | [] => by simp [regsL, NeedsApart]
  | e :: L => by
    rw [regsL_cons, List.nodup_append, nodup_regsL_iff]
    unfold NeedsApart
    rw [List.pairwise_cons]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      refine ⟨⟨fun e' he' r hr hr' => h4 r ((mem_flatten _ r).mpr hr) r
        (mem_regsL.mpr ⟨e', he', hr'⟩) rfl, h2⟩, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact distinct_of_nodup h1
      · exact h3 x hx
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨flatten_nodup (h3 e List.mem_cons_self), ⟨h2, fun x hx => h3 x (List.mem_cons_of_mem _ hx)⟩,
        fun a ha b hb hab => ?_⟩
      subst hab
      obtain ⟨e', he', hm⟩ := mem_regsL.mp hb
      exact h1 e' he' a ((mem_flatten _ a).mp ha) hm

/-! ## `+copy-need-make-ops`, counted -/

theorem fr_self (a y : Nat) : List.count y [a] ≤ fr a (a + 1) y := by
  unfold fr
  by_cases e : a = y
  · subst e; simp
  · simp [e]

/-- **The merged need and the moves' destinations, counted.** -/
theorem cn_count : ∀ (a b : Need) (ops : List Pole) (g g' : Comp.Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → ∃ new, x.2 = new ++ ops ∧ g.re ≤ g'.re ∧
      ∀ y, List.count y (flattenNeed x.1 ++ defsOf new) ≤
        List.count y (flattenNeed a ++ flattenNeed b) + fr g.re g'.re y := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Nat.le_refl _, fun y => by simp [flattenNeed, defsOf]⟩
  | this rl =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, Nat.le_refl _, fun y => by simp [flattenNeed, defsOf]⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov rl rr], rfl, Nat.le_refl _, fun y => ?_⟩
      rw [defsOf_mov]; simp [flattenNeed]
    | both x' hh tt =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov x' rl], rfl, Nat.le_refl _, fun y => ?_⟩
      rw [defsOf_mov]; simp only [flattenNeed, List.count_append, List.count_cons, List.count_nil]; omega
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov g.re rl], rfl, Nat.le_succ _, fun y => ?_⟩
      have := fr_self g.re y
      rw [defsOf_mov]
      simp only [flattenNeed, List.count_append, List.count_cons, List.count_nil] at this ⊢
      omega
  | pair pl ql ihp ihq =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, Nat.le_refl _, fun y => by simp [flattenNeed, defsOf]⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov g.re rr], rfl, Nat.le_succ _, fun y => ?_⟩
      have := fr_self g.re y
      rw [defsOf_mov]
      simp only [flattenNeed, List.count_append, List.count_cons, List.count_nil] at this ⊢
      omega
    | both x' hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨n1, e1, l1, c1⟩ := ihp hr _ g g1 _ h1
      obtain ⟨n2, e2, l2, c2⟩ := ihq tr _ g1 g2 _ h2
      dsimp only at e1 e2 c1 c2
      refine ⟨n2 ++ n1, by rw [e2, e1, List.append_assoc], Nat.le_trans l1 l2, fun y => ?_⟩
      have a1 := c1 y
      have a2 := c2 y
      have f := fr_add l1 l2 y
      simp only [flattenNeed, defsOf_append, List.count_append, List.count_cons] at a1 a2 ⊢
      omega
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨n1, e1, l1, c1⟩ := ihp pr _ g g1 _ h1
      obtain ⟨n2, e2, l2, c2⟩ := ihq qr _ g1 g2 _ h2
      dsimp only at e1 e2 c1 c2
      refine ⟨n2 ++ n1, by rw [e2, e1, List.append_assoc], Nat.le_trans l1 l2, fun y => ?_⟩
      have a1 := c1 y
      have a2 := c2 y
      have f := fr_add l1 l2 y
      have ec : flattenNeed (consNeed a' b') = flattenNeed a' ++ flattenNeed b' := by
        unfold consNeed; split
        · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; rfl
        · rfl
      rw [ec]
      simp only [flattenNeed, defsOf_append, List.count_append] at a1 a2 ⊢
      omega
  | both rl hl tl ihh iht =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, Nat.le_refl _, fun y => by simp [flattenNeed, defsOf]⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov rl rr], rfl, Nat.le_refl _, fun y => ?_⟩
      rw [defsOf_mov]; simp only [flattenNeed, List.count_append, List.count_cons, List.count_nil]; omega
    | both x' hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨n1, e1, l1, c1⟩ := ihh hr _ g g1 _ h1
      obtain ⟨n2, e2, l2, c2⟩ := iht tr _ g1 g2 _ h2
      dsimp only at e1 e2 c1 c2
      refine ⟨n2 ++ n1 ++ [Pole.mov x' rl], by rw [e2, e1]; simp, Nat.le_trans l1 l2, fun y => ?_⟩
      have a1 := c1 y
      have a2 := c2 y
      have f := fr_add l1 l2 y
      simp only [flattenNeed, defsOf_append, defsOf_mov, List.count_append, List.count_cons,
        List.count_nil] at a1 a2 ⊢
      omega
    | pair p q =>
      simp only [copyNeed] at h
      obtain ⟨x0, g0', h0, h⟩ := bind_some h
      rw [re_apply] at h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨n1, e1, l1, c1⟩ := ihh p _ _ g1 _ h1
      obtain ⟨n2, e2, l2, c2⟩ := iht q _ g1 g2 _ h2
      dsimp only at e1 e2 c1 c2 l1
      refine ⟨n2 ++ n1 ++ [Pole.mov g.re rl], by rw [e2, e1]; simp, by omega, fun y => ?_⟩
      have a1 := c1 y
      have a2 := c2 y
      have f := fr_add l1 l2 y
      have f0 := fr_add (a := g.re) (b := g.re + 1) (c := g2.re) (by omega) (by omega) y
      have s0 := fr_self g.re y
      simp only [flattenNeed, defsOf_append, defsOf_mov, List.count_append, List.count_cons,
        List.count_nil] at a1 a2 s0 ⊢
      omega


/-! ## The count of a merge -/

/-- **The registers of a merge, counted**: what the merge of the entries `La`
into `Lc` defines is old or among the destinations `D`, and the registers
of `Lc` with `D` are at most those of `La` and one per fresh register. -/
structure CR (La Lc : List (Nat × Lazy S)) (g g' : Comp.Gen Map) : Prop where
  le : g.re ≤ g'.re
  drop : g'.drop = g.drop
  cnt : ∃ D : List Nat, (∀ y, Defd g'.blocks y → Defd g.blocks y ∨ y ∈ D) ∧
    ∀ y, List.count y (regsL Lc ++ D) ≤ List.count y (regsL La) + fr g.re g'.re y

theorem CR.keep (L : List (Nat × Lazy S)) (g : Comp.Gen Map) : CR L L g g :=
  ⟨Nat.le_refl _, rfl, [], fun _ h => Or.inl h, fun y => by simp⟩

theorem CR.seq {La1 Lc1 La2 Lc2 : List (Nat × Lazy S)} {g g1 g2 : Comp.Gen Map} (h1 : CR La1 Lc1 g g1)
    (h2 : CR La2 Lc2 g1 g2) : CR (La1 ++ La2) (Lc1 ++ Lc2) g g2 := by
  obtain ⟨l1, d1, D1, hD1, c1⟩ := h1
  obtain ⟨l2, d2, D2, hD2, c2⟩ := h2
  refine ⟨Nat.le_trans l1 l2, d2.trans d1, D1 ++ D2, fun y hy => ?_, fun y => ?_⟩
  · rcases hD2 y hy with h | h
    · rcases hD1 y h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · exact Or.inr (List.mem_append_right _ h)
  · have a1 := c1 y
    have a2 := c2 y
    have f := fr_add l1 l2 y
    simp only [regsL_append, List.count_append] at a1 a2 ⊢
    omega

theorem CR.congr {La Lc La' Lc' : List (Nat × Lazy S)} {g g' : Comp.Gen Map} (h : CR La Lc g g')
    (ha : ∀ y, List.count y (regsL La) ≤ List.count y (regsL La'))
    (hc : ∀ y, List.count y (regsL Lc') ≤ List.count y (regsL Lc)) : CR La' Lc' g g' := by
  obtain ⟨l, d, D, hD, c⟩ := h
  refine ⟨l, d, D, hD, fun y => ?_⟩
  have := c y
  have := ha y
  have := hc y
  simp only [List.count_append] at *
  omega

theorem cr_root {t : Nat} {a b c : Lazy S} {ned : Need} {ops : List Pole} {g g1 g2 : Comp.Gen Map}
    (hc : c.sure.ned = ned) (h1 : copyNeed a.sure.ned b.sure.ned [] g = some ((ned, ops), g1)) (hd : g.drop = false)
    (h2 : addOps t ops g1 = some ((), g2)) : CR [(t, a), (t, b)] [(t, c)] g g2 := by
  obtain ⟨A, -, C⟩ := copyNeed_spec _ _ _ _ _ _ h1
  obtain ⟨new, enew, -, cn⟩ := cn_count _ _ _ _ _ _ h1
  have e1 : g1.drop = g.drop ∧ g1.blocks = g.blocks := by rw [C.gen]; exact ⟨rfl, rfl⟩
  have hd1 : g1.drop = false := e1.1.trans hd
  obtain ⟨AS, -, pr2⟩ := addOps_step hd1 h2
  dsimp only at enew cn
  rw [List.append_nil] at enew
  subst enew
  refine ⟨Nat.le_trans C.le AS.2.2.2.1, AS.2.1.trans e1.1, defsOf ops, fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨k, b0, hb0, hm⟩ := (defd_prep pr2).mp hy
    rw [e1.2] at hb0
    rcases hm with hm | hm
    · exact Or.inl (defd_iff.mpr ⟨k, b0, hb0, hm⟩)
    · by_cases hk : k = t
      · rw [if_pos hk] at hm; exact Or.inr hm
      · rw [if_neg hk] at hm; simp [defsOf] at hm
  · have h3 := cn y
    have f := fr_mono (a := g.re) AS.2.2.2.1 y
    simp only [regsL_cons, regsL_nil, List.append_nil, hc, List.count_append] at h3 ⊢
    omega

/-! ## Index lookups as a permutation -/

theorem filterMap_sub_map {α : Type} (key : α → Nat) (h : α → Option Nat)
    (hh : ∀ x, h x = Option.none ∨ h x = some (key x)) : ∀ (l : List α), (l.filterMap h).Sublist (l.map key)
  | [] => by simp
  | x :: l => by
    rcases hh x with e | e
    · simp only [List.filterMap_cons, e, List.map_cons]
      exact (filterMap_sub_map key h hh l).cons _
    · simp only [List.filterMap_cons, e, List.map_cons]
      exact (filterMap_sub_map key h hh l).cons_cons _

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), nodup_of_map f h.2⟩

theorem idx_perm {α : Type} (key : α → Nat) {l1 l2 : List α} (h1 : (l1.map key).Nodup) (h2 : (l2.map key).Nodup) :
    (l1.filterMap fun x => HoonMap.get (index (Map := Map) key l2) (key x)).Perm
      (l2.filter fun e => seen (S := S) key l1 (key e)) := by
  have hn2 : l2.Nodup := nodup_of_map key h2
  refine (List.perm_ext_iff_of_nodup ?_ (List.Nodup.sublist List.filter_sublist hn2)).mpr fun v => ?_
  · have hs : ((l1.filterMap fun x => HoonMap.get (index (Map := Map) key l2) (key x)).map key).Sublist
        (l1.map key) := by
      rw [List.map_filterMap]
      refine filterMap_sub_map key _ (fun x => ?_) l1
      cases e : HoonMap.get (index (Map := Map) key l2) (key x) with
      | none => left; rfl
      | some w => right; simp [(gm_index_get key e).2]
    exact nodup_of_map key (List.Nodup.sublist hs h1)
  · simp only [List.mem_filterMap, List.mem_filter]
    constructor
    · rintro ⟨x, hx, hv⟩
      obtain ⟨hv2, hk⟩ := gm_index_get key hv
      exact ⟨hv2, (gm_seen key l1 (key v)).mpr (List.mem_map.mpr ⟨x, hx, hk.symm⟩)⟩
    · rintro ⟨hv2, hs⟩
      obtain ⟨x, hx, hxk⟩ := List.mem_map.mp ((gm_seen key l1 (key v)).mp hs)
      exact ⟨x, hx, by rw [hxk]; exact gm_index_mem key h2 hv2⟩

theorem fe_perm {l l' : List (ForkE S)} (h : l.Perm l') : (forkEntries l).Perm (forkEntries l') := by
  have hc : ∀ (w : ForkE S) (ws : List (ForkE S)), forkEntries (w :: ws) = forkEntries [w] ++ forkEntries ws :=
    fun w ws => fe_append [w] ws
  induction h with
  | nil => exact List.Perm.refl _
  | @cons x l1 l2 _ ih => rw [hc x l1, hc x l2]; exact ih.append_left _
  | swap x y l =>
    rw [hc y (x :: l), hc x l, hc x (y :: l), hc y l, ← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem be_perm {l l' : List (Nat × Lazy S)} (h : l.Perm l') : (bondEntries l).Perm (bondEntries l') := by
  have hc : ∀ (w : Nat × Lazy S) (ws : List (Nat × Lazy S)), bondEntries (w :: ws) = bondEntries [w] ++ bondEntries ws :=
    fun w ws => be_append [w] ws
  induction h with
  | nil => exact List.Perm.refl _
  | @cons x l1 l2 _ ih => rw [hc x l1, hc x l2]; exact ih.append_left _
  | swap x y l =>
    rw [hc y (x :: l), hc x l, hc x (y :: l), hc y l, ← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The merged and the kept entries of `second` are at most its entries. -/
theorem count_split_fe {f1 sf : List (ForkE S)} (h1 : (f1.map fun e : ForkE S => e.1.1).Nodup)
    (h2 : (sf.map fun e : ForkE S => e.1.1).Nodup) (y : Nat) :
    List.count y (regsL (forkEntries (f1.filterMap fun fe => HoonMap.get (index (Map := Map)
        (fun e : ForkE S => e.1.1) sf) fe.1.1) ++
      forkEntries (sf.filter fun e => !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1)))) ≤
      List.count y (regsL (forkEntries sf)) := by
  have P := idx_perm (Map := Map) (S := S) (fun e : ForkE S => e.1.1) h1 h2
  have Q := (P.append_right (sf.filter fun e => !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1))).trans
    (List.filter_append_perm (fun e : ForkE S => seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1) sf)
  rw [← fe_append]
  exact Nat.le_of_eq ((regsL_perm (fe_perm Q)).count_eq y)

theorem count_split_be {b1 sb : List (Nat × Lazy S)} (h1 : (b1.map fun e : Nat × Lazy S => e.1).Nodup)
    (h2 : (sb.map fun e : Nat × Lazy S => e.1).Nodup) (y : Nat) :
    List.count y (regsL (bondEntries (b1.filterMap fun e => HoonMap.get (index (Map := Map)
        (fun e : Nat × Lazy S => e.1) sb) e.1) ++
      bondEntries (sb.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)))) ≤
      List.count y (regsL (bondEntries sb)) := by
  have P := idx_perm (Map := Map) (S := S) (fun e : Nat × Lazy S => e.1) h1 h2
  have Q := (P.append_right (sb.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1))).trans
    (List.filter_append_perm (fun e : Nat × Lazy S => seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1) sb)
  rw [← be_append]
  exact Nat.le_of_eq ((regsL_perm (be_perm Q)).count_eq y)


/-! ## The count of the merge -/

mutual
/-- **The registers of the merge of two `LabUniq` trees at `t`, counted.** -/
theorem cr_copyLazyL (t : Nat) : ∀ (a b : Lazy S) (g g' : Comp.Gen Map) (c : Lazy S),
    copyLazyL t a b g = some (c, g') → g.drop = false → LabUniq a → LabUniq b →
    CR (((t, a) :: entries a) ++ ((t, b) :: entries b)) ((t, c) :: entries c) g g'
  | mk s1 f1 b1, second, g, g', c, h, hd, hUa, hU => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨u, g2, h2, h⟩ := bind_some h
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hea : entries (mk s1 f1 b1) = bondEntries b1 ++ forkEntries f1 := rfl
    have heb := entries_parts second
    have hU0 := hU (0, second) List.mem_cons_self
    have hUa0 := hUa (0, mk s1 f1 b1) List.mem_cons_self
    have R1 := cr_root (t := t) (c := mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ fork bond)
      (a := mk s1 f1 b1) rfl h1 hd (by cases u; exact h2)
    have hd2 : g2.drop = false := R1.drop.trans hd
    -- the forks
    have R2 : CR (forkEntries f1 ++ forkEntries second.fork) (forkEntries fork) g2 g3 := by
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact (CR.keep _ g2).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c1] at h3
      by_cases c2 : f1.isEmpty = true
      · rw [if_pos c2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact (CR.keep _ g2).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c2] at h3
      obtain ⟨merged, g3', hm, h3⟩ := bind_some h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      have M := cr_mergeForks (index (Map := Map) (fun e : ForkE S => e.1.1) second.fork) f1 g2 g3' merged
        hm hd2 (fun v hv => by
          have hsub := fe_sub hv
          rw [fe_single] at hsub
          exact ⟨labUniq_of hUa (o := v.1.1) fun e he => by
              rw [hea]; exact List.mem_append_right _ (hsub e (List.mem_append_left _ he)),
            labUniq_of hUa (o := v.2.1) fun e he => by
              rw [hea]; exact List.mem_append_right _ (hsub e (List.mem_append_right _ he))⟩)
        (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := fe_sub hv
          rw [fe_single] at hsub
          exact ⟨labUniq_of hU (o := v.1.1) fun e he => by
              rw [heb]; exact List.mem_append_right _ (hsub e (List.mem_append_left _ he)),
            labUniq_of hU (o := v.2.1) fun e he => by
              rw [heb]; exact List.mem_append_right _ (hsub e (List.mem_append_right _ he)), hkv⟩)
      refine (M.seq (CR.keep (forkEntries (second.fork.filter fun e =>
        !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1))) g3')).congr (fun x => ?_) (fun x => ?_)
      · have := count_split_fe (Map := Map) (f1 := f1) (sf := second.fork) hUa0.2 hU0.2 x
        simp only [regsL_append, List.count_append] at this ⊢
        omega
      · rw [fe_append]; exact Nat.le_refl _
    obtain R2 := R2
    have hd3 : g3.drop = false := R2.drop.trans hd2
    -- the bonds
    have R3 : CR (bondEntries b1 ++ bondEntries second.bond) (bondEntries bond) g3 g4 := by
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact (CR.keep _ g3).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c1] at h4
      by_cases c2 : b1.isEmpty = true
      · rw [if_pos c2] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact (CR.keep _ g3).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c2] at h4
      obtain ⟨merged, g4', hm, h4⟩ := bind_some h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      have M := cr_mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1 g3 g4'
        merged hm hd3 (fun v hv => by
          have hsub := be_sub hv
          rw [be_single] at hsub
          exact labUniq_of hUa (o := v.1) fun e he => by rw [hea]; exact List.mem_append_left _ (hsub e he))
        (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := be_sub hv
          rw [be_single] at hsub
          exact ⟨labUniq_of hU (o := v.1) fun e he => by rw [heb]; exact List.mem_append_left _ (hsub e he), hkv⟩)
      refine (M.seq (CR.keep (bondEntries (second.bond.filter fun e =>
        !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1))) g4')).congr (fun x => ?_) (fun x => ?_)
      · have := count_split_be (Map := Map) (b1 := b1) (sb := second.bond) hUa0.1 hU0.1 x
        simp only [regsL_append, List.count_append] at this ⊢
        omega
      · rw [be_append]; exact Nat.le_refl _
    refine ((R1.seq R2).seq R3).congr (fun x => ?_) (fun x => ?_)
    · rw [hea, heb]
      simp only [regsL_append, regsL_cons, regsL_nil, List.count_append, List.cons_append, List.nil_append]
      omega
    · show List.count x (regsL ((t, _) :: (bondEntries bond ++ forkEntries fork))) ≤ _
      simp only [regsL_append, regsL_cons, regsL_nil, List.count_append, List.cons_append, List.nil_append]
      omega

/-- The forks of the merge, counted. -/
theorem cr_mergeForks (idx : Map (ForkE S)) :
    ∀ (l : List (ForkE S)) (g g' : Comp.Gen Map) (l' : List (ForkE S)),
    mergeForks idx l g = some (l', g') → g.drop = false → (∀ v ∈ l, LabUniq v.1.2 ∧ LabUniq v.2.2) →
    (∀ k v, HoonMap.get idx k = some v → LabUniq v.1.2 ∧ LabUniq v.2.2 ∧ v.1.1 = k) →
    CR (forkEntries l ++ forkEntries (l.filterMap fun fe => HoonMap.get idx fe.1.1)) (forkEntries l') g g'
  | [], g, g', l', h, _, _, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (CR.keep [] g).congr (fun x => by simp [forkEntries, regsL]) (fun x => by simp [forkEntries, regsL])
  | ((oy, y), (on, n)) :: rest, g, g', l', h, hd, hUl, hidx => by
    rw [mergeForks] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : ForkE S) (ws : List (ForkE S)), forkEntries (w :: ws) = forkEntries [w] ++ forkEntries ws :=
      fun w ws => fe_append [w] ws
    have hU1 := hUl _ List.mem_cons_self
    have hUr : ∀ v ∈ rest, LabUniq v.1.2 ∧ LabUniq v.2.2 := fun v hv => hUl v (List.mem_cons_of_mem _ hv)
    have E : CR (forkEntries [((oy, y), (on, n))] ++ forkEntries (HoonMap.get idx oy).toList)
        (forkEntries [e]) g g1 := by
      rcases hk : HoonMap.get idx oy with _ | ⟨⟨z, my⟩, ⟨mon, mn⟩⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact (CR.keep _ g).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      · rw [hk] at h1
        obtain ⟨hU1', hU2', hz⟩ := hidx oy _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        by_cases ce : on = mon
        · rw [if_pos ce] at h1
          subst ce
          obtain ⟨y', ga, hya, h1⟩ := bind_some h1
          obtain ⟨n', gb, hnb, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have A := cr_copyLazyL z y my g ga y' hya hd hU1.1 hU1'
          have B := cr_copyLazyL on n mn ga gb n' hnb (A.drop.trans hd) hU1.2 hU2'
          refine (A.seq B).congr (fun x => ?_) (fun x => ?_)
          · simp only [Option.toList, fe_single, regsL_append, regsL_cons, List.count_append]
            omega
          · simp only [fe_single, regsL_append, regsL_cons, List.count_append]
            omega
        · rw [if_neg ce] at h1
          cases h1
    have R := cr_mergeForks idx rest g1 g2 r h2 (E.drop.trans hd) hUr hidx
    refine (E.seq R).congr (fun x => ?_) (fun x => ?_)
    · rw [hcons ((oy, y), (on, n)) rest]
      simp only [filterMap_cons_toList, fe_append, regsL_append, List.count_append]
      omega
    · rw [hcons e r]; exact Nat.le_refl _

/-- The bonds of the merge, counted. -/
theorem cr_mergeBonds (idx : Map (Nat × Lazy S)) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Comp.Gen Map) (l' : List (Nat × Lazy S)),
    mergeBonds idx l g = some (l', g') → g.drop = false → (∀ v ∈ l, LabUniq v.2) →
    (∀ k v, HoonMap.get idx k = some v → LabUniq v.2 ∧ v.1 = k) →
    CR (bondEntries l ++ bondEntries (l.filterMap fun e => HoonMap.get idx e.1)) (bondEntries l') g g'
  | [], g, g', l', h, _, _, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (CR.keep [] g).congr (fun x => by simp [bondEntries, regsL]) (fun x => by simp [bondEntries, regsL])
  | (ob, lb) :: rest, g, g', l', h, hd, hUl, hidx => by
    rw [mergeBonds] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : Nat × Lazy S) (ws : List (Nat × Lazy S)), bondEntries (w :: ws) = bondEntries [w] ++ bondEntries ws :=
      fun w ws => be_append [w] ws
    have hU1 := hUl _ List.mem_cons_self
    have hUr : ∀ v ∈ rest, LabUniq v.2 := fun v hv => hUl v (List.mem_cons_of_mem _ hv)
    have E : CR (bondEntries [(ob, lb)] ++ bondEntries (HoonMap.get idx ob).toList) (bondEntries [e]) g g1 := by
      rcases hk : HoonMap.get idx ob with _ | ⟨z, m⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact (CR.keep _ g).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      · rw [hk] at h1
        obtain ⟨hU1', hz⟩ := hidx ob _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        obtain ⟨l2, ga, hla, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        have A := cr_copyLazyL z lb m g ga l2 hla hd hU1 hU1'
        refine A.congr (fun x => ?_) (fun x => ?_)
        · simp only [Option.toList, be_single, regsL_append, regsL_cons, List.count_append]
          omega
        · simp only [be_single, regsL_append, regsL_cons, List.count_append]
          omega
    have R := cr_mergeBonds idx rest g1 g2 r h2 (E.drop.trans hd) hUr hidx
    refine (E.seq R).congr (fun x => ?_) (fun x => ?_)
    · rw [hcons (ob, lb) rest]
      simp only [filterMap_cons_toList, be_append, regsL_append, List.count_append]
      omega
    · rw [hcons e r]; exact Nat.le_refl _
end


/-! ## The `IL` half -/

theorem poleRegs_sub {op : Pole} {x : Nat} (h : x ∈ Comp.poleRegs op) : x ∈ aliasReads op ∨ x ∈ poleWr op := by
  have e0 : Comp.poleRegs op = Opt.poleRegs op := by cases op <;> rfl
  rw [e0] at h
  unfold aliasReads
  cases e : aliasDst op with
  | none => exact Or.inl h
  | some d =>
    by_cases hx : x = d
    · subst hx; exact Or.inr (aliasDst_poleWr e)
    · exact Or.inl ((List.mem_erase_of_ne hx).mpr h)

/-- **The `IL` half of `+copy`.** -/
theorem copyL_il {K : Nat → Nat → Prop} {first : NextL S} {second : Lazy S} {s2 : Nat} {g g' : Comp.Gen Map}
    {nex : NextL S} (hI : IL K first.goal g) (hII : IL K (CGoalL.next second (jmp0 s2)) g)
    (hT : TreesApart first.th.there first.laz s2 second) (hUa : LabUniq first.laz) (hUb : LabUniq second)
    (h : copyL first second g = some (nex, g')) : IL K nex.goal g' := by
  have hd : g.drop = false := hI.ats.1
  have hG1 : GoalL g (CGoalL.next first.laz first.th) := hI.goal
  have hG2 : GoalL g (CGoalL.next second (jmp0 s2)) := hII.goal
  obtain ⟨hF1, hap1, hent1⟩ := hG1
  obtain ⟨-, hap2, hent2⟩ := hG2
  obtain ⟨A', KP', Fr'⟩ := (ht_copyL first second).run g nex g' hI.ats hF1 h
  obtain ⟨bt, hbt, -, targs⟩ := hF1
  unfold copyL at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  rw [emit_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨laz, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hd1 : (g.emitted ⟨[], [], Termin.hop first.th⟩).drop = false := hd
  let Src : Nat × Lazy S → Prop := fun e => e ∈ ((g.bo, first.laz) :: entries first.laz) ++
    ((g.bo, second) :: entries second)
  obtain ⟨P, M⟩ := mr_copyLazyL Src g.bo first.laz second _ g2 laz h2 hd1
    (fun e he => List.mem_append_left _ he) (fun e he => List.mem_append_right _ he) hUb
  obtain ⟨-, -, D, hD, hc⟩ := cr_copyLazyL g.bo first.laz second _ g2 laz h2 hd1 hUa hUb
  have Mle : g.re ≤ g2.re := M.le
  -- the registers of the two trees
  have eLa : regsL (((g.bo, first.laz) :: entries first.laz) ++ ((g.bo, second) :: entries second)) =
      regsL (((first.th.there, first.laz) :: entries first.laz) ++ ((s2, second) :: entries second)) := by
    simp only [regsL_append, regsL_cons]
  have hn : (regsL (((first.th.there, first.laz) :: entries first.laz) ++ ((s2, second) :: entries second))).Nodup := by
    rw [regsL_append, List.nodup_append]
    refine ⟨nodup_regsL_iff.mpr ⟨hap1, fun e he => (hent1 e he).2.1⟩,
      nodup_regsL_iff.mpr ⟨hap2, fun e he => (hent2 e he).2.1⟩, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨e, he, hm⟩ := mem_regsL.mp ha
    obtain ⟨e', he', hm'⟩ := mem_regsL.mp hb
    exact hT e he e' he' a hm hm'
  have hsrc : ∀ y ∈ regsL (((first.th.there, first.laz) :: entries first.laz) ++ ((s2, second) :: entries second)),
      y < g.re ∧ ¬ Defd g.blocks y ∧ HoonMap.get g.cond y = Option.none := by
    intro y hy
    obtain ⟨e, he, hm⟩ := mem_regsL.mp hy
    rcases List.mem_append.mp he with he | he
    · obtain ⟨l1, l2⟩ := (hent1 e he).2.2 y hm
      refine ⟨l1, l2, ?_⟩
      cases ec : HoonMap.get g.cond y with
      | none => rfl
      | some v => exact ((hI.cond y v ec).2.2.1 ⟨e, he, hm⟩).elim
    · obtain ⟨l1, l2⟩ := (hent2 e he).2.2 y hm
      refine ⟨l1, l2, ?_⟩
      cases ec : HoonMap.get g.cond y with
      | none => rfl
      | some v => exact ((hII.cond y v ec).2.2.1 ⟨e, he, hm⟩).elim
  -- the count: the result's registers and the destinations have no repetition
  have hc' : ∀ y, List.count y (regsL ((g.bo, laz) :: entries laz) ++ D) ≤ 1 := by
    intro y
    have h1 := hc y
    rw [eLa] at h1
    have hfr : fr (g.emitted ⟨[], [], Termin.hop first.th⟩).re g2.re y = fr g.re g2.re y := rfl
    rw [hfr] at h1
    by_cases hy : g.re ≤ y
    · have h0 : List.count y (regsL (((first.th.there, first.laz) :: entries first.laz) ++
          ((s2, second) :: entries second))) = 0 :=
        List.count_eq_zero.mpr fun hm => by have := (hsrc y hm).1; omega
      have := fr_le_one g.re g2.re y
      omega
    · have h0 : fr g.re g2.re y = 0 := by unfold fr; rw [if_neg (by omega)]
      have := count_le_one_of_nodup hn y
      omega
  have hN : (regsL ((g.bo, laz) :: entries laz) ++ D).Nodup := nodup_of_count hc'
  have hsf : ∀ y ∈ regsL ((g.bo, laz) :: entries laz) ++ D,
      y ∈ regsL (((first.th.there, first.laz) :: entries first.laz) ++ ((s2, second) :: entries second)) ∨
        (g.re ≤ y ∧ y < g2.re) := by
    intro y hy
    have h1 := hc y
    rw [eLa] at h1
    have hfr : fr (g.emitted ⟨[], [], Termin.hop first.th⟩).re g2.re y = fr g.re g2.re y := rfl
    rw [hfr] at h1
    have hp : 0 < List.count y (regsL ((g.bo, laz) :: entries laz) ++ D) := List.count_pos_iff.mpr hy
    by_cases hm : y ∈ regsL (((first.th.there, first.laz) :: entries first.laz) ++ ((s2, second) :: entries second))
    · exact Or.inl hm
    · have := List.count_eq_zero.mpr hm
      exact Or.inr (fr_pos (by omega))
  have hfree : HoonMap.get g.blocks g.bo = Option.none := hI.ats.free
  have hDe : ∀ r, Defd (g.emitted ⟨[], [], Termin.hop first.th⟩).blocks r → Defd g.blocks r := fun r hr => by
    have e := (defd_put (b := (⟨[], [], Termin.hop first.th⟩ : Blob)) hfree (r := r)).mp
      (by simpa [Gen.emitted, hd] using hr)
    rcases e with e | e
    · exact e
    · simp [blockDefs] at e
  have hndef : ∀ y ∈ regsL ((g.bo, laz) :: entries laz), ¬ Defd g2.blocks y := by
    intro y hy hdy
    rcases hD y hdy with hdy | hdy
    · have hdg := hDe y hdy
      rcases hsf y (List.mem_append_left _ hy) with hs | hs
      · exact (hsrc y hs).2.1 hdg
      · have := defd_lt hI.regs hdg; omega
    · exact (List.nodup_append.mp hN).2.2 y hy y hdy rfl
  have hnk : ∀ y ∈ regsL ((g.bo, laz) :: entries laz) ++ D, HoonMap.get g.cond y = Option.none := by
    intro y hy
    rcases hsf y hy with hs | hs
    · exact (hsrc y hs).2.2
    · cases ec : HoonMap.get g.cond y with
      | none => rfl
      | some v => have := (hI.cond y v ec).1; omega
  have hcond : g2.cond = g.cond := M.cond
  have hbo : g2.bo = g.bo + 1 := M.bo
  refine ⟨A', fun k b hb => ?_, fun k v hk => ?_, by rw [hbo]; exact hI.kvan.mono (Nat.le_succ _), ?_⟩
  · -- registers below `re`
    obtain ⟨b0, hb0, rfl⟩ := get_prep M.prep hb
    have hB0 : BlobIn (· < g2.re) b0 := by
      rw [em_get hd] at hb0
      split at hb0
      · cases hb0; exact blobIn_nil_fin (jmpIn_nil targs)
      · exact (hI.regs k b0 hb0).mono fun x hx => Nat.lt_of_lt_of_le hx Mle
    refine ⟨hB0.1, RegsIn.append (fun op hop x hx => ?_) hB0.2.1, hB0.2.2⟩
    rcases poleRegs_sub hx with hx | hx
    · obtain ⟨e, he, -, hm⟩ := M.rd k op hop x hx
      have hy : x ∈ regsL ((g.bo, laz) :: entries laz) := mem_regsL.mpr ⟨e, he, hm⟩
      rcases hsf x (List.mem_append_left _ hy) with hs | hs
      · exact Nat.lt_of_lt_of_le (hsrc x hs).1 Mle
      · exact hs.2
    · obtain ⟨e, hs, -, hm⟩ := M.wr k op hop x hx
      have : x ∈ regsL (((first.th.there, first.laz) :: entries first.laz) ++ ((s2, second) :: entries second)) := by
        rw [← eLa]; exact mem_regsL.mpr ⟨e, hs, hm⟩
      exact Nat.lt_of_lt_of_le (hsrc x this).1 Mle
  · -- the keys
    rw [hcond] at hk
    obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    have notin : k ∉ regsL ((g.bo, laz) :: entries laz) ++ D := fun hm => by rw [hnk k hm] at hk; cases hk
    refine ⟨Nat.lt_of_lt_of_le k1 Mle, fun hdk => ?_, fun hg => ?_, Nat.lt_of_lt_of_le k4 Mle,
      by rw [hcond]; exact k5⟩
    · rcases hD k hdk with h' | h'
      · exact k2 (hDe k h')
      · exact notin (List.mem_append_right _ h')
    · obtain ⟨e, he, hm⟩ := hg
      exact notin (List.mem_append_left _ (mem_regsL.mpr ⟨e, he, hm⟩))
  · -- the merged goal
    have hnd := nodup_regsL_iff.mp (List.nodup_append.mp hN).1
    refine ⟨Fr', hnd.1, fun e he => ⟨?_, hnd.2 e he, fun r hr => ?_⟩⟩
    · obtain ⟨⟨e', hs, ee⟩, -⟩ := M.ent e he
      rw [← ee]
      rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_cons.mp hs with rfl | hs
        · obtain ⟨b, hb, hp, -⟩ := Fr'
          exact ⟨b, hb, hp⟩
        · obtain ⟨b, hb, hp⟩ := (hent1 e' (List.mem_cons_of_mem _ hs)).1
          obtain ⟨b', hb', hp', -⟩ := KP'.2.2 _ b hb
          exact ⟨b', hb', hp'.trans hp⟩
      · rcases List.mem_cons.mp hs with rfl | hs
        · obtain ⟨b, hb, hp, -⟩ := Fr'
          exact ⟨b, hb, hp⟩
        · obtain ⟨b, hb, hp⟩ := (hent2 e' (List.mem_cons_of_mem _ hs)).1
          obtain ⟨b', hb', hp', -⟩ := KP'.2.2 _ b hb
          exact ⟨b', hb', hp'.trans hp⟩
    · have hy : r ∈ regsL ((g.bo, laz) :: entries laz) := mem_regsL.mpr ⟨e, he, hr⟩
      refine ⟨?_, hndef r hy⟩
      rcases hsf r (List.mem_append_left _ hy) with hs | hs
      · exact Nat.lt_of_lt_of_le (hsrc r hs).1 Mle
      · exact hs.2

/-- **The spec of `+copy`**, both halves. -/
theorem copyL_spec : CopySpecL S Map := fun _ _ _ _ _ _ _ hI hII hT hUa hUb h =>
  ⟨copyL_il hI hII hT hUa hUb h, fun r hl => copyL_live hI hII hUb h r hl⟩

end Raw
end SkaModel
end Formalization
