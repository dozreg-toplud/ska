import lemmas.Ska.CompSixNxTop
import lemmas.Ska.CompTagU
import lemmas.Ska.CompWholeKern
import lemmas.Ska.CompMedeE
import lemmas.Ska.CompFlatCopy

/-!
# The tag clause of the calling class, and calling branches of a `%6`

README Gaps 12.38, steps 1 and 2.  Phase S of `[6 c a b]` under `%next`
asks of each branch the tag clause `TagLSP` (`CompSixNxRun.lean`): every key
its run adds to `cond` has a tag with the region as a suffix.  Keys are
added only by `+proxy`, in a lazy block of the need that `+kern` (of the
indirect call's `+kerf`) or `+collapse-lazy-atom` (of `[4 p]`, `[3 p]`,
`[5 p q]`) walks, with that block's tag; and in the class `CallTreeA` tags
are set only by `+past`, at its new block, to the region.  So the
induction carries the tags of the lazy blocks: from a goal whose entries'
blocks have tags with the region as a suffix, a run sets only such tags,
adds only such keys, and leaves a result whose entries' blocks have such
tags (`TagCA`).  The statement was checked first (`CompSixNxTagCheck.lean`).

* `TagCS` (tags, `cond`, `drop`), `kernGate_tag`, `kerf_tagCS`,
  `medeL_tagCS`, `pastL_tagC`, `copyL_tagC`, `splitL_tagC`: the arms.
* `splitLoop_lab`, `copyLazyL_lab` (and their loops): the labels of the
  entries of `+split`'s halves and of `+copy-lazy`'s result are labels of
  their inputs' entries.
* `TagCA`, `tagCA_callTreeA`: the induction on `CallTreeA`;
  `tagLSP_callTreeA`: `TagLSP` of every member.
* `LOKSF.toE`, `entLS_of_noEnt`, `sixN_callTreeA`: `SixN` with the bound
  `0` of every member of `CallTreeA` with `NoEntF`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation of states -/

/-- **Tags and `cond` change only by entries whose tags have `R` as a
suffix, and `drop` is kept.** -/
structure TagCS (R : List Nat) (g0 g1 : Gen Map) : Prop where
  tags : TagStep R g0 g1
  cond : CondTag R g0.cond g1.cond
  drop : g1.drop = g0.drop

theorem TagCS.refl (R : List Nat) (g : Gen Map) : TagCS R g g :=
  ⟨TagStep.of_eq rfl, CondTag.refl _, rfl⟩

theorem TagCS.trans {R : List Nat} {a b c : Gen Map} (x : TagCS R a b) (y : TagCS R b c) : TagCS R a c :=
  ⟨x.tags.trans y.tags, x.cond.trans y.cond, y.drop.trans x.drop⟩

theorem TagCS.of_eqs {R : List Nat} {g g' : Gen Map} (t : g'.tags = g.tags) (c : g'.cond = g.cond)
    (d : g'.drop = g.drop) : TagCS R g g' :=
  ⟨TagStep.of_eq t, CondTag.of_eq c, d⟩

theorem TagCS.of_k {R : List Nat} {α : Type} {m : CM Map α} (ht : KT m) (hc : KC m) (hd : KD m)
    {g g' : Gen Map} {x : α} (h : m g = some (x, g')) : TagCS R g g' :=
  TagCS.of_eqs (ht.keep _ _ _ h) (hc.keep _ _ _ h) (hd.keep _ _ _ h)

theorem TagCS.of_st {R : List Nat} {g g' : Gen Map} (s : StepTag R g g') : TagCS R g g' :=
  ⟨TagStep.of_eq s.1, s.2.2, s.2.1⟩

theorem TagOK.cs {R : List Nat} {g g' : Gen Map} {o : Nat} (s : TagCS R g g') (h : TagOK R g o) :
    TagOK R g' o :=
  s.tags.keep h

/-! ## `+kern` and `+mede` -/

theorem kt_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, KT (kh x a)) (ht : ∀ x a, KT (kt x a)) (ops : List Pole) :
    KT (kernBoth r d kh kt ops) := by
  unfold kernBoth
  exact KT.bind' KT.re' fun _ => KT.bind' (ht _ _) fun _ => KT.bind' KT.re' fun _ =>
    KT.bind' (hh _ _) fun _ => by kt

theorem kt_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), KT (kernLoop r ned ops : CM Map (List Pole))
  | _, Need.none, _ => by unfold kernLoop; kt
  | _, Need.this _, _ => by unfold kernLoop; kt
  | _, Need.pair p q, _ => by
    unfold kernLoop
    exact KT.bind' KT.re' fun _ => kt_kernBoth _ _ (fun x a => kt_kernLoop x p a) (fun x a => kt_kernLoop x q a) _
  | _, Need.both _ h t, _ => by
    unfold kernLoop
    exact kt_kernBoth _ _ (fun x a => kt_kernLoop x h a) (fun x a => kt_kernLoop x t a) _

theorem kd_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, KD (kh x a)) (ht : ∀ x a, KD (kt x a)) (ops : List Pole) :
    KD (kernBoth r d kh kt ops) := by
  unfold kernBoth
  exact KD.bind' KD.re' fun _ => KD.bind' (ht _ _) fun _ => KD.bind' KD.re' fun _ =>
    KD.bind' (hh _ _) fun _ => by kd

theorem kd_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), KD (kernLoop r ned ops : CM Map (List Pole))
  | _, Need.none, _ => by unfold kernLoop; kd
  | _, Need.this _, _ => by unfold kernLoop; kd
  | _, Need.pair p q, _ => by
    unfold kernLoop
    exact KD.bind' KD.re' fun _ => kd_kernBoth _ _ (fun x a => kd_kernLoop x p a) (fun x a => kd_kernLoop x q a) _
  | _, Need.both _ h t, _ => by
    unfold kernLoop
    exact kd_kernBoth _ _ (fun x a => kd_kernLoop x h a) (fun x a => kd_kernLoop x t a) _

/-- **The gate of `+kern` makes its proxies in the lazy block it is given**,
with that block's tag. -/
theorem kernGate_tag (R : List Nat) (r o : Nat) : GateTag (S := S) (Map := Map) R o (kernGate r o) := by
  intro oL s g g' h hL
  unfold kernGate at h
  obtain ⟨ned, g1, h1, h⟩ := bind_some h
  have s1 : StepTag R g g1 := StepTag.of_k (kc_sureRequireLook _) (kt_sureRequireLook _) (kd_sureRequireLook _) h1
  have hL1 : oL = o ∨ TagOK R g1 oL := hL.imp id (fun ht => ht.st s1)
  split at h
  · cases h; exact s1
  · obtain ⟨src, g2, h2, h⟩ := bind_some h
    have s2 : StepTag R g1 g2 := by
      by_cases e : oL = o
      · rw [if_pos e] at h2; cases h2; exact StepTag.refl _
      · rw [if_neg e] at h2; exact proxy_tag h2 (hL1.resolve_left e)
    split at h
    · cases h
    · obtain ⟨ops, g3, h3, h4⟩ := bind_some h
      unfold kernNeed at h3
      exact s1.trans (s2.trans ((StepTag.of_k (kc_kernLoop _ _ _) (kt_kernLoop _ _ _) (kd_kernLoop _ _ _) h3).trans
        (StepTag.of_k (KC.addOps' _ _) (KT.addOps' _ _) (KD.addOps' _ _) h4)))

/-- **`+kerf` adds keys with the tags of the lazy blocks of the need.** -/
theorem kerf_tagCS {R : List Nat} {nex : NextL S} {g g' : Gen Map} {out pro : Nat}
    (h : kerf nex g = some ((out, pro), g')) (he : ∀ e ∈ entries nex.laz, TagOK R g e.1) : TagCS R g g' := by
  unfold kerf at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨r, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  have s1 : StepTag R g g1 := StepTag.of_k (KC.emit' _) (KT.emit' _) (KD.emit' _) h1
  rw [kern_eq] at h2
  obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
  have s3 : StepTag R g1 g3 := StepTag.of_k KC.re' KT.re' KD.re' h3
  obtain ⟨g4, g4', h4, h2⟩ := bind_some h2
  rw [get_apply] at h4
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨rfl, rfl⟩ := h4
  split at h2
  · cases h2; exact TagCS.of_st (s1.trans s3)
  · obtain ⟨u, g5, h5, h6⟩ := bind_some h2
    have W := walkLazy_tag (kernGate_tag R r0 o) o nex.laz _ g5 h5 (Or.inl rfl)
      (fun e hm => ((he e hm).st s1).st s3)
    have T := TagCS.of_st (s1.trans (s3.trans W))
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
    rw [← h6.2]; exact T

/-- **`+mede` makes no proxy.** -/
theorem medeL_tagCS {R : List Nat} {th : Jmp} {som : Noun} {laz : Lazy S} {g g' : Gen Map} {o : Nat}
    (h : medeL th som laz g = some (o, g')) (he : ∀ e ∈ entries laz, TagOK R g e.1) : TagCS R g g' := by
  rw [medeL_eq] at h
  obtain ⟨o1, g1, h1, h⟩ := bind_some h
  have s1 : StepTag R g g1 := StepTag.of_k (KC.emit' _) (KT.emit' _) (KD.emit' _) h1
  obtain ⟨g4, g4', h4, h⟩ := bind_some h
  rw [get_apply] at h4
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨rfl, rfl⟩ := h4
  split at h
  · cases h; exact TagCS.of_st s1
  · obtain ⟨u, g5, h5, h6⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
    rw [← h6.2]
    have G : GateTag (S := S) (Map := Map) R o1 (medeGate som) := fun oL s gA gB hg _ => by
      unfold medeGate at hg
      exact StepTag.of_k (KC.bind' (kc_sureRequireLook _) fun _ => kc_medeLoop _ _ _)
        (KT.bind' (kt_sureRequireLook _) fun _ => kt_medeLoop _ _ _)
        (KD.bind' (kd_sureRequireLook _) fun _ => kd_medeLoop _ _ _) hg
    exact TagCS.of_st (s1.trans (walkLazy_tag G o1 laz _ g5 h5 (Or.inl rfl) (fun e hm => (he e hm).st s1)))

/-! ## The labels of `+split` and `+copy-lazy` -/

theorem bondEntries_filter_sub (p : Nat × Lazy S → Bool) :
    ∀ (b : List (Nat × Lazy S)) (e : Nat × Lazy S), e ∈ bondEntries (b.filter p) → e ∈ bondEntries b
  | [], e, h => by simp [bondEntries] at h
  | (o, l) :: rest, e, h => by
    rw [List.filter_cons] at h
    split at h
    · simp only [bondEntries, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (bondEntries_filter_sub p rest e h)
    · simp only [bondEntries, List.mem_append]
      exact Or.inr (bondEntries_filter_sub p rest e h)

theorem forkEntries_filter_sub (p : ForkE S → Bool) :
    ∀ (f : List (ForkE S)) (e : Nat × Lazy S), e ∈ forkEntries (f.filter p) → e ∈ forkEntries f
  | [], e, h => by simp [forkEntries] at h
  | ((oy, y), (on, n)) :: rest, e, h => by
    rw [List.filter_cons] at h
    split at h
    · simp only [forkEntries, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (forkEntries_filter_sub p rest e h)
    · simp only [forkEntries, List.mem_append]
      exact Or.inr (forkEntries_filter_sub p rest e h)

theorem entries_prune_sub (l : Lazy S) (e : Nat × Lazy S) (h : e ∈ entries (lazyPrune l)) : e ∈ entries l := by
  rcases l with ⟨s, f, b⟩
  simp only [lazyPrune, sure_mk, fork_mk, bond_mk, entries, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (bondEntries_filter_sub _ _ _ h)
  · exact Or.inr (forkEntries_filter_sub _ _ _ h)

/-- The entries of a fork's two needs are among the entries of its list. -/
theorem forkChild_sub : ∀ (fk : List (ForkE S)) (e : ForkE S), e ∈ fk →
    (∀ x ∈ entries e.1.2, x ∈ forkEntries fk) ∧ (∀ x ∈ entries e.2.2, x ∈ forkEntries fk)
  | [], e, h => absurd h (List.not_mem_nil)
  | ((oy, y), (on, n)) :: rest, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨fun x hx => by simp [forkEntries, hx], fun x hx => by simp [forkEntries, hx]⟩
    · obtain ⟨a, b⟩ := forkChild_sub rest e h
      exact ⟨fun x hx => by simp [forkEntries, a x hx], fun x hx => by simp [forkEntries, b x hx]⟩

/-- The entries of a bond's need are among the entries of its list. -/
theorem bondChild_sub : ∀ (bd : List (Nat × Lazy S)) (e : Nat × Lazy S), e ∈ bd →
    ∀ x ∈ entries e.2, x ∈ bondEntries bd
  | [], e, h => absurd h (List.not_mem_nil)
  | (o, l) :: rest, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact fun x hx => by simp [bondEntries, hx]
    · exact fun x hx => by simp [bondEntries, bondChild_sub rest e h x hx]

/-- `tags`, `cond` and `drop` kept. -/
def Keep3 (g g' : Gen Map) : Prop := g'.tags = g.tags ∧ g'.cond = g.cond ∧ g'.drop = g.drop

theorem Keep3.trans {a b c : Gen Map} (x : Keep3 a b) (y : Keep3 b c) : Keep3 a c :=
  ⟨y.1.trans x.1, y.2.1.trans x.2.1, y.2.2.trans x.2.2⟩

mutual
/-- **The halves of `+split` have their entries at labels of the input's
entries**, and the split keeps `tags`, `cond` and `drop`. -/
theorem splitLoop_lab {Q : Nat → Prop} : ∀ (l : Lazy S) (o : Nat) (g g' : Gen Map) (x : Lazy S × Lazy S),
    splitLoop l o g = some (x, g') → (∀ e ∈ entries l, Q e.1) →
    Keep3 g g' ∧ (∀ e ∈ entries x.1, Q e.1) ∧ (∀ e ∈ entries x.2, Q e.1)
  | mk s f b, o, g, g', x, h, hq => by
    rw [splitLoop] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    have k1 : Keep3 g g1 :=
      ⟨(kt_splitSure s o).keep _ _ _ h1, (kc_splitSure s o).keep _ _ _ h1, (kd_splitSure s o).keep _ _ _ h1⟩
    cases hfb : (f.isEmpty && b.isEmpty)
    · simp only [fork_mk, bond_mk, hfb, Bool.false_eq_true, if_false] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have F := splitForks_lab f g1 g2 _ h2 (fun e he => hq e (by simp only [entries, List.mem_append]; exact Or.inr he))
      have B := splitBonds_lab b g2 g3 _ h3 (fun e he => hq e (by simp only [entries, List.mem_append]; exact Or.inl he))
      refine ⟨(k1.trans F.1).trans B.1, fun e he => ?_, fun e he => ?_⟩
      · have he' := entries_prune_sub _ e he
        simp only [entries, List.mem_append] at he'
        rcases he' with a | a
        · exact B.2.1 e a
        · exact F.2.1 e a
      · have he' := entries_prune_sub _ e he
        simp only [entries, List.mem_append] at he'
        rcases he' with a | a
        · exact B.2.2 e a
        · exact F.2.2 e a
    · simp only [fork_mk, bond_mk, hfb, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨k1, fun e he => by simp [entries_ofSure] at he, fun e he => by simp [entries_ofSure] at he⟩

theorem splitForks_lab {Q : Nat → Prop} : ∀ (f : List (ForkE S)) (g g' : Gen Map)
    (x : List (ForkE S) × List (ForkE S)),
    splitForks f g = some (x, g') → (∀ e ∈ forkEntries f, Q e.1) →
    Keep3 g g' ∧ (∀ e ∈ forkEntries x.1, Q e.1) ∧ (∀ e ∈ forkEntries x.2, Q e.1)
  | [], g, g', x, h, _ => by
    rw [splitForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨rfl, rfl, rfl⟩, fun e he => by simp [forkEntries] at he, fun e he => by simp [forkEntries] at he⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hq => by
    rw [splitForks] at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have Y := splitLoop_lab y oy g g1 _ h1 (fun e he => hq e (by simp [forkEntries, he]))
    have N := splitLoop_lab n on g1 g2 _ h2 (fun e he => hq e (by simp [forkEntries, he]))
    have Rr := splitForks_lab rest g2 g3 _ h3 (fun e he => hq e (by simp [forkEntries, he]))
    have qy : Q oy := hq (oy, y) (by simp [forkEntries])
    have qn : Q on := hq (on, n) (by simp [forkEntries])
    refine ⟨(Y.1.trans N.1).trans Rr.1, fun e he => ?_, fun e he => ?_⟩
    · simp only [forkEntries, List.mem_append, List.mem_cons] at he
      rcases he with ((rfl | he) | (rfl | he)) | he
      · exact qy
      · exact Y.2.1 e he
      · exact qn
      · exact N.2.1 e he
      · exact Rr.2.1 e he
    · simp only [forkEntries, List.mem_append, List.mem_cons] at he
      rcases he with ((rfl | he) | (rfl | he)) | he
      · exact qy
      · exact Y.2.2 e he
      · exact qn
      · exact N.2.2 e he
      · exact Rr.2.2 e he

theorem splitBonds_lab {Q : Nat → Prop} : ∀ (b : List (Nat × Lazy S)) (g g' : Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    splitBonds b g = some (x, g') → (∀ e ∈ bondEntries b, Q e.1) →
    Keep3 g g' ∧ (∀ e ∈ bondEntries x.1, Q e.1) ∧ (∀ e ∈ bondEntries x.2, Q e.1)
  | [], g, g', x, h, _ => by
    rw [splitBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨rfl, rfl, rfl⟩, fun e he => by simp [bondEntries] at he, fun e he => by simp [bondEntries] at he⟩
  | (o, l) :: rest, g, g', x, h, hq => by
    rw [splitBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have L1 := splitLoop_lab l o g g1 _ h1 (fun e he => hq e (by simp [bondEntries, he]))
    have Rr := splitBonds_lab rest g1 g2 _ h2 (fun e he => hq e (by simp [bondEntries, he]))
    have qo : Q o := hq (o, l) (by simp [bondEntries])
    refine ⟨L1.1.trans Rr.1, fun e he => ?_, fun e he => ?_⟩
    · simp only [bondEntries, List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | he
      · exact qo
      · exact L1.2.1 e he
      · exact Rr.2.1 e he
    · simp only [bondEntries, List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | he
      · exact qo
      · exact L1.2.2 e he
      · exact Rr.2.2 e he
end

mutual
/-- **`+copy-lazy` leaves entries at labels of its inputs' entries.** -/
theorem copyLazyL_lab {Q : Nat → Prop} (o : Nat) : ∀ (a b : Lazy S) (g g' : Gen Map) (l : Lazy S),
    copyLazyL o a b g = some (l, g') → (∀ e ∈ entries a, Q e.1) → (∀ e ∈ entries b, Q e.1) →
    ∀ e ∈ entries l, Q e.1
  | mk s1 f1 b1, second, g, g', l, h, ha, hb => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨_, g2, h2, h⟩ := bind_some h
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hbF : ∀ e ∈ forkEntries second.fork, Q e.1 := fun e he => hb e (by
      rcases second with ⟨_, _, _⟩; simp only [entries, List.mem_append, fork_mk] at he ⊢; exact Or.inr he)
    have hbB : ∀ e ∈ bondEntries second.bond, Q e.1 := fun e he => hb e (by
      rcases second with ⟨_, _, _⟩; simp only [entries, List.mem_append, bond_mk] at he ⊢; exact Or.inl he)
    have haF : ∀ e ∈ forkEntries f1, Q e.1 := fun e he => ha e (by
      simp only [entries, List.mem_append]; exact Or.inr he)
    have haB : ∀ e ∈ bondEntries b1, Q e.1 := fun e he => ha e (by
      simp only [entries, List.mem_append]; exact Or.inl he)
    have F : ∀ e ∈ forkEntries fork, Q e.1 := by
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1, pure_apply] at h3
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact haF
      · rw [if_neg c1] at h3
        by_cases c2 : f1.isEmpty = true
        · rw [if_pos c2, pure_apply] at h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          exact hbF
        · rw [if_neg c2] at h3
          obtain ⟨merged, g5, h5, h3⟩ := bind_some h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          intro e he
          rw [forkEntries_append] at he
          rcases List.mem_append.mp he with he | he
          · exact mergeForks_lab o _ (fun k e' hk => by
              obtain ⟨hm, -⟩ := mem_of_get_index _ hk
              exact ⟨fun x hx => hbF x ((forkChild_sub _ _ hm).1 x hx),
                fun x hx => hbF x ((forkChild_sub _ _ hm).2 x hx)⟩) f1 g2 g5 merged h5 haF e he
          · exact hbF e (forkEntries_filter_sub _ _ e he)
    have B : ∀ e ∈ bondEntries bond, Q e.1 := by
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1, pure_apply] at h4
        simp only [Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact haB
      · rw [if_neg c1] at h4
        by_cases c2 : b1.isEmpty = true
        · rw [if_pos c2, pure_apply] at h4
          simp only [Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          exact hbB
        · rw [if_neg c2] at h4
          obtain ⟨merged, g5, h5, h4⟩ := bind_some h4
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          intro e he
          rw [bondEntries_append] at he
          rcases List.mem_append.mp he with he | he
          · exact mergeBonds_lab o _ (fun k e' hk => by
              obtain ⟨hm, -⟩ := mem_of_get_index _ hk
              exact fun x hx => hbB x (bondChild_sub _ _ hm x hx)) b1 g3 g5 merged h5 haB e he
          · exact hbB e (bondEntries_filter_sub _ _ e he)
    intro e he
    simp only [entries, List.mem_append] at he
    rcases he with he | he
    · exact B e he
    · exact F e he

theorem mergeForks_lab {Q : Nat → Prop} (o : Nat) (idx : Map (ForkE S))
    (hidx : ∀ k e, HoonMap.get idx k = some e → (∀ x ∈ entries e.1.2, Q x.1) ∧ (∀ x ∈ entries e.2.2, Q x.1)) :
    ∀ (l : List (ForkE S)) (g g' : Gen Map) (r : List (ForkE S)),
    mergeForks idx l g = some (r, g') → (∀ e ∈ forkEntries l, Q e.1) → ∀ e ∈ forkEntries r, Q e.1
  | [], g, g', r, h, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro e he; simp [forkEntries] at he
  | ((oy, y), (on, n)) :: rest, g, g', r, h, hq => by
    rw [mergeForks] at h
    obtain ⟨e1, g1, h1, h⟩ := bind_some h
    obtain ⟨r1, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have R := mergeForks_lab o idx hidx rest g1 g2 r1 h2 (fun e he => hq e (by simp [forkEntries, he]))
    have qy : Q oy := hq (oy, y) (by simp [forkEntries])
    have qn : Q on := hq (on, n) (by simp [forkEntries])
    have E : Q e1.1.1 ∧ Q e1.2.1 ∧ (∀ x ∈ entries e1.1.2, Q x.1) ∧ (∀ x ∈ entries e1.2.2, Q x.1) := by
      cases hget : HoonMap.get idx oy with
      | none =>
        simp only [hget, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨qy, qn, fun x hx => hq x (by simp [forkEntries, hx]), fun x hx => hq x (by simp [forkEntries, hx])⟩
      | some v =>
        rcases v with ⟨⟨fst, my⟩, ⟨mon, mn⟩⟩
        simp only [hget] at h1
        by_cases hon : on = mon
        · rw [if_pos hon] at h1
          obtain ⟨y', g3, h3, h1⟩ := bind_some h1
          obtain ⟨n', g4, h4, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have I := hidx _ _ hget
          exact ⟨qy, qn, copyLazyL_lab oy y my g g3 y' h3 (fun x hx => hq x (by simp [forkEntries, hx])) I.1,
            copyLazyL_lab on n mn g3 g4 n' h4 (fun x hx => hq x (by simp [forkEntries, hx])) I.2⟩
        · rw [if_neg hon] at h1; cases h1
    rcases e1 with ⟨⟨a, ya⟩, ⟨b, nb⟩⟩
    intro e he
    simp only [forkEntries, List.mem_append, List.mem_cons] at he
    rcases he with ((rfl | he) | (rfl | he)) | he
    · exact E.1
    · exact E.2.2.1 e he
    · exact E.2.1
    · exact E.2.2.2 e he
    · exact R e he

theorem mergeBonds_lab {Q : Nat → Prop} (o : Nat) (idx : Map (Nat × Lazy S))
    (hidx : ∀ k e, HoonMap.get idx k = some e → ∀ x ∈ entries e.2, Q x.1) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Gen Map) (r : List (Nat × Lazy S)),
    mergeBonds idx l g = some (r, g') → (∀ e ∈ bondEntries l, Q e.1) → ∀ e ∈ bondEntries r, Q e.1
  | [], g, g', r, h, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro e he; simp [bondEntries] at he
  | (ob, l) :: rest, g, g', r, h, hq => by
    rw [mergeBonds] at h
    obtain ⟨e1, g1, h1, h⟩ := bind_some h
    obtain ⟨r1, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have R := mergeBonds_lab o idx hidx rest g1 g2 r1 h2 (fun e he => hq e (by simp [bondEntries, he]))
    have qo : Q ob := hq (ob, l) (by simp [bondEntries])
    have E : Q e1.1 ∧ (∀ x ∈ entries e1.2, Q x.1) := by
      cases hget : HoonMap.get idx ob with
      | none =>
        simp only [hget, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨qo, fun x hx => hq x (by simp [bondEntries, hx])⟩
      | some v =>
        rcases v with ⟨fst, m⟩
        simp only [hget] at h1
        obtain ⟨l', g3, h3, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨qo, copyLazyL_lab ob l m g g3 l' h3 (fun x hx => hq x (by simp [bondEntries, hx]))
          (hidx _ _ hget)⟩
    rcases e1 with ⟨a, la⟩
    intro e he
    simp only [bondEntries, List.mem_append, List.mem_cons] at he
    rcases he with (rfl | he) | he
    · exact E.1
    · exact E.2 e he
    · exact R e he
end

/-! ## The arms with a lazy need -/

/-- **`+split`** keeps `tags`, `cond`, `drop`, and its halves' entries'
blocks have tags with `R` as a suffix when the goal's have. -/
theorem splitL_tagC {R : List Nat} {nex : NextL S} {g g' : Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL nex g = some ((hed, tel, o), g')) (he : ∀ e ∈ entries nex.laz, TagOK R g e.1) :
    TagCS R g g' ∧ (∀ e ∈ entries hed, TagOK R g' e.1) ∧ (∀ e ∈ entries tel, TagOK R g' e.1) := by
  unfold splitL at h
  obtain ⟨o', g1, h1, h⟩ := bind_some h
  obtain ⟨⟨hd', tl'⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  have s1 : TagCS R g g1 := TagCS.of_k (KT.emit' _) (KC.emit' _) (KD.emit' _) h1
  obtain ⟨k, Hh, Ht⟩ := splitLoop_lab (Q := fun x => TagOK R g1 x) nex.laz o' g1 g2 _ h2
    (fun e hm => (he e hm).cs s1)
  have s2 : TagCS R g1 g2 := TagCS.of_eqs k.1 k.2.1 k.2.2
  exact ⟨s1.trans s2, fun e hm => (Hh e hm).cs s2, fun e hm => (Ht e hm).cs s2⟩

/-- **`+copy`** keeps `tags`, `cond`, `drop`, and its result's entries are
at labels of its two inputs' entries. -/
theorem copyL_tagC {R : List Nat} {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (h : copyL first second g = some (nex, g')) (h1 : ∀ e ∈ entries first.laz, TagOK R g e.1)
    (h2 : ∀ e ∈ entries second, TagOK R g e.1) : TagCS R g g' ∧ ∀ e ∈ entries nex.laz, TagOK R g' e.1 := by
  have s : TagCS R g g' := TagCS.of_k (kt_copyL _ _) (kc_copyL _ _) (kd_copyL _ _) h
  refine ⟨s, ?_⟩
  unfold copyL at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  obtain ⟨laz, g2, e2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have s1 : TagCS R g g1 := TagCS.of_k (KT.emit' _) (KC.emit' _) (KD.emit' _) e1
  intro e hm
  exact ((copyLazyL_lab (Q := fun x => TagOK R g1 x) o _ _ g1 g2 laz e2 (fun e hm => (h1 e hm).cs s1)
    (fun e hm => (h2 e hm).cs s1)) e hm).cs (TagCS.of_k (kt_copyLazyL _ _ _) (kc_copyLazyL _ _ _)
      (kd_copyLazyL _ _ _) e2)

/-- **`+past`** sets the tag of its new block to the region, and its
result's entries are that block and the input's entries. -/
theorem pastL_tagC {cod : Bell → Option Bool} {nex : NextL S} {nom : Nomm} {R : List Nat} {g g' : Gen Map}
    {nex' : NextL S} (hd : g.drop = false) (h : pastL cod nex nom R g = some (nex', g'))
    (he : ∀ e ∈ entries nex.laz, TagOK R g e.1) : TagCS R g g' ∧ ∀ e ∈ entries nex'.laz, TagOK R g' e.1 := by
  unfold pastL at h
  by_cases c : nex.laz.sure.ned = Need.none ∧ HoonSet.small nex.laz.sure.lok = true ∧ nex.laz.fork.isEmpty = true
  · rw [if_pos c, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TagCS.refl _ _, he⟩
  rw [if_neg c] at h
  cases hh : hinted cod nom with
  | none => simp only [hh] at h; cases h
  | some b =>
    cases b with
    | false =>
      simp only [hh, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨TagCS.refl _ _, he⟩
    | true =>
      simp only [hh] at h
      obtain ⟨o, g1, h1, h⟩ := bind_some h
      obtain ⟨u, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have s1 : TagCS R g g1 := TagCS.of_k (KT.emit' _) (KC.emit' _) (KD.emit' _) h1
      have d1 : g1.drop = false := s1.drop.trans hd
      rw [setTag_apply] at h2
      simp only [d1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      have et : g1.tagged o R = { g1 with tags := HoonMap.put g1.tags o R } := by
        simp only [Gen.tagged, d1, Bool.false_eq_true, ↓reduceIte]
      rw [et]
      have s2 : TagCS R g1 { g1 with tags := HoonMap.put g1.tags o R } := by
        refine ⟨fun x t ex => ?_, CondTag.refl _, rfl⟩
        simp only [HoonMap.get_put] at ex
        split at ex
        · cases ex; exact Or.inr (sfx_refl R)
        · exact Or.inl ex
      have hF : ∀ e ∈ forkEntries nex.laz.fork, e ∈ entries nex.laz := fun e hm => by
        rcases nex with ⟨⟨_, _, _⟩, _⟩
        simp only [entries, List.mem_append, fork_mk] at hm ⊢
        exact Or.inr hm
      have hB : ∀ e ∈ bondEntries nex.laz.bond, e ∈ entries nex.laz := fun e hm => by
        rcases nex with ⟨⟨_, _, _⟩, _⟩
        simp only [entries, List.mem_append, bond_mk] at hm ⊢
        exact Or.inl hm
      refine ⟨s1.trans s2, fun e hm => ?_⟩
      have hm' : e = (o, mk nex.laz.sure nex.laz.fork []) ∨ e ∈ forkEntries nex.laz.fork ∨
          e ∈ bondEntries nex.laz.bond := by
        simpa [entries, bondEntries, forkEntries, or_assoc] using hm
      rcases hm' with rfl | hm | hm
      · intro t et
        simp only [HoonMap.get_put, if_true] at et
        cases et; exact sfx_refl R
      · exact ((he e (hF e hm)).cs s1).cs s2
      · exact ((he e (hB e hm)).cs s1).cs s2

/-! ## The induction on the class -/

/-- **The tag invariant of a run under `%next`**: from a goal whose entries'
blocks have tags with the region as a suffix, the run sets only such tags,
adds only keys with such tags, and its result's entries' blocks have such
tags. -/
abbrev TagCA (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    g0.drop = false → (∀ e ∈ entries L, TagOK region g0 e.1) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    TagCS region g0 g1 ∧ ∀ e ∈ entries nex.laz, TagOK region g1 e.1

/-- **The `%0` case of `run` under `%next L th`.** -/
theorem runLC_n0_nextT (env : CallEnv) (sup : Option Nomm) (ax : Nat) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.n0 ax) (CGoalL.next L th) region : CM Map (NextL S)) =
      if ax = 0 then bombL (some th.there) else (do
        let nex ← simpleNextL (CGoalL.next L th)
        if ax = 1 then pure nex else
        match fromL ax nex.laz with
        | some laz => pure ⟨laz, nex.th⟩
        | Option.none => fun _ => Option.none) := rfl

/-- **The `%1` case of `run` under `%next L th`.** -/
theorem runLC_n1_nextT (env : CallEnv) (sup : Option Nomm) (k : Noun) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.n1 k) (CGoalL.next L th) region : CM Map (NextL S)) = (do
      let o ← medeL th k L
      pure ⟨ofSure Sure.bunt, jmp0 o⟩) := rfl

/-- **The cons case of `run` under `%next L th`.** -/
theorem runLC_cons_nextT (env : CallEnv) (sup : Option Nomm) (p q : Nomm) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.cons p q) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl

theorem noEntries_ofSure (s : Sure S) {Q : Nat × Lazy S → Prop} : ∀ e ∈ entries (ofSure s : Lazy S), Q e :=
  fun e he => by simp [entries_ofSure] at he

/-- **Every member of `CallTreeA` meets `TagCA`.** -/
theorem tagCA_callTreeA (env : CallEnv) {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) :
    TagCA (S := S) (Map := Map) env nm := by
  induction h with
  | n0 axe =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_n0_nextT] at hr
    by_cases a0 : axe = 0
    · rw [if_pos a0] at hr
      unfold bombL at hr
      obtain ⟨o, g', h1, h2⟩ := bind_some hr
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨TagCS.of_k (KT.emit' _) (KC.emit' _) (KD.emit' _) h1, noEntries_ofSure _⟩
    · rw [if_neg a0] at hr
      obtain ⟨n0, g', h1, h2⟩ := bind_some hr
      simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      by_cases a1 : axe = 1
      · rw [if_pos a1, pure_apply] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨TagCS.refl _ _, he⟩
      · rw [if_neg a1] at h2
        cases hl : fromL axe L with
        | none => simp only [hl] at h2; cases h2
        | some laz =>
          simp only [hl, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨TagCS.refl _ _, fun e hm => ?_⟩
          obtain ⟨l, _, he'⟩ := (fromL_ent axe _ _ hl).mem_right hm
          exact he (e.1, l) he'
  | n1 k =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_n1_nextT] at hr
    obtain ⟨o, g', h1, h2⟩ := bind_some hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨medeL_tagCS h1 he, noEntries_ofSure _⟩
  | cons _ _ ihp ihq =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_cons_nextT] at hr
    obtain ⟨⟨hed, tel, o⟩, g2, hs, hr⟩ := bind_some hr
    simp only at hr
    obtain ⟨nexh, g3, hph, hr⟩ := bind_some hr
    obtain ⟨nexq, g4, h4, hr⟩ := bind_some hr
    obtain ⟨nexq', g5, hp2, hr⟩ := bind_some hr
    obtain ⟨nexp, g6, h6, hcp⟩ := bind_some hr
    obtain ⟨S1, Hh, Ht⟩ := splitL_tagC hs he
    have d2 : g2.drop = false := S1.drop.trans d0
    obtain ⟨S2, Eh⟩ := pastL_tagC d2 hph Hh
    have d3 : g3.drop = false := S2.drop.trans d2
    obtain ⟨S3, Eq⟩ := ihq d3 (fun e hm => (Ht e hm).cs S2) h4
    have d4 : g4.drop = false := S3.drop.trans d3
    obtain ⟨S4, Eq'⟩ := pastL_tagC d4 hp2 Eq
    have d5 : g5.drop = false := S4.drop.trans d4
    obtain ⟨S5, Ep⟩ := ihp d5 (fun e hm => ((Eh e hm).cs S3).cs S4) h6
    obtain ⟨S6, Ec⟩ := copyL_tagC hcp Ep (fun e hm => (Eq' e hm).cs S5)
    exact ⟨S1.trans (S2.trans (S3.trans (S4.trans (S5.trans S6)))), Ec⟩
  | ind _ _ ihp ihq =>
    intro sup L th region g0 g1 nex d0 he hr
    obtain ⟨nex0, ga, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
      runLC_n2_none hr
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have S2 := kerf_tagCS h2 he
    have S3' := TagCS.of_k (R := region) (KT.emit' _) (KC.emit' _) (KD.emit' _) h3
    have S0 : TagCS region g2 { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } := TagCS.of_eqs rfl rfl rfl
    have S3 : TagCS region g2 g3 := S0.trans S3'
    have d3 : g3.drop = false := S3.drop.trans (S2.drop.trans d0)
    obtain ⟨S4, EF⟩ := ihq d3 (noEntries_ofSure _) h4
    have d4 : g4.drop = false := S4.drop.trans d3
    obtain ⟨S5, EF'⟩ := pastL_tagC d4 h5 EF
    have d5 : g5.drop = false := S5.drop.trans d4
    obtain ⟨S6, ES⟩ := ihp d5 (noEntries_ofSure _) h6
    obtain ⟨S7, Ec⟩ := copyL_tagC h7 ES (fun e hm => (EF' e hm).cs S6)
    exact ⟨S2.trans (S3.trans (S4.trans (S5.trans (S6.trans S7)))), Ec⟩
  | seven _ _ ihp ihq =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_n7] at hr
    obtain ⟨nx, g, h1, h2⟩ := bind_some hr
    simp only [NextL.goal] at h2
    obtain ⟨S1, E1⟩ := ihq d0 he h1
    obtain ⟨S2, E2⟩ := ihp (S1.drop.trans d0) E1 h2
    exact ⟨S1.trans S2, E2⟩
  | four _ ihp =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_n4_next] at hr
    obtain ⟨a, ga, ha, hr⟩ := bind_some hr
    obtain ⟨⟨pro, th'⟩, gb, hb, hr⟩ := bind_some hr
    obtain ⟨arg, gc, hc, hr⟩ := bind_some hr
    obtain ⟨o, gd, hd, hr⟩ := bind_some hr
    have Sa := TagCS.of_st (collapseL_tag ha he)
    have Sb : TagCS region ga gb := TagCS.of_k (by unfold collPick; kt) (by unfold collPick; kc)
      (by unfold collPick; kd) hb
    have Sc := TagCS.of_k (R := region) KT.re' KC.re' KD.re' hc
    have Sd := TagCS.of_k (R := region) (KT.emit' _) (KC.emit' _) (KD.emit' _) hd
    have dd : gd.drop = false := Sd.drop.trans (Sc.drop.trans (Sb.drop.trans (Sa.drop.trans d0)))
    obtain ⟨Sp, Ep⟩ := ihp dd (noEntries_ofSure _) hr
    exact ⟨Sa.trans (Sb.trans (Sc.trans (Sd.trans Sp))), Ep⟩
  | three _ ihp =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_n3_next] at hr
    by_cases cn : noneEquivalentL L = true
    · rw [if_pos cn] at hr; exact ihp d0 he hr
    · rw [if_neg cn] at hr
      obtain ⟨a, ga, ha, hr⟩ := bind_some hr
      have Sa := TagCS.of_st (collapseL_tag ha he)
      cases a with
      | none => cases hr
      | some x =>
        rcases x with ⟨r, o⟩
        simp only at hr
        obtain ⟨⟨z, o'⟩, gb, hb, hr⟩ := bind_some hr
        obtain ⟨r', gc, hc, hr⟩ := bind_some hr
        obtain ⟨oc, gd, hd, hr⟩ := bind_some hr
        have Sb := TagCS.of_k (R := region) (kt_forl _ _) (kc_forl _ _) (kd_forl _ _) hb
        have Sc := TagCS.of_k (R := region) KT.re' KC.re' KD.re' hc
        have Sd := TagCS.of_k (R := region) (KT.emit' _) (KC.emit' _) (KD.emit' _) hd
        have dd : gd.drop = false := Sd.drop.trans (Sc.drop.trans (Sb.drop.trans (Sa.drop.trans d0)))
        obtain ⟨Sp, Ep⟩ := ihp dd (noEntries_ofSure _) hr
        exact ⟨Sa.trans (Sb.trans (Sc.trans (Sd.trans Sp))), Ep⟩
  | five _ _ ihp ihq =>
    intro sup L th region g0 g1 nex d0 he hr
    rw [runLC_n5_next] at hr
    obtain ⟨rp, ga, ha, hr⟩ := bind_some hr
    obtain ⟨rq, gb, hb, hr⟩ := bind_some hr
    obtain ⟨o, gc, hc, hr⟩ := bind_some hr
    obtain ⟨nexq, gd, hd, hr⟩ := bind_some hr
    obtain ⟨nexq', ge, hpe, hr⟩ := bind_some hr
    obtain ⟨nexp, gf, hf, hcp⟩ := bind_some hr
    have Sa := TagCS.of_k (R := region) KT.re' KC.re' KD.re' ha
    have Sb := TagCS.of_k (R := region) KT.re' KC.re' KD.re' hb
    have Sc : TagCS region gb gc := by
      obtain ⟨a, gx, hx, hc⟩ := bind_some hc
      have Sx := TagCS.of_st (collapseL_tag hx (fun e hm => ((he e hm).cs Sa).cs Sb))
      cases a with
      | none =>
        simp only at hc
        by_cases ta : th.args = []
        · rw [if_pos ta] at hc
          exact Sx.trans (TagCS.of_k (KT.emit' _) (KC.emit' _) (KD.emit' _) hc)
        · rw [if_neg ta] at hc; cases hc
      | some x =>
        rcases x with ⟨r, o1⟩
        simp only at hc
        obtain ⟨⟨z, o'⟩, gy, hy, hc⟩ := bind_some hc
        exact Sx.trans ((TagCS.of_k (kt_forl _ _) (kc_forl _ _) (kd_forl _ _) hy).trans
          (TagCS.of_k (KT.emit' _) (KC.emit' _) (KD.emit' _) hc))
    have dc : gc.drop = false := Sc.drop.trans (Sb.drop.trans (Sa.drop.trans d0))
    obtain ⟨Sd, Eq⟩ := ihq dc (noEntries_ofSure _) hd
    have dd : gd.drop = false := Sd.drop.trans dc
    obtain ⟨Se, Eq'⟩ := pastL_tagC dd hpe Eq
    have de : ge.drop = false := Se.drop.trans dd
    obtain ⟨Sf, Ep⟩ := ihp de (noEntries_ofSure _) hf
    obtain ⟨Sg, Ec⟩ := copyL_tagC hcp Ep (fun e hm => (Eq' e hm).cs Sf)
    exact ⟨Sa.trans (Sb.trans (Sc.trans (Sd.trans (Se.trans (Sf.trans Sg))))), Ec⟩

/-- **`TagLSP` of every member of `CallTreeA`.** -/
theorem tagLSP_callTreeA (env : CallEnv) {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) :
    TagLSP (S := S) (Map := Map) env nm :=
  fun hE _ _ d0 _ _ _ _ _ hr =>
    (tagCA_callTreeA env h d0 (fun e he => by rw [hE] at he; cases he) hr).1.cond

/-! ## Calling branches -/

/-- **`LOKSF` gives `LOKSE false`**: a goal with no entry is flag-free. -/
theorem LOKSF.toE {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSF (S := S) (Map := Map) lib N env P f nm) : LOKSE (S := S) (Map := Map) false lib N env P f nm := by
  refine ⟨fun _ hc hr => H.clean hc hr, fun {sup L th region g0 g1 nex} hE hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl
    hcs hr => ?_⟩
  obtain ⟨R, hne, -, hfl, hec⟩ := H.run (Or.inr hE) hcount b0 d0 hu hcl hcb h1 h2 hta (by rw [hE]; simp) hsd hsl
    (fun e he => by rw [hE] at he; cases he) (by rw [hE]; simp) (fun e he => by rw [hE] at he; cases he)
    (entries_nil_flat hE) hcs (fun e he => by rw [hE] at he; cases he) hr
  exact ⟨R, hne, hfl, hec⟩

/-- **`NoEnt` gives the bound `0` on the entries.** -/
theorem entLS_of_noEnt {env : CallEnv} {nm : Nomm} (h : NoEnt (S := S) (Map := Map) env nm) :
    EntLS (S := S) (Map := Map) env nm 0 := by
  intro sup L th region g0 g1 nex hE hr
  obtain ⟨s, rfl⟩ : ∃ s, L = ofSure s := ⟨_, eq_ofSure_of_entries hE⟩
  rw [h (goal := CGoal.next s th) trivial hr]
  simp

/-- **Every member of `CallTreeA` with `NoEntF` is a branch of phase S**
(`SixN` with the bound `0`): `LOKSE false` from `lokS_callTreeA`, the tag
clause from `tagLSP_callTreeA`, the bound from `noEnt_of_noEntF`. -/
theorem sixN_callTreeA (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) {b : Bool} {f : Noun}
    {nm : Nomm} (h : CallTreeA b f nm) (hn : NoEntF nm) : SixN (S := S) (Map := Map) lib N env P f nm 0 :=
  sixN_of_lokSE ((lokS_callTreeA (S := S) (Map := Map) lib (N := N) env h P).1.1.toE) (tagLSP_callTreeA env h)
    (entLS_of_noEnt (noEnt_of_noEntF env hn))

/-! ## The instance at the top -/

/-- `[6 [3 [0 2]] [2 [0 6] [0 7]] [0 3]]`, a `%6` whose yes branch calls,
meets `RunTE`. -/
theorem sixIndBr_runTE (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) (n2 (A 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3))
      (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3)) :=
  six_nextT lib env (pickD_three2 lib env P) (pickF_pure env rfl rfl)
    (sixN_callTreeA lib env P (CallTreeA.ind (CallTreeA.n0 6) (CallTreeA.n0 7))
      (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)))
    (sixN_of_uok lib env (uok_x lib (fragX_n0 (by decide)))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 3).annot P) hs gul tm r) rfl)
    (by decide)

/-- **`[4 [6 [3 [0 2]] [2 [0 6] [0 7]] [0 3]]]` meets both halves of the
contract**: a `%6` with a calling branch under `%next`, the operand of
`%4`. -/
theorem fourSixIndBr_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n4 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 4) (n4 (A 6) (n2 (A 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n4 (A 6) (n2 (A 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => four_doneT lib (sixIndBr_runTE lib env _) (minkC4_four lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

-- The whole-subject code of `fourSixIndBr_contract`'s nomm exists and
-- agrees with `+mink` on the 24 subjects of `CompSixLSCheck.lean`.
#guard SixCheck.sem [Nomm.n4 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none)
  (Nomm.n0 3))] == (1, 1, 24, 24)

end Comp
end SkaModel
end Formalization
