import lemmas.Ska.CompTagX
import lemmas.Ska.CompDropKeep
import lemmas.Ska.CompSectSkip

/-!
# The tags of the proxies a run makes

README Gaps 12.2 (ninth session), step 2 of the plan: the tag invariant that
lets `+sect` skip every proxy the branches of a `%6` under a fork-free
`%next` made.

* `CondTag R c0 c1`: every key of `c1` has the tag it had in `c0`, or a tag
  with the region `R` as a suffix.
* `proxy_tag`, `collapseGate_tag`, `walkLazy_tag`, `collapseL_tag`: a proxy
  of `+collapse-lazy-atom` takes the tag of the lazy block it is read in, so
  when every lazy block of the need has a tag with `R` as a suffix, so has
  every key the collapse adds (`tags` and `drop` kept).
* `condTag_fragX`: a run of `FragX` adds no key.  `condTag_seven4`:
  `[7 [4 p] q]` with `p`, `q` in `FragX` for a fork-free goal adds keys only
  in the lazy blocks of `q`'s result, whose tags have the region as a suffix
  (`runX_tags`).
* `sect_h0`, `sect_h1`: the hypotheses of `sect_specV` from `CondTag` of
  the two branches with the region `rid :: region`.

Tested on the real compiler by `tools/hoon/tagkeep.py`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relations -/

/-- The tag of block `o` has `R` as a suffix. -/
def TagOK (R : List Nat) (g : Gen Map) (o : Nat) : Prop :=
  ∀ t, HoonMap.get g.tags o = some t → Sfx R t

/-- **Every key of `c1` has its tag in `c0` or one with `R` as a suffix.** -/
def CondTag (R : List Nat) (c0 c1 : Map (Nat × List Nat)) : Prop :=
  ∀ k d t, HoonMap.get c1 k = some (d, t) → (∃ d', HoonMap.get c0 k = some (d', t)) ∨ Sfx R t

theorem CondTag.refl {R : List Nat} (c : Map (Nat × List Nat)) : CondTag R c c :=
  fun _ d _ e => Or.inl ⟨d, e⟩

theorem CondTag.of_eq {R : List Nat} {c0 c1 : Map (Nat × List Nat)} (h : c1 = c0) : CondTag R c0 c1 := by
  rw [h]; exact CondTag.refl _

theorem CondTag.trans {R : List Nat} {c0 c1 c2 : Map (Nat × List Nat)} (a : CondTag R c0 c1)
    (b : CondTag R c1 c2) : CondTag R c0 c2 := fun k d t e =>
  (b k d t e).elim (fun ⟨d', e1⟩ => a k d' t e1) Or.inr

theorem CondTag.mono {R R' : List Nat} (hR : ∀ t, Sfx R' t → Sfx R t) {c0 c1 : Map (Nat × List Nat)}
    (h : CondTag R' c0 c1) : CondTag R c0 c1 := fun k d t e => (h k d t e).imp id (hR t)

/-- A step that keeps `tags` and `drop` and meets `CondTag`. -/
def StepTag (R : List Nat) (g g' : Gen Map) : Prop :=
  g'.tags = g.tags ∧ g'.drop = g.drop ∧ CondTag R g.cond g'.cond

theorem StepTag.refl {R : List Nat} (g : Gen Map) : StepTag R g g := ⟨rfl, rfl, CondTag.refl _⟩

theorem StepTag.trans {R : List Nat} {a b c : Gen Map} (x : StepTag R a b) (y : StepTag R b c) : StepTag R a c :=
  ⟨y.1.trans x.1, y.2.1.trans x.2.1, x.2.2.trans y.2.2⟩

theorem StepTag.of_k {R : List Nat} {α : Type} {m : CM Map α} (hc : KC m) (ht : KT m) (hd : KD m)
    {g g' : Gen Map} {x : α} (h : m g = some (x, g')) : StepTag R g g' :=
  ⟨ht.keep _ _ _ h, hd.keep _ _ _ h, CondTag.of_eq (hc.keep _ _ _ h)⟩

theorem TagOK.st {R : List Nat} {g g' : Gen Map} {o : Nat} (s : StepTag R g g') (h : TagOK R g o) :
    TagOK R g' o := fun t e => h t (by rw [s.1] at e; exact e)

/-! ## The collapse -/

/-- **A proxy takes the tag of the block it is read in.** -/
theorem proxy_tag {R : List Nat} {r o p : Nat} {g g' : Gen Map} (h : (proxy r o : CM Map Nat) g = some (p, g'))
    (ht : TagOK R g o) : StepTag R g g' := by
  unfold proxy at h
  dsimp only at h
  split at h
  · cases h; exact ⟨rfl, rfl, CondTag.refl _⟩
  · obtain ⟨tag, et, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    refine ⟨rfl, rfl, fun k d t ek => ?_⟩
    simp only [HoonMap.get_put] at ek
    split at ek
    · cases ek; exact Or.inr (ht _ et)
    · exact Or.inl ⟨d, ek⟩

/-- A gate of a walk that meets `StepTag` at `o` and at blocks whose tag has
`R` as a suffix. -/
def GateTag (R : List Nat) (o : Nat) (f : Nat → Sure S → CM Map Unit) : Prop :=
  ∀ oL s (g g' : Gen Map), f oL s g = some ((), g') → (oL = o ∨ TagOK R g oL) → StepTag R g g'

theorem collapseGate_tag (R : List Nat) (r o : Nat) : GateTag (S := S) (Map := Map) R o (collapseGate r o) := by
  intro oL s g g' h hL
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h⟩ := bind_some h
  have s1 : StepTag R g g1 := StepTag.of_k (kc_sureRequireLook _) (kt_sureRequireLook _) (kd_sureRequireLook _) h1
  have hL1 : oL = o ∨ TagOK R g1 oL := hL.imp id (fun ht => ht.st s1)
  have src : ∀ (gA : Gen Map) (x : Nat) (gB : Gen Map), (oL = o ∨ TagOK R gA oL) →
      (if oL = o then pure r else proxy r oL : CM Map Nat) gA = some (x, gB) → StepTag R gA gB := by
    intro gA x gB hA hs
    by_cases e : oL = o
    · rw [if_pos e] at hs; cases hs; exact StepTag.refl _
    · rw [if_neg e] at hs; exact proxy_tag hs (hA.resolve_left e)
  split at h
  · cases h; exact s1
  · split at h
    · cases h; exact s1
    · obtain ⟨x, g2, h2, h3⟩ := bind_some h
      exact s1.trans ((src g1 x g2 hL1 h2).trans (StepTag.of_k (KC.addOps' _ _) (KT.addOps' _ _) (KD.addOps' _ _) h3))
  · obtain ⟨x, g2, h2, h3⟩ := bind_some h
    exact s1.trans ((src g1 x g2 hL1 h2).trans
      (StepTag.of_k (kc_crashNeed _ _ _) (kt_crashNeed _ _ _) (kd_crashNeed _ _ _) h3))

mutual
/-- **A walk whose gate meets `GateTag`** meets `StepTag` when its root is
`o` or has a good tag and every lazy block below it has one. -/
theorem walkLazy_tag {R : List Nat} {o : Nat} {f : Nat → Sure S → CM Map Unit} (hf : GateTag (Map := Map) R o f) :
    ∀ (o0 : Nat) (l : Lazy S) (g g' : Gen Map), walkLazy f o0 l g = some ((), g') →
    (o0 = o ∨ TagOK R g o0) → (∀ e ∈ entries l, TagOK R g e.1) → StepTag R g g'
  | o0, mk s fk bd, g, g', h, h0, he => by
    unfold walkLazy at h
    obtain ⟨u, g1, h1, hr⟩ := bind_some h
    have W1 := hf o0 s g g1 h1 h0
    split at hr
    · cases hr; exact W1
    · obtain ⟨u2, g2, h2, h3⟩ := bind_some hr
      have WF := walkForks_tag hf fk g1 g2 h2 (fun e hm => (he e (by
        simp only [entries, List.mem_append]; exact Or.inr hm)).st W1)
      have WB := walkBonds_tag hf bd g2 g' h3 (fun e hm => ((he e (by
        simp only [entries, List.mem_append]; exact Or.inl hm)).st W1).st WF)
      exact W1.trans (WF.trans WB)

theorem walkForks_tag {R : List Nat} {o : Nat} {f : Nat → Sure S → CM Map Unit} (hf : GateTag (Map := Map) R o f) :
    ∀ (fk : List (ForkE S)) (g g' : Gen Map), walkForks f fk g = some ((), g') →
    (∀ e ∈ forkEntries fk, TagOK R g e.1) → StepTag R g g'
  | [], g, g', h, _ => by
    simp only [walkForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact StepTag.refl _
  | ((oy, y), (on, n)) :: rest, g, g', h, he => by
    unfold walkForks at h
    obtain ⟨u1, g1, h1, h⟩ := bind_some h
    obtain ⟨u2, g2, h2, h3⟩ := bind_some h
    have Wy := walkLazy_tag hf oy y g g1 h1 (Or.inr (he (oy, y) (by simp [forkEntries])))
      (fun e hm => he e (by simp [forkEntries, hm]))
    have Wn := walkLazy_tag hf on n g1 g2 h2 (Or.inr ((he (on, n) (by simp [forkEntries])).st Wy))
      (fun e hm => (he e (by simp [forkEntries, hm])).st Wy)
    have Wr := walkForks_tag hf rest g2 g' h3 (fun e hm => ((he e (by simp [forkEntries, hm])).st Wy).st Wn)
    exact Wy.trans (Wn.trans Wr)

theorem walkBonds_tag {R : List Nat} {o : Nat} {f : Nat → Sure S → CM Map Unit} (hf : GateTag (Map := Map) R o f) :
    ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map), walkBonds f bd g = some ((), g') →
    (∀ e ∈ bondEntries bd, TagOK R g e.1) → StepTag R g g'
  | [], g, g', h, _ => by
    simp only [walkBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact StepTag.refl _
  | (ob, l) :: rest, g, g', h, he => by
    unfold walkBonds at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have Wl := walkLazy_tag hf ob l g g1 h1 (Or.inr (he (ob, l) (by simp [bondEntries])))
      (fun e hm => he e (by simp [bondEntries, hm]))
    have Wr := walkBonds_tag hf rest g1 g' h2 (fun e hm => (he e (by simp [bondEntries, hm])).st Wl)
    exact Wl.trans Wr
end

/-- **`+collapse-lazy-atom` adds keys with the tags of the lazy blocks of
the need** (and keeps `tags` and `drop`). -/
theorem collapseL_tag {R : List Nat} {nex : NextL S} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtomL nex g = some (a, g')) (he : ∀ e ∈ entries nex.laz, TagOK R g e.1) :
    StepTag R g g' := by
  rcases nex with ⟨⟨s0, f0, b0⟩, th⟩
  unfold collapseLazyAtomL at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h; exact StepTag.refl _
  obtain ⟨ned, g1, h1, h⟩ := bind_some h
  have s1 : StepTag R g g1 := StepTag.of_k (kc_sureRequireLook _) (kt_sureRequireLook _) (kd_sureRequireLook _) h1
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have s2 : StepTag R g1 g2 := StepTag.of_k (by split <;> kc) (by split <;> kt) (by split <;> kd) h2
  obtain ⟨g3, g3', h3, h⟩ := bind_some h
  simp only [get, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  split at h
  · cases h; exact s1.trans s2
  · obtain ⟨u, g4, h4, h⟩ := bind_some h
    have W : StepTag R g2 g4 := walkLazy_tag (collapseGate_tag R r there) there _ g2 g4 h4 (Or.inl rfl)
      (by intro e hm; exact ((he e (by simpa [entries] using hm)).st s1).st s2)
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact (s1.trans s2).trans W

/-! ## The runs -/

/-- **A run of `FragX` for a fork-free goal adds no key to `cond`.** -/
theorem condTag_fragX {nm : Nomm} (hf : FragX (S := S) nm) {goal : CGoal S} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re goal) (hc : sixCount nm ≤ 255)
    (h : runL nm (CGoal.toL goal) region g0 = some (nex, g1)) : CondTag region g0.cond g1.cond :=
  CondTag.of_eq (runX_keeps hf hd hg hc h).cnd

/-- **`[7 [4 p] q]` with `p`, `q` in `FragX`, for a fork-free goal with
region `R`, adds only keys whose tags have `R` as a suffix**: the proxies of
the collapse are read in the lazy blocks of `q`'s result (`runX_tags`). -/
theorem condTag_seven4 {p q : Nomm} (hp : FragX (S := S) p) (hq : FragX (S := S) q) {goal : CGoal S}
    {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S} (d0 : g0.drop = false) (hg : GoalIn g0.re goal)
    (hc : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255)
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoal.toL goal) region g0 = some (nex, g2)) :
    CondTag region g0.cond g2.cond := by
  have hc' : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Kq := runX_keeps hq d0 hg hc'.2 h1
  have Tq := runX_tags hq d0 hg hc'.2 h1
  have d1 := Kq.keeps.dropF d0
  simp only [NextL.goal] at h2
  unfold runL at h2
  obtain ⟨a, ga, ha, h⟩ := bind_some h2
  have sa := collapseL_tag (R := region) ha (fun e he => Tq.ent e he)
  obtain ⟨⟨pro, th'⟩, gb, hb, h⟩ := bind_some h
  have sb : StepTag region ga gb := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact StepTag.refl _
    | none =>
      simp only at hb
      obtain ⟨r, g3, h3, hb⟩ := bind_some hb
      have s3 : StepTag region ga g3 := StepTag.of_k KC.re' KT.re' KD.re' h3
      split at hb
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨_, rfl⟩ := hb
        exact s3
      · cases hb
  obtain ⟨arg, gc, hc3, h⟩ := bind_some h
  obtain ⟨o, gd, hd4, h⟩ := bind_some h
  have sc : StepTag region gb gc := StepTag.of_k KC.re' KT.re' KD.re' hc3
  have sd : StepTag region gc gd := StepTag.of_k (KC.emit' _) (KT.emit' _) (KD.emit' _) hd4
  have dd : gd.drop = false := by rw [sd.2.1, sc.2.1, sb.2.1, sa.2.1]; exact d1
  obtain ⟨e3, q3, _⟩ := keeps_re hc3
  have red : gd.re = gc.re := by
    rw [emit_apply] at hd4
    simp only [Option.some.injEq, Prod.mk.injEq] at hd4
    obtain ⟨_, rfl⟩ := hd4
    rfl
  have Kp := runX_keeps hp (goal := CGoal.next (lazyReg arg) (jmp0 o)) dd
    ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ hc'.1 h
  exact (CondTag.of_eq Kq.cnd).trans (sa.2.2.trans (sb.2.2.trans (sc.2.2.trans (sd.2.2.trans
    (CondTag.of_eq Kp.cnd)))))

/-! ## `+sect` -/

/-- **The keys the yes branch made name `rid`**, when it meets `CondTag` with
the region `rid :: region` from the state between the branches. -/
theorem sect_h0 {rid : Nat} {region : List Nat} {cw : Map (Nat × List Nat)} {g : Gen Map}
    (ha : CondTag (rid :: region) cw g.cond) :
    ∀ rid' rest, rid :: region = rid' :: rest → ∀ k df tag, HoonMap.get (difM g.cond cw) k = some (df, tag) →
      rid' ∈ tag := by
  intro rid' rest e k df tag hk
  obtain ⟨rfl, rfl⟩ := List.cons.inj e
  rw [difM, get_foldl_del] at hk
  split at hk
  · cases hk
  · rename_i hn
    rcases ha k df tag hk with ⟨d', e'⟩ | s
    · exact absurd ((HoonMapKeys.mem_keys cw k).mpr (by simp [e'])) hn
    · exact s.mem

/-- **The keys the no branch made name `rid`.** -/
theorem sect_h1 {rid : Nat} {region : List Nat} {cb cw : Map (Nat × List Nat)}
    (hb : CondTag (rid :: region) cb cw) :
    ∀ rid' rest, rid :: region = rid' :: rest → ∀ k df tag, HoonMap.get (difM cw cb) k = some (df, tag) →
      rid' ∈ tag := by
  intro rid' rest e k df tag hk
  obtain ⟨rfl, rfl⟩ := List.cons.inj e
  rw [difM, get_foldl_del] at hk
  split at hk
  · cases hk
  · rename_i hn
    rcases hb k df tag hk with ⟨d', e'⟩ | s
    · exact absurd ((HoonMapKeys.mem_keys cb k).mpr (by simp [e'])) hn
    · exact s.mem

end Comp
end SkaModel
end Formalization
