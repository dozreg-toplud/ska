import lemmas.Ska.CompGenSevenD
import lemmas.Ska.RawInvCLCopy

/-!
# The example's `q`: the shape of its result

README Gaps 12.39, item 10.  The `q` of the example `[7 [[0 2] [0 3]] [6 [2
[0 3] [0 2]] [0 2] [0 2]]]` is a `%6` with a calling test whose parts'
needs have no entries.  Its result under `%done` is the fork of the two
branches' (possibly wrapped) needs, and every node of that tree has at most
one bond and one fork: `labUniq_six_leaves` (`Raw.LabUniq`, the premise the
cons's `+copy` asks of its goal).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- A need without entries is `ofSure` of some sure need. -/
theorem exists_ofSure_of_entries {l : Lazy S} (h : entries l = []) : ∃ s, l = ofSure s :=
  ⟨_, eq_ofSure_of_entries h⟩

/-- **The result of `[6 c a b]` under `%done`, `c` a calling test of
`PickTree` and the branches without entries**: the fork of the two
branches' needs, plain or wrapped at the fork's labels. -/
theorem six_leaves_shape (env : CallEnv) {sup : Option Nomm} {fc : Noun} {c a b : Nomm} (hc : PickTree fc c)
    (hcn : NoEntF c) (ha : NoEntF a) (hb : NoEntF b) {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    ∃ (sx : Sure S) (y n : Nat) (s0 s1 : Sure S) (l0 l1 : Lazy S),
      nex.laz = mk sx [((y, l0), (n, l1))] [] ∧
      ((l0 = ofSure s0 ∧ l1 = ofSure s1) ∨
        (l0 = mk (Sure.bunt : Sure S) [] [(y, ofSure s0)] ∧ l1 = mk (Sure.bunt : Sure S) [] [(n, ofSure s1)])) := by
  obtain ⟨x1, x0, xc, g1, g2, g3, l0, l1, h1, h2, -, -, h3, hl01, hrest⟩ := runLC_six_done_apartW env sup h
  have e1 : entries x1.laz = [] := noEnt_of_noEntF (S := S) (Map := Map) env hb (goal := CGoal.done) trivial h1
  have e0 : entries x0.laz = [] := noEnt_of_noEntF (S := S) (Map := Map) env ha (goal := CGoal.done) trivial h2
  have ec : entries xc.laz = [] := pickTree_noEnt (S := S) (Map := Map) env hc hcn h3
  obtain ⟨s0, hs0⟩ := exists_ofSure_of_entries e0
  obtain ⟨s1, hs1⟩ := exists_ofSure_of_entries e1
  obtain ⟨sc, hsc⟩ := exists_ofSure_of_entries ec
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]
    rcases hl01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [e0, e1, List.length_append, List.length_cons, List.length_nil]; decide
    · simp only [entries_wrap, e0, e1, List.length_append, List.length_cons, List.length_nil]; decide
  have hcp := hrest hbig
  rw [copyL_six_apart xc l0 l1 g2.bo (g2.bo + 1) g3 (by rw [hsc]; simp [ofSure])] at hcp
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  refine ⟨⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩, g2.bo, g2.bo + 1, s0, s1, l0, l1, ?_, ?_⟩
  · rw [hsc]; rfl
  · rcases hl01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hs0, hs1⟩
    · exact Or.inr ⟨by rw [hs0], by rw [hs1]⟩

/-- **`LabUniq` of that result**: every node has at most one bond and one
fork. -/
theorem labUniq_six_leaves (env : CallEnv) {sup : Option Nomm} {fc : Noun} {c a b : Nomm} (hc : PickTree fc c)
    (hcn : NoEntF c) (ha : NoEntF a) (hb : NoEntF b) {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    Raw.LabUniq nex.laz := by
  obtain ⟨sx, y, n, s0, s1, l0, l1, hx, hl⟩ := six_leaves_shape env hc hcn ha hb h
  rw [hx]
  intro e he
  rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [entries_six, ofSure, entries, bondEntries, forkEntries, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp
  · simp only [entries_six, entries_wrap, ofSure, entries, bondEntries, forkEntries, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The example's `q`. -/
theorem labUniq_exQ (env : CallEnv) {sup : Option Nomm} {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2))
      (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) : Raw.LabUniq nex.laz :=
  labUniq_six_leaves env (PickTree.ind (CallTreeA.n0 3) (CallTreeA.n0 2)) (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl))
    (NoEntF.pure rfl rfl) (NoEntF.pure rfl rfl) h

/-! ## `[7 p q]` under `%done` from a class of `p` -/

/-- **A `p` that only fronts its goal's labels, at any lazy goal** (the
shape `runOKGD_sevenG` takes): every run under `%next L th` from a goal of
`GoalG` whose registers are no keys of `cond`, with `LabUniq` (the
premise of the cons's `+copy`), from a state with the invariants of the
runs under `%done`, meets `RunOKGen` with `x = false`, grows as `GrowU`
and re-points none of the goal's entries. -/
abbrev NextGG (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    GoalG (Map := Map) L th g0 → (∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none) →
    (∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none) → Raw.LabUniq L →
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ Q : Wit, RunOKGen lib N P f L th Q false g0 g1 nex ∧ GrowU g0 g1 ∧
      ∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a

/-- **`[0 axe]` is in the class** (axis at least `2`). -/
theorem nextGG_n0 (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) {axe : Nat} (ha : 2 ≤ axe) :
    NextGG (S := S) (Map := Map) lib N env P (slot axe) (Nomm.n0 axe) := by
  intro sup region g0 g1 L th nex G hnc hec _ _ _ _ _ _ h
  rw [runLC_n0_next_from env sup ha] at h
  obtain ⟨L', hf, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have M0 : MinkEq lib P (slot axe) (Nomm.n0 axe) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 axe).annot P) hs gul tm r
  exact ⟨_, runOKGen_n0 (N := N) lib M0 hf G hnc hec id, GrowU.refl _, fun _ _ => not_repointG_refl⟩

/-- **`[7 p q]` under `%done`**: `q` of `SixDG` (a `%6`, any test, labels of
its result possibly repeated) whose results are `LabUniq`, and `p` of
`NextGG` at the image of `p`'s formula. -/
theorem seven_doneGD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fp fq : Noun} {p q : Nomm} {k : Nat}
    (Hp : NextGG (S := S) (Map := Map) lib N env P fp p)
    (Hq : SixDG (S := S) (Map := Map) lib N env (Img lib P fp) fq q k)
    (Lq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLC env sup q (CGoalL.done : CGoalL S) region g0 = some (nx, g1) → Raw.LabUniq nx.laz)
    {sup : Option Nomm} {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n7 p q) (CGoalL.done : CGoalL S) region g0 = some (nex, g2)) :
    RunOKGD lib N P (n3 (A 7) fp fq) (CGoal.done : CGoal S) g0 g2 nex := by
  rw [runLC_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (Hq b0 d0 hu hcl hcb h1).1
  simp only [NextL.goal] at h2
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 Rq.ext.2.1
  obtain ⟨Q, Rp, hgu, hnr⟩ := Hp (Rq.goalOut b0 (fun r hr => hr.elim)) Rq.ncond Rq.econd (Lq h1) b1
    (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu) (hcl.growU Rq.grow) (Rq.cfr.below hcb) h2
  exact runOKGD_sevenG (minkC7_seven lib P fp fq) Rq Rp hgu hnr (fun r hr => hr.elim)

/-- **The contract of `[7 p q]`** for `p` of `NextGG` and `q` of `SixDG`
with `LabUniq` results. -/
theorem seven_contractGD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fp fq : Noun} {p q : Nomm}
    {k : Nat} (Hp : NextGG (S := S) (Map := Map) lib N env P fp p)
    (Hq : SixDG (S := S) (Map := Map) lib N env (Img lib P fp) fq q k)
    (Lq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLC env sup q (CGoalL.done : CGoalL S) region g0 = some (nx, g1) → Raw.LabUniq nx.laz)
    {c : Straight Map} (hc : finishLUC (S := S) env (Nomm.n7 p q) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 7) fp fq) [s] c ∧ ContractBwd lib N s (n3 (A 7) fp fq) [s] c :=
  finishLUC_contractGD lib N (fun hr => seven_doneGD lib env Hp Hq Lq (by simp [gen0]) rfl upBelow_gen0 clear_gen0
    condBelow_gen0 hr) hc

end Comp
end SkaModel
end Formalization
