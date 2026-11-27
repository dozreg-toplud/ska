import lemmas.Ska.CompGenSevenD
import lemmas.Ska.RawInvCLCopy
import lemmas.Ska.CompGenOne

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

/-! ## `Clean` needs of the example's `q` -/

/-- **The needs of that result are `Clean`**: the sure need is the test's
(`PickOK.clean`), the branches' needs are clean (`DoneOK.clean`), the
wrappers' `bunt`. -/
theorem clean_six_leaves (lib : Lib) (N : Needs) (env : CallEnv) {sup : Option Nomm} {fc : Noun} {c : Nomm}
    {ba bb : Bool} {fa fb : Noun} {a b : Nomm} (hc : PickTree fc c) (hcn : NoEntF c)
    (ta : CallTreeA ba fa a) (ha : NoEntF a) (tb : CallTreeA bb fb b) (hb : NoEntF b)
    {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb0 : CondBelow g0)
    (h : runLC env sup (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    Clean nex.laz.sure.ned ∧ ∀ e ∈ entries nex.laz, Clean e.2.sure.ned := by
  obtain ⟨x1, x0, xc, g1, g2, g3, l0, l1, h1, h2, hx0a, hx1a, h3, hl01, hrest⟩ := runLC_six_done_apartW env sup h
  have Db := callTreeA_done lib (N := N) env tb (fun _ => True) b0 d0 hu hcl0 hcb0 h1
  have Rb := Db.run
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 Rb.ext.2.1
  have cl1 : Clear g1 := hcl0.growU Rb.grow
  have cb1 : CondBelow g1 := Rb.cfr.below hcb0
  have Da := callTreeA_done lib (N := N) env ta (fun _ => True) b1 d1 u1 cl1 cb1 h2
  have Ra := Da.run
  have lo0 : 1 ≤ x0.th.there := Ra.lo
  have hi0 : x0.th.there < g2.bo := Ra.hi
  have lo1 : 1 ≤ x1.th.there := Rb.lo
  have hi1 : x1.th.there < g1.bo := Rb.hi
  have cl2 : Clear g2 := cl1.growU Ra.grow
  have cb2 : CondBelow g2 := Ra.cfr.below cb1
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop lo0 hi0)
    (jumpsBelow_hop lo1 (by omega))).toU u2
  have uG : UpBelow (sixGenL g2 x0.th x1.th region) := GU.up u2
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  have Dc := pickTree_pick lib (N := N) env hc (fun _ => True) (z := jmp0 g2.bo) (o := jmp0 (g2.bo + 1))
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩ ⟨rfl, rfl⟩
    (by simp only [sixGenL_bo]; omega) dG uG (cl2.growU GU)
    (fun k hk => by simp only [sixGenL_cond, sixGenL_re] at hk ⊢; exact cb2 k hk) h3
  have e1 : entries x1.laz = [] := noEnt_of_noEntF (S := S) (Map := Map) env hb (goal := CGoal.done) trivial h1
  have e0 : entries x0.laz = [] := noEnt_of_noEntF (S := S) (Map := Map) env ha (goal := CGoal.done) trivial h2
  have ec : entries xc.laz = [] := pickTree_noEnt (S := S) (Map := Map) env hc hcn h3
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
  refine ⟨Dc.clean, fun e he => ?_⟩
  rw [entries_copy_six, ec, List.nil_append] at he
  have cbunt : Clean (Sure.bunt : Sure S).ned := by simp [Sure.bunt, Clean]
  rcases hl01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [e0, e1, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl
    · exact Da.clean
    · exact Db.clean
  · simp only [entries_wrap, e0, e1, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact cbunt
    · exact Da.clean
    · exact cbunt
    · exact Db.clean

/-- **What `[7 p q]` asks of the example's `q`**: `LabUniq` and `Clean`. -/
theorem shape_exQ (lib : Lib) (N : Needs) (env : CallEnv) {sup : Option Nomm} {region : List Nat} {g0 g4 : Gen Map}
    {nex : NextL S} (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2))
      (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    Raw.LabUniq nex.laz ∧ Clean nex.laz.sure.ned ∧ ∀ e ∈ entries nex.laz, Clean e.2.sure.ned :=
  ⟨labUniq_exQ env h, clean_six_leaves lib N env (PickTree.ind (CallTreeA.n0 3) (CallTreeA.n0 2))
    (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)) (CallTreeA.n0 2) (NoEntF.pure rfl rfl) (CallTreeA.n0 2)
    (NoEntF.pure rfl rfl) b0 d0 hu hcl hcb h⟩


/-! ## `[7 p q]` under `%done` from a class of `p` -/

/-- **A `p` that only fronts its goal's labels, at any lazy goal** (the
shape `runOKGD_sevenG` takes): every run under `%next L th` from a goal of
`GoalG` whose registers are no keys of `cond`, with `LabUniq` and `Clean`
needs (the premises of the cons's `+copy`) and a jump without arguments
(`[1 k]` hops to it), from a state with the invariants of the
runs under `%done`, meets `RunOKGen` with `x = false`, grows as `GrowU`
and re-points none of the goal's entries. -/
abbrev NextGG (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    GoalG (Map := Map) L th g0 → (∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none) →
    (∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none) → Raw.LabUniq L →
    Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) → th.args = [] →
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ Q : Wit, RunOKGen lib N P f L th Q false g0 g1 nex ∧ GrowU g0 g1 ∧
      ∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a

/-- **`[0 axe]` is in the class** (axis at least `2`). -/
theorem nextGG_n0 (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) {axe : Nat} (ha : 2 ≤ axe) :
    NextGG (S := S) (Map := Map) lib N env P (slot axe) (Nomm.n0 axe) := by
  intro sup region g0 g1 L th nex G hnc hec _ _ _ _ _ _ _ _ _ h
  rw [runLC_n0_next_from env sup ha] at h
  obtain ⟨L', hf, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have M0 : MinkEq lib P (slot axe) (Nomm.n0 axe) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 axe).annot P) hs gul tm r
  exact ⟨_, runOKGen_n0 (N := N) lib M0 hf G hnc hec id, GrowU.refl _, fun _ _ => not_repointG_refl⟩

/-- **`[1 k]` is in the class.** -/
theorem nextGG_n1 (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (k : Noun) :
    NextGG (S := S) (Map := Map) lib N env P (quote k) (Nomm.n1 k) := by
  intro sup region g0 g1 L th nex G hnc hec _ _ _ hta _ d0 hu _ hcb h
  have M1 : MinkEq lib P (quote k) (Nomm.n1 k) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 k).annot P) hs gul tm r
  obtain ⟨-, R, hgu, hnr⟩ := runOKGen_n1 (N := N) lib M1 G hnc hec d0 hu hcb hta h id
  exact ⟨_, R, hgu, hnr⟩

/-- **`[7 p q]` under `%done`**: `q` of `SixDG` (a `%6`, any test, labels of
its result possibly repeated) whose results are `LabUniq` with `Clean`
needs, and `p` of
`NextGG` at the image of `p`'s formula. -/
theorem seven_doneGD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fp fq : Noun} {p q : Nomm} {k : Nat}
    (Hp : NextGG (S := S) (Map := Map) lib N env P fp p)
    (Hq : SixDG (S := S) (Map := Map) lib N env (Img lib P fp) fq q k)
    (Lq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
      runLC env sup q (CGoalL.done : CGoalL S) region g0 = some (nx, g1) →
      Raw.LabUniq nx.laz ∧ Clean nx.laz.sure.ned ∧ ∀ e ∈ entries nx.laz, Clean e.2.sure.ned)
    {sup : Option Nomm} {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n7 p q) (CGoalL.done : CGoalL S) region g0 = some (nex, g2)) :
    RunOKGD lib N P (n3 (A 7) fp fq) (CGoal.done : CGoal S) g0 g2 nex := by
  rw [runLC_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (Hq b0 d0 hu hcl hcb h1).1
  simp only [NextL.goal] at h2
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 Rq.ext.2.1
  obtain ⟨lu, cl, ecl⟩ := Lq b0 d0 hu hcl hcb h1
  have hta : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  obtain ⟨Q, Rp, hgu, hnr⟩ := Hp (Rq.goalOut b0 (fun r hr => hr.elim)) Rq.ncond Rq.econd lu cl ecl hta b1
    (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu) (hcl.growU Rq.grow) (Rq.cfr.below hcb) h2
  exact runOKGD_sevenG (minkC7_seven lib P fp fq) Rq Rp hgu hnr (fun r hr => hr.elim)

/-- **The contract of `[7 p q]`** for `p` of `NextGG` and `q` of `SixDG`
with `LabUniq` results. -/
theorem seven_contractGD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fp fq : Noun} {p q : Nomm}
    {k : Nat} (Hp : NextGG (S := S) (Map := Map) lib N env P fp p)
    (Hq : SixDG (S := S) (Map := Map) lib N env (Img lib P fp) fq q k)
    (Lq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
      runLC env sup q (CGoalL.done : CGoalL S) region g0 = some (nx, g1) →
      Raw.LabUniq nx.laz ∧ Clean nx.laz.sure.ned ∧ ∀ e ∈ entries nx.laz, Clean e.2.sure.ned)
    {c : Straight Map} (hc : finishLUC (S := S) env (Nomm.n7 p q) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 7) fp fq) [s] c ∧ ContractBwd lib N s (n3 (A 7) fp fq) [s] c :=
  finishLUC_contractGD lib N (fun hr => seven_doneGD lib env Hp Hq Lq (by simp [gen0]) rfl upBelow_gen0 clear_gen0
    condBelow_gen0 hr) hc


/-- **The example `[7 [[0 2] [0 3]] [6 [2 [0 3] [0 2]] [0 2] [0 2]]]`, from
the cons**: its contract follows from `NextGG` of the cons of two leaves
(`nextGG_cons0`, not proved yet: `CompGenConsE.lean` states the missing
`runOKGen_cons00`), with `sixDG_callTest` and `shape_exQ` for `q`. -/
theorem exCons_contract_of (lib : Lib) (env : CallEnv) (N : Needs)
    (Hp : NextGG (S := S) (Map := Map) lib N env (fun _ => True) (C (slot 2) (slot 3))
      (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)))
    {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env (Nomm.n7 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3))
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2))) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 7) (C (slot 2) (slot 3)) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2)))
        [s] c ∧
      ContractBwd lib N s (n3 (A 7) (C (slot 2) (slot 3)) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2)))
        [s] c :=
  have H := seven_contractGD lib env Hp (sixDG_callTest lib N env _)
    (fun b0 d0 hu hcl hcb h => shape_exQ lib N env b0 d0 hu hcl hcb h) hc
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
