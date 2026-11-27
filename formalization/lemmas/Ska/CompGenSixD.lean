import lemmas.Ska.CompGenTop
import lemmas.Ska.CompSixLSClass

/-!
# `[6 c a b]` under `%done` with any test, on the REAL result (`RunOKGD`)

README Gaps 12.39.  `six_doneGBW` (`CompSixLSWrap.lean`) states the relation
of a `%6` with a calling test on the UNWRAPPED result `nexU` (`WalkEq`),
since the wrapped fork of `+past-fork` repeats labels and `RunOKGB` asks
`nodup`.  `RunOKGD` (`CompGenTop.lean`) takes repeated labels (`LabDisj`,
`AgreeG` per label), so the relation is stated here on the result itself:

* `SixDG`, `SixD.toG`: `SixDW` with `RunOKGD` of the real result.
* `atL_apart`, `atL_cons_ne`, `atL_cons_eq`, `notMem_of_atL`, `FillSemL.mono`,
  `FillSemL.toOne` (a conjunction of one need and `bunt`s is that need),
  `AgreeG.part` (a part's `AgreeG` from the whole's, its labels apart from
  the other parts').
* `WrapL` (a branch's need, plain or wrapped at the fork's label) with
  `WrapL.cases`, `WrapL.atL_ne`, `WrapL.atL_self`, `WrapL.pairwise`.
* `sixBlk_fwdG`, `sixBlk_bwdG`: `sixBlk_fwd/bwd` with `RunOKGD` and `AgreeG`.
* `six_doneGD`: `six_doneGBW` on the real result.
* `sixDG_callTest`: the `q` of `[7 [[0 2] [0 3]] [6 [2 [0 3] [0 2]] [0 2] [0 2]]]`;
  `finishLUC_contractSixDG`, `sixCallTest22_contractG`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Needs at one label -/

theorem atL_apart {es : List (Nat × Lazy S)} {o : Nat} (h : ∀ e ∈ es, e.1 ≠ o) : atL es o = [] := by
  unfold atL
  rw [List.filter_eq_nil_iff.mpr (fun e he hd => h e he (of_decide_eq_true hd))]
  rfl

theorem atL_cons_ne {e : Nat × Lazy S} {es : List (Nat × Lazy S)} {o : Nat} (h : e.1 ≠ o) :
    atL (e :: es) o = atL es o := by
  simp [atL, List.filter_cons, h]

theorem atL_cons_eq (e : Nat × Lazy S) (es : List (Nat × Lazy S)) : atL (e :: es) e.1 = e.2.sure :: atL es e.1 := by
  simp [atL, List.filter_cons]

theorem notMem_of_atL {es : List (Nat × Lazy S)} {o : Nat} (h : atL es o = []) : o ∉ es.map Prod.fst := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have hf : e ∈ es.filter (fun x => decide (x.1 = e.1)) := List.mem_filter.mpr ⟨he, by simp⟩
  unfold atL at h
  rw [List.map_eq_nil_iff] at h
  rw [h] at hf
  cases hf

section Fill
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
  {ned : Need} {lo : Nat} {A : List Pole} {s0 s : Noun}

theorem FillSemL.mono {Ls : List (Sure S)} {lo' : Nat} (h : FillSemL lib O c gul st t ned lo Ls A s0 s)
    (hl : lo' ≤ lo) : FillSemL lib O c gul st t ned lo' Ls A s0 s :=
  fun R hR => ⟨fun f => by
    obtain ⟨R', r, hh, k⟩ := (h R hR).1 f
    exact ⟨R', r, hh, fun x hx hn => k x (hx.elim Or.inl fun e => Or.inr (Nat.lt_of_lt_of_le e hl)) hn⟩,
    (h R hR).2⟩

/-- **A conjunction of one need and `bunt`s fills that need.** -/
theorem FillSemL.toOne {Ls : List (Sure S)} {M : Sure S} (h : FillSemL lib O c gul st t ned lo Ls A s0 s)
    (hm : M ∈ Ls) (hb : ∀ L ∈ Ls, L = M ∨ L = Sure.bunt) : FillSem lib O c gul st t ned lo M A s0 s := by
  intro R hR
  refine ⟨fun f => ?_, fun nf => (h R hR).2 ⟨M, hm, nf⟩⟩
  obtain ⟨R', r, hh, k⟩ := (h R hR).1 (fun L hL => by
    rcases hb L hL with rfl | rfl
    · exact f
    · exact fitsS_bunt s)
  exact ⟨R', r, hh M hm, fun x hx hn => k x hx (fun L hL => by
    rcases hb L hL with rfl | rfl
    · exact hn
    · exact fun h' => by simp [Sure.bunt, NMem] at h')⟩

end Fill

/-- **A part's `AgreeG` from the whole's**: the part's blocks are the whole's
in its range, its entries are the whole's, and at every label of its range the
whole has the part's needs and no other. -/
theorem AgreeG.part {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cf : Map (Nat × List Nat)} {ned : Need} {gW0 gW1 gA gB : Gen Map} {W laz : Lazy S} {s0 s : Noun}
    (ag : AgreeG lib O c gul st t cf ned gW0 gW1 W s0 s)
    (h0 : gW0.bo ≤ gA.bo) (h1 : gB.bo ≤ gW1.bo) (hre : gB.re ≤ gW1.re)
    (hblk : ∀ o, gA.bo ≤ o → o < gB.bo → HoonMap.get gW1.blocks o = HoonMap.get gB.blocks o)
    (hlab : ∀ e ∈ entries laz, e.1 < gB.bo)
    (hsub : ∀ e ∈ entries laz, e ∈ entries W)
    (hsu : ∀ o, gA.bo ≤ o → o < gB.bo → suresAt W o = suresAt laz o) :
    AgreeG lib O c gul st t cf ned gA gB laz s0 s := by
  refine ⟨fun o l u hn => ?_, fun o ho l => ?_⟩
  · have hW : o ∉ (entries W).map Prod.fst := by
      apply notMem_of_atL
      show suresAt W o = []
      rw [hsu o l u]; exact suresAt_nil hn
    rw [ag.1 o (by omega) (by omega) hW, hblk o l u]
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    have u := hlab e he
    obtain ⟨A, B, th, hg, hc, hf⟩ := ag.2 e.1 (List.mem_map_of_mem (hsub e he)) (by omega)
    refine ⟨A, B, th, (hblk e.1 l u).symm.trans hg, hc, ?_⟩
    rw [← hsu e.1 l u]; exact hf.mono hre

/-! ## A branch's need, plain or wrapped -/

/-- **The need of a branch as `+past-fork` leaves it**: plain, or wrapped in
a bond at the fork's own label. -/
def WrapL (y : Nat) (x l : Lazy S) : Prop := l = x ∨ l = mk (Sure.bunt : Sure S) [] [(y, x)]

/-- **The entries of a branch at the fork**: the wrapper (`bunt`, at `y`),
the branch's need at `y`, or an entry of the branch's need. -/
theorem WrapL.cases {y : Nat} {x l : Lazy S} (h : WrapL y x l) :
    ∀ e ∈ (y, l) :: entries l, (e.1 = y ∧ e.2.sure = Sure.bunt) ∨ e = (y, x) ∨ e ∈ entries x := by
  intro e he
  rcases h with h | h <;> subst l
  · rcases List.mem_cons.mp he with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [entries_wrap] at he
    rcases List.mem_cons.mp he with h | h
    · exact Or.inl ⟨by rw [h], by rw [h]; rfl⟩
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem WrapL.mem_self {y : Nat} {x l : Lazy S} (h : WrapL y x l) : (y, x) ∈ (y, l) :: entries l := by
  rcases h with h | h <;> subst l
  · exact List.mem_cons_self
  · rw [entries_wrap]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem WrapL.atL_ne {y : Nat} {x l : Lazy S} (h : WrapL y x l) {o : Nat} (ho : y ≠ o) :
    atL ((y, l) :: entries l) o = atL (entries x) o := by
  rcases h with h | h <;> subst l
  · exact atL_cons_ne ho
  · rw [entries_wrap, atL_cons_ne ho, atL_cons_ne ho]

theorem WrapL.atL_self {y : Nat} {x l : Lazy S} (h : WrapL y x l) (hx : ∀ e ∈ entries x, e.1 ≠ y) :
    atL ((y, l) :: entries l) y = [x.sure] ∨ atL ((y, l) :: entries l) y = [Sure.bunt, x.sure] := by
  rcases h with h | h <;> subst l
  · left
    rw [atL_cons_eq (y, x) (entries x), atL_apart hx]
  · right
    rw [entries_wrap, atL_cons_eq (y, _) _, atL_cons_eq (y, x) (entries x), atL_apart hx]
    rfl

/-- The entries of a branch at the fork are apart within a label. -/
theorem WrapL.pairwise {y : Nat} {x l : Lazy S} (h : WrapL y x l) (hd : LabDisj x) (hx : ∀ e ∈ entries x, e.1 ≠ y) :
    ((y, l) :: entries l).Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r := by
  rcases h with h | h <;> subst l
  · refine List.Pairwise.cons (fun e' he' heq => absurd heq.symm (hx e' he')) hd
  · rw [entries_wrap]
    refine List.Pairwise.cons (fun e' _ _ r hr => by simp [Sure.bunt, NMem] at hr) ?_
    exact List.Pairwise.cons (fun e' he' heq => absurd heq.symm (hx e' he')) hd

/-- Two lists of entries whose labels are apart are apart within a label. -/
theorem pairwise_apart {l1 l2 : List (Nat × Lazy S)}
    (h1 : l1.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r)
    (h2 : l2.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r)
    (hap : ∀ e ∈ l1, ∀ e' ∈ l2, e.1 ≠ e'.1) :
    (l1 ++ l2).Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r :=
  List.pairwise_append.mpr ⟨h1, h2, fun a ha b hb hab => absurd hab (hap a ha b hb)⟩

/-! ## The relation -/

/-- **`SixDW` on the real result**: every run under `%done` returns a result
that meets `RunOKGD` (labels possibly repeated), with at most `k` entries. -/
abbrev SixDG (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) →
    RunOKGD lib N P f (CGoal.done : CGoal S) g0 g1 nex ∧ (entries nex.laz).length ≤ k

theorem SixD.toG {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} {k : Nat}
    (H : SixD (S := S) (Map := Map) lib N env P f nm k) : SixDG (S := S) (Map := Map) lib N env P f nm k :=
  fun b0 d0 hu hcl hcb hr => ⟨(H b0 d0 hu hcl hcb hr).1.toGD, (H b0 d0 hu hcl hcb hr).2⟩

theorem WrapL.mem_of {y : Nat} {x l : Lazy S} (h : WrapL y x l) {e : Nat × Lazy S} (he : e ∈ entries x) :
    e ∈ (y, l) :: entries l := by
  rcases h with h | h <;> subst l
  · exact List.mem_cons_of_mem _ he
  · rw [entries_wrap]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)

/-! ## A lazy block of the fork -/

/-- **A lazy block of the fork, forward** (`sixBlk_fwd` with `RunOKGD`). -/
theorem sixBlk_fwdG {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S}
    (Rx : RunOKGD lib N P f (CGoal.done : CGoal S) gA gB x)
    {cf : Map (Nat × List Nat)} {cc : Straight Map} {ned : Need} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs}
    {O : Oracle σ} {n : Nat} {gul : Noun} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hF : OracleFwd lib Inv ν O n) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ (st' : σ) (t' : Trace), AgreeG lib O cc gul st' t' cf ned gA gB x.laz s0 s)
    {st : σ} {tm : Trace} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {R2 : Map (Option Noun)} (hR2 : HoldsN ned R2 s0) {r : Tone} (hm : minkF lib gul n tm s f = some r) :
    ReturnsC lib O cc gul Inv ν st R2 t (jmp0 o) r := by
  obtain ⟨A, hcb, hFl⟩ := hblk st
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy; have := ((Rx.regs y hy').resolve_left (fun e => e)).2; omega
  by_cases fi : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hFl hR2 x.th).1 fi
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    exact returnsC_step (Needs.le_refl _) (e0.trans e3)
      (Rx.sem cf hcf cc ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag
        (fun y hy => Nat.le_trans hlo (hned y hy)) R3 hh3 hn3)
  · have hb := (Rx.nec s hs fi).1 gul n tm r hm
    have e2 : r = Tone.two tm := by
      rcases hb with e | ⟨p, _, hp⟩
      · exact e
      · exact hp.elim
    subst e2
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, e0.trans ((fillSem_runK hFl hR2 x.th).2 fi), ToneRel.two htr⟩

/-- **A lazy block of the fork, backward** (`sixBlk_bwd` with `RunOKGD`). -/
theorem sixBlk_bwdG {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S}
    (Rx : RunOKGD lib N P f (CGoal.done : CGoal S) gA gB x)
    {cf : Map (Nat × List Nat)} {cc : Straight Map} {ned : Need} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs}
    {O : Oracle σ} {gul : Noun} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hB : OracleBwd lib Inv ν O) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ (st' : σ) (t' : Trace), AgreeG lib O cc gul st' t' cf ned gA gB x.laz s0 s)
    {st : σ} {tm : Trace} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {R2 : Map (Option Noun)} (hR2 : HoldsN ned R2 s0) {res : Tone × σ}
    (hres : goJ lib O cc gul st R2 t (jmp0 o) = some res) :
    ∃ r, Mink lib gul tm s f r ∧ ReturnsC lib O cc gul Inv ν st R2 t (jmp0 o) r := by
  obtain ⟨A, hcb, hFl⟩ := hblk st
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy; have := ((Rx.regs y hy').resolve_left (fun e => e)).2; omega
  by_cases fi : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hFl hR2 x.th).1 fi
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    obtain ⟨r, hr, G⟩ := Rx.semB cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag
      (fun y hy => Nat.le_trans hlo (hned y hy)) R3 hh3 hn3 res ((e0.trans e3).symm.trans hres)
    exact ⟨r, hr, returnsC_step (Needs.le_refl _) (e0.trans e3) G⟩
  · obtain ⟨r, hr, hb⟩ := (Rx.nec s hs fi).2 gul tm
    have e2 : r = Tone.two tm := by
      rcases hb with e | ⟨p, _, hp⟩
      · exact e
      · exact hp.elim
    subst e2
    exact ⟨_, hr, Tone.two t, st, hI, Needs.le_refl _, e0.trans ((fillSem_runK hFl hR2 x.th).2 fi),
      ToneRel.two htr⟩

/-! ## `[6 c a b]` under `%done` with any test, on the real result -/

/-- **`[6 c a b]` under `%done` with any test of `PickD` and branches of
`SixDG`**, the relation on the REAL result (`six_doneGBW` without `nexU`):
`+past-fork` may wrap each branch's need in a bond at the fork's own label
(`WrapL`), so the labels repeat; `LabDisj` holds since the wrapper's need is
`bunt` and the parts' labels lie apart, and at the fork's labels the whole's
`AgreeG` fills `[x.sure]` or `[bunt, x.sure]`, which is the branch's fill
(`FillSemL.toOne`).  Branches of `SixDG` may be `%6` again. -/
theorem six_doneGD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fc fa fb : Noun} {c a b : Nomm}
    {kc ka kb : Nat} (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (Ha : SixDG (S := S) (Map := Map) lib N env P fa a ka) (Hb : SixDG (S := S) (Map := Map) lib N env P fb b kb)
    (hk : ka + kb + 5 ≤ lazyMax) :
    SixDG (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (kc + ka + kb + 4) := by
  intro sup region g0 g4 nex b0 d0 hu hcl0 hcb0 h
  obtain ⟨x1, x0, xc, g1, g2, g3, l0, l1, h1, h2, hx0a, hx1a, h3, hl01, hrest⟩ := runLC_six_done_apartW env sup h
  obtain ⟨Rb, sb⟩ := Hb b0 d0 hu hcl0 hcb0 h1
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have cl1 : Clear g1 := hcl0.growU Rb.grow
  have cb1 : CondBelow g1 := Rb.cfr.below hcb0
  obtain ⟨Ra, sa⟩ := Ha b1 d1 u1 cl1 cb1 h2
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
  have w0 : WrapL g2.bo x0.laz l0 := hl01.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have w1 : WrapL (g2.bo + 1) x1.laz l1 := hl01.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have e0l : (entries l0).length ≤ ka + 1 := by
    rcases hl01 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · omega
    · rw [entries_wrap]; simp only [List.length_cons]; omega
  have e1l : (entries l1).length ≤ kb + 1 := by
    rcases hl01 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · omega
    · rw [entries_wrap]; simp only [List.length_cons]; omega
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    omega
  -- the test
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  obtain ⟨Rc, sc⟩ := Hc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩
    (by simp only [sixGenL_bo]; omega) dG uG (cl2.growU GU)
    (fun k hk => by simp only [sixGenL_cond, sixGenL_re] at hk ⊢; exact cb2 k hk) h3
  have u3 : UpBelow g3 := Rc.grow.up uG
  have d3 : g3.drop = false := Rc.ext.2.2.1.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Rc.ext.2.1; simpa using this
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ g2.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; simp only [sixGenL_bo] at this; omega
  have hcp' := hrest hbig
  rw [copyL_six_apart xc l0 l1 g2.bo (g2.bo + 1) g3 hap] at hcp'
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp'
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨A4, r4, bo4, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r4 bo4
  -- the states
  have E2 : Ext g2 (sixGenL g2 x0.th x1.th region) := ext_sixGenL _ _ _ _
  have E4 : Ext g3 g4' := (ext_emit g3 _).trans (ext_addOps_nil hadd)
  have E24 : Ext g2 g4' := E2.trans (Rc.ext.trans E4)
  have E14 : Ext g1 g4' := Ra.ext.trans E24
  have E04 : Ext g0 g4' := Rb.ext.trans E14
  have re01 := Rb.ext.1
  have re12 := Ra.ext.1
  have re2G : g2.re ≤ g3.re := by have := Rc.ext.1; simpa using this
  have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4'.blocks k = HoonMap.get g3.blocks k := fun k hk =>
    (A4 k).trans (get_emitted_ne hk)
  have h4o : HoonMap.get g4'.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A4 g3.bo).trans (emitted_get g3 _ d3)
  have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k =
      HoonMap.get (sixGenL g2 x0.th x1.th region).blocks k := fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
  have h4y : HoonMap.get g4'.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_y _ _ _ d2
  have h4n : HoonMap.get g4'.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_n _ _ _ d2
  have h42 : ∀ k, k < g2.bo → HoonMap.get g4'.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
  have h41 : ∀ k, k < g1.bo → HoonMap.get g4'.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
  -- the registers of the parts
  have raR : ∀ r, NMem x0.laz.sure.ned r → g1.re ≤ r ∧ r < g2.re := fun r hr => (Ra.regs r hr).resolve_left (fun e => e)
  have rbR : ∀ r, NMem x1.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re := fun r hr => (Rb.regs r hr).resolve_left (fun e => e)
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    have := Rc.labs e he; simp only [sixGenL_bo] at this; exact ⟨this.1, this.2.1⟩
  have la : ∀ e ∈ entries x0.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(Ra.labs e he).1, (Ra.labs e he).2.1⟩
  have lb : ∀ e ∈ entries x1.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(Rb.labs e he).1, (Rb.labs e he).2.1⟩
  have c0 := w0.cases
  have c1 := w1.cases
  have hd0 : ∀ e ∈ (g2.bo, l0) :: entries l0, e.1 = g2.bo ∨ (g1.bo ≤ e.1 ∧ e.1 < g2.bo) := fun e he => by
    rcases c0 e he with ⟨h, _⟩ | rfl | h
    · exact Or.inl h
    · exact Or.inl rfl
    · exact Or.inr (la e h)
  have hd1 : ∀ e ∈ (g2.bo + 1, l1) :: entries l1, e.1 = g2.bo + 1 ∨ (g0.bo ≤ e.1 ∧ e.1 < g1.bo) := fun e he => by
    rcases c1 e he with ⟨h, _⟩ | rfl | h
    · exact Or.inl h
    · exact Or.inl rfl
    · exact Or.inr (lb e h)
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    g2.bo (g2.bo + 1) l0 l1
  have memK : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond),
      e ∈ entries xc.laz ∨ e ∈ (g2.bo, l0) :: entries l0 ∨ e ∈ (g2.bo + 1, l1) :: entries l1 := by
    intro e he
    rw [en] at he
    rcases List.mem_append.mp he with h | h
    · exact Or.inl h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have inC : ∀ e ∈ entries xc.laz, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) := fun e he => by
    rw [en]; exact List.mem_append_left _ he
  have in0 : ∀ e ∈ (g2.bo, l0) :: entries l0, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) := fun e he => by
    rw [en]; exact List.mem_append_right _ (List.mem_append_left _ he)
  have in1 : ∀ e ∈ (g2.bo + 1, l1) :: entries l1, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) := fun e he => by
    rw [en]; exact List.mem_append_right _ (List.mem_append_right _ he)
  have labW : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond), g0.bo ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    rcases memK e he with h | h | h
    · have := lc e h; omega
    · rcases hd0 e h with h' | h' <;> omega
    · rcases hd1 e h with h' | h' <;> omega
  have hsW : ∀ o, suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) o =
      atL (entries xc.laz) o ++ (atL ((g2.bo, l0) :: entries l0) o ++ atL ((g2.bo + 1, l1) :: entries l1) o) :=
    fun o => by
      show atL _ o = _
      rw [en, atL_append, atL_append]
  have sC : ∀ o, g2.bo + 2 ≤ o → o < g3.bo → suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) o = suresAt xc.laz o := fun o h0 h1 => by
    rw [hsW, atL_apart (es := (g2.bo, l0) :: entries l0) (fun e he => by rcases hd0 e he with h | h <;> omega),
      atL_apart (es := (g2.bo + 1, l1) :: entries l1) (fun e he => by rcases hd1 e he with h | h <;> omega)]
    simp only [List.append_nil]; rfl
  have sA : ∀ o, g1.bo ≤ o → o < g2.bo → suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) o = suresAt x0.laz o := fun o h0 h1 => by
    rw [hsW, atL_apart (es := entries xc.laz) (fun e he => by have := lc e he; omega), w0.atL_ne (by omega),
      atL_apart (es := (g2.bo + 1, l1) :: entries l1) (fun e he => by rcases hd1 e he with h | h <;> omega)]
    simp only [List.append_nil, List.nil_append]; rfl
  have sB : ∀ o, g0.bo ≤ o → o < g1.bo → suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) o = suresAt x1.laz o := fun o h0 h1 => by
    rw [hsW, atL_apart (es := entries xc.laz) (fun e he => by have := lc e he; omega),
      atL_apart (es := (g2.bo, l0) :: entries l0) (fun e he => by rcases hd0 e he with h | h <;> omega), w1.atL_ne (by omega)]
    simp only [List.nil_append]; rfl
  have sY : suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) g2.bo = [x0.laz.sure] ∨
      suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) g2.bo = [Sure.bunt, x0.laz.sure] := by
    rw [hsW, atL_apart (es := entries xc.laz) (fun e he => by have := lc e he; omega),
      atL_apart (es := (g2.bo + 1, l1) :: entries l1) (fun e he => by rcases hd1 e he with h | h <;> omega)]
    simp only [List.append_nil, List.nil_append]
    exact w0.atL_self (fun e he => by have := la e he; omega)
  have sN : suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) (g2.bo + 1) = [x1.laz.sure] ∨
      suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) (g2.bo + 1) = [Sure.bunt, x1.laz.sure] := by
    rw [hsW, atL_apart (es := entries xc.laz) (fun e he => by have := lc e he; omega),
      atL_apart (es := (g2.bo, l0) :: entries l0) (fun e he => by rcases hd0 e he with h | h <;> omega)]
    simp only [List.nil_append]
    exact w1.atL_self (fun e he => by have := lb e he; omega)
  have hc43 : g4'.cond = g3.cond := by rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond]
  have cf34 : CondFresh g3 g4' := condFresh_of_eq E4.1 hc43
  have cfG : CondFresh g2 (sixGenL g2 x0.th x1.th region) :=
    condFresh_of_eq (by simp only [sixGenL_re]; omega) (by rw [sixGenL_cond])
  have cf24 : CondFresh g2 g4' := cfG.trans (Rc.cfr.trans cf34)
  have cf14 : CondFresh g1 g4' := Ra.cfr.trans cf24
  have hxca : xc.th.args = [] := by
    rcases Rc.ent with ⟨_, _, _, e⟩ | e
    · exact e
    · simp only [GoalJ] at e; rcases e with e | e <;> rw [e] <;> rfl
  -- what the program gives the parts
  have core : ∀ (cf : Map (Nat × List Nat)) (cc : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ)
      (gul : Noun) (t : Trace) (s0 s : Noun) (st : σ),
      (∀ st' : σ, AgreeG lib O cc gul st' t cf ned g0 g4'
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) s0 s) →
      HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned (sixGenL g2 x0.th x1.th region) g3 xc.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks g2.bo = some ⟨[], A, Termin.hop x0.th⟩ ∧
        FillSem lib O cc gul st' t ned g4'.re x0.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeG lib O cc gul st' t cf ned g1 g2 x0.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks (g2.bo + 1) = some ⟨[], A, Termin.hop x1.th⟩ ∧
        FillSem lib O cc gul st' t ned g4'.re x1.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeG lib O cc gul st' t cf ned g0 g1 x1.laz s0 s) := by
    intro cf cc ned σ O gul t s0 s st ag
    have fork : ∀ (o : Nat) (x : NextL S) (st' : σ),
        o ∈ (entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond)).map Prod.fst → g0.bo ≤ o →
        HoonMap.get g4'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → x.th.args = [] →
        (suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) o = [x.laz.sure] ∨
         suresAt (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond) o = [Sure.bunt, x.laz.sure]) →
        ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
          FillSem lib O cc gul st' t ned g4'.re x.laz.sure A s0 s := by
      intro o x st' hm hlo hb hxa hsu
      obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 o hm hlo
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      obtain ⟨rfl, rfl⟩ := hg
      refine ⟨A, by rw [hcb]; simp [renJmp_nil _ hxa], hF.toOne ?_ ?_⟩
      · rcases hsu with e | e <;> rw [e] <;> simp
      · rcases hsu with e | e <;> rw [e] <;> simp
    refine ⟨?_, fun st' => ?_, fun st' => fork g2.bo x0 st' (List.mem_map_of_mem (in0 _ List.mem_cons_self))
        (by omega) h4y hx0a sY,
      fun st' => ?_,
      fun st' => fork (g2.bo + 1) x1 st' (List.mem_map_of_mem (in1 _ List.mem_cons_self)) (by omega) h4n hx1a sN,
      fun st' => ?_⟩
    · have hn : g3.bo ∉ (entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, l0), (g2.bo + 1, l1))]) xc.laz.bond)).map Prod.fst := fun hm => by
        obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
        have := (labW e he).2; omega
      rw [(ag st).1 g3.bo (by omega) (by omega) hn, h4o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hxca]
    · refine AgreeG.toUB (AgreeG.part (ag st') (by simp only [sixGenL_bo]; omega) (by omega) (by omega)
        (fun o h0 h1 => h4k o (by omega)) (fun e he => (lc e he).2) (fun e he => inC e he)
        (fun o h0 h1 => sC o (by simpa using h0) h1)) Rc.nodup
        (fun e he => by simp only [sixGenL_bo]; exact (lc e he).1)
    · exact AgreeG.part (ag st') (by omega) (by omega) (by omega)
        (fun o h0 h1 => h42 o h1) (fun e he => (la e he).2) (fun e he => in0 e (w0.mem_of he)) sA
    · exact AgreeG.part (ag st') (by omega) (by omega) (by omega)
        (fun o h0 h1 => h41 o h1) (fun e he => (lb e he).2) (fun e he => in1 e (w1.mem_of he)) sB
  refine ⟨⟨E04, ?_, Rb.cfr.trans cf14, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h4o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, fun s hs hfs => ?_,
    fun r hr => by rw [hc43]; exact Rc.ncond r hr, ?_, ?_, ?_⟩, ?_⟩
  · -- grow
    have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) u3
    exact Rb.grow.trans (Ra.grow.trans (GU.trans
      (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up u3))))))
  · -- regs
    have := (Rc.regs r hr).resolve_left (fun e => e); simp only [sixGenL_re] at this
    exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    intro e he
    rcases memK e he with h | h | h
    · refine ⟨(Rc.eregs e h).1, fun r hr => ?_⟩
      have := (Rc.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e); simp only [sixGenL_re] at h1'
      exact ⟨Or.inr (by omega), by omega⟩
    · rcases c0 e h with ⟨_, hb⟩ | rfl | h
      · rw [hb]; exact ⟨trivial, fun r hr => by simp [Sure.bunt, NMem] at hr⟩
      · exact ⟨Ra.dist, fun r hr => ⟨Or.inr (by have := raR r hr; omega), by have := raR r hr; omega⟩⟩
      · refine ⟨(Ra.eregs e h).1, fun r hr => ?_⟩
        have := (Ra.eregs e h).2 r hr
        have h1' := this.1.resolve_left (fun e => e)
        exact ⟨Or.inr (by omega), by omega⟩
    · rcases c1 e h with ⟨_, hb⟩ | rfl | h
      · rw [hb]; exact ⟨trivial, fun r hr => by simp [Sure.bunt, NMem] at hr⟩
      · exact ⟨Rb.dist, fun r hr => ⟨Or.inr (by have := rbR r hr; omega), by have := rbR r hr; omega⟩⟩
      · refine ⟨(Rb.eregs e h).1, fun r hr => ?_⟩
        have := (Rb.eregs e h).2 r hr
        have h1' := this.1.resolve_left (fun e => e)
        exact ⟨Or.inr (by omega), by omega⟩
  · -- labs
    intro e he
    rcases memK e he with h | h | h
    · obtain ⟨_, _, B, th, hth⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, B, th, (h4k _ (by omega)).trans hth⟩
    · rcases c0 e h with ⟨hy, _⟩ | rfl | h
      · rw [hy]; exact ⟨by omega, by omega, [], x0.th, h4y⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x0.th, h4y⟩
      · obtain ⟨_, _, B, th, hth⟩ := Ra.labs e h
        have := la e h
        exact ⟨by omega, by omega, B, th, (h42 _ this.2).trans hth⟩
    · rcases c1 e h with ⟨hy, _⟩ | rfl | h
      · rw [hy]; exact ⟨by omega, by omega, [], x1.th, h4n⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x1.th, h4n⟩
      · obtain ⟨l1', _, B, th, hth⟩ := Rb.labs e h
        have := lb e h
        exact ⟨l1', by omega, B, th, (h41 _ this.2).trans hth⟩
  · -- labDisj
    unfold LabDisj
    rw [en]
    refine pairwise_apart (labDisj_of_nodup Rc.nodup)
      (pairwise_apart (w0.pairwise Ra.labDisj (fun e he => by have := la e he; omega))
        (w1.pairwise Rb.labDisj (fun e he => by have := lb e he; omega))
        (fun e he e' he' => by rcases hd0 e he with h | h <;> rcases hd1 e' he' with h' | h' <;> omega))
      (fun e he e' he' => by
        have := lc e he
        rcases List.mem_append.mp he' with h | h
        · rcases hd0 e' h with h' | h' <;> omega
        · rcases hd1 e' h with h' | h' <;> omega)
  · -- nec
    have fo' : ¬ FitsS xc.laz.sure s := fun f => hfs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    obtain ⟨N1, N2⟩ := Rc.nec s hs fo'
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
      have e2 : rb = Tone.two tm := by
        rcases N1 gul n' tm rb hb with e | ⟨p, _, hp⟩
        · exact e
        · exact hp.elim
      subst e2
      rcases hcase with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨p, e, _⟩
      · exact Or.inl e
      · cases e
      · cases e
      · cases e
    · obtain ⟨rb, hb, hbad⟩ := N2 gul tm
      have e2 : rb = Tone.two tm := by
        rcases hbad with e | ⟨p, _, hp⟩
        · exact e
        · exact hp.elim
      subst e2
      exact ⟨_, (mink_sixC_bwd (fc := fa) (fd := fb) hb).1 (fun _ e => by cases e), Or.inl rfl⟩
  · -- econd
    intro e he r hr
    rcases memK e he with h | h | h
    · rw [hc43]; exact Rc.econd e h r hr
    · rcases c0 e h with ⟨_, hb⟩ | rfl | h
      · rw [hb] at hr; simp [Sure.bunt, NMem] at hr
      · rw [cf24.get_lt (raR r hr).2]; exact Ra.ncond r hr
      · rw [cf24.get_lt ((Ra.eregs e h).2 r hr).2]; exact Ra.econd e h r hr
    · rcases c1 e h with ⟨_, hb⟩ | rfl | h
      · rw [hb] at hr; simp [Sure.bunt, NMem] at hr
      · rw [cf14.get_lt (rbR r hr).2]; exact Rb.ncond r hr
      · rw [cf14.get_lt ((Rb.eregs e h).2 r hr).2]; exact Rb.econd e h r hr
  · -- forward
    intro cf hcf cc ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hc3, agC, yesB, -, nuhB, -⟩ := core cf cc ned σ O gul t s0 s st (fun st' => ag st' t)
    have agA : ∀ (st' : σ) (t' : Trace), AgreeG lib O cc gul st' t' cf ned g1 g2 x0.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st (fun st'' => ag st'' t')).2.2.2.1 st'
    have agB : ∀ (st' : σ) (t' : Trace), AgreeG lib O cc gul st' t' cf ned g0 g1 x1.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st (fun st'' => ag st'' t')).2.2.2.2.2 st'
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf24.get_lt hk)
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf14.get_lt hk)
    obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
    have Gc := Rc.sem cf hcf3 cc ned σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rb
      hI htr hs hb agC (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    show ReturnsC lib O cc gul Inv ν st regs t (jmp0 g3.bo) r
    rcases hcase with ⟨hnz, hrr⟩ | ⟨rfl, ha⟩ | ⟨rfl, hb'⟩ | ⟨p, rfl, h0, h1, rfl⟩
    · rw [hrr]
      cases rb with
        | zero q => exact absurd rfl (hnz q)
        | one q => exact returnsC_step (Needs.le_refl _) e0 Gc
        | two q => exact returnsC_step (Needs.le_refl _) e0 Gc
    · obtain ⟨G0, -, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwdG Ra hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf2
        (by omega) hned hs yesB agA hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ha)
    · obtain ⟨-, G1, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwdG Rb hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf1
        (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) hb')
    · obtain ⟨-, -, G2⟩ := Gc
      exact returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)
  · -- backward
    intro cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hc3, agC, yesB, -, nuhB, -⟩ := core cf cc ned σ O gul t s0 s st (fun st' => ag st' t)
    have agA : ∀ (st' : σ) (t' : Trace), AgreeG lib O cc gul st' t' cf ned g1 g2 x0.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st (fun st'' => ag st'' t')).2.2.2.1 st'
    have agB : ∀ (st' : σ) (t' : Trace), AgreeG lib O cc gul st' t' cf ned g0 g1 x1.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st (fun st'' => ag st'' t')).2.2.2.2.2 st'
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf24.get_lt hk)
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf14.get_lt hk)
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    obtain ⟨rb, hmb, Gc⟩ := Rc.semB cf hcf3 cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs agC
      (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn res
      (e0.symm.trans hres)
    have MB := mink_sixC_bwd (fc := fa) (fd := fb) hmb
    show ∃ r, Mink lib gul tm s (n4 (A 6) fc fa fb) r ∧ ReturnsC lib O cc gul Inv ν st regs t (jmp0 g3.bo) r
    cases rb with
    | zero p =>
      by_cases h0 : p = A 0
      · subst h0
        obtain ⟨G0, -, -⟩ := Gc
        obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
        obtain ⟨r, hr, G⟩ := sixBlk_bwdG Ra hN hS hB hcf2 (by omega) hned hs yesB agA hI' (frames_mono hν htr)
          (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
        exact ⟨r, MB.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
      · by_cases h1 : p = A 1
        · subst h1
          obtain ⟨-, G1, -⟩ := Gc
          obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
          obtain ⟨r, hr, G⟩ := sixBlk_bwdG Rb hN hS hB hcf1 (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
            (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
          exact ⟨r, MB.2.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
        · obtain ⟨-, -, G2⟩ := Gc
          exact ⟨_, MB.2.2.2 p rfl h0 h1, returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)⟩
    | one q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
    | two q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
  · -- the bound
    rw [entries_copy_six]; simp only [List.length_append, List.length_cons]
    omega

/-! ## The example's `q` and the contract -/

/-- **The `q` of the example** `[7 [[0 2] [0 3]] [6 [2 [0 3] [0 2]] [0 2] [0 2]]]`:
a `%6` with a calling test and the branches `[0 2]` meets `SixDG` (its
result's labels repeat). -/
theorem sixDG_callTest (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) :
    SixDG (S := S) (Map := Map) lib N env P (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2))
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2)) (0 + 0 + 0 + 4) :=
  six_doneGD lib env (sixTest_pickD lib env P sixTest_ind)
    (SixD.toG (sixD_of_callTreeA lib env (CallTreeA.n0 2) (NoEntF.pure rfl rfl) P))
    (SixD.toG (sixD_of_callTreeA lib env (CallTreeA.n0 2) (NoEntF.pure rfl rfl) P)) (by decide)

/-- **The contract from `SixDG`** (through `finishLUC_contractGD`). -/
theorem finishLUC_contractSixDG (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    {k : Nat} (H : SixDG (S := S) (Map := Map) lib N env P f nm k) {c : Straight Map}
    (hc : finishLUC (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractGD lib N (fun hr => (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) hc


/-- **The contract of the example's `q` alone**, `[6 [2 [0 3] [0 2]] [0 2] [0 2]]`,
through the new relation (`RunOKGD` of the real result, labels repeated). -/
theorem sixCallTest22_contractG (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2)) [s] c ∧
      ContractBwd lib N s (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2)) [s] c :=
  have H := finishLUC_contractSixDG lib env (sixDG_callTest (S := S) (Map := Map) lib N env (fun _ => True)) hc
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
