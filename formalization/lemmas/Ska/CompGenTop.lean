import lemmas.Ska.CompGenSeven
import lemmas.Ska.CompLBDone

/-!
# The top of `RunOKGen`: `+kern` per label, and the contract under `%done`

README Gaps 12.39, item 5.  `finishTop_genB` reads `nodup` only for the
list of entries `+kerf` fills (`kern_spec`).  With repeated labels `+kern`
puts the fill of each entry at its label in front of the block, so the spec
is stated per label (`WalkOKL`: at every label the ops in front are the
concatenation of a list of pieces, one per entry there, up to a
permutation), and `FillSemL.cons` turns the pieces into the fill of the
conjunction `suresAt` that `AgreeG` asks, the registers of the entries at
one label being apart (`LabDisj`).

* `WalkOKL` with `nil`, `ofD`, `trans` (no disjointness), `perm`;
  `walkLazy_okL`, `walkForks_okL`, `walkBonds_okL`; `kern_specL` (`kern_spec`
  without `Nodup`).
* `FillSemL.perm`, `fillSemL_list`, `labDisj_at`, `kernFill`.
* `RunOKGD`: the `%done` relation with `LabDisj` for `nodup` and `AgreeG`
  (per label, every state and trace) for `AgreeUB`; `RunOKGB.toGD` (the old
  one feeds it); `TopSG`, `finishTop_genG`, `finishLUC_contractGD`: the
  contract from a `RunOKGD` run under `%done`, with no `WalkEq` / `Unwraps`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The walk per label -/

/-- The sure needs of the entries of `es` at the label `o`. -/
def atL (es : List (Nat × Lazy S)) (o : Nat) : List (Sure S) :=
  (es.filter fun e => decide (e.1 = o)).map fun e => e.2.sure

theorem atL_append (es1 es2 : List (Nat × Lazy S)) (o : Nat) : atL (es1 ++ es2) o = atL es1 o ++ atL es2 o := by
  simp only [atL, List.filter_append, List.map_append]

/-- **`WalkOKD` per label**: at every label the ops put in front are the
concatenation of pieces, one per entry of `es` at that label (up to a
permutation), each meeting `P`. -/
structure WalkOKL (C : Gen Map → Gen Map → Prop)
    (P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop) (g g' : Gen Map)
    (es : List (Nat × Lazy S)) : Prop where
  bo : g'.bo = g.bo
  drop : g'.drop = g.drop
  le : g.re ≤ g'.re
  cnd : C g g'
  other : ∀ o, o ∉ es.map Prod.fst → HoonMap.get g'.blocks o = HoonMap.get g.blocks o
  at_ : ∀ o, ∃ As : List (Sure S × List Pole), (∀ B fin, HoonMap.get g.blocks o = some ⟨[], B, fin⟩ →
    HoonMap.get g'.blocks o = some ⟨[], (As.map Prod.snd).flatten ++ B, fin⟩) ∧
    (As.map Prod.fst).Perm (atL es o) ∧ ∀ p ∈ As, P g'.cond g.re g'.re o p.1 p.2

section Walk
variable {C : Gen Map → Gen Map → Prop} {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop}

theorem WalkOKL.nil (cr : ∀ g, C g g) (P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop)
    (g : Gen Map) : WalkOKL C P g g [] :=
  ⟨rfl, rfl, Nat.le_refl _, cr g, fun _ _ => rfl,
   fun o => ⟨[], fun B fin hb => by simpa using hb, by simp [atL], fun _ h => by simp at h⟩⟩

theorem WalkOKD.toL {g g' : Gen Map} {o : Nat} {l : Lazy S} (W : WalkOKD C P g g' [(o, l)]) :
    WalkOKL C P g g' [(o, l)] := by
  refine ⟨W.bo, W.drop, W.le, W.cnd, W.other, fun o' => ?_⟩
  by_cases h : o' = o
  · subst h
    obtain ⟨A, hA, hP⟩ := W.at_ (o', l) (List.mem_singleton.mpr rfl)
    refine ⟨[(l.sure, A)], fun B fin hb => by simpa using hA B fin hb, by simp [atL], fun p hp => ?_⟩
    rw [List.mem_singleton.mp hp]; exact hP
  · refine ⟨[], fun B fin hb => by rw [W.other o' (by simp [h])]; simpa using hb, ?_, fun _ h => by simp at h⟩
    have : (o ≠ o') := fun e => h e.symm
    simp [atL, this]

theorem WalkOKL.trans (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    (pm : PMonoD P) {g g1 g2 : Gen Map} {es1 es2 : List (Nat × Lazy S)} (a : WalkOKL C P g g1 es1)
    (b : WalkOKL C P g1 g2 es2) : WalkOKL C P g g2 (es1 ++ es2) := by
  refine ⟨b.bo.trans a.bo, b.drop.trans a.drop, Nat.le_trans a.le b.le, ct _ _ _ a.cnd b.cnd, fun o ho => ?_,
    fun o => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or] at ho
    exact (b.other o ho.2).trans (a.other o ho.1)
  · obtain ⟨As1, h1, p1, q1⟩ := a.at_ o
    obtain ⟨As2, h2, p2, q2⟩ := b.at_ o
    refine ⟨As2 ++ As1, fun B fin hb => ?_, ?_, fun p hp => ?_⟩
    · rw [h2 _ fin (h1 B fin hb)]
      simp only [List.map_append, List.flatten_append, List.append_assoc]
    · rw [List.map_append, atL_append]
      exact (p2.append p1).trans List.perm_append_comm
    · rcases List.mem_append.mp hp with h | h
      · exact pm _ _ _ _ _ _ _ _ _ (q2 p h) (fun _ _ => rfl) a.le (Nat.le_refl _)
      · exact pm _ _ _ _ _ _ _ _ _ (q1 p h) (cb _ _ b.cnd) (Nat.le_refl _) b.le

theorem WalkOKL.perm {g g' : Gen Map} {es es' : List (Nat × Lazy S)} (W : WalkOKL C P g g' es)
    (hp : es.Perm es') : WalkOKL C P g g' es' := by
  refine ⟨W.bo, W.drop, W.le, W.cnd, fun o ho => W.other o fun hm => ho ((hp.map Prod.fst).mem_iff.mp hm),
    fun o => ?_⟩
  obtain ⟨As, h1, p1, q1⟩ := W.at_ o
  exact ⟨As, h1, p1.trans ((hp.filter _).map _), q1⟩

mutual
theorem walkLazy_okL (cr : ∀ g, C g g)
    (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {I : Gen Map → Prop} (ci : ∀ a b : Gen Map, C a b → I a → I b)
    (pm : PMonoD P) {f : Nat → Sure S → CM Map Unit} (hf : GateOKDI C I P f) : ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map),
    walkLazy f o l g = some ((), g') → g.drop = false → I g → WalkOKL C P g g' ((o, l) :: entries l)
  | o, mk s fk bd, g, g', h, hd, hI => by
    unfold walkLazy at h
    obtain ⟨u, g1, h1, hr⟩ := bind_some h
    have W1 := (hf o (mk s fk bd) g g1 h1 hd hI).toL
    have hI1 := ci _ _ W1.cnd hI
    have d1 : g1.drop = false := W1.drop.trans hd
    split at hr
    · rename_i hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      have h' : some ((), g1) = some ((), g') := hr
      cases h'
      have e : entries (mk s [] [] : Lazy S) = [] := by simp [entries, bondEntries, forkEntries]
      rw [e]; exact W1
    · obtain ⟨u2, g2, h2, h3⟩ := bind_some hr
      have WF := walkForks_okL cr ct cb ci pm hf fk g1 g2 h2 d1 hI1
      have WB := walkBonds_okL cr ct cb ci pm hf bd g2 g' h3 (WF.drop.trans d1) (ci _ _ WF.cnd hI1)
      refine ((W1.trans ct cb pm WF).trans ct cb pm WB).perm ?_
      simp only [entries, List.singleton_append, List.cons_append]
      exact List.Perm.cons _ List.perm_append_comm

theorem walkForks_okL (cr : ∀ g, C g g)
    (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {I : Gen Map → Prop} (ci : ∀ a b : Gen Map, C a b → I a → I b)
    (pm : PMonoD P) {f : Nat → Sure S → CM Map Unit} (hf : GateOKDI C I P f) : ∀ (fk : List (ForkE S)) (g g' : Gen Map),
    walkForks f fk g = some ((), g') → g.drop = false → I g → WalkOKL C P g g' (forkEntries fk)
  | [], g, g', h, _, _ => by
    simp only [walkForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOKL.nil cr P g
  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hI => by
    unfold walkForks at h
    obtain ⟨u1, g1, h1, h⟩ := bind_some h
    obtain ⟨u2, g2, h2, h3⟩ := bind_some h
    have Wy := walkLazy_okL cr ct cb ci pm hf oy y g g1 h1 hd hI
    have Wn := walkLazy_okL cr ct cb ci pm hf on n g1 g2 h2 (Wy.drop.trans hd) (ci _ _ Wy.cnd hI)
    have Wr := walkForks_okL cr ct cb ci pm hf rest g2 g' h3 (Wn.drop.trans (Wy.drop.trans hd))
      (ci _ _ Wn.cnd (ci _ _ Wy.cnd hI))
    simp only [forkEntries]
    exact (Wy.trans ct cb pm Wn).trans ct cb pm Wr

theorem walkBonds_okL (cr : ∀ g, C g g)
    (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {I : Gen Map → Prop} (ci : ∀ a b : Gen Map, C a b → I a → I b)
    (pm : PMonoD P) {f : Nat → Sure S → CM Map Unit} (hf : GateOKDI C I P f) : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map),
    walkBonds f bd g = some ((), g') → g.drop = false → I g → WalkOKL C P g g' (bondEntries bd)
  | [], g, g', h, _, _ => by
    simp only [walkBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOKL.nil cr P g
  | (o, l) :: rest, g, g', h, hd, hI => by
    unfold walkBonds at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have Wl := walkLazy_okL cr ct cb ci pm hf o l g g1 h1 hd hI
    have Wr := walkBonds_okL cr ct cb ci pm hf rest g1 g' h2 (Wl.drop.trans hd) (ci _ _ Wl.cnd hI)
    simp only [bondEntries]
    exact Wl.trans ct cb pm Wr
end

end Walk

/-- **`+kern` per label** (`kern_spec` without `Nodup`): at every label the
ops in front are one piece per entry there, each doing what `KernP r` says. -/
theorem kern_specL {o : Nat} {laz : Lazy S} {g g' : Gen Map} {r : Nat}
    (h : kern o laz g = some (r, g')) (hd : g.drop = false) (hI : CondBelow g) :
    r = g.re ∧ WalkOKL (ProxyFor r) (KernP (S := S) (Map := Map) r) { g with re := g.re + 1 } g'
      ((o, laz) :: entries laz) := by
  rw [kern_eq] at h
  obtain ⟨r', g1, h1, h⟩ := bind_some h
  rw [re_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨gg, g2, h2, h⟩ := bind_some h
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  simp only at h
  rw [if_neg (show ¬ (g.drop = true) by simp [hd])] at h
  obtain ⟨u, g3, h3, h4⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨e, rfl⟩ := h4
  subst e
  have hI1 : CondBelow ({ g with re := g.re + 1 } : Gen Map) := fun k hk => by
    have := hI k hk; simp only; omega
  exact ⟨rfl, walkLazy_okL (ProxyFor.refl g.re) (fun _ _ _ a b => ProxyFor.trans a b)
    (fun _ _ h _ hk => ProxyFor.get_lt h hk) (fun _ _ h hb => h.1.below hb) (kernP_mono g.re)
    (kernGate_ok g.re o) o laz _ g3 h3 hd hI1⟩

/-! ## Fills of the pieces at one label -/

section Fill
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
  {ned : Need} {lo : Nat} {s0 s : Noun}

theorem FillSemL.perm {Ls Ls' : List (Sure S)} {A : List Pole} (h : FillSemL lib O c gul st t ned lo Ls A s0 s)
    (hp : Ls.Perm Ls') : FillSemL lib O c gul st t ned lo Ls' A s0 s := by
  intro R hR
  refine ⟨fun f => ?_, fun ⟨L, hL, nf⟩ => (h R hR).2 ⟨L, hp.mem_iff.mpr hL, nf⟩⟩
  obtain ⟨R', r, hh, k⟩ := (h R hR).1 (fun L hL => f L (hp.mem_iff.mp hL))
  exact ⟨R', r, fun L hL => hh L (hp.mem_iff.mpr hL), fun x hx hn => k x hx (fun L hL => hn L (hp.mem_iff.mp hL))⟩

/-- **The pieces at one label fill the conjunction** (`FillSemL.cons` along
the list). -/
theorem fillSemL_list : ∀ (As : List (Sure S × List Pole)),
    (∀ p ∈ As, FillSem lib O c gul st t ned lo p.1 p.2 s0 s) → (∀ p ∈ As, ∀ x, NMem p.1.ned x → x < lo) →
    (∀ x, NMem ned x → lo ≤ x) → (As.map Prod.fst).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) →
    FillSemL lib O c gul st t ned lo (As.map Prod.fst) (As.map Prod.snd).flatten s0 s
  | [], _, _, _, _ => fillSemL_nil_nil
  | p :: As, h1, h2, hn, hp => by
    simp only [List.map_cons, List.flatten_cons]
    rw [List.map_cons, List.pairwise_cons] at hp
    exact FillSemL.cons (h1 p List.mem_cons_self)
      (fillSemL_list As (fun q hq => h1 q (List.mem_cons_of_mem _ hq)) (fun q hq => h2 q (List.mem_cons_of_mem _ hq))
        hn hp.2)
      (h2 p List.mem_cons_self) hn (fun L hL x hx => hp.1 L hL x hx)

end Fill

/-- **The needs at one label are apart**, from `LabDisj`. -/
theorem labDisj_at {laz : Lazy S} (h : LabDisj laz) (o : Nat) :
    (suresAt laz o).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r := by
  unfold suresAt
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter (fun e => decide (e.1 = o)) h)
  intro a b ha hb hab
  have e1 := of_decide_eq_true (List.mem_filter.mp ha).2
  have e2 := of_decide_eq_true (List.mem_filter.mp hb).2
  exact hab (e1.trans e2.symm)

theorem mem_suresAt {laz : Lazy S} {o : Nat} {L : Sure S} (h : L ∈ suresAt laz o) :
    ∃ e ∈ entries laz, e.1 = o ∧ e.2.sure = L := by
  unfold suresAt at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  exact ⟨e, (List.mem_filter.mp he).1, of_decide_eq_true (List.mem_filter.mp he).2, rfl⟩

/-- **One piece of `+kern` fills its need** from the register `g1.re`
holding the subject (the inner step of `finishTop_genB`). -/
theorem kernFill {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {g1 g4 : Gen Map} {sur : Sure S} {o : Nat} {A : List Pole} {s : Noun}
    (P : KernP (Map := Map) g1.re g4.cond (g1.re + 1) g4.re o sur A)
    (ag4 : ∀ k, k < g1.re + 1 → HoonMap.get g4.cond k = HoonMap.get g1.cond k)
    (u4r : HoonMap.get g4.cond g1.re = Option.none)
    (hd : Distinct sur.ned) (hr : ∀ x, NMem sur.ned x → x < g1.re)
    (hc : ∀ x, NMem sur.ned x → HoonMap.get g1.cond x = Option.none) :
    FillSem lib O c gul st t (Need.this g1.re) g1.re sur (A.map (renPole (unproxy g4.cond))) s s := by
  obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P
  have l0' : g1.re + 1 ≤ lo0 := l0
  have KS := sem (by omega) hd hr (unproxy g4.cond) (unproxy_none u4r)
    (fun x hx => unproxy_none (by rw [ag4 x (by have := hr x hx; omega)]; exact hc x hx))
    (fun _ _ => rfl)
  intro R hR
  obtain ⟨S1, S2⟩ := KS lib σ O c gul st t R s hR
  refine ⟨fun f => ?_, S2⟩
  obtain ⟨R', a, b, k⟩ := S1 f
  exact ⟨R', a, b, fun x hx hn => k x (by
    rcases hx with hx | hx
    · simp only [NMem] at hx; omega
    · omega) hn⟩

/-! ## The relation under `%done` -/

/-- **The forward `sem` under `%done` with `AgreeG`.** -/
def SemGD (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **The backward `sem` under `%done` with `AgreeG`.** -/
def SemGDB (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **`RunOKGB` at any lazy result**: `LabDisj` for `nodup`, `AgreeG` (per
label, at every state and trace) for `AgreeUB`. -/
structure RunOKGD (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (GMem goal r ∨ g0.re ≤ r) ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  labDisj : LabDisj nex.laz
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f goal s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemGD lib N P f goal g0 g1 nex
  semB : SemGDB lib N P f goal g0 g1 nex

/-- **`AgreeG` with distinct labels and every label from `g0.bo` is `AgreeUB`.** -/
theorem AgreeG.toUB {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeG lib O c gul st t cond ned g0 g1 laz s0 s) (hnd : ((entries laz).map Prod.fst).Nodup)
    (hl : ∀ e ∈ entries laz, g0.bo ≤ e.1) : AgreeUB lib O c gul st t cond ned g0 g1 laz s0 s := by
  refine ⟨h.1, fun e he => ?_⟩
  obtain ⟨A, B, th, h1, h2, h3⟩ := (h.toLB hnd).2 e he (hl e he)
  exact ⟨A, B, th, h1, h2, h3⟩

/-- **The old relation under `%done` feeds the new one.** -/
theorem RunOKGB.toGD {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {goal : CGoal S} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKGB (Map := Map) lib N P f goal g0 g1 nex) : RunOKGD lib N P f goal g0 g1 nex := by
  have hl : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 := fun e he => (R.labs e he).1
  refine ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, labDisj_of_nodup R.nodup,
    R.nec, R.ncond, R.econd, ?_, ?_⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
      (fun st' => (ag st' t).toUB R.nodup hl) hned regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => (ag st' t).toUB R.nodup hl) hned regs hh hn res hres

/-! ## The top -/

/-- **`TopSB` with `LabDisj` for `nodup`.** -/
structure TopSG (g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext gen0 g1
  grow : GrowU gen0 g1
  cfr : CondFresh gen0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  args : nex.th.args = []
  regs : ∀ r, NMem nex.laz.sure.ned r → (gen0 : Gen Map).re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (gen0 : Gen Map).re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, (gen0 : Gen Map).bo ≤ e.1 ∧ e.1 < g1.bo ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  labDisj : LabDisj nex.laz
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none

/-- **`finishTop_genB` per label**: the program `+kerf` and `+to-straight`
make agrees with the run's blocks in the form `AgreeG` (the fill of the
conjunction of the needs at each label, at every state and trace), with no
`Nodup` of the result's labels. -/
theorem finishTop_genG (lib : Lib) {g1 : Gen Map} {nex : NextL S} (R : TopSG g1 nex)
    (Φ : (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop)
    (hsem : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned gen0 g1 nex.laz s s) → (∀ r, NMem ned r → g1.re ≤ r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
      Φ σ O st t gul s (goJ lib O c gul st regs t nex.th))
    (hnec : ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → Φ σ O st t gul s (some (Tone.two t, st)))
    {o sub : Nat} {g3 : Gen Map} (h2 : kerf nex g1 = some ((o, sub), g3))
    {c' : Straight Map} (hts : toStraightF g3.cond g3.blocks (Need.this sub) o = some c') :
    c'.need = NeedOrd.this ∧ ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (t : Trace) (gul : Noun),
      Φ σ O st t gul s (execEntry lib O st c' [s] t gul) := by
  have d1 : g1.drop = false := R.ext.2.2.1
  have cb1 : CondBelow g1 := R.cfr.below condBelow_gen0
  unfold kerf at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, g4, h3, h4⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have lt0 : nex.th.there < g1.bo := R.hi
  have hlab : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => (R.labs e he).2.1
  have cbe : CondBelow (g1.emitted ⟨[], [], Termin.hop nex.th⟩) := cb1
  obtain ⟨hr, W⟩ := kern_specL h3 d1 cbe
  simp only [Gen.emitted] at hr
  subst hr
  have eblk : ∀ k, HoonMap.get (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have nlab : g1.bo ∉ (entries nex.laz).map Prod.fst := fun hm => by
    obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := hlab e he; omega
  -- the hop block: one piece, the sure need's
  obtain ⟨As0, hA0, pA0, qA0⟩ := W.at_ g1.bo
  have at0 : atL ((g1.bo, nex.laz) :: entries nex.laz) g1.bo = [nex.laz.sure] := by
    simp only [atL, List.filter_cons, decide_true, ↓reduceIte, List.map_cons]
    rw [filter_fst_nil _ _ nlab]; rfl
  rw [at0, List.perm_singleton] at pA0
  obtain ⟨p0, rfl, hp0⟩ := List.map_eq_singleton_iff.mp pA0
  have P0 := qA0 p0 List.mem_cons_self
  rw [hp0] at P0
  have hB0 : HoonMap.get g4.blocks g1.bo = some ⟨[], p0.2, Termin.hop nex.th⟩ := by
    have := hA0 [] (Termin.hop nex.th) (by simp only [eblk]; simp)
    simpa using this
  -- the entries' blocks: one piece per entry at the label
  have hE : ∀ k ∈ (entries nex.laz).map Prod.fst, ∃ (As : List (Sure S × List Pole)) (B : List Pole) (th : Jmp),
      HoonMap.get g1.blocks k = some ⟨[], B, Termin.hop th⟩ ∧
      HoonMap.get g4.blocks k = some ⟨[], (As.map Prod.snd).flatten ++ B, Termin.hop th⟩ ∧
      (As.map Prod.fst).Perm (suresAt nex.laz k) ∧
      ∀ p ∈ As, KernP g1.re g4.cond (g1.re + 1) g4.re k p.1 p.2 := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨_, _, B, th, hth⟩ := R.labs e he
    obtain ⟨As, hA, pA, qA⟩ := W.at_ e.1
    have ne : e.1 ≠ g1.bo := by have := hlab e he; omega
    have atE : atL ((g1.bo, nex.laz) :: entries nex.laz) e.1 = suresAt nex.laz e.1 := by
      simp only [atL, List.filter_cons, ne.symm, decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
    refine ⟨As, B, th, hth, ?_, atE ▸ pA, qA⟩
    exact hA B (Termin.hop th) (by simp only [eblk, ne, ↓reduceIte]; exact hth)
  have hO : ∀ k, k ≠ g1.bo → k ∉ (entries nex.laz).map Prod.fst → HoonMap.get g4.blocks k = HoonMap.get g1.blocks k := by
    intro k k1 k2
    rw [W.other k (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨k1, k2⟩)]
    simp only [eblk, k1, ↓reduceIte]
  -- the program: the blocks unproxied
  let c1 : Straight Map := ⟨NeedOrd.none, 0, mapVals (unproxyBlob g4.cond) g4.blocks⟩
  have hag : ∀ k, HoonMap.get c1.blocks k = (HoonMap.get g4.blocks k).map (unproxyBlob g4.cond) :=
    fun k => get_mapVals _ _ k
  have D1 := downRk_gen0 (R.grow.trans (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩)
    (fun j hj => by simp [finJumps] at hj; subst hj; exact ⟨R.lo, lt0⟩) (upBelow_of_growU R.grow)))
  have D4 := downRk_of_fins D1 (bs' := g4.blocks) fun k b' hk => by
    by_cases e1 : k = g1.bo
    · subst e1; rw [hB0] at hk; cases hk; exact ⟨⟨[], [], Termin.hop nex.th⟩, by rw [eblk]; simp, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨As, B, th, h1', h4', _⟩ := hE k e2
      rw [h4'] at hk; cases hk
      exact ⟨⟨[], B, Termin.hop th⟩, by rw [eblk, if_neg e1]; exact h1', rfl⟩
    · rw [hO k e1 e2] at hk; exact ⟨b', by rw [eblk, if_neg e1]; exact hk, rfl⟩
  have Dc : DownRk (upRk (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks) c1.blocks := by
    intro k b hk
    rw [hag k] at hk
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact downRk_unproxy _ (D4 k b0 hb0)
  obtain ⟨hneed, start, hst, hent⟩ := toStraightF_entryU hts (by simp [flattenNeed, isRun]) D4 Dc
    (fun k _ => hag k)
  rw [hB0] at hst; cases hst
  refine ⟨hneed, fun σ O st s t gul => ?_⟩
  obtain ⟨R0, hR0, he⟩ := hent lib O st s [s] t gul (by rw [hneed]; rfl)
  rw [he]
  have ag4 : ∀ k, k < g1.re + 1 → HoonMap.get g4.cond k = HoonMap.get g1.cond k := fun k hk => W.cnd.1.get_lt hk
  have u4r : HoonMap.get g4.cond g1.re = Option.none := by
    rw [ag4 _ (Nat.lt_succ_self _)]; exact condBelow_none cb1 (Nat.le_refl _)
  have regs1 : ∀ x, NMem nex.laz.sure.ned x → x < g1.re := fun x hx => (R.regs x hx).2
  have hj : nex.th.args = [] := R.args
  have hrj : renJmp (unproxy g4.cond) nex.th = nex.th := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hj; simp only at hj; subst hj; rfl
  -- the agreement of the program with the run's blocks, per label
  have ag : ∀ (st' : σ) (t' : Trace), AgreeG lib O c1 gul st' t' g4.cond (Need.this g1.re) gen0 g1 nex.laz s s :=
    fun st' t' => by
    refine ⟨fun o' _ u hnl => ?_, fun k hk _ => ?_⟩
    · rw [hag o', hO o' (by omega) hnl]
    · obtain ⟨As, B, th, h1', h4', pA, qA⟩ := hE k hk
      refine ⟨((As.map Prod.snd).flatten).map (renPole (unproxy g4.cond)), B, th, h1', ?_, ?_⟩
      · rw [hag, h4']; simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, List.map_append]
      · have memE : ∀ p ∈ As, ∃ e ∈ entries nex.laz, e.1 = k ∧ e.2.sure = p.1 := fun p hp =>
          mem_suresAt (pA.mem_iff.mp (List.mem_map.mpr ⟨p, hp, rfl⟩))
        let As' : List (Sure S × List Pole) := As.map fun p => (p.1, p.2.map (renPole (unproxy g4.cond)))
        have e1 : As'.map Prod.fst = As.map Prod.fst := by simp [As']
        have e2 : (As'.map Prod.snd).flatten = ((As.map Prod.snd).flatten).map (renPole (unproxy g4.cond)) := by
          simp only [As', List.map_flatten, List.map_map]; rfl
        have F := fillSemL_list (lib := lib) (O := O) (c := c1) (gul := gul) (st := st') (t := t')
          (ned := Need.this g1.re) (lo := g1.re) (s0 := s) (s := s) As'
          (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            obtain ⟨e, he, -, hes⟩ := memE p hp
            refine kernFill (qA p hp) ag4 u4r (hes ▸ (R.eregs e he).1) (fun x hx => ?_) (fun x hx => ?_)
            · exact ((R.eregs e he).2 x (hes ▸ hx)).2
            · exact R.econd e he x (hes ▸ hx))
          (fun q hq x hx => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            obtain ⟨e, he, -, hes⟩ := memE p hp
            exact ((R.eregs e he).2 x (hes ▸ hx)).2)
          (fun x hx => by simp only [NMem] at hx; omega)
          (by rw [e1]; exact (pA.pairwise_iff (fun h r a b => h r b a)).mpr (labDisj_at R.labDisj k))
        rw [e1, e2] at F
        exact F.perm pA
  -- the ops at the hop block, then the run
  obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P0
  have l0' : g1.re + 1 ≤ lo0 := l0
  have KS := sem (by omega) R.dist regs1 (unproxy g4.cond) (unproxy_none u4r)
    (fun x hx => unproxy_none (by rw [ag4 x (by have := regs1 x hx; omega)]; exact R.ncond x hx))
    (fun _ _ => rfl)
  obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st t R0 s hR0
  simp only [unproxyBlob, renBlob, List.map_nil, renFin, hrj]
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := S1 fo
    have e1 := hr1 [] (Termin.hop nex.th)
    simp only [List.append_nil] at e1
    rw [e1, execBlob_hop]
    have hn1 : HoldsN (Need.this g1.re) R1 s := by
      show SkaModel.read g1.re R1 = some s
      rw [kr1 g1.re (by omega) (fun hm => by have := regs1 _ hm; omega)]; exact hR0
    exact hsem g4.cond (fun k hk => ag4 k (by omega)) c1 (Need.this g1.re) σ O st t gul s ag
      (fun x hx => by simp only [NMem] at hx; omega) R1 hh1 hn1
  · have e2 := S2 fo [] (Termin.hop nex.th)
    simp only [List.append_nil] at e2
    rw [e2]; exact hnec σ O st t gul s fo

/-- **The contract from `RunOKGD` under `%done`**: the whole-subject code of
a nomm whose run for `%done` from `gen0` meets `RunOKGD` (labels possibly
repeated) has the need `this` and meets both halves of the contract. -/
theorem finishLUC_contractGD (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → RunOKGD lib N P f (CGoal.done : CGoal S) gen0 gE nex)
    {c : Straight Map} (h : finishLUC (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  unfold finishLUC at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  have R : RunOKGD lib N P f (CGoal.done : CGoal S) gen0 gE nex := hR hr
  have T : TopSG gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      labDisj := R.labDisj
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTop_genG lib T (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) hk hts
  have B := finishTop_genG lib T (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs => ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩⟩
  · exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr
  · exact B.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

end Comp
end SkaModel
end Formalization
