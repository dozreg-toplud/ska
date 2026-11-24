import lemmas.Ska.CompCollapseGate
import lemmas.Ska.CompBelowRun

/-!
# The first half of `+collapse-lazy-atom` in `[4 p]`, for every shape of the need

README Gaps 12.2, the collapse case.  The `%4` case of `run` under a goal
`%next laz th` first runs `+collapse-lazy-atom` and then, when that returns
`~`, takes a fresh register (`collPick`).  `collapsePre_spec` describes the two
together for every shape that `+sure-require-look` gives the sure need:

* `this d` (the need is `this d` with looks at axis `1` only): `r = d`,
  `there = th.there`, nothing at `th.there`;
* `none` (the need is `none` with looks at axis `1` only, and some fork or
  bond asks something): a fresh `r`, `there = th.there`, nothing at
  `th.there`;
* `pair` (the need takes the noun apart): a fresh `r` and a new block
  `[%bom ~]` at `there`;
* `both r'`: `r = r'` and a new block `[%bom ~]` at `there`;
* and the need equivalent to `none` (`+collapse-lazy-atom` returns `~`): a
  fresh `r`, `there = th.there`, and no op anywhere.

In the first two and the last, every atom fits the goal's sure need and `r`
holding it holds that need (`CollPre.shape`, first branch).  In `pair` and
`both` no atom fits it, and the ops the walk puts in front of the `[%bom ~]`
block do what `CollP r` says, so the block crashes whatever they do.  Checked
against the raw blocks of `tools/hoon/proxy-dump.hoon` (2026-11-24): for
`[7 [4 [0 3]] [0 2]]` the `%inc` hops to a block `[%bom ~]`; for
`[7 [4 [0 3]] [1 5]]` it writes a fresh register; for
`[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [0 2]]]` the lazy block of the branch
`[0 2]` gets `[%cel v3] [%imm 0 v1]`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A step that only allocates registers is a walk over no block. -/
theorem WalkOKD.of_re {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} {r : Nat}
    (g : Gen Map) (k : Nat) (hk : g.re ≤ k) : WalkOKD (ProxyFor r) P g { g with re := k } [] :=
  ⟨rfl, rfl, hk, ProxyFor.of_eq hk rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- The gate at the goal's own block, for the need `this d`: nothing. -/
theorem collapseGate_self {d o : Nat} {lok : S} {g g' : Gen Map}
    (hl : ∀ x ∈ HoonSet.toList lok, x = 1)
    (h : collapseGate (S := S) (Map := Map) d o o ⟨Need.this d, lok⟩ g = some ((), g')) :
    ∃ k, g.re ≤ k ∧ g' = { g with re := k } := by
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  have e : ned = Need.this d := L.same hl
  subst e
  obtain ⟨kk, rfl⟩ := L.gen
  simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  exact ⟨kk, L.le, rfl⟩

/-- Looks at axis `1` only hold of every noun. -/
theorem looks_one {lok : S} (hl : ∀ x ∈ HoonSet.toList lok, x = 1) (n : Noun) : Looks lok n :=
  fun x hx => by rw [hl x hx]; simp

/-- A need that `+sure-require-look` turns into one that an atom fits had
looks at axis `1` only. -/
theorem sureOK_small {sur : Sure S} {g0 g1 : Gen Map} {ned' : Need}
    (L : SureOK sur.ned (HoonSet.toList sur.lok) g0 g1 ned') (hf : Fits ned' (A 0)) :
    ∀ x ∈ HoonSet.toList sur.lok, x = 1 := by
  intro x hx
  have f := ((L.fits (A 0)).mp hf).2 x hx
  by_cases h2 : 2 ≤ x
  · rcases L.big ⟨x, hx, h2⟩ with ⟨p, q, e⟩ | ⟨y, p, q, e⟩ <;> (subst e; exact hf.elim)
  · have : x = 0 ∨ x = 1 := by omega
    rcases this with rfl | rfl
    · simp [slot?_zero] at f
    · rfl

/-- A need that `+sure-require-look` turns into a pair or a `both` fits no
atom. -/
theorem sureOK_noFit {sur : Sure S} {g0 g1 : Gen Map} {ned' : Need}
    (L : SureOK sur.ned (HoonSet.toList sur.lok) g0 g1 ned') (hf : ∀ v, ¬ Fits ned' (A v)) :
    ∀ v, ¬ FitsS sur (A v) := fun v f => hf v ((L.fits (A v)).mpr f)

/-! ## Needs equivalent to `none` -/

mutual
theorem noneEq_entries : ∀ (l : Lazy S), noneEquivalentL l = true → ∀ e ∈ entries l, noneEquivalentL e.2 = true
  | mk s fk bd, h, e, he => by
    simp only [noneEquivalentL, Bool.and_eq_true] at h
    simp only [entries, List.mem_append] at he
    rcases he with he | he
    · exact noneEq_bonds bd h.2 e he
    · exact noneEq_forks fk h.1.2 e he

theorem noneEq_bonds : ∀ (bd : List (Nat × Lazy S)), noneBonds bd = true →
    ∀ e ∈ bondEntries bd, noneEquivalentL e.2 = true
  | [], _, e, he => by simp [bondEntries] at he
  | (o, l) :: rest, h, e, he => by
    simp only [noneBonds, Bool.and_eq_true] at h
    simp only [bondEntries, List.mem_append, List.mem_cons] at he
    rcases he with (rfl | he) | he
    · exact h.1
    · exact noneEq_entries l h.1 e he
    · exact noneEq_bonds rest h.2 e he

theorem noneEq_forks : ∀ (fk : List (ForkE S)), noneForks fk = true →
    ∀ e ∈ forkEntries fk, noneEquivalentL e.2 = true
  | [], _, e, he => by simp [forkEntries] at he
  | ((oy, y), (on, n)) :: rest, h, e, he => by
    simp only [noneForks, Bool.and_eq_true] at h
    simp only [forkEntries, List.mem_append, List.mem_cons] at he
    rcases he with ((rfl | he) | (rfl | he)) | he
    · exact h.1.1
    · exact noneEq_entries y h.1.1 e he
    · exact h.1.2
    · exact noneEq_entries n h.1.2 e he
    · exact noneEq_forks rest h.2 e he
end

theorem noneEq_sure {l : Lazy S} (h : noneEquivalentL l = true) :
    l.sure.ned = Need.none ∧ ∀ x ∈ HoonSet.toList l.sure.lok, x = 1 := by
  rcases l with ⟨s, fk, bd⟩
  simp only [noneEquivalentL, Bool.and_eq_true, decide_eq_true_eq, HoonSet.small_iff] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

/-- No op at a block whose need is equivalent to `none`. -/
theorem collP_noneEq {r : Nat} {cond : Map (Nat × List Nat)} {lo hi o : Nat} {l : Lazy S}
    (h : noneEquivalentL l = true) : CollP (Map := Map) r cond lo hi o l.sure [] := by
  obtain ⟨hs, hl⟩ := noneEq_sure h
  intro u _ _ _ lib σ O c gul st t R v _
  have fit : FitsS l.sure (A v) := ⟨by rw [hs]; trivial, looks_one hl _⟩
  exact ⟨fun _ => ⟨R, Runs.nil R, ⟨by rw [hs]; trivial, looks_one hl _⟩, fun _ _ => rfl⟩,
    fun nf => absurd fit nf⟩

/-! ## The walk -/

/-- A walk that changes only the blocks of its entries, each by ops in front,
grows the state. -/
theorem WalkOKD.grow {C : Gen Map → Gen Map → Prop}
    {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} {g g' : Gen Map}
    {es : List (Nat × Lazy S)} (W : WalkOKD C P g g' es)
    (hlab : ∀ e ∈ es, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) : Grow g g' := by
  refine ⟨by rw [W.bo]; exact Nat.le_refl _, W.drop, fun kk b _ hb => ?_, fun kk b' hb' => ?_⟩
  · by_cases hm : kk ∈ es.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      obtain ⟨B, fin, hB⟩ := hlab e he
      obtain ⟨A, hA, _⟩ := W.at_ e he
      rw [hB] at hb; cases hb
      exact ⟨_, hA B fin hB, rfl, rfl⟩
    · exact ⟨b, (W.other kk hm).trans hb, rfl, rfl⟩
  · by_cases hm : kk ∈ es.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      obtain ⟨B, fin, hB⟩ := hlab e he
      obtain ⟨A, hA, _⟩ := W.at_ e he
      rw [hA B fin hB] at hb'; cases hb'
      exact Or.inl ⟨_, hB, rfl, rfl⟩
    · rw [W.other kk hm] at hb'
      exact Or.inl ⟨b', hb', rfl, rfl⟩

/-- **The walk of `+collapse-lazy-atom` when its own block wants `this d`
with looks at axis `1` only**: nothing at that block, the gate's ops at
every entry. -/
theorem walkThis {s : Sure S} {fk : List (ForkE S)} {bd : List (Nat × Lazy S)} {d o : Nat} {g gW : Gen Map}
    (hW : walkLazy (collapseGate d o) o (mk ⟨Need.this d, s.lok⟩ fk bd) g = some ((), gW))
    (hl : ∀ x ∈ HoonSet.toList s.lok, x = 1) (d0 : g.drop = false)
    (hn : (o :: (entries (mk s fk bd)).map Prod.fst).Nodup) :
    WalkOKD (ProxyFor d) (CollP (S := S) (Map := Map) d) g gW (entries (mk s fk bd)) := by
  unfold walkLazy at hW
  obtain ⟨u1, gA, hA, hr⟩ := bind_some hW
  obtain ⟨k2, hk2, hgA⟩ := collapseGate_self hl hA
  have W0 : WalkOKD (ProxyFor d) (CollP (S := S) (Map := Map) d) g gA [] := by
    rw [hgA]; exact WalkOKD.of_re (P := CollP (S := S) (Map := Map) d) (r := d) g k2 hk2
  have dA : gA.drop = false := by rw [hgA]; exact d0
  have ct : ∀ a b c : Gen Map, ProxyFor d a b → ProxyFor d b c → ProxyFor d a c := fun _ _ _ x y => ProxyFor.trans x y
  have cb : ∀ a b : Gen Map, ProxyFor d a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k :=
    fun _ _ x _ hk => ProxyFor.get_lt x hk
  have hn' := (List.nodup_cons.mp hn).2
  simp only [entries, List.map_append] at hn' ⊢
  split at hr
  · rename_i hfb
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
    obtain ⟨rfl, rfl⟩ := hfb
    have h' : some ((), _) = some ((), gW) := hr
    cases h'
    simpa [bondEntries, forkEntries] using W0
  · obtain ⟨u2, gB, h2, h3⟩ := bind_some hr
    have WF := walkForks_okD (ProxyFor.refl d) ct cb (collP_mono d) (collapseGate_ok d o) fk _ gB h2 dA
      (List.nodup_append.mp hn').2.1
    have WB := walkBonds_okD (ProxyFor.refl d) ct cb (collP_mono d) (collapseGate_ok d o) bd gB gW h3
      (WF.drop.trans dA) (List.nodup_append.mp hn').1
    have W := (W0.trans ct cb (collP_mono d) WF (fun x hx => absurd hx List.not_mem_nil)).trans ct cb
      (collP_mono d) WB (by
        intro x hx hm
        simp only [List.nil_append] at hx
        exact nodup_disj hn' x hm hx)
    exact W.congr fun e => by
      simp only [List.nil_append, List.mem_append]
      exact Or.comm

/-! ## Fact (i5) of the walk -/

section Keys
variable [HoonMapKeys Map]

/-- **The gate of `+collapse-lazy-atom` keeps (i5)** when `r` and the
block's need are below `re`: its ops mention `r` or a proxy, and the
registers of the need `+sure-require-look` gives. -/
theorem keeps_collapseGate {r o oL : Nat} {sur : Sure S} {g g' : Gen Map} (hd : g.drop = false) (hr : r < g.re)
    (hn : NB g.re sur.ned) (h : collapseGate (S := S) (Map := Map) r o oL sur g = some ((), g')) : Keeps g g' := by
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  obtain ⟨k1, n1⟩ := keeps_sureRequireLook hn h1
  have r1 : r < g1.re := Nat.lt_of_lt_of_le hr k1.le
  have d1 := k1.dropF hd
  have srcK : ∀ (src : Nat) (g2 : Gen Map), (if oL = o then pure r else proxy r oL : CM Map Nat) g1 = some (src, g2) →
      Keeps g1 g2 ∧ src < g2.re := by
    intro src g2 hs
    obtain ⟨-, hb2, hd2, hbo2, hre2, hsrc⟩ := collSrc_spec hs d1
    have sl : src < g2.re := by
      rcases hsrc with e | ⟨lt, _⟩
      · rw [e]; omega
      · exact lt
    by_cases e : oL = o
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      exact ⟨Keeps.refl _, sl⟩
    · rw [if_neg e] at hs
      exact ⟨⟨fun lo hl => belowIn_proxy hl hs, hre2, hd2, by omega⟩, sl⟩
  rcases ned with ⟨p, q⟩ | ⟨x, p, q⟩ | r' | _
  · obtain ⟨src, g2, hs, ha⟩ := bind_some h2
    obtain ⟨k2, s2⟩ := srcK src g2 hs
    exact k1.trans (k2.trans (keeps_crashNeed (n1.mono k2.le) (fun p e => by cases e; exact s2) ha))
  · obtain ⟨src, g2, hs, ha⟩ := bind_some h2
    obtain ⟨k2, s2⟩ := srcK src g2 hs
    exact k1.trans (k2.trans (keeps_crashNeed (n1.mono k2.le) (fun p e => by cases e; exact s2) ha))
  · simp only at h2
    by_cases e : r = r'
    · rw [if_pos e] at h2
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      exact k1
    · rw [if_neg e] at h2
      obtain ⟨src, g2, hs, ha⟩ := bind_some h2
      obtain ⟨k2, s2⟩ := srcK src g2 hs
      exact k1.trans (k2.trans (keeps_addOps (regsIn_mov s2 (Nat.lt_of_lt_of_le (n1 r' rfl) k2.le)
        (RegsIn.nil _)) ha).1)
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    exact k1

mutual
/-- **The walk of `+collapse-lazy-atom` keeps (i5)**, when `r` and the
needs of every block it visits are below `re`. -/
theorem keeps_walkColl {r o : Nat} : ∀ (oL : Nat) (l : Lazy S) (g g' : Gen Map),
    walkLazy (collapseGate (S := S) (Map := Map) r o) oL l g = some ((), g') → g.drop = false → r < g.re →
    (∀ e ∈ (oL, l) :: entries l, NB g.re e.2.sure.ned) → Keeps g g'
  | oL, mk s fk bd, g, g', h, hd, hr, hn => by
    unfold walkLazy at h
    obtain ⟨u, g1, h1, hr'⟩ := bind_some h
    cases u
    have k1 := keeps_collapseGate hd hr (hn _ (List.mem_cons_self ..)) h1
    have hn' : ∀ e ∈ entries (mk s fk bd), NB g1.re e.2.sure.ned :=
      fun e he => (hn e (List.mem_cons_of_mem _ he)).mono k1.le
    simp only [entries, List.mem_append] at hn'
    split at hr'
    · have h' : some ((), _) = some ((), g') := hr'
      cases h'
      exact k1
    · obtain ⟨u2, g2, h2, h3⟩ := bind_some hr'
      cases u2
      have k2 := keeps_walkForksColl fk g1 g2 h2 (k1.dropF hd) (Nat.lt_of_lt_of_le hr k1.le)
        (fun e he => hn' e (Or.inr he))
      have k3 := keeps_walkBondsColl bd g2 g' h3 (k2.dropF (k1.dropF hd)) (Nat.lt_of_lt_of_le hr (k1.trans k2).le)
        (fun e he => (hn' e (Or.inl he)).mono k2.le)
      exact k1.trans (k2.trans k3)

theorem keeps_walkForksColl {r o : Nat} : ∀ (fk : List (ForkE S)) (g g' : Gen Map),
    walkForks (collapseGate (S := S) (Map := Map) r o) fk g = some ((), g') → g.drop = false → r < g.re →
    (∀ e ∈ forkEntries fk, NB g.re e.2.sure.ned) → Keeps g g'
  | [], g, g', h, _, _, _ => by
    simp only [walkForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Keeps.refl _
  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hr, hn => by
    unfold walkForks at h
    obtain ⟨u1, g1, h1, h⟩ := bind_some h
    obtain ⟨u2, g2, h2, h3⟩ := bind_some h
    cases u1; cases u2
    simp only [forkEntries, List.mem_append, List.mem_cons] at hn
    have k1 := keeps_walkColl oy y g g1 h1 hd hr (fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hn _ (Or.inl (Or.inl (Or.inl rfl)))
      · exact hn _ (Or.inl (Or.inl (Or.inr he))))
    have k2 := keeps_walkColl on n g1 g2 h2 (k1.dropF hd) (Nat.lt_of_lt_of_le hr k1.le) (fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact (hn _ (Or.inl (Or.inr (Or.inl rfl)))).mono k1.le
      · exact (hn _ (Or.inl (Or.inr (Or.inr he)))).mono k1.le)
    have k3 := keeps_walkForksColl rest g2 g' h3 (k2.dropF (k1.dropF hd)) (Nat.lt_of_lt_of_le hr (k1.trans k2).le)
      (fun e he => (hn e (Or.inr he)).mono (k1.trans k2).le)
    exact k1.trans (k2.trans k3)

theorem keeps_walkBondsColl {r o : Nat} : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map),
    walkBonds (collapseGate (S := S) (Map := Map) r o) bd g = some ((), g') → g.drop = false → r < g.re →
    (∀ e ∈ bondEntries bd, NB g.re e.2.sure.ned) → Keeps g g'
  | [], g, g', h, _, _, _ => by
    simp only [walkBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Keeps.refl _
  | (ob, l) :: rest, g, g', h, hd, hr, hn => by
    unfold walkBonds at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    cases u1
    simp only [bondEntries, List.mem_append] at hn
    have k1 := keeps_walkColl ob l g g1 h1 hd hr (fun e he => hn e (Or.inl he))
    have k2 := keeps_walkBondsColl rest g1 g' h2 (k1.dropF hd) (Nat.lt_of_lt_of_le hr k1.le)
      (fun e he => (hn e (Or.inr he)).mono k1.le)
    exact k1.trans k2
end

/-! ## The first half of the `%4` case -/

/-- The choice of the register and the label after `+collapse-lazy-atom` in
the `%4` case of `run`. -/
def collPick (th : Jmp) : Option (Nat × Nat) → CM Map (Nat × Nat)
  | some x => pure x
  | Option.none => do
    let r ← re
    if th.args = [] then pure (r, th.there) else fun _ => Option.none

/-- **What the first half of the `%4` case does** under `%next laz th`: the
register `r` the increment writes, the label `there` it hops to, the ops at
the goal's entries (`CollP r` at the end's `cond`), `cond` grown by proxies
for `r` only, and either every atom fits the sure need and `r` holding it
holds the need, with `there = th.there` and no new block, or no atom fits it
and `there` is a new block `[%bom ~]` with the gate's ops in front. -/
structure CollPre (laz : Lazy S) (th : Jmp) (g0 g2 : Gen Map) (r there : Nat) : Prop where
  args : th.args = []
  drop : g2.drop = g0.drop
  le : g0.re ≤ g2.re
  bo1 : g0.bo ≤ g2.bo
  grow : Grow g0 g2
  keeps : Keeps g0 g2
  pfor : ProxyFor r g0 g2
  rlt : r < g2.re
  rkey : HoonMap.get g2.cond r = Option.none
  rreg : NMem laz.sure.ned r ∨ g0.re ≤ r
  other : ∀ o, o < g0.bo → o ∉ (entries laz).map Prod.fst → HoonMap.get g2.blocks o = HoonMap.get g0.blocks o
  at_ : ∀ e ∈ entries laz, ∃ A : List Pole, (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ →
    HoonMap.get g2.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧ CollP (S := S) r g2.cond g0.re g2.re e.1 e.2.sure A
  shape : (there = th.there ∧ g2.bo = g0.bo ∧ (∀ v, FitsS laz.sure (A v)) ∧
      ∀ (R : Map (Option Noun)) v, SkaModel.read r R = some (A v) → HoldsS laz.sure R (A v)) ∨
    (there = g0.bo ∧ g2.bo = g0.bo + 1 ∧ (∀ v, ¬ FitsS laz.sure (A v)) ∧
      ∃ F, HoonMap.get g2.blocks g0.bo = some ⟨[], F, Termin.bom Option.none⟩ ∧
        CollP (S := S) r g2.cond g0.re g2.re g0.bo ⟨Need.this r, laz.sure.lok⟩ F)

/-- The fit shapes: the walk starts at `th.there`, where it puts nothing. -/
theorem collPre_fit {laz : Lazy S} {th : Jmp} {g0 gW : Gen Map} {r k : Nat}
    (ea : th.args = []) (d0 : g0.drop = false) (hk : g0.re ≤ k) (hr : r < k)
    (hrk : HoonMap.get g0.cond r = Option.none) (hrr : NMem laz.sure.ned r ∨ g0.re ≤ r)
    (hl : ∀ x ∈ HoonSet.toList laz.sure.lok, x = 1) (hfits : ∀ v, Fits laz.sure.ned (A v))
    (hfit : ∀ (R : Map (Option Noun)) v, SkaModel.read r R = some (A v) → HoldsN laz.sure.ned R (A v))
    (hn : (th.there :: (entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hen : ∀ e ∈ entries laz, NB g0.re e.2.sure.ned)
    (hW : walkLazy (collapseGate r th.there) th.there (mk ⟨Need.this r, laz.sure.lok⟩ laz.fork laz.bond)
      { g0 with re := k } = some ((), gW)) :
    CollPre laz th g0 gW r th.there := by
  rcases laz with ⟨s, fk, bd⟩
  simp only [sure_mk, fork_mk, bond_mk] at hW hl hfits hfit hrr ⊢
  have KW := keeps_walkColl _ _ _ _ hW d0 hr (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact nb_this hr
    · exact (hen e he).mono hk)
  have W := walkThis hW hl d0 hn
  have hc : ∀ x, x < k → HoonMap.get gW.cond x = HoonMap.get g0.cond x := fun x hx => ProxyFor.get_lt W.cnd hx
  have Wle : k ≤ gW.re := W.le
  have Wbo : gW.bo = g0.bo := W.bo
  refine ⟨ea, W.drop, by omega, by omega, (grow_reg g0 k).trans (W.grow hlab), (keeps_reg g0 k hk).trans KW,
    (ProxyFor.of_eq (r := r) (g := g0) (g' := { g0 with re := k }) hk rfl).trans W.cnd,
    by omega, by rw [hc r hr]; exact hrk, hrr, fun o _ hn' => W.other o hn', fun e he => ?_,
    Or.inl ⟨rfl, Wbo, fun v => ⟨hfits v, looks_one hl _⟩, fun R v hR => ⟨hfit R v hR, looks_one hl _⟩⟩⟩
  obtain ⟨A, hA, hP⟩ := W.at_ e he
  exact ⟨A, fun B fin hb => hA B fin hb, collP_mono r _ _ _ _ _ _ _ _ _ hP (fun _ _ => rfl) hk (Nat.le_refl _)⟩

/-- The crash shapes: the walk starts at a new block `[%bom ~]`. -/
theorem collPre_bom {laz : Lazy S} {th : Jmp} {g0 gW : Gen Map} {r k : Nat}
    (ea : th.args = []) (d0 : g0.drop = false) (hk : g0.re ≤ k) (hr : r < k)
    (hrk : HoonMap.get g0.cond r = Option.none) (hrr : NMem laz.sure.ned r ∨ g0.re ≤ r)
    (hnf : ∀ v, ¬ FitsS laz.sure (A v))
    (hn : ((entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hen : ∀ e ∈ entries laz, NB g0.re e.2.sure.ned)
    (hW : walkLazy (collapseGate r g0.bo) g0.bo (mk ⟨Need.this r, laz.sure.lok⟩ laz.fork laz.bond)
      (({ g0 with re := k } : Gen Map).emitted ⟨[], [], Termin.bom Option.none⟩) = some ((), gW)) :
    CollPre laz th g0 gW r g0.bo := by
  rcases laz with ⟨s, fk, bd⟩
  simp only [sure_mk, fork_mk, bond_mk] at hW hnf hrr ⊢
  obtain ⟨gM, hgM⟩ : ∃ gM : Gen Map, gM = (({ g0 with re := k } : Gen Map).emitted ⟨[], [], Termin.bom Option.none⟩) :=
    ⟨_, rfl⟩
  rw [← hgM] at hW
  have dM : gM.drop = false := by rw [hgM]; exact d0
  have boM : gM.bo = g0.bo + 1 := by rw [hgM]; rfl
  have reM : gM.re = k := by rw [hgM]; rfl
  have cnM : gM.cond = g0.cond := by rw [hgM]; rfl
  have bM : HoonMap.get gM.blocks g0.bo = some ⟨[], [], Termin.bom Option.none⟩ := by
    rw [hgM]; exact emitted_get ({ g0 with re := k } : Gen Map) _ d0
  have oM : ∀ o, o ≠ g0.bo → HoonMap.get gM.blocks o = HoonMap.get g0.blocks o := fun o ho => by
    rw [hgM]; simp [Gen.emitted, d0, HoonMap.get_put, ho]
  have ee : entries (mk (⟨Need.this r, s.lok⟩ : Sure S) fk bd) = entries (mk s fk bd) := rfl
  have hn' : (((g0.bo, mk (⟨Need.this r, s.lok⟩ : Sure S) fk bd) ::
      entries (mk (⟨Need.this r, s.lok⟩ : Sure S) fk bd)).map Prod.fst).Nodup := by
    rw [ee]
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := (hlab e he).1; omega, hn⟩
  have KW := keeps_walkColl _ _ _ _ hW dM (by omega) (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact nb_this (by omega)
    · rw [ee] at he; exact (hen e he).mono (by omega))
  have KM : Keeps g0 gM := by
    rw [hgM]
    exact (keeps_reg g0 k hk).trans (keeps_emit (g := ({ g0 with re := k } : Gen Map)) d0
      (blobIn_fin (f := Termin.bom Option.none) trivial) (emit_apply _ _)).1
  have W := walkLazy_okColl (r := r) (o := g0.bo) g0.bo _ gM gW hW dM hn'
  rw [ee] at W
  have hc : ∀ x, x < k → HoonMap.get gW.cond x = HoonMap.get g0.cond x := fun x hx => by
    rw [ProxyFor.get_lt W.cnd (by omega), cnM]
  have Wle : gM.re ≤ gW.re := W.le
  have Wbo : gW.bo = gM.bo := W.bo
  have GM : Grow g0 gM := by
    rw [hgM]; exact (grow_reg g0 k).trans (grow_emit (jumpsBelow_nil rfl _))
  have GW : Grow gM gW := W.grow (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨[], _, bM⟩
    · obtain ⟨l, B, fin, hB⟩ := hlab e he
      exact ⟨B, fin, by rw [oM _ (by omega)]; exact hB⟩)
  refine ⟨ea, W.drop.trans (dM.trans d0.symm), by omega, by omega, GM.trans GW, KM.trans KW,
    (ProxyFor.of_eq (r := r) (g := g0) (g' := gM) (by omega) cnM).trans W.cnd, by omega, by rw [hc r hr]; exact hrk, hrr, fun o ho hn2 => ?_,
    fun e he => ?_, Or.inr ⟨rfl, by omega, hnf, ?_⟩⟩
  · rw [W.other o (by
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨by omega, hn2⟩)]
    exact oM o (by omega)
  · obtain ⟨A, hA, hP⟩ := W.at_ e (List.mem_cons_of_mem _ he)
    have l := (hlab e he).1
    exact ⟨A, fun B fin hb => hA B fin (by rw [oM _ (by omega)]; exact hb),
      collP_mono r _ _ _ _ _ _ _ _ _ hP (fun _ _ => rfl) (by omega) (Nat.le_refl _)⟩
  · obtain ⟨A, hA, hP⟩ := W.at_ _ (List.mem_cons_self ..)
    have hb := hA [] _ bM
    rw [List.append_nil] at hb
    exact ⟨A, hb, collP_mono r _ _ _ _ _ _ _ _ _ hP (fun _ _ => rfl) (by omega) (Nat.le_refl _)⟩

/-- **The first half of the `%4` case for every shape of the sure need.** -/
theorem collapsePre_spec {laz : Lazy S} {th : Jmp} {g0 gA g2 : Gen Map} {a : Option (Nat × Nat)} {r there : Nat}
    (hc : collapseLazyAtomL ⟨laz, th⟩ g0 = some (a, gA)) (hm : collPick th a gA = some ((r, there), g2))
    (d0 : g0.drop = false) (hcb : CondBelow g0)
    (hnr : ∀ x, NMem laz.sure.ned x → x < g0.re)
    (hnc : ∀ x, NMem laz.sure.ned x → HoonMap.get g0.cond x = Option.none)
    (hn : (th.there :: (entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hen : ∀ e ∈ entries laz, NB g0.re e.2.sure.ned) :
    CollPre laz th g0 g2 r there := by
  have fresh : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g0.cond x with
    | none => rfl
    | some _ => have := hcb x (by simp [e]); omega
  have hlab' : ∀ e ∈ entries laz, ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ :=
    fun e he => (hlab e he).2
  unfold collapseLazyAtomL at hc
  dsimp only at hc
  by_cases ea : th.args ≠ []
  · rw [if_pos ea] at hc; cases hc
  rw [if_neg ea] at hc
  have ea' : th.args = [] := by simpa using ea
  by_cases ne : noneEquivalentL laz = true
  · rw [if_pos ne] at hc
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [collPick, bind_apply, re_apply, Option.bind_some, ea', if_true, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    obtain ⟨hs, hl⟩ := noneEq_sure ne
    refine ⟨ea', rfl, Nat.le_succ _, Nat.le_refl _, grow_re g0, keeps_reg g0 _ (Nat.le_succ _), ProxyFor.of_eq (Nat.le_succ _) rfl,
      Nat.lt_succ_self _, fresh _ (Nat.le_refl _), Or.inr (Nat.le_refl _), fun _ _ _ => rfl,
      fun e he => ⟨[], fun B fin hb => by simpa using hb, collP_noneEq (noneEq_entries laz ne e he)⟩,
      Or.inl ⟨rfl, rfl, fun v => ⟨by rw [hs]; trivial, looks_one hl _⟩,
        fun R v _ => ⟨by rw [hs]; trivial, looks_one hl _⟩⟩⟩
  rw [if_neg (by simpa using ne)] at hc
  obtain ⟨nedS, g1, h1, hc⟩ := bind_some hc
  have L := sureRequireLook_spec h1
  obtain ⟨k1, hk1⟩ := L.gen
  subst hk1
  have L1 : g0.re ≤ k1 := L.le
  rcases nedS with ⟨p, q⟩ | ⟨x, p, q⟩ | r' | _
  · -- `pair`: a fresh register and a new block `[%bom ~]`
    simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply, get_apply, d0,
      Bool.false_eq_true, if_false] at hc
    obtain ⟨⟨u, gW⟩, hW, hP⟩ := Option.bind_eq_some_iff.mp hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    simp only [collPick, pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    cases u
    exact collPre_bom (k := k1 + 1) ea' d0 (by omega) (Nat.lt_succ_self _) (fresh _ L1) (Or.inr L1)
      (sureOK_noFit L fun v f => f) (List.nodup_cons.mp hn).2 hlab hen (by simpa only [d0] using hW)
  · -- `both x`: `x` and a new block `[%bom ~]`
    simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply, get_apply, d0,
      Bool.false_eq_true, if_false] at hc
    obtain ⟨⟨u, gW⟩, hW, hP⟩ := Option.bind_eq_some_iff.mp hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    simp only [collPick, pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    have hx := L.mem x (Or.inl rfl)
    cases u
    exact collPre_bom (k := k1) ea' d0 L1
      (hx.elim (fun hx => by have := hnr x hx; omega) (fun hx => hx.2))
      (hx.elim (fun hx => hnc x hx) (fun hx => fresh x hx.1))
      (hx.elim (fun hx => Or.inl hx) (fun hx => Or.inr hx.1))
      (sureOK_noFit L fun v f => f) (List.nodup_cons.mp hn).2 hlab hen (by simpa only [d0] using hW)
  · -- `this r'`: the need was `this r'` with looks at axis `1` only
    have hl := sureOK_small L trivial
    have hs : Need.this r' = laz.sure.ned := L.same hl
    simp only [bind_apply, pure_apply, Option.bind_some, get_apply, d0, Bool.false_eq_true, if_false] at hc
    obtain ⟨⟨u, gW⟩, hW, hP⟩ := Option.bind_eq_some_iff.mp hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    simp only [collPick, pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    have hm' : NMem laz.sure.ned r' := by rw [← hs]; rfl
    cases u
    exact collPre_fit (k := k1) ea' d0 L1 (by have := hnr r' hm'; omega) (hnc r' hm') (Or.inl hm') hl
      (fun v => by rw [← hs]; trivial) (fun R v hR => by rw [← hs]; exact hR) hn hlab' hen (by simpa only [d0] using hW)
  · -- `none`: the need was `none` with looks at axis `1` only, and a fresh register
    have hl := sureOK_small L trivial
    have hs : Need.none = laz.sure.ned := L.same hl
    simp only [bind_apply, pure_apply, Option.bind_some, re_apply, get_apply, d0, Bool.false_eq_true,
      if_false] at hc
    obtain ⟨⟨u, gW⟩, hW, hP⟩ := Option.bind_eq_some_iff.mp hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    simp only [collPick, pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    cases u
    exact collPre_fit (k := k1 + 1) ea' d0 (by omega) (Nat.lt_succ_self _) (fresh _ L1) (Or.inr L1) hl
      (fun v => by rw [← hs]; trivial) (fun R v _ => by rw [← hs]; trivial) hn hlab' hen (by simpa only [d0] using hW)

end Keys

end Comp
end SkaModel
end Formalization
