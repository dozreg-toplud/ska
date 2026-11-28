import lemmas.Ska.RawInvSix6
import lemmas.Ska.CompForkNeed

/-!
# `ATS6` through the primitives and `+fork-sure`

README Gaps 14 (b), track D (fork `k6p`).  `ATS6` (`RawInvSix6.lean`: no
dangling jump, no cycle) is kept by:

* `k6p_acyc_new`: **the general step for no cycle**: when old labels keep
  their edges and jump to old labels only, and new labels jump to old
  labels only, `Acyc` carries over (`k6p_acyc_sub`: no new edge);
* `k6p_same`: a step that keeps `drop` and the blocks and does not lower
  `bo` (`k6p_re`, `k6p_oo`, `k6p_setTag`, `k6p_copyTag`, `k6p_proxy`,
  `k6p_forkNeedGo`);
* `k6p_put`: a block meeting `BATC` at a reserved label (below `bo`, no
  block, at least `1`) (`k6p_emir`), and `k6p_emitted`, `k6p_emit`: a block
  meeting `BATC` at `bo`;
* `k6p_repl`: a block replaced by one with the same parameters, jump
  targets among the old ones and `BATC` (`k6p_addOps`, `k6p_jabBlock`,
  `k6p_jabLens`: `jabBlock o (lensHop args)` when `args` has the length of
  the target's parameters);
* **`k6p_forkSure`**: the Prop form of `ksrForkSureSpec`
  (`RawInvCLCheckSixR.lean`): from `ATS6`, reserved `o0 ≠ o1` and a block at
  `o` with no parameter, `+fork-sure` keeps `ATS6` and every other block,
  puts the join at the old `bo` (the parameters of `sur`, `hop o`) and at
  `o0`, `o1` hops to it with the registers of the two new needs, which are
  copies of `sur`'s shape (`NCopy`), distinct, apart, fresh.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {Map : Type → Type} [HoonMap Map]

/-! ## No cycle -/

/-- **No cycle carries over** when the labels not in `N` keep their edges and
jump outside `N`, and the labels in `N` jump outside `N`. -/
theorem k6p_acyc_new {bl bl' : Map Blob} (N : Nat → Prop) (hA : Acyc bl)
    (h1 : ∀ x y, ¬ N x → JEdge bl' y x → JEdge bl y x)
    (h2 : ∀ x y, ¬ N x → JEdge bl y x → ¬ N y)
    (h3 : ∀ x y, N x → JEdge bl' y x → ¬ N y) : Acyc bl' := by
  have old : ∀ k, Acc (JEdge bl) k → ¬ N k → Acc (JEdge bl') k := by
    intro k hk
    induction hk with
    | intro k _ ih =>
      intro hn
      exact Acc.intro k fun y hy => ih y (h1 k y hn hy) (h2 k y hn (h1 k y hn hy))
  intro k
  by_cases hn : N k
  · exact Acc.intro k fun y hy => old y (hA y) (h3 k y hn hy)
  · exact old k (hA k) hn

/-- No new edge, no new cycle. -/
theorem k6p_acyc_sub {bl bl' : Map Blob} (hA : Acyc bl) (h : ∀ x y, JEdge bl' y x → JEdge bl y x) :
    Acyc bl' :=
  k6p_acyc_new (fun _ => False) hA (fun x y _ he => h x y he) (fun _ _ _ _ h => h) (fun _ _ h => h.elim)

/-! ## Helpers -/

/-- `BATC` kept when every old block stays with its parameters. -/
theorem k6p_batc_par {bl bl' : Map Blob}
    (hk : ∀ k b, HoonMap.get bl k = some b → ∃ b', HoonMap.get bl' k = some b' ∧ b'.par = b.par)
    {b : Blob} (h : BATC bl b) : BATC bl' b := by
  refine ⟨fun j hj => ?_, h.2⟩
  obtain ⟨b2, h2, e2⟩ := h.1 j hj
  obtain ⟨b2', h2', p2⟩ := hk _ b2 h2
  exact ⟨b2', h2', by rw [p2]; exact e2⟩

/-- No block at or above `bo`. -/
theorem k6p_free {g : Comp.Gen Map} (h : ATS6 g) {o : Nat} (ho : g.bo ≤ o) :
    HoonMap.get g.blocks o = Option.none := by
  cases e : HoonMap.get g.blocks o with
  | none => rfl
  | some b => have := (h.2.2.1 o b e).1; omega

/-- A jump target has a block. -/
theorem k6p_edge_some {g : Comp.Gen Map} (h : ATS6 g) {x y : Nat} (he : JEdge g.blocks y x) :
    ∃ b, HoonMap.get g.blocks y = some b := by
  obtain ⟨b, hb, j, hj, rfl⟩ := he
  obtain ⟨b2, h2, -⟩ := (h.2.2.1 x b hb).2.1.1 j hj
  exact ⟨b2, h2⟩

/-! ## Steps that keep the blocks -/

/-- **A step that keeps `drop` and the blocks and does not lower `bo`.** -/
theorem k6p_same {g g' : Comp.Gen Map} (h : ATS6 g) (hd : g'.drop = g.drop) (hbo : g.bo ≤ g'.bo)
    (hb : g'.blocks = g.blocks) : ATS6 g' := by
  obtain ⟨d, b1, hB, hA⟩ := h
  refine ⟨hd.trans d, by omega, fun k b hk => ?_, hb ▸ hA⟩
  rw [hb] at hk
  obtain ⟨l, B, l1⟩ := hB k b hk
  exact ⟨by omega, hb ▸ B, l1⟩

theorem k6p_re {g g' : Comp.Gen Map} {r : Nat} (h : ATS6 g) (hr : (re : CM Map Nat) g = some (r, g')) :
    ATS6 g' := by
  simp only [re, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  exact k6p_same h rfl (Nat.le_refl _) rfl

theorem k6p_oo {g g' : Comp.Gen Map} {o : Nat} (h : ATS6 g) (hr : (oo : CM Map Nat) g = some (o, g')) :
    ATS6 g' ∧ o = g.bo ∧ g'.bo = g.bo + 1 ∧ g'.blocks = g.blocks ∧ g'.re = g.re ∧ g'.cond = g.cond := by
  simp only [oo, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨k6p_same h rfl (Nat.le_succ _) rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem k6p_setTag {g g' : Comp.Gen Map} {o : Nat} {region : List Nat} (h : ATS6 g)
    (hr : (setTag o region : CM Map Unit) g = some ((), g')) : ATS6 g' := by
  simp only [setTag, Option.some.injEq, Prod.mk.injEq, true_and] at hr
  subst hr
  split
  · exact h
  · exact k6p_same h rfl (Nat.le_refl _) rfl

theorem k6p_copyTag {g g' : Comp.Gen Map} {frm : Nat} {tos : List Nat} (h : ATS6 g)
    (hr : (copyTag frm tos : CM Map Unit) g = some ((), g')) : ATS6 g' := by
  simp only [copyTag] at hr
  split at hr
  · simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hr
    subst hr; exact h
  · obtain ⟨region, -, e⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq, true_and] at e
    subst e
    exact k6p_same h rfl (Nat.le_refl _) rfl

theorem k6p_proxy {g g' : Comp.Gen Map} {r o p : Nat} (h : ATS6 g)
    (hr : (proxy r o : CM Map Nat) g = some (p, g')) : ATS6 g' := by
  simp only [proxy] at hr
  split at hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    exact k6p_same h rfl (Nat.le_refl _) rfl
  · obtain ⟨tag, -, e⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    exact k6p_same h rfl (Nat.le_refl _) rfl

/-! ## A new block -/

/-- **A block meeting `BATC` at a reserved label** (below `bo`, no block,
at least `1`). -/
theorem k6p_put {g g' : Comp.Gen Map} (h : ATS6 g) {o : Nat} {b : Blob} (ho : o < g.bo) (h1 : 1 ≤ o)
    (hn : HoonMap.get g.blocks o = Option.none) (hb : BATC g.blocks b)
    (hg : g'.blocks = HoonMap.put g.blocks o b) (hd : g'.drop = g.drop) (hbo : g'.bo = g.bo) : ATS6 g' := by
  obtain ⟨d, b1, hB, hA⟩ := h
  have hkp : ∀ k b0, HoonMap.get g.blocks k = some b0 →
      ∃ b', HoonMap.get g'.blocks k = some b' ∧ b'.par = b0.par := by
    intro k b0 hk
    have : k ≠ o := by rintro rfl; rw [hn] at hk; cases hk
    exact ⟨b0, by rw [hg, get_put_ne this]; exact hk, rfl⟩
  refine ⟨hd.trans d, hbo ▸ b1, fun k b' hk => ?_, ?_⟩
  · rw [hg] at hk
    by_cases e : k = o
    · subst e; rw [get_put_self] at hk; cases hk
      exact ⟨hbo ▸ ho, k6p_batc_par hkp hb, h1⟩
    · rw [get_put_ne e] at hk
      obtain ⟨l, B, l1⟩ := hB k b' hk
      exact ⟨hbo ▸ l, k6p_batc_par hkp B, l1⟩
  · rw [hg]
    refine k6p_acyc_new (· = o) hA (fun x y hx he => ?_) (fun x y hx he => ?_) (fun x y hx he => ?_)
    · obtain ⟨b0, hb0, j, hj, e⟩ := he
      exact ⟨b0, by rw [get_put_ne hx] at hb0; exact hb0, j, hj, e⟩
    · intro hy
      obtain ⟨b0, hb0, j, hj, ej⟩ := he
      obtain ⟨b2, h2, -⟩ := (hB x b0 hb0).2.1.1 j hj
      rw [ej, hy, hn] at h2; cases h2
    · intro hy
      obtain ⟨b0, hb0, j, hj, ej⟩ := he
      rw [hx, get_put_self] at hb0; cases hb0
      obtain ⟨b2, h2, -⟩ := hb.1 j hj
      rw [ej, hy, hn] at h2; cases h2

/-- **`+emir` at a reserved label.** -/
theorem k6p_emir {g g' : Comp.Gen Map} (h : ATS6 g) {o : Nat} {b : Blob} (ho : o < g.bo) (h1 : 1 ≤ o)
    (hn : HoonMap.get g.blocks o = Option.none) (hb : BATC g.blocks b)
    (hr : (emir o b : CM Map Unit) g = some ((), g')) :
    ATS6 g' ∧ g'.blocks = HoonMap.put g.blocks o b ∧ g'.bo = g.bo ∧ g'.re = g.re ∧ g'.cond = g.cond ∧
      g'.tags = g.tags := by
  have hd : g.drop = false := h.1
  simp only [emir, hd, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq, true_and] at hr
  subst hr
  exact ⟨k6p_put h ho h1 hn hb rfl hd.symm rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A block meeting `BATC` at `bo`.** -/
theorem k6p_emitted {g : Comp.Gen Map} {b : Blob} (h : ATS6 g) (hb : BATC g.blocks b) :
    ATS6 (g.emitted b) := by
  have hd : g.drop = false := h.1
  have h0 : ATS6 ({ g with bo := g.bo + 1 } : Comp.Gen Map) := k6p_same h rfl (Nat.le_succ _) rfl
  exact k6p_put (g := { g with bo := g.bo + 1 }) h0 (o := g.bo) (Nat.lt_succ_self _) h.2.1
    (k6p_free h (Nat.le_refl _)) hb (by simp [Gen.emitted, hd]) rfl rfl

/-- **`+emit` of a block meeting `BATC`.** -/
theorem k6p_emit {g g' : Comp.Gen Map} {b : Blob} {o : Nat} (h : ATS6 g) (hb : BATC g.blocks b)
    (hr : (emit b : CM Map Nat) g = some (o, g')) : ATS6 g' ∧ o = g.bo ∧ g' = g.emitted b := by
  rw [emit_apply] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨k6p_emitted h hb, rfl, rfl⟩

/-! ## A block replaced -/

/-- **A block replaced by one with the same parameters, jump targets among
the old ones, and `BATC`.** -/
theorem k6p_repl {g g' : Comp.Gen Map} (h : ATS6 g) {o : Nat} {b b' : Blob}
    (hb : HoonMap.get g.blocks o = some b) (hp : b'.par = b.par)
    (ht : ∀ j ∈ finJumps b'.fin, ∃ j' ∈ finJumps b.fin, j'.there = j.there) (hB' : BATC g.blocks b')
    (hg : g'.blocks = HoonMap.put g.blocks o b') (hd : g'.drop = g.drop) (hbo : g'.bo = g.bo) : ATS6 g' := by
  obtain ⟨d, b1, hB, hA⟩ := h
  have hkp : ∀ k b0, HoonMap.get g.blocks k = some b0 →
      ∃ b'', HoonMap.get g'.blocks k = some b'' ∧ b''.par = b0.par := by
    intro k b0 hk
    rw [hg]
    by_cases e : k = o
    · subst e; rw [hb] at hk; cases hk
      exact ⟨b', get_put_self, hp⟩
    · exact ⟨b0, by rw [get_put_ne e]; exact hk, rfl⟩
  refine ⟨hd.trans d, hbo ▸ b1, fun k b0 hk => ?_, ?_⟩
  · rw [hg] at hk
    by_cases e : k = o
    · subst e; rw [get_put_self] at hk; cases hk
      obtain ⟨l, -, l1⟩ := hB k b hb
      exact ⟨hbo ▸ l, k6p_batc_par hkp hB', l1⟩
    · rw [get_put_ne e] at hk
      obtain ⟨l, B, l1⟩ := hB k b0 hk
      exact ⟨hbo ▸ l, k6p_batc_par hkp B, l1⟩
  · rw [hg]
    refine k6p_acyc_sub hA fun x y he => ?_
    obtain ⟨b0, hb0, j, hj, ej⟩ := he
    by_cases e : x = o
    · subst e; rw [get_put_self] at hb0; cases hb0
      obtain ⟨j', hj', ej'⟩ := ht j hj
      exact ⟨b, hb, j', hj', ej'.trans ej⟩
    · rw [get_put_ne e] at hb0
      exact ⟨b0, hb0, j, hj, ej⟩

theorem k6p_batc_fin {bl : Map Blob} {b b' : Blob} (h : BATC bl b) (hf : b'.fin = b.fin) : BATC bl b' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun j hj => h1 j (hf ▸ hj), fun ht j hj => h2 (hf ▸ ht) j (hf ▸ hj)⟩

/-- **`+add-ops`.** -/
theorem k6p_addOps {g g' : Comp.Gen Map} {o : Nat} {ops : List Pole} (h : ATS6 g)
    (hr : (addOps o ops : CM Map Unit) g = some ((), g')) : ATS6 g' := by
  simp only [addOps] at hr
  split at hr
  · simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hr
    subst hr; exact h
  · obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq, true_and] at e
    subst e
    exact k6p_repl (b' := { b with body := ops ++ b.body }) h hb rfl (fun j hj => ⟨j, hj, rfl⟩)
      (k6p_batc_fin (h.2.2.1 o b hb).2.1 rfl) rfl rfl rfl

/-- **`~(jab by blocks)`** with a gate that keeps the parameters, gives jump
targets among the old ones, and a block meeting `BATC`. -/
theorem k6p_jabBlock {g g' : Comp.Gen Map} {o : Nat} {f : Blob → Option Blob} (h : ATS6 g)
    (hf : ∀ b b', HoonMap.get g.blocks o = some b → f b = some b' →
      b'.par = b.par ∧ (∀ j ∈ finJumps b'.fin, ∃ j' ∈ finJumps b.fin, j'.there = j.there) ∧ BATC g.blocks b')
    (hr : (jabBlock o f : CM Map Unit) g = some ((), g')) : ATS6 g' := by
  simp only [jabBlock] at hr
  obtain ⟨b, hb, e⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨b', hb', e⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq, true_and] at e
  subst e
  obtain ⟨p, t, B⟩ := hf b b' hb hb'
  exact k6p_repl h hb p t B rfl rfl rfl

/-- **`jabBlock o (lensHop args)`** (the `lens-hop` of `+sect`) when `args`
has the length of the hop target's parameters. -/
theorem k6p_jabLens {g g' : Comp.Gen Map} {o : Nat} {args : List (Option Nat)} (h : ATS6 g)
    (hlen : ∀ b t bt, HoonMap.get g.blocks o = some b → b.fin = Termin.hop t →
      HoonMap.get g.blocks t.there = some bt → args.length = bt.par.length)
    (hr : (jabBlock o (lensHop args) : CM Map Unit) g = some ((), g')) : ATS6 g' := by
  refine k6p_jabBlock h (fun b b' hb hl => ?_) hr
  simp only [lensHop] at hl
  split at hl
  · rename_i t ht
    simp only [Option.some.injEq] at hl
    subst hl
    obtain ⟨bt, hbt, -⟩ := (h.2.2.1 o b hb).2.1.1 t (by rw [ht]; simp [finJumps])
    refine ⟨rfl, fun j hj => ⟨t, by rw [ht]; simp [finJumps], ?_⟩, ?_, ?_⟩
    · simp only [finJumps, List.mem_singleton] at hj
      subst hj; rfl
    · intro j hj
      simp only [finJumps, List.mem_singleton] at hj
      subst hj
      exact ⟨bt, hbt, hlen b t bt hb ht hbt⟩
    · intro htw; simp [Compiler.twoWay] at htw
  · cases hl

/-! ## `+fork-sure` -/

variable {S : Type} [HoonSet S] [HoonMapKeys Map]

theorem k6p_forkNeedGo {ned : Need} {g g' : Comp.Gen Map} {n : Need × Need} (h : ATS6 g)
    (hr : (forkNeedGo ned : CM Map (Need × Need)) g = some (n, g')) : ATS6 g' := by
  obtain ⟨⟨k, rfl⟩, -⟩ := forkNeedGo_spec ned g g' n.1 n.2 hr
  exact k6p_same h rfl (Nat.le_refl _) rfl


/-- **`+fork-sure` keeps `ATS6`** (the Prop form of `ksrForkSureSpec`):
from reserved `o0 ≠ o1` and a block at `o` with no parameter, every other
block kept, the join at the old `bo` (the parameters of `sur`, `hop o`),
`o0` and `o1` hopping to it with the registers of the two new needs, copies
of `sur`'s shape, distinct, apart and fresh. -/
theorem k6p_forkSure {sur : Sure S} {o o0 o1 : Nat} {g0 g1 : Comp.Gen Map} {x : Sure S × Sure S}
    (hA : ATS6 g0) (h0 : o0 < g0.bo) (h1 : o1 < g0.bo) (h01 : o0 ≠ o1) (p0 : 1 ≤ o0) (p1 : 1 ≤ o1)
    (n0 : HoonMap.get g0.blocks o0 = Option.none) (n1 : HoonMap.get g0.blocks o1 = Option.none)
    (ho : HasPar o [] g0)
    (h : (forkSure sur o o0 o1 : CM Map (Sure S × Sure S)) g0 = some (x, g1)) :
    ATS6 g1 ∧
    (∀ k, k ≠ g0.bo → k ≠ o0 → k ≠ o1 → HoonMap.get g1.blocks k = HoonMap.get g0.blocks k) ∧
    (∀ k b, HoonMap.get g0.blocks k = some b → HoonMap.get g1.blocks k = some b) ∧
    HoonMap.get g1.blocks g0.bo = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩ ∧
    HoonMap.get g1.blocks o0 = some ⟨[], [], Termin.hop ⟨(flattenNeed x.1.ned).map some, g0.bo⟩⟩ ∧
    HoonMap.get g1.blocks o1 = some ⟨[], [], Termin.hop ⟨(flattenNeed x.2.ned).map some, g0.bo⟩⟩ ∧
    x.1.lok = sur.lok ∧ x.2.lok = sur.lok ∧ NCopy sur.ned x.1.ned ∧ NCopy sur.ned x.2.ned ∧
    Distinct x.1.ned ∧ Distinct x.2.ned ∧ (∀ y, NMem x.1.ned y → ¬ NMem x.2.ned y) ∧
    (∀ y, NMem x.1.ned y ∨ NMem x.2.ned y → g0.re ≤ y ∧ y < g1.re) ∧
    g0.re ≤ g1.re ∧ g1.bo = g0.bo + 1 ∧ g1.drop = g0.drop ∧ g1.cond = g0.cond ∧ g1.tags = g0.tags := by
  have hd : g0.drop = false := hA.1
  unfold forkSure at h
  obtain ⟨⟨m0, m1⟩, gK, hK, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  unfold forkNeed at hK
  obtain ⟨⟨k0, k1⟩, gN, hN, h⟩ := bind_some hK
  obtain ⟨⟨k, eN⟩, c0, c1, d0, d1, j01, r01⟩ := forkNeedGo_spec _ _ _ _ _ hN
  subst eN
  have AN : ATS6 ({ g0 with re := g0.re + k } : Comp.Gen Map) := k6p_same hA rfl (Nat.le_refl _) rfl
  obtain ⟨barg, gE, hE, h⟩ := bind_some h
  have hjoin : BATC ({ g0 with re := g0.re + k } : Comp.Gen Map).blocks
      ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩ := by
    obtain ⟨bo', hbo', hp⟩ := ho
    refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
    simp only [finJumps, List.mem_singleton] at hj
    subst hj
    exact ⟨bo', hbo', by rw [hp]; rfl⟩
  obtain ⟨AE, rfl, rfl⟩ := k6p_emit AN hjoin hE
  obtain ⟨u0, gF, hF, h⟩ := bind_some h
  have getE : ∀ y, HoonMap.get (({ g0 with re := g0.re + k } : Comp.Gen Map).emitted
      ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩).blocks y =
      if y = g0.bo then some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩ else HoonMap.get g0.blocks y :=
    fun y => em_get (g := ({ g0 with re := g0.re + k } : Comp.Gen Map)) hd y
  have hne0 : o0 ≠ g0.bo := by omega
  have hne1 : o1 ≠ g0.bo := by omega
  have hB0 : BATC (({ g0 with re := g0.re + k } : Comp.Gen Map).emitted
      ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩).blocks
      ⟨[], [], Termin.hop ⟨(flattenNeed k0).map some, g0.bo⟩⟩ := by
    refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
    simp only [finJumps, List.mem_singleton] at hj
    subst hj
    refine ⟨⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩, by rw [getE]; simp, ?_⟩
    simp only [List.length_map]
    exact c0.length
  cases u0
  obtain ⟨AF, eF, bF, rF, cF, tF⟩ := k6p_emir AE (o := o0) (by simp only [emitted_bo]; omega) p0
    (by rw [getE, if_neg hne0]; exact n0) hB0 hF
  obtain ⟨u1, gG, hG, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have hB1 : BATC gF.blocks ⟨[], [], Termin.hop ⟨(flattenNeed k1).map some, g0.bo⟩⟩ := by
    refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
    simp only [finJumps, List.mem_singleton] at hj
    subst hj
    refine ⟨⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩, by rw [eF, get_put_ne (Ne.symm hne0), getE]; simp, ?_⟩
    simp only [List.length_map]
    exact c1.length
  cases u1
  obtain ⟨AG, eG, bG, rG, cG, tG⟩ := k6p_emir AF (o := o1) (by rw [bF]; simp only [emitted_bo]; omega) p1
    (by rw [eF, get_put_ne (Ne.symm h01), getE, if_neg hne1]; exact n1) hB1 hG
  have getG : ∀ y, HoonMap.get gG.blocks y =
      if y = o1 then some ⟨[], [], Termin.hop ⟨(flattenNeed k1).map some, g0.bo⟩⟩ else
      if y = o0 then some ⟨[], [], Termin.hop ⟨(flattenNeed k0).map some, g0.bo⟩⟩ else
      if y = g0.bo then some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩ else HoonMap.get g0.blocks y := by
    intro y
    rw [eG, HoonMap.get_put, eF, HoonMap.get_put, getE]
  have hre : gG.re = g0.re + k := by rw [rG, rF]; rfl
  refine ⟨AG, fun y a b c => ?_, fun y b hy => ?_, ?_, ?_, ?_, rfl, rfl, c0, c1, d0, d1, j01, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [getG, if_neg c, if_neg b, if_neg a]
  · have a : y ≠ g0.bo := fun e => by rw [e, k6p_free hA (Nat.le_refl _)] at hy; cases hy
    have b : y ≠ o0 := fun e => by rw [e, n0] at hy; cases hy
    have c : y ≠ o1 := fun e => by rw [e, n1] at hy; cases hy
    rw [getG, if_neg c, if_neg b, if_neg a]; exact hy
  · rw [getG, if_neg (Ne.symm hne1), if_neg (Ne.symm hne0), if_pos rfl]
  · rw [getG, if_neg h01, if_pos rfl]
  · rw [getG, if_pos rfl]
  · intro y hy; rw [hre]; exact r01 y hy
  · rw [hre]; omega
  · rw [bG, bF]; rfl
  · exact AG.1.trans hd.symm
  · rw [cG, cF]; rfl
  · rw [tG, tF]; rfl

end Raw
end SkaModel
end Formalization
