import lemmas.Ska.RawInvSix6
import lemmas.Ska.CompLazyRun
import lemmas.Ska.CompMede

/-!
# `ATS6` through `+sect`

README Gaps 14 (b), track D (fork `k6s`).  The `ATS6` part of `ksrSectSpec`
(`RawInvCLCheckSixR.lean`): `+sect` (`sect`, `CompLazyRun.lean`) emits the
two blocks `yes = bo` (`hop nex0.th`) and `nuh = bo + 1` (`hop nex1.th`),
tags them, and `sectThread` gives the join (the common hop target `tgt` of
the two ends `o0end`, `o1end`) new parameters and the two ends' hops as many
new arguments.

* `k6s_step`, `k6s_fold`: a step (and the `rep`) of `sectStep` keeps the
  blocks, `bo` and `drop`, and keeps the three lists of the accumulator (the
  yes end's arguments, the no end's, the join's parameters) of equal length.
* `k6s_jab`, `k6s_lensHop`, `k6s_setTag`: the other primitives.
* `k6s_acyc_ext`: new blocks that jump only to old ones keep `Acyc`;
  `k6s_jedge_congr`: `JEdge` depends only on the jump targets.
* `k6s_core`: the map after the three `jab`s of `sectThread`, from the
  facts of the state before (the work of `k6s_sect`).
* **`k6s_sect`**: from `ATS6` before `+sect`, the halves' jump targets
  blocks with no parameter, the two ends below `bo`, and, of the join `tgt`
  (the hop target of the block at `o0end`), that it is neither half's jump
  target and that only the two ends jump to it: `ATS6` after, `bo` up by
  two, the result `(mk bunt [((bo, nex0.laz), (bo + 1, nex1.laz))] [], bo,
  bo + 1)`, the two new blocks, the halves passing no argument, every old
  block keeping its body and jump targets, and the jump graph after is the
  one before with the two edges `bo -> nex0.th.there`,
  `bo + 1 -> nex1.th.there`.
* `k6s_sect_fresh`: the two new blocks are `Fresh`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The jump graph -/

/-- The jump targets of a block. -/
def k6sT (b : Blob) : List Nat := (finJumps b.fin).map (·.there)

theorem k6s_jedge_iff {bl : Map Blob} {y x : Nat} :
    JEdge bl y x ↔ ∃ b, HoonMap.get bl x = some b ∧ y ∈ k6sT b := by
  unfold JEdge k6sT
  constructor
  · rintro ⟨b, hb, j, hj, rfl⟩
    exact ⟨b, hb, List.mem_map.mpr ⟨j, hj, rfl⟩⟩
  · rintro ⟨b, hb, hy⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact ⟨b, hb, j, hj, rfl⟩

/-- **`JEdge` depends only on the jump targets.** -/
theorem k6s_jedge_congr {bl bl' : Map Blob}
    (h : ∀ k, (HoonMap.get bl' k).map k6sT = (HoonMap.get bl k).map k6sT) (y x : Nat) :
    JEdge bl' y x ↔ JEdge bl y x := by
  rw [k6s_jedge_iff, k6s_jedge_iff]
  have e := h x
  constructor
  · rintro ⟨b, hb, hy⟩
    rw [hb] at e
    cases hx : HoonMap.get bl x with
    | none => rw [hx] at e; cases e
    | some c =>
      rw [hx] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨c, rfl, e ▸ hy⟩
  · rintro ⟨b, hb, hy⟩
    rw [hb] at e
    cases hx : HoonMap.get bl' x with
    | none => rw [hx] at e; cases e
    | some c =>
      rw [hx] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨c, rfl, e.symm ▸ hy⟩

theorem k6s_acc_irrefl {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hx => ih x hx hx

/-- **New blocks that jump only to old blocks keep `Acyc`.** -/
theorem k6s_acyc_ext {bl bl' : Map Blob} (hA : Acyc bl)
    (hd : ∀ y x, JEdge bl y x → (HoonMap.get bl y).isSome = true)
    (hold : ∀ y x, JEdge bl' y x → (HoonMap.get bl x).isSome = true → JEdge bl y x)
    (hnew : ∀ y x, JEdge bl' y x → (HoonMap.get bl x).isSome = false → (HoonMap.get bl y).isSome = true) :
    Acyc bl' := by
  have key : ∀ k, Acc (JEdge bl) k → (HoonMap.get bl k).isSome = true → Acc (JEdge bl') k := by
    intro k hk
    induction hk with
    | intro x _ ih =>
      intro hx
      exact Acc.intro x fun y hy => ih y (hold y x hy hx) (hd y x (hold y x hy hx))
  intro k
  cases e : (HoonMap.get bl k).isSome with
  | true => exact key k (hA k) e
  | false => exact Acc.intro k fun y hy => key y (hA y) (hnew y k hy e)

/-- A put that keeps `F` of the block keeps `F` of the map. -/
theorem k6s_put_map {β : Type} (F : Blob → β) {m : Map Blob} {o : Nat} {b b' : Blob}
    (hb : HoonMap.get m o = some b) (he : F b' = F b) (k : Nat) :
    (HoonMap.get (HoonMap.put m o b') k).map F = (HoonMap.get m k).map F := by
  rw [HoonMap.get_put]
  split
  · rename_i e
    subst e
    rw [hb]
    simp only [Option.map_some, he]
  · rfl

/-! ## The primitives -/

/-- The three lists of the accumulator of `+sect` have one length. -/
def k6sL3 (acc : SectAcc Map) : Prop :=
  acc.2.1.length = acc.2.2.2.length ∧ acc.2.2.1.length = acc.2.2.2.length

theorem k6s_step {rid : Nat} {yes : Bool} {made : Map (Nat × List Nat)} {acc acc' : SectAcc Map} {k : Nat}
    {g g' : Comp.Gen Map} (h : sectStep rid yes made acc k g = some (acc', g')) (hL : k6sL3 acc) :
    g'.blocks = g.blocks ∧ g'.bo = g.bo ∧ g'.drop = g.drop ∧ k6sL3 acc' := by
  unfold sectStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, hL⟩
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, hL⟩
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, rfl, hL⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, rfl, rfl, ?_⟩
        obtain ⟨l1, l2⟩ := hL
        cases yes <;> simp only [k6sL3, Bool.false_eq_true, if_true, if_false, List.length_cons] <;>
          exact ⟨by omega, by omega⟩

/-- **The `rep` of `sectStep`.** -/
theorem k6s_fold {rid : Nat} {yes : Bool} {made : Map (Nat × List Nat)} :
    ∀ (ks : List Nat) (acc acc' : SectAcc Map) (g g' : Comp.Gen Map),
    (ks.foldlM (sectStep rid yes made) acc : CM Map (SectAcc Map)) g = some (acc', g') → k6sL3 acc →
    g'.blocks = g.blocks ∧ g'.bo = g.bo ∧ g'.drop = g.drop ∧ k6sL3 acc'
  | [], acc, acc', g, g', h, hL => by
    simp only [List.foldlM_nil, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, hL⟩
  | k :: ks, acc, acc', g, g', h, hL => by
    rw [List.foldlM_cons] at h
    obtain ⟨a1, g1, h1, h2⟩ := bind_some h
    obtain ⟨b1, o1, d1, L1⟩ := k6s_step h1 hL
    obtain ⟨b2, o2, d2, L2⟩ := k6s_fold ks a1 acc' g1 g' h2 L1
    exact ⟨b2.trans b1, o2.trans o1, d2.trans d1, L2⟩

theorem k6s_jab {o : Nat} {f : Blob → Option Blob} {g g' : Comp.Gen Map} {u : Unit}
    (h : (jabBlock o f : CM Map Unit) g = some (u, g')) :
    ∃ b b', HoonMap.get g.blocks o = some b ∧ f b = some b' ∧
      g' = { g with blocks := HoonMap.put g.blocks o b' } := by
  unfold jabBlock at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b', hb', h⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b, b', hb, hb', (Prod.mk.inj h).2.symm⟩

theorem k6s_lensHop {A : List (Option Nat)} {b b' : Blob} (h : lensHop A b = some b') :
    ∃ t, b.fin = Termin.hop t ∧ b' = { b with fin := Termin.hop { t with args := A } } := by
  unfold lensHop at h
  split at h
  · rename_i t ht
    exact ⟨t, ht, (Option.some.inj h).symm⟩
  · cases h

theorem k6s_setTag {o : Nat} {r : List Nat} {g g' : Comp.Gen Map} {u : Unit}
    (h : (setTag o r : CM Map Unit) g = some (u, g')) :
    g'.blocks = g.blocks ∧ g'.bo = g.bo ∧ g'.drop = g.drop := by
  simp only [setTag, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem k6s_get_ne {ν : Type} {m : Map ν} {o k : Nat} {v : ν} (h : k ≠ o) :
    HoonMap.get (HoonMap.put m o v) k = HoonMap.get m k := by
  rw [HoonMap.get_put, if_neg h]

theorem k6s_get_eq {ν : Type} {m : Map ν} {o : Nat} {v : ν} : HoonMap.get (HoonMap.put m o v) o = some v := by
  rw [HoonMap.get_put, if_pos rfl]


/-- **The map after `+sect`**: from the facts of the state before and the
three `jab`s, `ATS6`, the new blocks, the frame and the jump graph. -/
theorem k6s_core {nex0 nex1 : NextL S} {o0end o1end : Nat} {g0 g1 : Comp.Gen Map} {blA : Map Blob}
    {b0 b1 bt d1 : Blob} {t0 t1 s1 : Jmp} {A0 A1 : List (Option Nat)} {P : List Nat}
    (hd : g0.drop = false) (hbo1 : 1 ≤ g0.bo)
    (hblk : ∀ k b, HoonMap.get g0.blocks k = some b → k < g0.bo ∧ BATC g0.blocks b ∧ 1 ≤ k)
    (hacyc : Acyc g0.blocks)
    (hp0 : HasPar nex0.th.there [] g0) (hp1 : HasPar nex1.th.there [] g0)
    (he0 : o0end < g0.bo) (he1 : o1end < g0.bo) (a0 : nex0.th.args = []) (a1 : nex1.th.args = [])
    (hbA : ∀ k, HoonMap.get blA k =
      if k = g0.bo + 1 then some (⟨[], [], Termin.hop nex1.th⟩ : Blob)
      else if k = g0.bo then some ⟨[], [], Termin.hop nex0.th⟩ else HoonMap.get g0.blocks k)
    (hb0 : HoonMap.get g0.blocks o0end = some b0) (hf0 : b0.fin = Termin.hop t0)
    (hb1 : HoonMap.get g0.blocks o1end = some b1) (hf1 : b1.fin = Termin.hop t1)
    (htt' : t0.there = t1.there) (hb2 : HoonMap.get g0.blocks t0.there = some bt)
    (nt0 : t0.there ≠ o0end) (nt1 : t0.there ≠ o1end)
    (hJ0 : t0.there ≠ nex0.th.there) (hJ1 : t0.there ≠ nex1.th.there)
    (hJk : ∀ k b, HoonMap.get g0.blocks k = some b → ∀ j ∈ finJumps b.fin, j.there = t0.there →
      k = o0end ∨ k = o1end)
    (lA0 : A0.length = P.length) (lA1 : A1.length = P.length)
    (hd1 : HoonMap.get (HoonMap.put (HoonMap.put blA t0.there ({ par := P, body := bt.body, fin := bt.fin } : Blob))
      o0end ({ par := b0.par, body := b0.body, fin := Termin.hop { args := A0, there := t0.there } } : Blob))
        o1end = some d1)
    (hs1 : d1.fin = Termin.hop s1)
    (hB : g1.blocks = HoonMap.put (HoonMap.put (HoonMap.put blA t0.there
      ({ par := P, body := bt.body, fin := bt.fin } : Blob))
      o0end ({ par := b0.par, body := b0.body, fin := Termin.hop { args := A0, there := t0.there } } : Blob)) o1end
      ({ par := d1.par, body := d1.body, fin := Termin.hop { args := A1, there := s1.there } } : Blob))
    (hbo : g1.bo = g0.bo + 2) (hdr : g1.drop = false) :
    ATS6 g1 ∧
    HoonMap.get g1.blocks g0.bo = some ⟨[], [], Termin.hop nex0.th⟩ ∧
    HoonMap.get g1.blocks (g0.bo + 1) = some ⟨[], [], Termin.hop nex1.th⟩ ∧
    (∀ k b, HoonMap.get g0.blocks k = some b →
      ∃ b', HoonMap.get g1.blocks k = some b' ∧ b'.body = b.body ∧ k6sT b' = k6sT b) ∧
    (∀ y z, JEdge g1.blocks y z ↔
      JEdge g0.blocks y z ∨ (z = g0.bo ∧ y = nex0.th.there) ∨ (z = g0.bo + 1 ∧ y = nex1.th.there)) := by
  unfold ATS6
  rw [hB, hbo]
  generalize hc' : ({ par := P, body := bt.body, fin := bt.fin } : Blob) = c' at hd1 ⊢
  generalize he0' : ({ par := b0.par, body := b0.body, fin := Termin.hop { args := A0, there := t0.there } } :
    Blob) = e0 at hd1 ⊢
  generalize he1' : ({ par := d1.par, body := d1.body, fin := Termin.hop { args := A1, there := s1.there } } :
    Blob) = e1
  generalize hM1 : HoonMap.put blA t0.there c' = M1 at hd1 ⊢
  generalize hM2 : HoonMap.put M1 o0end e0 = M2 at hd1 ⊢
  have hlt : ∀ k b, HoonMap.get g0.blocks k = some b → k < g0.bo := fun k b hb => (hblk k b hb).1
  have hold : ∀ k, k < g0.bo → HoonMap.get blA k = HoonMap.get g0.blocks k := fun k hk => by
    rw [hbA, if_neg (by omega), if_neg (by omega)]
  have tlt : t0.there < g0.bo := hlt _ _ hb2
  have hb2' : HoonMap.get blA t0.there = some bt := by rw [hold _ tlt, hb2]
  have gM1o0 : HoonMap.get M1 o0end = some b0 := by
    rw [← hM1, k6s_get_ne (Ne.symm nt0), hold _ he0, hb0]
  have gM2o0 : HoonMap.get M2 o0end = some e0 := by rw [← hM2, k6s_get_eq]
  have hT : ∀ k, (HoonMap.get (HoonMap.put M2 o1end e1) k).map k6sT = (HoonMap.get blA k).map k6sT := by
    intro k
    rw [k6s_put_map k6sT hd1 (by rw [← he1']; simp [k6sT, finJumps, hs1]), ← hM2,
      k6s_put_map k6sT gM1o0 (by rw [← he0']; simp [k6sT, finJumps, hf0]), ← hM1,
      k6s_put_map k6sT hb2' (by rw [← hc']; rfl)]
  have hBd : ∀ k, (HoonMap.get (HoonMap.put M2 o1end e1) k).map Blob.body =
      (HoonMap.get blA k).map Blob.body := by
    intro k
    rw [k6s_put_map Blob.body hd1 (by rw [← he1']), ← hM2,
      k6s_put_map Blob.body gM1o0 (by rw [← he0']), ← hM1,
      k6s_put_map Blob.body hb2' (by rw [← hc'])]
  have hP : ∀ k, k ≠ t0.there → (HoonMap.get (HoonMap.put M2 o1end e1) k).map Blob.par =
      (HoonMap.get blA k).map Blob.par := by
    intro k hk
    rw [k6s_put_map Blob.par hd1 (by rw [← he1']), ← hM2,
      k6s_put_map Blob.par gM1o0 (by rw [← he0']), ← hM1, k6s_get_ne hk]
  have F3 : HoonMap.get (HoonMap.put M2 o1end e1) t0.there = some c' := by
    rw [k6s_get_ne nt1, ← hM2, k6s_get_ne nt0, ← hM1, k6s_get_eq]
  have F5 : ∀ k, k ≠ t0.there → k ≠ o0end → k ≠ o1end →
      HoonMap.get (HoonMap.put M2 o1end e1) k = HoonMap.get blA k := by
    intro k a b c
    rw [k6s_get_ne c, ← hM2, k6s_get_ne b, ← hM1, k6s_get_ne a]
  have hs1t : s1.there = t0.there := by
    by_cases e : o1end = o0end
    · rw [e, gM2o0] at hd1
      obtain rfl := Option.some.inj hd1
      rw [← he0'] at hs1
      simp only [Termin.hop.injEq] at hs1
      rw [← hs1]
    · rw [← hM2, k6s_get_ne e, ← hM1, k6s_get_ne (Ne.symm nt1), hold _ he1, hb1] at hd1
      obtain rfl := Option.some.inj hd1
      rw [hf1] at hs1
      simp only [Termin.hop.injEq] at hs1
      rw [← hs1, htt']
  have F4 : ∀ k b, HoonMap.get (HoonMap.put M2 o1end e1) k = some b → (k = o0end ∨ k = o1end) →
      ∃ s : Jmp, b.fin = Termin.hop s ∧ s.there = t0.there ∧ s.args.length = P.length := by
    intro k b hk hk'
    by_cases e1k : k = o1end
    · rw [e1k, k6s_get_eq] at hk
      obtain rfl := Option.some.inj hk
      exact ⟨{ args := A1, there := s1.there }, by rw [← he1'], hs1t, lA1⟩
    · have e0k : k = o0end := hk'.resolve_right e1k
      rw [k6s_get_ne e1k, e0k, gM2o0] at hk
      obtain rfl := Option.some.inj hk
      exact ⟨{ args := A0, there := t0.there }, by rw [← he0'], rfl, lA0⟩
  have hpar : ∀ y b2, HoonMap.get g0.blocks y = some b2 → y ≠ t0.there →
      ∃ b2', HoonMap.get (HoonMap.put M2 o1end e1) y = some b2' ∧ b2'.par = b2.par := by
    intro y b2 hy hne
    have hm := hP y hne
    rw [hold _ (hlt _ _ hy), hy, Option.map_some] at hm
    exact Option.map_eq_some_iff.mp hm
  have hbatc : ∀ k b, HoonMap.get (HoonMap.put M2 o1end e1) k = some b → BATC (HoonMap.put M2 o1end e1) b := by
    intro k b hk
    by_cases k01 : k = o0end ∨ k = o1end
    · obtain ⟨s, hs, hst, hsl⟩ := F4 k b hk k01
      refine ⟨fun j hj => ?_, fun ht => ?_⟩
      · rw [hs] at hj
        simp only [finJumps, List.mem_singleton] at hj
        subst hj
        rw [hst, F3]
        exact ⟨c', rfl, by rw [hsl, ← hc']⟩
      · rw [hs] at ht
        simp [Compiler.twoWay] at ht
    · rw [not_or] at k01
      by_cases kt : k = t0.there
      · rw [kt, F3] at hk
        obtain rfl := Option.some.inj hk
        have hB0 := (hblk _ _ hb2).2.1
        rw [← hc']
        refine ⟨fun j hj => ?_, fun ht j hj => hB0.2 ht j hj⟩
        obtain ⟨b2, hb2j, hl⟩ := hB0.1 j hj
        have hne : j.there ≠ t0.there := fun e => k6s_acc_irrefl (hacyc t0.there) ⟨bt, hb2, j, hj, e⟩
        obtain ⟨b2', hb2', hp'⟩ := hpar _ _ hb2j hne
        exact ⟨b2', hb2', by rw [hl, hp']⟩
      · rw [F5 k kt k01.1 k01.2, hbA] at hk
        split at hk
        · obtain rfl := Option.some.inj hk
          refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
          simp only [finJumps, List.mem_singleton] at hj
          subst hj
          obtain ⟨bn, hbn, hpn⟩ := hp1
          obtain ⟨b2', hb2', hp'⟩ := hpar _ _ hbn (Ne.symm hJ1)
          exact ⟨b2', hb2', by rw [a1, hp', hpn]; rfl⟩
        · split at hk
          · obtain rfl := Option.some.inj hk
            refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
            simp only [finJumps, List.mem_singleton] at hj
            subst hj
            obtain ⟨bn, hbn, hpn⟩ := hp0
            obtain ⟨b2', hb2', hp'⟩ := hpar _ _ hbn (Ne.symm hJ0)
            exact ⟨b2', hb2', by rw [a0, hp', hpn]; rfl⟩
          · have hB0 := (hblk _ _ hk).2.1
            refine ⟨fun j hj => ?_, fun ht j hj => hB0.2 ht j hj⟩
            obtain ⟨b2, hb2j, hl⟩ := hB0.1 j hj
            have hne : j.there ≠ t0.there := fun e => by
              rcases hJk k b hk j hj e with e' | e'
              · exact k01.1 e'
              · exact k01.2 e'
            obtain ⟨b2', hb2', hp'⟩ := hpar _ _ hb2j hne
            exact ⟨b2', hb2', by rw [hl, hp']⟩
  have hbnd : ∀ k b, HoonMap.get (HoonMap.put M2 o1end e1) k = some b → k < g0.bo + 2 ∧ 1 ≤ k := by
    intro k b hk
    have hm := hT k
    rw [hk, Option.map_some] at hm
    obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.mp hm.symm
    rw [hbA] at ha
    split at ha
    · omega
    · split at ha
      · omega
      · have := hblk _ _ ha
        omega
  have n0 : HoonMap.get g0.blocks g0.bo = Option.none := by
    cases e : HoonMap.get g0.blocks g0.bo with
    | none => rfl
    | some b => exact absurd (hlt _ _ e) (Nat.lt_irrefl _)
  have n1 : HoonMap.get g0.blocks (g0.bo + 1) = Option.none := by
    cases e : HoonMap.get g0.blocks (g0.bo + 1) with
    | none => rfl
    | some b => have := hlt _ _ e; omega
  have hJA : ∀ y z, JEdge blA y z ↔
      JEdge g0.blocks y z ∨ (z = g0.bo ∧ y = nex0.th.there) ∨ (z = g0.bo + 1 ∧ y = nex1.th.there) := by
    intro y z
    constructor
    · rintro ⟨b, hb, j, hj, rfl⟩
      rw [hbA] at hb
      split at hb
      · rename_i e
        obtain rfl := Option.some.inj hb
        simp only [finJumps, List.mem_singleton] at hj
        subst hj
        exact Or.inr (Or.inr ⟨e, rfl⟩)
      · split at hb
        · rename_i _ e
          obtain rfl := Option.some.inj hb
          simp only [finJumps, List.mem_singleton] at hj
          subst hj
          exact Or.inr (Or.inl ⟨e, rfl⟩)
        · exact Or.inl ⟨b, hb, j, hj, rfl⟩
    · rintro (⟨b, hb, j, hj, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨b, by rw [hold _ (hlt _ _ hb), hb], j, hj, rfl⟩
      · exact ⟨_, by rw [hbA, if_neg (by omega), if_pos rfl], nex0.th, by simp [finJumps], rfl⟩
      · exact ⟨_, by rw [hbA, if_pos rfl], nex1.th, by simp [finJumps], rfl⟩
  have hAcA : Acyc blA := k6s_acyc_ext hacyc
    (fun y x hy => by
      obtain ⟨b, hb, j, hj, e⟩ := hy
      obtain ⟨b2, hb2', -⟩ := (hblk _ _ hb).2.1.1 j hj
      rw [← e, hb2']
      rfl)
    (fun y x hy hx => by
      rcases (hJA y x).mp hy with h | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact h
      · simp [n0] at hx
      · simp [n1] at hx)
    (fun y x hy hx => by
      rcases (hJA y x).mp hy with ⟨b, hb, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp [hb] at hx
      · obtain ⟨bn, hbn, -⟩ := hp0
        rw [hbn]
        rfl
      · obtain ⟨bn, hbn, -⟩ := hp1
        rw [hbn]
        rfl)
  have hJ1' : ∀ y z, JEdge (HoonMap.put M2 o1end e1) y z ↔ JEdge blA y z := k6s_jedge_congr hT
  have hAc : Acyc (HoonMap.put M2 o1end e1) := by
    have e : JEdge (HoonMap.put M2 o1end e1) = JEdge blA :=
      funext fun y => funext fun z => propext (hJ1' y z)
    intro k
    rw [e]
    exact hAcA k
  refine ⟨⟨hdr, by omega, fun k b hk => ⟨(hbnd k b hk).1, hbatc k b hk, (hbnd k b hk).2⟩, hAc⟩, ?_, ?_, ?_,
    fun y z => (hJ1' y z).trans (hJA y z)⟩
  · rw [F5 _ (by omega) (by omega) (by omega), hbA, if_neg (by omega), if_pos rfl]
  · rw [F5 _ (by omega) (by omega) (by omega), hbA, if_pos rfl]
  · intro k b hk
    have hkl := hlt _ _ hk
    have m1 := hT k
    have m2 := hBd k
    rw [hold _ hkl, hk, Option.map_some] at m1 m2
    obtain ⟨b', hb', hT'⟩ := Option.map_eq_some_iff.mp m1
    rw [hb', Option.map_some, Option.some.injEq] at m2
    exact ⟨b', hb', m2, hT'⟩

/-! ## `+sect` -/

/-- **`ATS6` through `+sect`**, with the frame of the old blocks, the two new
blocks and the jump graph after. -/
theorem k6s_sect {nex0 nex1 : NextL S} {o0end o1end : Nat} {rb : List Nat}
    {cB cW : Map (Nat × List Nat)} {g0 g1 : Comp.Gen Map} {x : Lazy S × Nat × Nat}
    (hA : ATS6 g0) (hp0 : HasPar nex0.th.there [] g0) (hp1 : HasPar nex1.th.there [] g0)
    (he0 : o0end < g0.bo) (he1 : o1end < g0.bo)
    (hJ : ∀ b0 t0, HoonMap.get g0.blocks o0end = some b0 → b0.fin = Termin.hop t0 →
      t0.there ≠ nex0.th.there ∧ t0.there ≠ nex1.th.there ∧
      ∀ k b, HoonMap.get g0.blocks k = some b → ∀ j ∈ finJumps b.fin, j.there = t0.there → k = o0end ∨ k = o1end)
    (h : (sect nex0 nex1 o0end o1end rb cB cW : CM Map (Lazy S × Nat × Nat)) g0 = some (x, g1)) :
    ATS6 g1 ∧ g1.bo = g0.bo + 2 ∧
    x = (mk Sure.bunt [((g0.bo, nex0.laz), (g0.bo + 1, nex1.laz))] [], g0.bo, g0.bo + 1) ∧
    HoonMap.get g1.blocks g0.bo = some ⟨[], [], Termin.hop nex0.th⟩ ∧
    HoonMap.get g1.blocks (g0.bo + 1) = some ⟨[], [], Termin.hop nex1.th⟩ ∧
    nex0.th.args = [] ∧ nex1.th.args = [] ∧
    (∀ k b, HoonMap.get g0.blocks k = some b →
      ∃ b', HoonMap.get g1.blocks k = some b' ∧ b'.body = b.body ∧ k6sT b' = k6sT b) ∧
    (∀ y z, JEdge g1.blocks y z ↔
      JEdge g0.blocks y z ∨ (z = g0.bo ∧ y = nex0.th.there) ∨ (z = g0.bo + 1 ∧ y = nex1.th.there)) := by
  obtain ⟨hd, hbo1, hblk, hacyc⟩ := hA
  cases rb with
  | nil => simp [sect] at h
  | cons rid rest =>
  simp only [sect] at h
  obtain ⟨o0b, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o1b, gb, hb, h⟩ := bind_some h
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨u1, gc, hc, h⟩ := bind_some h
  obtain ⟨u2, gd, hgd, h⟩ := bind_some h
  obtain ⟨gq, gq', hq, h⟩ := bind_some h
  rw [get_apply] at hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  obtain ⟨sc1, sc2, sc3⟩ := k6s_setTag hc
  obtain ⟨sd1, sd2, sd3⟩ := k6s_setTag hgd
  have hdd : gd.drop = false := by rw [sd3, sc3]; exact hd
  have hbo2 : gd.bo = g0.bo + 2 := by rw [sd2, sc2]; rfl
  have hbA : ∀ k, HoonMap.get gd.blocks k =
      if k = g0.bo + 1 then some (⟨[], [], Termin.hop nex1.th⟩ : Blob)
      else if k = g0.bo then some ⟨[], [], Termin.hop nex0.th⟩ else HoonMap.get g0.blocks k := by
    intro k
    rw [sd1, sc1]
    simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put]
  have hold : ∀ k, k < g0.bo → HoonMap.get gd.blocks k = HoonMap.get g0.blocks k := by
    intro k hk
    rw [hbA, if_neg (by omega), if_neg (by omega)]
  have hlt : ∀ k b, HoonMap.get g0.blocks k = some b → k < g0.bo := fun k b hb => (hblk k b hb).1
  simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨u3, ge, hthr, h⟩ := bind_some h
  by_cases a0 : nex0.th.args = []
  rotate_left
  · simp [a0] at h
  by_cases a1 : nex1.th.args = []
  rotate_left
  · simp [a0, a1] at h
  simp only [a0, a1, ne_eq, not_true_eq_false, ↓reduceIte, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  unfold sectThread at hthr
  obtain ⟨b0, hb0, hthr⟩ := Option.bind_eq_some_iff.mp hthr
  obtain ⟨b1, hb1, hthr⟩ := Option.bind_eq_some_iff.mp hthr
  split at hthr
  rotate_left
  · cases hthr
  rename_i t0 t1 hf0 hf1
  split at hthr
  · cases hthr
  rename_i htt
  have htt' : t0.there = t1.there := Decidable.not_not.mp htt
  obtain ⟨bt, hbt, hthr⟩ := Option.bind_eq_some_iff.mp hthr
  obtain ⟨acc1, gf1, hf1', hthr⟩ := bind_some hthr
  obtain ⟨acc2, gf2, hf2', hthr⟩ := bind_some hthr
  obtain ⟨u4, gh1, hj1, hthr⟩ := bind_some hthr
  obtain ⟨u5, gh2, hj2, hj3⟩ := bind_some hthr
  -- the old blocks at the two ends and the join
  rw [hold _ he0] at hb0
  rw [hold _ he1] at hb1
  have m0 : t0 ∈ finJumps b0.fin := by rw [hf0]; simp [finJumps]
  have m1 : t1 ∈ finJumps b1.fin := by rw [hf1]; simp [finJumps]
  obtain ⟨b2, hb2, hl0⟩ := (hblk _ _ hb0).2.1.1 t0 m0
  obtain ⟨b3, hb3, hl1⟩ := (hblk _ _ hb1).2.1.1 t1 m1
  have htl : t0.there < g0.bo := hlt _ _ hb2
  rw [hold _ htl, hb2] at hbt
  cases hbt
  rw [← htt', hb2] at hb3
  cases hb3
  have nt0 : t0.there ≠ o0end := fun e => k6s_acc_irrefl (hacyc o0end) ⟨b0, hb0, t0, m0, e⟩
  have nt1 : t0.there ≠ o1end := fun e => k6s_acc_irrefl (hacyc o1end) ⟨b1, hb1, t1, m1, htt'.symm.trans e⟩
  obtain ⟨hJ0, hJ1, hJk⟩ := hJ b0 t0 hb0 hf0
  -- the `rep`s
  obtain ⟨f1b, f1o, f1d, L1⟩ := k6s_fold _ _ _ _ _ hf1' ⟨hl0, hl1⟩
  obtain ⟨f2b, f2o, f2d, L2⟩ := k6s_fold _ _ _ _ _ hf2' L1
  -- the three jabs
  obtain ⟨c, c', hc0, hcc, hgh1⟩ := k6s_jab hj1
  obtain ⟨d0, d0', hd0, hdd0, hgh2⟩ := k6s_jab hj2
  obtain ⟨d1, d1', hd1, hdd1, hge⟩ := k6s_jab hj3
  simp only [Option.some.injEq] at hcc
  subst hcc
  have eb : gf2.blocks = gd.blocks := f2b.trans f1b
  rw [eb, hold _ htl, hb2] at hc0
  cases hc0
  rw [hgh1] at hd0
  simp only at hd0
  rw [eb, k6s_get_ne (Ne.symm nt0), hold _ he0, hb0] at hd0
  cases hd0
  obtain ⟨s0, hs0, rfl⟩ := k6s_lensHop hdd0
  rw [hf0] at hs0
  cases hs0
  obtain ⟨s1, hs1, rfl⟩ := k6s_lensHop hdd1
  rw [hgh2] at hd1
  simp only at hd1
  rw [hgh1] at hd1
  simp only at hd1
  rw [eb] at hd1
  have B3 := congrArg Comp.Gen.blocks hge
  have O3 := congrArg Comp.Gen.bo hge
  have D3 := congrArg Comp.Gen.drop hge
  simp only at B3 O3 D3
  rw [hgh2] at B3 O3 D3
  simp only at B3 O3 D3
  rw [hgh1] at B3 O3 D3
  simp only at B3 O3 D3
  rw [eb] at B3
  rw [f2o, f1o, hbo2] at O3
  rw [f2d, f1d, hdd] at D3
  obtain ⟨C1, C2, C3, C4, C5⟩ := k6s_core hd hbo1 hblk hacyc hp0 hp1 he0 he1 a0 a1 hbA hb0 hf0 hb1 hf1 htt'
    hb2 nt0 nt1 hJ0 hJ1 hJk L2.1 L2.2 hd1 hs1 B3 O3 D3
  exact ⟨C1, O3, rfl, C2, C3, a0, a1, C4, C5⟩

/-- **The two new blocks of `+sect` are `Fresh`.** -/
theorem k6s_sect_fresh {nex0 nex1 : NextL S} {o0end o1end : Nat} {rb : List Nat}
    {cB cW : Map (Nat × List Nat)} {g0 g1 : Comp.Gen Map} {x : Lazy S × Nat × Nat}
    (hA : ATS6 g0) (hp0 : HasPar nex0.th.there [] g0) (hp1 : HasPar nex1.th.there [] g0)
    (he0 : o0end < g0.bo) (he1 : o1end < g0.bo)
    (hJ : ∀ b0 t0, HoonMap.get g0.blocks o0end = some b0 → b0.fin = Termin.hop t0 →
      t0.there ≠ nex0.th.there ∧ t0.there ≠ nex1.th.there ∧
      ∀ k b, HoonMap.get g0.blocks k = some b → ∀ j ∈ finJumps b.fin, j.there = t0.there → k = o0end ∨ k = o1end)
    (h : (sect nex0 nex1 o0end o1end rb cB cW : CM Map (Lazy S × Nat × Nat)) g0 = some (x, g1)) :
    Fresh g1 (jmp0 x.2.1) ∧ Fresh g1 (jmp0 x.2.2) := by
  obtain ⟨-, -, rfl, h0, h1, -⟩ := k6s_sect hA hp0 hp1 he0 he1 hJ h
  exact ⟨⟨_, h0, rfl, rfl⟩, ⟨_, h1, rfl, rfl⟩⟩

end Raw
end SkaModel
end Formalization
