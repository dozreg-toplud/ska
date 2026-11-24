import lemmas.Ska.OptAliasPlainDriver

/-!
# The driver under `FillFresh`, the weaker invariant

`DInvF` = `DInvS` and `FillFresh` (no register with a dead fill in a
reachable block has a definition that counts) is weaker than `DInvR`
(`dInvF_of_R`): it allows a register with several dead fills, or a register
whose only definitions are dead fills.  Every pass keeps it too, so the driver
theorem holds under it (**`optimize_keeps_fresh`**,
**`optimize_keeps_fresh_pickR`**), and `optimize_keeps_plain` is the special
case.

A pass keeps `FillFresh` through a map of the places of definitions after to
places before that is reachable and injective for a fixed register (as for
`DefOnceR`) and maps a definition that counts to one that counts, that is a
dead fill before at the image is one after (**`fillFresh_of_map`**): a dead
fill after maps to a dead fill before, which no definition that counts may
accompany, or to a definition that counts before, which `DefOnceB` makes the
image of the definition that counts after, so the two places after are one.

* `+remove-useless-branching`, `+remove-empty-middle`: the identity map,
  `ssk_rub_live`, `ssk_mid_live` (**`rub_fresh`**, **`mid_fresh`**).
* `+trim-trace-hints`, `+remove-dead-code`: passes that keep labels,
  parameters and ends and a part of each body (`SubPass`), the `j`-th op after
  at `fidx`, `didx` before; a dead fill before stays one after (`sub_live`)
  since the ops after it are among the ops before after its place, and a read
  after is a read before at the mapped place (**`trim_fresh`**,
  **`dead_fresh`**).
* `+remove-hops`: `hk_site` and `hk_live` with the chains disjoint
  (**`hk_fresh`**, **`hops_fresh`**).
* `+alias`: `alias_fillFresh`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- **The weaker block invariant**: `DInvS` and `FillFresh`. -/
def DInvF (bl : Map Blob) : Prop := DInvS bl ∧ FillFresh bl

theorem dInvF_of_R {bl : Map Blob} (h : DInvR bl) : DInvF bl := ⟨dInvR_dInvS h, fillFresh_of_R h.2.2.2⟩

/-- **A map of the places of definitions after to places before** that is
reachable, injective for a fixed register and maps a definition that counts
to one that counts carries `FillFresh` over, given `DefOnceB` before. -/
theorem fillFresh_of_map {bl bl' : Map Blob} (m : Nat × Option Nat → Nat × Option Nat)
    (hsite : ∀ r s, Reach bl' s.1 → DefSite bl' r s → Reach bl (m s).1 ∧ DefSite bl r (m s))
    (hinj : ∀ r s s', DefSite bl' r s → DefSite bl' r s' → m s = m s' → s = s')
    (hlive : ∀ r s, LiveDef bl' r s → LiveDef bl r (m s))
    (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' := by
  intro r o i hR hdf s hs
  have hd := deadFill_site hdf
  obtain ⟨a1, a2⟩ := hsite r (o, some i) hR hd
  have l2 := hlive r s hs
  by_cases hx : ∃ k, (m (o, some i)).2 = some k ∧ DeadFill bl r (m (o, some i)).1 k
  · obtain ⟨k, -, hdk⟩ := hx
    exact hF r _ k a1 hdk _ l2
  · have l1 : LiveDef bl r (m (o, some i)) := ⟨a1, a2, fun k hk hdk => hx ⟨k, hk, hdk⟩⟩
    have e := hinj r _ _ hd hs.2.1 (h1 r _ _ l1 l2)
    subst e
    exact hs.2.2 i rfl hdf

/-! ## The identity passes -/

/-- **`+remove-useless-branching` keeps `FillFresh`.** -/
theorem rub_fresh {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' := by
  have hR := rub_blocks h
  exact fillFresh_of_map id (fun r s hr hd => ⟨ssk_rub_reach hR hr, ssk_rub_site hR hd⟩)
    (fun _ _ _ _ _ e => e) (fun r s hl => ssk_rub_live hR hl) h1 hF

/-- **`+remove-empty-middle` keeps `FillFresh`.** -/
theorem mid_fresh {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' := by
  have hM := mid_blocks h
  exact fillFresh_of_map id (fun r s hr hd => ⟨ssk_mid_reach hM hr, ssk_mid_site hM hd⟩)
    (fun _ _ _ _ _ e => e) (fun r s hl => ssk_mid_live hM hl) h1 hF

/-! ## Passes that keep a part of each body -/

/-- **A pass that keeps labels, parameters and ends and a part of each
body**: the `j`-th op after is the op at `ι o j` before, the ops after from
`j` are among the ops before from `ι o j`, a read after at `j` is a read
before at `ι o j`, and `ι o` is monotone, strictly on the ops after. -/
def SubPass (bl bl' : Map Blob) (ι : Nat → Nat → Nat) : Prop :=
  ∀ o b', HoonMap.get bl' o = some b' → ∃ b, HoonMap.get bl o = some b ∧ b'.par = b.par ∧ b'.fin = b.fin ∧
    (∀ j op, b'.body[j]? = some op → b.body[ι o j]? = some op) ∧
    (∀ j, ∀ op ∈ b'.body.drop j, op ∈ b.body.drop (ι o j)) ∧
    (∀ j r, ReadAt b' j r → ReadAt b (ι o j) r) ∧
    (∀ j j', j ≤ j' → ι o j ≤ ι o j') ∧
    (∀ j j', j < j' → j < b'.body.length → ι o j < ι o j')

section sub
variable {bl bl' : Map Blob} {ι : Nat → Nat → Nat} (hS : SubPass bl bl' ι)
include hS

theorem sub_reach {o : Nat} (h : Reach bl' o) : Reach bl o := by
  induction h with
  | zero => exact Reach.zero
  | jump _ hb hj ih =>
    obtain ⟨b, hb0, -, hf, -⟩ := hS _ _ hb
    exact Reach.jump (j := _) ih hb0 (by rw [← hf]; exact hj)

theorem sub_site {r : Nat} {s : Nat × Option Nat} (hr : Reach bl' s.1) (hd : DefSite bl' r s) :
    Reach bl (subMap ι s).1 ∧ DefSite bl r (subMap ι s) := by
  obtain ⟨o, _ | j⟩ := s
  · obtain ⟨b', hb', hm⟩ := hd
    obtain ⟨b, hb, hp, -⟩ := hS o b' hb'
    exact ⟨sub_reach hS hr, b, hb, by rw [← hp]; exact hm⟩
  · obtain ⟨b', op, hb', hop, hdst⟩ := hd
    obtain ⟨b, hb, -, -, hops, -⟩ := hS o b' hb'
    exact ⟨sub_reach hS hr, b, op, hb, hops j op hop, hdst⟩

theorem sub_inj {r : Nat} {s s' : Nat × Option Nat} (hd : DefSite bl' r s) (hd' : DefSite bl' r s')
    (he : subMap ι s = subMap ι s') : s = s' := by
  obtain ⟨o, _ | j⟩ := s <;> obtain ⟨o', _ | j'⟩ := s' <;> simp only [subMap, Prod.mk.injEq] at he
  · rw [he.1]
  · simp at he
  · simp at he
  · obtain ⟨rfl, he⟩ := he
    simp only [Option.some.injEq] at he
    obtain ⟨b', op, hb', hop, -⟩ := hd
    obtain ⟨b'', op', hb'', hop', -⟩ := hd'
    rw [hb'] at hb''; cases hb''
    obtain ⟨b, -, -, -, -, -, -, -, hmono⟩ := hS o b' hb'
    have hl : j < b'.body.length := (List.getElem?_eq_some_iff.mp hop).1
    have hl' : j' < b'.body.length := (List.getElem?_eq_some_iff.mp hop').1
    rcases Nat.lt_trichotomy j j' with hc | hc | hc
    · have := hmono j j' hc hl; omega
    · rw [hc]
    · have := hmono j' j hc hl'; omega

/-- **A definition that counts after maps to one that counts before**: a
dead fill before at the image is one after. -/
theorem sub_live {r : Nat} {s : Nat × Option Nat} (hl : LiveDef bl' r s) : LiveDef bl r (subMap ι s) := by
  obtain ⟨a1, a2⟩ := sub_site hS hl.1 hl.2.1
  refine ⟨a1, a2, fun k hk hdk => ?_⟩
  obtain ⟨o, _ | j⟩ := s
  · cases hk
  · simp only [subMap, Option.some.injEq] at hk
    subst hk
    apply hl.2.2 j rfl
    obtain ⟨b', op, hb', hop, hdst⟩ := hl.2.1
    obtain ⟨b, hb, -, hf, hops, hdrop, hread, hmono, -⟩ := hS o b' hb'
    obtain ⟨b1, hb1, ⟨u, hu⟩, ⟨n, hn⟩, himm, hrd⟩ := hdk
    simp only [subMap] at hb1 hn himm hrd
    rw [hb] at hb1; cases hb1
    refine ⟨b', hb', ⟨u, by rw [hf]; exact hu⟩, ⟨n, ?_⟩, fun op' hop' => himm op' (hdrop j op' hop'),
      fun o' b'' j' hr' hb'' hj' => ?_⟩
    · rw [hop, ← Option.some.inj ((hops j op hop).symm.trans hn)]
    · obtain ⟨b2, hb2, -, -, -, -, hread2, -, -⟩ := hS o' b'' hb''
      obtain ⟨rfl, hlt⟩ := hrd o' b2 _ (sub_reach hS hr') hb2 (hread2 j' r hj')
      rw [hb] at hb2; cases hb2
      rw [hb'] at hb''; cases hb''
      refine ⟨rfl, Classical.byContradiction fun hn' => ?_⟩
      have := hmono j j' (by omega)
      omega

theorem sub_fresh (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' :=
  fillFresh_of_map (subMap ι) (fun _ _ hr hd => sub_site hS hr hd) (fun _ _ _ hd hd' he => sub_inj hS hd hd' he)
    (fun _ _ hl => sub_live hS hl) h1 hF

end sub

/-- Filtering bodies is a `SubPass` with `fidx`. -/
theorem filt_sub {bl bl' : Map Blob} {p : Pole → Bool}
    (hg : ∀ o, HoonMap.get bl' o = (HoonMap.get bl o).map fun b => { b with body := b.body.filter p }) :
    SubPass bl bl' (fun o j => ((HoonMap.get bl o).map fun b => fidx p b.body j).getD j) := by
  intro o b' hb'
  have hb'0 := hb'
  rw [hg] at hb'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
  simp only [hb, Option.map_some, Option.getD_some]
  refine ⟨b, rfl, rfl, rfl, fun j op hop => ?_, fun j op hop => ?_, fun j r hr => readAt_filt hg hr,
    fun j j' hj => fidx_mono p b.body j j' hj, fun j j' hj hl => fidx_lt_of p b.body j j' hj hl⟩
  · rw [← List.head?_drop, ← fidx_head, List.head?_drop]; exact hop
  · rw [fidx_drop] at hop
    exact (List.mem_filter.mp hop).1

/-- **`+trim-trace-hints` keeps `FillFresh`.** -/
theorem trim_fresh {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (h : trimTraceHints bl topo rev = some bl') (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact sub_fresh (filt_sub (trimRun_get bl uns (trimOpened bl))) h1 hF

/-- `+remove-dead-code` is a `SubPass` with `didx`, on a `topo` with
`TopoOK`. -/
theorem dead_sub {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') :
    ∃ Sf : Nat → List Nat, SubPass bl bl' (fun o j => ((HoonMap.get bl o).map fun b => didx b.body (Sf o) j).getD j) := by
  obtain ⟨Sf, W, hout⟩ := ssk_dead_walk ht h
  refine ⟨Sf, fun o b' hb' => ?_⟩
  have hback : ∃ b, HoonMap.get bl o = some b ∧ b' = { b with body := (deadF b.body (Sf o)).1 } := by
    by_cases ho : o ∈ topo
    · obtain ⟨b, hb, hb2, -⟩ := W.blk o ho
      rw [hb2] at hb'; cases hb'
      exact ⟨b, hb, rfl⟩
    · rw [hout o ho] at hb'; cases hb'
  obtain ⟨b, hb, rfl⟩ := hback
  simp only [hb, Option.map_some, Option.getD_some]
  refine ⟨b, rfl, rfl, rfl, fun j op hop => ?_, fun j op hop => ssk_dd_mem _ _ _ _ hop, fun j r hr => ?_,
    fun j j' hj => ssk_dd_mono (Sf o) b.body j j' hj, fun j j' hj hl => ssk_dd_lt (Sf o) b.body j j' hj hl⟩
  · rw [← List.head?_drop, ← ssk_dd_head, List.head?_drop]; exact hop
  · rcases hr with hr | ⟨hj, hr⟩
    · left
      simp only at hr
      rw [← ssk_dd_head]; exact hr
    · right
      simp only at hj
      exact ⟨ssk_dd_len _ _ _ (by omega), hr⟩

/-- **`+remove-dead-code` keeps `FillFresh`**, on a `topo` with `TopoOK`. -/
theorem dead_fresh {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' := by
  obtain ⟨Sf, hS⟩ := dead_sub ht h
  exact sub_fresh hS h1 hF

/-! ## `+remove-hops` -/

section
variable {bl bl' : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

/-- **`+remove-hops` keeps `FillFresh`**, on blocks with `Acyclic` and
`ParNodup`, with `TopoInv` and `DefOnceB`. -/
theorem hk_fresh (hB : HopsBlocks bl rev topo bl') (hT : TopoInv bl topo rev) (hA : Acyclic bl)
    (hpn : ParNodup bl) (h1 : DefOnceB bl) (hF : FillFresh bl) : FillFresh bl' := by
  obtain ⟨ρ, hρ⟩ := hA
  have hsites : ∀ o m, HoonMap.get bl' o = some m →
      ∃ b T F f, HoonMap.get bl o = some b ∧ m = merge b T F ∧ HkSites bl rev o b T F f := by
    intro o m hm
    obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o m hm
    obtain ⟨f, hf⟩ := hk_sites hρ hpn hmt hb
    exact ⟨b, T, F, f, hb, rfl, hf⟩
  have hA : Acyclic bl := ⟨ρ, hρ⟩
  have blk : ∀ {r o opt}, DefSite bl' r (o, opt) → ∃ m, HoonMap.get bl' o = some m := by
    intro r o opt h
    cases opt with
    | none => obtain ⟨m, hm, -⟩ := h; exact ⟨m, hm⟩
    | some k => obtain ⟨m, -, hm, -⟩ := h; exact ⟨m, hm⟩
  intro r o i hR hdf ⟨o', opt'⟩ hs
  have hd := deadFill_site hdf
  obtain ⟨m, hm⟩ := blk hd
  obtain ⟨b, T, F, f, hb, rfl, hS⟩ := hsites o m hm
  obtain ⟨a1, a2, M1⟩ := hk_site hB hb hm hS hR hd
  obtain ⟨m', hm'⟩ := blk hs.2.1
  obtain ⟨b', T', F', f', hb', rfl, hS'⟩ := hsites o' m' hm'
  obtain ⟨l2, M2⟩ := hk_live hB hT hA hsites hb' hm' hS' hs
  by_cases hx : ∃ k, (hkSig f o (some i)).2 = some k ∧ DeadFill bl r (hkSig f o (some i)).1 k
  · obtain ⟨k, -, hdk⟩ := hx
    exact hF r _ k a1 hdk _ l2
  · have l1 : LiveDef bl r (hkSig f o (some i)) := ⟨a1, a2, fun k hk hdk => hx ⟨k, hk, hdk⟩⟩
    have e := h1 r _ _ l1 l2
    rw [e] at M1
    have hoo : o = o' := hk_disj hB hT hA hR hs.1 M1 M2
    subst hoo
    obtain ⟨l3, -⟩ := hk_live hB hT hA hsites hb hm hS hs
    have e2 := h1 r _ _ l1 l3
    have hk : ∀ {k}, DefSite bl' r (o, some k) → ∃ op, (b.body ++ T)[k]? = some op ∧ aliasDst op = some r := by
      intro k h
      obtain ⟨m2, op, hm2, hop, hd⟩ := h
      rw [hm] at hm2; cases hm2
      exact ⟨op, hop, hd⟩
    obtain ⟨op, hop, hdo⟩ := hk hd
    cases opt' with
    | none => exact absurd e2 (hS.mem i (List.getElem?_eq_some_iff.mp hop).1).2
    | some k' =>
      obtain ⟨op', hop', hdo'⟩ := hk hs.2.1
      have := hS.inj i k' op op' r hop hop' hdo hdo' e2
      subst this
      exact hs.2.2 i rfl hdf

end

/-- **`+remove-hops` keeps `FillFresh`** at the arguments the driver gives
it. -/
theorem hops_fresh {fuel : Nat} {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {ch : Bool}
    (hD : DInvS bl) (hi : TopoInv bl topo rev) (h : removeHops fuel bl rev topo = some (ch, bl'))
    (hF : FillFresh bl) : FillFresh bl' :=
  hk_fresh (hops_blocks hi.1.1 hi.1.2.1 h) hi hD.1.1.2.1 hD.1.1.1.1 hD.2.1.1 hF

/-! ## The driver -/

section
/-- **The field `alias` at `DInvF`** for the model. -/
theorem alias_fieldF {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {n : Nat}
    {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {f : Bool} {bl' : Map Blob} (hD : DInvF bl)
    (hT : TopoInvR bl topo rev) (h : aliasM pick n bl rev topo = some (f, bl')) :
    KeepsB bl bl' ∧ DInvF bl' ∧
      TopoInvR bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)) := by
  have hS := hD.1
  have hk := alias_keepsB hpick hS hT h
  unfold aliasM at h
  obtain ⟨g, hg, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain ⟨hpo, hdp, hK, hss⟩ := alias_restSSAB_fresh hpick hS hT hg hD.2
  have hdt := hS.1
  exact ⟨hk, ⟨⟨⟨⟨⟨alias_parNodup hT hdt.1.1.1 hg, hpo⟩, alias_acyclic hT hdt.1.2.1 hg, hdp⟩, hK⟩, hss,
    alias_nolti hT hS.2.2 hg⟩, alias_fillFresh hpick hS hT hg hD.2⟩, alias_topoInvR hT hg⟩

/-- **Every field of `DriverHyp` at `DInvF`**, with the model of `+alias`,
the real trim pass and the model switch pass. -/
theorem driverHypF_of {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints)
    (hsw : P.switch = switchChains sfuel) : DriverHyp fuel P DInvF TopoInvR where
  topo := fun bl topo hb h => ⟨topo_field hb.1.1.1 h, revCfg_sound bl topo⟩
  hops := fun bl topo rev ch bl' hb hi h => by
    have hS := hb.1
    obtain ⟨k, d, t⟩ := hops_fieldD hS.1.1 hi.1 h
    obtain ⟨Kt, hK⟩ := hS.1.2
    have hss : AliasSSAB bl' := hopsSSA_of hopsOnce_proved bl topo rev ch bl' hS.1 hi.1 hS.2.1 h
    refine ⟨k, ⟨⟨⟨d, Kt, hops_trimBr hi.1.1.1 hi.1.1.2.1 h hK⟩, hss, nolti_hops hS.2.2 hi.1.1.1 hi.1.1.2.1 h⟩,
      hops_fresh hS hi.1 h hb.2⟩, fun e => ⟨t e, ?_⟩⟩
    subst e
    exact rvs_eq hi.2 (hops_same hi.1.1.1 h).1
  rub := fun bl topo rev ch bl' hb h => by
    have hS := hb.1
    obtain ⟨k, d, t⟩ := rub_fieldD hS.1.1 h
    obtain ⟨Kt, hK⟩ := hS.1.2
    refine ⟨k, ⟨⟨⟨d, Kt, rub_trimBr h hK⟩, ssk_rub h hS.2.1, nolti_rub hS.2.2 h⟩, rub_fresh h hS.2.1.1 hb.2⟩,
      fun hi e => ⟨t hi.1 e, ?_⟩⟩
    subst e
    exact rvs_rub hi.2 h
  middle := fun bl topo rev ch bl' hb h => by
    have hS := hb.1
    obtain ⟨k, d, t⟩ := middle_fieldD hS.1.1 h
    obtain ⟨Kt, hK⟩ := hS.1.2
    refine ⟨k, ⟨⟨⟨d, Kt, mid_trimBr h hK⟩, ssk_mid h hS.2.1, nolti_mid hS.2.2 h⟩, mid_fresh h hS.2.1.1 hb.2⟩,
      fun hi e => ⟨t hi.1 e, ?_⟩⟩
    subst e
    exact rvs_eq hi.2 fun k _ => mid_same h k
  alias := fun n bl topo rev f bl' hb hi h => by
    rw [ha] at h
    exact alias_fieldF hpick hb hi h
  trim := fun bl topo rev bl' hb hi h => by
    rw [ht] at h
    obtain ⟨k, d, t⟩ := trim_fieldT hb.1.1 hi.1 h
    have hs := trim_shape h
    exact ⟨k, ⟨⟨d, trim_ssa h hb.1.2.1, nolti_shape hb.1.2.2 hs.1⟩, trim_fresh h hb.1.2.1.1 hb.2⟩, t,
      rvs_shape hi.2 hs.1 fun k hk => by rw [hs.2 k]; exact hi.1.1.2.2.1 k hk⟩
  dead := fun bl topo rev bl' hb hi h => by
    obtain ⟨Kt, hK⟩ := hb.1.1.2
    obtain ⟨d, t⟩ := dead_inv hb.1.1.1 hi.1 h
    have hs := dead_shape h
    exact ⟨fun c hc => by subst hc; exact dead_keeps c hi.1.1 h,
      ⟨⟨⟨d, Kt, dead_trimBr hi.1.1 h hK⟩, ssk_dead hi.1.1 h hb.1.2.1, nolti_shape hb.1.2.2 hs.1⟩,
        dead_fresh hi.1.1 h hb.1.2.1.1 hb.2⟩, t,
      rvs_shape hi.2 hs.1 fun k hk => hs.2 k (List.mem_reverse.mpr hk)⟩
  switch := fun bl bl' hb h => by rw [hsw] at h; exact switch_fieldT _ hb.1.1 h

/-- **`+optimize` with the model of `+alias` keeps the code** on blocks with
`DInvF` (`DInvS` and `FillFresh`), given only that `pick` picks a member of
its list. -/
theorem optimize_keeps_fresh {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints)
    (hsw : P.switch = switchChains sfuel) {s s' : Straight Map} (hb : DInvF s.blocks)
    (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps (driverHypF_of hpick ha ht hsw) hb h

/-- **`+optimize` with the passes of the Hoon keeps the code** on blocks with
`DInvF`, with no other hypothesis. -/
theorem optimize_keeps_fresh_pickR (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {s s' : Straight Map} (hb : DInvF s.blocks)
    (h : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ s = some s') : Keeps s s' :=
  optimize_keeps_fresh (fun l hl => Ana.pickR_mem l hl) rfl rfl rfl hb h

end

/-- The witness blocks violate `DInvF`. -/
theorem not_dInvF_w : ¬ DInvF wBlocks := fun h => not_fillFresh_w h.2

theorem not_dInvF_v : ¬ DInvF vBlocks := fun h => not_fillFresh_v h.2

end Opt
end SkaModel
end Formalization
