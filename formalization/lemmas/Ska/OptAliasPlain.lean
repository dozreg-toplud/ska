import lemmas.Ska.OptAliasSSADead
import lemmas.Ska.OptAliasOnce

/-!
# Plain single assignment, the block invariant the driver carries

## The invariant

`DefOnceB` of the result of `+alias` fails on blocks with `DInvS`
(`OptAliasOnce.lean`, `OptAliasWitness.lean`), so the driver needs a stronger
invariant of its blocks, true of raw `+comp` output and kept by every pass.
Two candidates: `DInvS ∧ FillFresh` (no register with a dead fill in a
reachable block has a definition that counts), and plain single assignment on
the reachable blocks, **`DefOnceR`**: every register has at most one
definition (a parameter or an op, dead fills included) in the blocks
reachable from `0`.  The second is chosen, as **`DInvR`** = `DInvT`,
`DefFirst`, `NoLti` and `DefOnceR`:

* it implies the first (`defOnceB_of_R`, `fillFresh_of_R`, `dInvR_dInvS`), so
  every theorem stated at `DInvS` applies;
* every pass keeps it through one map of the places of definitions after to
  places before, reachable, injective for a fixed register
  (`onceR_of_map`), the map the proofs of `DefOnceB` already build; keeping
  `FillFresh` needs that map and in addition that a definition that counts
  after maps to one that counts before (a dead fill stays one), a second
  argument per pass;
* it says nothing about dead fills, so the invariant raw `+comp` output owes
  is simpler to state and to prove (track C); single assignment over all
  blocks (`DefOnce`: the definitions of the whole map distinct) implies it
  (`defOnceR_of_defOnce`);
* it holds on the corpus of `tools/hoon/ssacheck.hoon` at every pass of every
  round once `+crash-need` stops filling the register it tests (the
  candidate change of the Hoon, not applied); without the change it fails
  there, as `FillFresh` does.

The driver theorem is proved under both (`OptAliasPlainDriver.lean`,
`OptAliasFresh.lean`).

## It survives the passes that make dead fills

A merge of `+remove-hops` can turn an ordinary `%imm` into a dead fill:
block `0` = `[%imm 5 x]`, `[%hop [~ 1]]`, block `1` (whose one predecessor is
`0`) = no op, `[%bom ~]`; after the pass block `0` is `[%imm 5 x]`,
`[%bom ~]` and block `1` is gone (`ex_hops`), and with `x` read nowhere the
`%imm` is now a dead fill.  `x` has one definition before, `(0, some 0)`, and
one after, at the same place: a
merge creates no definition, every place after maps to one before
(`hops_onceR`).  (Under `FillFresh` the example survives too: `x` had a
definition that counts and no dead fill before, and after its only definition
is the dead fill, so it has none that counts.)

`+alias` turning an end into `%bom` does the same: block `0` = `[%imm 5 c]
[%imm 7 x]`, `[%brn c [~ 1] [~ 2]]`, with `1` and `2` reading `x`; `c` holds
the immediate `5`, which is no loobean, so the end becomes `[%bom ~]`, blocks
`1` and `2` are no longer reachable, and both `%imm` ops are dead fills.
`+alias` keeps a subsequence of each body with the destinations unchanged,
so `x` still has one definition (`alias_onceR`; `ex_alias` with `c`, `x` the
registers `1`, `2`).

## The passes

`onceR_of_sub`: a pass that keeps the labels and parameters, keeps every op
that writes a register of a body at a place given by a map strictly monotone
on the ops after, and whose reachable blocks were reachable, keeps
`DefOnceR`.  So do **`rub_onceR`** (`+remove-useless-branching`: an epilogue
that writes no register), **`mid_onceR`** (`+remove-empty-middle`: ends
only), **`trim_onceR`** (`+trim-trace-hints`, through **`filt_onceR`**) and
**`dead_onceR`** (`+remove-dead-code`, on `TopoOK`).

**`hops_onceR`** (`+remove-hops`): a place of a merged body goes to an op of
a member of the chain merged, or, for the move of an argument into a
parameter of the next member (a `[%mov a p]`, or the `[%imm 0 p]` of a `~`
argument), to that parameter, `(x, none)`; the map is injective for a fixed
register (`HkSites.inj`), and the chains of two blocks reachable after are
disjoint (`hk_disj`), so two definitions after of one register go to two
definitions before.  **`alias_onceR`** (`+alias`): an op kept is the op
before with its reads renamed and its destination unchanged, at a place the
walk of the body gives, and a parameter after is one before.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- **Plain single assignment** on the blocks reachable from `0`: every
register has at most one definition, a parameter or an op, dead fills
included. -/
def DefOnceR (bl : Map Blob) : Prop :=
  ∀ r s s', Reach bl s.1 → DefSite bl r s → Reach bl s'.1 → DefSite bl r s' → s = s'

/-- **The block invariant of the driver**: `DInvT` (distinct parameters,
`PassOK`, `Acyclic`, `DownPar`, bracketed trace hints), `DefFirst`, no `%lti`
end, and plain single assignment on the reachable blocks. -/
def DInvR (bl : Map Blob) : Prop := DInvT bl ∧ DefFirst bl ∧ NoLti bl ∧ DefOnceR bl

theorem defOnceB_of_R {bl : Map Blob} (h : DefOnceR bl) : DefOnceB bl :=
  fun r s s' hs hs' => h r s s' hs.1 hs.2.1 hs'.1 hs'.2.1

theorem deadFill_site {bl : Map Blob} {r o i : Nat} (h : DeadFill bl r o i) : DefSite bl r (o, some i) := by
  obtain ⟨b, hb, -, ⟨n, hn⟩, -, -⟩ := h
  exact ⟨b, _, hb, hn, rfl⟩

/-- **Plain single assignment gives `FillFresh`**: the only definition of a
register with a dead fill is that fill, which does not count. -/
theorem fillFresh_of_R {bl : Map Blob} (h : DefOnceR bl) : FillFresh bl := by
  intro r o i hR hdf s hs
  have e := h r _ _ hs.1 hs.2.1 hR (deadFill_site hdf)
  subst e
  exact hs.2.2 i rfl hdf

theorem pw_rel {α : Type} {R : α → α → Prop} (hs : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ea | ha <;> rcases List.mem_cons.mp hb with eb | hb
    · exact absurd (ea.trans eb.symm) hne
    · rw [ea]; exact h.1 b hb
    · rw [eb]; exact hs (h.1 a ha)
    · exact pw_rel hs h.2 ha hb hne

/-- Two ops of a body whose destinations are one register, in a body whose
destinations are distinct, are one op. -/
theorem filterMap_nodup_idx {f : Pole → Option Nat} : ∀ (l : List Pole) (i j : Nat) (a b : Pole) (r : Nat),
    (l.filterMap f).Nodup → l[i]? = some a → l[j]? = some b → f a = some r → f b = some r → i = j
  | [], _, _, _, _, _, _, h, _, _, _ => by simp at h
  | x :: l, i, j, a, b, r, hn, ha, hb, hfa, hfb => by
    have hn' : (l.filterMap f).Nodup := hn.sublist ((List.sublist_cons_self x l).filterMap f)
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
        subst ha
        rw [List.filterMap_cons, hfa] at hn
        exact absurd (List.mem_filterMap.mpr ⟨b, List.mem_of_getElem? hb, hfb⟩) (List.nodup_cons.mp hn).1
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
        subst hb
        rw [List.filterMap_cons, hfb] at hn
        exact absurd (List.mem_filterMap.mpr ⟨a, List.mem_of_getElem? ha, hfa⟩) (List.nodup_cons.mp hn).1
      | succ j =>
        simp only [List.getElem?_cons_succ] at ha hb
        rw [filterMap_nodup_idx l i j a b r hn' ha hb hfa hfb]

/-- **Single assignment over all blocks** (`DefOnce`: the definitions of the
whole map are distinct) gives `DefOnceR`. -/
theorem defOnceR_of_defOnce {bl : Map Blob} (h : DefOnce bl) : DefOnceR bl := by
  unfold DefOnce allDefs List.Nodup at h
  rw [List.pairwise_flatMap] at h
  obtain ⟨hin, hpw⟩ := h
  have site : ∀ r (s : Nat × Option Nat), DefSite bl r s → ∃ b, HoonMap.get bl s.1 = some b ∧ r ∈ blockDefs b := by
    rintro r ⟨o, _ | i⟩ hd
    · obtain ⟨b, hb, hm⟩ := hd
      exact ⟨b, hb, List.mem_append_left _ hm⟩
    · obtain ⟨b, op, hb, hop, hdst⟩ := hd
      exact ⟨b, hb, List.mem_append_right _ (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hop, hdst⟩)⟩
  intro r s s' _ hd _ hd'
  obtain ⟨b, hb, hm⟩ := site r s hd
  obtain ⟨b', hb', hm'⟩ := site r s' hd'
  have hk : s.1 ∈ MapKeys.keys bl := (MapKeys.mem_keys bl _).mpr (by rw [hb]; rfl)
  have hk' : s'.1 ∈ MapKeys.keys bl := (MapKeys.mem_keys bl _).mpr (by rw [hb']; rfl)
  by_cases ho : s.1 = s'.1
  · obtain ⟨o, opt⟩ := s
    obtain ⟨o', opt'⟩ := s'
    simp only at ho hb hb' hk
    subst ho
    rw [hb] at hb'; cases hb'
    have hnd : (blockDefs b).Nodup := by
      have := hin o hk
      rw [hb] at this
      exact this
    unfold blockDefs at hnd
    obtain ⟨-, hnd2, hdisj⟩ := List.nodup_append.mp hnd
    cases opt with
    | none =>
      cases opt' with
      | none => rfl
      | some j' =>
        obtain ⟨b2, op, hb2, hop, hdst⟩ := hd'
        obtain ⟨b3, hb3, hm3⟩ := hd
        rw [hb] at hb2 hb3; cases hb2; cases hb3
        exact absurd rfl (hdisj r hm3 r (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hop, hdst⟩))
    | some j =>
      cases opt' with
      | none =>
        obtain ⟨b2, op, hb2, hop, hdst⟩ := hd
        obtain ⟨b3, hb3, hm3⟩ := hd'
        rw [hb] at hb2 hb3; cases hb2; cases hb3
        exact absurd rfl (hdisj r hm3 r (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hop, hdst⟩))
      | some j' =>
        obtain ⟨b2, op, hb2, hop, hdst⟩ := hd
        obtain ⟨b3, op', hb3, hop', hdst'⟩ := hd'
        rw [hb] at hb2 hb3; cases hb2; cases hb3
        rw [filterMap_nodup_idx b.body j j' op op' r hnd2 hop hop' hdst hdst']
  · exfalso
    have := pw_rel (R := fun a₁ a₂ => ∀ x ∈ ((HoonMap.get bl a₁).map blockDefs).getD [],
        ∀ y ∈ ((HoonMap.get bl a₂).map blockDefs).getD [], x ≠ y)
      (fun h x hx y hy e => h y hy x hx e.symm) hpw hk hk' ho
    exact this r (by rw [hb]; exact hm) r (by rw [hb']; exact hm') rfl

theorem dInvR_dInvS {bl : Map Blob} (h : DInvR bl) : DInvS bl :=
  ⟨h.1, ⟨defOnceB_of_R h.2.2.2, h.2.1⟩, h.2.2.1⟩

theorem dInvR_of {bl : Map Blob} (hS : DInvS bl) (hO : DefOnceR bl) : DInvR bl :=
  ⟨hS.1, hS.2.1.2, hS.2.2, hO⟩

/-- **A map of the places of definitions after to places before**, reachable
and injective for a fixed register, carries `DefOnceR` over. -/
theorem onceR_of_map {bl bl' : Map Blob} (m : Nat × Option Nat → Nat × Option Nat)
    (hsite : ∀ r s, Reach bl' s.1 → DefSite bl' r s → Reach bl (m s).1 ∧ DefSite bl r (m s))
    (hinj : ∀ r s s', DefSite bl' r s → DefSite bl' r s' → m s = m s' → s = s')
    (h : DefOnceR bl) : DefOnceR bl' := by
  intro r s s' hr hd hr' hd'
  obtain ⟨a1, a2⟩ := hsite r s hr hd
  obtain ⟨b1, b2⟩ := hsite r s' hr' hd'
  exact hinj r s s' hd hd' (h r _ _ a1 a2 b1 b2)

/-- The place before of a place after, for a pass that keeps labels and maps
the `j`-th op of block `o` to place `ι o j`. -/
def subMap (ι : Nat → Nat → Nat) : Nat × Option Nat → Nat × Option Nat
  | (o, none) => (o, none)
  | (o, some j) => (o, some (ι o j))

/-- **A pass that keeps labels and parameters and a monotone part of each
body keeps `DefOnceR`**: every op after that writes a register is the op at
`ι o j` before, `ι o` is strictly monotone on the ops after, and a block
reachable after was reachable before. -/
theorem onceR_of_sub {bl bl' : Map Blob} (ι : Nat → Nat → Nat) (hreach : ∀ o, Reach bl' o → Reach bl o)
    (hback : ∀ o b', HoonMap.get bl' o = some b' → ∃ b, HoonMap.get bl o = some b ∧ b'.par = b.par ∧
      (∀ j op r, b'.body[j]? = some op → aliasDst op = some r → b.body[ι o j]? = some op) ∧
      ∀ j j', j < j' → j < b'.body.length → ι o j < ι o j')
    (h : DefOnceR bl) : DefOnceR bl' := by
  refine onceR_of_map (subMap ι) (fun r s hr hd => ?_) (fun r s s' hd hd' he => ?_) h
  · obtain ⟨o, _ | j⟩ := s
    · obtain ⟨b', hb', hm⟩ := hd
      obtain ⟨b, hb, hp, -, -⟩ := hback o b' hb'
      exact ⟨hreach o hr, b, hb, by rw [← hp]; exact hm⟩
    · obtain ⟨b', op, hb', hop, hdst⟩ := hd
      obtain ⟨b, hb, -, hops, -⟩ := hback o b' hb'
      exact ⟨hreach o hr, b, op, hb, hops j op r hop hdst, hdst⟩
  · obtain ⟨o, _ | j⟩ := s <;> obtain ⟨o', _ | j'⟩ := s' <;> simp only [subMap, Prod.mk.injEq] at he
    · rw [he.1]
    · simp at he
    · simp at he
    · obtain ⟨rfl, he⟩ := he
      simp only [Option.some.injEq] at he
      obtain ⟨b', op, hb', hop, -⟩ := hd
      obtain ⟨b'', op', hb'', hop', -⟩ := hd'
      rw [hb'] at hb''; cases hb''
      obtain ⟨b, -, -, -, hmono⟩ := hback o b' hb'
      have hl : j < b'.body.length := (List.getElem?_eq_some_iff.mp hop).1
      have hl' : j' < b'.body.length := (List.getElem?_eq_some_iff.mp hop').1
      rcases Nat.lt_trichotomy j j' with hc | hc | hc
      · have := hmono j j' hc hl; omega
      · rw [hc]
      · have := hmono j' j hc hl'; omega

/-! ## The passes but `+remove-hops` and `+alias` -/

/-- **`+remove-useless-branching` keeps `DefOnceR`**: the epilogue it appends
writes no register. -/
theorem rub_onceR {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hO : DefOnceR bl) : DefOnceR bl' := by
  have hR := rub_blocks h
  refine onceR_of_sub (fun _ j => j) (fun o ho => ssk_rub_reach hR ho) (fun o b' hb' => ?_) hO
  obtain ⟨b, e, hb, he, rfl⟩ := hR.back hb'
  refine ⟨b, hb, rfl, fun j op r hop hd => ?_, fun j j' hj _ => hj⟩
  simp only [rubBlob] at hop
  by_cases hi : j < b.body.length
  · rwa [List.getElem?_append_left hi] at hop
  · rw [List.getElem?_append_right (by omega)] at hop
    rw [ssk_rub_epi he op (List.mem_of_getElem? hop)] at hd; cases hd

/-- **`+remove-empty-middle` keeps `DefOnceR`**: it changes ends only, and a
block reachable after was reachable before. -/
theorem mid_onceR {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (hO : DefOnceR bl) : DefOnceR bl' := by
  have hM := mid_blocks h
  refine onceR_of_sub (fun _ j => j) (fun o ho => ssk_mid_reach hM ho) (fun o b' hb' => ?_) hO
  obtain ⟨b, f', hb, -, rfl⟩ := hM.back hb'
  exact ⟨b, hb, rfl, fun j op r hop _ => hop, fun j j' hj _ => hj⟩

/-- **Filtering bodies keeps `DefOnceR`** (the `j`-th op kept sits at
`fidx`). -/
theorem filt_onceR {bl bl' : Map Blob} {p : Pole → Bool}
    (hg : ∀ o, HoonMap.get bl' o = (HoonMap.get bl o).map fun b => { b with body := b.body.filter p })
    (hO : DefOnceR bl) : DefOnceR bl' := by
  refine onceR_of_sub (fun o j => ((HoonMap.get bl o).map fun b => fidx p b.body j).getD j)
    (fun o ho => reach_filt hg ho) (fun o b' hb' => ?_) hO
  rw [hg] at hb'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
  simp only [hb, Option.map_some, Option.getD_some]
  refine ⟨b, rfl, rfl, fun j op r hop _ => ?_, fun j j' hj hl => fidx_lt_of p b.body j j' hj hl⟩
  rw [← List.head?_drop, ← fidx_head, List.head?_drop]; exact hop

/-- **`+trim-trace-hints` keeps `DefOnceR`**: it filters bodies. -/
theorem trim_onceR {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (h : trimTraceHints bl topo rev = some bl') (hO : DefOnceR bl) : DefOnceR bl' := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact filt_onceR (trimRun_get bl uns (trimOpened bl)) hO

/-- **`+remove-dead-code` keeps `DefOnceR`**, on a `topo` with `TopoOK`: it
keeps a sublist of each body (the `j`-th op kept sits at `didx`). -/
theorem dead_onceR {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') (hO : DefOnceR bl) : DefOnceR bl' := by
  obtain ⟨Sf, W, hout⟩ := ssk_dead_walk ht h
  have hback : ∀ o b', HoonMap.get bl' o = some b' → ∃ b, HoonMap.get bl o = some b ∧
      b' = { b with body := (deadF b.body (Sf o)).1 } := by
    intro o b' hb'
    by_cases ho : o ∈ topo
    · obtain ⟨b, hb, hb2, -⟩ := W.blk o ho
      rw [hb2] at hb'; cases hb'
      exact ⟨b, hb, rfl⟩
    · rw [hout o ho] at hb'; cases hb'
  refine onceR_of_sub (fun o j => ((HoonMap.get bl o).map fun b => didx b.body (Sf o) j).getD j)
    (fun o hr => ?_) (fun o b' hb' => ?_) hO
  · induction hr with
    | zero => exact Reach.zero
    | jump _ hb hj ih =>
      obtain ⟨b, hb0, rfl⟩ := hback _ _ hb
      exact Reach.jump (j := _) ih hb0 hj
  · obtain ⟨b, hb, rfl⟩ := hback o b' hb'
    simp only [hb, Option.map_some, Option.getD_some]
    refine ⟨b, rfl, rfl, fun j op r hop _ => ?_, fun j j' hj hl => ssk_dd_lt (Sf o) b.body j j' hj hl⟩
    rw [← List.head?_drop, ← ssk_dd_head, List.head?_drop]; exact hop

/-! ## `+remove-hops` -/

section
variable {bl bl' : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

/-- **A definition after at a place of a merged block** goes to a reachable
definition before, in the chain of the block (`hk_live` without the clause on
dead fills). -/
theorem hk_site (hB : HopsBlocks bl rev topo bl') {o : Nat} {b : Blob} {T : List Pole} {F : Termin}
    {f : Nat → Nat × Option Nat} (hbo : HoonMap.get bl o = some b) (hmo : HoonMap.get bl' o = some (merge b T F))
    (hS : HkSites bl rev o b T F f) {r : Nat} {opt : Option Nat} (ho : Reach bl' o)
    (hds : DefSite bl' r (o, opt)) :
    Reach bl (hkSig f o opt).1 ∧ DefSite bl r (hkSig f o opt) ∧ HkMem bl rev o (hkSig f o opt).1 := by
  have hob : Reach bl o := hk_reach_back hB ho
  cases opt with
  | none =>
    obtain ⟨m, hm, hr⟩ := hds
    rw [hmo] at hm; cases hm
    exact ⟨hob, ⟨b, hbo, hr⟩, HkMem.refl⟩
  | some k =>
    obtain ⟨m, op, hm, hop, hd⟩ := hds
    rw [hmo] at hm; cases hm
    have hk : k < (b.body ++ T).length := (List.getElem?_eq_some_iff.mp hop).1
    obtain ⟨hmem, -⟩ := hS.mem k hk
    simp only [hkSig]
    refine ⟨hk_mem_reach hmem hob, ?_, hmem⟩
    cases e : f k with
    | mk x oj =>
      cases oj with
      | none => exact hS.par k x op r e hop hd
      | some j =>
        obtain ⟨bx, hbx, hj⟩ := hS.op k x j hk e
        exact ⟨bx, op, hbx, by rw [hj]; exact hop, hd⟩

/-- **`+remove-hops` keeps `DefOnceR`**, on blocks with `Acyclic` and
`ParNodup`, with `TopoInv`: the places of a merged body go injectively to
definitions before (`HkSites`), and the chains of two blocks reachable after
are disjoint (`hk_disj`). -/
theorem hk_onceR (hB : HopsBlocks bl rev topo bl') (hT : TopoInv bl topo rev) (hA : Acyclic bl)
    (hpn : ParNodup bl) (h1 : DefOnceR bl) : DefOnceR bl' := by
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
  rintro r ⟨o, opt⟩ ⟨o', opt'⟩ hr hs hr' hs'
  obtain ⟨m, hm⟩ := blk hs
  obtain ⟨m', hm'⟩ := blk hs'
  obtain ⟨b, T, F, f, hb, rfl, hS⟩ := hsites o m hm
  obtain ⟨b', T', F', f', hb', rfl, hS'⟩ := hsites o' m' hm'
  obtain ⟨a1, a2, M1⟩ := hk_site hB hb hm hS hr hs
  obtain ⟨c1, c2, M2⟩ := hk_site hB hb' hm' hS' hr' hs'
  have e := h1 r _ _ a1 a2 c1 c2
  rw [e] at M1
  have hoo : o = o' := hk_disj hB hT hA hr hr' M1 M2
  subst hoo
  obtain ⟨d1, d2, -⟩ := hk_site hB hb hm hS hr hs'
  have e2 := h1 r _ _ a1 a2 d1 d2
  have hk : ∀ {k}, DefSite bl' r (o, some k) → ∃ op, (b.body ++ T)[k]? = some op ∧ aliasDst op = some r := by
    intro k h
    obtain ⟨m2, op, hm2, hop, hd⟩ := h
    rw [hm] at hm2; cases hm2
    exact ⟨op, hop, hd⟩
  cases opt with
  | none =>
    cases opt' with
    | none => rfl
    | some k' =>
      obtain ⟨op, hop, -⟩ := hk hs'
      exact absurd e2.symm (hS.mem k' (List.getElem?_eq_some_iff.mp hop).1).2
  | some k =>
    cases opt' with
    | none =>
      obtain ⟨op, hop, -⟩ := hk hs
      exact absurd e2 (hS.mem k (List.getElem?_eq_some_iff.mp hop).1).2
    | some k' =>
      obtain ⟨op, hop, hd⟩ := hk hs
      obtain ⟨op', hop', hd'⟩ := hk hs'
      rw [hS.inj k k' op op' r hop hop' hd hd' e2]

end

/-- **`+remove-hops` keeps `DefOnceR`** at the arguments the driver gives
it. -/
theorem hops_onceR {fuel : Nat} {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {ch : Bool}
    (hD : DInvT bl) (hi : TopoInv bl topo rev) (h : removeHops fuel bl rev topo = some (ch, bl'))
    (hO : DefOnceR bl) : DefOnceR bl' :=
  hk_onceR (hops_blocks hi.1.1 hi.1.2.1 h) hi hD.1.2.1 hD.1.1.1 hO

/-! ## `+alias` -/

/-- A definition after at an op of a block of `+alias` is one before, at the
op it was kept from. -/
theorem alias_site_op {pick : List Nat → Nat} {o i r : Nat} {b' b : Blob} {st0 : ABody}
    {rb : List Pole × ABody} {rf : Termin × (Nat → List Nat) × Bool} {bl' : Map Blob}
    (hb' : HoonMap.get bl' o = some b') (hrb : aliasBody pick b.body st0 = some rb)
    (hbe : b' = { par := b.par, body := rb.1, fin := rf.1 }) (hd : DefSite bl' r (o, some i)) :
    ∃ k op outa sta, b.body[k]? = some op ∧ aliasDst op = some r ∧
      aliasBody pick (b.body.take k) st0 = some (outa, sta) ∧ outa.length = i := by
  obtain ⟨b2, op', hb2, hi, hdst⟩ := hd
  rw [hb'] at hb2; cases hb2
  subst hbe
  obtain ⟨k, op, sta, outa, outb, st1, st', hk, hba, hlen, hop, -, -⟩ := abody_split hrb hi
  exact ⟨k, op, outa, sta, hk, by rw [← hdst, aop_rename hop, aliasDst_rename], hba, hlen⟩

/-- **`+alias` keeps `DefOnceR`**: it keeps a subsequence of each body with
the destinations unchanged, and its blocks reachable after were reachable
before. -/
theorem alias_onceR {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
    {rev : Map (List Nat)} {gF : AGen Map} (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) (hO : DefOnceR bl) : DefOnceR gF.new := by
  have hGs := alias_targetsSub hT h
  have site : ∀ r o opt, Reach gF.new o → DefSite gF.new r (o, opt) →
      Reach bl o ∧ ∃ opt0, DefSite bl r (o, opt0) ∧ opt.isSome = opt0.isSome := by
    intro r o opt hr hd
    refine ⟨reach_sub hGs hr, ?_⟩
    cases opt with
    | none =>
      obtain ⟨b', hb', hm⟩ := hd
      obtain ⟨b, _st0, _rb, _rf, hb, -, hbe, -, -⟩ := alias_blk hT h hb'
      rw [hbe] at hm
      exact ⟨none, ⟨b, hb, hm⟩, rfl⟩
    | some i =>
      obtain ⟨b', -, hb', -, -⟩ := id hd
      obtain ⟨b, st0, rb, rf, hb, hrb, hbe, -, -⟩ := alias_blk hT h hb'
      obtain ⟨k, op, -, -, hk, hdk, -, -⟩ := alias_site_op hb' hrb hbe hd
      exact ⟨some k, ⟨b, op, hb, hk, hdk⟩, rfl⟩
  rintro r ⟨o, opt⟩ ⟨o', opt'⟩ hr hd hr' hd'
  obtain ⟨a1, p0, a2, a3⟩ := site r o opt hr hd
  obtain ⟨c1, p1, c2, c3⟩ := site r o' opt' hr' hd'
  have e := hO r _ _ a1 a2 c1 c2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  cases opt with
  | none =>
    cases opt' with
    | none => rfl
    | some i' => rw [← c3] at a3; cases a3
  | some i =>
    cases opt' with
    | none => rw [← c3] at a3; cases a3
    | some i' =>
      obtain ⟨b', -, hb', -, -⟩ := id hd
      obtain ⟨b, st0, rb, rf, hb, hrb, hbe, -, -⟩ := alias_blk hT h hb'
      obtain ⟨k1, op1, outa1, sta1, hk1, hd1, hba1, hl1⟩ := alias_site_op hb' hrb hbe hd
      obtain ⟨k2, op2, outa2, sta2, hk2, hd2, hba2, hl2⟩ := alias_site_op hb' hrb hbe hd'
      have e2 := hO r (o, some k1) (o, some k2) a1 ⟨b, op1, hb, hk1, hd1⟩ a1 ⟨b, op2, hb, hk2, hd2⟩
      simp only [Prod.mk.injEq, Option.some.injEq, true_and] at e2
      subst e2
      rw [hba1] at hba2
      simp only [Option.some.injEq, Prod.mk.injEq] at hba2
      rw [← hl1, ← hl2, hba2.1]

end Opt
end SkaModel
end Formalization
