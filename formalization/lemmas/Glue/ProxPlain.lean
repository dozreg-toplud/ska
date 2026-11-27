import lemmas.Glue.StraightPlain

/-!
# The proxy facts on `PlainN` from track D's `IL` (track G, twelfth pass)

LEDGER 2.c.  `ProxEnd` (`Glue/StraightRen.lean`) asks three facts of the
state the top `+kerf` leaves; its `src` (a block that splits a key or tests
it with `%cel` does not write the key's source) is a cross-block fact with
no invariant behind it.  What the renaming needs is narrower:

* the `%cel` disjunct of `Want` matters only for a register that is
  annotated somewhere (it feeds `CellOut` of an edge into an annotated
  label), and `blocksOKA_np` annotates no key; so `WantN` keeps it only
  then, and **`celAnn_renameN`** is `celAnn_rename` under `RenAN`;
* then `src` is needed only for keys that are SPLIT, and on every checked
  state no key is split (`Glue/ProxPlainCheck.lean`: 2,856 `PlainN` nomms,
  7 direct calls, 7,920 `enumDX` nomms; 28 hand-made nomms where a `%cel`
  of a key does occur).

`ProxOKN`: `wr` and `nsk` (no split op splits a key).  On `PlainN`:

* `wr` and `nsk` are track D's `IL.cond` (a key is never defined,
  `topU_of`), once every split register is defined earlier in its own body
  (`SDBody`: the only splits are those of `+kern-need`, each after the
  `%mov` into the register it splits);
* `SplitDefEnd`: `SDBody` of every block after the top `+kerf` (the one
  body-local leaf left, a run invariant of the `KP` shape);
* **`proxEndN_of`**: `ProxEndN` from `SplitDefEnd`;
* **`guardMonoC_plainE`**, **`entryMono_plainE`**: `GuardMonoC` / `EntryMono`
  on `PlainM` from `KIMid` and `SplitDefEnd`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## The narrower renaming condition -/

/-- The registers whose guard matters in block `b` at `k`, the `%cel` test
counted only for a register annotated somewhere. -/
def WantN (K : Nat → Nat → Prop) (k : Nat) (b : Blob) (s : Nat) : Prop :=
  K k s ∨ (∃ p ∈ b.body, splitReg p = some s) ∨ (Pole.cel s ∈ b.body ∧ ∃ l, K l s)

/-- **The narrower renaming condition.** -/
def RenAN (bs : Map Blob) (K : Nat → Nat → Prop) (f : Nat → Nat) : Prop :=
  ∀ k b, HoonMap.get bs k = some b → ∀ s, WantN K k b s →
    (∀ q ∈ b.body, ∀ x, aliasDst q = some x → f x = f s → x = s) ∧ (∀ p ∈ b.par, f p = f s → p = s)

theorem wantN_of_cellOut {K : Nat → Nat → Prop} {k : Nat} {b : Blob} {s : Nat} (h : CellOut K k b s)
    (hl : ∃ l, K l s) : WantN K k b s := by
  rcases h with ⟨h1, -⟩ | ⟨j, -, hc, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr ⟨List.mem_of_getElem? hc, hl⟩)

/-- **The renaming path keeps the cell annotation** under `RenAN`. -/
theorem celAnn_renameN {bs new : Map Blob} {K : Nat → Nat → Prop} {f : Nat → Nat} (hB : BlocksOKA bs K)
    (hf : RenAN bs K f) (h : renameBlocks bs f = some new) :
    NoPoison new ∧ CelAnn new (fun l s => ∃ s0, K l s0 ∧ f s0 = s) := by
  have get : ∀ k b', HoonMap.get new k = some b' → ∃ b fin, HoonMap.get bs k = some b ∧
      chaseFin bs f b.fin = some fin ∧ b' = ⟨b.par.map f, b.body.map (renPole f), fin⟩ := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := Raw.renameBlocks_get h hk
    unfold keepBlock at hkb
    split at hkb
    · cases hkb
    obtain ⟨fin, hfin, e⟩ := Option.map_eq_some_iff.mp hkb
    cases e
    exact ⟨b, fin, hb, hfin, rfl⟩
  have back : ∀ s0 br j j1, chase bs br j = some j1 → K j1.there s0 → K j.there s0 :=
    fun s0 br j j1 hc hk1 => chase_back bs br (fun l => K l s0) (ann_back hB br s0) j j1 hc hk1
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro k b' j' _ hk hj
    obtain ⟨b, fin, hb, hfin, rfl⟩ := get k b' hk
    obtain ⟨j, hj0, br, j1, hc, rfl⟩ := chaseFin_jmps hfin j' hj
    refine none_not_mem_renJmp (chase_keeps bs br (fun j => Option.none ∉ j.args) (fun k1 b1 t hb1 ht => ?_)
      j j1 hc (hB.noNone k b hb j hj0))
    exact hB.noNone k1 b1 hb1 t (by rw [ht]; simp [getJmps])
  · rintro k b' s hk ⟨s0, hk0, rfl⟩ hm
    obtain ⟨b, fin, hb, hfin, rfl⟩ := get k b' hk
    obtain ⟨p, hp, ep⟩ := List.mem_map.mp hm
    exact hB.par k b s0 hb hk0 (by rw [← (hf k b hb s0 (Or.inl hk0)).2 p hp ep]; exact hp)
  · rintro s ⟨s0, h0, -⟩; exact hB.zero s0 h0
  · rintro k b' j' s _ hk hj ⟨s0, hk0, rfl⟩
    obtain ⟨b, fin, hb, hfin, rfl⟩ := get k b' hk
    have W : CellOut K k b s0 → ∀ q ∈ b.body, ∀ x, aliasDst q = some x → f x = f s0 → x = s0 :=
      fun hc => (hf k b hb s0 (wantN_of_cellOut hc ⟨_, hk0⟩)).1
    by_cases hq : ∃ s1 z w, b.fin = Termin.clq s1 z w
    · obtain ⟨s1, z, w, hfb⟩ := hq
      have orig := fun j hj hk => hB.edge k b j s0 hb hj hk
      rw [hfb] at hfin orig
      simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hfin
      obtain ⟨z', hz, w', hw, rfl⟩ := hfin
      have hwback : K w'.there s0 → CellOut K k b s0 := fun hk1 => by
        rcases orig w (by simp [getJmps]) (back s0 true w w' hw hk1) with ⟨z2, w2, e2, ne⟩ | hc
        · cases e2; exact absurd rfl ne
        · exact hc
      simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · rcases orig z (by simp [getJmps]) (back s0 true z z' hz hk0) with ⟨z2, w2, e2, ne⟩ | hc
        · cases e2
          by_cases hzw : w'.there = z'.there
          · have hc := hwback (by rw [hzw]; exact hk0)
            exact Or.inr (cellOut_ren hc (W hc))
          · exact Or.inl ⟨renJmp f z', renJmp f w', rfl, hzw⟩
        · exact Or.inr (cellOut_ren hc (W hc))
      · have hc := hwback hk0
        exact Or.inr (cellOut_ren hc (W hc))
    · obtain ⟨j, hj0, br, j1, hc, rfl⟩ := chaseFin_jmps hfin j' hj
      rcases hB.edge k b j s0 hb hj0 (back s0 br j j1 hc hk0) with ⟨z2, w2, e2, -⟩ | hc'
      · exact absurd ⟨_, _, _, e2⟩ hq
      · exact Or.inr (cellOut_ren hc' (W hc'))
  · intro k b' i p' s _ hk hp hs
    obtain ⟨b, fin, hb, hfin, rfl⟩ := get k b' hk
    change (b.body.map (renPole f))[i]? = some p' at hp
    rw [List.getElem?_map] at hp
    obtain ⟨p, hp0, rfl⟩ := Option.map_eq_some_iff.mp hp
    rw [splitReg_ren] at hs
    obtain ⟨s0, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
    have W := (hf k b hb s0 (Or.inr (Or.inl ⟨p, List.mem_of_getElem? hp0, hs0⟩))).1
    rcases hB.split k b hb i p s0 hp0 hs0 with ⟨j, hj, hc, hw⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨j, hj, by show (b.body.map (renPole f))[j]? = _; rw [List.getElem?_map, hc]; rfl,
        fun l l1 l2 => noWrite_ren (hw l l1 l2) W⟩
    · exact Or.inr ⟨⟨s0, h1, rfl⟩, nwb_ren h2 W⟩

/-! ## The two proxy facts -/

/-- **The proxy facts the renaming needs**: no written register and no
parameter is a key (`wr`), no split op splits a key (`nsk`). -/
structure ProxOKN (bl : Map Blob) (cond : Map (Nat × List Nat)) : Prop where
  wr : ∀ k b, HoonMap.get bl k = some b → ∀ x, (x ∈ b.par ∨ ∃ q ∈ b.body, aliasDst q = some x) →
    HoonMap.get cond x = Option.none
  nsk : ∀ k b, HoonMap.get bl k = some b → ∀ p ∈ b.body, ∀ s, splitReg p = some s →
    HoonMap.get cond s = Option.none

theorem proxOKN_start {bl : Map Blob} {cond : Map (Nat × List Nat)} {o : Nat} {start : Blob} (hP : ProxOKN bl cond)
    (hst : HoonMap.get bl o = some start) : ProxOKN (HoonMap.put (HoonMap.del bl o) 0 start) cond where
  wr := fun k b hb => by
    rcases get_start hb with ⟨-, rfl⟩ | hb
    · exact hP.wr o _ hst
    · exact hP.wr k b hb
  nsk := fun k b hb => by
    rcases get_start hb with ⟨-, rfl⟩ | hb
    · exact hP.nsk o _ hst
    · exact hP.nsk k b hb

/-- **The annotation restricted to registers that are no keys.** -/
theorem blocksOKA_npN {bl : Map Blob} {cond : Map (Nat × List Nat)} {K : Nat → Nat → Prop} (hB : BlocksOKA bl K)
    (hP : ProxOKN bl cond) : BlocksOKA bl (fun l s => K l s ∧ HoonMap.get cond s = Option.none) where
  noNone := hB.noNone
  par := fun o b s hb hk => hB.par o b s hb hk.1
  zero := fun s hk => hB.zero s hk.1
  edge := fun o b j s hb hj hk => by
    rcases hB.edge o b j s hb hj hk.1 with h | ⟨h1, h2⟩ | h3
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨⟨h1, hk.2⟩, h2⟩)
    · exact Or.inr (Or.inr h3)
  split := fun o b hb i p s hp hs => by
    have hc := hP.nsk o b hb p (List.mem_of_getElem? hp) s hs
    rcases hB.split o b hb i p s hp hs with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨h1, hc⟩, h2⟩

/-- **`ProxOKN` gives `RenAN` for `renReg ∘ unproxy`**: every register whose
guard matters is no key. -/
theorem renA_proxN {bl : Map Blob} {cond : Map (Nat × List Nat)} {K : Nat → Nat → Prop} (hP : ProxOKN bl cond)
    (r0 n : Nat) :
    RenAN bl (fun l s => K l s ∧ HoonMap.get cond s = Option.none) (proxRen cond (hasProxies cond) (renReg r0 n)) := by
  have key : ∀ k b, HoonMap.get bl k = some b → ∀ s x, WantN (fun l s => K l s ∧ HoonMap.get cond s = Option.none) k b s →
      (x ∈ b.par ∨ ∃ q ∈ b.body, aliasDst q = some x) →
      proxRen cond (hasProxies cond) (renReg r0 n) x = proxRen cond (hasProxies cond) (renReg r0 n) s → x = s := by
    intro k b hb s x hW hx e
    have hs : HoonMap.get cond s = Option.none := by
      rcases hW with ⟨-, h⟩ | ⟨p, hp, hsp⟩ | ⟨-, l, -, h⟩
      · exact h
      · exact hP.nsk k b hb p hp s hsp
      · exact h
    have hxn := hP.wr k b hb x hx
    simp only [proxRen] at e
    have ex := renReg_inj r0 n _ _ e
    cases hp : hasProxies cond
    · simpa [hp] using ex
    · simpa [hp, unproxy_self hxn, unproxy_self hs] using ex
  intro k b hb s hW
  exact ⟨fun q hq x hx e => key k b hb s x hW (Or.inr ⟨q, hq, hx⟩) e,
    fun p hp e => key k b hb s p hW (Or.inl hp) e⟩

/-! ## `PlainN`: from track D's `IL` and the body-local leaf -/

/-- Every split register of a body is defined by an earlier op of it. -/
def SDBody (body : List Pole) : Prop :=
  ∀ i p s, body[i]? = some p → splitReg p = some s → ∃ j : Nat, j < i ∧ ∃ q, body[j]? = some q ∧ aliasDst q = some s

/-- **The body-local leaf**: after the top run and its `+kerf` on
`PlainN`, every body meets `SDBody`. -/
def SplitDefEnd (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv) :
    Prop :=
  ∀ nm, PlainN nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
    (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2) →
    ∀ k b, HoonMap.get g2.blocks k = some b → SDBody b.body

/-- **The proxy facts at the end on `PlainN`.** -/
def ProxEndN (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop :=
  ∀ nm, PlainN nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) →
    kerf nex g1 = some ((o, sub), g2) → ProxOKN g2.blocks g2.cond

/-- **`ProxEndN` from `SplitDefEnd`**: `wr` and `nsk` are `IL.cond` (a key
has no definition) at the state after the top `+kerf` (`topU_of`). -/
theorem proxEndN_of {env : CallEnv} (hS : SplitDefEnd S Map env) : ProxEndN S Map env := by
  intro nm hp nex g1 g2 o sub h1 h2
  rw [runLCM_eq env true nm (by simp [plainN_noDirect nm hp])] at h1
  have T := topU_of (S := S) env splitSpecL intoSpecL hp h1 h2
  have nd : ∀ x, Defd g2.blocks x → HoonMap.get g2.cond x = Option.none := by
    intro x hx
    cases e : HoonMap.get g2.cond x with
    | none => rfl
    | some v => exact absurd hx (T.il.cond x v e).2.1
  have dq : ∀ k b, HoonMap.get g2.blocks k = some b → ∀ q ∈ b.body, ∀ x, aliasDst q = some x → Defd g2.blocks x := by
    intro k b hb q hq x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    exact ⟨(k, some i), b, q, hb, hi, hx⟩
  refine ⟨fun k b hb x hx => nd x ?_, fun k b hb p hpb s hs => nd s ?_⟩
  · rcases hx with hx | ⟨q, hq, hx⟩
    · exact ⟨(k, Option.none), b, hb, hx⟩
    · exact dq k b hb q hq x hx
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpb
    obtain ⟨j, -, q, hq, hx⟩ := hS nm hp nex g1 g2 o sub h1 h2 k b hb i p s hi hs
    exact dq k b hb q (List.mem_of_getElem? hq) s hx

/-- **`GuardMonoC` on `PlainM`** from `KIMid` and `ProxEndN`. -/
theorem guardMonoC_plainE (hD : ∀ env, KIMid S Map env) (hP : ∀ env, ProxEndN S Map env) :
    GuardMonoC S Map PlainM := by
  intro env N bl nm c hf hs
  have hn : NoSixC nm := noSix_of_plain nm hf
  unfold finishLUCM at hs
  obtain ⟨⟨nex, g1⟩, h1, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨K, hI, hfo⟩ := top_kerfA (hD env) hn h1 h2
  have P := hP env nm hf nex g1 g2 o sub h1 h2
  dsimp only at hs
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at hs
  simp only [flattenNeed, List.headD, List.length] at hs
  obtain ⟨start, hst, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hs
  have P0 := proxOKN_start P hst
  have B1 := blocksOKA_npN (blocksOKA_start hI.ok hfo.2 hst) P0
  have R := celAnn_renameN B1 (renA_proxN P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`EntryMono` on `PlainM`** from `KIMid` and the body-local leaf
`SplitDefEnd` (track D's `optInMono_plain`, `readsInMono_plain`). -/
theorem entryMono_plainE (lib : Lib) (hD : ∀ env, KIMid S Map env) (hS : ∀ env, SplitDefEnd S Map env) :
    EntryMono S Map lib PlainM :=
  entryMono_of lib optInMono_plain readsInMono_plain (guardMonoC_plainE hD fun env => proxEndN_of (hS env))

end Glue
end SkaModel
end Formalization
