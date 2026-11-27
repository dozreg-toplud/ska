import lemmas.Glue.GuardCallsTop

/-!
# `StraightA`: the final pass keeps the cell annotation (track G, eleventh pass)

LEDGER 2.c.  The final pass of `finishLUCM` is `+to-straight` of the state
the top `+kerf` leaves.  On the run `[sub]` of inputs it is the renaming
path by `f = renReg sub 1 ∘ unproxy` (`toStraightF_run`): the start block is
moved to `0`, every kept block is renamed by `f` and its end chased.  The
old route (`blocksOK_rename` through `RenOK`: `f` sends no written register
onto another) fails with calls: an inner `+kerf` reads the register its
`%nok` / `%cal` writes through proxies, so `unproxy` merges that register
with its proxies (640 of the 7,920 `enumDX` states, `StraightRenCheck`).

What the renaming must keep is narrower (`RenA`): for every register whose
guard matters in a block (annotated there, split there or tested by `%cel`
there: `Want`), `f` sends no OTHER register the block writes or takes as a
parameter onto it.

* `chase_back`: what `+chase` lands on carries the annotation back to the
  jump it started from (a bypassed block is an empty hop: its edge condition
  is the annotation itself, `ann_back`).
* **`celAnn_rename`**: `BlocksOKA bs K` and `RenA bs K f` give `NoPoison` and
  `CelAnn` of the renamed blocks with the renamed annotation
  `fun l s => ∃ s0, K l s0 ∧ f s0 = s`.  A `%clq` whose two ends chase to
  one block loses its `ClqYes`; then the no-end's own edge condition gives
  `CellOut`.
* `blocksOKA_start`: moving the unannotated start block to `0`.
* `ProxOK bl cond`: the three proxy facts of a state, none naming the
  annotation: no written register or parameter is a key of `cond` (`wr`), a
  split of a key comes after a `%cel` of it (`cel`), and a block that splits
  or tests a key does not write or take its source (`src`).
* `blocksOKA_np`: the annotation restricted to registers that are no keys;
  `renA_prox`: `ProxOK` gives `RenA` for `renReg ∘ unproxy`.
* **`straightA_of`**: `StraightA` from the named hypothesis `ProxEnd`
  (`ProxOK` at the state after the top `+kerf`; checked: 7 of 7 direct calls,
  7,920 of 7,920 `enumDX`, `Glue/StraightRenCheck.lean`).
* **`guardMonoC_noSixP`**, `entryMono_noSixP`: `GuardMonoC` / `EntryMono` on
  `NoSixM` from `KIMid` and `ProxEnd`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## `+chase`, backward -/

theorem bypassable_body {br : Bool} {b : Blob} (h : bypassable br b = true) : b.body = [] := by
  obtain ⟨par, body, fin⟩ := b
  cases par <;> cases body <;> cases fin <;> simp_all [bypassable]

open Lean.Order in
/-- **A property of the target of a chase holds of the jump it started
from**, if every bypassed block passes it back from its hop. -/
theorem chase_back (bs : Map Blob) (br : Bool) (Q : Nat → Prop)
    (h : ∀ k b t, HoonMap.get bs k = some b → bypassable br b = true → b.fin = Termin.hop t → Q t.there → Q k) :
    ∀ j j', chase bs br j = some j' → Q j'.there → Q j.there := by
  refine chase.fixpoint_induct bs br (fun f => ∀ j j', f j = some j' → Q j'.there → Q j.there) ?_ ?_
  · exact admissible_pi_apply _ (fun j => admissible_pi _ (fun j' => Option.admissible_eq_some _ j'))
  · intro f ih j j' hf hj
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
    obtain ⟨b, hb, hf⟩ := hf
    split at hf
    · rename_i t ht
      split at hf
      · rename_i hby
        split at hf
        · exact h _ _ _ hb hby ht (ih t j' hf hj)
        · cases hf
      · cases hf; exact hj
    · cases hf; exact hj

/-- **An empty hop passes the annotation back.** -/
theorem ann_back {bs : Map Blob} {K : Nat → Nat → Prop} (hB : BlocksOKA bs K) (br : Bool) (s0 : Nat) :
    ∀ k b t, HoonMap.get bs k = some b → bypassable br b = true → b.fin = Termin.hop t → K t.there s0 →
      K k s0 := by
  intro k b t hb hby ht hk
  rcases hB.edge k b t s0 hb (by rw [ht]; simp [getJmps]) hk with ⟨z, w, e, -⟩ | ⟨h1, -⟩ | ⟨j, hj, -⟩
  · rw [ht] at e; cases e
  · exact h1
  · rw [bypassable_body hby] at hj; simp at hj

/-! ## Renaming a block -/

/-- The registers whose guard matters in block `b` at `k`. -/
def Want (K : Nat → Nat → Prop) (k : Nat) (b : Blob) (s : Nat) : Prop :=
  K k s ∨ (∃ p ∈ b.body, splitReg p = some s) ∨ Pole.cel s ∈ b.body

/-- **The renaming condition**: `f` sends no other register a block writes
or takes as a parameter onto a register whose guard matters there. -/
def RenA (bs : Map Blob) (K : Nat → Nat → Prop) (f : Nat → Nat) : Prop :=
  ∀ k b, HoonMap.get bs k = some b → ∀ s, Want K k b s →
    (∀ q ∈ b.body, ∀ x, aliasDst q = some x → f x = f s → x = s) ∧ (∀ p ∈ b.par, f p = f s → p = s)

theorem noWrite_ren {f : Nat → Nat} {body : List Pole} {s l : Nat}
    (hw : ∀ q, body[l]? = some q → aliasDst q ≠ some s)
    (hf : ∀ q ∈ body, ∀ x, aliasDst q = some x → f x = f s → x = s) :
    ∀ q, (body.map (renPole f))[l]? = some q → aliasDst q ≠ some (f s) := by
  intro q' hq
  rw [List.getElem?_map] at hq
  obtain ⟨q, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  rw [aliasDst_ren]
  intro e
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.mp e
  exact hw q hq0 (by rw [hx, hf q (List.mem_of_getElem? hq0) x hx ex])

theorem nwb_ren {f : Nat → Nat} {body : List Pole} {i s : Nat} (hw : NoWriteBefore body i s)
    (hf : ∀ q ∈ body, ∀ x, aliasDst q = some x → f x = f s → x = s) :
    NoWriteBefore (body.map (renPole f)) i (f s) :=
  fun l hl => noWrite_ren (hw l hl) hf

theorem want_of_cellOut {K : Nat → Nat → Prop} {k : Nat} {b : Blob} {s : Nat} (h : CellOut K k b s) :
    Want K k b s := by
  rcases h with ⟨h1, -⟩ | ⟨j, -, hc, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr (List.mem_of_getElem? hc))

theorem cellOut_ren {K : Nat → Nat → Prop} {f : Nat → Nat} {k : Nat} {b : Blob} {fin : Termin} {s : Nat}
    (h : CellOut K k b s) (hf : ∀ q ∈ b.body, ∀ x, aliasDst q = some x → f x = f s → x = s) :
    CellOut (fun l s' => ∃ s0, K l s0 ∧ f s0 = s') k ⟨b.par.map f, b.body.map (renPole f), fin⟩ (f s) := by
  rcases h with ⟨h1, h2⟩ | ⟨j, hj, hc, hw⟩
  · refine Or.inl ⟨⟨s, h1, rfl⟩, ?_⟩
    show NoWriteBefore (b.body.map (renPole f)) (b.body.map (renPole f)).length (f s)
    rw [List.length_map]; exact nwb_ren h2 hf
  · refine Or.inr ⟨j, by simpa using hj, by show (b.body.map (renPole f))[j]? = _; rw [List.getElem?_map, hc]; rfl,
      fun l h1 h2 => noWrite_ren (hw l h1 (by simpa using h2)) hf⟩

/-- **The renaming path keeps the cell annotation**, renamed with the
registers. -/
theorem celAnn_rename {bs new : Map Blob} {K : Nat → Nat → Prop} {f : Nat → Nat} (hB : BlocksOKA bs K)
    (hf : RenA bs K f) (h : renameBlocks bs f = some new) :
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
      fun hc => (hf k b hb s0 (want_of_cellOut hc)).1
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

/-! ## The start block -/

theorem get_start {bl : Map Blob} {o : Nat} {start : Blob} {k : Nat} {b : Blob}
    (hb : HoonMap.get (HoonMap.put (HoonMap.del bl o) 0 start) k = some b) :
    (k = 0 ∧ b = start) ∨ HoonMap.get bl k = some b := by
  rw [HoonMap.get_put] at hb
  split at hb
  · rename_i e; cases hb; exact Or.inl ⟨e, rfl⟩
  · rw [HoonMap.get_del] at hb
    split at hb
    · cases hb
    · exact Or.inr hb

/-- **Moving the unannotated start block to `0` keeps `BlocksOKA`.** -/
theorem blocksOKA_start {bl : Map Blob} {K : Nat → Nat → Prop} {o : Nat} {start : Blob} (hB : BlocksOKA bl K)
    (ho : ∀ s, ¬ K o s) (hst : HoonMap.get bl o = some start) :
    BlocksOKA (HoonMap.put (HoonMap.del bl o) 0 start) K where
  noNone := fun k b hb => by
    rcases get_start hb with ⟨-, rfl⟩ | hb
    · exact hB.noNone o _ hst
    · exact hB.noNone k b hb
  par := fun k b s hb hk => by
    rcases get_start hb with ⟨rfl, -⟩ | hb
    · exact absurd hk (hB.zero s)
    · exact hB.par k b s hb hk
  zero := hB.zero
  edge := fun k b j s hb hj hk => by
    rcases get_start hb with ⟨rfl, rfl⟩ | hb
    · rcases hB.edge o _ j s hst hj hk with h | ⟨h1, -⟩ | h
      · exact Or.inl h
      · exact absurd h1 (ho s)
      · exact Or.inr (Or.inr h)
    · exact hB.edge k b j s hb hj hk
  split := fun k b hb i p s hp hs => by
    rcases get_start hb with ⟨rfl, rfl⟩ | hb
    · rcases hB.split o _ hst i p s hp hs with h | ⟨h1, -⟩
      · exact Or.inl h
      · exact absurd h1 (ho s)
    · exact hB.split k b hb i p s hp hs

/-! ## The proxy facts -/

/-- **The proxy facts of a state** (no annotation named). -/
structure ProxOK (bl : Map Blob) (cond : Map (Nat × List Nat)) : Prop where
  wr : ∀ k b, HoonMap.get bl k = some b → ∀ x, (x ∈ b.par ∨ ∃ q ∈ b.body, aliasDst q = some x) →
    HoonMap.get cond x = Option.none
  cel : ∀ k b, HoonMap.get bl k = some b → ∀ (i : Nat) (p : Pole) (s : Nat), b.body[i]? = some p → splitReg p = some s →
    HoonMap.get cond s ≠ Option.none → ∃ j : Nat, j < i ∧ b.body[j]? = some (Pole.cel s)
  src : ∀ k b, HoonMap.get bl k = some b → ∀ s v, HoonMap.get cond s = some v →
    ((∃ p ∈ b.body, splitReg p = some s) ∨ Pole.cel s ∈ b.body) →
    v.1 ∉ b.par ∧ ∀ q ∈ b.body, aliasDst q ≠ some v.1

theorem proxOK_start {bl : Map Blob} {cond : Map (Nat × List Nat)} {o : Nat} {start : Blob} (hP : ProxOK bl cond)
    (hst : HoonMap.get bl o = some start) : ProxOK (HoonMap.put (HoonMap.del bl o) 0 start) cond where
  wr := fun k b hb => by
    rcases get_start hb with ⟨-, rfl⟩ | hb
    · exact hP.wr o _ hst
    · exact hP.wr k b hb
  cel := fun k b hb => by
    rcases get_start hb with ⟨-, rfl⟩ | hb
    · exact hP.cel o _ hst
    · exact hP.cel k b hb
  src := fun k b hb => by
    rcases get_start hb with ⟨-, rfl⟩ | hb
    · exact hP.src o _ hst
    · exact hP.src k b hb

/-- **The annotation restricted to registers that are no keys of `cond`.** -/
theorem blocksOKA_np {bl : Map Blob} {cond : Map (Nat × List Nat)} {K : Nat → Nat → Prop} (hB : BlocksOKA bl K)
    (hP : ProxOK bl cond) : BlocksOKA bl (fun l s => K l s ∧ HoonMap.get cond s = Option.none) where
  noNone := hB.noNone
  par := fun o b s hb hk => hB.par o b s hb hk.1
  zero := fun s hk => hB.zero s hk.1
  edge := fun o b j s hb hj hk => by
    rcases hB.edge o b j s hb hj hk.1 with h | ⟨h1, h2⟩ | h3
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨⟨h1, hk.2⟩, h2⟩)
    · exact Or.inr (Or.inr h3)
  split := fun o b hb i p s hp hs => by
    by_cases hc : HoonMap.get cond s = Option.none
    · rcases hB.split o b hb i p s hp hs with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨h1, hc⟩, h2⟩
    · obtain ⟨j, hj, hcj⟩ := hP.cel o b hb i p s hp hs hc
      refine Or.inl ⟨j, hj, hcj, fun l _ _ q hq e => hc ?_⟩
      exact hP.wr o b hb s (Or.inr ⟨q, List.mem_of_getElem? hq, e⟩)

theorem unproxy_self {cond : Map (Nat × List Nat)} {x : Nat} (h : HoonMap.get cond x = Option.none) :
    unproxy cond x = x := by
  simp [unproxy, h]

/-- **`ProxOK` gives the renaming condition for `renReg ∘ unproxy`.** -/
theorem renA_prox {bl : Map Blob} {cond : Map (Nat × List Nat)} {K : Nat → Nat → Prop} (hP : ProxOK bl cond)
    (r0 n : Nat) :
    RenA bl (fun l s => K l s ∧ HoonMap.get cond s = Option.none) (proxRen cond (hasProxies cond) (renReg r0 n)) := by
  have key : ∀ k b, HoonMap.get bl k = some b → ∀ s x, Want (fun l s => K l s ∧ HoonMap.get cond s = Option.none) k b s →
      (x ∈ b.par ∨ ∃ q ∈ b.body, aliasDst q = some x) →
      proxRen cond (hasProxies cond) (renReg r0 n) x = proxRen cond (hasProxies cond) (renReg r0 n) s → x = s := by
    intro k b hb s x hW hx e
    simp only [proxRen] at e
    have ex := renReg_inj r0 n _ _ e
    have hxn := hP.wr k b hb x hx
    cases hp : hasProxies cond
    · simpa [hp] using ex
    · simp only [hp, if_true, unproxy_self hxn] at ex
      cases hs : HoonMap.get cond s with
      | none => rw [unproxy_self hs] at ex; exact ex
      | some v =>
        have hu : unproxy cond s = v.1 := by simp [unproxy, hs]
        rw [hu] at ex
        subst ex
        exfalso
        rcases hW with ⟨-, hn⟩ | hW
        · rw [hs] at hn; cases hn
        · obtain ⟨h1, h2⟩ := hP.src k b hb s v hs hW
          rcases hx with hx | ⟨q, hq, hq'⟩
          · exact h1 hx
          · exact h2 q hq hq'
  intro k b hb s hW
  exact ⟨fun q hq x hx e => key k b hb s x hW (Or.inr ⟨q, hq, hx⟩) e,
    fun p hp e => key k b hb s p hW (Or.inl hp) e⟩

/-! ## `StraightA` -/

/-- **The proxy facts at the end** (named hypothesis): the state the top
`+kerf` leaves on a nomm with no `%6` meets `ProxOK`. -/
def ProxEnd (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]
    (env : CallEnv) : Prop :=
  ∀ nm, NoSixC nm → ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) →
    kerf nex g1 = some ((o, sub), g2) → ProxOK g2.blocks g2.cond

/-- **`StraightA` from the proxy facts at the end.** -/
theorem straightA_of {env : CallEnv} (hP : ProxEnd S Map env) : StraightA S Map env := by
  intro nm hn nex g1 g2 o sub c K h1 h2 hI hfo h
  have P := hP nm hn nex g1 g2 o sub h1 h2
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at h
  simp only [flattenNeed, List.headD, List.length] at h
  obtain ⟨start, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  have P0 := proxOK_start P hst
  have B1 := blocksOKA_np (blocksOKA_start hI.ok hfo.2 hst) P0
  have R := celAnn_rename B1 (renA_prox P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`GuardMonoC` on code with calls and no `%6`** from `KIMid` (track D)
and the proxy facts at the end `ProxEnd`. -/
theorem guardMonoC_noSixP (hD : ∀ env, KIMid S Map env) (hP : ∀ env, ProxEnd S Map env) :
    GuardMonoC S Map NoSixM :=
  guardMonoC_noSix hD fun env => straightA_of (hP env)

/-- **`EntryMono` on code with calls and no `%6`** from track D's two leaves,
`KIMid` and `ProxEnd`. -/
theorem entryMono_noSixP (lib : Lib) (hO : OptInMono S Map NoSixM) (hR : ReadsInMono S Map NoSixM)
    (hD : ∀ env, KIMid S Map env) (hP : ∀ env, ProxEnd S Map env) : EntryMono S Map lib NoSixM :=
  entryMono_of lib hO hR (guardMonoC_noSixP hD hP)

end Glue
end SkaModel
end Formalization
