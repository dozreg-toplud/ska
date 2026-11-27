import lemmas.Compiler.OptLinkAlStartImms
import lemmas.Compiler.OptLinkAlNounsStart

/-!
# `+alias`: the edges into a block (phase 12 of the plan, README Gaps 13, first part)

```hoon
    =/  edges=(list [p=@uwoo args=(list (unit @uvre))])
      %-  zing
      %+  turn  pre
      |=  p=@uwoo
      %+  murn  (get-jmps fin:(~(got by new.gen) p))
      |=  j=jmp
      ?.  =(there.j o)  ~
      `[p args.j]
```

The subject is `[bob [imms [info [pre S]]]]` with `S` the walk's subject
`alWS` (`alPS`).

* `edgeN`: the noun `[p args]` of an edge.
* `murn_gate_T`, `turn_gate_rel`, `turn_gate_some`: `+murn` and `+turn` on
  typed lists (a gate given per element; for `+turn`, a relation between the
  product and the model's value).
* `al_edm`: the gate of the `+murn` (`alEdM`).
* `al_edt`: the gate of the `+turn` (`alEdT`): `+got:by` on `new.gen`,
  `+get-jmps`, the `+murn`; it needs `NoLti` of `g.new` (`+get-jmps` of a
  `%lti` is not the model's).
* `al_edges`: **`edges` is the noun of `aliasEdges g o pre`**, on the Hoon's
  `pre`, a crash where the model is `none`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of an edge `[p args]`. -/
def edgeN (e : Nat × List (Option Nat)) : Noun := C (A e.1) (listNoun (unitNoun A) e.2)

/-- The subject of phase 12: `[bob [imms [info [pre S]]]]`. -/
def alPS (BOB IMMS INF PRE GEN NA BL REV TOPO : Noun) : Noun :=
  C BOB (C IMMS (C INF (C PRE (alWS GEN NA BL REV TOPO))))

/-! ## `+murn` and `+turn` on typed lists -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp), filterMap_congr' l (fun x hx => h x (by simp [hx]))]

theorem mapM_nock_fun {α β : Type} (E : α → Noun) (F : β → Noun) (bp bc : Noun) (G : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, nock (C bp (C (E a) bc)) bp = (G a).map F) →
      (l.map E).mapM (fun x => nock (C bp (C x bc)) bp) = (l.mapM G).map fun r => r.map F
  | [], _ => rfl
  | a :: l, hf => by
    have ih := mapM_nock_fun E F bp bc G l (fun x hx => hf x (by simp [hx]))
    simp only [List.map_cons, List.mapM_cons, hf a (by simp), ih]
    cases G a <;> cases l.mapM G <;> rfl

/-- `+turn` over the nouns `E a` with a gate that is `G a` encoded by `F`. -/
theorem turn_gate_T {α β : Type} (E : α → Noun) (F : β → Noun) (c : Noun) (hc : HomoIn c)
    (bp bs bc : Noun) (G : α → Option β) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = (G a).map F) :
    nock (C turn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) turn.battery
      = (l.mapM G).map fun r => listN (r.map F) := by
  rw [turn_gate_mapM c hc bp bs bc (fun x => nock (C bp (C x bc)) bp) (l.map E) (fun _ _ => rfl),
    mapM_nock_fun E F bp bc G l hf]
  cases l.mapM G <;> rfl

theorem unitVal_unitNoun_id (o : Option Noun) : unitVal (unitNoun id o) = o := by
  cases o <;> rfl

/-- **`+murn`** with a gate that makes the unit of `fu a` from each element `a`. -/
theorem murn_gate_T {α : Type} (E : α → Noun) (c : Noun) (hc : HomoIn c) (bp bs bc : Noun)
    (fu : α → Option Noun) (l : List α) (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (unitNoun id (fu a))) :
    nock (C murn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) murn.battery
      = some (listN (l.filterMap fu)) := by
  rw [murn_gate c hc bp bs bc (fun x => (nock (C bp (C x bc)) bp).getD (A 0)) (l.map E) (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rw [hf a ha]
    refine ⟨rfl, ?_⟩
    cases fu a with
    | none => exact Or.inl rfl
    | some v => exact Or.inr ⟨_, _, rfl⟩)]
  rw [List.filterMap_map]
  congr 2
  apply filterMap_congr' _
  intro a ha
  simp only [Function.comp, hf a ha, Option.getD_some, unitVal_unitNoun_id]

theorem mapM_some_eq {α β : Type} (f : α → β) : ∀ l : List α, l.mapM (fun a => some (f a)) = some (l.map f)
  | [] => rfl
  | a :: l => by simp only [List.mapM_cons, mapM_some_eq f l]; rfl

/-- **`+turn`** with a gate that maps every element `a` to `f a`. -/
theorem turn_gate_some {α β : Type} (E : α → Noun) (F : β → Noun) (c : Noun) (hc : HomoIn c)
    (bp bs bc : Noun) (f : α → β) (l : List α) (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (F (f a))) :
    nock (C turn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) turn.battery
      = some (listN ((l.map f).map F)) := by
  rw [turn_gate_T E F c hc bp bs bc (fun a => some (f a)) l (fun a ha => by rw [hf a ha]; rfl), mapM_some_eq]
  rfl

theorem mapM_nock_rel {α β : Type} (E : α → Noun) (R : Noun → β → Prop) (G : α → Option β)
    (bp bc : Noun) :
    ∀ (l : List α) (bs : List β), l.mapM G = some bs →
      (∀ a ∈ l, ∀ b, G a = some b → ∃ N, nock (C bp (C (E a) bc)) bp = some N ∧ R N b) →
      ∃ L : List (Noun × β), (∀ p ∈ L, R p.1 p.2) ∧ L.map Prod.snd = bs ∧
        (l.map E).mapM (fun x => nock (C bp (C x bc)) bp) = some (L.map Prod.fst)
  | [], bs, hm, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
    subst hm
    exact ⟨[], by simp, rfl, rfl⟩
  | a :: l, bs, hm, hf => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at hm
    cases ea : G a with
    | none => rw [ea] at hm; cases hm
    | some b =>
      rw [ea] at hm
      cases el : l.mapM G with
      | none => rw [el] at hm; cases hm
      | some bs' =>
        rw [el] at hm
        simp only [Option.bind_some, Option.some.injEq] at hm
        subst hm
        obtain ⟨N, hN, hR⟩ := hf a (by simp) b ea
        obtain ⟨L, hL, h2, h3⟩ := mapM_nock_rel E R G bp bc l bs' el (fun a' ha' => hf a' (by simp [ha']))
        refine ⟨(N, b) :: L, ?_, by simp [h2], ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hR
          · exact hL p hp
        · simp [List.mapM_cons, hN, h3]

/-- **`+turn`** with a gate whose product on `a` is related to `G a` where the
model returns: the list of products is related to the model's list. -/
theorem turn_gate_rel {α β : Type} (E : α → Noun) (R : Noun → β → Prop) (G : α → Option β) (c : Noun)
    (hc : HomoIn c) (bp bs bc : Noun) (l : List α) (r : List β) (hm : l.mapM G = some r)
    (hf : ∀ a ∈ l, ∀ b, G a = some b → ∃ N, nock (C bp (C (E a) bc)) bp = some N ∧ R N b) :
    ∃ L : List (Noun × β), (∀ p ∈ L, R p.1 p.2) ∧ L.map Prod.snd = r ∧
      nock (C turn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) turn.battery
        = some (listN (L.map Prod.fst)) := by
  obtain ⟨L, h1, h2, h3⟩ := mapM_nock_rel E R G bp bc l r hm hf
  refine ⟨L, h1, h2, ?_⟩
  rw [turn_gate_mapM c hc bp bs bc (fun x => nock (C bp (C x bc)) bp) (l.map E) (fun _ _ => rfl), h3]
  rfl

/-! ## The gates of `edges` -/

/-- The model's edges of one predecessor `p` into `o`. -/
def edgesOf (o p : Nat) (pb : Blob) : List (Nat × List (Option Nat)) :=
  (Opt.getJmps pb.fin).filterMap fun j => if j.there = o then some (p, j.args) else none

/-- **The gate of the `+murn`**: `?.  =(there.j o)  ~  `[p args.j]`. -/
theorem al_edm (j : Jmp) (p o : Nat) (BOB IMMS INF PRE GEN NA BL REV T : Noun) :
    nock (C alEdM (C j.toNoun (C alEdT (C (A p) (alPS BOB IMMS INF PRE GEN NA BL REV (C (A o) T)))))) alEdM
      = some (unitNoun id (if j.there = o then some (edgeN (p, j.args)) else none)) := by
  unfold alPS alWS
  by_cases e : j.there = o
  · subst e
    simp [nock_exec, alEdM, Jmp.toNoun, eqCode, edgeN, unitNoun]
  · have e' : ¬ A j.there = A o := fun h => e (Noun.atom.inj h)
    simp [nock_exec, alEdM, Jmp.toNoun, eqCode, edgeN, unitNoun, e, e']

theorem finPlain_of_noLti {bl : TreapMap mugF Blob} (h : Opt.NoLti bl) {p : Nat} {b : Blob}
    (hb : HoonMap.get bl p = some b) : finPlain b.fin = true := by
  have := h p b hb
  cases e : b.fin with
  | lti n s z o' => exact absurd e (this n s z o')
  | _ => rfl

/-- The arm `+murn` of `layer2` gives its gate. -/
theorem murn_arm' (c : Noun) :
    nock c murn.arm = some (C murn.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) c)) := by
  nock_open murn.arm; simp only [nock_exec]

/-- The arm `+zing` of `layer2` gives its gate. -/
theorem zing_arm' (c : Noun) : nock c zing.arm = some (C zing.battery (C (A 0) c)) := by
  nock_open zing.arm; simp only [nock_exec]

/-- **The gate of the `+turn`** over `pre`: the edges of `p` into `o`
(`+got:by` on `new.gen`, `+get-jmps`, the `+murn`); a crash where `p` has no
block in `new.gen`. -/
theorem al_edt (g : Opt.AGen (TreapMap mugF)) (hn : Opt.NoLti g.new) (p o : Nat)
    (BOB IMMS INF PRE OLD INFO IMMSg LOC IMML RV F NA BL REV T : Noun) :
    nock (C alEdT (C (A p) (alPS BOB IMMS INF PRE
        (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMSg LOC IMML RV F) NA BL REV (C (A o) T)))) alEdT
      = (HoonMap.get g.new p).map fun pb => listNoun edgeN (edgesOf o p pb) := by
  have hgot := blocks_got g.new p
  have hL := optC_layer2
  have hT := optC_types
  have hgja := gj_at
  cases eb : HoonMap.get g.new p with
  | none =>
    rw [eb] at hgot
    unfold alPS alWS genN
    generalize optC = OC at hL hT
    generalize HoonMap.toNoun Blob.toNoun g.new = NEW at hgot
    simp [nock_exec, alEdT, hL, hT, murn.arm_at, murn_arm', hgja, gj_arm, by.arm_at, by_arm, by.got.arm_at,
      got_arm, hgot]
  | some pb =>
    rw [eb] at hgot
    have hgj := gj_gate compTypes pb.fin (finPlain_of_noLti hn eb)
    rw [listNoun_map_listN] at hgj
    have hm := murn_gate_T Jmp.toNoun layer2 homoIn_layer2 alEdM (C (A 0) (A 0))
      (C alEdT (C (A p) (alPS BOB IMMS INF PRE
        (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMSg LOC IMML RV F) NA BL REV (C (A o) T))))
      (fun j => if j.there = o then some (edgeN (p, j.args)) else none) (Opt.getJmps pb.fin)
      (fun j _ => al_edm j p o BOB IMMS INF PRE _ NA BL REV T)
    have hfm : ((Opt.getJmps pb.fin).filterMap fun j => if j.there = o then some (edgeN (p, j.args)) else none)
        = (edgesOf o p pb).map edgeN := by
      unfold edgesOf
      rw [List.map_filterMap]
      apply filterMap_congr' _
      intro j _
      by_cases e : j.there = o <;> simp [e]
    rw [hfm] at hm
    rw [Option.map_some, listNoun_map_listN]
    unfold alPS alWS genN at hm ⊢
    generalize optC = OC at hL hT hm
    generalize HoonMap.toNoun Blob.toNoun g.new = NEW at hgot hm
    simp only [Option.map_some] at hgot
    nock_open alEdT
    simp [nock_exec, hL, hT, murn.arm_at, murn_arm', hgja, gj_arm, by.arm_at, by_arm, by.got.arm_at,
      got_arm, hgot, Blob.toNoun, hgj, hm]

/-- **`edges`**: the noun of the model's `aliasEdges g o pre`, on the Hoon's
`pre`; a crash where the model is `none`. -/
theorem al_edges (g : Opt.AGen (TreapMap mugF)) (hn : Opt.NoLti g.new) (o : Nat) (pre : List Nat)
    (BOB IMMS INF OLD INFO IMMSg LOC IMML RV F NA BL REV T : Noun) :
    nock (alPS BOB IMMS INF (listNoun A pre)
        (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMSg LOC IMML RV F) NA BL REV (C (A o) T)) alEdgesC
      = (Opt.aliasEdges g o pre).map (listNoun edgeN) := by
  have ht := turn_gate_T A (listNoun edgeN) layer2 homoIn_layer2 alEdT (A 0)
    (alPS BOB IMMS INF (listNoun A pre)
        (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMSg LOC IMML RV F) NA BL REV (C (A o) T))
    (fun p => (HoonMap.get g.new p).map fun pb => edgesOf o p pb) pre
    (fun p _ => by rw [al_edt g hn p o]; cases HoonMap.get g.new p <;> rfl)
  have hL := optC_layer2
  unfold Opt.aliasEdges
  simp only [← listNoun_map_listN] at ht
  cases em : pre.mapM (fun p => (HoonMap.get g.new p).map fun pb => edgesOf o p pb) with
  | none =>
    rw [em] at ht
    have em' : (pre.mapM fun p => (HoonMap.get g.new p).map fun pb =>
        (Opt.getJmps pb.fin).filterMap fun j => if j.there = o then some (p, j.args) else none) = none := em
    rw [em']
    unfold alPS alWS at ht ⊢
    generalize optC = OC at hL ht
    simp [nock_exec, alEdgesC, hL, zing.arm_at, zing_arm', turn.arm_at, turn_arm, ht]
  | some r =>
    rw [em] at ht
    have em' : (pre.mapM fun p => (HoonMap.get g.new p).map fun pb =>
        (Opt.getJmps pb.fin).filterMap fun j => if j.there = o then some (p, j.args) else none) = some r := em
    rw [em']
    have hz := zing_gate layer2 welp.arm_at (r.map (List.map edgeN))
    have e1 : (r.map (List.map edgeN)).map listN = r.map (listNoun edgeN) := by
      rw [List.map_map]; apply List.map_congr_left; intro x _; exact (listNoun_map_listN edgeN x).symm
    have e2 : listN (r.map (List.map edgeN)).flatten = listNoun edgeN r.flatten := by
      rw [listNoun_map_listN, List.map_flatten]
    rw [e1, e2] at hz
    simp only [← listNoun_map_listN] at hz
    simp only [Option.map_some] at ht ⊢
    unfold alPS alWS at ht ⊢
    generalize optC = OC at hL ht
    simp [nock_exec, alEdgesC, hL, zing.arm_at, zing_arm', turn.arm_at, turn_arm, ht, hz]

end Compiler
end Formalization
