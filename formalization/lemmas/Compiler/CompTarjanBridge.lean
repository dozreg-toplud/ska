import lemmas.Compiler.CompTarjanJug
import lemmas.Ska.TarjanSound
import lemmas.Compiler.PokeLinkGood5
import lemmas.Compiler.CompInlinedL5
import lemmas.Compiler.SkaArms

/-!
# From `TjSpec` on the jug of `+ska-poke` to track P's `TarjanSpec` (track Q)

The model half of the leaf `SccsLeafAt` (`PokeLinkLoop.lean`) and track P's
`TarjanExists` (`PokeLinkGood5.lean`):

* `preorder_keys_nodupC`, `finMap_rap_nodup`: the keys of the pre-order of
  an `IsMap` noun, and of `FinMap.rap`, are distinct;
* the graph `tjGraph (jugNoun nc)` of the jug push 8 builds
  (`CompTarjanJug.lean`): distinct keys (`jugGr_keys_nodup`), nonempty on a
  nonempty table (`jugGr_ne`), its kids are the `Edge`s of `nc`
  (`mem_kidsOf_jug`), its vertices the encoded keys (`mem_tjVerts_jug`),
  its reachability track P's `Reach` (`tjReach_jug`);
* `compSet l`: the set of the bells a list of nouns holds; on a component
  of a `TjSpec` list it is `sccSet nc b` of each member (`compSet_scc`);
* **`tarjanSpec_of_tj`**: `TjSpec` of the jug graph, flopped and read as
  sets, is `TarjanSpec nc`;
* **`tarjanSpecN_of`**: the list noun of the set nouns of a `TjSpec` list
  (`TjFinIs`), flopped, is `TarjanSpecN nc`; `tarjanSpecN_empty`: `~` on an
  empty table;
* **`tarjanExists`**: track P's `TarjanExists`;
* **`inlinedM_returns_ex`**: `inlinedM_returns` with its `TarjanSpecP`
  hypothesis discharged.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Glue SkaModel.Ana SkaModel.Bake SkaModel.PokeF Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Distinct keys -/

/-- The key of a pair noun. -/
def pairKey : Noun → Noun
  | Noun.cell k _ => k
  | x => x

theorem mem_map_pairKey {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) (k : Noun) :
    k ∈ (preorder a).map pairKey ↔ ∃ v, Get a k v := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k', v, rfl, hg⟩ := (mem_preorder h x).1 hx
    exact ⟨v, hg⟩
  · rintro ⟨v, hv⟩
    exact ⟨C k v, (mem_preorder h _).2 ⟨k, v, rfl, hv⟩, rfl⟩

/-- **The keys of the pre-order of a map are distinct.** -/
theorem preorder_keys_nodupC {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) :
    ((preorder a).map pairKey).Nodup := by
  induction h with
  | nil => simp [preorder]
  | @node p q l r hl hr hL hR ihl ihr =>
    have hl' : IsMap mug l := hl
    have hr' : IsMap mug r := hr
    rw [preorder_node, List.map_cons, List.map_append, List.nodup_cons, List.nodup_append]
    refine ⟨?_, ihl, ihr, ?_⟩
    · intro hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨v, hv⟩ := (mem_map_pairKey hl' p).1 hp
        exact (hL p v hv).1 rfl
      · obtain ⟨v, hv⟩ := (mem_map_pairKey hr' p).1 hp
        exact (hR p v hv).1 rfl
    · intro k hk k' hk' e
      subst e
      obtain ⟨v, hv⟩ := (mem_map_pairKey hl' k).1 hk
      obtain ⟨v', hv'⟩ := (mem_map_pairKey hr' k).1 hk'
      exact (hL k v hv).1 (gorF_antisymm mug (hL k v hv).2.1 (hR k v' hv').2.1)

/-- **The keys of `FinMap.rap` are distinct.** -/
theorem finMap_rap_nodup {κ ν : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ ν) : ((FinMap.rap m).map Prod.fst).Nodup := by
  have h := preorder_keys_nodupC (FinMap.isMap_toNoun (fun _ => A 0) m)
  rw [FinMap.preorder_toNoun, List.map_map] at h
  have e : (pairKey ∘ fun e : κ × ν => C (TKey.enc e.1) (A 0)) = TKey.enc ∘ Prod.fst := by
    funext e; rfl
  rw [e, ← List.map_map] at h
  exact List.Pairwise.of_map TKey.enc (fun a b h e => h (congrArg TKey.enc e)) h

/-! ## The jug graph -/

section Jug

variable (nc : FinMap Bell (VarEntry FinMap))

theorem jugGr_eq : tjGraph (jugNoun nc) =
    (FinMap.rap (jugOf nc)).map fun e => (TKey.enc e.1, preorder (FinMap.setNoun e.2)) := by
  unfold tjGraph jugNoun
  rw [FinMap.preorder_toNoun, List.map_map]
  rfl

theorem jugGr_keys_nodup : ((tjGraph (jugNoun nc)).map Prod.fst).Nodup := by
  rw [jugGr_eq, List.map_map]
  have e : (Prod.fst ∘ fun e : Bell × FinMap Bell Unit => (TKey.enc e.1, preorder (FinMap.setNoun e.2))) =
      TKey.enc ∘ Prod.fst := by funext e; rfl
  rw [e, ← List.map_map]
  exact List.Pairwise.map TKey.enc (fun a b h e => h (TKey.enc_inj a b e)) (finMap_rap_nodup (jugOf nc))

theorem mem_jugGr (p : Noun × List Noun) :
    p ∈ tjGraph (jugNoun nc) ↔ ∃ b e, FinMap.get nc b = some e ∧
      p = (TKey.enc b, preorder (FinMap.setNoun (keysIn nc e.calls))) := by
  rw [jugGr_eq, List.mem_map]
  constructor
  · rintro ⟨⟨b, S⟩, hm, rfl⟩
    have h := (FinMap.mem_rap (jugOf nc) b S).1 hm
    have h' : FinMap.get (jugOf nc) b = some S := h
    rw [jugOf_get] at h'
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h'
    exact ⟨b, e, he, rfl⟩
  · rintro ⟨b, e, he, rfl⟩
    refine ⟨(b, keysIn nc e.calls), (FinMap.mem_rap (jugOf nc) b _).2 ?_, rfl⟩
    show FinMap.get (jugOf nc) b = _
    rw [jugOf_get, he]; rfl

theorem jugGr_ne {b : Bell} {e : VarEntry FinMap} (h : FinMap.get nc b = some e) : tjGraph (jugNoun nc) ≠ [] := by
  intro h0
  have := (mem_jugGr nc _).2 ⟨b, e, h, rfl⟩
  rw [h0] at this; cases this

theorem kidsOf_none {G : Gr Noun} {x : Noun} (h : ∀ p ∈ G, p.1 ≠ x) : Tarjan.kidsOf G x = [] := by
  unfold Tarjan.kidsOf
  rw [List.find?_eq_none.2]
  intro p hp
  simpa using h p hp

/-- **The kids of the jug graph are the `Edge`s of `nc`.** -/
theorem mem_kidsOf_jug (x c : Noun) :
    c ∈ Tarjan.kidsOf (tjGraph (jugNoun nc)) x ↔ ∃ b c', x = TKey.enc b ∧ c = TKey.enc c' ∧ Edge nc b c' := by
  by_cases hx : ∃ b e, FinMap.get nc b = some e ∧ x = TKey.enc b
  · obtain ⟨b, e, he, rfl⟩ := hx
    rw [Tarjan.kidsOf_key (jugGr_keys_nodup nc) _ ((mem_jugGr nc _).2 ⟨b, e, he, rfl⟩)]
    simp only
    rw [mem_preorder_setNoun]
    constructor
    · rintro ⟨c', hc', rfl⟩
      obtain ⟨h1, e', h2⟩ := (keysIn_get nc e.calls c').1 hc'
      exact ⟨b, c', rfl, rfl, e, he, h1, e', h2⟩
    · rintro ⟨b', c', hb, rfl, e1, he1, h1, e', h2⟩
      have := TKey.enc_inj _ _ hb; subst this
      rw [he] at he1; cases he1
      exact ⟨c', (keysIn_get nc e.calls c').2 ⟨h1, e', h2⟩, rfl⟩
  · rw [kidsOf_none]
    · simp only [List.not_mem_nil, false_iff]
      rintro ⟨b, c', rfl, -, e, he, -⟩
      exact hx ⟨b, e, he, rfl⟩
    · intro p hp e
      obtain ⟨b, e', he', rfl⟩ := (mem_jugGr nc p).1 hp
      exact hx ⟨b, e', he', e.symm⟩

/-- **The vertices of the jug graph are the encoded keys.** -/
theorem mem_tjVerts_jug (u : Noun) :
    u ∈ tjVerts (tjGraph (jugNoun nc)) ↔ ∃ b e, FinMap.get nc b = some e ∧ u = TKey.enc b := by
  rw [Tarjan.mem_tjVerts]
  constructor
  · rintro ⟨p, hp, hu | hu⟩
    · obtain ⟨b, e, he, rfl⟩ := (mem_jugGr nc p).1 hp
      exact ⟨b, e, he, hu⟩
    · have hk := Tarjan.kidsOf_key (jugGr_keys_nodup nc) p hp
      rw [← hk] at hu
      obtain ⟨-, c', -, rfl, -, -, -, e', he'⟩ := (mem_kidsOf_jug nc _ _).1 hu
      exact ⟨c', e', he', rfl⟩
  · rintro ⟨b, e, he, rfl⟩
    exact ⟨_, (mem_jugGr nc _).2 ⟨b, e, he, rfl⟩, Or.inl rfl⟩

/-- **Reachability in the jug graph is track P's `Reach`.** -/
theorem tjReach_jug (b c : Bell) :
    TjReach (tjGraph (jugNoun nc)) (TKey.enc b) (TKey.enc c) ↔ Reach nc b c := by
  constructor
  · intro h
    suffices H : ∀ a z, TjReach (tjGraph (jugNoun nc)) a z → ∀ b c, a = TKey.enc b → z = TKey.enc c → Reach nc b c from
      H _ _ h b c rfl rfl
    intro a z h
    induction h with
    | refl a =>
      intro b c hb hc
      rw [hb] at hc
      rw [TKey.enc_inj _ _ hc]; exact Reach.refl c
    | step hk _ ih =>
      intro b c hb hc
      obtain ⟨b', c', hb', rfl, hE⟩ := (mem_kidsOf_jug nc _ _).1 hk
      rw [hb'] at hb
      have := TKey.enc_inj _ _ hb; subst this
      exact Reach.step hE (ih c' c rfl hc)
  · intro h
    induction h with
    | refl => exact TjReach.refl _
    | step hE _ ih => exact TjReach.step ((mem_kidsOf_jug nc _ _).2 ⟨_, _, rfl, rfl, hE⟩) ih

end Jug

/-! ## The components as sets -/

/-- The bells a list of nouns holds, as a set. -/
noncomputable def compSet (l : List Noun) : FinMap Bell Unit :=
  open Classical in
  ⟨fun c => if TKey.enc c ∈ l then some () else none, ⟨l.filterMap FinMap.decode?, fun c hc => by
    by_cases h : TKey.enc c ∈ l
    · exact List.mem_filterMap.2 ⟨_, h, FinMap.decode?_enc c⟩
    · simp [h] at hc⟩⟩

theorem compSet_get (l : List Noun) (c : Bell) : FinMap.get (compSet l) c = some () ↔ TKey.enc c ∈ l := by
  unfold compSet FinMap.get
  simp only
  split <;> simp_all

theorem mem_rap_compSet (l : List Noun) (c : Bell) :
    c ∈ (FinMap.rap (compSet l)).map Prod.fst ↔ TKey.enc c ∈ l := by
  rw [← compSet_get, List.mem_map]
  constructor
  · rintro ⟨⟨c', u⟩, hm, rfl⟩
    exact (FinMap.mem_rap _ c' u).1 hm
  · intro h
    exact ⟨(c, ()), (FinMap.mem_rap _ c ()).2 h, rfl⟩

theorem finMap_unit_ext {S S' : FinMap Bell Unit} (h : ∀ c, FinMap.get S c = some () ↔ FinMap.get S' c = some ()) :
    S = S' := by
  apply Subtype.ext
  funext c
  have hc := h c
  show FinMap.get S c = FinMap.get S' c
  cases e : FinMap.get S c with
  | none =>
    cases e' : FinMap.get S' c with
    | none => rfl
    | some u => rw [e, e'] at hc; exact absurd (hc.2 rfl) (by simp)
  | some u => rw [e] at hc; exact (hc.1 rfl).symm

section Spec

variable {nc : FinMap Bell (VarEntry FinMap)} {L : List (List Noun)}

theorem mem_flat_verts (h : TjSpec (tjGraph (jugNoun nc)) L) (u : Noun) :
    u ∈ L.flatten ↔ u ∈ tjVerts (tjGraph (jugNoun nc)) := by
  have hc := h.2.1 u
  constructor
  · intro hu
    have := List.count_pos_iff.2 hu
    split at hc
    · assumption
    · omega
  · intro hu
    rw [if_pos hu] at hc
    exact List.count_pos_iff.1 (by omega)

/-- On a component, `compSet` is the SCC of each member. -/
theorem compSet_scc (h : TjSpec (tjGraph (jugNoun nc)) L) {l : List Noun} (hl : l ∈ L) {b : Bell}
    (hb : TKey.enc b ∈ l) : compSet l = sccSet nc b := by
  apply finMap_unit_ext
  intro c
  rw [compSet_get]
  show _ ↔ (sccSet nc b).1 c = some ()
  rw [sccSet_get]
  rw [(h.1 l hl).2 _ hb]
  constructor
  · intro hc
    have hcl := ((h.1 l hl).2 _ hb _).2 hc
    obtain ⟨c', e', he', hc'⟩ := (mem_tjVerts_jug nc _).1
      ((mem_flat_verts h _).1 (List.mem_flatten.2 ⟨l, hl, hcl⟩))
    have := TKey.enc_inj _ _ hc'; subst this
    exact ⟨⟨e', he'⟩, (tjReach_jug nc b c).1 hc.1, (tjReach_jug nc c b).1 hc.2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨(tjReach_jug nc b c).2 h1, (tjReach_jug nc c b).2 h2⟩

/-- **`TjSpec` of the jug graph, flopped and read as sets, is `TarjanSpec`.** -/
theorem tarjanSpec_of_tj (h : TjSpec (tjGraph (jugNoun nc)) L) :
    TarjanSpec nc ((L.reverse.map compSet).map fun S => (FinMap.rap S).map Prod.fst) := by
  have hnd : L.flatten.Nodup := by
    rw [List.nodup_iff_count]
    intro u; rw [h.2.1 u]; split <;> omega
  have hdis := (List.pairwise_flatten.1 hnd).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    simp only [List.map_map, List.mem_map, List.mem_reverse, Function.comp] at hS
    obtain ⟨l, hl, rfl⟩ := hS
    obtain ⟨hne, -⟩ := h.1 l hl
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨b, e, he, rfl⟩ := (mem_tjVerts_jug nc _).1
      ((mem_flat_verts h _).1 (List.mem_flatten.2 ⟨_, hl, List.mem_cons_self⟩))
    refine ⟨b, ⟨e, he⟩, ?_⟩
    rw [compSet_scc h hl List.mem_cons_self]
    rfl
  · show List.Pairwise _ _
    rw [List.pairwise_flatten]
    refine ⟨fun S hS => ?_, ?_⟩
    · obtain ⟨S', -, rfl⟩ := List.mem_map.1 hS
      exact finMap_rap_nodup S'
    · rw [List.map_map, List.pairwise_map, List.pairwise_reverse]
      refine hdis.imp fun {l l'} hll' => ?_
      intro x hx y hy e
      subst e
      simp only [Function.comp] at hx hy
      exact hll' _ ((mem_rap_compSet l x).1 hy) _ ((mem_rap_compSet l' x).1 hx) rfl
  · intro b
    simp only [List.map_map, List.mem_flatten, List.mem_map, List.mem_reverse, Function.comp]
    constructor
    · rintro ⟨S, ⟨l, hl, rfl⟩, hb⟩
      obtain ⟨b', e, he, hb'⟩ := (mem_tjVerts_jug nc _).1
        ((mem_flat_verts h _).1 (List.mem_flatten.2 ⟨l, hl, (mem_rap_compSet l b).1 hb⟩))
      have := TKey.enc_inj _ _ hb'; subst this
      exact ⟨e, he⟩
    · rintro ⟨e, he⟩
      obtain ⟨l, hl, hbl⟩ := List.mem_flatten.1 ((mem_flat_verts h _).2 ((mem_tjVerts_jug nc _).2 ⟨b, e, he, rfl⟩))
      exact ⟨_, ⟨l, hl, rfl⟩, (mem_rap_compSet l b).2 hbl⟩
  · intro i j hij hi hj b hb c hc hE
    simp only [List.map_map, List.length_map, List.length_reverse] at hi hj
    simp only [List.map_map, List.getElem_map, Function.comp] at hb hc
    have hb' := (mem_rap_compSet _ b).1 hb
    have hc' := (mem_rap_compSet _ c).1 hc
    exact tjSpec_flop h i j hij (by simpa using hi) (by simpa using hj) _ hb' _ hc'
      ((mem_kidsOf_jug nc _ _).2 ⟨b, c, rfl, rfl, hE⟩)

theorem tjFinIs_forall {Ss : List Noun} : ∀ {L : List (List Noun)}, TjFinIs (listN Ss) L →
    Ss.length = L.length ∧ ∀ i (hi : i < Ss.length) (hj : i < L.length), TjSet Ss[i] (fun k => k ∈ L[i]) := by
  induction Ss with
  | nil =>
    intro L h
    cases L with
    | nil => exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
    | cons l ls => obtain ⟨S, REST, e, -⟩ := h; cases e
  | cons S Ss ih =>
    intro L h
    cases L with
    | nil => cases h
    | cons l ls =>
      obtain ⟨S', REST, e, hS, hR⟩ := h
      simp only [listN, appendN, Noun.cell.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨h1, h2⟩ := ih hR
      refine ⟨by simp [h1], fun i hi hj => ?_⟩
      cases i with
      | zero => exact hS
      | succ i => exact h2 i (by simpa using hi) (by simpa using hj)

theorem listN_map (Ls : List (FinMap Bell Unit)) : listN (Ls.map FinMap.setNoun) = listNoun FinMap.setNoun Ls := by
  induction Ls with
  | nil => rfl
  | cons S Ls ih => simp only [List.map_cons, listN, appendN, listNoun] at ih ⊢; rw [ih]

/-- **The list noun of a `TjSpec` list, flopped, is `TarjanSpecN`.** -/
theorem tarjanSpecN_of (h : TjSpec (tjGraph (jugNoun nc)) L) {Ss : List Noun} (hS : TjFinIs (listN Ss) L) :
    TarjanSpecN nc (listN Ss.reverse) := by
  obtain ⟨hlen, hset⟩ := tjFinIs_forall hS
  have hSs : Ss = L.map fun l => FinMap.setNoun (compSet l) := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hi'
    rw [List.getElem_map]
    have hj : i < L.length := by simpa using hi'
    have hl : L[i] ∈ L := List.getElem_mem hj
    refine isSet_ext (hset i hi hj).1 (FinMap.isSet_setNoun _) fun k => ?_
    rw [(hset i hi hj).2, FinMap.has_setNoun]
    constructor
    · intro hk
      obtain ⟨c, e, he, rfl⟩ := (mem_tjVerts_jug nc _).1 ((mem_flat_verts h _).1 (List.mem_flatten.2 ⟨_, hl, hk⟩))
      exact ⟨c, (compSet_get _ c).2 hk, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact (compSet_get _ c).1 hc
  refine ⟨L.reverse.map compSet, ?_, tarjanSpec_of_tj h⟩
  rw [← listN_map, hSs, List.map_reverse, List.map_reverse, List.map_map]
  rfl

/-- **On an empty table**, `~` is `TarjanSpecN`. -/
theorem tarjanSpecN_empty (h : ∀ b, FinMap.get nc b = none) : TarjanSpecN nc (A 0) := by
  refine ⟨[], rfl, ?_⟩
  unfold TarjanSpec
  refine ⟨?_, (by simp), ?_, ?_⟩
  · intro S hS; cases hS
  · intro b; simp [h b]
  · intro i j _ hi; simp at hi

end Spec

/-! ## `TarjanExists` and the fuel of `+inlined` -/

/-- **Track P's `TarjanExists`**: every table has a callees-first list of
its SCCs (`+tarjan`'s model on the table's jug graph, flopped). -/
theorem tarjanExists : TarjanExists := by
  intro nc
  by_cases hk : ∃ b e, FinMap.get nc b = some e
  · obtain ⟨b, e, he⟩ := hk
    obtain ⟨L, -, hL⟩ := tarjanM_spec (tjGraph (jugNoun nc)) (jugGr_ne nc he) (jugGr_keys_nodup nc)
    exact ⟨_, tarjanSpec_of_tj hL⟩
  · refine ⟨[], ?_⟩
    unfold TarjanSpec
    refine ⟨fun S hS => (by cases hS), (by simp), fun b => ?_, fun i j _ hi => (by simp at hi)⟩
    simp only [List.flatten_nil, List.not_mem_nil, false_iff]
    rintro ⟨e, he⟩
    exact hk ⟨b, e, he⟩

/-- **`inlinedM` returns on every key** of a closed table whose info bells
are calls, with no hypothesis on `+tarjan` (`inlinedM_returns` at a list of
`tarjanExists`). -/
theorem inlinedM_returns_ex {T : FinMap Bell (VarEntry FinMap)} {calls : Bell → Bell → Bool}
    {hot single : Bell → Bool} (hC : CodeClosed T) (hI : InfoCalls T)
    (hc : CallsOf T calls) (hs : SingleScc T single) :
    ∀ b e, FinMap.get T b = some e → ∃ f m, inlinedM (nmOf T) calls hot single f b = some m := by
  intro b e he
  obtain ⟨L, hL⟩ := tarjanExists T
  obtain ⟨m, hm⟩ := inlinedM_returns (hot := hot) hC hI (tarjanSpecP_of hL) hc hs b e he
  exact ⟨_, m, hm⟩

end Compiler
end Formalization
