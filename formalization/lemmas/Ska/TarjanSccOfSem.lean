import lemmas.Ska.TarjanSccOfTotal

/-!
# The miss of `+scc-of`: totality and what it writes (track Q)

On top of `TarjanSccOfTotal.lean` (`sub` is `SubIs`):

* the graph of `sub` (`scoMiss.tjGraphM`): distinct keys, nonempty, its
  vertices the nouns `ScoReach`able from `b` (`mem_tjVerts_sub`), and
  `TjReach` from such a noun is `ScoReach` (`tjReach_sub`);
* `scoRoll_spec`: the roll over disjoint sets;
* **`scoMiss_total`**: at the fuel `scoFuel`, the miss returns;
* **`scoMiss_spec`**: whenever the miss returns, it gives `[S sccs']` with
  `b ↦ S` in `sccs'`, and the pairs of `sccs'` are the old pairs on the nouns
  not reachable from `b`, and on each noun `m` reachable from `b` the set of
  the `x` with `ScoReach m x` and `ScoReach x m`;
* `scoMiss_keeps`: on a miss, every old pair stays.
-/

namespace Formalization
namespace Tarjan

open Nock Hoon

set_option linter.unusedSectionVars false

/-! ## The graph of `sub` -/

/-- An entry of the graph of a jug noun. -/
def scoEnt : Noun → Noun × List Noun
  | Noun.cell v ks => (v, preorder ks)
  | Noun.atom _ => (A 0, [])

theorem tjGraphM_eq (G : Noun) : scoMiss.tjGraphM G = (preorder G).map scoEnt := rfl

theorem sub_keys_nodup {SUB : Noun} (h : IsMap mugF SUB) : ((scoMiss.tjGraphM SUB).map Prod.fst).Nodup := by
  rw [tjGraphM_eq, List.map_map]
  exact preorder_keys_nodup h _ (fun k v => rfl)

theorem mem_subGraph {SUB : Noun} (h : IsMap mugF SUB) (p : Noun × List Noun) :
    p ∈ scoMiss.tjGraphM SUB ↔ ∃ k v, p = (k, preorder v) ∧ Get SUB k v := by
  rw [tjGraphM_eq, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, v, rfl, hg⟩ := (mem_preorder h x).1 hx
    exact ⟨k, v, rfl, hg⟩
  · rintro ⟨k, v, rfl, hg⟩
    exact ⟨C k v, (mem_preorder h _).2 ⟨k, v, rfl, hg⟩, rfl⟩

theorem kidsOf_sub_key {SUB k v : Noun} (h : IsMap mugF SUB) (hg : Get SUB k v) :
    kidsOf (scoMiss.tjGraphM SUB) k = preorder v :=
  kidsOf_key (sub_keys_nodup h) (k, preorder v) ((mem_subGraph h _).2 ⟨k, v, rfl, hg⟩)

theorem sub_ne_nil {CA SC B SUB : Noun} (hS : SubIs CA SC B SUB) : scoMiss.tjGraphM SUB ≠ [] := by
  obtain ⟨v, hv⟩ := (hS.keys B).2 (ScoReach.refl B)
  intro e
  have := (mem_subGraph hS.map (B, preorder v)).2 ⟨B, v, rfl, hv⟩
  rw [e] at this
  cases this

/-- **`TjReach` on the graph of `sub`, from a reachable noun, is `ScoReach`.** -/
theorem tjReach_sub {CA SC B SUB : Noun} (hS : SubIs CA SC B SUB) {x y : Noun} (hx : ScoReach CA SC B x) :
    TjReach (scoMiss.tjGraphM SUB) x y ↔ ScoReach CA SC x y := by
  constructor
  · intro h
    revert hx
    induction h with
    | refl => intro _; exact ScoReach.refl _
    | @step a b c e _ ih =>
      intro hx
      obtain ⟨v, hv⟩ := (hS.keys a).2 hx
      rw [kidsOf_sub_key hS.map hv] at e
      have hk : ScoKids CA SC a b := ((hS.val a v hv).2 b).1 ((mem_preorder_set (hS.val a v hv).1 b).1 e)
      exact ScoReach.step hk (ih (hx.tail hk))
  · intro h
    revert hx
    induction h with
    | refl => intro _; exact TjReach.refl _
    | @step a b c e _ ih =>
      intro hx
      obtain ⟨v, hv⟩ := (hS.keys a).2 hx
      have hb : b ∈ kidsOf (scoMiss.tjGraphM SUB) a := by
        rw [kidsOf_sub_key hS.map hv]
        exact (mem_preorder_set (hS.val a v hv).1 b).2 (((hS.val a v hv).2 b).2 e)
      exact TjReach.step hb (ih (hx.tail e))

/-- **The vertices of the graph of `sub`** are the nouns reachable from `b`. -/
theorem mem_tjVerts_sub {CA SC B SUB : Noun} (hS : SubIs CA SC B SUB) (u : Noun) :
    u ∈ tjVerts (scoMiss.tjGraphM SUB) ↔ ScoReach CA SC B u := by
  rw [mem_tjVerts]
  constructor
  · rintro ⟨p, hp, hu⟩
    obtain ⟨k, v, rfl, hg⟩ := (mem_subGraph hS.map p).1 hp
    have hk := (hS.keys k).1 ⟨v, hg⟩
    rcases hu with rfl | hu
    · exact hk
    · exact hk.tail (((hS.val k v hg).2 u).1 ((mem_preorder_set (hS.val k v hg).1 u).1 hu))
  · intro hu
    obtain ⟨v, hv⟩ := (hS.keys u).2 hu
    exact ⟨(u, preorder v), (mem_subGraph hS.map _).2 ⟨u, v, rfl, hv⟩, Or.inl rfl⟩

/-- Mutual reachability in the graph of `sub` from a reachable noun. -/
theorem tjScc_sub {CA SC B SUB : Noun} (hS : SubIs CA SC B SUB) {k x : Noun} (hk : ScoReach CA SC B k) :
    (TjReach (scoMiss.tjGraphM SUB) k x ∧ TjReach (scoMiss.tjGraphM SUB) x k) ↔
      (ScoReach CA SC k x ∧ ScoReach CA SC x k) := by
  constructor
  · rintro ⟨h1, h2⟩
    have r1 := (tjReach_sub hS hk).1 h1
    exact ⟨r1, (tjReach_sub hS (hk.trans r1)).1 h2⟩
  · rintro ⟨r1, r2⟩
    exact ⟨(tjReach_sub hS hk).2 r1, (tjReach_sub hS (hk.trans r1)).2 r2⟩

/-! ## The sets and the roll -/

theorem mapM_scoSetN_some : ∀ (L : List (List Noun)), ∃ Ss, L.mapM scoSetN = some Ss
  | [] => ⟨[], rfl⟩
  | l :: ls => by
    obtain ⟨S, hs, -⟩ := scoSetN_spec l
    obtain ⟨Ss, h⟩ := mapM_scoSetN_some ls
    exact ⟨S :: Ss, by simp [List.mapM_cons, hs, h]⟩

/-- `Ss` lists the set nouns of the lists of `L`. -/
inductive SetsOf : List (List Noun) → List Noun → Prop
  | nil : SetsOf [] []
  | cons {l S L Ss} : IsSet mugF S → (∀ k, Has S k ↔ k ∈ l) → SetsOf L Ss → SetsOf (l :: L) (S :: Ss)

theorem mapM_scoSetN : ∀ (L : List (List Noun)) (Ss : List Noun), L.mapM scoSetN = some Ss → SetsOf L Ss
  | [], Ss, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact SetsOf.nil
  | l :: ls, Ss, h => by
    obtain ⟨S', hs1, hs2, hs3⟩ := scoSetN_spec l
    simp only [List.mapM_cons, hs1, Option.bind_eq_bind, Option.bind_some] at h
    cases hr : ls.mapM scoSetN with
    | none => rw [hr] at h; cases h
    | some Ss' =>
      rw [hr] at h
      simp only [Option.bind_some, pure, Option.some.injEq] at h
      subst h
      exact SetsOf.cons hs2 hs3 (mapM_scoSetN ls Ss' hr)

theorem setsOf_mem : ∀ {L : List (List Noun)} {Ss : List Noun}, SetsOf L Ss →
    ∀ S ∈ Ss, ∃ l ∈ L, IsSet mugF S ∧ ∀ k, Has S k ↔ k ∈ l
  | _, _, SetsOf.nil, _, h => absurd h List.not_mem_nil
  | _, _, SetsOf.cons h1 h2 rest, S, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, h1, h2⟩
    · obtain ⟨l, hl, h'⟩ := setsOf_mem rest S h
      exact ⟨l, List.mem_cons_of_mem _ hl, h'⟩

theorem setsOf_mem_left : ∀ {L : List (List Noun)} {Ss : List Noun}, SetsOf L Ss →
    ∀ l ∈ L, ∃ S ∈ Ss, IsSet mugF S ∧ ∀ k, Has S k ↔ k ∈ l
  | _, _, SetsOf.nil, _, h => absurd h List.not_mem_nil
  | _, _, SetsOf.cons h1 h2 rest, l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, h1, h2⟩
    · obtain ⟨S, hS, h'⟩ := setsOf_mem_left rest l h
      exact ⟨S, List.mem_cons_of_mem _ hS, h'⟩

theorem setsOf_pairwise : ∀ {L : List (List Noun)} {Ss : List Noun}, SetsOf L Ss →
    L.Pairwise (fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) → Ss.Pairwise (fun S S' => ∀ k, Has S k → ¬ Has S' k)
  | _, _, SetsOf.nil, _ => List.Pairwise.nil
  | _, _, SetsOf.cons _ h2 rest, hp => by
    obtain ⟨p1, p2⟩ := List.pairwise_cons.1 hp
    refine List.pairwise_cons.2 ⟨fun S' hS' k hk hk' => ?_, setsOf_pairwise rest p2⟩
    obtain ⟨l', hl', -, h2'⟩ := setsOf_mem rest S' hS'
    exact p1 l' hl' k ((h2 k).1 hk) k ((h2' k).1 hk') rfl

/-- One step of the roll. -/
theorem rollStep_spec (S : Noun) : ∀ (l : List Noun) (acc : Noun), IsMap mugF acc →
    ∃ out, l.foldlM (fun acc m => putF mugF m S acc) acc = some out ∧ IsMap mugF out ∧
      ∀ k v, Get out k v ↔ (k ∈ l ∧ v = S) ∨ (k ∉ l ∧ Get acc k v)
  | [], acc, h => ⟨acc, rfl, h, fun k v => by simp⟩
  | y :: ys, acc, h => by
    obtain ⟨o, ho, hom, hog⟩ := putF_spec mugF acc y S h
    obtain ⟨out, h1, h2, h3⟩ := rollStep_spec S ys o hom
    refine ⟨out, by simp [List.foldlM_cons, ho, h1], h2, fun k v => ?_⟩
    rw [h3, hog]
    by_cases b : k = y
    · subst b
      by_cases a : k ∈ ys <;> simp [a]
    · by_cases a : k ∈ ys <;> simp [a, b]

/-- **The roll** over a list of disjoint sets. -/
theorem scoRoll_spec : ∀ (Ss : List Noun) (SC : Noun), IsMap mugF SC → (∀ S ∈ Ss, IsSet mugF S) →
    Ss.Pairwise (fun S S' => ∀ k, Has S k → ¬ Has S' k) →
    ∃ out, scoRoll SC Ss = some out ∧ IsMap mugF out ∧
      ∀ k v, Get out k v ↔ (∃ S ∈ Ss, Has S k ∧ v = S) ∨ ((∀ S ∈ Ss, ¬ Has S k) ∧ Get SC k v)
  | [], SC, h, _, _ => ⟨SC, rfl, h, fun k v => by simp⟩
  | S :: Ss, SC, h, hs, hp => by
    obtain ⟨a1, h1, h1m, h1g⟩ := rollStep_spec S (preorder S) SC h
    obtain ⟨out, h2, h2m, h2g⟩ := scoRoll_spec Ss a1 h1m (fun S' hS' => hs S' (List.mem_cons_of_mem _ hS'))
      (List.pairwise_cons.1 hp).2
    refine ⟨out, ?_, h2m, fun k v => ?_⟩
    · unfold scoRoll at h2 ⊢
      simp only [List.foldlM_cons, scoRollStep, h1, Option.bind_eq_bind, Option.bind_some]
      exact h2
    · rw [h2g, h1g, mem_preorder_set (hs S List.mem_cons_self)]
      have hd := (List.pairwise_cons.1 hp).1
      by_cases hk : Has S k
      · have hn : ∀ S' ∈ Ss, ¬ Has S' k := fun S' hS' => hd S' hS' k hk
        constructor
        · rintro (⟨S', hS', hk', _⟩ | ⟨_, (⟨_, hv⟩ | ⟨hk', _⟩)⟩)
          · exact absurd hk' (hn S' hS')
          · exact Or.inl ⟨S, List.mem_cons_self, hk, hv⟩
          · exact absurd hk hk'
        · rintro (⟨S', hS', hk', hv⟩ | ⟨hn', _⟩)
          · rcases List.mem_cons.1 hS' with e | hS'
            · subst e; exact Or.inr ⟨hn, Or.inl ⟨hk', hv⟩⟩
            · exact absurd hk' (hn S' hS')
          · exact absurd hk (hn' S List.mem_cons_self)
      · constructor
        · rintro (⟨S', hS', hk', hv⟩ | ⟨hn, (⟨hk', _⟩ | ⟨_, hg⟩)⟩)
          · exact Or.inl ⟨S', List.mem_cons_of_mem _ hS', hk', hv⟩
          · exact absurd hk' hk
          · refine Or.inr ⟨fun S' hS' => ?_, hg⟩
            rcases List.mem_cons.1 hS' with e | hS'
            · subst e; exact hk
            · exact hn S' hS'
        · rintro (⟨S', hS', hk', hv⟩ | ⟨hn, hg⟩)
          · rcases List.mem_cons.1 hS' with e | hS'
            · subst e; exact absurd hk' hk
            · exact Or.inl ⟨S', hS', hk', hv⟩
          · exact Or.inr ⟨fun S' hS' => hn S' (List.mem_cons_of_mem _ hS'), Or.inr ⟨hk, hg⟩⟩

/-! ## The miss -/

/-- The facts of the middle of the miss: `sub`, `+tarjan`'s list, the sets,
the roll. -/
theorem sco_mid {CA SC B SUB : Noun} (hO : ScoOK CA SC) (hS : SubIs CA SC B SUB) {L : List (List Noun)}
    (hL : tarjanM (scoMiss.tjGraphM SUB) = some L) {Ss : List Noun} (hSs : L.mapM scoSetN = some Ss) :
    ∃ SC', scoRoll SC Ss = some SC' ∧ IsMap mugF SC' ∧ (∃ S, Get SC' B S) ∧
      ∀ k v, Get SC' k v ↔ (¬ ScoReach CA SC B k ∧ Get SC k v) ∨
        (ScoReach CA SC B k ∧ IsSet mugF v ∧ ∀ x, Has v x ↔ ScoReach CA SC k x ∧ ScoReach CA SC x k) := by
  obtain ⟨L', hL', hspec⟩ := tarjanM_spec _ (sub_ne_nil hS) (sub_keys_nodup hS.map)
  rw [hL] at hL'
  cases hL'
  have hF := mapM_scoSetN L Ss hSs
  have hnd : L.flatten.Nodup := List.nodup_iff_count.2 fun u => by rw [hspec.2.1 u]; split <;> omega
  have hpw : L.Pairwise fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y := (List.pairwise_flatten.1 hnd).2
  have hdisj : Ss.Pairwise (fun S S' => ∀ k, Has S k → ¬ Has S' k) := setsOf_pairwise hF hpw
  obtain ⟨SC', hR, hRm, hRg⟩ := scoRoll_spec Ss SC hO.sc (fun S hS' => by
    obtain ⟨_, _, h1, _⟩ := setsOf_mem hF S hS'; exact h1) hdisj
  -- a member of a set is reachable from `b`
  have memR : ∀ S ∈ Ss, ∀ k, Has S k → ScoReach CA SC B k := by
    intro S hS' k hk
    obtain ⟨l, hl, hr⟩ := setsOf_mem hF S hS'
    have hkf : k ∈ L.flatten := List.mem_flatten.2 ⟨l, hl, (hr.2 k).1 hk⟩
    have hc := hspec.2.1 k
    have hpos : 0 < L.flatten.count k := List.count_pos_iff.2 hkf
    by_cases hv : k ∈ tjVerts (scoMiss.tjGraphM SUB)
    · exact (mem_tjVerts_sub hS k).1 hv
    · rw [if_neg hv] at hc; omega
  -- the members of the set of a reachable noun
  have setOf : ∀ k, ScoReach CA SC B k → ∃ S ∈ Ss, Has S k ∧ IsSet mugF S ∧
      ∀ x, Has S x ↔ ScoReach CA SC k x ∧ ScoReach CA SC x k := by
    intro k hk
    have hv := (mem_tjVerts_sub hS k).2 hk
    have hc := hspec.2.1 k
    rw [if_pos hv] at hc
    obtain ⟨l, hl, hkl⟩ := List.mem_flatten.1 (List.count_pos_iff.1 (by omega : 0 < L.flatten.count k))
    obtain ⟨S, hS', hr⟩ := setsOf_mem_left hF l hl
    refine ⟨S, hS', (hr.2 k).2 hkl, hr.1, fun x => ?_⟩
    rw [hr.2 x, (hspec.1 l hl).2 k hkl x]
    exact tjScc_sub hS hk
  refine ⟨SC', hR, hRm, ?_, fun k v => ?_⟩
  · obtain ⟨S2, hS2, hk2, -⟩ := setOf B (ScoReach.refl B)
    exact ⟨S2, (hRg B S2).2 (Or.inl ⟨S2, hS2, hk2, rfl⟩)⟩
  rw [hRg]
  constructor
  · rintro (⟨S, hS', hk, hv⟩ | ⟨hn, hg⟩)
    · subst hv
      have hk' := memR v hS' k hk
      obtain ⟨S2, hS2, hk2, hset2, hm2⟩ := setOf k hk'
      -- the sets are disjoint, so `S` is `S2`
      have e : v = S2 := by
        by_cases ne : v = S2
        · exact ne
        exfalso
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hS'
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hS2
        have hij : i ≠ j := fun h => ne (by subst h; rfl)
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · exact (List.pairwise_iff_getElem.1 hdisj i j hi hj h) k hk hk2
        · exact (List.pairwise_iff_getElem.1 hdisj j i hj hi h) k hk2 hk
      subst e
      exact Or.inr ⟨hk', hset2, hm2⟩
    · refine Or.inl ⟨fun hr => ?_, hg⟩
      obtain ⟨S2, hS2, hk2, -⟩ := setOf k hr
      exact hn S2 hS2 hk2
  · rintro (⟨hn, hg⟩ | ⟨hk, hset, hm⟩)
    · exact Or.inr ⟨fun S hS' hk => hn (memR S hS' k hk), hg⟩
    · obtain ⟨S2, hS2, hk2, hset2, hm2⟩ := setOf k hk
      have e : v = S2 := isSet_ext hset hset2 fun x => (hm x).trans (hm2 x).symm
      exact Or.inl ⟨S2, hS2, hk2, e⟩

/-- **The miss of `+scc-of` returns**, at the fuel `scoFuel`. -/
theorem scoMiss_total {B CA SC : Noun} (hO : ScoOK CA SC) :
    ∃ r, scoMiss B CA SC (scoFuel CA SC B) = some r := by
  obtain ⟨SUB, hsub, hS⟩ := scoSub_total (B := B) hO
  obtain ⟨L, hL⟩ := tarjanM_total _ (sub_ne_nil hS) (sub_keys_nodup hS.map)
  obtain ⟨Ss, hSs⟩ := mapM_scoSetN_some L
  obtain ⟨SC', hR, hRm, hB, -⟩ := sco_mid hO hS hL hSs
  obtain ⟨S, hS2⟩ := hB
  refine ⟨C S SC', ?_⟩
  simp [scoMiss, hsub, hL, hSs, hR, scoGot, getF_some hRm hS2]

/-- **What the miss writes**: whenever it returns, `[S sccs']` with
`b ↦ S`; the pairs of `sccs'` are the old pairs off the nouns reachable from
`b`, and on each noun `m` reachable from `b` the set of the `x` with
`ScoReach m x` and `ScoReach x m`. -/
theorem scoMiss_spec {B CA SC : Noun} (hO : ScoOK CA SC) {n : Nat} {r : Noun} (h : scoMiss B CA SC n = some r) :
    ∃ S SC', r = C S SC' ∧ IsMap mugF SC' ∧ Get SC' B S ∧
      ∀ k v, Get SC' k v ↔ (¬ ScoReach CA SC B k ∧ Get SC k v) ∨
        (ScoReach CA SC B k ∧ IsSet mugF v ∧ ∀ x, Has v x ↔ ScoReach CA SC k x ∧ ScoReach CA SC x k) := by
  unfold scoMiss at h
  obtain ⟨SUB, hsub, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨L, hL, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Ss, hSs, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨SC', hR, h⟩ := Option.bind_eq_some_iff.1 h
  have hS := scoSub_ok2 hO n [B] (A 0) SUB (subInv_init CA SC B) hsub
  obtain ⟨SC'', hR', hRm, ⟨S, hS2⟩, hRg⟩ := sco_mid hO hS hL hSs
  rw [hR] at hR'
  cases hR'
  unfold scoGot at h
  rw [getF_some hRm hS2] at h
  simp only [Option.some.injEq] at h
  exact ⟨S, SC', h.symm, hRm, hS2, hRg⟩

/-- On a miss (`b` not a key of `sccs`), no noun reachable from `b` is a key
of `sccs`. -/
theorem scoReach_fresh {B CA SC : Noun} (hO : ScoOK CA SC) (hB : getF mugF B SC = some (A 0)) {k : Noun}
    (hk : ScoReach CA SC B k) : ∀ w, ¬ Get SC k w := by
  rcases reach_last hk with rfl | ⟨y, hy⟩
  · exact (getF_nil_iff hO.sc).1 hB
  · exact hy.2

/-- **On a miss, every old pair stays.** -/
theorem scoMiss_keeps {B CA SC : Noun} (hO : ScoOK CA SC) (hB : getF mugF B SC = some (A 0)) {n : Nat}
    {S SC' : Noun} (h : scoMiss B CA SC n = some (C S SC')) : ∀ k v, Get SC k v → Get SC' k v := by
  obtain ⟨S1, SC1, e, -, -, hg⟩ := scoMiss_spec hO h
  cases e
  intro k v hv
  exact (hg k v).2 (Or.inl ⟨fun hr => scoReach_fresh hO hB hr v hv, hv⟩)

end Tarjan
end Formalization
