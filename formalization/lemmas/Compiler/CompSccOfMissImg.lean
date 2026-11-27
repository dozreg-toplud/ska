import lemmas.Compiler.CompSccOfMissEnc
import lemmas.Compiler.PokeLinkSccHit
import lemmas.Ska.TarjanSccOfSem
import lemmas.Compiler.PokeLinkGood5

/-!
# `+scc-of` on the encoded state: its image and its read-back (track Q)

On the nouns of a table's `calls` (`callsNoun`) and of `sccs.cache`
(`sccsNoun`), the miss of `+scc-of` is `scoMiss` (`sccG_miss_enc`), which
returns (`scoMiss_total`) and writes the mutual-`ScoReach` classes of the
nouns reachable from `b` (`scoMiss_spec`, `Ska/TarjanSccOfSem.lean`):

* `scoOK_enc`, `sccG_miss_eq`: the gate on a miss returns `scoMiss`'s noun;
* the read-back: `rbSet` / `rbSccs` read a set noun of bells / a map noun
  from bells to set nouns of bells as `FinMap`s (`setNoun_rbSet`,
  `sccsNoun_rbSccs`); `setNounB_inj`, `sccsNoun_inj`, `sccPairNoun_inj`;
* **`sccImageMiss`** (track P's `SccImageMiss`) and **`sccImage`**
  (`SccImage`): every key and member the miss writes is a bell
  (`scoReach_bell`);
* `sccOfP_hit`, **`sccOfP_miss`**: what `sccOfP` returns on a hit, and on a
  miss in terms of `ScoReach` on the encoded nouns (keys and members as
  `Bell.toNoun`, which is `TKey.enc`);
* **`sccOfKeeps_of`**: track P's `SccOfKeeps Ar` for every `Ar` whose
  `sccOf` is `sccOfP`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM Tarjan

/-! ## The miss returns `scoMiss`'s noun -/

theorem scoOK_enc (L : LongB FinMap) (sc : FinMap Bell (FinMap Bell Unit)) :
    ScoOK (callsNoun L) (sccsNoun sc) where
  ca := FinMap.isMap_toNoun _ _
  caSet := fun k v h => by
    obtain ⟨b, e, -, -, rfl⟩ := (FinMap.get_toNoun _ L.code k v).1 h
    exact FinMap.isSet_setNoun _
  sc := FinMap.isMap_toNoun _ _

theorem getF_miss {b : Bell} {sc : FinMap Bell (FinMap Bell Unit)} (hb : sc.get b = none) :
    getF mugF b.toNoun (sccsNoun sc) = some (A 0) := by
  have h := FinMap.getF_toNoun FinMap.setNoun sc b
  rw [hb] at h
  exact h

/-- **On a miss the gate returns `scoMiss`'s noun** (at the fuel `scoFuel`). -/
theorem sccG_miss_eq {b : Bell} {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)} (hb : sc.get b = none) :
    ∃ r, scoMiss b.toNoun (callsNoun L) (sccsNoun sc) (scoFuel (callsNoun L) (sccsNoun sc) b.toNoun) = some r ∧
      sccG b.toNoun (callsNoun L) (sccsNoun sc) = some r := by
  obtain ⟨r, hr⟩ := scoMiss_total (B := b.toNoun) (scoOK_enc L sc)
  exact ⟨r, hr, sccG_miss_enc b L sc hb _ r hr⟩

/-! ## Reading nouns back as `FinMap`s -/

theorem get_mem_preorder {a k v : Noun} (h : Get a k v) : C k v ∈ preorder a := by
  induction h with
  | here => rw [preorder_node]; exact List.mem_cons_self
  | left _ ih => rw [preorder_node]; exact List.mem_cons_of_mem _ (List.mem_append_left _ ih)
  | right _ ih => rw [preorder_node]; exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)

/-- The bell the key of a pair noun encodes. -/
noncomputable def pairBell : Noun → Option Bell
  | Noun.cell kn _ => FinMap.decode? kn
  | Noun.atom _ => none

theorem pairBell_mem {a : Noun} {k : Bell} {v : Noun} (h : Get a k.toNoun v) :
    k ∈ (preorder a).filterMap pairBell :=
  List.mem_filterMap.2 ⟨_, get_mem_preorder h, by
    show FinMap.decode? (TKey.enc k) = some k
    exact FinMap.decode?_enc k⟩

open Classical in
/-- The bells of a set noun, as a `FinMap`. -/
noncomputable def rbSet (S : Noun) : FinMap Bell Unit :=
  ⟨fun k => if Has S k.toNoun then some () else none, (preorder (toMap S)).filterMap pairBell, fun k hk => by
    by_cases h : Has S k.toNoun
    · exact pairBell_mem h
    · simp [h] at hk⟩

theorem rbSet_get (S : Noun) (k : Bell) : FinMap.get (rbSet S) k = some () ↔ Has S k.toNoun := by
  unfold rbSet FinMap.get
  by_cases h : Has S k.toNoun <;> simp [h]

/-- **A set noun of bells is the noun of its read-back.** -/
theorem setNoun_rbSet {S : Noun} (hS : IsSet mugF S) (hb : ∀ x, Has S x → ∃ k : Bell, x = k.toNoun) :
    FinMap.setNoun (rbSet S) = S := by
  apply isSet_ext (FinMap.isSet_setNoun _) hS
  intro x
  rw [FinMap.has_setNoun]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (rbSet_get S k).1 hk
  · intro hx
    obtain ⟨k, rfl⟩ := hb x hx
    exact ⟨k, (rbSet_get S k).2 hx, rfl⟩

open Classical in
/-- A map noun from bells to set nouns, as a `FinMap`. -/
noncomputable def rbSccs (SC : Noun) : FinMap Bell (FinMap Bell Unit) :=
  ⟨fun k => if h : ∃ v, Get SC k.toNoun v then some (rbSet (Classical.choose h)) else none,
    (preorder SC).filterMap pairBell, fun k hk => by
    by_cases h : ∃ v, Get SC k.toNoun v
    · obtain ⟨v, hv⟩ := h
      exact pairBell_mem hv
    · simp [h] at hk⟩

open Classical in
theorem rbSccs_get {SC : Noun} (hm : IsMap mugF SC) (k : Bell) (S : FinMap Bell Unit) :
    FinMap.get (rbSccs SC) k = some S ↔ ∃ v, Get SC k.toNoun v ∧ S = rbSet v := by
  show (if h : ∃ v, Get SC k.toNoun v then some (rbSet (Classical.choose h)) else none) = some S ↔ _
  by_cases h : ∃ v, Get SC k.toNoun v
  · rw [dif_pos h]
    constructor
    · intro e
      exact ⟨_, Classical.choose_spec h, (Option.some.inj e).symm⟩
    · rintro ⟨v, hv, rfl⟩
      rw [tj_get_uniq hm (Classical.choose_spec h) hv]
  · rw [dif_neg h]
    constructor
    · intro e; cases e
    · rintro ⟨v, hv, -⟩; exact absurd ⟨v, hv⟩ h

/-- **A map noun from bells to set nouns of bells is `sccsNoun` of its
read-back.** -/
theorem sccsNoun_rbSccs {SC : Noun} (hm : IsMap mugF SC)
    (hk : ∀ k v, Get SC k v → (∃ b : Bell, k = b.toNoun) ∧ IsSet mugF v ∧ ∀ x, Has v x → ∃ c : Bell, x = c.toNoun) :
    sccsNoun (rbSccs SC) = SC := by
  apply isMap_ext (FinMap.isMap_toNoun _ _) hm
  intro kn vn
  show Get ((rbSccs SC).toNoun FinMap.setNoun) kn vn ↔ Get SC kn vn
  rw [FinMap.get_toNoun]
  constructor
  · rintro ⟨k, S, h1, rfl, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (rbSccs_get hm k S).1 h1
    have := hk _ v hv
    rw [setNoun_rbSet this.2.1 this.2.2]
    exact hv
  · intro hv
    obtain ⟨⟨k, rfl⟩, hs, hb⟩ := hk kn vn hv
    exact ⟨k, rbSet vn, (rbSccs_get hm k _).2 ⟨vn, hv, rfl⟩, rfl, (setNoun_rbSet hs hb).symm⟩

theorem has_setNoun_enc (S : FinMap Bell Unit) (k : Bell) :
    Has (FinMap.setNoun S) k.toNoun ↔ FinMap.get S k = some () := by
  rw [FinMap.has_setNoun]
  constructor
  · rintro ⟨k', h, e⟩
    have e' : k = k' := TKey.enc_inj k k' e
    subst e'
    exact h
  · intro h
    exact ⟨k, h, rfl⟩

theorem setNounB_inj {S S' : FinMap Bell Unit} (h : FinMap.setNoun S = FinMap.setNoun S') : S = S' := by
  apply Subtype.ext
  funext k
  have hk : FinMap.get S k = some () ↔ FinMap.get S' k = some () := by
    rw [← has_setNoun_enc, ← has_setNoun_enc, h]
  unfold FinMap.get at hk
  cases e : S.1 k <;> cases e' : S'.1 k <;> simp_all

/-- The pairs of `sccsNoun m` are the encoded pairs of `m`. -/
theorem sccs_get_iff (m : FinMap Bell (FinMap Bell Unit)) (k : Bell) (S : FinMap Bell Unit) :
    FinMap.get m k = some S ↔ Get (sccsNoun m) k.toNoun (FinMap.setNoun S) := by
  unfold sccsNoun
  rw [FinMap.get_toNoun]
  constructor
  · intro hS
    exact ⟨k, S, hS, rfl, rfl⟩
  · rintro ⟨k', S', h1, e1, e2⟩
    have e1' : k = k' := TKey.enc_inj k k' e1
    subst e1'
    rw [setNounB_inj e2]
    exact h1

theorem sccsNoun_inj {m m' : FinMap Bell (FinMap Bell Unit)} (h : sccsNoun m = sccsNoun m') : m = m' := by
  apply Subtype.ext
  funext k
  cases e : m.1 k with
  | none =>
    cases e' : m'.1 k with
    | none => rfl
    | some S =>
      have h1 := (sccs_get_iff m' k S).1 e'
      rw [← h, ← sccs_get_iff] at h1
      have : m.1 k = some S := h1
      rw [e] at this
      cases this
  | some S =>
    have h1 := (sccs_get_iff m k S).1 e
    rw [h, ← sccs_get_iff] at h1
    exact h1.symm

theorem sccPairNoun_inj {r r' : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)}
    (h : sccPairNoun r = sccPairNoun r') : r = r' := by
  unfold sccPairNoun at h
  simp only [Noun.cell.injEq] at h
  exact Prod.ext (setNounB_inj h.1) (sccsNoun_inj h.2)

/-! ## The image -/

/-- A noun `ScoReach` reaches on the encoded nouns is the start or a bell. -/
theorem scoReach_bell {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)} {a y : Noun}
    (h : ScoReach (callsNoun L) (sccsNoun sc) a y) : y = a ∨ ∃ c : Bell, y = c.toNoun := by
  rcases Tarjan.reach_last h with rfl | ⟨x, hx⟩
  · exact Or.inl rfl
  · right
    obtain ⟨⟨v, hv, hc⟩, -⟩ := hx
    obtain ⟨b, e, -, -, rfl⟩ := (FinMap.get_toNoun _ L.code x v).1 hv
    obtain ⟨c, -, rfl⟩ := (FinMap.has_setNoun _ y).1 hc
    exact ⟨c, rfl⟩

/-- **The image of `+scc-of` on a miss**: the noun of a pair of maps. -/
theorem sccImageMiss : SccImageMiss := by
  intro b L sc x hb hx
  obtain ⟨r, hr, hg⟩ := sccG_miss_eq (L := L) hb
  rw [hg] at hx
  cases hx
  obtain ⟨S, SC', rfl, hm, hS, hp⟩ := scoMiss_spec (scoOK_enc L sc) hr
  have hbell : ∀ k v, Get SC' k v →
      (∃ c : Bell, k = c.toNoun) ∧ IsSet mugF v ∧ ∀ y, Has v y → ∃ c : Bell, y = c.toNoun := by
    intro k v hkv
    rcases (hp k v).1 hkv with ⟨-, hold⟩ | ⟨hk, hs, hmem⟩
    · obtain ⟨k', S', -, rfl, rfl⟩ := (FinMap.get_toNoun _ sc k v).1 hold
      refine ⟨⟨k', rfl⟩, FinMap.isSet_setNoun _, fun y hy => ?_⟩
      obtain ⟨c, -, rfl⟩ := (FinMap.has_setNoun _ y).1 hy
      exact ⟨c, rfl⟩
    · have hkb : ∃ c : Bell, k = c.toNoun := by
        rcases scoReach_bell hk with rfl | h
        · exact ⟨b, rfl⟩
        · exact h
      refine ⟨hkb, hs, fun y hy => ?_⟩
      rcases scoReach_bell ((hmem y).1 hy).1 with rfl | h
      · exact hkb
      · exact h
  have hSb := hbell _ _ hS
  refine ⟨(rbSet S, rbSccs SC'), ?_⟩
  unfold sccPairNoun
  rw [setNoun_rbSet hSb.2.1 hSb.2.2, sccsNoun_rbSccs hm hbell]

/-- **`SccImage`** (track P, `PokeLinkScc.lean`). -/
theorem sccImage : SccImage := sccImage_of_miss sccImageMiss

/-! ## `sccOfP` read back -/

theorem sccOfP_spec {b : Bell} {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)}
    {q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)} (h : sccOfP b L sc = some q) :
    sccG b.toNoun (callsNoun L) (sccsNoun sc) = some (sccPairNoun q) := by
  unfold sccOfP at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem sccOfP_of {b : Bell} {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)}
    {r : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)}
    (h : sccG b.toNoun (callsNoun L) (sccsNoun sc) = some (sccPairNoun r)) : sccOfP b L sc = some r := by
  have hex : ∃ r, sccG b.toNoun (callsNoun L) (sccsNoun sc) = some (sccPairNoun r) := ⟨r, h⟩
  unfold sccOfP
  rw [dif_pos hex]
  have e : some (sccPairNoun (Classical.choose hex)) = some (sccPairNoun r) :=
    (Classical.choose_spec hex).symm.trans h
  exact congrArg some (sccPairNoun_inj (Option.some.inj e))

/-- **The hit**: `sccs` unchanged. -/
theorem sccOfP_hit {b : Bell} {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)} {v : FinMap Bell Unit}
    (hv : sc.get b = some v) : sccOfP b L sc = some (v, sc) :=
  sccOfP_of (sccG_hit b (callsNoun L) sc v hv)

theorem forall_has_iff {S : FinMap Bell Unit} {M : Noun → Prop} (hM : ∀ x, M x → ∃ c : Bell, x = c.toNoun) :
    (∀ x, Has (FinMap.setNoun S) x ↔ M x) ↔ ∀ x : Bell, FinMap.get S x = some () ↔ M x.toNoun := by
  constructor
  · intro h x
    rw [← has_setNoun_enc]
    exact h _
  · intro h x
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (FinMap.has_setNoun S x).1 hx
      exact (h c).1 hc
    · intro hx
      obtain ⟨c, rfl⟩ := hM x hx
      exact (has_setNoun_enc S c).2 ((h c).2 hx)

/-- **The miss read back**: `b` gets the first half; the pairs of the new
`sccs` are the old pairs off the bells reachable from `b`, and on each bell
`k` reachable from `b` the bells `x` with `k` and `x` reaching each other,
all along `ScoReach` on the encoded `calls` and `sccs`. -/
theorem sccOfP_miss {b : Bell} {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)}
    {q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)} (hb : sc.get b = none) (h : sccOfP b L sc = some q) :
    FinMap.get q.2 b = some q.1 ∧ ∀ k S, FinMap.get q.2 k = some S ↔
      (FinMap.get sc k = some S ∧ ¬ ScoReach (callsNoun L) (sccsNoun sc) b.toNoun k.toNoun) ∨
      (ScoReach (callsNoun L) (sccsNoun sc) b.toNoun k.toNoun ∧ ∀ x, FinMap.get S x = some () ↔
        ScoReach (callsNoun L) (sccsNoun sc) k.toNoun x.toNoun ∧
          ScoReach (callsNoun L) (sccsNoun sc) x.toNoun k.toNoun) := by
  have hg := sccOfP_spec h
  obtain ⟨r, hr, hg'⟩ := sccG_miss_eq (L := L) hb
  rw [hg] at hg'
  have hr' : r = sccPairNoun q := (Option.some.inj hg').symm
  subst hr'
  obtain ⟨S, SC', e, -, hS, hp⟩ := scoMiss_spec (scoOK_enc L sc) hr
  unfold sccPairNoun at e
  simp only [Noun.cell.injEq] at e
  obtain ⟨e1, e2⟩ := e
  subst e1
  subst e2
  refine ⟨(sccs_get_iff q.2 b q.1).2 hS, fun k S => ?_⟩
  rw [sccs_get_iff q.2 k S, hp, ← sccs_get_iff sc k S]
  have hM : ∀ x, (ScoReach (callsNoun L) (sccsNoun sc) k.toNoun x ∧ ScoReach (callsNoun L) (sccsNoun sc) x k.toNoun) →
      ∃ c : Bell, x = c.toNoun := by
    rintro x ⟨h1, -⟩
    rcases scoReach_bell h1 with rfl | h
    · exact ⟨k, rfl⟩
    · exact h
  have hF := forall_has_iff (S := S)
    (M := fun x => ScoReach (callsNoun L) (sccsNoun sc) k.toNoun x ∧ ScoReach (callsNoun L) (sccsNoun sc) x k.toNoun) hM
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, -, h3⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h1, hF.1 h3⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h3⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h1, FinMap.isSet_setNoun _, hF.2 h3⟩

/-! ## `SccOfKeeps` -/

/-- **`+scc-of` keeps `SccsGoodM` and every old entry** (track P's
`SccOfKeeps`), for every `Ar` whose `sccOf` is the pill's. -/
theorem sccOfKeeps_of {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} (hA : Ar.sccOf = sccOfP) :
    SccOfKeeps Ar := by
  intro b L sc q hg h
  rw [hA] at h
  cases hb : sc.get b with
  | some v =>
    rw [sccOfP_hit hb, Option.some.injEq] at h
    subst h
    exact ⟨hg, fun k S hk => hk⟩
  | none =>
    obtain ⟨-, hq⟩ := sccOfP_miss hb h
    have hfresh : ∀ k S, FinMap.get sc k = some S → ¬ ScoReach (callsNoun L) (sccsNoun sc) b.toNoun k.toNoun :=
      fun k S hk hr => scoReach_fresh (scoOK_enc L sc) (getF_miss hb) hr _ ((sccs_get_iff sc k S).1 hk)
    have hkeep : ∀ k S, FinMap.get sc k = some S → FinMap.get q.2 k = some S :=
      fun k S hk => (hq k S).2 (Or.inl ⟨hk, hfresh k S hk⟩)
    refine ⟨fun k S hk => ?_, hkeep⟩
    rcases (hq k S).1 hk with ⟨hold, -⟩ | ⟨hr, hS⟩
    · obtain ⟨h1, h2⟩ := hg k S hold
      exact ⟨h1, fun k' hk' => hkeep k' S (h2 k' hk')⟩
    · refine ⟨(hS k).2 ⟨ScoReach.refl _, ScoReach.refl _⟩, fun k' hk' => ?_⟩
      obtain ⟨r1, r2⟩ := (hS k').1 hk'
      exact (hq k' S).2 (Or.inr ⟨hr.trans r1, fun x => (hS x).trans
        ⟨fun ⟨a1, a2⟩ => ⟨r2.trans a1, a2.trans r1⟩, fun ⟨a1, a2⟩ => ⟨r1.trans a1, a2.trans r2⟩⟩⟩)

end Compiler
end Formalization
