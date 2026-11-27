import lemmas.Ska.PokeAna
import lemmas.Compiler.TreapSet
import lemmas.Compiler.OptLinkBase
import lemmas.Compiler.PokeFrame

/-!
# The model's state as the compiler's core: `enc`

`Gap` of `Assembly.lean` takes the compiler's state as the noun of its core,
and the one route to its fields (`PokeM.gap_of`) asks for an injective
`enc : CSt M Map J H CR → Noun`.  Here `enc` is defined, with the pill's
types: `M := FinMap` (the instance of `Compiler/TreapKey.lean`), `Map :=
TreapMap mugF`, and the parts the model keeps abstract as their nouns (`J`:
`jets` of `long-ska`, `H`: `jets-hot`, `CR`: `inl` and `sure` of the cache).

The compiler's core is `[pokeBat [monoBat [state lib]]]` (`PokeFrame.lean`),
and `state=state-0` is `[%0 long-ska jets-hot cache]` with `long-ska =
[jets memo code calls vars seek]` and `cache = [nary mono sccs inl sure]`
(README Gaps 23 has the axes).  The model's `code` is one table of
`VarEntry`s (`nomm`, `calls`, `seek`); the pill keeps three maps, and in
`code` the flags `pure` and `total` of `+eval-finalized` next to the nomm,
which the model does not have.  So `enc` takes the flags as a parameter `fl`,
a function of the table and the bell (mismatch P1 of Gaps 23).

`enc` is a function with no choice in it: a map's noun is `FinMap.toNoun`, the
one treap under `mugF` with its pairs (`isMap_ext`).  It is injective for
every `fl` (`enc_inj`): the pairs of a map's noun are those of the map
(`toNoun_pairs`), and the nouns of nomms, datums, straights and needs are
injective (`nomm_toNoun_inj`, `fdatum_toNoun_inj`, `straight_toNoun_inj`,
the last the leaf `hinj` of the ledger).  The pill's `cor` is the encoding of
the empty state (`cor_enc`, leaf 4.1), by the kernel on axis `14` of `cor`
only.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## Injective nouns -/

theorem unitNoun_id_inj {a b : Option Noun} (h : unitNoun (fun x => x) a = unitNoun (fun x => x) b) :
    a = b := by
  cases a <;> cases b <;> simp_all [unitNoun]

theorem unitNoun_inj_of {α : Type} {f : α → Noun} (hf : ∀ a b, f a = f b → a = b) {a b : Option α}
    (h : unitNoun f a = unitNoun f b) : a = b := by
  cases a <;> cases b <;> simp_all [unitNoun]
  exact hf _ _ h

theorem bell_toNoun_inj {a b : Bell} (h : a.toNoun = b.toNoun) : a = b := TKey.enc_inj a b h

theorem nomm_toNoun_ne_atom : ∀ (n : Nomm) (k : Nat), n.toNoun ≠ A k := by
  intro n k; cases n <;> simp [Nomm.toNoun]

theorem nomm_atom_ne_toNoun (n : Nomm) (k : Nat) : A k ≠ n.toNoun := fun h => nomm_toNoun_ne_atom n k h.symm

theorem nomm_toNoun_inj : ∀ {a b : Nomm}, a.toNoun = b.toNoun → a = b := by
  intro a
  induction a with
  | cons p q ihp ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h
    · rw [ihp h.1, ihq h.2]
  | n0 p => intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢; exact h
  | n1 p => intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢; exact h
  | n2 p q i ihp ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    refine ⟨ihp h.1, ihq h.2.1, ?_⟩
    refine unitNoun_inj_of (fun x y e => ?_) h.2.2
    obtain ⟨b1, k1⟩ := x
    obtain ⟨b2, k2⟩ := y
    simp only [Noun.cell.injEq] at e
    rw [bell_toNoun_inj e.1, unitNoun_id_inj e.2]
  | n3 p ih => intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢; exact ih h
  | n4 p ih => intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢; exact ih h
  | n5 p q ihp ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | n6 p q r ihp ihq ihr =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨ihp h.1, ihq h.2.1, ihr h.2.2⟩
  | n7 p q ihp ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | n10 a v q ihv ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨h.1.1, ihv h.1.2, ihq h.2⟩
  | n11s t q body ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨h.1, ihq h.2.1, h.2.2⟩
  | n11d t hh q body ihh ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨h.1.1, ihh h.1.2, ihq h.2.1, h.2.2⟩
  | n12 p q ihp ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | mean p bl q body k ihp ihq =>
    intro b h; cases b <;> simp [Nomm.toNoun, nomm_toNoun_ne_atom, nomm_atom_ne_toNoun, Tag.mean] at h ⊢
    exact ⟨ihp h.1, bell_toNoun_inj h.2.1, ihq h.2.2.1, h.2.2.2.1, unitNoun_id_inj h.2.2.2.2⟩

theorem needOrd_toNoun_ne_atom : ∀ (n : NeedOrd) (k : Nat), n.toNoun ≠ A k := by
  intro n k; cases n <;> simp [NeedOrd.toNoun]

theorem needOrd_atom_ne_toNoun (n : NeedOrd) (k : Nat) : A k ≠ n.toNoun :=
  fun h => needOrd_toNoun_ne_atom n k h.symm

theorem needOrd_toNoun_inj : ∀ {a b : NeedOrd}, a.toNoun = b.toNoun → a = b := by
  intro a
  induction a with
  | pair p q ihp ihq =>
    intro b h; cases b <;> simp [NeedOrd.toNoun, needOrd_toNoun_ne_atom, needOrd_atom_ne_toNoun] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | both p q ihp ihq =>
    intro b h; cases b <;> simp [NeedOrd.toNoun, needOrd_toNoun_ne_atom, needOrd_atom_ne_toNoun, Tag.both, Tag.this, Tag.none] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | this => intro b h; cases b <;> simp [NeedOrd.toNoun, needOrd_toNoun_ne_atom, needOrd_atom_ne_toNoun, Tag.both, Tag.this, Tag.none] at h ⊢
  | none => intro b h; cases b <;> simp [NeedOrd.toNoun, needOrd_toNoun_ne_atom, needOrd_atom_ne_toNoun, Tag.both, Tag.this, Tag.none] at h ⊢

theorem tr_toNoun_inj {ν : Type} {f : ν → Noun} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {a b : Tr ν}, a.toNoun f = b.toNoun f → a = b
  | .nil, .nil, _ => rfl
  | .nil, .node _ _ _ _, h => by simp [Tr.toNoun] at h
  | .node _ _ _ _, .nil, h => by simp [Tr.toNoun] at h
  | .node k v l r, .node k' v' l' r', h => by
    simp only [Tr.toNoun, Noun.cell.injEq, Noun.atom.injEq] at h
    obtain ⟨⟨rfl, hv⟩, hl, hr⟩ := h
    rw [hf _ _ hv, tr_toNoun_inj hf hl, tr_toNoun_inj hf hr]

/-- **`Straight.toNoun` is injective** (the leaf `hinj` of the ledger). -/
theorem straight_toNoun_inj {a b : Straight (TreapMap mugF)} (h : a.toNoun = b.toNoun) : a = b := by
  obtain ⟨na, ka, ba⟩ := a
  obtain ⟨nb, kb, bb⟩ := b
  simp only [Straight.toNoun, Noun.cell.injEq, Noun.atom.injEq] at h
  obtain ⟨h1, rfl, h3⟩ := h
  have hb : ba = bb := Subtype.ext (tr_toNoun_inj (fun x y e => blob_toNoun_inj.1 e) h3)
  rw [needOrd_toNoun_inj h1, hb]

/-! ## Maps: the pairs of a map's noun -/

namespace FinMap

variable {κ ν ν' : Type} [TKey κ]

/-- Two maps with one noun, under two layouts of the values, have the same
pairs up to the layouts. -/
theorem toNoun_pairs {f : ν → Noun} {f' : ν' → Noun} {m : FinMap κ ν} {m' : FinMap κ ν'}
    (h : m.toNoun f = m'.toNoun f') (k : κ) : (m.1 k).map f = (m'.1 k).map f' := by
  have fwd : ∀ v, m.1 k = some v → ∃ v', m'.1 k = some v' ∧ f v = f' v' := by
    intro v hk
    have g := (get_toNoun f m (TKey.enc k) (f v)).2 ⟨k, v, hk, rfl, rfl⟩
    rw [h] at g
    obtain ⟨k', v', h1, e1, e2⟩ := (get_toNoun f' m' _ _).1 g
    rw [TKey.enc_inj _ _ e1]
    exact ⟨v', h1, e2⟩
  have bwd : ∀ v', m'.1 k = some v' → ∃ v, m.1 k = some v := by
    intro v' hk
    have g := (get_toNoun f' m' (TKey.enc k) (f' v')).2 ⟨k, v', hk, rfl, rfl⟩
    rw [← h] at g
    obtain ⟨k', v, h1, e1, -⟩ := (get_toNoun f m _ _).1 g
    rw [TKey.enc_inj _ _ e1]
    exact ⟨v, h1⟩
  cases e : m.1 k with
  | some v =>
    obtain ⟨v', h1, h2⟩ := fwd v e
    rw [h1]; simp [h2]
  | none =>
    cases e' : m'.1 k with
    | none => rfl
    | some v' =>
      obtain ⟨v, h1⟩ := bwd v' e'
      rw [e] at h1; cases h1

theorem toNoun_inj' {f : ν → Noun} (hf : ∀ a b, f a = f b → a = b) {m m' : FinMap κ ν}
    (h : m.toNoun f = m'.toNoun f) : m = m' := by
  apply Subtype.ext; funext k
  have := toNoun_pairs h k
  cases e : m.1 k <;> cases e' : m'.1 k <;> simp_all
  exact hf _ _ this

theorem setNoun_inj {m m' : FinMap κ Unit} (h : m.setNoun = m'.setNoun) : m = m' := by
  have h2 := congrArg toMap h
  rw [toMap_setNoun, toMap_setNoun] at h2
  exact toNoun_inj' (fun _ _ _ => rfl) h2

/-- The noun of a map with no pairs. -/
theorem toNoun_of_none {f : ν → Noun} {m : FinMap κ ν} (h : ∀ k, m.1 k = none) : m.toNoun f = A 0 := by
  unfold toNoun
  generalize m.supp = L
  induction L with
  | nil => rfl
  | cons k L ih => simp only [List.foldl_cons, step, h]; exact ih

/-- A map with its values changed by a function of the key. -/
def mapK (g : κ → ν → ν') (m : FinMap κ ν) : FinMap κ ν' :=
  ⟨fun k => (m.1 k).map (g k), by
    obtain ⟨l, hl⟩ := m.2
    exact ⟨l, fun k h => hl k (fun e => h (by simp [e]))⟩⟩

end FinMap

theorem fdatum_toNoun_inj {a b : FDatum FinMap} (h : a.toNoun = b.toNoun) : a = b := by
  obtain ⟨c1, n1, l1, i1, s1, p1, m1, a1⟩ := a
  obtain ⟨c2, n2, l2, i2, s2, p2, m2, a2⟩ := b
  simp only [FDatum.toNoun, Noun.cell.injEq] at h
  obtain ⟨hc, hn, hl, hi, hs, ⟨hp, hm⟩, ha⟩ := h
  have hc' : c1 = c2 := FinMap.setNoun_inj hc
  rw [hc', nomm_toNoun_inj hn, Sock.toNoun_inj _ _ hl, Cape.toNoun_inj _ _ hi, Cape.toNoun_inj _ _ hs,
    Sock.toNoun_inj _ _ hp, hm, unitNoun_id_inj ha]

theorem memoNoun_inj {a b : Memo FinMap} (h : memoNoun a = memoNoun b) : a = b := by
  refine FinMap.toNoun_inj' (fun x y e => FinMap.toNoun_inj' (fun u w e' => ?_) e) h
  obtain ⟨i1, d1⟩ := u
  obtain ⟨i2, d2⟩ := w
  simp only [entryNoun, Noun.cell.injEq] at e'
  rw [TKey.enc_inj i1 i2 e'.1, fdatum_toNoun_inj e'.2]

/-! ## The encoding -/

/-- The model's state with the pill's types: `J` the noun of `jets` of
`long-ska`, `H` that of `jets-hot`, `CR` those of `inl` and `sure`. -/
abbrev PSt := CSt FinMap (TreapMap mugF) Noun Noun (Noun × Noun)

/-- The flags `[pure total]` of the entry of a bell of a table, as the pill
stores them next to the nomm (not in the model: mismatch P1). -/
abbrev Flags := FinMap Bell (VarEntry FinMap) → Bell → Noun

/-- The noun of `code.long-ska`: `[nomm pure total]` by bell. -/
noncomputable def codeNoun (fl : Flags) (code : FinMap Bell (VarEntry FinMap)) : Noun :=
  (FinMap.mapK (fun b e => C e.nomm.toNoun (fl code b)) code).toNoun fun x => x

/-- `long-ska` = `[jets memo code calls vars seek]`. -/
noncomputable def longNoun (fl : Flags) (j : Noun) (L : LongB FinMap) : Noun :=
  C j (C (memoNoun L.memo) (C (codeNoun fl L.code)
    (C (L.code.toNoun fun e => FinMap.setNoun e.calls)
      (C (L.vars.toNoun FinMap.setNoun) (L.code.toNoun fun e => e.seek.toNoun)))))

/-- `comp-cache` = `[nary mono sccs inl sure]`. -/
noncomputable def cacheNoun (c : Cache FinMap (TreapMap mugF) (Noun × Noun)) : Noun :=
  C (c.nary.toNoun Straight.toNoun) (C (c.mono.toNoun Straight.toNoun)
    (C (c.sccs.toNoun FinMap.setNoun) (C c.rest.1 c.rest.2)))

/-- `state-0` = `[%0 long-ska jets-hot cache]`. -/
noncomputable def stNoun (fl : Flags) (st : PSt) : Noun :=
  C (A 0) (C (longNoun fl st.jets st.long) (C st.hot (cacheNoun st.cache)))

/-- The parts of `cor` around the state: the two batteries and the library. -/
def corB2 : Noun := match cor with | Noun.cell h _ => h | Noun.atom _ => A 0
def corB6 : Noun := match cor with | Noun.cell _ (Noun.cell h _) => h | _ => A 0
def corLib : Noun := match cor with | Noun.cell _ (Noun.cell _ (Noun.cell _ t)) => t | _ => A 0

/-- **`enc`**: the compiler's core with the state `st`. -/
noncomputable def enc (fl : Flags) (st : PSt) : Noun := C corB2 (C corB6 (C (stNoun fl st) corLib))

/-- The table of `VarEntry`s from its three nouns. -/
theorem code_inj {fl fl' : Flags} {c c' : FinMap Bell (VarEntry FinMap)}
    (h1 : codeNoun fl c = codeNoun fl' c')
    (h2 : (c.toNoun fun e => FinMap.setNoun e.calls) = c'.toNoun fun e => FinMap.setNoun e.calls)
    (h3 : (c.toNoun fun e => e.seek.toNoun) = c'.toNoun fun e => e.seek.toNoun) : c = c' := by
  apply Subtype.ext; funext k
  have p1 := FinMap.toNoun_pairs h1 k
  have p2 := FinMap.toNoun_pairs h2 k
  have p3 := FinMap.toNoun_pairs h3 k
  simp only [FinMap.mapK, Option.map_map] at p1
  cases e : c.1 k <;> cases e' : c'.1 k <;> simp_all
  rename_i v v'
  obtain ⟨n, cl, sk⟩ := v
  obtain ⟨n', cl', sk'⟩ := v'
  simp only [Function.comp, Noun.cell.injEq] at p1
  simp only at p2 p3
  rw [nomm_toNoun_inj p1.1, FinMap.setNoun_inj p2, Cape.toNoun_inj _ _ p3]

/-- **`enc` is injective**, for every choice of the flags. -/
theorem enc_inj (fl : Flags) : ∀ a b : PSt, enc fl a = enc fl b → a = b := by
  intro a b h
  obtain ⟨⟨am, ac, av⟩, aj, ah, ⟨amo, ana, asc, ar⟩⟩ := a
  obtain ⟨⟨bm, bc, bv⟩, bj, bh, ⟨bmo, bna, bsc, br⟩⟩ := b
  simp only [enc, stNoun, longNoun, cacheNoun, Noun.cell.injEq] at h
  obtain ⟨-, -, ⟨-, ⟨hj, hm, hc1, hc2, hv, hc3⟩, hh, hna, hmo, hsc, hr1, hr2⟩, -⟩ := h
  have hr : ar = br := Prod.ext hr1 hr2
  rw [memoNoun_inj hm, code_inj hc1 hc2 hc3, FinMap.toNoun_inj' (fun _ _ e => FinMap.setNoun_inj e) hv,
    hj, hh, FinMap.toNoun_inj' (fun _ _ e => straight_toNoun_inj e) hna,
    FinMap.toNoun_inj' (fun _ _ e => straight_toNoun_inj e) hmo,
    FinMap.toNoun_inj' (fun _ _ e => FinMap.setNoun_inj e) hsc, hr]

/-! ## Leaf 4.1: `cor` is the encoding of the empty state -/

/-- `jets` of the bunt `long-ska`: `[root core batt arms pend [call back]]`, all `~`. -/
def jets0 : Noun := C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))

/-- The empty state, as `gap_of` names it, with the pill's bunt nouns. -/
noncomputable def emptySt : PSt :=
  ⟨⟨Treap.empty, Treap.empty, Treap.empty⟩, jets0, A 0, ⟨Treap.empty, Treap.empty, Treap.empty, (A 0, A 0)⟩⟩

theorem stNoun_empty (fl : Flags) :
    stNoun fl emptySt = C (A 0) (C (C jets0 (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))) (C (A 0)
      (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))) := by
  have e : ∀ {ν : Type} {κ : Type} [TKey κ] (f : ν → Noun), FinMap.toNoun f (Treap.empty : FinMap κ ν) = A 0 :=
    fun f => FinMap.toNoun_of_none (fun _ => rfl)
  have em : memoNoun (Treap.empty : Memo FinMap) = A 0 := e _
  have ec : ∀ fl : Flags, codeNoun fl (Treap.empty : FinMap Bell (VarEntry FinMap)) = A 0 :=
    fun _ => FinMap.toNoun_of_none (fun _ => rfl)
  simp only [stNoun, longNoun, cacheNoun, emptySt, em, ec, e]

/-- The pill's `cor` around its state: axis `14` is the bunt `state-0`. -/
theorem cor_parts : cor = C corB2 (C corB6 (C (C (A 0) (C (C jets0 (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))
    (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))) corLib)) := by
  kernel_rfl

/-- **Leaf 4.1**: the pill's compiler core is the encoding of the empty state:
empty memo, code table, variants and caches (for every choice of the flags). -/
theorem cor_enc (fl : Flags) : cor = enc fl emptySt := by
  rw [enc, stNoun_empty]; exact cor_parts

/-- `cor` is the encoding of a state of the shape `gap_of` names. -/
theorem cor_enc_gap (fl : Flags) : ∃ jets hot rest,
    cor = enc fl ⟨⟨Treap.empty, Treap.empty, Treap.empty⟩, jets, hot,
      ⟨Treap.empty, Treap.empty, Treap.empty, rest⟩⟩ :=
  ⟨jets0, A 0, (A 0, A 0), cor_enc fl⟩

/-! ## What the cores the pill reaches must be -/

/-- **The image condition of `liftPoke`** (leaf 1.1, open): every core the
pill reaches by pokes encodes a state.  Its `start` case is `cor_enc`; the
`poke` case is what the links of `+poke` give (the pill writes only treaps
of decodable pairs), with the flags (P1) the one part not in the model. -/
def PokeReachEnc (fl : Flags) : Prop := ∀ cr, PokeReach cr → ∃ st, enc fl st = cr

/-- The start of `PokeReachEnc`. -/
theorem pokeReachEnc_start (fl : Flags) : ∃ st, enc fl st = cor := ⟨emptySt, (cor_enc fl).symm⟩

end Compiler
end Formalization
