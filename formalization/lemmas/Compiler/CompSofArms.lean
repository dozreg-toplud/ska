import lemmas.Compiler.CompSofSoft
import lemmas.Compiler.CompSofPush
import lemmas.Ska.DatFacts

/-!
# `SofArms` discharged (README Gaps 19, item (f))

The two arm facts of `CompSofPush.lean` from the links of `+sound-far`
(`sf_gate`) and `+need-soft` (`ns_gate`) and the totality of the models
(`soundFar_some`, `needSoft_some`):

* `nommOf CODE`: the nomms of the entries of `code.long-ska`, as a table
  (`CodeNomms`, `codeNomms_nommOf`).
* `SfTable cod`: every nomm of the table has no `%10` at axis `0` on its
  product path and an entry for every callee there (`sfTable_of`: from
  `Bake.NoAx0`, the fact `folMade_noAx0` gives for the analysis's nomms).
* **`soundFarRet_of`**, **`needSoftRet_of`**: the arm facts.
* **`sofArms_code`**: `SofArms` at every direct call of a `DirOk` nomm whose
  callees have nomm entries and a sock that is not `%void`.
* **`cu_gate_dir_code`**: the gate of `+compile-unary` on `DirOk` without the
  arm hypothesis of `cu_gate_dir_arms`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-! ## The code table of `code.long-ska` -/

/-- **The nomm of the entry of `b`** in the map noun `CODE`: the nomm whose
noun is at axis `2` of the value, `none` when there is none. -/
noncomputable def nommOf (CODE : Noun) (b : Bell) : Option Nomm :=
  open Classical in
  if h : ∃ m : Nomm, ∃ V, getF mugF b.toNoun CODE = some (C (A 0) V) ∧ slot? 2 V = some m.toNoun
  then some (Classical.choose h) else Option.none

theorem codeNomms_nommOf (CODE : Noun) : CodeNomms (nommOf CODE) CODE := by
  intro b m h
  unfold nommOf at h
  split at h
  · rename_i hx
    cases h
    obtain ⟨V, hV⟩ := Classical.choose_spec hx
    exact ⟨V, hV⟩
  · cases h

theorem nommOf_some {CODE : Noun} {b : Bell} {m : Nomm} {V : Noun}
    (hg : getF mugF b.toNoun CODE = some (C (A 0) V)) (hv : slot? 2 V = some m.toNoun) :
    ∃ m', nommOf CODE b = some m' := by
  unfold nommOf
  rw [dif_pos ⟨m, V, hg, hv⟩]
  exact ⟨_, rfl⟩

/-! ## A code table closed for `+sound-far` -/

/-- **The table is closed for `+sound-far`**: every nomm in it has no `%10`
at axis `0` on its product path, and every callee on that path has an
entry. -/
def SfTable (cod : Bell → Option Nomm) : Prop :=
  ∀ b m, cod b = some m → SfNoAx0 m ∧ ∀ b' ∈ sfBells m, ∃ m', cod b' = some m'

theorem sfNoAx0_of_noAx0 : ∀ n : Nomm, Bake.NoAx0 n → SfNoAx0 n
  | Nomm.cons p q, h => ⟨sfNoAx0_of_noAx0 p h.1, sfNoAx0_of_noAx0 q h.2⟩
  | Nomm.n6 _ q r, h => ⟨sfNoAx0_of_noAx0 q h.2.1, sfNoAx0_of_noAx0 r h.2.2⟩
  | Nomm.n7 _ q, h => sfNoAx0_of_noAx0 q h.2
  | Nomm.n11s _ q _, h => sfNoAx0_of_noAx0 q h
  | Nomm.n11d _ _ q _, h => sfNoAx0_of_noAx0 q h.2
  | Nomm.mean _ _ q _ _, h => sfNoAx0_of_noAx0 q h.2
  | Nomm.n10 a v q, h => ⟨Nat.pos_of_ne_zero h.1, sfNoAx0_of_noAx0 v h.2.1, sfNoAx0_of_noAx0 q h.2.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 _ _ _, _ => trivial
  | Nomm.n3 _, _ => trivial
  | Nomm.n4 _, _ => trivial
  | Nomm.n5 _ _, _ => trivial
  | Nomm.n12 _ _, _ => trivial

/-- `SfTable` from `Bake.NoAx0` of every nomm in the table and an entry for
every callee on the product path. -/
theorem sfTable_of {cod : Bell → Option Nomm}
    (h : ∀ b m, cod b = some m → Bake.NoAx0 m ∧ ∀ b' ∈ sfBells m, ∃ m', cod b' = some m') : SfTable cod :=
  fun b m hm => ⟨sfNoAx0_of_noAx0 m (h b m hm).1, (h b m hm).2⟩

theorem sfClosed_of_table {cod : Bell → Option Nomm} (ht : SfTable cod) :
    ∀ (d : Nat) (nom : Nomm), SfNoAx0 nom → (∀ b ∈ sfBells nom, ∃ m, cod b = some m) → SfClosed cod d nom
  | 0, _, h0, _ => h0
  | d + 1, nom, h0, hb => ⟨h0, fun b mem => by
      obtain ⟨m, hm⟩ := hb b mem
      exact ⟨m, hm, sfClosed_of_table ht d m (ht b m hm).1 (ht b m hm).2⟩⟩

/-! ## The arm facts -/

/-- **`+sound-far` returns** on a nomm closed at depth `3` for the table of
`CODE`. -/
theorem soundFarRet_of {CODE : Noun} {nom : Nomm} (h : SfClosed (nommOf CODE) 3 nom) (ned : NeedOrd) :
    SoundFarRet nom ned CODE := by
  obtain ⟨s, hs⟩ := soundFar_some (nommOf CODE) 3 nom h ned
  exact ⟨s, sf_gate (nommOf CODE) CODE (codeNomms_nommOf CODE) 3 nom ned s hs⟩

/-- **`+need-soft` returns** on every sock but `%void`. -/
theorem needSoftRet_of (ned sur : NeedOrd) {k : Sock} (hk : k ≠ Sock.void) : NeedSoftRet ned sur k := by
  obtain ⟨s, hs⟩ := needSoft_some ned sur k hk
  exact ⟨s, ns_gate ned sur k s hs⟩

/-! ## Every call -/

theorem sfNoAx0_of_dirOk : ∀ n : Nomm, DirOk n = true → SfNoAx0 n
  | Nomm.cons p q, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨sfNoAx0_of_dirOk p h.1, sfNoAx0_of_dirOk q h.2⟩
  | Nomm.n6 _ q r, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨sfNoAx0_of_dirOk q h.1.2, sfNoAx0_of_dirOk r h.2⟩
  | Nomm.n7 _ q, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact sfNoAx0_of_dirOk q h.2
  | Nomm.n10 a v q, h => by
    simp only [DirOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨Nat.pos_of_ne_zero h.1.1, sfNoAx0_of_dirOk v h.1.2, sfNoAx0_of_dirOk q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 _ _ _, _ => trivial
  | Nomm.n3 _, _ => trivial
  | Nomm.n4 _, _ => trivial
  | Nomm.n5 _ _, _ => trivial
  | Nomm.n12 _ _, h => by simp [DirOk] at h
  | Nomm.n11s _ _ _, h => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [DirOk] at h

theorem sfBells_sub : ∀ (n : Nomm), DirOk n = true → ∀ b, b ∈ sfBells n → b ∈ dirBells n
  | Nomm.cons p q, hd, b, h => by
    simp only [DirOk, Bool.and_eq_true] at hd
    simp only [sfBells, dirBells, List.mem_append] at h ⊢
    exact h.imp (sfBells_sub p hd.1 b) (sfBells_sub q hd.2 b)
  | Nomm.n6 p q r, hd, b, h => by
    simp only [DirOk, Bool.and_eq_true] at hd
    simp only [sfBells, dirBells, List.mem_append] at h ⊢
    exact h.elim (fun m => Or.inl (Or.inr (sfBells_sub q hd.1.2 b m))) (fun m => Or.inr (sfBells_sub r hd.2 b m))
  | Nomm.n7 p q, hd, b, h => by
    simp only [DirOk, Bool.and_eq_true] at hd
    simp only [sfBells, dirBells, List.mem_append] at h ⊢
    exact Or.inr (sfBells_sub q hd.2 b h)
  | Nomm.n10 _ v q, hd, b, h => by
    simp only [DirOk, Bool.and_eq_true] at hd
    simp only [sfBells, dirBells, List.mem_append] at h ⊢
    exact h.imp (sfBells_sub v hd.1.2 b) (sfBells_sub q hd.2 b)
  | Nomm.n2 _ _ (some (b0, _)), _, b, h => by
    simp only [sfBells, dirBells, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
    exact Or.inl h
  | Nomm.n2 _ _ Option.none, _, b, h => by simp [sfBells] at h
  | Nomm.n0 _, _, b, h => by simp [sfBells] at h
  | Nomm.n1 _, _, b, h => by simp [sfBells] at h
  | Nomm.n3 _, _, b, h => by simp [sfBells] at h
  | Nomm.n4 _, _, b, h => by simp [sfBells] at h
  | Nomm.n5 _ _, _, b, h => by simp [sfBells] at h
  | Nomm.n12 _ _, _, b, h => by simp [sfBells] at h
  | Nomm.n11s _ _ _, hd, _, _ => by simp [DirOk] at hd
  | Nomm.n11d _ _ _ _, hd, _, _ => by simp [DirOk] at hd
  | Nomm.mean _ _ _ _ _, hd, _, _ => by simp [DirOk] at hd

theorem made_cases (p : Nomm) (ms : Option Nomm) : made p ms = p ∨ ∃ m, ms = some m ∧ made p ms = m := by
  unfold made; split <;> simp_all

/-- What a callee needs for the arm facts: an entry with a nomm, and a sock
that is not `%void`. -/
def SofBell (CODE : Noun) (b : Bell) : Prop := (∃ m, nommOf CODE b = some m) ∧ b.less ≠ Sock.void

/-- `SoundFarRet` on a nomm of `DirOk` whose callees are `SofBell`, in a
closed table. -/
theorem soundFarRet_dir {CODE : Noun} (ht : SfTable (nommOf CODE)) {X : Nomm} (hX : DirOk X = true)
    (hb : ∀ b ∈ dirBells X, SofBell CODE b) (ned : NeedOrd) : SoundFarRet X ned CODE :=
  soundFarRet_of (sfClosed_of_table ht 3 X (sfNoAx0_of_dirOk X hX)
    (fun b m => (hb b (sfBells_sub X hX b m)).1)) ned

/-- **`SofArms` at every direct call** of a `DirOk` nomm whose callees are
`SofBell`, at a `msup` whose nomm is `DirOk` with `SofBell` callees, for
a table of `CODE` closed for `+sound-far`. -/
theorem sofArms_code {env : CallEnv} {CODE : Noun} (ht : SfTable (nommOf CODE)) :
    ∀ (ms : Option Nomm) (n : Nomm), DirOk n = true → (∀ b ∈ dirBells n, SofBell CODE b) →
      (∀ m, ms = some m → DirOk m = true ∧ ∀ b ∈ dirBells m, SofBell CODE b) → SofArms env CODE ms n
  | ms, Nomm.cons p q, h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofArms_code ht ms p h.1 (fun b m => hb b (Or.inl m)) hm,
      sofArms_code ht ms q h.2 (fun b m => hb b (Or.inr m)) hm⟩
  | _, Nomm.n0 _, _, _, _ => trivial
  | _, Nomm.n1 _, _, _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofArms_code ht ms p h.1 (fun b m => hb b (Or.inl m)) hm,
      sofArms_code ht ms q h.2 (fun b m => hb b (Or.inr m)) hm⟩
  | ms, Nomm.n2 p q (some (b0, Option.none)), h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_cons, List.mem_append] at hb
    have hbp : ∀ b ∈ dirBells p, SofBell CODE b := fun b m => hb b (Or.inr (Or.inl m))
    refine ⟨fun nb _ => ⟨?_, needSoftRet_of nb (env.sure b0) (hb b0 (Or.inl rfl)).2⟩,
      sofArms_code ht ms p h.1 hbp hm, sofArms_code ht ms q h.2 (fun b m => hb b (Or.inr (Or.inr m))) hm⟩
    rcases made_cases p ms with e | ⟨m, rfl, e⟩
    · rw [e]; exact soundFarRet_dir ht h.1 hbp nb
    · rw [e]; exact soundFarRet_dir ht (hm m rfl).1 (hm m rfl).2 nb
  | _, Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [DirOk] at h
  | ms, Nomm.n3 p, h, hb, hm => by simp only [DirOk] at h; exact sofArms_code ht ms p h hb hm
  | ms, Nomm.n4 p, h, hb, hm => by simp only [DirOk] at h; exact sofArms_code ht ms p h hb hm
  | ms, Nomm.n5 p q, h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofArms_code ht ms p h.1 (fun b m => hb b (Or.inl m)) hm,
      sofArms_code ht ms q h.2 (fun b m => hb b (Or.inr m)) hm⟩
  | ms, Nomm.n6 p q r, h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofArms_code ht ms p h.1.1 (fun b m => hb b (Or.inl (Or.inl m))) hm,
      sofArms_code ht ms q h.1.2 (fun b m => hb b (Or.inl (Or.inr m))) hm,
      sofArms_code ht ms r h.2 (fun b m => hb b (Or.inr m)) hm⟩
  | ms, Nomm.n7 p q, h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofArms_code ht ms p h.1 (fun b m => hb b (Or.inl m)) hm,
      sofArms_code ht (some p) q h.2 (fun b m => hb b (Or.inr m))
        (fun m e => by cases e; exact ⟨h.1, fun b m => hb b (Or.inl m)⟩)⟩
  | ms, Nomm.n10 _ v q, h, hb, hm => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofArms_code ht ms v h.1.2 (fun b m => hb b (Or.inl m)) hm,
      sofArms_code ht ms q h.2 (fun b m => hb b (Or.inr m)) hm⟩
  | _, Nomm.n11s _ _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.n11d _ _ _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.n12 _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.mean _ _ _ _ _, h, _, _ => by simp [DirOk] at h

/-- **The gate of `+compile-unary` on `DirOk` with direct calls, item (f)
discharged** (README Gaps 19): `cu_gate_dir_arms` with `SofArms` from
`sofArms_code`.  On the arms it takes, in place of `harm`, facts of the
code table: every callee of `n` has an entry whose head is a nomm and a
sock that is not `%void` (`SofBell`), and the table of `CODE` is closed for
`+sound-far` (`SfTable`, e.g. by `sfTable_of` from `Bake.NoAx0`). -/
theorem cu_gate_dir_code (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE) (hcr : CodeNoRing CODE COLE n)
    (hn : DirOk n = true) (he : EnvFrom env CODE COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hneed : CsiNeeds env SCC NM CA n) (hsure : CsiSures env CA n)
    (htab : SfTable (nommOf CODE)) (hbell : ∀ b ∈ dirBells n, SofBell CODE b) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA :=
  cu_gate_dir_arms FUNC SCC CODE LSR JH CACHE NM CA V COLE env n hgot hv hcl hcr hn he hcsi hneed hsure
    (sofArms_code htab Option.none n hn hbell (fun _ e => by cases e))

end Compiler
end Formalization
