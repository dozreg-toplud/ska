import lemmas.Ska.CompHintCls
import lemmas.Ska.CompHintTreeEx
import lemmas.Ska.CompHintSpotEx
import lemmas.Ska.CompHintRegEx
import lemmas.Ska.CompSevenMink

/-!
# The class of hinted nomms: the theorem (README Gaps 24.22)

* `hcLeaf_sound`: a leaf is a direct-free member of `CallTreeHU` at every
  subject predicate, its `+hinted` independent of the table.
* `hcNB_noBond`: `hcNB` gives `NoBondH`.
* `HVOK`: what each field of `HV` promises; `hvLeaf_ok`, `hvKeptD_ok`,
  `hvMean_ok`, `hvDirect_ok`, `hvSur3_ok`, `topKF_ok` (the d13 rule), the
  `%6` pieces `hcTest_ok`, `hcBranch_ok`, the `[7 [0 1] q]` texts at one `P`.
* **`hcV_sound`**: every field of `hcV snd f nm` holds, under `HintTab` and
  `FitH`, by induction on `nm`.
* **`hintCls_contract`**: every member (`top`) has both halves of the
  contract at the top, traces included.
* Re-derived by membership: `contract_spotArmC`, `contract_d10C`,
  `contract_d13C`, `contract_d18C`, `contract_d20C`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Leaves and clues -/

/-- **A leaf is a direct-free member of `CallTreeHU`**, and its `+hinted` is
the same with any table. -/
theorem hcLeaf_sound (lib : Lib) (env : CallEnv) (N : Needs) :
    ∀ (nm : Nomm) (f : Noun) (x : Bool), hcLeaf f nm = some x →
      (∀ cod, hinted cod nm = hinted0 nm) ∧ ∀ P, CallTreeHU lib env N P x f nm
  | Nomm.n0 a, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n0 a = Nomm.n0 _›
    split at h
    · next he => cases h; subst he; exact ⟨fun _ => rfl, fun P => CallTreeHU.base (CallTreeD.n0 _) rfl⟩
    · cases h
  | Nomm.n1 k, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n1 k = Nomm.n1 _›
    split at h
    · next he => cases h; subst he; exact ⟨fun _ => rfl, fun P => CallTreeHU.base (CallTreeD.n1 _) rfl⟩
    · cases h
  | Nomm.cons p q, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.cons p q = Nomm.cons _ _›
    split at h <;> try contradiction
    rename_i x1 x2 h1 h2
    cases h
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N p _ _ h1
    obtain ⟨e2, T2⟩ := hcLeaf_sound lib env N q _ _ h2
    refine ⟨fun cod => ?_, fun P => ?_⟩
    · show orB (hinted cod p) (hinted cod q) = orB (hinted0 p) (hinted0 q)
      rw [e1, e2]
    · have T := CallTreeHU.cons (T1 P) (T2 P)
      rwa [e2] at T
  | Nomm.n2 p q info, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n2 p q info = Nomm.n2 _ _ _›
    split at h <;> try contradiction
    rename_i x1 x2 h1 h2
    cases h
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N p _ _ h1
    obtain ⟨e2, T2⟩ := hcLeaf_sound lib env N q _ _ h2
    exact ⟨fun cod => rfl, fun P => CallTreeHU.ind (T1 P) (T2 P)⟩
  | Nomm.n3 p, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n3 p = Nomm.n3 _›
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨y, h1, rfl⟩ := h
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N p _ _ h1
    exact ⟨fun cod => e1 cod, fun P => CallTreeHU.three (T1 P)⟩
  | Nomm.n4 p, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n4 p = Nomm.n4 _›
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨y, h1, rfl⟩ := h
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N p _ _ h1
    exact ⟨fun cod => e1 cod, fun P => CallTreeHU.four (T1 P)⟩
  | Nomm.n5 p q, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n5 p q = Nomm.n5 _ _›
    split at h <;> try contradiction
    rename_i x1 x2 h1 h2
    cases h
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N p _ _ h1
    obtain ⟨e2, T2⟩ := hcLeaf_sound lib env N q _ _ h2
    refine ⟨fun cod => ?_, fun P => CallTreeHU.five (T1 P) (T2 P)⟩
    show orB (hinted cod p) (hinted cod q) = orB (hinted0 p) (hinted0 q)
    rw [e1, e2]
  | Nomm.n7 p q, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n7 p q = Nomm.n7 _ _›
    split at h <;> try contradiction
    rename_i h1
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N p _ _ h1
    obtain ⟨e2, T2⟩ := hcLeaf_sound lib env N q _ _ h
    refine ⟨fun cod => ?_, fun P => CallTreeHU.seven (T1 P) (T2 _)⟩
    show orB (hinted cod p) (hinted cod q) = orB (hinted0 p) (hinted0 q)
    rw [e1, e2]
  | Nomm.n11s tag q body, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n11s tag q body = Nomm.n11s _ _ _›
    split at h <;> try contradiction
    rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨rfl, hs⟩ := hc
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N q _ _ h
    refine ⟨fun cod => ?_, fun P => CallTreeHU.n11s body (T1 P) hs⟩
    show orB (some (hintStatic _)) (hinted cod q) = orB (some (hintStatic _)) (hinted0 q)
    rw [e1]
  | Nomm.n11d tag hh q body, f, x, h => by
    unfold hcLeaf at h
    split at h <;> try contradiction
    cases ‹Nomm.n11d tag hh q body = Nomm.n11d _ _ _ _›
    split at h <;> try contradiction
    rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨⟨rfl, rfl⟩, hs⟩ := hc
    obtain ⟨e1, T1⟩ := hcLeaf_sound lib env N q _ _ h
    refine ⟨fun cod => ?_, fun P => CallTreeHU.n11d body (T1 P) hs rfl (ClueSafe.quote lib P _) rfl rfl⟩
    show orB (some (hintDynamic _)) (orB (some false) (hinted cod q)) =
      orB (some (hintDynamic _)) (orB (some false) (hinted0 q))
    rw [e1]
  | Nomm.n6 _ _ _, f, x, h => by unfold hcLeaf at h; split at h <;> contradiction
  | Nomm.n10 _ _ _, f, x, h => by unfold hcLeaf at h; split at h <;> contradiction
  | Nomm.n12 _ _, f, x, h => by unfold hcLeaf at h; split at h <;> contradiction
  | Nomm.mean _ _ _ _ _, f, x, h => by unfold hcLeaf at h; split at h <;> contradiction

theorem hcNB_hinted : ∀ (nm : Nomm), hcNB nm = true → ∀ cod, hinted cod nm = some false
  | Nomm.n0 _, _, _ => rfl
  | Nomm.n1 _, _, _ => rfl
  | Nomm.n4 p, h, cod => by simp only [hcNB] at h; exact hcNB_hinted p h cod
  | Nomm.cons p q, h, cod => by
    simp only [hcNB, Bool.and_eq_true] at h
    show orB (hinted cod p) (hinted cod q) = some false
    rw [hcNB_hinted p h.1.1.1 cod, hcNB_hinted q h.1.1.2 cod]; rfl
  | Nomm.n2 _ _ _, h, _ => by simp [hcNB] at h
  | Nomm.n3 _, h, _ => by simp [hcNB] at h
  | Nomm.n5 _ _, h, _ => by simp [hcNB] at h
  | Nomm.n6 _ _ _, h, _ => by simp [hcNB] at h
  | Nomm.n7 _ _, h, _ => by simp [hcNB] at h
  | Nomm.n10 _ _ _, h, _ => by simp [hcNB] at h
  | Nomm.n11s _ _ _, h, _ => by simp [hcNB] at h
  | Nomm.n11d _ _ _ _, h, _ => by simp [hcNB] at h
  | Nomm.n12 _ _, h, _ => by simp [hcNB] at h
  | Nomm.mean _ _ _ _ _, h, _ => by simp [hcNB] at h

section
variable {snd : Nomm → NeedOrd → Bool} {env : CallEnv}

/-- **`hcNB` gives `NoBondH`.** -/
theorem hcNB_noBond : ∀ (nm : Nomm), hcNB nm = true → NoBondH (S := S) (Map := Map) snd env nm
  | Nomm.n0 a, _ => noBondH_n0 a
  | Nomm.n1 k, _ => noBondH_n1 k
  | Nomm.n4 p, h => by simp only [hcNB] at h; exact noBondH_n4 (hcNB_noBond p h)
  | Nomm.cons p q, h => by
    simp only [hcNB, Bool.and_eq_true] at h
    exact noBondH_cons (hcNB_noBond p h.1.1.1) (hcNB_noBond q h.1.1.2)
      (by rw [hcNB_hinted p h.1.1.1]; simp) (by rw [hcNB_hinted q h.1.1.2]; simp)
  | Nomm.n2 _ _ _, h => by simp [hcNB] at h
  | Nomm.n3 _, h => by simp [hcNB] at h
  | Nomm.n5 _ _, h => by simp [hcNB] at h
  | Nomm.n6 _ _ _, h => by simp [hcNB] at h
  | Nomm.n7 _ _, h => by simp [hcNB] at h
  | Nomm.n10 _ _ _, h => by simp [hcNB] at h
  | Nomm.n11s _ _ _, h => by simp [hcNB] at h
  | Nomm.n11d _ _ _ _, h => by simp [hcNB] at h
  | Nomm.n12 _ _, h => by simp [hcNB] at h
  | Nomm.mean _ _ _ _ _, h => by simp [hcNB] at h

end

/-! ## What the fields promise -/

/-- The result of a direct call `[2 [0 1] q b]` under `%next (lazy-from-reg r)`:
no entry, a `RegLike` need (`directZ_shape`, the premise `hq` of `regGBT_sevenS`). -/
def ZRun (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure (lazyReg rg)) th) region g0 =
      some (nx, g1) → entries nx.laz = [] ∧ RegLike nx.laz.sure

/-- **What each field of `HV` promises** of `(f, nm)` at the subject predicate `P`. -/
structure HVOK (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    (f : Noun) (nm : Nomm) (v : HV) : Prop where
  leaf : ∀ x, v.leaf = some x → hcLeaf f nm = some x
  sur : v.sur = true → SurGBT (S := S) (Map := Map) snd lib N env P RegLike f nm
  reg : v.reg = true → RegGBT (S := S) (Map := Map) snd lib N env P f nm
  ft : v.ft = true → RegFT (S := S) (Map := Map) snd lib N env P f nm
  zc : v.zc = true → v.ft = true ∧ ZRun (S := S) (Map := Map) env snd nm
  dall : v.dall = true → DoneAllT (S := S) (Map := Map) lib N env snd P f nm
  top : v.top = true → DoneG (S := S) (Map := Map) lib N env snd P f nm
  sh : ∀ k, v.sh = some k → ShapeH (S := S) (Map := Map) snd env IsReg nm k

section
variable {lib : Lib} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {N : Needs} {P : Noun → Prop}

theorem hvNone_ok {f : Noun} {nm : Nomm} : HVOK (S := S) (Map := Map) lib env snd N P f nm {} :=
  ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun h => (by cases h),
    fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩

/-- **A leaf meets every field** (`LOKSFH` through `lokSHU_callTreeHU`). -/
theorem hvLeafC_ok {f : Noun} {nm : Nomm} {x : Bool} (hx : hcLeaf f nm = some x) (c : Bool) :
    HVOK (S := S) (Map := Map) lib env snd N P f nm { hvLeaf x nm with clue := c } := by
  have T := (hcLeaf_sound lib env N nm f x hx).2 P
  have L := (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1
  have hc : sixCount nm ≤ 255 := by rw [T.sixCount]; omega
  refine ⟨fun y hy => ?_, fun _ => SurGBT.of_loksf RegLike L hc, fun _ => RegGBT.of_loksf L hc,
    fun _ => RegFT.of_loksf L hc, fun h => by simp [hvLeaf] at h, fun _ => doneAllT_callTreeHU lib env T,
    fun _ => DoneAllT.toG (doneAllT_callTreeHU lib env T), fun k hk => ?_⟩
  · simp only [hvLeaf, Option.some.injEq] at hy; rw [hx, hy]
  · cases nm with
    | n0 a =>
      simp only [hvLeaf] at hk
      split at hk
      · next h2 => cases hk; exact shapeH_n0 IsReg h2
      · cases hk
    | _ => simp [hvLeaf] at hk

theorem hvLeaf_ok {f : Noun} {nm : Nomm} {x : Bool} (hx : hcLeaf f nm = some x) :
    HVOK (S := S) (Map := Map) lib env snd N P f nm (hvLeaf x nm) :=
  hvLeafC_ok hx false

/-- **A kept dynamic hint, its `sur` and `reg` parts** (`surGBT_n11dKept`,
`surGBT_n11dQuiet` with `regLike_soundFit`; `regGBT_n11dKept`, `regGBT_n11dQuiet`). -/
theorem keptD_parts {tag : Nat} {fh fq : Noun} {h q : Nomm} {body : Noun} {vq : HV}
    (hs : hintDynamic tag = true) (V : HVOK (S := S) (Map := Map) lib env snd N P fq q vq)
    (hok : ((hcLeaf fh h).isSome && hcNB h && snd q NeedOrd.this) = true) :
    (vq.sur = true → SurGBT (S := S) (Map := Map) snd lib N env P RegLike
      (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) fh) fq)) (Nomm.n11d tag h q body)) ∧
    (vq.reg = true → RegGBT (S := S) (Map := Map) snd lib N env P
      (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) fh) fq)) (Nomm.n11d tag h q body)) := by
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hok
  obtain ⟨⟨⟨x, hx⟩, hnb⟩, hsnd⟩ := hok
  have T := (hcLeaf_sound lib env N h fh x hx).2 P
  have Lh := (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1
  have hch : sixCount h ≤ 255 := by rw [T.sixCount]; omega
  have hnh : NoBondH (S := S) (Map := Map) snd env h := hcNB_noBond h hnb
  cases hst : stopTag tag
  · exact ⟨fun hv => SurGBT.mono (fun s hs' => ⟨hs', (regLike_soundFit hsnd lib P fq hs').1⟩)
        (surGBT_n11dQuiet (V.sur hv) Lh hch hnh hs hst body),
      fun hv => regGBT_n11dQuiet (V.reg hv) hsnd Lh hch hnh hs hst body⟩
  · exact ⟨fun hv => SurGBT.mono (fun s hs' => ⟨hs', regLike_soundFit hsnd lib P fq hs'⟩)
        (surGBT_n11dKept (V.sur hv) Lh hch hnh hs hst body),
      fun hv => regGBT_n11dKept (V.reg hv) hsnd Lh hch hnh hs hst body⟩

/-- **A kept dynamic hint meets its fields** (`hvKeptD`). -/
theorem hvKeptD_ok {tag : Nat} {fh fq : Noun} {h q : Nomm} {body : Noun} {vq : HV}
    (hs : hintDynamic tag = true) (V : HVOK (S := S) (Map := Map) lib env snd N P fq q vq) (c1 : Bool)
    (hc1 : c1 = true → ∃ k, h = Nomm.n1 k) :
    HVOK (S := S) (Map := Map) lib env snd N P
      (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) fh) fq)) (Nomm.n11d tag h q body)
      (hvKeptD snd fh h q vq c1 (stopTag tag)) := by
  refine ⟨fun _ hh => by simp [hvKeptD] at hh, fun hh => ?_, fun hh => ?_, fun hh => by simp [hvKeptD] at hh,
    fun hh => by simp [hvKeptD] at hh, fun hh => ?_, fun hh => ?_, fun k hk => ?_⟩
  · simp only [hvKeptD, Bool.and_eq_true] at hh
    exact (keptD_parts hs V (by simp only [Bool.and_eq_true]; exact hh.1)).1 hh.2
  · simp only [hvKeptD, Bool.and_eq_true] at hh
    exact (keptD_parts hs V (by simp only [Bool.and_eq_true]; exact hh.1)).2 hh.2
  · simp only [hvKeptD, Bool.and_eq_true, Option.isSome_iff_exists] at hh
    obtain ⟨⟨⟨⟨⟨⟨x, hx⟩, hnb⟩, hsnd⟩, hst⟩, ⟨y, hy⟩⟩, hnq⟩ := hh
    have T := (hcLeaf_sound lib env N h fh x hx).2 P
    have Tq := (hcLeaf_sound lib env N q fq y (V.leaf y hy)).2 P
    intro sup region g0 g1 nex
    exact doneAllT_n11dKept (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env Tq).1.1
      (by rw [Tq.sixCount]; omega) (hcNB_noBond q hnq) hsnd
      (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1 (by rw [T.sixCount]; omega)
      (hcNB_noBond h hnb) hs hst body
  · simp only [hvKeptD, Bool.and_eq_true] at hh
    exact doneG_of_next ((keptD_parts hs V (by simp only [Bool.and_eq_true]; exact hh.1)).2 hh.2)
      (doneNext_n11d env hs h q body)
  · simp only [hvKeptD] at hk
    split at hk
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨k1, rfl⟩ := hc1 hc.1
      obtain ⟨k0, h0, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact shapeH_n11dKept hs k1 body (V.sh k0 h0) (isReg_sound hc.2)
    · cases hk

/-- **A `%mean` with no constant meets its fields** (the kept dynamic case,
`regGBT_mean`, `surGBT_mean`, `doneNext_mean`). -/
theorem hvMean_ok {fp fq : Noun} {p q : Nomm} {b : Bell} {body : Noun} {k : Option Noun} {vq : HV}
    (hk : meanKonst env b k = Option.none) (V : HVOK (S := S) (Map := Map) lib env snd N P fq q vq) :
    HVOK (S := S) (Map := Map) lib env snd N P
      (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom Tag.mean) fp) fq)) (Nomm.mean p b q body k)
      { hvKeptD snd fp p q vq false false with dall := false } := by
  have hs : hintDynamic Tag.mean = true := by decide
  refine ⟨fun _ hh => by simp [hvKeptD] at hh, fun hh => ?_, fun hh => ?_, fun hh => by simp [hvKeptD] at hh,
    fun hh => by simp [hvKeptD] at hh, fun hh => by simp at hh, fun hh => ?_, fun k hk => by simp [hvKeptD] at hk⟩
  · simp only [hvKeptD, Bool.and_eq_true] at hh
    exact surGBT_mean hk ((keptD_parts (body := body) hs V (by simp only [Bool.and_eq_true]; exact hh.1)).1 hh.2)
  · simp only [hvKeptD, Bool.and_eq_true] at hh
    exact regGBT_mean hk ((keptD_parts (body := body) hs V (by simp only [Bool.and_eq_true]; exact hh.1)).2 hh.2)
  · simp only [hvKeptD, Bool.and_eq_true] at hh
    exact doneG_of_next
      (regGBT_mean hk ((keptD_parts (body := body) hs V (by simp only [Bool.and_eq_true]; exact hh.1)).2 hh.2))
      (doneNext_mean hk)

/-- **A direct call's fields** from its `RegFT` and its `ZRun`. -/
theorem hvDirect_ok {f : Noun} {nm : Nomm} {o z : Bool}
    (FT : o = true → RegFT (S := S) (Map := Map) snd lib N env P f nm)
    (Z : z = true → o = true ∧ ZRun (S := S) (Map := Map) env snd nm) :
    HVOK (S := S) (Map := Map) lib env snd N P f nm { ft := o, reg := o, zc := z } :=
  ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => RegFT.toReg (FT h), FT, Z, fun h => (by cases h),
    fun h => (by cases h), fun _ h => (by cases h)⟩

/-- **A member of `SurGBT RegLike` whose `%done` run is the `%next` one**:
`sur`, `reg` (`SurGBT.toReg`), `top` (`doneG_of_next`). -/
theorem hvSur3_ok {f : Noun} {nm : Nomm} {o : Bool}
    (H : o = true → SurGBT (S := S) (Map := Map) snd lib N env P RegLike f nm)
    (hD : DoneNext (S := S) (Map := Map) env snd nm) :
    HVOK (S := S) (Map := Map) lib env snd N P f nm { sur := o, reg := o, top := o } :=
  ⟨fun _ h => (by cases h), H, fun h => SurGBT.toReg (H h), fun h => (by cases h), fun h => (by cases h),
    fun h => (by cases h), fun h => doneG_of_next (SurGBT.toReg (H h)) hD, fun _ h => (by cases h)⟩

end

/-! ## Formula transfers: `%9`, `%8` (`MinkC7`), a dropped hint over a constant (`MinkAs`) -/

section Transfer
variable {lib : Lib} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {N : Needs} {P : Noun → Prop}

/-- **A hint dropped over a constant is the constant** to `+mink`, at every
trace (the clue `[1 c]` cannot crash, the trace pushed is popped). -/
theorem minkAs_dropK {f k : Noun} (h : hcDropK f k = true) : MinkAs lib f (quote k) := by
  unfold hcDropK at h
  split at h
  · rename_i tag k'
    simp only [decide_eq_true_eq] at h; subst h
    refine ⟨fun {gul n tm s r} hm => ?_, fun {gul tm s r} hm => ?_⟩
    · cases n with
      | zero => simp [minkF] at hm
      | succ m => exact ⟨m, Nat.le_succ m, (minkF_n11s lib gul m tm s tag (quote k)).symm.trans hm⟩
    · obtain ⟨n, hn⟩ := hm
      exact ⟨n + 1, (minkF_n11s lib gul n tm s tag (quote k)).trans hn⟩
  · rename_i tag c k'
    simp only [decide_eq_true_eq] at h; subst h
    refine ⟨fun {gul n tm s r} hm => ?_, fun {gul tm s r} hm => ?_⟩
    · cases n with
      | zero => simp [minkF] at hm
      | succ m =>
        rw [minkF_n11d_any] at hm
        cases m with
        | zero => simp [minkF, tbind] at hm
        | succ j =>
          simp only [minkF_quote, tbind] at hm
          exact ⟨j + 1, by omega, by rw [minkF_quote]; exact hm⟩
    · obtain ⟨n, hn⟩ := hm
      cases n with
      | zero => simp [minkF] at hn
      | succ m =>
        rw [minkF_quote] at hn
        cases hn
        exact ⟨2, by rw [minkF_n11d_any]; rfl⟩
  · cases h

theorem SurGBT.minkAs' {Ap : Sure S → Prop} {f f' : Noun} {nm : Nomm} (M : MinkAs lib f' f)
    (H : SurGBT (S := S) (Map := Map) snd lib N env P Ap f nm) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap f' nm := by
  intro sup sur th region g0 g1 nex a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hr
  exact (H a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hr).minkAs M

theorem RegGBT.minkAs' {f f' : Noun} {nm : Nomm} (M : MinkAs lib f' f)
    (H : RegGBT (S := S) (Map := Map) snd lib N env P f nm) : RegGBT (S := S) (Map := Map) snd lib N env P f' nm := by
  intro sup rg th region g0 g1 nex a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hr
  exact (H a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hr).minkAs M

theorem RegFT.minkAs' {f f' : Noun} {nm : Nomm} (M : MinkAs lib f' f)
    (H : RegFT (S := S) (Map := Map) snd lib N env P f nm) : RegFT (S := S) (Map := Map) snd lib N env P f' nm := by
  intro sup rg th region g0 g1 nex a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hr
  have R := H a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hr
  exact ⟨R.run.minkAs M, R.nent, R.flat, R.clean, R.eclean⟩

theorem DoneAllT.minkAs' {f f' : Noun} {nm : Nomm} (M : MinkAs lib f' f)
    (H : DoneAllT (S := S) (Map := Map) lib N env snd P f nm) : DoneAllT (S := S) (Map := Map) lib N env snd P f' nm := by
  intro sup region g0 g1 nex a1 a2 a3 a4 a5 hr
  have D := H a1 a2 a3 a4 a5 hr
  exact ⟨D.run.minkAs M, D.nent, D.flat, D.clean, D.eclean⟩

theorem DoneG.minkAs' {f f' : Noun} {nm : Nomm} (M : MinkAs lib f' f)
    (H : DoneG (S := S) (Map := Map) lib N env snd P f nm) : DoneG (S := S) (Map := Map) lib N env snd P f' nm := by
  intro sup region g0 g1 nex a1 a2 a3 a4 a5 hr
  exact (H a1 a2 a3 a4 a5 hr).minkAs M

theorem SixNH.minkAs' {Ap : Sure S → Prop} {f f' : Noun} {nm : Nomm} {k : Nat} (M : MinkAs lib f' f)
    (H : SixNH (S := S) (Map := Map) snd lib N env P Ap f nm k) : SixNH (S := S) (Map := Map) snd lib N env P Ap f' nm k := by
  intro sup sur th region g0 g1 nex a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 hr
  have R := H a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 hr
  exact ⟨R.1.minkAs M, R.2⟩

/-- **A dropped hint over a constant**: every kind of `[1 k]`. -/
theorem hvDrop_ok {f k : Noun} (hd : hcDropK f k = true) :
    HVOK (S := S) (Map := Map) lib env snd N P f (Nomm.n1 k) hvDrop := by
  have V := hvLeaf_ok (S := S) (Map := Map) (lib := lib) (env := env) (snd := snd) (N := N) (P := P)
    (f := quote k) (nm := Nomm.n1 k) (x := true) (by simp [hcLeaf])
  have M := minkAs_dropK (lib := lib) hd
  exact ⟨fun _ h => (by cases h), fun _ => SurGBT.minkAs' M (V.sur rfl), fun _ => RegGBT.minkAs' M (V.reg rfl),
    fun _ => RegFT.minkAs' M (V.ft rfl), fun h => (by cases h), fun _ => DoneAllT.minkAs' M (V.dall rfl),
    fun _ => DoneG.minkAs' M (V.top rfl), fun _ h => (by cases h)⟩

/-- The direct call's formula part `[0 a]` returns `F` on subjects holding it. -/
theorem slot_hq1 {a : Nat} {F s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone} (hs : slot? a s = some F)
    (h : minkF lib gul n tm s (slot a) = some rc) : rc = Tone.zero F := by
  cases n with
  | zero => simp [minkF] at h
  | succ m =>
    simp only [minkF, minkStep, hs] at h
    cases h; rfl

theorem slot_hq2 {a : Nat} {F s gul : Noun} {tm : Trace} (hs : slot? a s = some F) :
    Mink lib gul tm s (slot a) (Tone.zero F) :=
  ⟨1, by simp only [minkF, minkStep, hs]⟩

end Transfer

/-! ## The `%6`, the `S3` body, `[7 [0 1] q]`, the `d13` rule -/

theorem hintTab_mono {env : CallEnv} {N : Needs} {nm m : Nomm} (h : HintTab env N nm)
    (hc : ∀ b, b ∈ callBells m → b ∈ callBells nm) (hm : ∀ b, b ∈ meanBells m → b ∈ meanBells nm) :
    HintTab env N m :=
  ⟨fun b hb => h.1 b (hc b hb), fun b hb => h.2 b (hm b hb)⟩

theorem img_slot1 (lib : Lib) (P : Noun → Prop) : Img lib P (slot 1) = P := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, gul, hx, hm⟩
    have e := Mink.det hm (⟨1, by simp [minkF_succ_eq, minkStep]⟩ : Mink lib gul [] x (slot 1) (Tone.zero x))
    cases e; exact hx
  · intro hy
    exact ⟨y, A 0, hy, 1, by simp [minkF_succ_eq, minkStep]⟩

theorem fromPath_three (r : Nat) : fromPath (Need.this r) 3 = Need.pair Need.none (Need.this r) := by
  rw [fromPath]
  simp only [show ¬ (3 ≤ 1) by omega, dite_false, show cap 3 = 3 by simp [cap], show mas 3 = 1 by simp [mas]]
  rw [fromPath]; simp

theorem isS3Body_eq {nm : Nomm} (h : isS3Body nm = true) :
    ∃ k4 F b, nm = Nomm.n7 (spotS3Ten k4) (spotS3Call F b) := by
  unfold isS3Body at h
  split at h
  · rename_i tag k4 body F b
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k4, F, b, rfl⟩
  · cases h

section
variable {lib : Lib} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {N : Needs} {P : Noun → Prop}

/-- **The tests the class takes** are hint-free, call-free, unhinted, in `PickD`. -/
theorem hcTest_ok {fc : Noun} {c : Nomm} (h : hcTest fc c = true) :
    c.noHint = true ∧ c.noDirect = true ∧ (∀ cod, hinted cod c = some false) ∧
      ∃ kc, PickD (S := S) (Map := Map) lib N env P fc c kc := by
  unfold hcTest at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, ha⟩ := h
    exact ⟨rfl, rfl, fun _ => rfl, pickD_n0 ha⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, ha⟩ := h
    exact ⟨rfl, rfl, fun _ => rfl, pickD_three0 ha⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, ha⟩ := h
    exact ⟨rfl, rfl, fun _ => rfl, pickD_wut ha⟩
  · cases h

/-- **A branch the class takes is in `SixNH IsReg`** (`sixNH_n1`, `sixNH_of_shape`). -/
theorem hcBranch_ok {fa : Noun} {a : Nomm} {va : HV} {ka : Nat}
    (V : HVOK (S := S) (Map := Map) lib env snd N P fa a va) (h : hcBranch fa a va = some ka) :
    SixNH (S := S) (Map := Map) snd lib N env P IsReg fa a ka := by
  unfold hcBranch at h
  split at h
  · split at h
    · rename_i he
      cases h; subst he; exact sixNH_n1 _
    · cases h
  · split at h
    · rename_i hd
      cases h; exact SixNH.minkAs' (minkAs_dropK hd) (sixNH_n1 _)
    · cases h
  · split at h
    · rename_i hr
      exact sixNH_of_shape (RegGBT.toSur (V.reg hr)) (V.sh ka h)
    · cases h

theorem regGBT_seven01P {c : Noun} {q : Nomm} (H : RegGBT (S := S) (Map := Map) snd lib N env P c q) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 7) (slot 1) c) (Nomm.n7 (Nomm.n0 1) q) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_seven01] at hr
  exact (H b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr).minkAs (minkAs_seven01 lib c)

theorem surGBT_seven01P {c : Noun} {q : Nomm} (H : SurGBT (S := S) (Map := Map) snd lib N env P RegLike c q) :
    SurGBT (S := S) (Map := Map) snd lib N env P RegLike (n3 (A 7) (slot 1) c) (Nomm.n7 (Nomm.n0 1) q) := by
  intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr
  rw [runLCH_seven01] at hr
  exact (H hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr).minkAs (minkAs_seven01 lib c)

theorem doneG_seven01P {c : Noun} {q : Nomm} (H : DoneG (S := S) (Map := Map) lib N env snd P c q) :
    DoneG (S := S) (Map := Map) lib N env snd P (n3 (A 7) (slot 1) c) (Nomm.n7 (Nomm.n0 1) q) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [runLCH_seven01] at hr
  exact (H b0 d0 hu hcl hcb hr).minkAs (minkAs_seven01 lib c)

/-- **The `d13` rule**: `[7 [tag h p'] [4 [0 a]]]` under `%done`, a kept
dynamic hint over a hint-free cons (`surSeven_done`; the need of `[0 a]`
is `+sound` for `p'`, and the products of a cons are cells). -/
theorem topKF_core {tag : Nat} {fh x y z : Noun} {h p' : Nomm} {body : Noun} {a : Nat}
    (hs : hintDynamic tag = true) (ha : a = 2 ∨ a = 3) {xh xp : Bool} (hlh : hcLeaf fh h = some xh)
    (hnb : hcNB h = true) (hlp : hcLeaf (Noun.cell (Noun.cell x y) z) p' = some xp)
    (hsnd : snd p' (if a = 2 then NeedOrd.pair NeedOrd.this NeedOrd.none
      else NeedOrd.pair NeedOrd.none NeedOrd.this) = true) :
    DoneG (S := S) (Map := Map) lib N env snd P
      (Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) fh)
        (Noun.cell (Noun.cell x y) z))) (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 0) (Noun.atom a)))))
      (Nomm.n7 (Nomm.n11d tag h p' body) (Nomm.n4 (Nomm.n0 a))) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  have Th := (hcLeaf_sound lib env N h fh xh hlh).2 P
  have Tp := (hcLeaf_sound lib env N p' _ xp hlp).2 P
  have Lh := (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env Th).1.1
  have Lp := (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env Tp).1.1
  have hch : sixCount h ≤ 255 := by rw [Th.sixCount]; omega
  have Sp : SurGBT (S := S) (Map := Map) snd lib N env P (fun _ => True) (C (C x y) z) p' :=
    SurGBT.of_loksf (fun _ => True) Lp (by rw [Tp.sixCount]; omega)
  have hnh : NoBondH (S := S) (Map := Map) snd env h := hcNB_noBond h hnb
  have Hq : DoneAllT (S := S) (Map := Map) lib N env snd
      (Img lib P (n3 (A 11) (C (A tag) fh) (C (C x y) z))) (n2 (A 4) (slot a)) (Nomm.n4 (Nomm.n0 a)) :=
    doneAllT_callTreeHU lib env (CallTreeHU.four (b1 := true) (CallTreeHU.base (CallTreeD.n0 a) rfl))
  have hq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLCH (S := S) (Map := Map) env snd true sup (Nomm.n4 (Nomm.n0 a)) CGoalL.done region g0 = some (nx, g1) →
      entries nx.laz = [] ∧ (SoundK snd p' nx.laz.sure ∧ FitP lib P (C (C x y) z) nx.laz.sure) := by
    intro sup region g0 g1 nx hr
    obtain ⟨r, e⟩ := runLCH_n4n0_done (by omega) hr
    rw [e]
    refine ⟨entries_ofSure _, ⟨?_, ?_⟩, ?_⟩
    · simp [ofSure]; exact (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x)
    · rcases ha with rfl | rfl
      · simp only [ofSure, fromPath_two]; first | exact hsnd | simpa using hsnd
      · simp only [ofSure, fromPath_three]; first | exact hsnd | simpa using hsnd
    · intro s _ gul tm p hm
      obtain ⟨n, hn⟩ := hm
      obtain ⟨n', -, rh, -, hc⟩ := minkF_consG ⟨x, y, rfl⟩ hn
      obtain ⟨u, w, rfl⟩ : ∃ u w, p = C u w := by
        rcases hc with ⟨hne, e⟩ | ⟨u, -, rt, -, ⟨hne, e⟩ | ⟨w, -, e⟩⟩
        · exact absurd e.symm (hne p)
        · exact absurd e.symm (hne p)
        · exact ⟨u, w, Tone.zero.inj e⟩
      refine ⟨?_, looks_empty _⟩
      rcases ha with rfl | rfl
      · simp only [ofSure, fromPath_two, Fits]; exact ⟨trivial, trivial⟩
      · simp only [ofSure, fromPath_three, Fits]; exact ⟨trivial, trivial⟩
  cases hst : stopTag tag
  · exact surSeven_done lib (SurGBT.mono (Ap := fun s => SoundK snd p' s ∧ FitP lib P (C (C x y) z) s)
      (fun s hs' => ⟨trivial, hs'.1⟩) (surGBT_n11dQuiet Sp Lh hch hnh hs hst body)) Hq hq b0 d0 hu hcl hcb hr
  · exact surSeven_done lib (SurGBT.mono (Ap := fun s => SoundK snd p' s ∧ FitP lib P (C (C x y) z) s)
      (fun s hs' => ⟨trivial, hs'.1, hs'.2⟩) (surGBT_n11dKept Sp Lh hch hnh hs hst body)) Hq hq b0 d0 hu hcl hcb hr

theorem topKF_ok {f : Noun} {nm : Nomm} (h : hcTopKF snd f nm = true) :
    DoneG (S := S) (Map := Map) lib N env snd P f nm := by
  unfold hcTopKF at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, hs⟩, rfl⟩, ha⟩, ⟨xh, hlh⟩⟩, hnb⟩, ⟨xp, hlp⟩⟩, hsnd⟩ := h
    exact topKF_core hs ha hlh hnb hlp hsnd
  · cases h

end

/-! ## The theorem -/


/-! ## The `%7` texts with any `MinkC7` (`[7 b c]`, `[9 a c]`, `[8 b c]`) -/

section Seven
variable {snd : Nomm → NeedOrd → Bool}

/-- (The text of `regGBT_sevenS` with any `MinkC7`.) -/
theorem regGBT_sevenSM (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {f b c : Noun} {p q : Nomm} {Ap : Sure S → Prop} (M : MinkC7 lib P f b c)
    (Hp : SurGBT (S := S) (Map := Map) snd lib N env P Ap b p)
    (Hq : RegFT (S := S) (Map := Map) snd lib N env (Img lib P b) c q)
    (hq : ∀ {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLCH (S := S) (Map := Map) env snd true sup q (CGoalL.next (ofSure (lazyReg rg)) th) region g0 =
        some (nx, g1) → entries nx.laz = [] ∧ Ap nx.laz.sure) :
    RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n7 p q) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 h1
  have Rq := D.run
  obtain ⟨hne, hA⟩ := hq h1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · simp only [GoalJ] at e; rw [e]; exact hta
  have h2' : runLCH (S := S) (Map := Map) env snd true sup p (CGoalL.next (ofSure nx.laz.sure) nx.th) region ga =
      some (nex, g1) := by
    rw [← eq_ofSure_of_entries hne]; exact h2
  have Rp := Hp hA (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow)
    (Rq.cfr.below hcb) Rq.lo Rq.hi hj Rq.dist D.clean
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · have := Rq.ext.1; simp only [GMem, lazyReg, NMem] at e; omega
      · exact e.2, Rq.ncond x hx⟩) h2'
  exact runOKGBT_sevenG M Rq hne Rp (fun r hr => by simp only [GMem, lazyReg, NMem] at hr; omega)

/-- (The text of `regFT_seven` with any `MinkC7`.) -/
theorem regFT_sevenM (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f b c : Noun} {p q : Nomm}
    (M : MinkC7 lib P f b c)
    (hp : CallTreeHU lib env N P true b p) (Hq : RegFT (S := S) (Map := Map) snd lib N env (Img lib P b) c q) :
    RegFT (S := S) (Map := Map) snd lib N env P f (Nomm.n7 p q) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 h1
  have Rq := D.run
  have Lp := ((lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib (N := N) env hp).2 rfl).1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · simp only [GoalJ] at e; rw [e]; exact hta
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
    (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · have := Rq.ext.1; simp only [GMem, lazyReg, NMem] at e; omega
      · exact e.2, Rq.ncond x hx⟩)
    (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
    D.flat D.clean D.eclean h2
  exact ⟨runOKGBT_sevenL M Rq RS.toRunOKLB
    (fun r hr => by simp only [GMem, lazyReg, NMem] at hr; omega), hne, hfl, Lp.clean (L := nx.laz) D.clean h2, hec⟩

/-- (The text of `doneAllT_seven` with any `MinkC7`.) -/
theorem doneAllT_sevenM (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f b c : Noun} {p q : Nomm}
    (M : MinkC7 lib P f b c)
    (hp : CallTreeHU lib env N P true b p) (Hq : DoneAllT (S := S) (Map := Map) lib N env snd (Img lib P b) c q) :
    DoneAllT (S := S) (Map := Map) lib N env snd P f (Nomm.n7 p q) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb h1
  have Rq := D.run
  have Lp := ((lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib (N := N) env hp).2 rfl).1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
    (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · exact e.elim
      · exact e.2, Rq.ncond x hx⟩)
    (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
    D.flat D.clean D.eclean h2
  exact ⟨runOKGBT_sevenL M Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
    Lp.clean (L := nx.laz) D.clean h2, hec⟩

end Seven

section
variable {lib : Lib} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {N : Needs} {P : Noun → Prop}

/-- **A `%7` by `MinkC7`** (`hv7G`): the fields from the parts'. -/
theorem hv7G_ok {f b c : Noun} {p q : Nomm} {vp vq : HV} (M : MinkC7 lib P f b c)
    (Vp : HVOK (S := S) (Map := Map) lib env snd N P b p vp)
    (Vq : HVOK (S := S) (Map := Map) lib env snd N (Img lib P b) c q vq) (ht : HintTab env N (Nomm.n7 p q)) :
    HVOK (S := S) (Map := Map) lib env snd N P f (Nomm.n7 p q) (hv7G snd f (Nomm.n7 p q) b p vp vq) := by
  refine ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => ?_, fun h => ?_, fun h => (by cases h),
    fun h => ?_, fun h => ?_, fun k h => ?_⟩
  · simp only [hv7G, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact RegFT.toReg (regFT_sevenM lib env M ((hcLeaf_sound lib env N p b true h1).2 P) (Vq.ft h2))
    · obtain ⟨hf, hz⟩ := Vq.zc h2
      exact regGBT_sevenSM lib M (Vp.sur h1) (Vq.ft hf) hz
  · simp only [hv7G, Bool.and_eq_true, beq_iff_eq] at h
    exact regFT_sevenM lib env M ((hcLeaf_sound lib env N p b true h.1).2 P) (Vq.ft h.2)
  · simp only [hv7G, Bool.and_eq_true, beq_iff_eq] at h
    exact doneAllT_sevenM lib env M ((hcLeaf_sound lib env N p b true h.1).2 P) (Vq.dall h.2)
  · simp only [hv7G, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact DoneAllT.toG (doneAllT_sevenM lib env M ((hcLeaf_sound lib env N p b true h1).2 P) (Vq.dall h2))
    · exact topKF_ok h
  · simp only [hv7G] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      cases h
      obtain ⟨k4, F, b', he⟩ := isS3Body_eq hc.1
      obtain ⟨hring, ⟨bNed, hned, hNf⟩, ⟨ndT, hNt⟩, hpure⟩ :=
        ht.1 b' (by rw [he]; simp [callBells, spotS3Call, spotS3Ten, spotS4])
      rw [he]
      exact shapeH_s3body k4 F hring hned hpure hc.2
    · cases h

end

/-- **Every field of `hcV snd f nm` holds**, under `HintTab` and `FitH`. -/
theorem hcV_sound (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) :
    ∀ (nm : Nomm) (f : Noun) (P : Noun → Prop), HintTab env N nm → FitH lib P f nm →
      HVOK (S := S) (Map := Map) lib env snd N P f nm (hcV snd f nm)
  | Nomm.n0 a, f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; split
    · rename_i x hx; exact hvLeaf_ok hx
    · exact hvNone_ok
  | Nomm.n1 k, f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; split
    · rename_i x hx; exact hvLeaf_ok hx
    · split
      · rename_i hd; exact hvDrop_ok hd
      · exact hvNone_ok
  | Nomm.cons p q, f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; split
    · rename_i x hx; exact hvLeafC_ok hx _
    · exact hvNone_ok
  | Nomm.n5 p q, f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; split
    · rename_i x hx; exact hvLeaf_ok hx
    · exact hvNone_ok
  | Nomm.n12 p q, f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; exact hvNone_ok
  | Nomm.n4 p, f, P, ht, hfit => by
    have IH := fun fb P' ht' fh' => hcV_sound lib env snd N p fb P' ht' fh'
    have htp : HintTab env N p :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i fb
      try dsimp only
      split
      · rename_i x hx; exact hvLeaf_ok hx
      · have V := IH fb P htp (by simpa [FitH] using hfit)
        exact ⟨fun _ h => (by cases h), fun h => surGBT_four (V.reg h) (minkC4_four lib P fb),
          fun h => regGBT_four (V.reg h) (minkC4_four lib P fb), fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => doneG_four lib (V.reg h) (minkC4_four lib P fb),
          fun k h => shapeH_four (V.sh k h)⟩
    · exact hvNone_ok
  | Nomm.n3 p, f, P, ht, hfit => by
    have IH := fun fb P' ht' fh' => hcV_sound lib env snd N p fb P' ht' fh'
    have htp : HintTab env N p :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i fb
      try dsimp only
      split
      · rename_i x hx; exact hvLeaf_ok hx
      · have V := IH fb P htp (by simpa [FitH] using hfit)
        exact ⟨fun _ h => (by cases h), fun h => surGBT_three (V.reg h) (minkC3_three lib P fb),
          fun h => regGBT_three (V.reg h) (minkC3_three lib P fb), fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩
    · exact hvNone_ok
  | Nomm.n2 p q Option.none, f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; split
    · try dsimp only
      split
      · rename_i x hx; exact hvLeaf_ok hx
      · exact hvNone_ok
    · exact hvNone_ok
  | Nomm.n2 p q (some (b, some k)), f, P, ht, hfit => by
    rw [hcV.eq_def]; dsimp only; split
    · exact hvNone_ok
    · exact hvNone_ok
  | Nomm.n2 p q (some (b, Option.none)), f, P, ht, hfit => by
    obtain ⟨hring, ⟨bNed, hned, hNf⟩, ⟨ndT, hNt⟩, hpure⟩ := ht.1 b (by simp [callBells])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i fb fq
      try dsimp only
      simp only [FitH] at hfit
      refine hvDirect_ok (fun hh => ?_) (fun hh => ?_)
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hh
        obtain ⟨⟨⟨⟨x, hx⟩, hsf⟩, h6⟩, hm⟩ := hh
        split at hm
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
          obtain ⟨rfl, hF⟩ := hm
          have T := (hcLeaf_sound lib env N p fb x hx).2 P
          intro sup rg th region g0 g1 nex
          exact regFT_direct lib env hring hned hNf hNt hpure
            (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1 hsf hfit.1
            (fun _ h => by rw [← hF]; exact quote_hq1 h) (fun _ => by rw [← hF]; exact quote_hq2) h6
        · simp only [decide_eq_true_eq] at hm
          have T := (hcLeaf_sound lib env N p fb x hx).2 P
          have hsl := hfit.2.2 _ rfl
          intro sup rg th region g0 g1 nex
          exact regFT_direct lib env hring hned hNf hNt hpure
            (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1 hsf hfit.1
            (fun hs h => slot_hq1 (hsl _ hs) h) (fun hs => slot_hq2 (hsl _ hs)) h6
        · cases hm
      · simp only [Bool.and_eq_true] at hh
        obtain ⟨hok, hp⟩ := hh
        refine ⟨by simp only [Bool.and_eq_true]; exact hok, ?_⟩
        obtain ⟨⟨⟨_, hsf⟩, _⟩, _⟩ := hok
        split at hp
        · intro sup rg th region g0 g1 nx hr
          exact directZ_shape hring hned hsf hpure hr
        · cases hp
    · exact hvNone_ok
  | Nomm.n7 p q, f, P, ht, hfit => by
    have IHp := fun fb P' ht' fh' => hcV_sound lib env snd N p fb P' ht' fh'
    have IHq := fun fc P' ht' fh' => hcV_sound lib env snd N q fc P' ht' fh'
    have htp : HintTab env N p :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    have htq : HintTab env N q :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i b c
      try dsimp only
      split
      · rename_i x hx; exact hvLeaf_ok hx
      · simp only [FitH] at hfit
        split
        · have hq' : FitH lib P c q := by
            have := hfit.2; rwa [show Img lib P (Noun.cell (Noun.atom 0) (Noun.atom 1)) = P from img_slot1 lib P] at this
          have V := IHq c P htq hq'
          have V' := IHq c _ htq hfit.2
          have T1 : CallTreeHU lib env N P true (slot 1) (Nomm.n0 1) := CallTreeHU.base (CallTreeD.n0 1) rfl
          refine ⟨fun _ h => (by cases h), fun h => surGBT_seven01P (V.sur h), fun h => ?_,
            fun h => regFT_seven lib env T1 (V'.ft h), fun h => (by cases h), fun h => (by cases h),
            fun h => doneG_seven01P (V.top h), fun _ h => (by cases h)⟩
          simp only [Bool.or_eq_true] at h
          rcases h with h | h
          · exact regGBT_seven01P (V.reg h)
          · exact RegFT.toReg (regFT_seven lib env T1 (V'.ft h))
        · exact hv7G_ok (minkC7_seven lib P b c) (IHp b P htp hfit.1) (IHq c _ htq hfit.2) ht
    · rename_i a c
      simp only [FitH] at hfit
      exact hv7G_ok (minkC7_nine lib P a c) (IHp c P htp hfit.1) (IHq _ _ htq hfit.2) ht
    · rename_i a1 a2 c
      simp only [FitH] at hfit
      exact hv7G_ok (minkC7_eight lib P a1 a2 c) (IHp _ P htp (by simp only [FitH])) (IHq c _ htq hfit.2) ht
    · exact hvNone_ok
  | Nomm.n10 a v q, f, P, ht, hfit => by
    have IH := fun fv P' ht' fh' => hcV_sound lib env snd N v fv P' ht' fh'
    have htv : HintTab env N v :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i a' fv fq
      try dsimp only
      simp only [FitH] at hfit
      have Vv := IH fv P htv hfit
      refine hvSur3_ok (fun hh => ?_) (doneNext_n10 env a v q)
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
      obtain ⟨⟨⟨⟨rfl, ha⟩, hv⟩, hm⟩, hs⟩ := hh
      split at hm
      · exact surGBT_tenKept' ha (hinted_crash hv env.cod) (Vv.sur hs) (fun hR hi => into_regLike_reg ha hR hi)
      · cases hm
    · exact hvNone_ok
  | Nomm.n6 c a b, f, P, ht, hfit => by
    have IHa := fun fa P' ht' fh' => hcV_sound lib env snd N a fa P' ht' fh'
    have IHb := fun fb P' ht' fh' => hcV_sound lib env snd N b fb P' ht' fh'
    have hta : HintTab env N a :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    have htb : HintTab env N b :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i fc fa fb
      try dsimp only
      simp only [FitH] at hfit
      have Va := IHa fa P hta hfit.1
      have Vb := IHb fb P htb hfit.2
      split
      · rename_i ka kb hka hkb
        refine ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => ?_, fun h => (by cases h),
          fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨htest, hk⟩, h6⟩ := h
        obtain ⟨hch, hcd, hcf, kc, Hc⟩ := hcTest_ok (S := S) (Map := Map) (lib := lib) (env := env) (N := N)
          (P := P) htest
        exact regGBT_six lib Hc hch hcd (hcf env.cod) (hcBranch_ok Va hka) (hcBranch_ok Vb hkb) hk h6
      · exact hvNone_ok
    · exact hvNone_ok
  | Nomm.n11s tag q body, f, P, ht, hfit => by
    have IH := fun fq P' ht' fh' => hcV_sound lib env snd N q fq P' ht' fh'
    have htq : HintTab env N q :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i x hx; exact hvLeaf_ok hx
    · split
      · rename_i tag' fq _
        try dsimp only
        simp only [FitH] at hfit
        have V := IH fq P htq hfit
        refine ⟨fun _ h => (by cases h), fun h => ?_, fun h => ?_, fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => ?_, fun _ h => (by cases h)⟩
        all_goals simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        all_goals obtain ⟨⟨⟨rfl, hs⟩, hsnd⟩, hv⟩ := h
        · exact SurGBT.mono (fun s hs' => ⟨hs', (regLike_soundFit hsnd lib P fq hs').1⟩)
            (surGBT_n11sKept (V.sur hv) hs body)
        · exact regGBT_n11sKept (V.reg hv) hsnd hs body
        · exact doneG_of_next (regGBT_n11sKept (V.reg hv) hsnd hs body) (doneNext_n11s env hs q body)
      · exact hvNone_ok
  | Nomm.n11d tag h q body, f, P, ht, hfit => by
    have IH := fun fq P' ht' fh' => hcV_sound lib env snd N q fq P' ht' fh'
    have htq : HintTab env N q :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    rw [hcV.eq_def]; dsimp only; split
    · rename_i x hx; exact hvLeaf_ok hx
    · split
      · rename_i tag' fh fq _
        try dsimp only
        simp only [FitH] at hfit
        have V := IH fq P htq hfit
        split
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨rfl, hs⟩ := hc
          refine hvKeptD_ok hs V _ ?_
          intro hc1
          split at hc1 <;> first | exact ⟨_, rfl⟩ | cases hc1
        · exact hvNone_ok
      · exact hvNone_ok
  | Nomm.mean p b q body k, f, P, ht, hfit => by
    have IH := fun fq P' ht' fh' => hcV_sound lib env snd N q fq P' ht' fh'
    have htq : HintTab env N q :=
      hintTab_mono ht (fun b hb => by simp [callBells, hb]) (fun b hb => by simp [meanBells, hb])
    have hk : meanKonst env b k = Option.none := by
      cases k with
      | none => rfl
      | some n => simp only [meanKonst, ht.2 b (by simp [meanBells]), Bool.false_eq_true, ↓reduceIte]
    rw [hcV.eq_def]; dsimp only; split
    · rename_i tag' fp fq
      try dsimp only
      simp only [FitH] at hfit
      have V := IH fq P htq hfit
      split
      · rename_i htag
        subst htag
        exact hvMean_ok hk V
      · exact hvNone_ok
    · exact hvNone_ok

/-- **The contract of the class**: every member of `hcV`'s `top` has both
halves of the contract at the top, traces included, under the code table
(`HintTab`) and the fit of the callees' `less` (`FitH`). -/
theorem hintCls_contract (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    {f : Noun} {nm : Nomm} (hm : (hcV snd f nm).top = true) (ht : HintTab env N nm) (hfit : FitH lib P f nm)
    {c : Straight Map} (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractDoneG lib ((hcV_sound (S := S) (Map := Map) lib env snd N nm f P ht hfit).top hm) hc

/-! ## Re-derived by membership -/

theorem spot_dynamic' : hintDynamic 1953460339 = true := by decide
theorem spot_stop' : stopTag 1953460339 = true := by decide

section
variable {snd : Nomm → NeedOrd → Bool}

/-- `contract_d10` by membership (`hintCls_contract`). -/
theorem contract_d10C (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsq : snd exD10Q NeedOrd.this = true) (hsi : snd exD10I NeedOrd.this = true)
    (hc : finishLUCH (S := S) env snd exD10 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD10F [s] c ∧ ContractBwd lib N s exD10F [s] c := by
  have H := hintCls_contract lib env snd N (fun _ => True) (f := exD10F) ?_ ?_ ?_ hc
  · exact ⟨H.1, fun s => H.2 s trivial⟩
  · simp only [exD10I, exD10Q, exD10QF, exD10IF, tagSpot] at hsq hsi
    simp [hcV, hcLeaf, hvLeaf, hvKeptD, hcNB, hinted0, hinted, orB, tagSpot, spot_dynamic', spot_stop',
      exD10, exD10F, exD10I, exD10IF, exD10Q, exD10QF, hsq, hsi]
  · exact ⟨fun b hb => by simp [callBells, exD10, exD10I, exD10Q] at hb,
      fun b hb => by simp [meanBells, exD10, exD10I, exD10Q] at hb⟩
  · simp [FitH, exD10, exD10F, exD10I, exD10IF, exD10Q, exD10QF]

/-- `contract_d13` by membership (the `d13` rule, `hcTopKF`). -/
theorem contract_d13C (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (NeedOrd.pair NeedOrd.this NeedOrd.none) = true)
    (hc : finishLUCH (S := S) env snd exD13 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD13F [s] c ∧ ContractBwd lib N s exD13F [s] c := by
  have H := hintCls_contract lib env snd N (fun _ => True) (f := exD13F) ?_ ?_ ?_ hc
  · exact ⟨H.1, fun s => H.2 s trivial⟩
  · simp [hcV, hcLeaf, hvLeaf, hvKeptD, hv7G, hcNB, hinted0, hinted, orB, hcTopKF, tagSpot, spot_dynamic', spot_stop',
      exD13, exD13F, exD13K, exD13KF, hsnd]
  · exact ⟨fun b hb => by simp [callBells, exD13, exD13K] at hb, fun b hb => by simp [meanBells, exD13, exD13K] at hb⟩
  · simp [FitH, exD13, exD13F, exD13K, exD13KF]

/-- `contract_d18` by membership (the `%6`). -/
theorem contract_d18C (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd exD18Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD18 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD18F [s] c ∧ ContractBwd lib N s exD18F [s] c := by
  have H := hintCls_contract lib env snd N (fun _ => True) (f := exD18F) ?_ ?_ ?_ hc
  · exact ⟨H.1, fun s => H.2 s trivial⟩
  · simp only [exD18Q] at hsnd
    simp [hcV, hcLeaf, hvLeaf, hvKeptD, hcNB, hinted0, hinted, orB, hcTest, hcBranch, tagSpot, spot_dynamic',
      spot_stop', sixCount, lazyMax, exD18, exD18F, exD18Q, exD18QF, hsnd]
  · exact ⟨fun b hb => by simp [callBells, exD18, exD18Q] at hb, fun b hb => by simp [meanBells, exD18, exD18Q] at hb⟩
  · simp [FitH, exD18, exD18F, exD18Q, exD18QF]

/-- `contract_d20` by membership (the `%10`). -/
theorem contract_d20C (lib : Lib) (env : CallEnv) (N : Needs) {c : Straight Map}
    (hsq : snd exD10Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD20 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD20F [s] c ∧ ContractBwd lib N s exD20F [s] c := by
  have H := hintCls_contract lib env snd N (fun _ => True) (f := exD20F) ?_ ?_ ?_ hc
  · exact ⟨H.1, fun s => H.2 s trivial⟩
  · simp only [exD10Q] at hsq
    simp [hcV, hcLeaf, hvLeaf, hvKeptD, hcNB, hinted0, hinted, orB, tagSpot, spot_dynamic', spot_stop',
      exD20, exD20F, exD19K, exD19KF, exD10Q, exD10QF, hsq]
  · exact ⟨fun b hb => by simp [callBells, exD20, exD19K, exD10Q] at hb,
      fun b hb => by simp [meanBells, exD20, exD19K, exD10Q] at hb⟩
  · simp [FitH, exD20, exD20F, exD19K, exD19KF, exD10Q, exD10QF]

/-- **`contract_spotArm` by membership**: the statement of `contract_spotArm`
(`CompHintTenEx.lean`) with the recursion's formula `F` the callee's
`b.fol` (so `hF` is gone); the rest of its hypotheses discharge `top`,
`HintTab` (`callBells` is `[b]`) and `FitH` (it is `hAp`). -/
theorem contract_spotArmC (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs)
    (k1 k2 k3 k4 B1 B2 B3 : Noun)
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false)
    (hAp : ∀ x gul y, Img lib (fun _ => True) (spotS3TenF k4) x → Mink lib gul [] x (slot 1) (Tone.zero y) →
      SkaModel.Fits b.less y)
    (hsnd7 : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call b.fol b)) NeedOrd.this = true)
    (h4 : snd (Nomm.n4 (spotS3 k3 k4 b.fol b B3)) NeedOrd.this = true)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true)
    (h6 : sixCount (spotSix (spotS2 k2 k3 k4 b.fol b B2 B3)) ≤ 255)
    (hsnd : snd (spotSix (spotS2 k2 k3 k4 b.fol b B2 B3)) NeedOrd.this = true) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd
      (Nomm.n11d tagSpot (Nomm.n1 k1) (spotSix (spotS2 k2 k3 k4 b.fol b B2 B3)) B1) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 b.fol))) [s] c ∧
      ContractBwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 b.fol))) [s] c := by
  have H := hintCls_contract lib env snd N (fun _ => True)
    (f := n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 b.fol))) ?_ ?_ ?_ hc
  · exact ⟨H.1, fun s => H.2 s trivial⟩
  · simp only [spotSix, spotS2, spotS3, spotS3Ten, spotS3Call, spotS4, spotTest, tagSpot] at hsnd7 h4 hsnd
    simp [hcV, hcLeaf, hvLeaf, hvKeptD, hv7G, hcNB, hinted0, hinted, orB, hcTest, hcBranch, isS3Body, tagSpot,
      spot_dynamic', spot_stop', sixCount, safeFolFol, lazyMax, spotSix, spotSixF, spotS2, spotS2F, spotS3, spotS3F,
      spotS3Ten, spotS3TenF, spotS3Call, spotS3CallF, spotS4, spotS4F, spotTest, spotTestF, hsnd7, h4, h13, hsnd]
  · refine ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩
    · simp [callBells, spotSix, spotS2, spotS3, spotS3Ten, spotS3Call, spotS4, spotTest] at hb'
      subst hb'
      exact ⟨hring, ⟨bNed, hned, hNf⟩, ⟨ndT, hNt⟩, hpure⟩
    · simp [meanBells, spotSix, spotS2, spotS3, spotS3Ten, spotS3Call, spotS4, spotTest] at hb'
  · simp only [FitH, spotSix, spotSixF, spotS2, spotS2F, spotS3, spotS3F, spotS3Ten, spotS3TenF, spotS3Call,
      spotS3CallF, spotS4, spotS4F, spotTest, spotTestF, true_and, and_true]
    exact ⟨hAp, fun a ha => by cases ha⟩

end

namespace HintClsSound
open HintNest HintKeep HintSpot HintSeven HintTen
#guard (hcV sndH exD10F exD10).top
#guard (hcV sndH exD13F exD13).top
#guard (hcV sndH exD18F exD18).top
#guard (hcV sndH exD20F exD20).top
#guard (hcV sndH (n3 (A 11) (C (A tagSpot) (quote (spK 108 29 108 48)))
    (spotSixF (spotS2F (spK 108 36 108 47) (spK 108 38 108 46) (spK 108 42 108 45) bellR.fol)))
  (Nomm.n11d tagSpot (Nomm.n1 (spK 108 29 108 48))
    (spotSix (spotS2 (spK 108 36 108 47) (spK 108 38 108 46) (spK 108 42 108 45) bellR.fol bellR (A 2) (A 3)))
    (A 1))).top
end HintClsSound

end Comp
end SkaModel
end Formalization
