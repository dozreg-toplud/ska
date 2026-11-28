import lemmas.Ska.CompHintW
import lemmas.Ska.CompHintClsSound

/-!
# The wider class of hinted nomms: soundness and the contract (README Gaps 24.23)

* `HWOK`: what each field of `HW` promises (`HVOK`'s fields and `st`:
  `SixTopD`); `HWOK.ofV` (from `HVOK` when the fields agree).
* `hwKeptD_ok` (kept dynamic hints, `ShapeH` with an `hcNB` clue),
  `hwMean_ok` (the `%mean`, split on `+mean-konst`: no constant as before,
  a constant by `regGBT_meanK`, `surGBT_meanK`, `doneNext_meanK`,
  `shapeH_meanK`), `hwDirect_ok` (the tail call, `tailP_doneMH`),
  `hw7G_ok`, `hwSix_ok` (`%6` at the top, `sixTopD_six`).
* **`hcW_sound`**: one structural recursion over all nomm constructors.
* **`hintClsW_contract`**: a member of `hcW`'s `top`, under `HintTabW` and
  `FitHW`, has both halves of the contract at the top.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The `HV` part of an `HW`. -/
def HW.toV (w : HW) : HV := ⟨w.leaf, w.clue, w.sur, w.reg, w.ft, w.zc, w.dall, w.top, w.sh⟩

/-- **What each field of `HW` promises.** -/
structure HWOK (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    (f : Noun) (nm : Nomm) (v : HW) : Prop where
  leaf : ∀ x, v.leaf = some x → hcLeaf f nm = some x
  sur : v.sur = true → SurGBT (S := S) (Map := Map) snd lib N env P RegLike f nm
  reg : v.reg = true → RegGBT (S := S) (Map := Map) snd lib N env P f nm
  ft : v.ft = true → RegFT (S := S) (Map := Map) snd lib N env P f nm
  zc : v.zc = true → v.ft = true ∧ ZRun (S := S) (Map := Map) env snd nm
  dall : v.dall = true → DoneAllT (S := S) (Map := Map) lib N env snd P f nm
  top : v.top = true → DoneG (S := S) (Map := Map) lib N env snd P f nm
  sh : ∀ k, v.sh = some k → ShapeH (S := S) (Map := Map) snd env IsReg nm k
  st : ∀ k, v.st = some k → SixTopD (S := S) (Map := Map) lib N env snd P f nm k

section
variable {lib : Lib} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {N : Needs} {P : Noun → Prop}

theorem HWOK.toV' {f : Noun} {nm : Nomm} {w : HW} (W : HWOK (S := S) (Map := Map) lib env snd N P f nm w) :
    HVOK (S := S) (Map := Map) lib env snd N P f nm w.toV :=
  ⟨W.leaf, W.sur, W.reg, W.ft, W.zc, W.dall, W.top, W.sh⟩

theorem HWOK.ofV {f : Noun} {nm : Nomm} {v : HV} {w : HW} (V : HVOK (S := S) (Map := Map) lib env snd N P f nm v)
    (e : w.toV = v) (hst : ∀ k, w.st = some k → SixTopD (S := S) (Map := Map) lib N env snd P f nm k) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm w := by
  subst e
  exact ⟨V.leaf, V.sur, V.reg, V.ft, V.zc, V.dall, V.top, V.sh, hst⟩

theorem hwNone_ok {f : Noun} {nm : Nomm} : HWOK (S := S) (Map := Map) lib env snd N P f nm {} :=
  ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun h => (by cases h),
    fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem hwLeaf_st {f : Noun} {nm : Nomm} {x : Bool} :
    ∀ k, (hwLeaf x f nm).st = some k → SixTopD (S := S) (Map := Map) lib N env snd P f nm k := by
  intro k hk
  simp only [hwLeaf] at hk
  split at hk
  · rename_i h; cases hk; exact sixTopD_leaf lib env snd P h
  · cases hk

/-- **A leaf** (with a clue flag). -/
theorem hwLeafC_ok {f : Noun} {nm : Nomm} {x : Bool} (hx : hcLeaf f nm = some x) (c : Bool) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm { hwLeaf x f nm with clue := c } :=
  HWOK.ofV (hvLeafC_ok hx c) rfl (hwLeaf_st (x := x))

theorem hwLeaf_ok {f : Noun} {nm : Nomm} {x : Bool} (hx : hcLeaf f nm = some x) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm (hwLeaf x f nm) :=
  HWOK.ofV (hvLeaf_ok hx) rfl (hwLeaf_st (x := x))

/-- **A `[4 p]` leaf with `p`'s `sh`** (`shapeH_four`). -/
theorem hwLeafFour_ok {fb : Noun} {p : Nomm} {x : Bool} (hx : hcLeaf (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p) = some x)
    {sh : Option Nat} (hsh : ∀ k, sh = some k → ShapeH (S := S) (Map := Map) snd env IsReg p k) :
    HWOK (S := S) (Map := Map) lib env snd N P (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p)
      { hwLeaf x (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p) with sh := sh } := by
  have V := hvLeaf_ok (S := S) (Map := Map) (lib := lib) (env := env) (snd := snd) (N := N) (P := P) hx
  exact ⟨V.leaf, V.sur, V.reg, V.ft, V.zc, V.dall, V.top, fun k hk => shapeH_four (hsh k hk), hwLeaf_st (x := x)⟩

theorem hwDrop_ok {f k : Noun} (hd : hcDropK f k = true) :
    HWOK (S := S) (Map := Map) lib env snd N P f (Nomm.n1 k) hwDrop :=
  HWOK.ofV (hvDrop_ok hd) rfl (fun _ h => by cases h)

/-- **A kept dynamic hint meets its fields** (`hwKeptD`). -/
theorem hwKeptD_ok {tag : Nat} {fh fq : Noun} {h q : Nomm} {body : Noun} {vq : HW}
    (hs : hintDynamic tag = true) (V : HWOK (S := S) (Map := Map) lib env snd N P fq q vq) :
    HWOK (S := S) (Map := Map) lib env snd N P
      (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) fh) fq)) (Nomm.n11d tag h q body)
      (hwKeptD snd fh h q vq (stopTag tag)) := by
  have V0 := hvKeptD_ok (fh := fh) (h := h) (body := body) hs V.toV' false (fun h => by cases h)
  have Hreg : (((hcLeaf fh h).isSome && hcNB h && snd q NeedOrd.this) && vq.reg) = true →
      RegGBT (S := S) (Map := Map) snd lib N env P
        (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) fh) fq)) (Nomm.n11d tag h q body) :=
    fun hh => V0.reg hh
  have Hsh : ∀ k, (if hcNB h && snd q NeedOrd.this then vq.sh.map (· + 1) else Option.none) = some k →
      ShapeH (S := S) (Map := Map) snd env IsReg (Nomm.n11d tag h q body) k := by
    intro k hk
    split at hk
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨k0, h0, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact shapeH_n11dLeafShapeW hs hc.1 body (V.sh k0 h0) (isReg_sound hc.2)
    · cases hk
  refine ⟨V0.leaf, V0.sur, V0.reg, V0.ft, V0.zc, V0.dall, V0.top, Hsh, fun k hk => ?_⟩
  simp only [hwKeptD] at hk
  split at hk
  · rename_i hc
    exact sixTopD_of_next (Hreg hc) (doneNext_n11d env hs h q body) (Hsh k hk)
  · cases hk

/-- **A `%mean` meets its fields** (`hwKeptD` with `stop` `|`), with or
without a constant. -/
theorem hwMean_ok {fp fq : Noun} {p q : Nomm} {b : Bell} {body : Noun} {k : Option Noun} {vq : HW}
    (V : HWOK (S := S) (Map := Map) lib env snd N P fq q vq)
    (hK : ∀ n, meanKonst env b k = some n → ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s →
      Mink lib gul tm s fp (Tone.zero trap) → MackRel lib trap n) :
    HWOK (S := S) (Map := Map) lib env snd N P
      (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom Tag.mean) fp) fq)) (Nomm.mean p b q body k)
      (hwKeptD snd fp p q vq false) := by
  have hs : hintDynamic Tag.mean = true := by decide
  cases hm : meanKonst env b k with
  | none =>
    have V0 := hvMean_ok (body := body) (p := p) (fp := fp) hm V.toV'
    have Hsh : ∀ k', (if hcNB p && snd q NeedOrd.this then vq.sh.map (· + 1) else Option.none) = some k' →
        ShapeH (S := S) (Map := Map) snd env IsReg (Nomm.mean p b q body k) k' := by
      intro k' hk
      split at hk
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        obtain ⟨k0, h0, rfl⟩ := Option.map_eq_some_iff.mp hk
        exact shapeH_meanLeafShapeW hm hc.1 (V.sh k0 h0) (isReg_sound hc.2)
      · cases hk
    refine ⟨fun _ hh => by simp [hwKeptD] at hh, V0.sur, V0.reg, fun hh => by simp [hwKeptD] at hh,
      fun hh => by simp [hwKeptD] at hh, fun hh => by simp [hwKeptD] at hh, V0.top, Hsh, fun k' hk => ?_⟩
    simp only [hwKeptD] at hk
    split at hk
    · rename_i hc
      exact sixTopD_of_next (V0.reg hc) (doneNext_mean hm) (Hsh k' hk)
    · cases hk
  | some n =>
    have hKn : ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s → Mink lib gul tm s fp (Tone.zero trap) →
        MackRel lib trap n := fun hs' hm' => hK n hm hs' hm'
    have parts : ((hcLeaf fp p).isSome && hcNB p && snd q NeedOrd.this) = true →
        LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fp p ∧ sixCount p ≤ 255 ∧
          NoBondH (S := S) (Map := Map) snd env p ∧ hcNB p = true ∧ snd q NeedOrd.this = true := by
      intro hok
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hok
      obtain ⟨⟨⟨x, hx⟩, hnb⟩, hsnd⟩ := hok
      have T := (hcLeaf_sound lib env N p fp x hx).2 P
      exact ⟨(lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1, by rw [T.sixCount]; omega,
        hcNB_noBond p hnb, hnb, hsnd⟩
    have Hreg : (((hcLeaf fp p).isSome && hcNB p && snd q NeedOrd.this) && vq.reg) = true →
        RegGBT (S := S) (Map := Map) snd lib N env P
          (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom Tag.mean) fp) fq)) (Nomm.mean p b q body k) := by
      intro hh
      simp only [Bool.and_eq_true] at hh
      obtain ⟨Hp, hcp, hnp, -, hsnd⟩ := parts (by simp only [Bool.and_eq_true]; exact hh.1)
      exact regGBT_meanK hm (V.reg hh.2) hsnd Hp hcp hnp hKn
    have Hsh : ∀ k', (if hcNB p && snd q NeedOrd.this then vq.sh.map (· + 1) else Option.none) = some k' →
        ShapeH (S := S) (Map := Map) snd env IsReg (Nomm.mean p b q body k) k' := by
      intro k' hk
      split at hk
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        obtain ⟨k0, h0, rfl⟩ := Option.map_eq_some_iff.mp hk
        exact shapeH_meanK hm (V.sh k0 h0) (isReg_sound hc.2) (hcNB_noBond p hc.1)
          (fun d0 hr => ⟨(clue_tagShapeW hc.1 d0 hr).1, fun e he => by
            rw [(clue_tagShapeW hc.1 d0 hr).2] at he; cases he⟩)
      · cases hk
    refine ⟨fun _ hh => by simp [hwKeptD] at hh, fun hh => ?_, Hreg, fun hh => by simp [hwKeptD] at hh,
      fun hh => by simp [hwKeptD] at hh, fun hh => by simp [hwKeptD] at hh,
      fun hh => doneG_of_next (Hreg hh) (doneNext_meanK hm), Hsh, fun k' hk => ?_⟩
    · simp only [hwKeptD, Bool.and_eq_true] at hh
      obtain ⟨Hp, hcp, hnp, -, hsnd⟩ := parts (by simp only [Bool.and_eq_true]; exact hh.1)
      exact SurGBT.mono (fun s hs' => ⟨hs', regLike_soundFit hsnd lib P fq hs'⟩)
        (surGBT_meanK hm (V.sur hh.2) Hp hcp hnp hKn)
    · simp only [hwKeptD] at hk
      split at hk
      · rename_i hc
        exact sixTopD_of_next (Hreg hc) (doneNext_meanK hm) (Hsh k' hk)
      · cases hk

/-- **A direct call's fields**: `RegFT`, `ZRun`, and under `%done` the tail call. -/
theorem hwDirect_ok {f : Noun} {nm : Nomm} {o z : Bool}
    (FT : o = true → RegFT (S := S) (Map := Map) snd lib N env P f nm)
    (Z : z = true → o = true ∧ ZRun (S := S) (Map := Map) env snd nm)
    (D : o = true → DoneAllT (S := S) (Map := Map) lib N env snd P f nm) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm { ft := o, reg := o, zc := z, dall := o, top := o } :=
  ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => RegFT.toReg (FT h), FT, Z, D,
    fun h => DoneAllT.toG (D h), fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem hwSur3_ok {f : Noun} {nm : Nomm} {o : Bool}
    (H : o = true → SurGBT (S := S) (Map := Map) snd lib N env P RegLike f nm)
    (hD : DoneNext (S := S) (Map := Map) env snd nm) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm { sur := o, reg := o, top := o } :=
  HWOK.ofV (hvSur3_ok H hD) rfl (fun _ h => by cases h)

/-- **A `%7` by `MinkC7`** (`hw7G`). -/
theorem hw7G_ok {f b c : Noun} {p q : Nomm} {vp vq : HW} (M : MinkC7 lib P f b c)
    (Vp : HWOK (S := S) (Map := Map) lib env snd N P b p vp)
    (Vq : HWOK (S := S) (Map := Map) lib env snd N (Img lib P b) c q vq) (ht : HintTabW env N (Nomm.n7 p q)) :
    HWOK (S := S) (Map := Map) lib env snd N P f (Nomm.n7 p q) (hw7G snd f (Nomm.n7 p q) b p vp vq) := by
  refine ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => ?_, fun h => ?_, fun h => (by cases h),
    fun h => ?_, fun h => ?_, fun k h => ?_, fun _ h => (by cases h)⟩
  · simp only [hw7G, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact RegFT.toReg (regFT_sevenM lib env M ((hcLeaf_sound lib env N p b true h1).2 P) (Vq.ft h2))
    · obtain ⟨hf, hz⟩ := Vq.zc h2
      exact regGBT_sevenSM lib M (Vp.sur h1) (Vq.ft hf) hz
  · simp only [hw7G, Bool.and_eq_true, beq_iff_eq] at h
    exact regFT_sevenM lib env M ((hcLeaf_sound lib env N p b true h.1).2 P) (Vq.ft h.2)
  · simp only [hw7G, Bool.and_eq_true, beq_iff_eq] at h
    exact doneAllT_sevenM lib env M ((hcLeaf_sound lib env N p b true h.1).2 P) (Vq.dall h.2)
  · simp only [hw7G, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact DoneAllT.toG (doneAllT_sevenM lib env M ((hcLeaf_sound lib env N p b true h1).2 P) (Vq.dall h2))
    · exact topKF_ok h
  · simp only [hw7G] at h
    split at h
    · rename_i hc
      cases h
      exact shapeH_s3bodyShapeW hc ht
    · cases h

theorem hwBranch_ok {fa : Noun} {a : Nomm} {va : HW} {ka : Nat}
    (V : HWOK (S := S) (Map := Map) lib env snd N P fa a va) (h : hwBranch fa a va = some ka) :
    SixNH (S := S) (Map := Map) snd lib N env P IsReg fa a ka :=
  hcBranch_ok V.toV' h

theorem hintTabW_mono {env : CallEnv} {N : Needs} {nm m : Nomm} (h : HintTabW env N nm)
    (hc : ∀ b, b ∈ callBells m → b ∈ callBells nm) : HintTabW env N m := fun b hb => h b (hc b hb)

end

/-- **The wider class is sound**: every field of `hcW` meets its promise. -/
theorem hcW_sound (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) :
    ∀ (nm : Nomm) (f : Noun) (P : Noun → Prop), HintTabW env N nm → FitHW lib env P f nm →
      HWOK (S := S) (Map := Map) lib env snd N P f nm (hcW snd f nm)
  | Nomm.n0 a, f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeaf_ok hx
    · exact hwNone_ok
  | Nomm.n1 k, f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeaf_ok hx
    · split
      · rename_i hd; exact hwDrop_ok hd
      · exact hwNone_ok
  | Nomm.cons p q, f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeafC_ok hx _
    · exact hwNone_ok
  | Nomm.n5 p q, f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeaf_ok hx
    · exact hwNone_ok
  | Nomm.n12 p q, f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; exact hwNone_ok
  | Nomm.n4 p, f, P, ht, hfit => by
    have IH := fun fb P' ht' fh' => hcW_sound lib env snd N p fb P' ht' fh'
    have htp : HintTabW env N p := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i fb
      try dsimp only
      have V := IH fb P htp (by simpa [FitHW] using hfit)
      split
      · rename_i x hx; exact hwLeafFour_ok hx V.sh
      · exact ⟨fun _ h => (by cases h), fun h => surGBT_four (V.reg h) (minkC4_four lib P fb),
          fun h => regGBT_four (V.reg h) (minkC4_four lib P fb), fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => doneG_four lib (V.reg h) (minkC4_four lib P fb),
          fun k h => shapeH_four (V.sh k h), fun _ h => (by cases h)⟩
    · exact hwNone_ok
  | Nomm.n3 p, f, P, ht, hfit => by
    have IH := fun fb P' ht' fh' => hcW_sound lib env snd N p fb P' ht' fh'
    have htp : HintTabW env N p := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i fb
      try dsimp only
      split
      · rename_i x hx; exact hwLeaf_ok hx
      · have V := IH fb P htp (by simpa [FitHW] using hfit)
        exact ⟨fun _ h => (by cases h), fun h => surGBT_three (V.reg h) (minkC3_three lib P fb),
          fun h => regGBT_three (V.reg h) (minkC3_three lib P fb), fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩
    · exact hwNone_ok
  | Nomm.n2 p q Option.none, f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; split
    · try dsimp only
      split
      · rename_i x hx; exact hwLeaf_ok hx
      · exact hwNone_ok
    · exact hwNone_ok
  | Nomm.n2 p q (some (b, some k)), f, P, ht, hfit => by
    rw [hcW.eq_def]; dsimp only; split
    · exact hwNone_ok
    · exact hwNone_ok
  | Nomm.n2 p q (some (b, Option.none)), f, P, ht, hfit => by
    obtain ⟨hring, ⟨bNed, hned, hNf⟩, ⟨ndT, hNt⟩, hpure⟩ := ht b (by simp [callBells])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i fb fq
      try dsimp only
      simp only [FitHW] at hfit
      obtain ⟨hAp, -, hsl0⟩ := hfit
      refine hwDirect_ok (fun hh => ?_) ?zc (fun hh => ?_)
      case zc =>
        intro hh
        simp only [Bool.and_eq_true] at hh
        obtain ⟨hok, hp⟩ := hh
        refine ⟨by simp only [Bool.and_eq_true]; exact hok, ?_⟩
        obtain ⟨⟨⟨_, hsf⟩, _⟩, _⟩ := hok
        split at hp
        · intro sup rg th region g0 g1 nx hr
          exact directZ_shape hring hned hsf hpure hr
        · cases hp
      all_goals
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hh
        obtain ⟨⟨⟨⟨x, hx⟩, hsf⟩, h6⟩, hm⟩ := hh
        have T := (hcLeaf_sound lib env N p fb x hx).2 P
        have Lp := (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env T).1.1
        have hcp : sixCount p ≤ 255 := by rw [T.sixCount]; omega
        split at hm
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
          obtain ⟨rfl, hF⟩ := hm
          first
          | (intro sup rg th region g0 g1 nex; exact regFT_direct lib env hring hned hNf hNt hpure Lp hsf hAp
              (fun _ h => by rw [← hF]; exact quote_hq1 h) (fun _ => by rw [← hF]; exact quote_hq2) h6)
          | intro sup region g0 g1 nex b0 d0 hu hcl hcb hr; exact (tailP_doneMH lib hring hned hNf hNt Lp hcp hsf hAp
              (fun _ h => by rw [← hF]; exact quote_hq1 h) (fun _ => by rw [← hF]; exact quote_hq2)
              b0 d0 hu hcl hcb hr).toT
        · simp only [decide_eq_true_eq] at hm
          have hsl := hsl0 _ rfl
          first
          | (intro sup rg th region g0 g1 nex; exact regFT_direct lib env hring hned hNf hNt hpure Lp hsf hAp
              (fun hs h => slot_hq1 (hsl _ hs) h) (fun hs => slot_hq2 (hsl _ hs)) h6)
          | intro sup region g0 g1 nex b0 d0 hu hcl hcb hr; exact (tailP_doneMH lib hring hned hNf hNt Lp hcp hsf hAp
              (fun hs h => slot_hq1 (hsl _ hs) h) (fun hs => slot_hq2 (hsl _ hs)) b0 d0 hu hcl hcb hr).toT
        · cases hm
    · exact hwNone_ok
  | Nomm.n7 p q, f, P, ht, hfit => by
    have IHp := fun fb P' ht' fh' => hcW_sound lib env snd N p fb P' ht' fh'
    have IHq := fun fc P' ht' fh' => hcW_sound lib env snd N q fc P' ht' fh'
    have htp : HintTabW env N p := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i b c
      try dsimp only
      split
      · rename_i x hx; exact hwLeaf_ok hx
      · simp only [FitHW] at hfit
        split
        · have hq' : FitHW lib env P c q := by
            have := hfit.2; rwa [show Img lib P (Noun.cell (Noun.atom 0) (Noun.atom 1)) = P from img_slot1 lib P] at this
          have V := IHq c P htq hq'
          have V' := IHq c _ htq hfit.2
          have T1 : CallTreeHU lib env N P true (slot 1) (Nomm.n0 1) := CallTreeHU.base (CallTreeD.n0 1) rfl
          refine ⟨fun _ h => (by cases h), fun h => surGBT_seven01P (V.sur h), fun h => ?_,
            fun h => regFT_seven lib env T1 (V'.ft h), fun h => (by cases h), fun h => (by cases h),
            fun h => doneG_seven01P (V.top h), fun _ h => (by cases h), fun _ h => (by cases h)⟩
          simp only [Bool.or_eq_true] at h
          rcases h with h | h
          · exact regGBT_seven01P (V.reg h)
          · exact RegFT.toReg (regFT_seven lib env T1 (V'.ft h))
        · exact hw7G_ok (minkC7_seven lib P b c) (IHp b P htp hfit.1) (IHq c _ htq hfit.2) ht
    · rename_i a c
      simp only [FitHW] at hfit
      exact hw7G_ok (minkC7_nine lib P a c) (IHp c P htp hfit.1) (IHq _ _ htq hfit.2) ht
    · rename_i a1 a2 c
      simp only [FitHW] at hfit
      exact hw7G_ok (minkC7_eight lib P a1 a2 c) (IHp _ P htp (by simp only [FitHW])) (IHq c _ htq hfit.2) ht
    · exact hwNone_ok
  | Nomm.n10 a v q, f, P, ht, hfit => by
    have IH := fun fv P' ht' fh' => hcW_sound lib env snd N v fv P' ht' fh'
    have htv : HintTabW env N v := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i a' fv fq
      try dsimp only
      simp only [FitHW] at hfit
      have Vv := IH fv P htv hfit
      refine hwSur3_ok (fun hh => ?_) (doneNext_n10 env a v q)
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
      obtain ⟨⟨⟨⟨rfl, ha⟩, hv⟩, hm⟩, hs⟩ := hh
      split at hm
      · exact surGBT_tenKept' ha (hinted_crash hv env.cod) (Vv.sur hs) (fun hR hi => into_regLike_reg ha hR hi)
      · cases hm
    · exact hwNone_ok
  | Nomm.n6 c a b, f, P, ht, hfit => by
    have IHa := fun fa P' ht' fh' => hcW_sound lib env snd N a fa P' ht' fh'
    have IHb := fun fb P' ht' fh' => hcW_sound lib env snd N b fb P' ht' fh'
    have hta : HintTabW env N a := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    have htb : HintTabW env N b := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i fc fa fb
      try dsimp only
      simp only [FitHW] at hfit
      have Va := IHa fa P hta hfit.1
      have Vb := IHb fb P htb hfit.2
      have Hst : ∀ k, (match (hcW snd fa a).st, (hcW snd fb b).st with
          | some ka, some kb =>
              if sixTopLeafB true fc c && decide (ka + kb + 5 ≤ lazyMax) then some (0 + ka + kb + 4)
              else Option.none
          | _, _ => Option.none) = some k →
          SixTopD (S := S) (Map := Map) lib N env snd P (Noun.cell (Noun.atom 6) (Noun.cell fc (Noun.cell fa fb)))
            (Nomm.n6 c a b) k := by
        intro k hk
        split at hk
        · rename_i ka kb hka hkb
          split at hk
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            cases hk
            obtain ⟨Hc, hch, hcd, hcf⟩ := pickD_sixTopLeaf (S := S) (Map := Map) lib (N := N) env P hc.1
            exact sixTopD_six lib Hc hch hcd (hcf env.cod) (Va.st ka hka) (Vb.st kb hkb) hc.2
          · cases hk
        · cases hk
      refine ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => ?_, fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), fun h => ?_, fun _ h => (by cases h), Hst⟩
      · split at h
        · rename_i ka kb hka hkb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨htest, hk⟩, h6⟩ := h
          obtain ⟨hch, hcd, hcf, kc, Hc⟩ := hcTest_ok (S := S) (Map := Map) (lib := lib) (env := env) (N := N)
            (P := P) htest
          exact regGBT_six lib Hc hch hcd (hcf env.cod) (hwBranch_ok Va hka) (hwBranch_ok Vb hkb) hk h6
        · cases h
      · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
        exact SixTopD.toDoneG (Hst k hk)
    · exact hwNone_ok
  | Nomm.n11s tag q body, f, P, ht, hfit => by
    have IH := fun fq P' ht' fh' => hcW_sound lib env snd N q fq P' ht' fh'
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeaf_ok hx
    · split
      · rename_i tag' fq _
        try dsimp only
        simp only [FitHW] at hfit
        have V := IH fq P htq hfit
        refine ⟨fun _ h => (by cases h), fun h => ?_, fun h => ?_, fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
        all_goals simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        all_goals obtain ⟨⟨⟨rfl, hs⟩, hsnd⟩, hv⟩ := h
        · exact SurGBT.mono (fun s hs' => ⟨hs', (regLike_soundFit hsnd lib P fq hs').1⟩)
            (surGBT_n11sKept (V.sur hv) hs body)
        · exact regGBT_n11sKept (V.reg hv) hsnd hs body
        · exact doneG_of_next (regGBT_n11sKept (V.reg hv) hsnd hs body) (doneNext_n11s env hs q body)
      · exact hwNone_ok
  | Nomm.n11d tag h q body, f, P, ht, hfit => by
    have IH := fun fq P' ht' fh' => hcW_sound lib env snd N q fq P' ht' fh'
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeaf_ok hx
    · split
      · rename_i tag' fh fq _
        try dsimp only
        simp only [FitHW] at hfit
        have V := IH fq P htq hfit
        split
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨rfl, hs⟩ := hc
          exact hwKeptD_ok hs V
        · exact hwNone_ok
      · exact hwNone_ok
  | Nomm.mean p b q body k, f, P, ht, hfit => by
    have IH := fun fq P' ht' fh' => hcW_sound lib env snd N q fq P' ht' fh'
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcW.eq_def]; dsimp only; split
    · rename_i tag' fp fq
      try dsimp only
      simp only [FitHW] at hfit
      have V := IH fq P htq hfit.1
      split
      · rename_i htag
        subst htag
        exact hwMean_ok V hfit.2
      · exact hwNone_ok
    · exact hwNone_ok

/-- **The contract of the wider class**: every member of `hcW`'s `top` has
both halves of the contract at the top, traces included, under the code
table (`HintTabW`) and the fit facts with the constants of `%mean` (`FitHW`). -/
theorem hintClsW_contract (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    {f : Noun} {nm : Nomm} (hm : (hcW snd f nm).top = true) (ht : HintTabW env N nm) (hfit : FitHW lib env P f nm)
    {c : Straight Map} (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractDoneG lib ((hcW_sound (S := S) (Map := Map) lib env snd N nm f P ht hfit).top hm) hc

end Comp
end SkaModel
end Formalization
