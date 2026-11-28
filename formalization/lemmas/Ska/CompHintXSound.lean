import lemmas.Ska.CompHintXBat
import lemmas.Ska.CompHintWSound

/-!
# The class `hcX`: soundness and the contract (README Gaps 24.24)

* `RunOKGBT.minkAsP` and the goal kinds through `MinkAsP` (the formula runs
  as another on the subjects of `P`); `minkAsP_of_c7` (a `MinkC7` whose
  first formula is `[0 1]`), `minkAsP_inline` (the inlined call: on the
  subjects whose axis `a` is `F`, `[2 [0 1] [0 a]]` runs as `F`),
  `minkAsP_nine01`, `minkAsP_seven01`.
* `hw01_ok`, `hwOr_ok`, `hwLeafX_ok` (`ShapeH` `0` of an `hcNB` leaf by
  `clue_tagShapeW`), `batOK_at`.
* **`hcX_sound`**: one structural recursion over all nomm constructors.
* **`hintClsX_contract`**: a member of `hcX`'s `top`, under `HintTabW`,
  `FitHX` and `BatOK`, has both halves of the contract at the top;
  **`hintClsX_contract_less`**: at a bell, `bat` read from its `less`
  (`sockBat`), `BatOK` discharged on `Fits bl.less` (`batOK_less`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- (The text of `RunOKGBT.minkAs` with `MinkAsP`.) -/
theorem RunOKGBT.minkAsP {lib : Lib} {N : Needs} {P : Noun → Prop} {f f' : Noun} {goal : CGoal S}
    {g0 g1 : Gen Map} {nex : NextL S} (M : MinkAsP lib P f' f) (R : RunOKGBT lib N P f goal g0 g1 nex) :
    RunOKGBT lib N P f' goal g0 g1 nex where
  ext := R.ext
  grow := R.grow
  cfr := R.cfr
  lo := R.lo
  hi := R.hi
  ent := R.ent
  regs := R.regs
  dist := R.dist
  eregs := R.eregs
  labs := R.labs
  nodup := R.nodup
  nec := fun s hs hfit => by
    obtain ⟨h1, h2⟩ := R.nec s hs hfit
    refine ⟨fun gul n tm r h => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', -, h'⟩ := M.fwd hs h
      exact h1 gul n' tm r h'
    · obtain ⟨r, hm, hb⟩ := h2 gul tm
      exact ⟨r, M.bwd hs hm, hb⟩
  ncond := R.ncond
  econd := R.econd
  sem := fun cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI ht hP hm => by
    obtain ⟨n', hn, h'⟩ := M.fwd hP hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn) st t tm s0 s r hI ht hP h'
  semB := fun cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg => by
    obtain ⟨r, hm, hg'⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg
    exact ⟨r, M.bwd hP hm, hg'⟩

/-- **A `MinkC7` whose first formula is `[0 1]`** runs as its second. -/
theorem minkAsP_of_c7 {lib : Lib} {P : Noun → Prop} {f c : Noun} (M : MinkC7 lib P f (slot 1) c) :
    MinkAsP lib P f c where
  fwd := fun {gul n tm s r} hs h => by
    obtain ⟨n1, hn1, rb, hb, h1 | ⟨u, rfl, n2, hn2, hc⟩⟩ := M.fwd hs h
    · cases n1 with
      | zero => simp [minkF] at hb
      | succ m => rw [minkF_slot1] at hb; cases hb; exact absurd rfl (h1.1 s)
    · cases n1 with
      | zero => simp [minkF] at hb
      | succ m => rw [minkF_slot1] at hb; cases hb; exact ⟨n2, hn2, hc⟩
  bwd := fun {gul tm s r} hs hc => (M.bwd hs ⟨1, minkF_slot1 lib gul 0 tm s⟩).2 s r rfl hc

theorem MinkAs.toP {lib : Lib} {P : Noun → Prop} {f c : Noun} (M : MinkAs lib f c) : MinkAsP lib P f c :=
  ⟨fun _ h => M.fwd h, fun _ h => M.bwd h⟩

/-- **The inlined call**: on the subjects whose axis `a` is `F`, `[2 [0 1] [0 a]]` runs as `F`. -/
theorem minkAsP_inline (lib : Lib) {P : Noun → Prop} {a : Nat} {F : Noun} (hs : ∀ s, P s → slot? a s = some F) :
    MinkAsP lib P (n3 (A 2) (slot 1) (slot a)) F :=
  minkAsP_of_c7 (minkC7_inline lib (fun x gul hx => slot_hq2 (hs x hx)))

theorem minkAsP_nine01 (lib : Lib) (P : Noun → Prop) (a : Nat) :
    MinkAsP lib P (n3 (A 9) (A a) (slot 1)) (n3 (A 2) (slot 1) (slot a)) :=
  minkAsP_of_c7 (minkC7_nine lib P a (slot 1))

theorem minkAsP_seven01 (lib : Lib) (P : Noun → Prop) (c : Noun) : MinkAsP lib P (n3 (A 7) (slot 1) c) c :=
  (minkAs_seven01 lib c).toP

theorem batOK_at {lib : Lib} {bat : Bat} {P : Noun → Prop} (h : BatOK bat P) (b : Noun) :
    BatOK (batAt bat b) (Img lib P b) := by
  unfold batAt
  split
  · rename_i e; subst e; rw [img_slot1]; exact h
  · exact batOK_noBat _

section
variable {lib : Lib} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {N : Needs} {P : Noun → Prop}

/-- **`[7 [0 1] q]`** with a formula that runs as `q`'s. -/
theorem hw01_ok {f c : Noun} {q : Nomm} {vq : HW} (M : MinkAsP lib P f c)
    (V : HWOK (S := S) (Map := Map) lib env snd N P c q vq) :
    HWOK (S := S) (Map := Map) lib env snd N P f (Nomm.n7 (Nomm.n0 1) q) (hw01 vq) := by
  have Hreg : vq.reg = true → RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n7 (Nomm.n0 1) q) := by
    intro h sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
    rw [runLCH_seven01] at hr
    exact (V.reg h b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr).minkAsP M
  have Hft : vq.ft = true → RegFT (S := S) (Map := Map) snd lib N env P f (Nomm.n7 (Nomm.n0 1) q) := by
    intro h sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
    rw [runLCH_seven01] at hr
    have R := V.ft h b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
    exact ⟨R.run.minkAsP M, R.nent, R.flat, R.clean, R.eclean⟩
  refine ⟨fun _ h => by simp [hw01] at h, fun h => ?_, fun h => ?_, Hft, fun h => by simp [hw01] at h,
    fun h => ?_, fun h => ?_, fun _ h => by simp [hw01] at h, fun _ h => by simp [hw01] at h⟩
  · intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr
    rw [runLCH_seven01] at hr
    exact (V.sur h hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr).minkAsP M
  · simp only [hw01, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Hreg h
    · exact RegFT.toReg (Hft h)
  · intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_seven01] at hr
    have D := V.dall h b0 d0 hu hcl hcb hr
    exact ⟨D.run.minkAsP M, D.nent, D.flat, D.clean, D.eclean⟩
  · intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_seven01] at hr
    exact (V.top h b0 d0 hu hcl hcb hr).minkAsP M

theorem option_or_some {α : Type} {o o' : Option α} {x : α} (h : o.or o' = some x) : o = some x ∨ o' = some x := by
  cases o <;> simp_all

/-- **Either set of fields.** -/
theorem hwOr_ok {f : Noun} {nm : Nomm} {v w : HW} (V : HWOK (S := S) (Map := Map) lib env snd N P f nm v)
    (W : HWOK (S := S) (Map := Map) lib env snd N P f nm w) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm (hwOr v w) := by
  refine ⟨fun x h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun k h => ?_, fun k h => ?_⟩
  all_goals simp only [hwOr, Bool.or_eq_true] at h
  · rcases option_or_some h with h | h
    · exact V.leaf x h
    · exact W.leaf x h
  · rcases h with h | h
    · exact V.sur h
    · exact W.sur h
  · rcases h with h | h
    · exact V.reg h
    · exact W.reg h
  · rcases h with h | h
    · exact V.ft h
    · exact W.ft h
  · rcases h with h | h
    · obtain ⟨a, b⟩ := V.zc h; exact ⟨by simp [hwOr, a], b⟩
    · obtain ⟨a, b⟩ := W.zc h; exact ⟨by simp [hwOr, a], b⟩
  · rcases h with h | h
    · exact V.dall h
    · exact W.dall h
  · rcases h with h | h
    · exact V.top h
    · exact W.top h
  · rcases option_or_some h with h | h
    · exact V.sh k h
    · exact W.sh k h
  · rcases option_or_some h with h | h
    · exact V.st k h
    · exact W.st k h

/-- **`ShapeH` `0` of an `hcNB` nomm** (`clue_tagShapeW`). -/
theorem shapeH_hcNB {Ap : Sure S → Prop} {nm : Nomm} (hh : hcNB nm = true) :
    ShapeH (S := S) (Map := Map) snd env Ap nm 0 := by
  intro sup sur th region g0 g1 nex hA d0 hta hr
  obtain ⟨T, hE⟩ := clue_tagShapeW hh d0 hr
  refine ⟨T, ?_, ?_⟩
  · intro e he; rw [hE] at he; cases he
  · rw [hE]; simp

theorem hwLeafX_sh (lib : Lib) (N : Needs) (P : Noun → Prop) {f : Noun} {nm : Nomm} {x : Bool} (hx : hcLeaf f nm = some x) :
    ∀ k, (hwLeafX x f nm).sh = some k → ShapeH (S := S) (Map := Map) snd env IsReg nm k := by
  intro k h
  simp only [hwLeafX] at h
  rcases option_or_some h with h | h
  · exact (hwLeaf_ok (S := S) (Map := Map) (lib := lib) (env := env) (snd := snd) (N := N) (P := P) hx).sh k h
  · split at h
    · rename_i hh; cases h; exact shapeH_hcNB hh
    · cases h

/-- **A leaf** (`hwLeafX`). -/
theorem hwLeafX_ok {f : Noun} {nm : Nomm} {x : Bool} (hx : hcLeaf f nm = some x) :
    HWOK (S := S) (Map := Map) lib env snd N P f nm (hwLeafX x f nm) := by
  have V := hwLeaf_ok (S := S) (Map := Map) (lib := lib) (env := env) (snd := snd) (N := N) (P := P) hx
  exact ⟨V.leaf, V.sur, V.reg, V.ft, V.zc, V.dall, V.top, hwLeafX_sh lib N P hx, V.st⟩

theorem HWOK.withClue {f : Noun} {nm : Nomm} {v : HW} (V : HWOK (S := S) (Map := Map) lib env snd N P f nm v)
    (c : Bool) : HWOK (S := S) (Map := Map) lib env snd N P f nm { v with clue := c } :=
  ⟨V.leaf, V.sur, V.reg, V.ft, V.zc, V.dall, V.top, V.sh, V.st⟩

/-- **A `[4 p]` leaf with `p`'s `sh` or its own.** -/
theorem hwLeafFourX_ok {fb : Noun} {p : Nomm} {x : Bool} (hx : hcLeaf (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p) = some x)
    {sh : Option Nat} (hsh : ∀ k, sh = some k → ShapeH (S := S) (Map := Map) snd env IsReg p k) :
    HWOK (S := S) (Map := Map) lib env snd N P (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p)
      { hwLeafX x (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p) with
        sh := sh.or (hwLeafX x (Noun.cell (Noun.atom 4) fb) (Nomm.n4 p)).sh } := by
  have V := hwLeafX_ok (S := S) (Map := Map) (lib := lib) (env := env) (snd := snd) (N := N) (P := P) hx
  refine ⟨V.leaf, V.sur, V.reg, V.ft, V.zc, V.dall, V.top, fun k hk => ?_, V.st⟩
  rcases option_or_some hk with h | h
  · exact shapeH_four (hsh k h)
  · exact V.sh k h

end

/-- **The class `hcX` is sound**: every field of `hcX` meets its promise. -/
theorem hcX_sound (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) :
    ∀ (nm : Nomm) (f : Noun) (P : Noun → Prop) (bat : Bat), BatOK bat P → HintTabW env N nm →
      FitHX lib env bat P f nm → HWOK (S := S) (Map := Map) lib env snd N P f nm (hcX snd bat f nm)
  | Nomm.n0 a, f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeafX_ok hx
    · exact hwNone_ok
  | Nomm.n1 k, f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeafX_ok hx
    · split
      · rename_i hd; exact hwDrop_ok hd
      · exact hwNone_ok
  | Nomm.cons p q, f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; split
    · rename_i x hx; exact (hwLeafX_ok hx).withClue _
    · exact hwNone_ok
  | Nomm.n5 p q, f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeafX_ok hx
    · exact hwNone_ok
  | Nomm.n12 p q, f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; exact hwNone_ok
  | Nomm.n4 p, f, P, bat, hb, ht, hfit => by
    have IH := fun fb P' bat' hb' ht' fh' => hcX_sound lib env snd N p fb P' bat' hb' ht' fh'
    have htp : HintTabW env N p := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i fb
      try dsimp only
      have V := IH fb P bat hb htp (by simpa [FitHX] using hfit)
      split
      · rename_i x hx; exact hwLeafFourX_ok hx V.sh
      · exact ⟨fun _ h => (by cases h), fun h => surGBT_four (V.reg h) (minkC4_four lib P fb),
          fun h => regGBT_four (V.reg h) (minkC4_four lib P fb), fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => doneG_four lib (V.reg h) (minkC4_four lib P fb),
          fun k h => shapeH_four (V.sh k h), fun _ h => (by cases h)⟩
    · exact hwNone_ok
  | Nomm.n3 p, f, P, bat, hb, ht, hfit => by
    have IH := fun fb P' bat' hb' ht' fh' => hcX_sound lib env snd N p fb P' bat' hb' ht' fh'
    have htp : HintTabW env N p := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i fb
      try dsimp only
      split
      · rename_i x hx; exact hwLeafX_ok hx
      · have V := IH fb P bat hb htp (by simpa [FitHX] using hfit)
        exact ⟨fun _ h => (by cases h), fun h => surGBT_three (V.reg h) (minkC3_three lib P fb),
          fun h => regGBT_three (V.reg h) (minkC3_three lib P fb), fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩
    · exact hwNone_ok
  | Nomm.n2 p q Option.none, f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; split
    · try dsimp only
      split
      · rename_i x hx; exact hwLeafX_ok hx
      · exact hwNone_ok
    · exact hwNone_ok
  | Nomm.n2 p q (some (b, some k)), f, P, bat, hb, ht, hfit => by
    rw [hcX.eq_def]; dsimp only; split
    · exact hwNone_ok
    · exact hwNone_ok
  | Nomm.n2 p q (some (b, Option.none)), f, P, bat, hb, ht, hfit => by
    obtain ⟨hring, ⟨bNed, hned, hNf⟩, ⟨ndT, hNt⟩, hpure⟩ := ht b (by simp [callBells])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i fb fq
      try dsimp only
      simp only [FitHX] at hfit
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
  | Nomm.n7 p q, f, P, bat, hb, ht, hfit => by
    have IHp := fun fb P' bat' hb' ht' fh' => hcX_sound lib env snd N p fb P' bat' hb' ht' fh'
    have IHq := fun fc P' bat' hb' ht' fh' => hcX_sound lib env snd N q fc P' bat' hb' ht' fh'
    have htp : HintTabW env N p := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    have e1 : batAt bat (Noun.cell (Noun.atom 0) (Noun.atom 1)) = bat := if_pos rfl
    have e2 : Img lib P (Noun.cell (Noun.atom 0) (Noun.atom 1)) = P := img_slot1 lib P
    rw [hcX.eq_def]; dsimp only; split
    · rename_i b c
      try dsimp only
      split
      · rename_i x hx; exact hwLeafX_ok hx
      · simp only [FitHX] at hfit
        split
        · have hq' := hfit.2
          rw [e1, e2] at hq'
          exact hw01_ok (minkAsP_seven01 lib P _) (IHq _ P bat hb htq hq')
        · exact hw7G_ok (minkC7_seven lib P b c) (IHp b P bat hb htp hfit.1) (IHq c _ _ (batOK_at hb b) htq hfit.2) ht
    · rename_i a c
      simp only [FitHX] at hfit
      split
      · have hq' := hfit.2
        rw [e1, e2] at hq'
        have Vq := IHq _ P bat hb htq hq'
        have Vq' : HWOK (S := S) (Map := Map) lib env snd N (Img lib P (Noun.cell (Noun.atom 0) (Noun.atom 1)))
            (Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1)) (Noun.cell (Noun.atom 0) (Noun.atom a)))) q
            (hcX snd bat (Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
              (Noun.cell (Noun.atom 0) (Noun.atom a)))) q) := by
          rw [e2]; exact Vq
        exact hwOr_ok (hw7G_ok (minkC7_nine lib P a _) (IHp _ P bat hb htp hfit.1) Vq' ht)
          (hw01_ok (minkAsP_nine01 lib P a) Vq)
      · exact hw7G_ok (minkC7_nine lib P a c) (IHp c P bat hb htp hfit.1) (IHq _ _ _ (batOK_at hb c) htq hfit.2) ht
    · rename_i a1 a2 c
      simp only [FitHX] at hfit
      exact hw7G_ok (minkC7_eight lib P a1 a2 c) (IHp _ P bat hb htp (by simp only [FitHX]))
        (IHq c _ noBat (batOK_noBat _) htq hfit.2) ht
    · rename_i a
      simp only [FitHX] at hfit
      split
      · exact hw01_ok (minkAsP_inline lib (hb a _ ‹bat a = some _›)) (IHq _ P bat hb htq (hfit _ ‹bat a = some _›))
      · exact hwNone_ok
    · exact hwNone_ok
  | Nomm.n10 a v q, f, P, bat, hb, ht, hfit => by
    have IH := fun fv P' bat' hb' ht' fh' => hcX_sound lib env snd N v fv P' bat' hb' ht' fh'
    have htv : HintTabW env N v := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i a' fv fq
      try dsimp only
      simp only [FitHX] at hfit
      have Vv := IH fv P bat hb htv hfit
      refine hwSur3_ok (fun hh => ?_) (doneNext_n10 env a v q)
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
      obtain ⟨⟨⟨⟨rfl, ha⟩, hv⟩, hm⟩, hs⟩ := hh
      split at hm
      · exact surGBT_tenKept' ha (hinted_crash hv env.cod) (Vv.sur hs) (fun hR hi => into_regLike_reg ha hR hi)
      · cases hm
    · exact hwNone_ok
  | Nomm.n6 c a b, f, P, bat, hb, ht, hfit => by
    have IHa := fun fa P' bat' hb' ht' fh' => hcX_sound lib env snd N a fa P' bat' hb' ht' fh'
    have IHb := fun fb P' bat' hb' ht' fh' => hcX_sound lib env snd N b fb P' bat' hb' ht' fh'
    have hta : HintTabW env N a := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    have htb : HintTabW env N b := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i fc fa fb
      try dsimp only
      simp only [FitHX] at hfit
      have Va := IHa fa P bat hb hta hfit.1
      have Vb := IHb fb P bat hb htb hfit.2
      have Hst : ∀ k, (match (hcX snd bat fa a).st, (hcX snd bat fb b).st with
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
  | Nomm.n11s tag q body, f, P, bat, hb, ht, hfit => by
    have IH := fun fq P' bat' hb' ht' fh' => hcX_sound lib env snd N q fq P' bat' hb' ht' fh'
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeafX_ok hx
    · split
      · rename_i tag' fq _
        try dsimp only
        simp only [FitHX] at hfit
        have V := IH fq P bat hb htq hfit
        refine ⟨fun _ h => (by cases h), fun h => ?_, fun h => ?_, fun h => (by cases h), fun h => (by cases h),
          fun h => (by cases h), fun h => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
        all_goals simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        all_goals obtain ⟨⟨⟨rfl, hs⟩, hsnd⟩, hv⟩ := h
        · exact SurGBT.mono (fun s hs' => ⟨hs', (regLike_soundFit hsnd lib P fq hs').1⟩)
            (surGBT_n11sKept (V.sur hv) hs body)
        · exact regGBT_n11sKept (V.reg hv) hsnd hs body
        · exact doneG_of_next (regGBT_n11sKept (V.reg hv) hsnd hs body) (doneNext_n11s env hs q body)
      · exact hwNone_ok
  | Nomm.n11d tag h q body, f, P, bat, hb, ht, hfit => by
    have IH := fun fq P' bat' hb' ht' fh' => hcX_sound lib env snd N q fq P' bat' hb' ht' fh'
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i x hx; exact hwLeafX_ok hx
    · split
      · rename_i tag' fh fq _
        try dsimp only
        simp only [FitHX] at hfit
        have V := IH fq P bat hb htq hfit
        split
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨rfl, hs⟩ := hc
          exact hwKeptD_ok hs V
        · exact hwNone_ok
      · exact hwNone_ok
  | Nomm.mean p b q body k, f, P, bat, hb, ht, hfit => by
    have IH := fun fq P' bat' hb' ht' fh' => hcX_sound lib env snd N q fq P' bat' hb' ht' fh'
    have htq : HintTabW env N q := hintTabW_mono ht (fun b hb => by simp [callBells, hb])
    rw [hcX.eq_def]; dsimp only; split
    · rename_i tag' fp fq
      try dsimp only
      simp only [FitHX] at hfit
      have V := IH fq P bat hb htq hfit.1
      split
      · rename_i htag
        subst htag
        exact hwMean_ok V hfit.2
      · exact hwNone_ok
    · exact hwNone_ok

/-- **The contract of the class `hcX`**: every member of `hcX`'s `top` has
both halves of the contract at the top, traces included, under the code
table (`HintTabW`), the fit facts (`FitHX`) and what `bat` says (`BatOK`). -/
theorem hintClsX_contract (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    {bat : Bat} {f : Noun} {nm : Nomm} (hm : (hcX snd bat f nm).top = true) (hb : BatOK bat P)
    (ht : HintTabW env N nm) (hfit : FitHX lib env bat P f nm)
    {c : Straight Map} (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractDoneG lib ((hcX_sound (S := S) (Map := Map) lib env snd N nm f P bat hb ht hfit).top hm) hc

/-- **At a bell**: `bat` read from the bell's `less` (`sockBat`), on the
subjects that fit it (`BatOK` by `batOK_less`). -/
theorem hintClsX_contract_less (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (bl : Bell)
    {f : Noun} {nm : Nomm} (hm : (hcX snd (sockBat bl.less) f nm).top = true) (ht : HintTabW env N nm)
    (hfit : FitHX lib env (sockBat bl.less) (SkaModel.Fits bl.less) f nm)
    {c : Straight Map} (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  hintClsX_contract lib env snd N _ hm (batOK_less bl.less) ht hfit hc

end Comp
end SkaModel
end Formalization
