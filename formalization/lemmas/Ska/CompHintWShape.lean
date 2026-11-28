import lemmas.Ska.CompHintClsSound
import lemmas.Ska.CompHintEq
import lemmas.Ska.CompDirectMEq

/-!
# `ShapeH` for more branches of a `%6` (README Gaps 24.22, the wider class)

`ShapeH IsReg` (`CompHintSixRegS2.lean`) of two more shapes of a `%6`
branch, for the wider check of the class:

* **`shapeH_s3bodyShapeW`**: `spotArm`'s `S3` body (`shapeH_s3body`) with
  the `%10` at any axis `a10 ≥ 2`, its value a kept dynamic hint of any tag
  with a constant clue over `[0 a]` at any axis `a ≥ 2` (real `t05` reads
  `[0 12]`), and the direct call `[2 [0 1] [1 F] b]` of any bell; the test
  `isS3BodyShapeW snd` (with `+sound` of `[0 a]` at `%this`).  The proof is
  `shapeH_s3body`'s, the constants `13`, `6` replaced by the parameters
  (`spotS4_bondShapeW`, `shapeH_tenShapeW`).
* **`shapeH_n11dLeafShapeW`**: `shapeH_n11dKept` with the clue `h` any
  nomm of `hcNB` (`[0 a]`, `[1 k]`, `[4 p]`, a cons of those): such a clue
  has no hint and no direct call, so its run is `runLC`'s
  (`runLCH_eq`, `runLCM_true`), whose tags are `tagCA_callTreeA`'s, and it
  has no bond (`hcNB_noBond`).  **`shapeH_meanLeafShapeW`**: the same for a
  `%mean` with no constant (`shapeH_mean`), the trap the clue (real `g05`'s
  trap is `[[1 k] [0 1]]`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The `S3` body at any axis -/

/-- `S4` at any dynamic tag and axis: `[tag [1 k4] [0 a]]`. -/
def s4ShapeW (tag a : Nat) (k4 B : Noun) : Nomm := Nomm.n11d tag (Nomm.n1 k4) (Nomm.n0 a) B

/-- `S3`'s `%10` at any axis: `[10 a10 S4 [0 1]]`. -/
def s3TenShapeW (a10 tag a : Nat) (k4 B : Noun) : Nomm := Nomm.n10 a10 (s4ShapeW tag a k4 B) (Nomm.n0 1)

/-- **The `S3` body at any axis**, `[7 [10 a10 [tag [1 k] [0 a]] [0 1]] [2 [0 1] [1 F] b]]`,
`tag` dynamic, `2 ≤ a`, `2 ≤ a10`, `+sound` of `[0 a]` at `%this`. -/
def isS3BodyShapeW (snd : Nomm → NeedOrd → Bool) : Nomm → Bool
  | Nomm.n7 (Nomm.n10 a10 (Nomm.n11d tag (Nomm.n1 _) (Nomm.n0 a) _) (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 1) (Nomm.n1 _) (some (_, Option.none))) =>
      hintDynamic tag && decide (2 ≤ a) && decide (2 ≤ a10) && snd (Nomm.n0 a) NeedOrd.this
  | _ => false

theorem isS3BodyShapeW_eq {snd : Nomm → NeedOrd → Bool} {nm : Nomm} (h : isS3BodyShapeW snd nm = true) :
    ∃ a10 tag a k4 B F b, nm = Nomm.n7 (s3TenShapeW a10 tag a k4 B) (spotS3Call F b) ∧
      hintDynamic tag = true ∧ 2 ≤ a ∧ 2 ≤ a10 ∧ snd (Nomm.n0 a) NeedOrd.this = true := by
  unfold isS3BodyShapeW at h
  split at h
  · rename_i a10 tag k4 a B F b
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨a10, tag, a, k4, B, F, b, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

section Shape
variable {snd : Nomm → NeedOrd → Bool}

/-- **`S4` at any axis under `%next (ofSure d) th`**: one bond, its label the
block after the epilogue (the text of `spotS4_bond`). -/
theorem spotS4_bondShapeW {env : CallEnv} {tag a : Nat} (hs : hintDynamic tag = true) (ha : 2 ≤ a) (k4 B : Noun)
    {sup : Option Nomm} {d : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hA : HoonSet.small d.lok = true ∧ snd (Nomm.n0 a) (needToOrd d.ned) = true) (d0 : g0.drop = false)
    (hr : runLCH (S := S) (Map := Map) env snd true sup (s4ShapeW tag a k4 B) (CGoalL.next (ofSure d) th) region g0 =
      some (nex, g1)) :
    ∀ e ∈ nex.laz.bond, e.1 = g0.bo + 1 := by
  obtain ⟨nq, gc, nh, gh, h3, hqa, h6, h7⟩ := runLCH_n11d_kept_sur hs hA hr
  obtain ⟨rfl, -⟩ := runLCH_n0_ax ha (entries_ofSure _) h3
  have dc : (genN g0 tag B th).drop = false := d0
  obtain ⟨SB, -⟩ := lazyBound_tagCS nq.th region dc
  simp only [runLCH] at h6
  obtain ⟨o, gm, hm, h6⟩ := bind_some h6
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  have SM := medeL_tagCS (R := region) hm (noEntries_ofSure _)
  have dm := SM.drop.trans (SB.drop.trans dc)
  obtain ⟨rfl, -⟩ := copyL_bond1 dm rfl rfl h7
  intro e he
  simp only [bond_mk, List.mem_singleton] at he
  subst he
  rfl

/-- **`S3`'s `%10` at any axes, at a `RegLike` need**: two entries (the text
of `shapeH_ten`). -/
theorem shapeH_tenShapeW {env : CallEnv} {a10 tag a : Nat} (hs : hintDynamic tag = true) (ha : 2 ≤ a)
    (ha10 : 2 ≤ a10) (k4 B : Noun) (ha' : snd (Nomm.n0 a) NeedOrd.this = true) :
    ShapeH (S := S) (Map := Map) snd env RegLike (s3TenShapeW a10 tag a k4 B) 2 := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  have hv : hinted env.cod (s4ShapeW tag a k4 B) = some true := by
    simp only [s4ShapeW, hinted, hs, orB]
  obtain ⟨d, r, o, g2, nb, g3, nexDon, g4, hi, hcase, hvr, hcp⟩ := runLCH_n10_kept hv hr
  rcases hcase with ⟨h1, h2, -, -⟩ | ⟨-, hlb⟩
  · exact absurd ⟨h1, h2⟩ (into_rec_asks hi ha10)
  rw [lazyBound_apply rfl] at hlb
  simp only [Option.some.injEq, Prod.mk.injEq] at hlb
  obtain ⟨rfl, rfl⟩ := hlb
  have SI : TagCS region g0 g2 := TagCS.of_k (kt_into _ _) (kc_into _ _) (kd_into _ _) hi
  have d2 : g2.drop = false := SI.drop.trans d0
  obtain ⟨SB, TB⟩ := lazyBound_tagCS (jmp0 o) region d2
  have d3 : ((g2.emitted ⟨[], [], Termin.hop (jmp0 o)⟩).tagged g2.bo region).drop = false := SB.drop.trans d2
  obtain ⟨hsm, hord⟩ := into_regLike_sound (a := a10) ha10 hAp hi
  have hA4 : HoonSet.small d.lok = true ∧ snd (Nomm.n0 a) (needToOrd d.ned) = true := ⟨hsm, by rw [hord]; exact ha'⟩
  have H0 : ShapeH (S := S) (Map := Map) snd env
      (fun d : Sure S => HoonSet.small d.lok = true ∧ snd (Nomm.n0 a) (needToOrd d.ned) = true) (Nomm.n0 a) 0 :=
    fun hA d0 hta hr => shapeH_n0 (ax := a)
      (fun d : Sure S => HoonSet.small d.lok = true ∧ snd (Nomm.n0 a) (needToOrd d.ned) = true) ha
      hA d0 hta hr
  obtain ⟨S4, E4, L4⟩ := shapeH_n11dKept (S := S) (Map := Map) (snd := snd) (env := env)
    (Ap := fun d : Sure S => HoonSet.small d.lok = true ∧ snd (Nomm.n0 a) (needToOrd d.ned) = true)
    hs k4 B @H0 (fun _ h => h) hA4 d3 rfl hvr
  have B4 := spotS4_bondShapeW hs ha k4 B hA4 d3 hvr
  have d4 : g4.drop = false := S4.drop.trans d3
  have hent : entries (mk Sure.bunt [] [(g2.bo, ofSure r)] : Lazy S) = [(g2.bo, ofSure r)] := by
    rw [entries_bound1, entries_ofSure]
  obtain ⟨SC, EC⟩ := copyL_tagC hcp (fun e he => by
    rw [hent, List.mem_singleton] at he
    subst he
    exact TB.cs S4) (fun e he => E4 e he)
  have hb : ∀ e ∈ nexDon.laz.bond, g2.bo ≠ e.1 := fun e he => by
    rw [B4 e he]; simp only [tagged_bo, emitted_bo]; omega
  obtain ⟨rfl, -⟩ := copyL_bondFront d4 hb hcp
  refine ⟨SI.trans (SB.trans (S4.trans SC)), EC, ?_⟩
  rw [entries_bondFront _ _ _ _ (entries_ofSure _), List.length_cons]
  simp only [Nat.zero_add] at L4
  omega

/-- **The `S3` body at any axes, at `lazy-from-reg`** (the text of
`shapeH_s3body`): the call's result has no entry and a `RegLike` need, so
the `%10` runs at it. -/
theorem shapeH_s3bodyGenShapeW {env : CallEnv} {a10 tag a : Nat} (hs : hintDynamic tag = true) (ha : 2 ≤ a)
    (ha10 : 2 ≤ a10) (k4 B F : Noun) {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none)
    (hned : env.need b = some bNed) (hpure : env.pure b = false) (ha' : snd (Nomm.n0 a) NeedOrd.this = true) :
    ShapeH (S := S) (Map := Map) snd env IsReg (Nomm.n7 (s3TenShapeW a10 tag a k4 B) (spotS3Call F b)) 2 := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  obtain ⟨rg, rfl⟩ := hAp
  rw [runLCH_n7] at hr
  obtain ⟨nx, g, h1, h2⟩ := bind_some hr
  obtain ⟨SC, E, R, hargs⟩ := call_tagCS hring hned rfl hpure h1
  simp only [NextL.goal] at h2
  rw [eq_ofSure_of_entries E] at h2
  obtain ⟨S2, E2, L2⟩ := shapeH_tenShapeW hs ha ha10 k4 B ha' R (SC.drop.trans d0) hargs h2
  exact ⟨SC.trans S2, E2, L2⟩

/-- **`ShapeH IsReg` of a body `isS3BodyShapeW` takes**, its callee's table
entry (`TabOK`, as `HintTab` gives it) for the ring, need and `pure`. -/
theorem shapeH_s3bodyShapeW {env : CallEnv} {N : Needs} {nm : Nomm} (h : isS3BodyShapeW snd nm = true)
    (hT : ∀ b ∈ callBells nm, TabOK env N b) :
    ShapeH (S := S) (Map := Map) snd env IsReg nm 2 := by
  obtain ⟨a10, tag, a, k4, B, F, b, rfl, hs, ha, ha10, ha'⟩ := isS3BodyShapeW_eq h
  obtain ⟨hring, ⟨bNed, hned, -⟩, -, hpure⟩ :=
    hT b (by simp [callBells, s3TenShapeW, s4ShapeW, spotS3Call])
  exact shapeH_s3bodyGenShapeW hs ha ha10 k4 B F hring hned hpure ha'

/-! ## A kept dynamic hint with a clue of `hcNB` -/

/-- A formula for a nomm of `hcNB` (its erasure): `[0 a]`, `[1 k]`, `[4 p]`, a cons. -/
def folShapeW : Nomm → Noun
  | Nomm.n0 a => slot a
  | Nomm.n1 k => quote k
  | Nomm.n4 p => n2 (A 4) (folShapeW p)
  | Nomm.cons p q => C (folShapeW p) (folShapeW q)
  | _ => A 0

/-- **A nomm of `hcNB` is in `CallTreeA`** (with its erasure), and has no
hint and no direct call. -/
theorem hcNB_callTreeAShapeW : ∀ (nm : Nomm), hcNB nm = true →
    (∃ x, CallTreeA x (folShapeW nm) nm) ∧ nm.noHint = true ∧ nm.noDirect = true
  | Nomm.n0 a, _ => ⟨⟨_, CallTreeA.n0 a⟩, rfl, rfl⟩
  | Nomm.n1 k, _ => ⟨⟨_, CallTreeA.n1 k⟩, rfl, rfl⟩
  | Nomm.n4 p, h => by
    simp only [hcNB] at h
    obtain ⟨⟨x, T⟩, h1, h2⟩ := hcNB_callTreeAShapeW p h
    exact ⟨⟨_, CallTreeA.four T⟩, by simpa [Nomm.noHint] using h1, by simpa [Nomm.noDirect] using h2⟩
  | Nomm.cons p q, h => by
    simp only [hcNB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hq⟩, _⟩, _⟩ := h
    obtain ⟨⟨x, Tp⟩, hp1, hp2⟩ := hcNB_callTreeAShapeW p hp
    obtain ⟨⟨y, Tq⟩, hq1, hq2⟩ := hcNB_callTreeAShapeW q hq
    have hcell : ∃ a1 a2, folShapeW p = C a1 a2 := by
      cases p with
      | n0 a => exact ⟨_, _, rfl⟩
      | n1 k => exact ⟨_, _, rfl⟩
      | n4 p' => exact ⟨_, _, rfl⟩
      | cons p1 p2 => exact ⟨_, _, rfl⟩
      | _ => simp [hcNB] at hp
    obtain ⟨a1, a2, he⟩ := hcell
    have Tp' : CallTreeA x (C a1 a2) p := he ▸ Tp
    have T : CallTreeA (y && (x || !q.pure)) (folShapeW (Nomm.cons p q)) (Nomm.cons p q) := by
      show CallTreeA _ (C (folShapeW p) (folShapeW q)) (Nomm.cons p q)
      rw [he]
      exact CallTreeA.cons Tp' Tq
    exact ⟨⟨_, T⟩, by simp [Nomm.noHint, hp1, hq1], by simp [Nomm.noDirect, hp2, hq2]⟩
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

/-- **The run of a clue of `hcNB` under `%next (ofSure sur) th`**: `TagCS`
of the region, no entry. -/
theorem clue_tagShapeW {env : CallEnv} {h : Nomm} (hh : hcNB h = true) {sup : Option Nomm} {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (d0 : g0.drop = false)
    (hr : runLCH (S := S) (Map := Map) env snd true sup h (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    TagCS region g0 g1 ∧ entries nex.laz = [] := by
  obtain ⟨⟨x, T⟩, hn, hd⟩ := hcNB_callTreeAShapeW h hh
  rw [runLCH_eq env snd true h hn, runLCM_true env hd] at hr
  obtain ⟨SC, -⟩ := tagCA_callTreeA (S := S) (Map := Map) env T d0 (noEntries_ofSure _) hr
  obtain ⟨hf, hb⟩ := hcNB_noBond (S := S) (Map := Map) (snd := snd) (env := env) h hh
    (by rw [runLCH_eq env snd true h hn, runLCM_true env hd]; exact hr)
  refine ⟨SC, ?_⟩
  rcases nex with ⟨⟨s1, f1, b1⟩, th1⟩
  simp only at hf hb
  subst hf hb
  simp [entries, bondEntries, forkEntries]

/-- **A kept dynamic hint with a clue of `hcNB` over `q`**, `+sound` of the
goal's need: one entry more than `q` (the text of `shapeH_n11dKept`, the
clue's run by `clue_tagShapeW`). -/
theorem shapeH_n11dLeafShapeW {env : CallEnv} {Ap : Sure S → Prop} {h q : Nomm} {k : Nat} {tag : Nat}
    (hs : hintDynamic tag = true) (hh : hcNB h = true) (body : Noun) (Hq : ShapeH (S := S) (Map := Map) snd env Ap q k)
    (hA : ∀ sur : Sure S, Ap sur → HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true) :
    ShapeH (S := S) (Map := Map) snd env Ap (Nomm.n11d tag h q body) (k + 1) := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  obtain ⟨nq, gc, nh, gh, h3, hqa, h6, h7⟩ := runLCH_n11d_kept_sur hs (hA sur hAp) hr
  have S0 : TagCS region g0 (genN g0 tag body th) := TagCS.of_eqs rfl rfl rfl
  obtain ⟨Sq, Eq, Lq⟩ := Hq hAp (show (genN g0 tag body th).drop = false from d0) rfl h3
  have dc : gc.drop = false := Sq.drop.trans d0
  obtain ⟨SB, TB⟩ := lazyBound_tagCS nq.th region dc
  have SP : TagCS region ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
      (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩) := TagCS.of_eqs rfl rfl rfl
  -- the clue
  have dP : (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩).drop = false := SP.drop.trans (SB.drop.trans dc)
  obtain ⟨SM, EM⟩ := clue_tagShapeW (env := env) hh dP h6
  have dm := SM.drop.trans dP
  obtain ⟨hfh, hbh⟩ := hcNB_noBond (S := S) (Map := Map) (snd := snd) (env := env) h hh h6
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = (gc.bo, nq.laz) :: entries nq.laz :=
    entries_bound1 _ _ _
  obtain ⟨SC, EC⟩ := copyL_tagC h7 (fun e he => by rw [EM] at he; cases he) (fun e he => by
    rw [hent, List.mem_cons] at he
    rcases he with rfl | he
    · exact (TB.cs SP).cs SM
    · exact (((Eq e he).cs SB).cs SP).cs SM)
  obtain ⟨rfl, -⟩ := copyL_bond1 dm hfh hbh h7
  refine ⟨S0.trans (Sq.trans (SB.trans (SP.trans (SM.trans SC)))), EC, ?_⟩
  rw [entries_bound1, List.length_cons]
  omega

/-- **A `%mean` with no constant, its trap of `hcNB`** (`shapeH_mean`). -/
theorem shapeH_meanLeafShapeW {env : CallEnv} {Ap : Sure S → Prop} {p q : Nomm} {b : Bell} {body : Noun}
    {kk : Option Noun} {k : Nat} (hk : meanKonst env b kk = Option.none) (hh : hcNB p = true)
    (Hq : ShapeH (S := S) (Map := Map) snd env Ap q k)
    (hA : ∀ sur : Sure S, Ap sur → HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true) :
    ShapeH (S := S) (Map := Map) snd env Ap (Nomm.mean p b q body kk) (k + 1) :=
  shapeH_mean hk (shapeH_n11dLeafShapeW mean_dynamic hh body Hq hA)

end Shape

end Comp
end SkaModel
end Formalization
