import lemmas.Ska.CompHintSixRegClass
import lemmas.Ska.CompHintTenSur
import lemmas.Ska.CompSixNxTag

/-!
# The entries and the tag clause of `spotArm`'s branch `S2` (README Gaps 24.21)

`regGBT_spotSix` / `contract_spotS1` (`CompHintSixRegClass.lean`) take, of
the branch `S2 = [spot [4 S3]]`, the bound `EntH IsReg S2 4` and the tag
clause `TagH IsReg S2`, both over every state.  The runs of `S2` keep the
states' `drop`, and a kept hint's `+lazy-bound` sets a tag only when `drop`
is `|`, so the facts are proved at the states with `drop` `|` and a jump
without arguments, which is what `SixNH` gives its branches:

* `ShapeH`: under `%next (ofSure sur) th`, `sur` in `Ap`, `drop` `|`,
  `th.args = []`: `TagCS` of the region (so `CondTag`), the result's entries
  at blocks tagged within the region, and at most `k` of them.
* The constructors: `shapeH_n0` (`[0 a]`, `2 ≤ a`, no entry),
  `shapeH_n11dKept` (a kept dynamic hint with a constant clue over `q`: one
  entry more, `+sound` of the goal's need), `shapeH_four` (`[4 p]` at
  `lazy-from-reg`), `call_tagCS` (the direct call with `p = [0 1]`:
  `+need-ord-alloc-regs`, `+kerf`, `+mono-try-loop`, `+copy`),
  `shapeH_ten` (`S3`'s `%10`: `+into`, `+lazy-bound`, `S4`, `+copy` of the
  parked recipient: two entries), `shapeH_s3body` (`S3`'s `%7`), and
  **`shapeH_spotS2`**: `ShapeH IsReg S2 4`.
* `into_regLike_sound`: `+into` of a `RegLike` need gives a donor need that
  asks one register with an empty lock (`intoLoop_this`), so `S4`'s `+sound`
  is `snd [0 13] %this`.
* `sixNH_of_shape` (`sixNH_of` from `ShapeH`), **`regGBT_spotSixW`**,
  **`contract_spotS1W`** (`regGBT_spotSix`, `contract_spotS1` with `ShapeH` in
  place of `EntH` and `TagH`), **`contract_spotS1S2`** (`S2` itself, its
  `ShapeH` discharged: only its `RegGBT` is left as a premise).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- **The shape of the runs under `%next (ofSure sur) th`, `sur` in `Ap`**,
at the states with `drop` `|` and a jump without arguments: the run sets
tags and adds `cond` keys only within the region, the result's entries are
at blocks tagged within it, and there are at most `k`. -/
abbrev ShapeH (snd : Nomm → NeedOrd → Bool) (env : CallEnv) (Ap : Sure S → Prop) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Ap sur → g0.drop = false → th.args = [] →
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    TagCS region g0 g1 ∧ (∀ e ∈ entries nex.laz, TagOK region g1 e.1) ∧ (entries nex.laz).length ≤ k

/-! ## The steps -/

/-- **`+lazy-bound`'s block** is tagged with the region, and nothing else
changes but the blocks. -/
theorem lazyBound_tagCS (th : Jmp) (region : List Nat) {g : Gen Map} (hd : g.drop = false) :
    TagCS region g ((g.emitted ⟨[], [], Termin.hop th⟩).tagged g.bo region) ∧
      TagOK region ((g.emitted ⟨[], [], Termin.hop th⟩).tagged g.bo region) g.bo := by
  have d1 : (g.emitted ⟨[], [], Termin.hop th⟩).drop = false := hd
  have et : (g.emitted ⟨[], [], Termin.hop th⟩).tagged g.bo region =
      { (g.emitted ⟨[], [], Termin.hop th⟩) with
        tags := HoonMap.put (g.emitted ⟨[], [], Termin.hop th⟩).tags g.bo region } := by
    simp only [Gen.tagged, d1, Bool.false_eq_true, ↓reduceIte]
  rw [et]
  refine ⟨(TagCS.of_eqs (R := region) (g := g) (g' := g.emitted ⟨[], [], Termin.hop th⟩) rfl rfl rfl).trans
    ⟨fun x t ex => ?_, CondTag.refl _, rfl⟩, fun t ex => ?_⟩
  · simp only [HoonMap.get_put] at ex
    split at ex
    · cases ex; exact Or.inr (sfx_refl region)
    · exact Or.inl ex
  · simp only [HoonMap.get_put, if_true] at ex
    cases ex; exact sfx_refl region

theorem kt_needOrdAllocRegsH : ∀ (ord : NeedOrd), KT (needOrdAllocRegs ord : CM Map Need)
  | NeedOrd.none => by unfold needOrdAllocRegs; kt
  | NeedOrd.this => by unfold needOrdAllocRegs; kt
  | NeedOrd.pair p q => by
    unfold needOrdAllocRegs
    exact KT.bind' (kt_needOrdAllocRegsH p) fun _ => KT.bind' (kt_needOrdAllocRegsH q) fun _ => by kt
  | NeedOrd.both p q => by
    unfold needOrdAllocRegs
    exact KT.bind' KT.re' fun _ =>
      KT.bind' (kt_needOrdAllocRegsH p) fun _ => KT.bind' (kt_needOrdAllocRegsH q) fun _ => by kt

theorem kd_needOrdAllocRegsH : ∀ (ord : NeedOrd), KD (needOrdAllocRegs ord : CM Map Need)
  | NeedOrd.none => by unfold needOrdAllocRegs; kd
  | NeedOrd.this => by unfold needOrdAllocRegs; kd
  | NeedOrd.pair p q => by
    unfold needOrdAllocRegs
    exact KD.bind' (kd_needOrdAllocRegsH p) fun _ => KD.bind' (kd_needOrdAllocRegsH q) fun _ => by kd
  | NeedOrd.both p q => by
    unfold needOrdAllocRegs
    exact KD.bind' KD.re' fun _ =>
      KD.bind' (kd_needOrdAllocRegsH p) fun _ => KD.bind' (kd_needOrdAllocRegsH q) fun _ => by kd

theorem kc_monoTryLoopH (fail : Nat) : ∀ (ned : Need) (r o : Nat), KC (monoTryLoop fail ned r o : CM Map Nat)
  | Need.none, _, _ => by unfold monoTryLoop; kc
  | Need.this _, _, _ => by unfold monoTryLoop; kc
  | Need.pair h t, r, o => by
    unfold monoTryLoop
    exact KC.bind' KC.re' fun rt => KC.bind' KC.re' fun rh => KC.bind' (kc_monoTryLoopH fail t rt o) fun ot =>
      KC.bind' (kc_monoTryLoopH fail h rh ot) fun _ => by kc
  | Need.both _ h t, r, o => by
    unfold monoTryLoop
    exact KC.bind' KC.re' fun rt => KC.bind' KC.re' fun rh => KC.bind' (kc_monoTryLoopH fail t rt o) fun ot =>
      KC.bind' (kc_monoTryLoopH fail h rh ot) fun _ => by kc

theorem kt_monoTryLoopH (fail : Nat) : ∀ (ned : Need) (r o : Nat), KT (monoTryLoop fail ned r o : CM Map Nat)
  | Need.none, _, _ => by unfold monoTryLoop; kt
  | Need.this _, _, _ => by unfold monoTryLoop; kt
  | Need.pair h t, r, o => by
    unfold monoTryLoop
    exact KT.bind' KT.re' fun rt => KT.bind' KT.re' fun rh => KT.bind' (kt_monoTryLoopH fail t rt o) fun ot =>
      KT.bind' (kt_monoTryLoopH fail h rh ot) fun _ => by kt
  | Need.both _ h t, r, o => by
    unfold monoTryLoop
    exact KT.bind' KT.re' fun rt => KT.bind' KT.re' fun rh => KT.bind' (kt_monoTryLoopH fail t rt o) fun ot =>
      KT.bind' (kt_monoTryLoopH fail h rh ot) fun _ => by kt

theorem kd_monoTryLoopH (fail : Nat) : ∀ (ned : Need) (r o : Nat), KD (monoTryLoop fail ned r o : CM Map Nat)
  | Need.none, _, _ => by unfold monoTryLoop; kd
  | Need.this _, _, _ => by unfold monoTryLoop; kd
  | Need.pair h t, r, o => by
    unfold monoTryLoop
    exact KD.bind' KD.re' fun rt => KD.bind' KD.re' fun rh => KD.bind' (kd_monoTryLoopH fail t rt o) fun ot =>
      KD.bind' (kd_monoTryLoopH fail h rh ot) fun _ => by kd
  | Need.both _ h t, r, o => by
    unfold monoTryLoop
    exact KD.bind' KD.re' fun rt => KD.bind' KD.re' fun rh => KD.bind' (kd_monoTryLoopH fail t rt o) fun ot =>
      KD.bind' (kd_monoTryLoopH fail h rh ot) fun _ => by kd

/-! ## `+into` of a register need -/

/-- **`+into-need`'s loop on a need asking one register** gives the donor a
need asking one register. -/
theorem intoLoop_this (o : Nat) : ∀ (axe : Nat) (k : Nat) (tack : List (Bool × Need)) (ops : List Pole)
    (g g' : Gen Map) (nd nr : Need), intoLoop o axe (Need.this k) tack ops g = some ((nd, nr), g') →
    ∃ k', nd = Need.this k' := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro k tack ops g g' nd nr h
  unfold intoLoop at h
  split at h
  · obtain ⟨u, g1, h1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨k, rfl⟩
  · rename_i ha
    simp only at h
    obtain ⟨l, g1, h1, h⟩ := bind_some h
    obtain ⟨r', g2, h2, h⟩ := bind_some h
    exact ih (mas axe) (mas_lt axe (by omega)) _ _ _ _ _ _ _ h

/-- **`+into` of a `RegLike` need** at an axis of at least `2`: the donor's
lock is empty and its need asks one register. -/
theorem into_regLike_sound {sur : Sure S} {th : Jmp} {a : Nat} (ha : 2 ≤ a) {g g' : Gen Map} {d r : Sure S}
    {o : Nat} (hR : RegLike sur) (h : into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g')) :
    HoonSet.small d.lok = true ∧ needToOrd d.ned = NeedOrd.this := by
  obtain ⟨k, hk, hl⟩ := hR
  simp only [into] at h
  obtain ⟨o', g0, h0, h⟩ := bind_some h
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, hl', h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [intoLok, hl, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hl'
  obtain ⟨rfl, rfl⟩ := hl'
  refine ⟨small_empty, ?_⟩
  rw [hk] at h3
  simp only [intoNeed, show a ≠ 0 by omega, show a ≠ 1 by omega, ↓reduceIte] at h3
  obtain ⟨k', rfl⟩ := intoLoop_this o' a k [] [] g0 g2 nd nr h3
  rfl

/-! ## The constructors -/

section Shape
variable {snd : Nomm → NeedOrd → Bool}

/-- `[0 a]`, `2 ≤ a`, under `%next L th` with no entry: the state as it is,
no entry. -/
theorem runLCH_n0_ax {env : CallEnv} {sup : Option Nomm} {ax : Nat} (h2 : 2 ≤ ax) {L : Lazy S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hE : entries L = [])
    (h : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n0 ax) (CGoalL.next L th) region g0 = some (nex, g1)) :
    g1 = g0 ∧ entries nex.laz = [] := by
  have a0 : ax ≠ 0 := by omega
  have a1 : ax ≠ 1 := by omega
  simp only [runLCH, a0, a1, ↓reduceIte, simpleNextL, bind_apply, pure_apply, Option.bind_some] at h
  cases hl : fromL ax L with
  | none => simp [hl] at h
  | some laz =>
    simp only [hl, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, List.eq_nil_iff_forall_not_mem.mpr fun e hm => ?_⟩
    obtain ⟨l, _, he'⟩ := (fromL_ent ax _ _ hl).mem_right hm
    rw [hE] at he'; cases he'

/-- **`[0 a]`, `2 ≤ a`, has no entry and keeps the state.** -/
theorem shapeH_n0 {env : CallEnv} (Ap : Sure S → Prop) {ax : Nat} (h2 : 2 ≤ ax) :
    ShapeH (S := S) (Map := Map) snd env Ap (Nomm.n0 ax) 0 := by
  intro sup sur th region g0 g1 nex hA d0 hta hr
  obtain ⟨rfl, hE⟩ := runLCH_n0_ax h2 (entries_ofSure _) hr
  refine ⟨TagCS.refl _ _, fun e he => ?_, ?_⟩
  · rw [hE] at he; cases he
  · rw [hE]; simp

/-- **A kept dynamic hint with a constant clue over `q`**, `+sound` of the
goal's need: one entry more than `q` (the bond of `+lazy-bound`, tagged
with the region). -/
theorem shapeH_n11dKept {env : CallEnv} {Ap : Sure S → Prop} {q : Nomm} {k : Nat} {tag : Nat}
    (hs : hintDynamic tag = true) (k1 body : Noun) (Hq : ShapeH (S := S) (Map := Map) snd env Ap q k)
    (hA : ∀ sur : Sure S, Ap sur → HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true) :
    ShapeH (S := S) (Map := Map) snd env Ap (Nomm.n11d tag (Nomm.n1 k1) q body) (k + 1) := by
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
  simp only [runLCH] at h6
  obtain ⟨o, gm, hm, h6⟩ := bind_some h6
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  have SM := medeL_tagCS (R := region) hm (noEntries_ofSure _)
  have dm := SM.drop.trans (SP.drop.trans (SB.drop.trans dc))
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = (gc.bo, nq.laz) :: entries nq.laz :=
    entries_bound1 _ _ _
  obtain ⟨SC, EC⟩ := copyL_tagC h7 (noEntries_ofSure _) (fun e he => by
    rw [hent, List.mem_cons] at he
    rcases he with rfl | he
    · exact (TB.cs SP).cs SM
    · exact (((Eq e he).cs SB).cs SP).cs SM)
  obtain ⟨rfl, -⟩ := copyL_bond1 dm rfl rfl h7
  refine ⟨S0.trans (Sq.trans (SB.trans (SP.trans (SM.trans SC)))), EC, ?_⟩
  rw [entries_bound1, List.length_cons]
  omega

/-- **`[4 p]` at `lazy-from-reg`** has `p`'s entries (`+collapse` of
`lazy-from-reg` keeps the state). -/
theorem shapeH_four {env : CallEnv} {p : Nomm} {k : Nat} (Hp : ShapeH (S := S) (Map := Map) snd env IsReg p k) :
    ShapeH (S := S) (Map := Map) snd env IsReg (Nomm.n4 p) k := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  obtain ⟨rg, rfl⟩ := hAp
  rw [runLCH_n4_next] at hr
  simp only [bind_apply, collapseL_lazyReg hta g0 d0, Option.bind_some, collPick, pure_apply, re_apply,
    emit_apply] at hr
  rw [jmp0_there hta] at hr
  have S0 : TagCS region g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [Pole.inc g0.re rg], Termin.hop th⟩) :=
    TagCS.of_eqs rfl rfl rfl
  obtain ⟨S1, E1, L1⟩ := Hp ⟨g0.re, rfl⟩ (by simpa [emitted_drop] using d0) rfl hr
  exact ⟨S0.trans S1, E1, L1⟩

/-- **The direct call with `p = [0 1]` under `%next (lazy-from-reg rg)`**:
`TagCS` of the region (no proxy: the goal has no entry), no entry, a
`RegLike` need, a jump without arguments. -/
theorem call_tagCS {env : CallEnv} {sup : Option Nomm} {q : Nomm} {b : Bell} {bNed : NeedOrd}
    (hring : env.ring b = Option.none) (hned : env.need b = some bNed) (hq : safeFolFol q = true)
    (hpure : env.pure b = false) {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S}
    (h : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n2 (Nomm.n0 1) q (some (b, Option.none)))
      (CGoalL.next (ofSure (lazyReg rg)) th) region g0 = some (nx, g1)) :
    TagCS region g0 g1 ∧ entries nx.laz = [] ∧ RegLike nx.laz.sure ∧ nx.th.args = [] := by
  have hp' : (env.pure b && noneEquivalentL (ofSure (lazyReg rg) : Lazy S)) = false := by rw [hpure]; rfl
  obtain ⟨E, R⟩ := directZ_shape hring hned hq hpure h
  obtain ⟨sub, gA, out, pro, g2, o', gT, nexS, g5, ha, hk, hm, hp, hc⟩ := runLCH_cal hring hned hq hp' h
  obtain ⟨rfl, rfl⟩ := runLCH_n0_one hp
  have SA : TagCS region g0 gA :=
    TagCS.of_k (kt_needOrdAllocRegsH _) (kc_needOrdAllocRegs _) (kd_needOrdAllocRegsH _) ha
  have SK := kerf_tagCS (R := region) hk (noEntries_ofSure _)
  have SG : TagCS region g2 (callBlocksGen g2 b sub pro out) := TagCS.of_eqs rfl rfl rfl
  have SM :=
    TagCS.of_k (R := region) (kt_monoTryLoopH _ _ _ _) (kc_monoTryLoopH _ _ _ _) (kd_monoTryLoopH _ _ _ _) hm
  obtain ⟨SC, -⟩ := copyL_tagC hc (noEntries_ofSure _) (noEntries_ofSure _)
  refine ⟨SA.trans (SK.trans (SG.trans (SM.trans SC))), E, R, ?_⟩
  rw [copyL_th hc]; rfl

/-- **`S4 = [spot [0 13]]` under `%next (ofSure d) th`**: one entry, its
label the block after the epilogue (`g0.bo + 1`). -/
theorem spotS4_bond {env : CallEnv} (k4 : Noun) {sup : Option Nomm} {d : Sure S} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S}
    (hA : HoonSet.small d.lok = true ∧ snd (Nomm.n0 13) (needToOrd d.ned) = true) (d0 : g0.drop = false)
    (hr : runLCH (S := S) (Map := Map) env snd true sup (spotS4 k4) (CGoalL.next (ofSure d) th) region g0 =
      some (nex, g1)) :
    ∀ e ∈ nex.laz.bond, e.1 = g0.bo + 1 := by
  obtain ⟨nq, gc, nh, gh, h3, hqa, h6, h7⟩ := runLCH_n11d_kept_sur spot_dynamic hA hr
  obtain ⟨rfl, -⟩ := runLCH_n0_ax (by decide) (entries_ofSure _) h3
  have dc : (genN g0 tagSpot (C (A 0) (A 13)) th).drop = false := d0
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

/-- **`S3`'s `%10`, `[10 6 S4 [0 1]]`, at a `RegLike` need**: `+into`,
`+lazy-bound` of the recipient (tagged), `S4` (one entry), `+copy`: two
entries. -/
theorem shapeH_ten {env : CallEnv} (k4 : Noun) (h13 : snd (Nomm.n0 13) NeedOrd.this = true) :
    ShapeH (S := S) (Map := Map) snd env RegLike (spotS3Ten k4) 2 := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  have hv : hinted env.cod (spotS4 k4) = some true := rfl
  obtain ⟨d, r, o, g2, nb, g3, nexDon, g4, hi, hcase, hvr, hcp⟩ := runLCH_n10_kept hv hr
  rcases hcase with ⟨h1, h2, -, -⟩ | ⟨-, hlb⟩
  · exact absurd ⟨h1, h2⟩ (into_rec_asks hi (by decide))
  rw [lazyBound_apply rfl] at hlb
  simp only [Option.some.injEq, Prod.mk.injEq] at hlb
  obtain ⟨rfl, rfl⟩ := hlb
  have SI : TagCS region g0 g2 := TagCS.of_k (kt_into _ _) (kc_into _ _) (kd_into _ _) hi
  have d2 : g2.drop = false := SI.drop.trans d0
  obtain ⟨SB, TB⟩ := lazyBound_tagCS (jmp0 o) region d2
  have d3 : ((g2.emitted ⟨[], [], Termin.hop (jmp0 o)⟩).tagged g2.bo region).drop = false := SB.drop.trans d2
  obtain ⟨hsm, hord⟩ := into_regLike_sound (a := 6) (by decide) hAp hi
  have hA4 : HoonSet.small d.lok = true ∧ snd (Nomm.n0 13) (needToOrd d.ned) = true := ⟨hsm, by rw [hord]; exact h13⟩
  have H0 : ShapeH (S := S) (Map := Map) snd env
      (fun d : Sure S => HoonSet.small d.lok = true ∧ snd (Nomm.n0 13) (needToOrd d.ned) = true) (Nomm.n0 13) 0 :=
    fun hA d0 hta hr => shapeH_n0 (ax := 13)
      (fun d : Sure S => HoonSet.small d.lok = true ∧ snd (Nomm.n0 13) (needToOrd d.ned) = true) (by decide)
      hA d0 hta hr
  obtain ⟨S4, E4, L4⟩ := shapeH_n11dKept (S := S) (Map := Map) (snd := snd) (env := env)
    (Ap := fun d : Sure S => HoonSet.small d.lok = true ∧ snd (Nomm.n0 13) (needToOrd d.ned) = true)
    spot_dynamic k4 (C (A 0) (A 13)) @H0 (fun _ h => h) hA4 d3 rfl hvr
  have B4 := spotS4_bond k4 hA4 d3 hvr
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

/-- **`S3`'s `%7`, the `%10` then the direct call, at `lazy-from-reg`**: the
call's result has no entry and a `RegLike` need, so the `%10` runs at it. -/
theorem shapeH_s3body {env : CallEnv} (k4 F : Noun) {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none)
    (hned : env.need b = some bNed) (hpure : env.pure b = false) (h13 : snd (Nomm.n0 13) NeedOrd.this = true) :
    ShapeH (S := S) (Map := Map) snd env IsReg (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) 2 := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  obtain ⟨rg, rfl⟩ := hAp
  rw [runLCH_n7] at hr
  obtain ⟨nx, g, h1, h2⟩ := bind_some hr
  obtain ⟨SC, E, R, ha⟩ := call_tagCS hring hned rfl hpure h1
  simp only [NextL.goal] at h2
  rw [eq_ofSure_of_entries E] at h2
  obtain ⟨S2, E2, L2⟩ := shapeH_ten k4 h13 R (SC.drop.trans d0) ha h2
  exact ⟨SC.trans S2, E2, L2⟩

/-- `+sound` of `%this` at `lazy-from-reg`. -/
theorem isReg_sound {q : Nomm} (h : snd q NeedOrd.this = true) :
    ∀ sur : Sure S, IsReg sur → HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true := by
  rintro sur ⟨r, rfl⟩
  exact ⟨small_empty, h⟩

/-- **`ShapeH IsReg S2 4`**: `S2 = [spot [4 S3]]`,
`S3 = [spot [7 [10 6 S4 [0 1]] [2 [0 1] [1 F] b]]]`, `S4 = [spot [0 13]]`:
the bonds of `S2`, `S3`, the parked recipient of the `%10` and `S4`. -/
theorem shapeH_spotS2 (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (k2 k3 k4 F B2 B3 : Noun) {b : Bell}
    {bNed : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed) (hpure : env.pure b = false)
    (hsnd : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) NeedOrd.this = true)
    (h4 : snd (Nomm.n4 (spotS3 k3 k4 F b B3)) NeedOrd.this = true)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true) :
    ShapeH (S := S) (Map := Map) snd env IsReg (spotS2 k2 k3 k4 F b B2 B3) 4 :=
  shapeH_n11dKept spot_dynamic k2 B2
    (shapeH_four (shapeH_n11dKept spot_dynamic k3 B3 (shapeH_s3body k4 F hring hned hpure h13) (isReg_sound hsnd)))
    (isReg_sound h4)

end Shape

/-! ## `spotArm`'s `%6` and `S1` with `ShapeH` -/

/-- **`sixNH_of` with `ShapeH`** (the states of `SixNH` have `drop` `|` and
a jump without arguments). -/
theorem sixNH_of_shape {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {Ap : Sure S → Prop} {f : Noun} {nm : Nomm} {k : Nat} (H : SurGBT (S := S) (Map := Map) snd lib N env P Ap f nm)
    (K : ShapeH (S := S) (Map := Map) snd env Ap nm k) :
    SixNH (S := S) (Map := Map) snd lib N env P Ap f nm k :=
  fun _ b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hA hr =>
    ⟨H hA b0 d0 hu hcl hcb h1 h2 hta hsd hcs hsl hr, (K hA d0 hta hr).2.2, (K hA d0 hta hr).1.cond⟩

/-- **`spotArm`'s `%6` in `RegGBT`** from its branch in `RegGBT` with
`ShapeH` (the text of `regGBT_spotSix`). -/
theorem regGBT_spotSixW (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    {fs2 : Noun} {s2 : Nomm} (H2 : RegGBT (S := S) (Map := Map) snd lib N env P fs2 s2)
    (K2 : ShapeH (S := S) (Map := Map) snd env IsReg s2 4) (h6 : sixCount (spotSix s2) ≤ 255) :
    RegGBT (S := S) (Map := Map) snd lib N env P (spotSixF fs2) (spotSix s2) :=
  regGBT_six lib (pickD_spotTest lib env P) rfl rfl rfl
    (sixNH_of_sixN rfl rfl (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 0)).annot P) hs gul tm r) rfl))
    (sixNH_of_shape (RegGBT.toSur H2) K2) (by decide) h6

/-- **`spotArm` at the top (position 1)** from its branch in `RegGBT` with
`ShapeH` (the text of `contract_spotS1`). -/
theorem contract_spotS1W (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (k1 B1 : Noun)
    {fs2 : Noun} {s2 : Nomm} (H2 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) fs2 s2)
    (K2 : ShapeH (S := S) (Map := Map) snd env IsReg s2 4)
    (h6 : sixCount (spotSix s2) ≤ 255) (hsnd : snd (spotSix s2) NeedOrd.this = true) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd (Nomm.n11d tagSpot (Nomm.n1 k1) (spotSix s2) B1) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF fs2)) [s] c ∧
      ContractBwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF fs2)) [s] c := by
  have H := finishLUCH_contractN11dKeptR (S := S) (Map := Map) (snd := snd) lib (N := N) (P := fun _ => True)
    (regGBT_spotSixW lib env snd N _ H2 K2 h6) hsnd (clueLOKS_n1 lib env _ k1) (by simp [sixCount])
    (noBondH_n1 k1) spot_dynamic spot_stop B1 hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **`spotArm` at the top with its own `S2`**: only `S2`'s `RegGBT` is left
as a premise (`shapeH_spotS2` discharges the shape). -/
theorem contract_spotS1S2 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs)
    (k1 k2 k3 k4 F B1 B2 B3 : Noun) {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none)
    (hned : env.need b = some bNed) (hpure : env.pure b = false)
    (hsnd7 : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) NeedOrd.this = true)
    (h4 : snd (Nomm.n4 (spotS3 k3 k4 F b B3)) NeedOrd.this = true)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true)
    (H2 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS2F k2 k3 k4 F)
      (spotS2 k2 k3 k4 F b B2 B3))
    (h6 : sixCount (spotSix (spotS2 k2 k3 k4 F b B2 B3)) ≤ 255)
    (hsnd : snd (spotSix (spotS2 k2 k3 k4 F b B2 B3)) NeedOrd.this = true) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd
      (Nomm.n11d tagSpot (Nomm.n1 k1) (spotSix (spotS2 k2 k3 k4 F b B2 B3)) B1) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 F))) [s] c ∧
      ContractBwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 F))) [s] c :=
  contract_spotS1W lib env snd N k1 B1 H2
    (shapeH_spotS2 (S := S) (Map := Map) env snd k2 k3 k4 F B2 B3 hring hned hpure hsnd7 h4 h13) h6 hsnd hc

end Comp
end SkaModel
end Formalization
