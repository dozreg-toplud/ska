import lemmas.Ska.CompHintTen

/-!
# `[10 [a v] [0 1]]` with a kept value in `SurGBT` (README Gaps 24.20)

The `%10` of `spotArm`'s `S3` and of `d20`: under `%next (ofSure sur) th`,
`+into` at `a` (the block `o` of `%con`s to `th`, the donor `d`, the
recipient `r`), `+lazy-bound` parks `⟨ofSure r, jmp0 o⟩` behind a block
`o'` (the axis is in `r`'s lock, so `r` asks something), `v` runs under
`%next (ofSure d) (jmp0 o')`, and `+copy` puts `v`'s result after the
parked recipient.  At run time: the copy block, `v`'s code (its product
`x` in `d`'s registers), the bond block `o'` (fills `r` for the subject,
keeping `d`'s registers), the `%con`s of `o` (the goal's registers hold
`edit a x s`), `th`.

* `into_lok_rec`: `+into` puts the axis in the recipient's lock.
* `tenTone`, `minkF_ten`, `minkF_ten_cases`, `mink_ten_bwd`: `+mink` of
  `[10 [a fv] [0 1]]` from `+mink` of `fv`.
* `copyL_bondFront`, `entries_bondFront`: `+copy` of the parked recipient
  with `v`'s result: the bonds side by side.
* **`surGBT_tenKept`**: the `%10` with a hinted value in `SurGBT Ap`, the
  value in `SurGBT Ad` where `Ad` holds of every donor need `+into` makes
  from a need of `Ap`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+into` puts the axis in the recipient's lock.** -/
theorem into_lok_rec {sur : Sure S} {th : Jmp} {a : Nat} {g g' : Gen Map} {d r : Sure S} {o : Nat}
    (h : into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g')) (ha : 2 ≤ a) : a ∈ HoonSet.toList r.lok := by
  simp only [into] at h
  obtain ⟨o', g0, h0, h⟩ := bind_some h
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [if_neg (show a ≠ 1 by omega)]
  exact (HoonSet.mem_put _ _ _).mpr (Or.inl rfl)

/-- The recipient of `+into` at an axis of at least `2` asks something. -/
theorem into_rec_asks {sur : Sure S} {th : Jmp} {a : Nat} {g g' : Gen Map} {d r : Sure S} {o : Nat}
    (h : into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g')) (ha : 2 ≤ a) :
    ¬ (r.ned = Need.none ∧ HoonSet.small r.lok = true) := fun ⟨_, hs⟩ => by
  have := (HoonSet.small_iff _).mp hs a (into_lok_rec h ha); omega

/-! ## `+mink` of `[10 [a fv] [0 1]]` -/

/-- The tone of `[10 [a fv] [0 1]]` from the tone of `fv`. -/
def tenTone (a : Nat) (tm : Trace) (s : Noun) : Tone → Tone
  | Tone.zero x => match edit? a x s with
    | Option.none => Tone.two tm
    | some n => Tone.zero n
  | r => r

theorem minkF_ten (lib : Lib) (gul : Noun) (m : Nat) (tm : Trace) (s fv : Noun) {a : Nat} (ha : a ≠ 0) :
    minkF lib gul (m + 2) tm s (n3 (A 10) (C (A a) fv) (slot 1)) =
      (minkF lib gul (m + 1) tm s fv).map (tenTone a tm s) := by
  rw [minkF_succ_eq]
  have e1 : minkF lib gul (m + 1) tm s (slot 1) = some (Tone.zero s) := by
    rw [minkF_succ_eq]
    show minkStep lib gul (minkF lib gul m) tm s (Noun.cell (Noun.atom 0) (Noun.atom 1)) = _
    simp only [minkStep, slot?_one]
  show minkStep lib gul (minkF lib gul (m + 1)) tm s
    (Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a) fv) (slot 1))) = _
  simp only [minkStep, if_neg ha, e1, tbind]
  cases minkF lib gul (m + 1) tm s fv with
  | none => rfl
  | some rv =>
    cases rv with
    | zero x =>
      simp only [Option.map_some, tenTone]
      cases edit? a x s <;> rfl
    | one _ => rfl
    | two _ => rfl

theorem minkF_ten_cases {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s fv : Noun} {a : Nat} (ha : a ≠ 0)
    {rr : Tone} (h : minkF lib gul n tm s (n3 (A 10) (C (A a) fv) (slot 1)) = some rr) :
    ∃ m rv, n = m + 2 ∧ minkF lib gul (m + 1) tm s fv = some rv ∧ rr = tenTone a tm s rv := by
  match n, h with
  | 0, h => simp [minkF] at h
  | 1, h =>
    rw [minkF_succ_eq] at h
    change minkStep lib gul (minkF lib gul 0) tm s
      (Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a) fv) (slot 1))) = _ at h
    simp only [minkStep, if_neg ha, minkF, tbind] at h
    cases h
  | m + 2, h =>
    rw [minkF_ten lib gul m tm s fv ha] at h
    obtain ⟨rv, e, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨m, rv, rfl, e, rfl⟩

theorem mink_ten_bwd {lib : Lib} {gul : Noun} {tm : Trace} {s fv : Noun} {a : Nat} (ha : a ≠ 0) {rv : Tone}
    (h : Mink lib gul tm s fv rv) : Mink lib gul tm s (n3 (A 10) (C (A a) fv) (slot 1)) (tenTone a tm s rv) := by
  obtain ⟨n, e⟩ := h
  match n, e with
  | 0, e => simp [minkF] at e
  | m + 1, e => exact ⟨m + 2, by rw [minkF_ten lib gul m tm s fv ha, e]; rfl⟩

/-- A failure of `fv` for the donor is a failure of the `%10` for the goal. -/
theorem badC_ten {a : Nat} {tm : Trace} {s : Noun} {sur d r : Sure S} {j th : Jmp}
    (F : ∀ x t n, edit? a x t = some n → (FitsS sur n ↔ FitsS d x ∧ FitsS r t)) {rv : Tone}
    (h : BadC (CGoal.next d j) tm rv) : BadC (CGoal.next sur th) tm (tenTone a tm s rv) := by
  rcases h with rfl | ⟨x, rfl, hx⟩
  · exact Or.inl rfl
  · simp only [tenTone]
    cases e : edit? a x s with
    | none => exact Or.inl rfl
    | some n => exact Or.inr ⟨n, rfl, fun hf => hx ((F x s n e).mp hf).1⟩

/-! ## `+copy` of the parked recipient with the value's result -/

/-- **`+copy` of a bond in front of a result whose bond labels are apart**:
one hop block to the first's jump; the sure need is the second's (its lock
after the empty one), the forks the second's, the bonds the first's then the
second's. -/
theorem copyL_bondFront {th : Jmp} {o' : Nat} {R second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (hd : g.drop = false) (hb : ∀ e ∈ second.bond, o' ≠ e.1)
    (h : copyL ⟨mk Sure.bunt [] [(o', R)], th⟩ second g = some (nex, g')) :
    nex = ⟨mk ⟨second.sure.ned, HoonSet.uni HoonSet.empty second.sure.lok⟩ second.fork ((o', R) :: second.bond),
      jmp0 g.bo⟩ ∧
      g'.re = g.re ∧ g'.bo = g.bo + 1 ∧ g'.drop = false ∧ g'.cond = g.cond ∧
      ∀ k, HoonMap.get g'.blocks k = HoonMap.get (g.emitted ⟨[], [], Termin.hop th⟩).blocks k := by
  unfold copyL at h
  obtain ⟨oc, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨laz, gf, hc, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [copyLazyL_apart g.bo Sure.bunt [] [(o', R)] second (fun e he => by cases he)
    (fun e he e' he' => by rw [List.mem_singleton] at he; subst he; exact hb e' he')] at hc
  simp only [Sure.bunt, copyNeed, bind_apply, pure_apply, Option.bind_some] at hc
  obtain ⟨⟨u, gu⟩, hu, hc⟩ := Option.bind_eq_some_iff.mp hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨bk, hbk, rfl⟩ := addOps_spec hu (by simp only [emitted_drop, hd])
  refine ⟨rfl, rfl, rfl, hd, rfl, fun k => ?_⟩
  simp only [HoonMap.get_put, List.nil_append]
  split
  · rename_i e; subst e; rw [hbk]
  · rfl

theorem entries_bondFront (s : Sure S) (o : Nat) (R second : Lazy S) (hR : entries R = []) :
    entries (mk s second.fork ((o, R) :: second.bond)) = (o, R) :: entries second := by
  cases second
  simp [entries, bondEntries, hR]

/-! ## The `%10` in `SurGBT` -/

section Ten
variable {snd : Nomm → NeedOrd → Bool}

/-- **`[10 [a v] [0 1]]` with a hinted value is in `SurGBT Ap`** when the
value is in `SurGBT Ad` and every donor need `+into` makes at `a` from a
need of `Ap` has `Ad` (`2 ≤ a`, so the recipient is parked by `+lazy-bound`
behind the block `o'`). -/
theorem surGBT_tenKept' {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fv : Noun} {a : Nat} {v : Nomm}
    {Ap Ad : Sure S → Prop} (ha : 2 ≤ a) (hv : hinted env.cod v = some true)
    (Hv : SurGBT (S := S) (Map := Map) snd lib N env P Ad fv v)
    (hAd : ∀ {sur : Sure S} {th : Jmp} {g g' : Gen Map} {d r : Sure S} {o : Nat}, Ap sur →
      into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g') → Ad d) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap (n3 (A 10) (C (A a) fv) (slot 1)) (Nomm.n10 a v (Nomm.n0 1)) := by
  intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr
  obtain ⟨d, r, o, g2, nb, g3, nexDon, g4, hi, hcase, hvr, hcp⟩ := runLCH_n10_kept (snd := snd) hv hr
  have hAdd : Ad d := hAd hA hi
  have ID := into_down hi th1 th2 d0
  obtain ⟨a1, eo, E2, b2, Md, Mr, Fe, SP⟩ := into_okK hi
  subst eo
  obtain ⟨Dd, Dr, Ddr, F, B⟩ := SP hsd (fun y hy => (hsl y hy).1)
  have CI := clean_into hi hcs
  have c2 : g2.cond = g0.cond := (kc_into _ _).keep _ _ _ hi
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have GU2 : GrowU g0 g2 := ID.1.toU hu
  have u2 : UpBelow g2 := GU2.up hu
  have cl2 : Clear g2 := hcl.growU GU2
  have cb2 : CondBelow g2 := (condFresh_of_eq E2.1 c2).below hcb
  have re02 := E2.1
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g2.bo → (HoonMap.get g2.blocks k).map (unproxyBlob cf) = HoonMap.get g2.blocks k :=
    fix_of_keeps (gs := g0) rfl
      (keepsA_into (P := (fun r => HoonMap.get g0.cond r = Option.none)) (nex := ⟨sur, th⟩) d0
        ⟨fun r hr => (hsl r hr).2, jmpIn_nil hta⟩ (fun r hr => condBelow_none hcb hr) hi).1
      (keeps_into (nex := ⟨sur, th⟩) d0 ⟨fun r hr => (hsl r hr).1, jmpIn_nil hta⟩ hi).1
  have dreg : ∀ x, NMem d.ned x → x < g2.re ∧ HoonMap.get g0.cond x = Option.none := fun x hx => by
    rcases Md x hx with e | ⟨e1, e2⟩
    · exact ⟨Nat.lt_of_lt_of_le (hsl x e).1 E2.1, (hsl x e).2⟩
    · exact ⟨e2, condBelow_none hcb e1⟩
  have rreg : ∀ x, NMem r.ned x → x < g2.re ∧ HoonMap.get g0.cond x = Option.none := fun x hx => by
    rcases Mr x hx with e | ⟨e1, e2⟩
    · exact ⟨Nat.lt_of_lt_of_le (hsl x e).1 E2.1, (hsl x e).2⟩
    · exact ⟨e2, condBelow_none hcb e1⟩
  -- the recipient is parked behind `o' = g2.bo`
  rcases hcase with ⟨h1, h2, -, -⟩ | ⟨-, hlb⟩
  · exact absurd ⟨h1, h2⟩ (into_rec_asks hi ha)
  rw [lazyBound_apply rfl] at hlb
  simp only [Option.some.injEq, Prod.mk.injEq] at hlb
  obtain ⟨rfl, rfl⟩ := hlb
  dsimp only at hvr hcp
  have hb3 : ∀ k, HoonMap.get ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region).blocks k =
      if k = g2.bo then some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ else HoonMap.get g2.blocks k := fun k => by
    simp only [tagged_blocks, Gen.emitted, d2, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G23 : GrowU g2 ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) :=
    (growU_emit (b := ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; exact ⟨b0, by omega⟩) u2).trans
      (growU_tagged _ _ _)
  have re3 : ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region).re = g2.re := by
    simp [Gen.emitted]
  have bo3 : ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region).bo = g2.bo + 1 := by
    simp [Gen.emitted]
  have cd3 : ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region).cond = g2.cond := by
    rw [tagged_cond]; rfl
  have E23 : Ext g2 ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) :=
    (ext_emit _ _).trans (ext_tagged _ _ _)
  generalize eg3 : (g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region = g3 at hb3 G23 re3 bo3 cd3 E23 hvr hcp
  have u3 : UpBelow g3 := G23.up u2
  have cl3 : Clear g3 := cl2.growU G23
  have CF23 : CondFresh g2 g3 := condFresh_of_eq (Nat.le_of_eq re3.symm) cd3
  have cb3 : CondBelow g3 := CF23.below cb2
  have d3 : g3.drop = false := E23.2.2.1.trans d2
  -- the value
  have RV := Hv (sup := sup) (sur := d) (th := jmp0 g2.bo) (region := region) hAdd (by rw [bo3]; omega) d3 u3 cl3 cb3
    (by simp only [jmp0]; omega) (by simp only [jmp0]; rw [bo3]; omega) rfl Dd CI.1
    (fun x hx => ⟨by rw [re3]; exact (dreg x hx).1, by rw [cd3, c2]; exact (dreg x hx).2⟩) hvr
  have d4 : g4.drop = false := RV.ext.2.2.1.trans d3
  have re34 := RV.ext.1
  have bo34 := RV.ext.2.1
  have lab4 : ∀ e ∈ entries nexDon.laz, g3.bo ≤ e.1 ∧ e.1 < g4.bo := fun e he => ⟨(RV.labs e he).1, (RV.labs e he).2.1⟩
  have hargs : nexDon.th.args = [] := nextArgs_nil RV.ent rfl
  -- the copy
  obtain ⟨enx, r1, b1, dd1, c1, k1⟩ := copyL_bondFront d4
    (fun e he => by have := (lab4 e (bond_in_entries he)).1; rw [bo3] at this; omega) hcp
  have hent0 := entries_bondFront ⟨nexDon.laz.sure.ned, HoonSet.uni HoonSet.empty nexDon.laz.sure.lok⟩ g2.bo
    (ofSure r) nexDon.laz (entries_ofSure r)
  generalize hL : (mk ⟨nexDon.laz.sure.ned, HoonSet.uni HoonSet.empty nexDon.laz.sure.lok⟩ nexDon.laz.fork
    ((g2.bo, ofSure r) :: nexDon.laz.bond) : Lazy S) = LZ at enx hent0
  subst enx
  have hent : entries LZ = (g2.bo, ofSure r) :: entries nexDon.laz := hent0
  have hsure : LZ.sure = ⟨nexDon.laz.sure.ned, HoonSet.uni HoonSet.empty nexDon.laz.sure.lok⟩ := by
    rw [← hL]; rfl
  have hb1 : ∀ k, HoonMap.get g1.blocks k =
      if k = g4.bo then some ⟨[], [], Termin.hop nexDon.th⟩ else HoonMap.get g4.blocks k := by
    intro k; rw [k1 k]; simp [Gen.emitted, d4, HoonMap.get_put]
  have E41 : Ext g4 g1 := ⟨by omega, by omega, by rw [dd1, d4], fun o ho => by rw [hb1, if_neg (by omega)]⟩
  have GG : Grow g4 g1 := Grow.congr_right (grow_emit (g := g4) (b := ⟨[], [], Termin.hop nexDon.th⟩) (fun j hj => by
    simp [finJumps] at hj; subst hj; exact ⟨RV.lo, RV.hi⟩)) b1 (by rw [dd1, emitted_drop, d4]) k1
  have E31 : Ext g3 g1 := RV.ext.trans E41
  have E21 : Ext g2 g1 := E23.trans E31
  have CF41 : CondFresh g4 g1 := condFresh_of_eq (by omega) c1
  have CF21 : CondFresh g2 g1 := CF23.trans (RV.cfr.trans CF41)
  have hnot : ∀ k, k ≠ g2.bo → (k < g3.bo ∨ g4.bo ≤ k) → k ∉ (entries LZ).map Prod.fst := fun k hk hlt hm => by
    rw [hent, List.map_cons, List.mem_cons] at hm
    rcases hm with hm | hm
    · exact hk hm
    · obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := lab4 e he; omega
  have hout : ∀ k, g3.bo ≤ k → k < g4.bo → k ∈ (entries LZ).map Prod.fst → k ∈ (entries nexDon.laz).map Prod.fst :=
    fun k h0 h1 hm => by
      rw [hent, List.map_cons, List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only at hm; rw [bo3] at h0; omega
      · exact hm
  have hmem : ∀ e ∈ entries nexDon.laz, e ∈ entries LZ := fun e he => by rw [hent]; exact List.mem_cons_of_mem _ he
  have agD : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1 LZ s0 s → AgreeUB lib O c gul st t cf ned g3 g4 nexDon.laz s0 s :=
    fun ag => ag.part (by rw [bo3]; omega) E41 hmem hout (fun e he => (lab4 e he).2)
  have hcf4 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ k, k < g4.re → HoonMap.get cf k = HoonMap.get g4.cond k := fun cf hcf k hk => by
    rw [hcf k (by omega), c1]
  -- the blocks in the program
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g0 g1 LZ s0 s →
      HoonMap.get c.blocks g4.bo = some ⟨[], [], Termin.hop nexDon.th⟩ ∧ Agree c g0 g2 ∧
      ∃ A, HoonMap.get c.blocks g2.bo = some ⟨[], A ++ [], Termin.hop (jmp0 g0.bo)⟩ ∧
        FillSem lib O c gul st t ned g1.re r A s0 s := by
    intro cf hcf c ned σ O gul st t s0 s ag
    have hcf0 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk => by
      rw [hcf k (by omega), CF21.get_lt hk, c2]
    refine ⟨?_, fun k h0 h1 => ?_, ?_⟩
    · rw [ag.1 g4.bo (by omega) (by omega) (hnot _ (by omega) (Or.inr (Nat.le_refl _))), hb1, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp_nil _ hargs]
    · rw [ag.1 k h0 (by omega) (hnot k (by omega) (Or.inl (by omega))), E21.2.2.2 k h1]
      exact hfix cf hcf0 k h0 h1
    · obtain ⟨A, Bb, th', h1, h2, h3⟩ := ag.2 (g2.bo, ofSure r) (by rw [hent]; exact List.mem_cons_self)
      rw [E31.2.2.2 _ (by rw [bo3]; omega), hb3, if_pos rfl] at h1
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simp only [List.map_nil] at h2
      rw [renJmp_nil _ rfl] at h2
      exact ⟨A, h2, h3⟩
  -- what the code after `v` does, for each tone of `v`
  have fin : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
      (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm →
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g1 LZ s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 → ∀ rv,
      GoalSemCM lib O c gul Inv ν (fun x => (x < g3.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next d (jmp0 g2.bo)) x)
        st regs t tm nexDon.th (CGoal.next d (jmp0 g2.bo)) rv →
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th) x)
        st regs t tm (jmp0 g4.bo) (CGoal.next sur th) (tenTone a tm s rv) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs hn rv G
    obtain ⟨hcp, -, -⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st' regs', goJ lib O c gul st' regs' t (jmp0 g4.bo) = goJ lib O c gul st' regs' t nexDon.th :=
      fun st' regs' => by rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop]
    cases rv with
    | one b =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := G
      exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | two tr =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := G
      exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | zero x =>
      by_cases fx : FitsS d x
      · obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := G.1 fx
        obtain ⟨-, AG, A, hbA, FS⟩ := blocks cf hcf c ned O gul st1 t s0 s (ag st1 t)
        have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun y hy => hk1 y ⟨Or.inr hy, fun hg => by
          have := (dreg y hg).1; have := hned y hy; omega⟩)
        by_cases fr : FitsS r s
        · obtain ⟨R2, hr2, hh2, hk2⟩ := (FS regs1 hn1).1 fr
          obtain ⟨n, en⟩ := Option.isSome_iff_exists.mp (Fe x s fr)
          have hd2 : HoldsN d.ned R2 x := holdsN_frame d.ned hh1 (fun y hy =>
            hk2 y (Or.inr (by have := (dreg y hy).1; omega)) (Ddr y hy))
          obtain ⟨R3, hl3, hk3, ej⟩ := B d0 c AG lib σ O st1 t R2 x s n gul en hd2 hh2.1
          have fs : FitsS sur n := (F x s n en).mpr ⟨fx, fr⟩
          simp only [tenTone, en]
          refine ⟨fun _ => ⟨st1, R3, hI1, hle1, hl3, fun y ⟨k1, k2⟩ => ?_, ?_⟩, fun h => absurd fs h⟩
          · have hlt : y < g0.re ∨ g1.re ≤ y := k1.imp id (fun h => hned y h)
            have nr : ¬ NMem r.ned y := fun hm => by
              rcases Mr y hm with e | ⟨e1, e2⟩
              · exact k2 e
              · omega
            have nd : ¬ NMem d.ned y := fun hm => by
              rcases Md y hm with e | ⟨e1, e2⟩
              · exact k2 e
              · omega
            rw [hk3 y (Or.inl ⟨k2, hlt.imp id (fun h => by omega)⟩),
              hk2 y (k1.elim (fun h => Or.inr (by omega)) Or.inl) nr,
              hk1 y ⟨k1.imp (fun h => by omega) id, nd⟩]
          · rw [ecopy, e1, goJ_jmp0 _ _ _ _ hbA, hr2 [] (Termin.hop (jmp0 g0.bo)), execBlob_hop, ej]
        · have hc := (FS regs1 hn1).2 fr [] (Termin.hop (jmp0 g0.bo))
          refine goalSemCM_of_badC ?_ ⟨Tone.two t, st1, hI1, hle1, by rw [ecopy, e1, goJ_jmp0 _ _ _ _ hbA, hc],
            ToneRel.two (frames_mono hle1 htr)⟩
          simp only [tenTone]
          cases en : edit? a x s with
          | none => exact Or.inl rfl
          | some n => exact Or.inr ⟨n, rfl, fun hf => fr ((F x s n en).mp hf).2⟩
      · obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := G.2 fx
        exact goalSemCM_of_badC (badC_ten (j := jmp0 g2.bo) F (Or.inr ⟨x, rfl, fx⟩))
          ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
  refine ⟨E2.trans E21, GU2.trans (G23.trans (RV.grow.trans (GG.toU (RV.grow.up u3)))),
    (condFresh_of_eq E2.1 c2).trans CF21,
    by simp only [jmp0]; rw [bo3] at bo34; omega, by simp only [jmp0]; omega,
    Or.inl ⟨_, by simp only [jmp0]; rw [hb1, if_pos rfl], rfl, rfl⟩,
    fun x hx => ?_, by rw [hsure]; exact RV.dist, fun e he => ?_, fun e he => ?_, ?_, fun s hs hf => ?_,
    fun x hx => by rw [hsure] at hx; rw [c1]; exact RV.ncond x hx, fun e he x hx => ?_, ?_, ?_⟩
  · -- regs
    rw [hsure] at hx
    rcases RV.regs x hx with h | h
    · rcases Md x h with e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr ⟨e1, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    rw [hent] at he
    rcases List.mem_cons.mp he with rfl | he'
    · refine ⟨Dr, fun x hx => ?_⟩
      rcases Mr x hx with e | ⟨e1, e2⟩
      · exact ⟨Or.inl e, by have := (hsl x e).1; omega⟩
      · exact ⟨Or.inr e1, by omega⟩
    · refine ⟨(RV.eregs e he').1, fun x hx => ?_⟩
      obtain ⟨h1, h2⟩ := (RV.eregs e he').2 x hx
      rcases h1 with h | h
      · rcases Md x h with e' | ⟨e1, e2⟩
        · exact ⟨Or.inl e', by omega⟩
        · exact ⟨Or.inr e1, by omega⟩
      · exact ⟨Or.inr (by omega), by omega⟩
  · -- labs
    rw [hent] at he
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨by omega, by omega, [], _, by rw [E31.2.2.2 _ (by rw [bo3]; omega), hb3, if_pos rfl]⟩
    · obtain ⟨x1, x2, Bb, th', z⟩ := RV.labs e he'
      exact ⟨by rw [bo3] at x1; omega, by omega, Bb, th', by rw [E41.2.2.2 _ x2]; exact z⟩
  · -- nodup
    rw [hent, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := (lab4 e he).1; simp only at e1; rw [bo3] at this; omega, RV.nodup⟩
  · -- nec
    rw [hsure] at hf
    have hf' : ¬ FitsS nexDon.laz.sure s := fun h2 => hf ⟨h2.1, (looks_uni _ _ _).mpr ⟨looks_empty _, h2.2⟩⟩
    have NC := RV.nec s hs hf'
    refine ⟨fun gul n tm rr hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨m, rv, rfl, hmv, rfl⟩ := minkF_ten_cases (by omega) hm
      exact badC_ten F (NC.1 gul (m + 1) tm rv hmv)
    · obtain ⟨rv, hmv, hb⟩ := NC.2 gul tm
      exact ⟨_, mink_ten_bwd (by omega) hmv, badC_ten F hb⟩
  · -- econd
    rw [hent] at he
    rcases List.mem_cons.mp he with rfl | he'
    · obtain ⟨l1, l2⟩ := rreg x hx
      rw [CF21.get_lt l1, c2]; exact l2
    · rw [c1]; exact RV.econd e he' x hx
  · -- sem
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s rr hI htr hs hm ag hned regs hh hn
    rw [hsure] at hh
    obtain ⟨m, rv, rfl, hmv, rfl⟩ := minkF_ten_cases (by omega) hm
    have Gv := RV.sem cf (hcf4 cf hcf) c ned σ Inv ν O (m + 1) gul hN hS (oracleFwd_le hF (by omega)) st t tm s0 s rv
      hI htr hs hmv (fun st' t' => agD (ag st' t')) (fun x hx => by have := hned x hx; omega) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).2⟩ hn
    exact fin cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs hn rv Gv
  · -- semB
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    rw [hsure] at hh
    obtain ⟨hcp, -, -⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop] at hres
    obtain ⟨rv, hmv, Gv⟩ := RV.semB cf (hcf4 cf hcf) c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' t' => agD (ag st' t')) (fun x hx => by have := hned x hx; omega) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).2⟩ hn res hres
    exact ⟨_, mink_ten_bwd (by omega) hmv, fin cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs hn rv Gv⟩

/-- **`surGBT_tenKept'` in the form the track brief stated** (the shape
premise `hvf` on the value's result is not needed: `+copy` puts the forks
and bonds side by side whatever they are). -/
theorem surGBT_tenKept {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fv : Noun} {a : Nat} {v : Nomm}
    {Ap Ad : Sure S → Prop} (ha : 2 ≤ a) (hv : hinted env.cod v = some true)
    (Hv : SurGBT (S := S) (Map := Map) snd lib N env P Ad fv v)
    (hAd : ∀ {sur : Sure S} {th : Jmp} {g g' : Gen Map} {d r : Sure S} {o : Nat}, Ap sur →
      into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g') → Ad d)
    (hvf : ∀ {sup : Option Nomm} {d : Sure S} {th : Jmp} {region : List Nat} {g g' : Gen Map} {nex : NextL S},
      Ad d → runLCH (S := S) (Map := Map) env snd true sup v (CGoalL.next (ofSure d) th) region g = some (nex, g') →
      nex.laz.fork = []) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap (n3 (A 10) (C (A a) fv) (slot 1)) (Nomm.n10 a v (Nomm.n0 1)) :=
  surGBT_tenKept' ha hv Hv hAd

end Ten

end Comp
end SkaModel
end Formalization
