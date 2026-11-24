import lemmas.Ska.CompCallC

/-!
# The cons whose parts may both call

README Gaps 12.20.  The cons `[p d]` under a fork-free `%next`, either part
may call (`pairLC_ok` with the `con` block of `+split` as the last step):
`+split`, then `+past` behind the tail `d` (when `d` is hinted and the
head's need asks something, the head's need is parked in a bond and the head
runs under the bond goal, `BondOKC`), the tail (`UOKC`), `+past` behind the
head (when the head is hinted, `tailGC_of_past`), the head, `+copy`.

The raw blocks of `[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` (`%cc2`,
`CompRunOKLC.lean`) show both `+past` blocks: `7` (the tail's need behind the
head's call, filled from the subject) and `3` (the head's need behind the
tail's call, `mov v7 v2` from the head call's `+kern` register).

* `BondOKC`: what the cons asks of a head under the bond goal (`RunOKLC` for
  some witness relation), `bondOKC_of_bondOK` (a call-free head).
* `minkF_consG`, `mink_consG_bwd`: `+mink` on a cell formula with a cell head.
* `consLC_runN`, `consLC_cleanN`, `consLC_runD`, `uokc_consLC`, `entNew_consLC`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## What the cons asks of its head under the bond goal -/

/-- **A head under the bond goal of `+past`** (`BondOK` for runs that may
call): every run under `mk bunt [] [(b, hed)]` returns a clean need and,
from a state with the hypotheses of `OKNV`, meets `RunOKLC` for some
witness relation. -/
structure BondOKC (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {hed : Sure S} {b : Nat}
    {th : Jmp}, runLC env sup nm (CGoalL.next (mk Sure.bunt [] [(b, ofSure hed)]) th) region g0 = some (nex, g1) →
    Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {hed : Sure S} {b : Nat}
    {th jb : Jmp},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → b ≠ th.there → b < g0.bo →
    HoonMap.get g0.blocks b = some ⟨[], [], Termin.hop jb⟩ → Distinct hed.ned →
    (∀ x, NMem hed.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    runLC env sup nm (CGoalL.next (mk Sure.bunt [] [(b, ofSure hed)]) th) region g0 = some (nex, g1) →
    ∃ Q, RunOKLC (Map := Map) lib P f (mk Sure.bunt [] [(b, ofSure hed)]) th Q g0 g1 nex

/-- **A call-free head with `BondOK` meets `BondOKC`** (`RunOKL.toLC`). -/
theorem bondOKC_of_bondOK {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (u : UOK (S := S) (Map := Map) lib nm) (M : MinkEq lib P f nm) (B : BondOK (S := S) (Map := Map) lib nm) :
    BondOKC (S := S) (Map := Map) lib env P f nm := by
  have nc := Nomm.noCall_of_pure nm u.pure
  refine ⟨fun h => B.clean (by rw [runLC_eq env nm nc] at h; exact h),
    fun hc b0 d0 hu hcl hcb h1 h2 _ hne hb hbb hd hen h => ?_⟩
  rw [runLC_eq env nm nc] at h
  obtain ⟨D, W, R⟩ := B.run hc b0 d0 hu hcl hcb h1 h2 hne hb hbb hd hen h
  exact ⟨_, R.toLC M⟩

/-! ## `+mink` on a cons whose head is a cell -/

theorem minkF_consG {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s fh ft : Noun} {r : Tone}
    (hfh : ∃ a b, fh = C a b) (h : minkF lib gul n tm s (C fh ft) = some r) :
    ∃ n', n' < n ∧ ∃ rh, minkF lib gul n' tm s fh = some rh ∧
      (((∀ q, rh ≠ Tone.zero q) ∧ r = rh) ∨ ∃ x, rh = Tone.zero x ∧ ∃ rt, minkF lib gul n' tm s ft = some rt ∧
        (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ r = Tone.zero (C x y))) := by
  obtain ⟨a, b, rfl⟩ := hfh
  cases n with
  | zero => simp [minkF] at h
  | succ n' =>
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    refine ⟨n', Nat.lt_succ_self n', ?_⟩
    cases eh : minkF lib gul n' tm s (C a b) with
    | none => rw [eh] at h; simp [tbind] at h
    | some rh =>
      rw [eh] at h
      refine ⟨rh, rfl, ?_⟩
      cases rh with
      | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
      | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
      | zero x =>
        refine Or.inr ⟨x, rfl, ?_⟩
        simp only [tbind_zero] at h
        cases et : minkF lib gul n' tm s ft with
        | none => rw [et] at h; simp [tbind] at h
        | some rt =>
          rw [et] at h
          refine ⟨rt, rfl, ?_⟩
          cases rt with
          | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
          | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
          | zero y =>
            simp only [tbind_zero, Option.some.injEq] at h
            exact Or.inr ⟨y, rfl, h.symm⟩

theorem mink_consG_bwd {lib : Lib} {gul : Noun} {tm : Trace} {s fh ft : Noun} {rh : Tone}
    (hfh : ∃ a b, fh = C a b) (hh : Mink lib gul tm s fh rh) :
    ((∀ q, rh ≠ Tone.zero q) → Mink lib gul tm s (C fh ft) rh) ∧
    ∀ x rt, rh = Tone.zero x → Mink lib gul tm s ft rt →
      ((∀ q, rt ≠ Tone.zero q) → Mink lib gul tm s (C fh ft) rt) ∧
      ∀ y r, rt = Tone.zero y → r = Tone.zero (C x y) → Mink lib gul tm s (C fh ft) r := by
  obtain ⟨a, b, rfl⟩ := hfh
  obtain ⟨n1, e1⟩ := hh
  refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun x rt ex ht => ?_⟩
  · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1]
    cases rh with
    | zero q => exact absurd rfl (hn q)
    | one _ => rfl
    | two _ => rfl
  · subst ex
    obtain ⟨n2, e2⟩ := ht
    have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s (C a b) _ e1
    have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s ft _ e2
    refine ⟨fun hn => ⟨max n1 n2 + 1, ?_⟩, fun y r ey er => ⟨max n1 n2 + 1, ?_⟩⟩
    · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']
      cases rt with
      | zero q => exact absurd rfl (hn q)
      | one _ => rfl
      | two _ => rfl
    · subst ey er
      rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']; rfl


/-! ## The cons from its run -/

/-- **The cons `[p d]` whose parts may both call, under a fork-free `%next
sur th`**, for a head with `UOKC` (and `BondOKC` when the tail is hinted) and
a tail with `UOKC` (and `EntNew` when it is hinted), for the formula `[fh ft]`
with `fh` a cell, from any state with the hypotheses of `OKNV`: the run of
`consT_runN` with the `+past` behind the head (`tailGC_of_past`), composed by
`pairLC_ok` with the `con` block of `+split` as the last step. -/
theorem consLC_runN (lib : Lib) {p d : Nomm} {env : CallEnv} {P : Noun → Prop} {fh ft : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fh p)
    (Bp : hinted env.cod d = some true → BondOKC (S := S) (Map := Map) lib env P fh p)
    (hfh : ∃ x y, fh = C x y) (Ud : UOKC (S := S) (Map := Map) lib env P ft d)
    (Ed : hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d)
    (hcount : sixCount p + sixCount d ≤ 255) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.cons p d) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKGC lib P (C fh ft) (CGoal.next sur th) g0 g1 nex ∧ g0.bo ≤ nex.th.there := by
  have e : (runLC env sup (Nomm.cons p d) (CGoalL.next (ofSure sur) th) region :
      CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ d region
        let nex2 ← runLC env sup d (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at h
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok hs2
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hok.1 hok.2
  obtain ⟨G2, eo', lt2, _⟩ := split_down hs2 hj.1 hj.2 d0
  simp only at eo'
  subst eo
  have CS := clean_split hs2 hcl
  simp only at CS
  have c2 : g2.cond = g0.cond := (kc_split _).keep _ _ _ hs2
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (G2.toU hu).up hu
  have lt2' : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y a) E2.1
    · exact a
  have G2U : GrowU g0 g2 := G2.toU hu
  have cl2 : Clear g2 := hcl0.growU G2U
  have cf2 : CondFresh g0 g2 := condFresh_of_eq E2.1 c2
  have cb2 : CondBelow g2 := cf2.below hcb
  have nk2 : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → HoonMap.get g2.cond y = Option.none := fun n M y hy => by
    rw [c2]
    rcases M y hy with a | ⟨a, _⟩
    · exact hkg y a
    · exact condBelow_none hcb a
  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g2 :=
    (keepsA_split (P := fun r => HoonMap.get g0.cond r = Option.none) d0 hkg (jmpIn_nil hth)
      (fun r hr => condBelow_none hcb hr) hs2).1.ab _ (aboveIn_start _ g0)
  have BS : BelowIn g0.bo g2 :=
    (keeps_split d0 (fun r hr => hok.2 r hr) (jmpIn_nil hth) hs2).1.bel _ (belowIn_start g0)
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g2.bo → (HoonMap.get g2.blocks k).map (unproxyBlob cf) = HoonMap.get g2.blocks k := by
    intro cf hcf k h0 h1
    have u0 : ∀ x, x < g2.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
    have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
    cases hg : HoonMap.get g2.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1 hg), renBlob_congr u1 (AS k b h0 h1 hg), renBlob_id]
  have hblk : ∀ (c : Straight Map), Agree c g0 g2 →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS hed x → FitsS tel y → HoldsN hed.ned regs x →
        HoldsN tel.ned regs y →
          GoalSem lib O c gul st (Keep g0 g2 (CGoal.next sur th)) regs t (jmp0 g0.bo) (CGoal.next sur th)
            (some (C x y)) := by
    intro c hc σ O st regs t gul x y fx fy hx hy
    refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩
  have hnot : ∀ x y, ¬ FitsS hed x ∨ ¬ FitsS tel y → ¬ FitsS sur (C x y) := fun x y hn hf => by
    rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  -- the last step: the `con` block
  have hA : ∀ (c : Straight Map), Agree c g0 g2 → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (n : Nat) (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun) (n' : Nat) (r : Tone), n' < n → Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS hed x → FitsS tel y → HoldsN hed.ned regs x →
        HoldsN tel.ned regs y → r = Tone.zero (C x y) →
        GoalSemCM lib O c gul Inv ν (Keep g0 g2 (CGoal.next sur th)) st regs t tm (jmp0 g0.bo)
          (CGoal.next sur th) r := by
    intro c hc σ Inv ν O n gul hS hF st regs t tm x y n' r _ hI htr fx fy hx hy hr
    subst hr
    exact goalSemC_of_goalSem hI htr _ (some (C x y)) (hblk c hc σ O st regs t gul x y fx fy hx hy)
  have hAB : ∀ (c : Straight Map), Agree c g0 g2 → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun), Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS hed x → FitsS tel y → HoldsN hed.ned regs x →
        HoldsN tel.ned regs y → ∀ res, goJ lib O c gul st regs t (jmp0 g0.bo) = some res →
        ∃ r, r = Tone.zero (C x y) ∧
          GoalSemCM lib O c gul Inv ν (Keep g0 g2 (CGoal.next sur th)) st regs t tm (jmp0 g0.bo)
            (CGoal.next sur th) r := by
    intro c hc σ Inv ν O gul hS hB st regs t tm x y hI htr fx fy hx hy res _
    exact ⟨_, rfl, goalSemC_of_goalSem hI htr _ (some (C x y)) (hblk c hc σ O st regs t gul x y fx fy hx hy)⟩
  have hnotF : ∀ (gul : Noun) (n' : Nat) (tm : Trace) (x y : Noun) (r : Tone), (¬ FitsS hed x ∨ ¬ FitsS tel y) →
      r = Tone.zero (C x y) → BadC (CGoal.next sur th) tm r :=
    fun _ _ _ x y r hn hr => Or.inr ⟨C x y, hr, hnot x y hn⟩
  have hnotB : ∀ (gul : Noun) (tm : Trace) (x y : Noun), (¬ FitsS hed x ∨ ¬ FitsS tel y) →
      ∃ r, r = Tone.zero (C x y) ∧ BadC (CGoal.next sur th) tm r :=
    fun _ _ x y hn => ⟨_, rfl, Or.inr ⟨C x y, rfl, hnot x y hn⟩⟩
  have Mf := fun {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone} (_ : P s)
      (hm : minkF lib gul n tm s (C fh ft) = some r) => minkF_consG hfh hm
  have Mb := fun {s gul : Noun} {tm : Trace} {rh : Tone} (_ : P s) (hh : Mink lib gul tm s fh rh) =>
    mink_consG_bwd (ft := ft) hfh hh
  have cq := Ud.clean (goal := CGoal.next tel nexh.th) trivial CS.2 h3
  -- `+past` behind the tail
  have pcase : (nexh = ⟨ofSure hed, jmp0 g0.bo⟩ ∧ g2' = g2 ∧ ((∀ x, FitsS hed x) ∨ TotalC lib P ft)) ∨
      (hinted env.cod d = some true ∧
        nexh = ⟨mk (Sure.bunt : Sure S) [] [(g2.bo, ofSure hed)], jmp0 g2.bo⟩ ∧
        g2' = (g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) := by
    rcases Ud.kind with ⟨ud, Md⟩ | hd
    · rw [pastL_pure _ _ ud.pure, pure_apply] at hph
      simp only [Option.some.injEq, Prod.mk.injEq] at hph
      obtain ⟨rfl, rfl⟩ := hph
      exact Or.inl ⟨rfl, rfl, Or.inr (totalC_of_minkEq Md)⟩
    · rcases pastL_hinted hd hph with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2, Or.inl (fun x => fitsS_trivial en es x)⟩
      · exact Or.inr ⟨hd, x1, x2⟩
  rcases pcase with ⟨x1, x2, hfl⟩ | ⟨hd, x1, x2⟩
  · -- the head's goal is `ofSure hed`
    subst x1; subst g2'
    have Rq := Ud.run (sup := sup) (goal := CGoal.next tel (jmp0 g0.bo)) (region := region) trivial rfl
      ⟨b0, by simp only [jmp0]; omega⟩ ⟨Dt, lt2' _ Mt⟩ CS.2 (by omega) (by omega) d2 u2 cl2 cb2 (nk2 _ Mt) h3
    obtain ⟨T, hhd, cq', -⟩ := tailGC_of_past Up Rq cq (lt2' _ Mt) (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) hp2
    have Rp := Up.run (sup := sup) (goal := CGoal.next hed nex2'.th) (region := region) trivial
      (nextArgs_nil T.ent rfl) ⟨T.lo, T.hi⟩ ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) T.ext.1⟩ CS.1
      (by omega) (by have := T.lo; have := T.hi; omega) (T.ext.2.2.1.trans d2) (T.grow.up u2) (cl2.growU T.grow)
      (T.cfr.below cb2) (fun y hy => by rw [T.cfr.get_lt (lt2' _ Mh y hy)]; exact nk2 _ Mh y hy) h4
    have cp := Up.clean (goal := CGoal.next hed nex2'.th) trivial CS.1 h4
    exact pairLC_ok Mf Mb hok E2 G2U c2 hcb Mh Mt Dht (Ext.refl g2) (GrowU.refl g2) rfl rfl
      (Or.inl ⟨rfl, rfl, hfl⟩) hhd T (RunOKGC.toLC Rp) cq' cp hcp hu d0 hfix hnotF hnotB hA hAB
  · -- the head's need parked in a bond behind the tail
    subst x1; subst g2'
    have hbk : ∀ k, HoonMap.get ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region).blocks k =
        if k = g2.bo then some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ else HoonMap.get g2.blocks k := fun k => by
      simp only [tagged_blocks, Gen.emitted, d2, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
    have Eb : Ext g2 ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) :=
      (ext_emit g2 _).trans (ext_tagged _ _ _)
    have Gb : GrowU g2 ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) :=
      (growU_emit (b := ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) (fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; exact ⟨b0, lt2⟩) u2).trans
        (growU_tagged _ _ _)
    have cbb : CondBelow ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) := fun k hk => by
      rw [tagged_cond] at hk
      have := cb2 k hk
      simp [Gen.emitted]; omega
    have Rq := Ud.run (sup := sup) (goal := CGoal.next tel (jmp0 g2.bo)) (region := region) trivial rfl
      ⟨by simp only [jmp0]; omega, by simp [jmp0, Gen.emitted]⟩
      ⟨Dt, fun y hy => by have := lt2' _ Mt y hy; simp [Gen.emitted]; omega⟩ CS.2 (by omega)
      (by simp [Gen.emitted]) (by simp [Gen.emitted, d2]) (Gb.up u2) (cl2.growU Gb) cbb
      (fun y hy => by rw [tagged_cond]; exact nk2 _ Mt y hy) h3
    have fr := Ed hd (sup := sup) (region := region) ⟨by simp only [jmp0]; omega, by simp [jmp0, Gen.emitted]⟩ rfl
      ⟨Dt, fun y hy => by have := lt2' _ Mt y hy; simp [Gen.emitted]; omega⟩ CS.2 (by omega)
      (by simp [Gen.emitted]) (by simp [Gen.emitted, d2]) (Gb.up u2) (cl2.growU Gb) cbb
      (fun y hy => by rw [tagged_cond]; exact nk2 _ Mt y hy) h3
    have fr' : g2.bo + 1 ≤ nex2.th.there := by simpa [Gen.emitted] using fr
    have bo3 : g2.bo + 1 ≤ g3.bo := by simpa [Gen.emitted] using Rq.ext.2.1
    have re3 : g2.re ≤ g3.re := by simpa [Gen.emitted] using Rq.ext.1
    obtain ⟨T, hhd, cq', hth2⟩ := tailGC_of_past Up Rq cq
      (fun y hy => by have := lt2' _ Mt y hy; simp [Gen.emitted]; omega) (Rq.ext.2.2.1.trans (by simp [Gen.emitted, d2]))
      (Rq.grow.up (Gb.up u2)) hp2
    have tb : g2.bo + 1 ≤ nex2'.th.there := by
      rcases hth2 with e | e
      · rw [e]; exact fr'
      · omega
    have tbo : (((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region)).bo = g2.bo + 1 := by
      simp [Gen.emitted]
    have bo3' := T.ext.2.1
    obtain ⟨Q, RL⟩ := (Bp hd).run (region := region) (jb := jmp0 g0.bo) (by omega) (by omega)
      (T.ext.2.2.1.trans (by simp [Gen.emitted, d2])) (T.grow.up (Gb.up u2)) ((cl2.growU Gb).growU T.grow)
      (T.cfr.below cbb) T.lo T.hi (nextArgs_nil T.ent rfl) (by omega) (by omega)
      (by rw [T.ext.2.2.2 _ (by omega), hbk, if_pos rfl])
      Dh (fun x hx => ⟨by have := lt2' _ Mh x hx; have := T.ext.1; simp [Gen.emitted] at this; omega, by
        rw [T.cfr.get_lt (by have := lt2' _ Mh x hx; simp [Gen.emitted]; omega), tagged_cond]
        exact nk2 _ Mh x hx⟩) h4
    have cp := (Bp hd).clean h4
    exact pairLC_ok (Lh := mk (Sure.bunt : Sure S) [] [(g2.bo, ofSure hed)]) Mf Mb hok E2 G2U c2 hcb Mh Mt Dht
      Eb Gb (by rw [tagged_cond]; rfl) (by simp [Gen.emitted])
      (Or.inr ⟨rfl, rfl, by simp [Gen.emitted], by rw [hbk, if_pos rfl]⟩) hhd T RL cq' cp hcp hu d0 hfix
      hnotF hnotB hA hAB

/-- **The sure need of the cons's run under `%next` is clean** (`+copy` of
the head's, clean by `UOKC.clean` or `BondOKC.clean`, and the tail's, clean
by `UOKC.clean`, or the bunt of `+past`). -/
theorem consLC_cleanN {lib : Lib} {p d : Nomm} {env : CallEnv} {P : Noun → Prop} {fh ft : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fh p)
    (Bp : hinted env.cod d = some true → BondOKC (S := S) (Map := Map) lib env P fh p)
    (Ud : UOKC (S := S) (Map := Map) lib env P ft d) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcl : Clean sur.ned)
    (h : runLC env sup (Nomm.cons p d) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    Clean nex.laz.sure.ned := by
  have e : (runLC env sup (Nomm.cons p d) (CGoalL.next (ofSure sur) th) region :
      CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ d region
        let nex2 ← runLC env sup d (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at h
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  have CS := clean_split hs2 hcl
  simp only at CS
  have cq := Ud.clean (goal := CGoal.next tel nexh.th) trivial CS.2 h3
  have cq' : Clean nex2'.laz.sure.ned := by
    rcases Up.kind with ⟨up, _⟩ | hh
    · rw [pastL_pure _ _ up.pure, pure_apply] at hp2
      simp only [Option.some.injEq, Prod.mk.injEq] at hp2
      obtain ⟨rfl, rfl⟩ := hp2
      exact cq
    · rcases pastL_hinted hh hp2 with ⟨x1, x2, _⟩ | ⟨x1, x2⟩
      · subst nex2' g3'; exact cq
      · subst nex2' g3'; trivial
  have cp : Clean nex1.laz.sure.ned := by
    rcases Ud.kind with ⟨ud, _⟩ | hd
    · rw [pastL_pure _ _ ud.pure, pure_apply] at hph
      simp only [Option.some.injEq, Prod.mk.injEq] at hph
      obtain ⟨rfl, rfl⟩ := hph
      exact Up.clean (goal := CGoal.next hed nex2'.th) trivial CS.1 h4
    · rcases pastL_hinted hd hph with ⟨x1, x2, _⟩ | ⟨x1, x2⟩
      · subst nexh g2'; exact Up.clean (goal := CGoal.next hed nex2'.th) trivial CS.1 h4
      · subst nexh g2'; exact (Bp hd).clean h4
  exact clean_copyL hcp cp cq'

/-- **The cons whose parts may both call, under `%done`**: the block
`[don re]`, then the run under `%next (lazy-from-reg re)` (`consLC_runN`),
turned into `%done` by `runOKGC_of_next`. -/
theorem consLC_runD (lib : Lib) {p d : Nomm} {env : CallEnv} {P : Noun → Prop} {fh ft : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fh p)
    (Bp : hinted env.cod d = some true → BondOKC (S := S) (Map := Map) lib env P fh p)
    (hfh : ∃ x y, fh = C x y) (Ud : UOKC (S := S) (Map := Map) lib env P ft d)
    (Ed : hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d)
    (hcount : sixCount p + sixCount d ≤ 255) {sup : Option Nomm} {region : List Nat} {g0 g' : Gen Map}
    {nex : NextL S} (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0)
    (hcb : CondBelow g0) (h : runLC env sup (Nomm.cons p d) CGoalL.done region g0 = some (nex, g')) :
    RunOKGC lib P (C fh ft) (CGoal.done : CGoal S) g0 g' nex := by
  rw [runLC_cons_done] at h
  obtain ⟨r, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨od, gb, hb, h⟩ := bind_some h
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have R := (consLC_runN (sur := lazyReg g0.re) (th := jmp0 g0.bo) lib Up Bp hfh Ud Ed hcount
    ⟨b0, by simp only [jmp0, Gen.emitted]; omega⟩ rfl
    ⟨trivial, fun x hx => by simp only [lazyReg, NMem] at hx; subst hx; simp only [Gen.emitted]; omega⟩ trivial
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      exact condBelow_none hcb (Nat.le_refl _)) h).1
  have hb : HoonMap.get g'.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    rw [R.ext.2.2.2 _ (by simp only [Gen.emitted]; omega)]
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  exact runOKGC_of_next (goal := CGoal.done) trivial hu hcb (fun j hj => by simp [finJumps] at hj) rfl hb
    (fun cf c0 => by simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0])
    (fun c σ O gul Inv ν K K' st regs t tm je r _ _ hbc H => goalSemCM_done_of_next hbc H) R

/-- **The cons whose parts may both call meets `UOKC`** for `[fh ft]` with
`fh` a cell, when it is hinted (`consLC_runN`, `consLC_runD`,
`consLC_cleanN`). -/
theorem uokc_consLC (lib : Lib) (env : CallEnv) {p d : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fh p)
    (Bp : hinted env.cod d = some true → BondOKC (S := S) (Map := Map) lib env P fh p)
    (hfh : ∃ x y, fh = C x y) (Ud : UOKC (S := S) (Map := Map) lib env P ft d)
    (Ed : hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d)
    (hh : hinted env.cod (Nomm.cons p d) = some true) :
    UOKC (S := S) (Map := Map) lib env P (C fh ft) (Nomm.cons p d) := by
  refine ⟨Or.inr hh, fun {sup goal region g0 g1 nex} hnp hc h => ?_,
    fun {sup goal region g0 g1 nex} hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h => ?_⟩
  · cases goal with
    | next sur th => exact consLC_cleanN Up Bp Ud hc h
    | done =>
      simp only [CGoal.toL] at h
      rw [runLC_cons_done] at h
      obtain ⟨r, ga, ha, h⟩ := bind_some h
      obtain ⟨od, gb, hb, h⟩ := bind_some h
      exact consLC_cleanN Up Bp Ud (show Clean (lazyReg (S := S) r).ned from trivial) h
    | pick z o => exact hnp.elim
  · cases goal with
    | next sur th => exact (consLC_runN lib Up Bp hfh Ud Ed hcount hj ha hok hcl b0 d0 hu hcl0 hcb hkg h).1
    | done => exact consLC_runD lib Up Bp hfh Ud Ed hcount b0 d0 hu hcl0 hcb h
    | pick z o => exact hnp.elim

/-- **The cons whose parts may both call meets `EntNew`** (`consLC_runN`). -/
theorem entNew_consLC (lib : Lib) (env : CallEnv) {p d : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fh p)
    (Bp : hinted env.cod d = some true → BondOKC (S := S) (Map := Map) lib env P fh p)
    (hfh : ∃ x y, fh = C x y) (Ud : UOKC (S := S) (Map := Map) lib env P ft d)
    (Ed : hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d) :
    EntNew (S := S) (Map := Map) env (Nomm.cons p d) := by
  intro sup sur th region g0 g1 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  exact (consLC_runN lib Up Bp hfh Ud Ed hcount hj hth hok hcl b0 d0 hu hcl0 hcb hkg h).2

end Comp
end SkaModel
end Formalization
