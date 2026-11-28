import lemmas.Ska.CompHintTenEx
import lemmas.Ska.CompHintSurOps

/-!
# Helpers of the hinted class `HintCls` (README Gaps 24.22)

* `DoneG` (every run under `%done` gives `RunOKGBT`), `DoneNext` (the run
  under `%done` is the block `[don re]`, then the run under `%next
  (lazy-from-reg re)`), **`doneG_of_next`** (`RegGBT` and `DoneNext` give
  `DoneG`), `doneNext_n10`, `doneNext_n11s`, `doneNext_n11d`,
  `doneNext_mean` (the cases of `+run` that begin with `+simple-next`),
  `doneG_four` (`[4 p]` has its own `%done` case: `four_doneR`),
  `DoneAllT.toG`, **`finishLUCH_contractDoneG`**.
* `SurGBT.mono`, `regLike_soundFit` (a `RegLike` need meets what `+past-if`
  asks of a kept hint), `into_regLike_reg` (the donor of `+into` under a
  `RegLike` need is `RegLike`), `SurGBT.toReg`.
* `orB_mono`, **`hinted_crash`** (`+hinted` decided with every callee
  crashing is `+hinted` under any table).
* `splitL_ofSure`, `pastL_notHinted`, **`noBondH_cons`** (a cons of unhinted
  parts with `NoBondH`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `%done` -/

/-- **Every run under `%done`** from a state as the top gives, gives `RunOKGBT`. -/
def DoneG (lib : Lib) (N : Needs) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLCH env snd true sup nm CGoalL.done region g0 = some (nex, g1) →
    RunOKGBT lib N P f (CGoal.done : CGoal S) g0 g1 nex

/-- **The run under `%done` is the block `[don re]`, then the run under
`%next (lazy-from-reg re)` into it** (the cases that begin with
`+simple-next`). -/
def DoneNext (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) : Prop :=
  ∀ (sup : Option Nomm) (region : List Nat) (g0 : Gen Map),
    (runLCH env snd true sup nm CGoalL.done region g0 : Option (NextL S × Gen Map)) =
      runLCH env snd true sup nm (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩)

section
variable {snd : Nomm → NeedOrd → Bool}

/-- **`RegGBT` and `DoneNext` give `DoneG`** (the proof of `ten_doneS`). -/
theorem doneG_of_next {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : RegGBT (S := S) (Map := Map) snd lib N env P f nm) (hD : DoneNext (S := S) (Map := Map) env snd nm) :
    DoneG (S := S) (Map := Map) lib N env snd P f nm := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [hD] at hr
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have GA := (growU_re g0 _).trans G1
  have R := H (by simp [Gen.emitted]) (by simpa [Gen.emitted] using d0) (GA.up hu)
    (hcl.growU GA) (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl (by simp [Gen.emitted])
    (by simp only [Gen.emitted]; exact condBelow_none hcb (Nat.le_refl _)) hr
  exact runOKGBT_done hu hcb (by rw [R.ext.2.2.2 _ (by simp [Gen.emitted])]; exact hk_emitted_self d0 _) R

theorem doneNext_n10 (env : CallEnv) (a : Nat) (v q : Nomm) :
    DoneNext (S := S) (Map := Map) env snd (Nomm.n10 a v q) :=
  fun sup region g0 => runLCH_n10_done_next env sup region g0

theorem doneNext_n11s (env : CallEnv) {tag : Nat} (hs : hintStatic tag = true) (q : Nomm) (body : Noun) :
    DoneNext (S := S) (Map := Map) env snd (Nomm.n11s tag q body) := by
  intro sup region g0
  simp only [runLCH, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_apply, simpleNextL_done,
    Option.bind_some]
  simp only [simpleNextL, pure_apply, Option.bind_some]

theorem doneNext_n11d (env : CallEnv) {tag : Nat} (hs : hintDynamic tag = true) (h q : Nomm) (body : Noun) :
    DoneNext (S := S) (Map := Map) env snd (Nomm.n11d tag h q body) :=
  fun sup region g0 => runLCH_n11d_done_next hs sup region g0

theorem doneNext_mean {env : CallEnv} {p : Nomm} {b : Bell} {q : Nomm} {body : Noun} {k : Option Noun}
    (hk : meanKonst env b k = Option.none) : DoneNext (S := S) (Map := Map) env snd (Nomm.mean p b q body k) := by
  intro sup region g0
  simp only [runLCH, hk, ↓reduceIte, bind_apply, simpleNextL_done, Option.bind_some]
  simp only [simpleNextL, pure_apply, Option.bind_some]

/-- `[4 p]` under `%done` (its own case of `+run`, `four_doneR`). -/
theorem doneG_four (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {f fb : Noun} {p : Nomm}
    (Sp : RegGBT (S := S) (Map := Map) snd lib N env P fb p) (M : MinkC4 lib P f fb) :
    DoneG (S := S) (Map := Map) lib N env snd P f (Nomm.n4 p) :=
  fun b0 d0 hu hcl hcb hr => four_doneR lib Sp M b0 d0 hu hcl hcb hr

theorem DoneAllT.toG {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : DoneAllT (S := S) (Map := Map) lib N env snd P f nm) : DoneG (S := S) (Map := Map) lib N env snd P f nm :=
  fun b0 d0 hu hcl hcb hr => (H b0 d0 hu hcl hcb hr).run

/-- **The contract at the top of anything with `DoneG`**, traces included. -/
theorem finishLUCH_contractDoneG (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : DoneG (S := S) (Map := Map) lib N env snd P f nm) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractGBT lib N (fun hr => H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc

/-! ## The needs of the sure class -/

theorem SurGBT.mono {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    {Ap Ap' : Sure S → Prop} (hA : ∀ s, Ap s → Ap' s) (H : SurGBT (S := S) (Map := Map) snd lib N env P Ap' f nm) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap f nm := by
  intro sup sur th region g0 g1 nex hap
  exact H (hA _ hap)

/-- **A `RegLike` need meets what `+past-if` asks of a kept hint** over a
formula with `+sound` of `%this`. -/
theorem regLike_soundFit {q : Nomm} (hs : snd q NeedOrd.this = true) (lib : Lib) (P : Noun → Prop) (fq : Noun)
    {sur : Sure S} (hR : RegLike sur) : SoundK snd q sur ∧ FitP lib P fq sur := by
  obtain ⟨k, hk, hl⟩ := hR
  refine ⟨⟨(HoonSet.small_iff _).2 (fun x hx => by rw [hl] at hx; cases hx), (by rw [hk]; exact hs)⟩, ?_⟩
  intro s _ gul tm p _
  refine ⟨?_, (fun a ha => by rw [hl] at ha; cases ha)⟩
  rw [hk]; trivial

/-- **The donor of `+into` under a `RegLike` need is `RegLike`** (the proof
of `into_regLike_fit`). -/
theorem into_regLike_reg {sur : Sure S} {th : Jmp} {a : Nat} (ha : 2 ≤ a) {g g' : Gen Map} {d r : Sure S}
    {o : Nat} (hR : RegLike sur) (h : into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g')) : RegLike d := by
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
  rw [hk] at h3
  simp only [intoNeed, show a ≠ 0 by omega, show a ≠ 1 by omega, ↓reduceIte] at h3
  obtain ⟨k', rfl⟩ := intoLoop_this o' a k [] [] g0 g2 nd nr h3
  exact ⟨k', rfl, List.eq_nil_iff_forall_not_mem.mpr fun x hx => HoonSet.mem_empty x hx⟩

/-- **`SurGBT RegLike` is in `RegGBT`** (`lazy-from-reg` is `RegLike`). -/
theorem SurGBT.toReg {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : SurGBT (S := S) (Map := Map) snd lib N env P RegLike f nm) :
    RegGBT (S := S) (Map := Map) snd lib N env P f nm :=
  RegGBT.ofSur (SurGBT.mono (fun s hs => by obtain ⟨r, rfl⟩ := hs; exact regLike_lazyReg r) H)

end

/-! ## `+hinted` with every callee crashing -/

theorem orB_mono {a b a' b' : Option Bool} (ha : ∀ x, a = some x → a' = some x)
    (hb : ∀ x, b = some x → b' = some x) (x : Bool) (h : orB a b = some x) : orB a' b' = some x := by
  cases a with
  | none => simp [orB] at h
  | some c =>
    rw [ha c rfl]
    cases c with
    | false => exact hb x h
    | true => exact h

theorem hinted_crash_all (cod : Bell → Option Bool) :
    ∀ (v : Nomm) (r : Bool), hinted (fun _ => Option.none) v = some r → hinted cod v = some r := by
  intro v
  induction v with
  | cons p q ihp ihq => intro r h; simp only [hinted] at h ⊢; exact orB_mono ihp ihq r h
  | n0 _ => exact fun r h => h
  | n1 _ => exact fun r h => h
  | n2 p q info ihp ihq =>
    intro r h
    cases info with
    | none => exact h
    | some bi => obtain ⟨b, x⟩ := bi; simp [hinted, orB] at h
  | n3 p ih => intro r h; simp only [hinted] at h ⊢; exact ih r h
  | n4 p ih => intro r h; simp only [hinted] at h ⊢; exact ih r h
  | n5 p q ihp ihq => intro r h; simp only [hinted] at h ⊢; exact orB_mono ihp ihq r h
  | n6 p q s ihp ihq ihs =>
    intro r h; simp only [hinted] at h ⊢; exact orB_mono ihp (fun x => orB_mono ihq ihs x) r h
  | n7 p q ihp ihq => intro r h; simp only [hinted] at h ⊢; exact orB_mono ihp ihq r h
  | n10 a v q ihv ihq => intro r h; simp only [hinted] at h ⊢; exact orB_mono ihv ihq r h
  | n11s tag q body ih => intro r h; simp only [hinted] at h ⊢; exact orB_mono (fun x hx => hx) ih r h
  | n11d tag h q body ihh ihq =>
    intro r hh; simp only [hinted] at hh ⊢; exact orB_mono (fun x hx => hx) (fun x => orB_mono ihh ihq x) r hh
  | n12 p q _ _ => exact fun r h => h
  | mean p b q body k _ _ => exact fun r h => h

/-- **`+hinted` decided with every callee crashing is `+hinted` under any
table.** -/
theorem hinted_crash {v : Nomm} {r : Bool} (h : hinted (fun _ => Option.none) v = some r)
    (cod : Bell → Option Bool) : hinted cod v = some r :=
  hinted_crash_all cod v r h

/-! ## `NoBondH` of a cons -/

/-- `+split` of a flat need without forks or bonds gives two flat needs. -/
theorem splitL_ofSure {sur : Sure S} {th : Jmp} {g g' : Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL (⟨ofSure sur, th⟩ : NextL S) g = some ((hed, tel, o), g')) :
    ∃ sh st : Sure S, hed = ofSure sh ∧ tel = ofSure st := by
  unfold splitL at h
  obtain ⟨o', g1, he, h⟩ := bind_some h
  obtain ⟨⟨h', t'⟩, g2, hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  simp only [ofSure, splitLoop, List.isEmpty_nil, Bool.and_self, ↓reduceIte] at hl
  obtain ⟨⟨sh, st⟩, g3, h3, h4⟩ := bind_some hl
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  exact ⟨sh, st, rfl, rfl⟩

/-- `+past` over a nomm that is not hinted returns the need. -/
theorem pastL_notHinted {cod : Bell → Option Bool} {nex nex' : NextL S} {nom : Nomm} {region : List Nat}
    {g g' : Gen Map} (hh : hinted cod nom ≠ some true) (h : pastL cod nex nom region g = some (nex', g')) :
    nex' = nex := by
  unfold pastL at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  · cases eh : hinted cod nom with
    | none => simp [eh] at h
    | some b =>
      cases b with
      | true => exact absurd eh hh
      | false =>
        simp only [eh, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        exact h.1.symm

section
variable {snd : Nomm → NeedOrd → Bool} {env : CallEnv}

/-- **`NoBondH` of a cons whose parts have it and are not hinted.** -/
theorem noBondH_cons {p q : Nomm} (hp : NoBondH (S := S) (Map := Map) snd env p)
    (hq : NoBondH (S := S) (Map := Map) snd env q) (hhp : hinted env.cod p ≠ some true)
    (hhq : hinted env.cod q ≠ some true) : NoBondH (S := S) (Map := Map) snd env (Nomm.cons p q) := by
  intro sup sur th region g0 g1 nex hr
  have e : (runLCH env snd true sup (Nomm.cons p q) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) =
      (do
        let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLCH env snd true sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLCH env snd true sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, ga, hs, r1⟩ := bind_some hr
  obtain ⟨sh, st, rfl, rfl⟩ := splitL_ofSure hs
  obtain ⟨nexh, gb, hh, r2⟩ := bind_some r1
  have eh := pastL_notHinted hhq hh
  subst eh
  obtain ⟨nex2, gc, h2, r3⟩ := bind_some r2
  obtain ⟨f2, b2⟩ := hq h2
  obtain ⟨nex2', gd, h2', r4⟩ := bind_some r3
  have e2 := pastL_notHinted hhp h2'
  subst e2
  obtain ⟨nex1, ge, h1, hC⟩ := bind_some r4
  obtain ⟨f1, b1⟩ := hp h1
  exact copyL_noBond f1 b1 f2 b2 hC

end

end Comp
end SkaModel
end Formalization
