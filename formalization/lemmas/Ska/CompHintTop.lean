import lemmas.Ska.CompHintEq
import lemmas.Ska.CompFourTop

/-!
# The first contract with a hint: `[11 tag f]` around `CallTreeA` (README Gaps 24)

A static hint whose tag is not `hint-static` (every tag but `%bout` and
`%xray`: `%spot`, `%fast`, `%memo`, an unknown one) compiles as its formula
(`runLCH_n11s`: line 4271, `$(nomm q.nomm)`), and `+mink` runs it as its
formula with one more level of fuel (`minkAs_n11s`).  So:

* `MinkAs lib f' f`: `+mink` on `f'` returns what it returns on `f` with no
  more fuel, and every result of `f` is one of `f'`;
* `RunOKGB.minkAs`, `DoneOK.minkAs`: the relations of a run for `f` hold
  for `f'` (the fields `nec`, `sem`, `semB` read the formula; `sem` with
  `oracleFwd_le`);
* `n11s_doneA`: `DoneOK` of `[11 tag f]` for `n11s tag q body` with `q` in
  `CallTreeA` under `%done`, with `runLCH` and `mono` `&`;
* `finishLUCH_contractN11s`: the contract at the top, both halves, of the
  whole-subject code `finishLUCH` makes, for the formula `[11 tag f]`, and
  `finishLUCH_bellContractN11s`, the bell contract.

The contract is trace-aware as it stands (`ToneRel`, `FrameRel`); a static
hint pushes no frame, so the traces are those of `f`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- `+mink` runs `f'` as `f`. -/
structure MinkAs (lib : Lib) (f' f : Noun) : Prop where
  fwd : ∀ {gul : Noun} {n : Nat} {tm : Trace} {s : Noun} {r : Tone}, minkF lib gul n tm s f' = some r →
    ∃ n', n' ≤ n ∧ minkF lib gul n' tm s f = some r
  bwd : ∀ {gul : Noun} {tm : Trace} {s : Noun} {r : Tone}, Mink lib gul tm s f r → Mink lib gul tm s f' r

theorem tbind_zero (x : Option Tone) : tbind x (fun p => some (Tone.zero p)) = x := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> rfl

theorem minkF_n11s (lib : Lib) (gul : Noun) (n : Nat) (tm : Trace) (s : Noun) (tag : Nat) (f : Noun) :
    minkF lib gul (n + 1) tm s (n3 (A 11) (A tag) f) = minkF lib gul n tm s f := by
  show tbind (minkF lib gul n tm s f) (fun p => some (Tone.zero p)) = _
  exact tbind_zero _

/-- **A static hint runs as its formula.** -/
theorem minkAs_n11s (lib : Lib) (tag : Nat) (f : Noun) : MinkAs lib (n3 (A 11) (A tag) f) f where
  fwd := fun {gul n tm s r} h => by
    cases n with
    | zero => simp [minkF] at h
    | succ n =>
      rw [minkF_n11s] at h
      exact ⟨n, Nat.le_succ n, h⟩
  bwd := fun {gul tm s r} ⟨n, h⟩ => ⟨n + 1, by rw [minkF_n11s]; exact h⟩

/-- **`RunOKGB` for `f` holds for a formula `+mink` runs as `f`.** -/
theorem RunOKGB.minkAs {lib : Lib} {N : Needs} {P : Noun → Prop} {f f' : Noun} {goal : CGoal S}
    {g0 g1 : Gen Map} {nex : NextL S} (M : MinkAs lib f' f) (R : RunOKGB lib N P f goal g0 g1 nex) :
    RunOKGB lib N P f' goal g0 g1 nex where
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
    · obtain ⟨n', -, h'⟩ := M.fwd h
      exact h1 gul n' tm r h'
    · obtain ⟨r, hm, hb⟩ := h2 gul tm
      exact ⟨r, M.bwd hm, hb⟩
  ncond := R.ncond
  econd := R.econd
  sem := fun cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI ht hP hm => by
    obtain ⟨n', hn, h'⟩ := M.fwd hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn) st t tm s0 s r hI ht hP h'
  semB := fun cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg => by
    obtain ⟨r, hm, hg'⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg
    exact ⟨r, M.bwd hm, hg'⟩

/-- **`DoneOK` for `f` holds for a formula `+mink` runs as `f`.** -/
theorem DoneOK.minkAs {lib : Lib} {N : Needs} {P : Noun → Prop} {f f' : Noun} {g0 g1 : Gen Map} {nex : NextL S}
    (M : MinkAs lib f' f) (D : DoneOK lib N P f g0 g1 nex) : DoneOK lib N P f' g0 g1 nex :=
  ⟨D.run.minkAs M, D.nent, D.flat, D.clean, D.eclean⟩

/-- The nomms of `CallTreeA` have no hint. -/
theorem CallTreeA.noHint {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) : nm.noHint = true := by
  induction h <;> simp_all [Nomm.noHint]

/-- The nomms of `CallTreeA` have no direct call. -/
theorem CallTreeA.noDirect {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) : nm.noDirect = true := by
  induction h <;> simp_all [Nomm.noDirect]

/-- **A static hint that is not `hint-static` compiles as its formula.** -/
theorem runLCH_n11s [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (mono : Bool)
    {tag : Nat} (hs : hintStatic tag = false) (sup : Option Nomm) (q : Nomm) (body : Noun) (goal : CGoalL S)
    (region : List Nat) :
    (runLCH env snd mono sup (Nomm.n11s tag q body) goal region : CM Map (NextL S)) =
      runLCH env snd mono sup q goal region := by
  simp only [runLCH, hs, Bool.not_false, if_true]

/-- The same with `mono` `&` on `q` without hints and direct calls: `runLC`. -/
theorem runLCH_n11s_LC [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    {tag : Nat} (hs : hintStatic tag = false) (sup : Option Nomm) {q : Nomm} (hh : q.noHint = true)
    (hd : q.noDirect = true) (body : Noun) (goal : CGoalL S) (region : List Nat) :
    (runLCH env snd true sup (Nomm.n11s tag q body) goal region : CM Map (NextL S)) =
      runLC env sup q goal region := by
  rw [runLCH_n11s env snd true hs, runLCH_eq env snd true q hh, runLCM_true env hd]

/-- **`DoneOK` of a static hint around `CallTreeA`.** -/
theorem n11s_doneA [HoonMapKeys Map] (lib : Lib) {N : Needs} (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    {tag : Nat} (hs : hintStatic tag = false) {b : Bool} {f : Noun} {q : Nomm} (h : CallTreeA b f q) (body : Noun)
    (P : Noun → Prop) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH env snd true sup (Nomm.n11s tag q body) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P (n3 (A 11) (A tag) f) g0 g1 nex := by
  rw [runLCH_n11s_LC env snd hs sup h.noHint h.noDirect] at hr
  exact (callTreeA_done lib env h P b0 d0 hu hcl hcb hr).minkAs (minkAs_n11s lib tag f)

variable [HoonMapKeys Map]

/-- `finishLUCH` of the hint is `finishLUC` of its formula. -/
theorem finishLUCH_n11s (env : CallEnv) (snd : Nomm → NeedOrd → Bool) {tag : Nat} (hs : hintStatic tag = false)
    {q : Nomm} (hh : q.noHint = true) (hd : q.noDirect = true) (body : Noun) :
    finishLUCH (S := S) (Map := Map) env snd (Nomm.n11s tag q body) = finishLUC (S := S) env q := by
  unfold finishLUCH finishLUC
  rw [runLCH_n11s_LC env snd hs Option.none hh hd]

/-- **The contract at the top of `[11 tag f]` with `f` of `CallTreeA`**: the
whole-subject code `finishLUCH` makes meets both halves of the contract for
the hinted formula, traces included, on every subject. -/
theorem finishLUCH_contractN11s (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (P : Noun → Prop)
    {tag : Nat} (hs : hintStatic tag = false) {b : Bool} {f : Noun} {q : Nomm} (h : CallTreeA b f q) (body : Noun)
    {c : Straight Map} (hc : finishLUCH (S := S) env snd (Nomm.n11s tag q body) = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 11) (A tag) f) [s] c ∧ ContractBwd lib N s (n3 (A 11) (A tag) f) [s] c := by
  rw [finishLUCH_n11s env snd hs h.noHint h.noDirect] at hc
  exact finishLUC_contractGB lib N (fun hr => ((callTreeA_done (S := S) (Map := Map) lib env h P (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr).minkAs (minkAs_n11s lib tag f)).run) hc

/-- **The bell contract**, for a bell whose formula is `[11 tag f]`. -/
theorem finishLUCH_bellContractN11s {lib : Lib} {bl : Bell} (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    {tag : Nat} (hs : hintStatic tag = false) {b : Bool} {f : Noun} {q : Nomm} (h : CallTreeA b f q) (body : Noun)
    (hf : bl.fol = n3 (A 11) (A tag) f)
    {cd : Straight Map} (hc : finishLUCH (S := S) env snd (Nomm.n11s tag q body) = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUCH_contractN11s (S := S) lib env snd (SkaModel.Fits bl.less) hs h body hc N
  refine ⟨H.1, fun s hs' args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  rw [hf]
  exact H.2 s hs'

end Comp
end SkaModel
end Formalization
