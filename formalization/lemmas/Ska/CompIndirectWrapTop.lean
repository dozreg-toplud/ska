import lemmas.Ska.CompIndirectGen

/-!
# The first call theorem on every `Annot` of `[2 p q]` but the bare ones

README Gaps 12.12 (sixteenth session).  `indirectTop_contractA`: the
whole-subject code of the nomm `[2 p q]` with no callee, `p` and `q` in
`FragU`, at most 255 `%6`, and `q` not the literal `[1 f]` of a `%bare`
formula, meets `BellContract lib N bl true` for every `Annot` of the bell's
formula by that nomm.  The proof is that of `indirectTop_contract` with
`MinkN2` (`minkN2_of_annot`) in place of `Annot.indirect`: `indirectTop_gen`
with `fwdPhi` and `bwdPhi` on the formula `bl.fol` itself, their `sem` from
`indirect_semM`, `indirect_semBM` (generated), their `nec` from
`indirect_necM`, `indirect_necBM`.  For example the formula
`[6 [1 0] [2 [0 3] [0 2]] [0 0]]`, whose nomm is `[2 [0 3] [0 2]]` through
`Annot.six0`, is covered, which `indirectTop_contract` (on `[2 b c]`) is
not.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- Where the run's need does not fit, the code's crash meets `fwdPhi`. -/
theorem indirect_necM {lib : Lib} {P : Noun → Prop} {f : Noun} {p q : Nomm} (M : MinkN2 lib P f p q)
    (N : Needs) {g3 g6 : Gen Map} {nex : NextL S}
    (Rm : RunOKNV lib (Nomm.cons p q) (pairSure 2 3 : Sure S) (jmp0 3) g3 g6 nex) :
    ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → fwdPhi lib N P f σ O st t gul s (some (Tone.two t, st)) := by
  intro σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr
  rcases Rm.nec s hfs with e | ⟨v, ev, hv⟩
  · rcases M.fwd hs hm with ⟨n', x, y, _, ex, ey, _⟩ | ⟨_, er⟩
    · rw [pureEval_cons, ex, ey] at e; simp at e
    · exact ⟨Tone.two t, st, rfl, by rw [er]; exact ToneRel.two htr⟩
  · exfalso
    apply hv
    rw [pureEval_cons] at ev
    obtain ⟨x, -, ev⟩ := Option.bind_eq_some_iff.mp ev
    obtain ⟨y, -, ev⟩ := Option.bind_eq_some_iff.mp ev
    cases ev
    exact ⟨⟨trivial, trivial⟩, looks_empty _⟩

/-- Where the run's need does not fit, the code's crash meets `bwdPhi`. -/
theorem indirect_necBM {lib : Lib} {P : Noun → Prop} {f : Noun} {p q : Nomm} (M : MinkN2 lib P f p q)
    (N : Needs) {g3 g6 : Gen Map} {nex : NextL S}
    (Rm : RunOKNV lib (Nomm.cons p q) (pairSure 2 3 : Sure S) (jmp0 3) g3 g6 nex) :
    ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → bwdPhi lib N P f σ O st t gul s (some (Tone.two t, st)) := by
  intro σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx
  cases hx
  rcases Rm.nec s hfs with e | ⟨v, ev, hv⟩
  · rw [pureEval_cons] at e
    exact ⟨_, M.crash hs e, ToneRel.two htr⟩
  · exfalso
    apply hv
    rw [pureEval_cons] at ev
    obtain ⟨x, -, ev⟩ := Option.bind_eq_some_iff.mp ev
    obtain ⟨y, -, ev⟩ := Option.bind_eq_some_iff.mp ev
    cases ev
    exact ⟨⟨trivial, trivial⟩, looks_empty _⟩

/-- **The first call theorem on `MinkN2`, forward.** -/
theorem indirectTop_fwdM {lib : Lib} {bl : Bell} {p q : Nomm}
    (M : MinkN2 lib (SkaModel.Fits bl.less) bl.fol p q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s → ContractFwd lib N s bl.fol [s] c := by
  have F := indirectTop_gen (lib := lib) hp hq hcount (fwdPhi lib N (SkaModel.Fits bl.less) bl.fol)
    (fun _ _ _ Rm r3 b3 cn3 k1 k2 k3 =>
      ⟨indirect_semM M N Rm r3 b3 cn3 k1 k2 k3, indirect_necM M N Rm⟩) h
  refine ⟨F.1, fun s hs σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_⟩
  exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr

/-- **The first call theorem on `MinkN2`, backward.** -/
theorem indirectTop_bwdM {lib : Lib} {bl : Bell} {p q : Nomm}
    (M : MinkN2 lib (SkaModel.Fits bl.less) bl.fol p q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s → ContractBwd lib N s bl.fol [s] c := by
  have F := indirectTop_gen (lib := lib) hp hq hcount (bwdPhi lib N (SkaModel.Fits bl.less) bl.fol)
    (fun _ _ _ Rm r3 b3 cn3 k1 k2 k3 =>
      ⟨indirect_semBM M N Rm r3 b3 cn3 k1 k2 k3, indirect_necBM M N Rm⟩) h
  refine ⟨F.1, fun s hs σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩
  exact F.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The first call theorem on `MinkN2`**: both halves. -/
theorem indirectTop_contractM {lib : Lib} {bl : Bell} {p q : Nomm}
    (M : MinkN2 lib (SkaModel.Fits bl.less) bl.fol p q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ BellContract lib N bl true c := by
  refine ⟨(indirectTop_fwdM M hp hq hcount h N).1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact ⟨(indirectTop_fwdM M hp hq hcount h N).2 s hs, (indirectTop_bwdM M hp hq hcount h N).2 s hs⟩

/-- **The first call theorem on every `Annot` of `[2 p q]` but the bare
ones**: the whole-subject code of the nomm `[2 p q]` with no callee, for
any `Annot` of the bell's formula by it (the formula `[2 b c]` under any
number of `%memo` and constant `%6`), with `p`, `q` in `FragU`, at most 255
`%6`, and `q` not the literal of a `%bare` formula, meets `BellContract`. -/
theorem indirectTop_contractA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {p q : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n2 p q Option.none))
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    (hb : bareLitQ q = false)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ BellContract lib N bl true c :=
  indirectTop_contractM (minkN2_of_annot hok hA rfl (fragU_pure hp) (fragU_pure hq) hb) hp hq hcount h N

end Comp
end SkaModel
end Formalization
