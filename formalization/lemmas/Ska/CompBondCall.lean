import lemmas.Ska.CompKerfLC
import lemmas.Ska.CompFragD

/-!
# The indirect call as a head under the bond goal, and the fragment `FragE`

README Gaps 12.20.  The cons whose both parts call (`[[2 [0 3] [0 2]] [2 [0 3]
[0 2]]]`, `%cc2` of `CompRunOKLC.lean`) runs its head call under the bond
goal of `+past` behind the tail call: the call's `+kerf` puts `mov v7 v2` at
the bond block, and the head meets `RunOKLC` with the witness `kernWit pro`
(`kerfLC` after `indirectC_inner`).

* `RunOKLC.wrap`, `BondOKC.wrap`: through the memo hint and the folded `%6`.
* `bondOKC_indirectC`: the indirect call whose parts meet `UOKC` meets
  `BondOKC`.
* `FragE`: `FragD` with the cons whose head is such an indirect call and
  whose tail is in `FragE` (`FragE.consI`), `uokc_entNew_of_fragE`,
  `finishLUC_contractUE`; `consCC_example` (`[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]`,
  both halves).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`RunOKLC` goes through a wrapper** (`WrapRel`). -/
theorem RunOKLC.wrap {lib : Lib} {P : Noun → Prop} {f f' : Noun} (W : WrapRel lib P f f') {L : Lazy S} {th : Jmp}
    {Q : Wit} {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKLC (Map := Map) lib P f L th Q g0 g1 nex) :
    RunOKLC lib P f' L th Q g0 g1 nex := by
  refine ⟨R.re, R.bo, R.drop, R.keep, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    R.dreg, fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, R.ncond, R.econd, R.front, ?_, ?_⟩
  · obtain ⟨n', _, hm'⟩ := W.fwd hs hm
    exact (R.nec s hs hf).1 gul n' tm r hm'
  · obtain ⟨r, hm, hb⟩ := (R.nec s hs hf).2 gul tm
    exact ⟨r, W.bwd hs hm, hb⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hle, hm'⟩ := W.fwd hs hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hle) st t tm s0 s r hI htr hs hm' ag hned
      regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact ⟨r, W.bwd hs hm, G⟩

theorem BondOKC.wrap {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f f' : Noun} {nm : Nomm}
    (W : WrapRel lib P f f') (B : BondOKC (S := S) (Map := Map) lib env P f nm) :
    BondOKC (S := S) (Map := Map) lib env P f' nm :=
  ⟨B.clean, fun hc b0 d0 hu hcl hcb h1 h2 ha hne hb hbb hd hen h => by
    obtain ⟨Q, R⟩ := B.run hc b0 d0 hu hcl hcb h1 h2 ha hne hb hbb hd hen h
    exact ⟨Q, R.wrap W⟩⟩

/-- **The indirect call whose parts meet `UOKC` meets `BondOKC`**: under the
bond goal `+simple-next` is the identity, `+kerf` fills the bond block from
`pro` (`kerf_specL`), the rest is `indirectC_inner`, and `kerfLC` composes. -/
theorem bondOKC_indirectC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) : BondOKC (S := S) (Map := Map) lib env P f (Nomm.n2 p q Option.none) := by
  refine ⟨fun h => indirectC_clean Up Uq h, fun {sup region g0 g' nex hed b th jb} hc b0 d0 hu hcl hcb h1 h2 ha
    hne hb hbb hd hen h => ?_⟩
  have hcount : sixCount p + sixCount q ≤ 255 := hc
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, hs1, hk, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs1
  obtain ⟨rfl, rfl⟩ := hs1
  have E := entries_bond1 b hed
  have hlab : ∀ e ∈ entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]),
      e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ := by
    rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hb, [], _, hbb⟩
  have hnd : ((entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)])).map Prod.fst).Nodup := by rw [E]; simp
  obtain ⟨rfl, rfl, b2, dr2, l2, PF, G2, -, -, -, c0, -⟩ := kerf_specL hk d0 hcb hu h1 h2 hlab hnd
  have R := (indirectC_inner lib Up Uq M hcount (by omega) b0 (by omega) c0 (by omega) (dr2.trans d0) (G2.up hu)
    (hcl.growU G2) (PF.1.below hcb) h3 h4 h5 h6 h7).1
  exact ⟨_, kerfLC hk d0 hcb hu ha h1 h2 trivial (fun x hx => absurd hx (by simp [Sure.bunt, NMem])) hlab hnd
    (by rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hd, hen⟩) R⟩


/-! ## The indirect call as a head on every `Annot` -/

/-- **The indirect call with call-free parts meets `BondOKC` on every
`Annot`** (`bondOKC_indirectC`, the wrappers by `BondOKC.wrap`). -/
theorem bondOKC_indA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {b c : Nomm}
    (hb : FragU (S := S) b) (hc : FragU (S := S) c) (hbl : bareLitQ c = false)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n2 b c Option.none → BondOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | indirect hb' hc' _ _ =>
    intro e
    cases e
    exact bondOKC_indirectC lib env (uokcU hok env hb hb') (uokcU hok env hc hc') (minkC2_indirect lib _ _ _)
  | bare hf => intro e; cases e; simp [bareLitQ, hf] at hbl
  | bareLit hf _ => intro e; cases e; simp [bareLitQ, hf] at hbl
  | memo hm _ ih' => intro e; exact BondOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact BondOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact BondOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e

/-- **The cons on every `Annot`, with the head under the bond goal given**
(`uokc_consDA` with any provider of `BondOKC`). -/
theorem uokc_consEA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p d : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (ihb : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → hinted env.cod d = some true →
      BondOKC (S := S) (Map := Map) lib env P f p)
    (ihd : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f d →
      UOKC (S := S) (Map := Map) lib env P f d ∧ (hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d))
    (hh : hinted env.cod (Nomm.cons p d) = some true)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.cons p d → UOKC (S := S) (Map := Map) lib env P f nm ∧ EntNew (S := S) (Map := Map) env nm := by
  induction hA with
  | cons hA1 hA2 _ _ =>
    intro e
    cases e
    exact ⟨uokc_consLC lib env (ihp hA1) (ihb hA1) ⟨_, _, rfl⟩ (ihd hA2).1 (ihd hA2).2 hh,
      entNew_consLC lib env (ihp hA1) (ihb hA1) ⟨_, _, rfl⟩ (ihd hA2).1 (ihd hA2).2⟩
  | memo hm _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_memo hm) (ih' e).1, (ih' e).2⟩
  | six0 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | six1 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e
  | bareLit => intro e; cases e

/-! ## The fragment with calls in both halves of a cons -/

/-- **`FragD` with the cons whose head is an indirect call** (with call-free
parts) and whose tail is in the fragment (so the tail calls and the head
runs under the bond goal). -/
inductive FragE : Nomm → Prop
  | d {nm : Nomm} : FragD (S := S) nm → FragE nm
  | consI {b c d : Nomm} : FragU (S := S) b → FragU (S := S) c → bareLitQ c = false → FragE d →
      FragE (Nomm.cons (Nomm.n2 b c Option.none) d)

def FragUE (S : Type) [HoonSet S] (nm : Nomm) : Prop := FragU (S := S) nm ∨ FragE (S := S) nm

theorem fragE_hinted (cod : Bell → Option Bool) {nm : Nomm} (h : FragE (S := S) nm) : hinted cod nm = some true := by
  induction h with
  | d h => exact fragD_hinted cod h
  | consI _ _ _ _ ih => simp only [hinted, ih]; rfl

/-- **The joint induction over `FragE`.** -/
theorem uokc_entNew_of_fragE {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv)
    {nm : Nomm} (hf : FragE (S := S) nm) :
    ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f nm →
      UOKC (S := S) (Map := Map) lib env P f nm ∧ EntNew (S := S) (Map := Map) env nm := by
  induction hf with
  | d h => exact fun hA => uokc_entNew_of_fragD hok env h hA
  | consI hb hc hbl hd ih =>
    intro P f hA
    exact uokc_consEA env (fun h => (uokc_indDA env (uokcU hok env hb) (uokcU hok env hc) hbl h rfl).1)
      (fun h _ => bondOKC_indA hok env hb hc hbl h rfl) (fun h => ⟨(ih h).1, fun _ => (ih h).2⟩)
      (by simp only [hinted, fragE_hinted env.cod hd]; rfl) hA rfl

theorem uokc_of_fragUE {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {nm : Nomm}
    (hf : FragUE S nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    UOKC (S := S) (Map := Map) lib env P f nm := by
  rcases hf with h | h
  · exact uokcU hok env h hA
  · exact (uokc_entNew_of_fragE hok env h hA).1

/-- **The contract on `FragUE`** (`finishLUC_contractG`). -/
theorem finishLUC_contractUE {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm) (hf : FragUE S nm)
    (hcount : sixCount nm ≤ 255) {env : CallEnv} {cd : Straight Map} (h : finishLUC (S := S) env nm = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractG lib (uokc_of_fragUE (Map := Map) hok env hf hA) hcount h N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-- **`[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` end to end** (`%cc2`): calls in
both halves of a cons, the head call under the bond goal of `+past` behind
the tail call, its `+kern` filling the bond block (`mov v7 v2`). -/
theorem consCC_example {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = C (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 3) (slot 2))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) := by
    rw [hfol]
    exact Annot.cons (Annot.indirect Annot.n0 Annot.n0) (Annot.indirect Annot.n0 Annot.n0)
  have hf : FragUE S (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) :=
    Or.inr (FragE.consI (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial)) rfl
      (FragE.d (FragD.ind (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial)) rfl)))
  exact finishLUC_contractUE hok hA hf (by decide) h N

end Comp
end SkaModel
end Formalization
