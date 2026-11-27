import lemmas.Ska.CompHintTop
import lemmas.Ska.CompDirectMTree

/-!
# `LOKSH`: the class relation of the run with hints (README Gaps 24.12)

`LOKSH snd x` is `LOKSM x` (`CompDirectMCal.lean`) for the run with hints
`runLCH env snd true` in place of `runLCM env true`.  The copies of the
constructors for it are generated (`tools/gen/lokh.py`,
`CompHintLS.lean`, `CompHintLSCons.lean`); the bridges from the old
relations on nomms without hints are in `CompHintLSBridge.lean`.

* `LOKSH`, `LOKSM.toH` (`runLCH_eq`).
* `RunOKLB.minkAs`, `RunOKLS.minkAs`: the relation of a run for `f` holds
  for a formula `+mink` runs as `f` (`MinkAs`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`LOKSM` for the run with hints** (`runLCH env snd true`). -/
structure LOKSH (snd : Nomm → NeedOrd → Bool) (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop)
    (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLCH env snd true sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    Flat L → Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) →
    runLCH env snd true sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ Flat nex.laz ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)

/-- **`LOKSM` of a nomm without hints is `LOKSH`** (`runLCH_eq`). -/
theorem LOKSM.toH {snd : Nomm → NeedOrd → Bool} {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv}
    {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSM (S := S) (Map := Map) x lib N env P f nm) (hh : nm.noHint = true) :
    LOKSH (S := S) (Map := Map) snd x lib N env P f nm :=
  ⟨fun hc hr => H.clean hc (by rwa [runLCH_eq env snd true nm hh] at hr),
   fun hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    H.run hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce
      (by rwa [runLCH_eq env snd true nm hh] at hr)⟩

/-- **`RunOKLB` for `f` holds for a formula `+mink` runs as `f`.** -/
theorem RunOKLB.minkAs {lib : Lib} {N : Needs} {P : Noun → Prop} {f f' : Noun} {L : Lazy S} {th : Jmp} {Q : Wit}
    {x : Bool} {g0 g1 : Gen Map} {nex : NextL S} (M : MinkAs lib f' f)
    (R : RunOKLB (Map := Map) lib N P f L th Q x g0 g1 nex) : RunOKLB (Map := Map) lib N P f' L th Q x g0 g1 nex where
  re := R.re
  bo := R.bo
  drop := R.drop
  keep := R.keep
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
  dreg := R.dreg
  nec := fun s hs hfit => by
    obtain ⟨h1, h2⟩ := R.nec s hs hfit
    refine ⟨fun gul n tm r h => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', -, h'⟩ := M.fwd h
      exact h1 gul n' tm r h'
    · obtain ⟨r, hm, hb⟩ := h2 gul tm
      exact ⟨r, M.bwd hm, hb⟩
  ncond := R.ncond
  econd := R.econd
  front := R.front
  sem := fun cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI ht hP hm => by
    obtain ⟨n', hn, h'⟩ := M.fwd hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn) st t tm s0 s r hI ht hP h'
  semB := fun cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg => by
    obtain ⟨r, hm, hg'⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg
    exact ⟨r, M.bwd hm, hg'⟩

/-- **`RunOKLS` for `f` holds for a formula `+mink` runs as `f`.** -/
theorem RunOKLS.minkAs {lib : Lib} {N : Needs} {P : Noun → Prop} {f f' : Noun} {L : Lazy S} {th : Jmp} {Q : Wit}
    {x : Bool} {g0 g1 : Gen Map} {nex : NextL S} (M : MinkAs lib f' f)
    (R : RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex) : RunOKLS (Map := Map) lib N P f' L th Q x g0 g1 nex :=
  { R.toRunOKLB.minkAs M with fs := R.fs }

end Comp
end SkaModel
end Formalization
