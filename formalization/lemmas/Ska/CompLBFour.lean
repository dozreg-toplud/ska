import lemmas.Ska.CompLBDone

/-!
# `[4 p]` under any lazy goal with bodies, reading the goal's register

README Gaps 12.23, finding 3 of `CompNC.lean`.  Under a lazy goal whose sure
part is one register `d` (`this d`), `+collapse-lazy-atom` takes `d` itself
and the ops it puts in front of the goal entries' blocks read `d` (through a
proxy): `%s4t`, `8: inc v7 v4`, `3: mov v6 v2` with `v6` a proxy of the
goal's `v4`.  `RunOKLC` is false there (`dreg`: the witness is not
allocated in the run); `RunOKLB` with `x = true` holds: the fronts read `d`
as the goal's sure register, which holds the product (`FrontLB` with `E` the
goal's sure need).  When `d` is fresh (the goal's sure part asks nothing or a
cell) the old relation holds (`runOKL_n4`).  `CollRunU` (`collRun_n4`)
already allows bodies at the goal entries, so no simulation is needed.

* `holdsN_atom_mem`: a need holding an atom names only one register, the
  whole.
* `runOKLB_n4`: `CollRunU` of `[4 p]` gives `RunOKLB` with `x = true`, for
  every register `d` it takes.
* `lokb_n4X`: `[4 p]` with `p` in `FragX` meets `LOKB true`, every lazy
  goal, bodies at the entries.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A need holding an atom is `this` of its one register.** -/
theorem holdsN_atom_mem : ∀ {ned : Need} {R : Map (Option Noun)} {m d : Nat},
    HoldsN ned R (A m) → NMem ned d → SkaModel.read d R = some (A m)
  | Need.none, _, _, _, _, hd => hd.elim
  | Need.this r, _, _, d, h, hd => by
    have e : d = r := hd
    subst e; exact h
  | Need.pair _ _, _, _, _, h, _ => h.elim
  | Need.both _ _ _, _, _, _, h, _ => h.elim

/-- **`[4 p]` from `CollRunU`, any register `d`**: `RunOKLB` with
`x = true` (the fronts may read the goal's register `d`). -/
theorem runOKLB_n4 {lib : Lib} {P : Noun → Prop} {f : Noun} {p : Nomm} (M : MinkEq lib P f (Nomm.n4 p))
    {L : Lazy S} {th : Jmp} {d : Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (CR : CollRunU (Map := Map) lib (Nomm.n4 p) L th d g0 g1 nex)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re) (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hec : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) :
    ∃ Q, RunOKLB (Map := Map) lib P f L th Q true g0 g1 nex := by
  by_cases hdf : g0.re ≤ d
  · exact ⟨_, ((runOKL_n4 CR hdf hlab hec).toLC M).toB.up hL true⟩
  have hd : NMem L.sure.ned d := CR.dreg.resolve_right hdf
  have Cre := CR.re
  have Cdl := CR.dlt
  have dlt : d < g0.re := hL d hd
  -- the products are atoms
  have atom : ∀ s v, pureEval (Nomm.n4 p) s = some v → ∃ m, v = A m := fun s v hev => by
    rw [pureEval_n4] at hev
    cases ep : pureEval p s with
    | none => rw [ep] at hev; cases hev
    | some x =>
      rw [ep] at hev
      cases x with
      | atom n => simp [incF] at hev; exact ⟨n + 1, hev.symm⟩
      | cell _ _ => simp [incF] at hev
  have hl : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 → ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ :=
    fun e he _ => (CR.labs e he).2.2
  refine ⟨fun s v d' w => pureEval (Nomm.n4 p) s = some v ∧ d' = Need.none ∧ w = A 0, ?_⟩
  refine ⟨CR.re, CR.bo, CR.drop, CR.keep, CR.grow, CR.pfor.1, CR.lo, CR.hi, Or.inl CR.ent,
    fun r hr => Or.inr (CR.regs r hr), CR.dist,
    fun e he => ⟨(CR.eregs e he).1, fun r hr => Or.inr (Or.inr ((CR.eregs e he).2 r hr))⟩,
    fun e he => ⟨Or.inr ⟨(CR.labs e he).1, by have := (CR.labs e he).2.1; have := CR.hi; omega⟩, [],
      (CR.labs e he).2.2⟩, CR.nodup,
    fun s v d' w r hq hr => by obtain ⟨_, rfl, _⟩ := hq; exact hr.elim,
    fun s hs hf => necC_of_pure M hs (Or.inl (CR.nec s hf)), CR.ncond, CR.econd, fun e he => ?_, ?_, ?_⟩
  · -- front: the ops read `d`, the goal's register
    obtain ⟨F, hF, hP⟩ := CR.front e he
    refine ⟨F, hF, fun cf hcf => Or.inr ⟨fun hm => ?_, ?_⟩⟩
    · obtain ⟨e', he', e1⟩ := List.mem_map.mp hm
      have := (CR.labs e' he').1; have := hlab e he; omega
    intro lib σ O c gul st t ned A0 s0 s v d' w _ hq hfill
    obtain ⟨hev, rfl, rfl⟩ := hq
    obtain ⟨m, rfl⟩ := atom s v hev
    have FP := collP_fillSem hP ((hcf d Cdl).trans CR.dkey)
      (fun x hx => by
        have hx1 := hec e he x hx
        rw [hcf x (by omega), ProxyFor.get_lt CR.pfor hx1.1]; exact hx1.2)
      (fun k hk => hcf k hk) lib O c gul st t ned g0.re s0 m
    have H := fillSem_bunt_append hfill (fun x hx => by have : x = d := hx; subst this; omega) (by omega) FP
    show FillSem lib O c gul st t (Need.pair (Need.pair ned Need.none) L.sure.ned) g0.re e.2.sure _ _ _
    exact H.conv (N1 := Need.pair (Need.pair ned Need.none) L.sure.ned) (x1 := C (C s0 (A 0)) (A m))
      (fun R hR => ⟨hR.1.1, holdsN_atom_mem hR.2 hd⟩) (fun z hz => by
        rcases hz with (hz | hz) | hz
        · exact Or.inl (Or.inl hz)
        · exact hz.elim
        · exact Or.inr (hL z hz))
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have ag' : AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s :=
      ((ag st).toL hl).toU fun e he => (CR.labs e he).1
    have Sp := CR.sem cf hcf c ned σ O st t gul s0 s ag' (fun r hr => Or.inl (hned r hr)) regs hh hn
    rw [(M s hs gul tm r).mp ⟨n, hm⟩]
    exact goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩)
      (goalSem_toGoalSemD lib O c gul st (GoalSem.mono (fun x hx => by
        rcases hx with ⟨h | h, h'⟩
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h) Sp))
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have ag' : AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s :=
      ((ag st).toL hl).toU fun e he => (CR.labs e he).1
    have Sp := CR.sem cf hcf c ned σ O st t gul s0 s ag' (fun r hr => Or.inl (hned r hr)) regs hh hn
    exact ⟨_, (M s hs gul tm _).mpr rfl, goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩)
      (goalSem_toGoalSemD lib O c gul st (GoalSem.mono (fun x hx => by
        rcases hx with ⟨h | h, h'⟩
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h) Sp))⟩

/-- **`[4 p]` with `p` in `FragX` meets `LOKB true`**: every lazy goal, bodies
at the entries, the fronts reading the goal's register when
`+collapse-lazy-atom` takes it (`collRun_n4`, `runOKLB_n4`);
its jump is at none of its entries (they are all new and below it). -/
theorem lokb_n4X (lib : Lib) (env : CallEnv) {p : Nomm} (hp : FragX (S := S) p) {P : Noun → Prop} {f : Noun}
    (M : MinkEq lib P f (Nomm.n4 p)) : LOKB (S := S) (Map := Map) true lib env P f (Nomm.n4 p) := by
  have pp : (Nomm.n4 p).pure = true := by simpa [Nomm.pure] using fragX_pure hp
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g1 nex} hc b0 d0 hu hcl hcb h1 h2
    ha ht hsd hsl hlab hnd hed h => ?_⟩
  · rw [runLC_eq env _ (Nomm.noCall_of_pure _ pp)] at h
    exact clean_n4L (runX_clean hp) h
  · rw [runLC_eq env _ (Nomm.noCall_of_pure _ pp)] at h
    obtain ⟨d, CR⟩ := collRun_n4 lib (runX_ok lib hp).2.1 (runX_semR lib hp).2.1 (runX_keeps hp)
      (aboveX_of_fragX hp) h (by simpa [sixCount] using hc) b0 d0 hu hcl h1 h2 (fun x hx => (hsl x hx).1)
      (fun x hx => (hsl x hx).2) hcb (List.nodup_cons.mpr ⟨ht, hnd⟩)
      (fun e he => ⟨(hlab e he).1, by obtain ⟨B, th', hb⟩ := (hlab e he).2; exact ⟨B, _, hb⟩⟩)
      (fun e he x hx => ((hed e he).2 x hx).1)
    refine ⟨runOKLB_n4 M CR (fun r hr => (hsl r hr).1) (fun e he => (hlab e he).1) (fun e he => (hed e he).2),
      fun hm => ?_⟩
    obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (CR.labs e he).2.1
    omega

end Comp
end SkaModel
end Formalization
