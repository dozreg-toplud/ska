import lemmas.Compiler.CompSixHelp

/-!
# The case `%6` of `+run`: the tail of phase S

Phase S of the case `%6` (`cr6S0` ... `cr6S9`, `CompRunSixN.lean`) ends,
after the run of the test `p`, with the test `(lazy-big (soft-less lazy))`
(`cr6S9`): on `|` the `+copy` of `nex-cond` and `lazy`, on `&` the `+emit` of
`[~ ~ %hop then.nex-cond]` as `o`, `+lazy-shut` at `o` and the `+copy` of
`nex-cond(then ~^o)`.  The model is the end of `sixNextSimpleC` and of the
`%done`, `%pick` branch of `runLC` (`sixTail`).

`cr6s_tail`: the Nock of `cr6S9` on its subject is `sixTail`, given that the
registers of `nex-cond` and of `lazy` are below the counter and apart (the
side condition of `+copy`) and that no sure need of `lazy` looks at axis `0`
(the walk of `+kern` in `+lazy-shut`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The tail of phase S in the model. -/
noncomputable def sixTail (nexCond : NextL CSet) (lazy : Lazy CSet) : CM (TreapMap mugF) (NextL CSet) :=
  if !(Lazy.lazyBig (Lazy.softLess Lazy.noSoft lazy)) then copyL nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyL ⟨nexCond.laz, jmp0 o⟩ lazy

theorem km_kernG (r o oLaz : Nat) (sur : Sure CSet) : KM (kernG r o oLaz sur) := by
  unfold kernG
  refine KM.bind' (km_sureRequireLook _) fun ned => KM.ite' _ (KM.pure' _) ?_
  refine KM.bind' (KM.ite' _ (KM.pure' _) (KM.proxy' _ _)) fun src => KM.ite' _ KM.fail ?_
  exact KM.bind' (km_kernLoop _ _ _) fun _ => KM.addOps' _ _

theorem get_apply' (g : Gen (TreapMap mugF)) : (get : CM (TreapMap mugF) (Gen (TreapMap mugF))) g = some (g, g) := rfl

/-- `+kern` takes the counter as its register and moves the counter past it. -/
theorem kern_reg {o : Nat} {laz : Lazy CSet} {g g' : Gen (TreapMap mugF)} {r : Nat}
    (h : kern o laz g = some (r, g')) : r = g.re ∧ g.re < g'.re := by
  rw [kern_eq, bind_apply, re_apply, Option.bind_some, bind_apply, get_apply', Option.bind_some] at h
  by_cases hd : g.drop = true
  · rw [if_pos hd, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  · rw [if_neg hd, bind_apply] at h
    obtain ⟨⟨u, g2⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rw [pure_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have := ((km_walkLazy (fun o' s => km_kernG g.re o o' s) o laz).keep _ u _ h1).1
    exact ⟨rfl, by simp at this; omega⟩

theorem pf_noun (n : NextL CSet) (o : Nat) :
    (⟨n.laz, jmp0 o⟩ : NextL CSet).goal.toNoun = C (A 0x7478656e) (C n.laz.toNoun (C (A 0) (A o))) := by
  simp [NextL.goal, CGoalL.toNoun, Jmp.toNoun, jmp0, listNoun]

/-- **The tail of phase S** (`cr6S9`): the test `(lazy-big (soft-less
lazy))`, then `+copy`, or `+emit`, `+lazy-shut` and `+copy`, on the subject
of phase S after the run of the test, given the side conditions of `+copy`
(the registers of `nex-cond` and `lazy` below the counter and apart) and no
look at axis `0` in `lazy`. -/
theorem cr6s_tail (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF))
    (nexCond : NextL CSet) (lazy : Lazy CSet) (Y V6 V5 V4 V3 V2 V1 V0 B1 B2 SAM : Noun)
    (hf : ∀ r ∈ lregs nexCond.laz, r < g.re) (hs : ∀ r ∈ lregs lazy, r < g.re)
    (ap : ∀ r ∈ lregs nexCond.laz, r ∉ lregs lazy) (hl : LAll CrLok lazy) :
    nock (C nexCond.goal.toNoun (C (C lazy.toNoun Y) (C V6 (C V5 (C V4 (C V3 (C V2 (C V1 (C V0
      (C B1 (C B2 (C SAM (compCore g x ctx))))))))))))) cr6S9
      = (sixTail nexCond lazy g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hsl := sl_all hc x hx g lazy
  have hlg := lg_gate lazy
  have hD1 := sl_at
  have hD2 := comp_cp_at
  have hD3 := comp_emit_at
  have hD4 := lsh_at
  unfold sixTail
  rw [Lazy.softLess_noSoft]
  simp only [compCore] at hsl ⊢
  cases eb : Lazy.lazyBig lazy
  · have hcp := comp_copy_all h7 x g nexCond lazy (copyH_of_regs hf hs ap)
    simp only [compCore] at hcp
    generalize comp.door = Dr at hsl hD1 hD2 hD3 hD4 hcp ⊢
    unfold cr6S9
    simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD2, cr_cp_arm, hcp]
  · have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop nexCond.th⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
    have hre := cf_emitG_re ⟨[], [], Termin.hop nexCond.th⟩ g
    generalize hg1 : cfEmitG ⟨[], [], Termin.hop nexCond.th⟩ g = g1 at he hre
    have hsh := comp_lazy_shut h7 x hx g1 g.bo lazy (walk_mdP hx _ hl)
    simp only [compCore] at hsh
    unfold lazyShut at hsh
    rw [Lazy.softLess_noSoft, eb] at hsh
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at hsh
    cases ek : kern g.bo lazy g1 with
    | none =>
      rw [bind_apply, ek] at hsh
      generalize comp.door = Dr at hsl hD1 hD2 hD3 hD4 he hsh ⊢
      unfold cr6S9
      simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD3, comp_emit_arm, he, hD4,
        lsh_arm, hsh, cf_emit_g, hg1, bind, StateT.bind, lazyShut, Lazy.softLess_noSoft, ek, NextL.goal, CGoalL.toNoun]
    | some rk =>
      obtain ⟨r, g2⟩ := rk
      obtain ⟨er, lr⟩ := kern_reg ek
      rw [bind_apply, ek] at hsh
      simp only [Option.bind_some, pure_apply, Option.map_some] at hsh
      have hcp := comp_copy_all h7 x g2 ⟨nexCond.laz, jmp0 g.bo⟩ (Lazy.ofSure ⟨Need.this r, HoonSet.empty⟩)
        (copyH_of_regs (fun y hy => by have := hf y hy; omega)
          (fun y hy => by
            have e : lregs (Lazy.ofSure (⟨Need.this r, HoonSet.empty⟩ : Sure CSet)) = [r] := lregs_reg r
            rw [e] at hy; simp at hy; omega)
          (fun y hy hy' => by
            have e : lregs (Lazy.ofSure (⟨Need.this r, HoonSet.empty⟩ : Sure CSet)) = [r] := lregs_reg r
            rw [e] at hy'; simp at hy'; have := hf y hy; omega))
      simp only [compCore, pf_noun] at hcp
      generalize comp.door = Dr at hsl hD1 hD2 hD3 hD4 he hsh hcp ⊢
      unfold cr6S9
      simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD3, comp_emit_arm, he, hD4,
        lsh_arm, hsh, cf_emit_g, hg1, bind, StateT.bind, lazyShut, Lazy.softLess_noSoft, ek, hD2, cr_cp_arm, hcp,
        NextL.goal, CGoalL.toNoun, pure, StateT.pure]

end Compiler
end Formalization
