import lemmas.Compiler.CompRunHintSixAll

/-!
# The hint cases of `+run`: the dropped dynamic tag (README Gaps 25)

`[11 [tag h] q]` with `tag` not `hint-dynamic` (`%memo` with an unsafe clue,
`%fast`, an unknown tag): `q` under the goal; if `+safe-nomm h`, that is all;
else `+past` of it over `h`, `h` under `[%next *need-lazy then]`, `+copy`.
The branch `cr11NDyn` of `crK11` is written out as `cr11Nd`
(`tools/gen/runhint.py`).

* `cr11_nd`: `crK11` on a cell tag that is not `hint-dynamic` is `cr11Nd`.
* **`comp_run_n11d_nd`**: the case on every goal against any model `R` that
  runs it as above, from the links of `q` and `h` (`CompRunAtX`), `+past`
  over `h` (`PastAt`) and the `CopyH` of the `+copy`.
* `runLCH_n11d_nd`: `runLCH` runs it so.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ctx : Noun}

def cr11Nd : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 58) (C (A 0) (A 470))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 5494) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2005))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 2)) (C (A 0) (A 126))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 2005)) (C (A 0) (A 1006))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 2005))) (C (A 0) (A 7)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))

theorem cr11nd_eq : cr11NDyn = cr11Nd := by kernel_rfl

/-- A cell tag whose tag is not `hint-dynamic`: `crK11` is `cr11Nd`. -/
theorem cr11_nd {tag : Nat} (hd : hintDynamic tag = false) (h q : Noun) (mono body goal region sup D : Noun) :
    nock (crSubj mono (C (A 11) (C (C (A tag) h) (C q body))) goal region sup D) crK11
      = nock (crSubj mono (C (A 11) (C (C (A tag) h) (C q body))) goal region sup D) cr11Nd := by
  have h1 : tag ≠ 0x74756f62 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h2 : tag ≠ 0x79617278 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h3 : tag ≠ 0x6e697073 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h4 : tag ≠ 0x786e696a := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h5 : tag ≠ 0x6576696c := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h6 : tag ≠ 0x6b6e7568 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h7 : tag ≠ 0x646e6168 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h8 : tag ≠ 0x65736f6c := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h9 : tag ≠ 0x6e61656d := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h10 : tag ≠ 0x746f7073 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  have h11 : tag ≠ 0x676f6c73 := by intro e; subst e; simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, HintTag.slog] at hd
  rw [cr11_eq, ← cr11nd_eq]
  unfold cr11Head cr11Dy cr11T cr11TD
  simp [nock_exec, crSubj, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, Ne.symm h1, Ne.symm h2, Ne.symm h3,
    Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11]

/-- `runLCH` on a cell tag that is not `hint-dynamic`. -/
theorem runLCH_n11d_nd (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (mono : Bool) {tag : Nat}
    (hd : hintDynamic tag = false) (sup : Option Nomm) (h q : Nomm) (body : Noun) (goal : CGoalL CSet)
    (region : List Nat) :
    (runLCH env snd mono sup (Nomm.n11d tag h q body) goal region : CM (TreapMap mugF) (NextL CSet)) =
      (do
        let nexFol ← runLCH env snd mono sup q goal region
        if safeNomm h then pure nexFol else do
        let nexFol ← pastL env.cod nexFol h region
        let nexToke ← runLCH env snd mono sup h (CGoalL.next (Lazy.ofSure Sure.bunt) nexFol.th) region
        copyL nexToke nexFol.laz) := by
  simp only [runLCH, hd, Bool.not_false, if_true]

/-- **The dropped dynamic tag on every goal**, against any model that runs
it as `runLCH` does. -/
theorem comp_run_n11d_nd (h7 : slot? 7 ctx = some compK)
    {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {cod : Bell → Option Bool} {tag : Nat}
    (hdy : hintDynamic tag = false) (h q : Nomm) (body : Noun) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF))
    (hR : R (Nomm.n11d tag h q body) goal region g = (do
        let nexFol ← R q goal region
        if safeNomm h then pure nexFol else do
        let nexFol ← pastL cod nexFol h region
        let nexToke ← R h (CGoalL.next (Lazy.ofSure Sure.bunt) nexFol.th) region
        copyL nexToke nexFol.laz : CM (TreapMap mugF) (NextL CSet)) g)
    (hq : CompRunAtX R ctx X q goal region g) (hpa : PastAt ctx cod h)
    (hh : ∀ n1 g1 n2 g2, R q goal region g = some (n1, g1) → pastL cod n1 h region g1 = some (n2, g2) →
      CompRunAtX R ctx X h (CGoalL.next (Lazy.ofSure Sure.bunt) n2.th) region g2)
    (hcp : ∀ n1 g1 n2 g2 n3 g3, R q goal region g = some (n1, g1) → pastL cod n1 h region g1 = some (n2, g2) →
      R h (CGoalL.next (Lazy.ofSure Sure.bunt) n2.th) region g2 = some (n3, g3) → CopyH g3.re n3.laz n2.laz) :
    CompRunAtX R ctx X (Nomm.n11d tag h q body) goal region g := by
  intro x mono sup hx hX
  rw [hR]
  simp only [Nomm.toNoun]
  rw [cr_disp_n11, cr11_nd hdy]
  have hq1 := hq x mono sup hx hX
  simp only [crSubj, compCore] at hq1
  have h63 := crd_ctx63 h7
  have hsa := safe_nomm.arm_at
  have hsf := safe_nomm_pill h
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases e1 : R q goal region g with
  | none =>
    rw [e1] at hq1
    generalize comp.door = Dr at hq1 hD1 hD2 ⊢
    unfold cr11Nd
    simp [nock_exec, crSubj, cr_bat_dol, bind, StateT.bind, hq1, e1]
  | some r1 =>
    obtain ⟨n1, g1⟩ := r1
    rw [e1] at hq1
    simp only [Option.map_some] at hq1
    cases hs : safeNomm h with
    | true =>
      generalize comp.door = Dr at hq1 hD1 hD2 ⊢
      unfold cr11Nd
      simp [nock_exec, crSubj, cr_bat_dol, bind, StateT.bind, hq1, e1, h63, hsa, safe_nomm_arm, hsf, hs, loob,
        pure, StateT.pure]
    | false =>
      have hpa1 := hpa x g1 n1 region
      simp only [cr_next_nounL, compCore] at hpa1
      cases e2 : pastL (S := CSet) (Map := TreapMap mugF) cod n1 h region g1 with
      | none =>
        rw [e2] at hpa1
        generalize comp.door = Dr at hq1 hD1 hD2 hpa1 ⊢
        unfold cr11Nd
        simp [nock_exec, crSubj, cr_bat_dol, bind, StateT.bind, hq1, e1, h63, hsa, safe_nomm_arm, hsf, hs, loob,
          h7, hD1, cr_past_arm, hpa1, e2, cr_next_nounL]
      | some r2 =>
        obtain ⟨n2, g2⟩ := r2
        rw [e2] at hpa1
        simp only [Option.map_some, cr_next_nounL] at hpa1
        have hh1 := hh n1 g1 n2 g2 e1 e2 x mono sup hx hX
        simp only [crSubj, compCore, cgl_next_noun, cr_bunt_noun] at hh1
        cases e3 : R h (CGoalL.next (Lazy.ofSure Sure.bunt) n2.th) region g2 with
        | none =>
          rw [e3] at hh1
          generalize comp.door = Dr at hq1 hD1 hD2 hpa1 hh1 ⊢
          unfold cr11Nd
          simp [nock_exec, crSubj, cr_bat_dol, bind, StateT.bind, hq1, e1, h63, hsa, safe_nomm_arm, hsf, hs, loob,
            h7, hD1, cr_past_arm, hpa1, e2, cr_next_nounL, hh1, e3]
        | some r3 =>
          obtain ⟨n3, g3⟩ := r3
          rw [e3] at hh1
          simp only [Option.map_some, cr_next_nounL] at hh1
          have hcpy := comp_copy_all h7 x g3 n3 n2.laz (hcp n1 g1 n2 g2 n3 g3 e1 e2 e3)
          simp only [compCore, cr_next_nounL] at hcpy
          generalize comp.door = Dr at hq1 hD1 hD2 hpa1 hh1 hcpy ⊢
          unfold cr11Nd
          simp [nock_exec, crSubj, cr_bat_dol, bind, StateT.bind, hq1, e1, h63, hsa, safe_nomm_arm, hsf, hs, loob,
            h7, hD1, cr_past_arm, hpa1, e2, cr_next_nounL, hh1, e3, hD2, cr_cp_arm, hcpy]

/-! ## The dropped dynamic tag from `PartH` -/

/-- The run of `q` as a trivial first run of the tail lemmas of
`CompRunRes.lean` (started at the state after `q`). -/
theorem gres_self {g1 : Gen (TreapMap mugF)} {n1 : NextL CSet} (hG : GInv g1 n1.goal) :
    GRes g1 (CGoalL.next n1.laz n1.th) g1 n1 :=
  ⟨Nat.le_refl _, Nat.le_refl _, hG, fun r hr => Or.inr (by simpa [gregs] using hr)⟩

/-- **The dropped dynamic tag as a part**: `PartH` of `q` and of `h` give
`PartH` of `[11 [tag h] q]` (`tag` not `hint-dynamic`). -/
theorem partH_n11d_nd (h7 : slot? 7 ctx = some compK) {env : CallEnv} {snd : Nomm → NeedOrd → Bool}
    {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {tag : Nat} (hdy : hintDynamic tag = false)
    {h q : Nomm} (body : Noun) {region : List Nat} (Q : PartH env snd msup ctx X q region)
    (H : PartH env snd msup ctx X h region) (hpa : PastAt ctx env.cod (Nomm.n11d tag h q body)) :
    PartH env snd msup ctx X (Nomm.n11d tag h q body) region := by
  have hG2 : ∀ goal g n1 g1 n2 g2, GInv g goal →
      runLCH env snd true msup q goal region g = some (n1, g1) → pastL env.cod n1 h region g1 = some (n2, g2) →
      GInv g2 (CGoalL.next (Lazy.ofSure Sure.bunt) n2.th) := by
    intro goal g n1 g1 n2 g2 hi e1 e2
    have hG1 := (Q.res goal g g1 n1 hi e1).2.2.1
    exact (tail_pgoal (p := h) hG1 (linv_bunt g1.re g1.bo) (gres_self hG1) e2).1
  have hap : ∀ (g1 : Gen (TreapMap mugF)) (n1 : NextL CSet), GInv g1 n1.goal →
      (lregs (Lazy.ofSure (Sure.bunt : Sure CSet)) ++ lregs n1.laz).Nodup := by
    intro g1 n1 hG1
    rw [lregs_bunt, List.nil_append]; exact hG1.1.2.1
  refine ⟨fun goal g hi => ?_, fun goal g g' nex hi he => ?_, hpa⟩
  · refine comp_run_n11d_nd h7 hdy h q body goal region g (by rw [runLCH_n11d_nd env snd true hdy])
      (Q.link goal g hi) H.past (fun n1 g1 n2 g2 e1 e2 => H.link _ g2 (hG2 goal g n1 g1 n2 g2 hi e1 e2))
      (fun n1 g1 n2 g2 n3 g3 e1 e2 e3 => ?_)
    have hG1 := (Q.res goal g g1 n1 hi e1).2.2.1
    exact (tail_copyH (p := h) hG1 (linv_bunt g1.re g1.bo) (hap g1 n1 hG1) (gres_self hG1) e2
      (H.res _ g2 g3 n3 (hG2 goal g n1 g1 n2 g2 hi e1 e2) e3)).1
  · rw [runLCH_n11d_nd env snd true hdy] at he
    obtain ⟨n1, g1, e1, he⟩ := bind_some he
    have R0 := Q.res goal g g1 n1 hi e1
    cases hs : safeNomm h with
    | true =>
      simp only [hs, if_true, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact R0
    | false =>
      simp only [hs, Bool.false_eq_true, if_false] at he
      obtain ⟨n2, g2, e2, he⟩ := bind_some he
      obtain ⟨n3, g3, e3, e4⟩ := bind_some he
      have hG1 := R0.2.2.1
      have R1 := H.res _ g2 g3 n3 (hG2 goal g n1 g1 n2 g2 hi e1 e2) e3
      obtain ⟨l, b, gi, rg⟩ := tail_res (p := h) hG1 (linv_bunt g1.re g1.bo) (hap g1 n1 hG1) (gres_self hG1) e2 R1 e4
      refine ⟨Nat.le_trans R0.1 l, Nat.le_trans R0.2.1 b, gi, fun r hr => ?_⟩
      rcases rg r hr with e | e
      · rw [lregs_bunt, List.nil_append] at e
        exact R0.2.2.2 r e
      · exact Or.inl (Nat.le_trans R0.1 e)

end Compiler
end Formalization
