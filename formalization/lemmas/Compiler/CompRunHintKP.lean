import lemmas.Compiler.CompRunHintKR

/-!
# The kept hints of `+run` as parts (README Gaps 25)

* `cd_steps`: the goals of `q` and of the clue `h` in the kept dynamic case
  meet `GInv`, and the `+copy` meets `CopyH`, from a goal with `GInv` and
  what `q` and `h` return (`GRes`).
* **`partH_n11d_kept`**: `PartH` of `q` and `h`, `SoundAt` of `q` and `+past`
  over the hint give `PartH` of `[11 [tag h] q]` with `tag` `hint-dynamic`.
* `ck_steps`, **`partH_n11s_kept`**: the same for the kept static tag.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ctx : Noun}

theorem cdG4_re (tag : Nat) (body : Noun) (th : Jmp) (g2 : Gen (TreapMap mugF)) :
    (cdG4 tag body th g2).re = g2.re + 1 := by simp [cdG4, cf_emitG_re]
theorem cdG4_bo (tag : Nat) (body : Noun) (th : Jmp) (g2 : Gen (TreapMap mugF)) :
    (cdG4 tag body th g2).bo = g2.bo + 1 := by simp [cdG4, cf_emitG_bo]
theorem cdG4_drop (tag : Nat) (body : Noun) (th : Jmp) (g2 : Gen (TreapMap mugF)) :
    (cdG4 tag body th g2).drop = g2.drop := by simp [cdG4, cf_emitG_drop]

/-- **The steps of the kept dynamic case** from a goal with `GInv`. -/
theorem cd_steps {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)} {snd : Nomm → NeedOrd → Bool}
    {tag : Nat} {h q : Nomm} {body : Noun} {region : List Nat}
    (Qr : ResForR R q region) (Hr : ResForR R h region) {goal : CGoalL CSet}
    {g g1 g2 : Gen (TreapMap mugF)} {nex0 nex1 : NextL CSet} (hi : GInv g goal)
    (e0 : simpleNextL goal g = some (nex0, g1)) (e1 : pastIfL snd nex0 q region g1 = some (nex1, g2)) :
    GInv (cdG4 tag body nex1.th g2) (CGoalL.next nex1.laz (jmp0 g2.bo)) ∧
    ∀ n1 g5 n2 g6, R q (CGoalL.next nex1.laz (jmp0 g2.bo)) region (cdG4 tag body nex1.th g2) = some (n1, g5) →
      lazyBound n1 region g5 = some (n2, g6) →
      GInv (cfEmitG (cdProl tag g2.re body n2.th) g6) (cdGoal g2.re g6.bo) ∧
      ∀ n3 g8, R h (cdGoal g2.re g6.bo) region (cfEmitG (cdProl tag g2.re body n2.th) g6) = some (n3, g8) →
        CopyH g8.re n3.laz n2.laz ∧ LInv g8.re g8.bo n3.laz ∧ LInv g8.re g8.bo n2.laz ∧
        (lregs n3.laz ++ lregs n2.laz).Nodup ∧ g8.drop = false ∧ g.re ≤ g8.re ∧ g.bo ≤ g8.bo ∧
        ∀ r ∈ lregs n3.laz ++ lregs n2.laz, g.re ≤ r ∨ r ∈ gregs goal := by
  obtain ⟨l0, b0, ⟨i0, d0, j0⟩, s0⟩ := simpleNextL_res hi e0
  obtain ⟨r1, b1, d1, i1, j1, m1⟩ := pastIfL_inv i0 j0 e1
  have rr := cdG4_re tag body nex1.th g2
  have bb := cdG4_bo tag body nex1.th g2
  have dd := cdG4_drop tag body nex1.th g2
  have iq : GInv (cdG4 tag body nex1.th g2) (CGoalL.next nex1.laz (jmp0 g2.bo)) :=
    ⟨linv_mono i1 (by omega) (by omega), by rw [dd, d1, d0], jmpIn_jmp0 _ _⟩
  refine ⟨iq, fun n1 g5 n2 g6 e3 e4 => ?_⟩
  obtain ⟨l3, b3, i3, s3⟩ := Qr _ _ _ _ iq e3
  obtain ⟨rfl, r4, b4, d4⟩ := lazyBound_eq e4
  obtain ⟨i3l, d3, -⟩ := i3
  obtain ⟨L4, M4⟩ := linv_bound i3l
  have ih : GInv (cfEmitG (cdProl tag g2.re body (jmp0 g5.bo)) g6) (cdGoal g2.re g6.bo) :=
    ginv_reg _ (by rw [cf_emitG_re]; omega) (by rw [cf_emitG_drop, d4, d3])
  refine ⟨ih, fun n3 g8 e5 => ?_⟩
  obtain ⟨l5, b5, ⟨i5, d5, -⟩, s5⟩ := Hr _ _ _ _ ih e5
  rw [cf_emitG_re] at l5
  rw [cf_emitG_bo] at b5
  simp only at M4 L4 ⊢
  have hn2 : ∀ r ∈ lregs n1.laz, r < g5.re := lnb_regs i3l.1
  have hn2' : ∀ r ∈ lregs n1.laz, g2.re + 1 ≤ r ∨ r < g2.re := fun r hr => by
    rcases s3 r hr with e | e
    · left; rw [rr] at e; exact e
    · right; simp only [gregs] at e; exact lnb_regs i1.1 r e
  have hn3 : ∀ r ∈ lregs n3.laz, g6.re ≤ r ∨ r = g2.re := fun r hr => by
    rcases s5 r hr with e | e
    · left; rw [cf_emitG_re] at e; exact e
    · right; simpa [gregs, cdGoal, lregs_reg] using e
  have apart : ∀ r ∈ lregs n3.laz, r ∉ lregs n1.laz := fun r h3 h2 => by
    have := hn2 r h2
    rcases hn3 r h3 with e | e
    · omega
    · subst e; rcases hn2' _ h2 with e' | e' <;> omega
  refine ⟨copyH_of_regs (lnb_regs i5.1) (fun r hr => by rw [M4] at hr; have := hn2 r hr; omega)
      (fun r hr hr' => apart r hr (M4 ▸ hr')), i5, linv_mono L4 (by omega) (by omega),
    ?_, d5, by omega, by omega, fun r hr => ?_⟩
  · rw [List.nodup_append, M4]
    exact ⟨i5.2.1, M4 ▸ L4.2.1, fun a ha b hb e => apart a ha (e ▸ hb)⟩
  · rcases List.mem_append.1 hr with hr | hr
    · rcases hn3 r hr with e | e
      · left; omega
      · left; omega
    · rw [M4] at hr
      rcases hn2' r hr with e | e
      · left; omega
      · rcases s3 r hr with e' | e'
        · left; omega
        · simp only [gregs] at e'
          rcases s0 r ((m1 r).1 e') with e'' | e''
          · left; exact e''
          · right; exact e''

/-- **The kept dynamic tag as a part**: `PartH` of `q` and of the clue `h`,
`SoundAt` of `q` and `+past` over the hint give `PartH` of `[11 [tag h] q]`
(`tag` `hint-dynamic`: `%spot`, `%slog`, `%hunk`, ...). -/
theorem partH_n11d_kept (h7 : slot? 7 ctx = some compK) {env : CallEnv} {snd : Nomm → NeedOrd → Bool}
    {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {tag : Nat} (hdy : hintDynamic tag = true)
    {h q : Nomm} (body : Noun) {region : List Nat} (Q : PartH env snd msup ctx X q region)
    (H : PartH env snd msup ctx X h region) (hs : SoundAt ctx snd q)
    (hpa : PastAt ctx env.cod (Nomm.n11d tag h q body)) :
    PartH env snd msup ctx X (Nomm.n11d tag h q body) region := by
  refine ⟨fun goal g hi => ?_, fun goal g g' nex hi he => ?_, hpa⟩
  · refine comp_run_n11d_kept h7 env snd msup hdy h q body goal region g hs (fun nex0 g1 nex1 g2 e0 e1 => ?_)
    obtain ⟨iq, K⟩ := cd_steps Q.res H.res hi e0 e1
    exact ⟨Q.link _ _ iq, fun n1 g5 n2 g6 e3 e4 => H.link _ _ (K n1 g5 n2 g6 e3 e4).1,
      fun n1 g5 n2 g6 n3 g8 e3 e4 e5 => ((K n1 g5 n2 g6 e3 e4).2 n3 g8 e5).1⟩
  · rw [runLCH_n11d_kept env snd msup hdy] at he
    obtain ⟨nex0, g1, e0, he⟩ := bind_some he
    simp only [cdFrom] at he
    obtain ⟨nex1, g2, e1, he⟩ := bind_some he
    obtain ⟨toke, g3, e2, he⟩ := bind_some he
    rw [re_apply] at e2
    simp only [Option.some.injEq, Prod.mk.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    obtain ⟨epil, g4, e3, he⟩ := bind_some he
    rw [cf_emit_g] at e3
    simp only [Option.some.injEq, Prod.mk.injEq] at e3
    obtain ⟨rfl, rfl⟩ := e3
    simp only [cdTail4] at he
    obtain ⟨n1, g5, e4, he⟩ := bind_some he
    obtain ⟨n2, g6, e5, he⟩ := bind_some he
    obtain ⟨prol, g7, e6, he⟩ := bind_some he
    rw [cf_emit_g] at e6
    simp only [Option.some.injEq, Prod.mk.injEq] at e6
    obtain ⟨rfl, rfl⟩ := e6
    simp only [cdTail7] at he
    obtain ⟨n3, g8, e7, e8⟩ := bind_some he
    obtain ⟨-, K⟩ := cd_steps (tag := tag) (body := body) Q.res H.res hi e0 e1
    have K2 := (K n1 g5 n2 g6 e4 e5).2 n3 g8 e7
    obtain ⟨-, i3, i2, nd, d8, l8, b8, rg⟩ := K2
    obtain ⟨l, b, gi, rs⟩ := copyL_inv i3 i2 nd d8 e8
    exact ⟨by omega, by omega, gi, fun r hr => by
      rcases rs r hr with e | e
      · exact rg r e
      · left; omega⟩

/-- **The steps of the kept static case** from a goal with `GInv`. -/
theorem ck_steps {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)} {snd : Nomm → NeedOrd → Bool}
    {tag : Nat} {q : Nomm} {body : Noun} {region : List Nat}
    (Qr : ResForR R q region) {goal : CGoalL CSet}
    {g g1 g2 : Gen (TreapMap mugF)} {nex0 nex1 : NextL CSet} (hi : GInv g goal)
    (e0 : simpleNextL goal g = some (nex0, g1)) (e1 : pastIfL snd nex0 q region g1 = some (nex1, g2)) :
    GInv (cfEmitG (ckEpil tag body nex1.th) g2) (CGoalL.next nex1.laz (jmp0 g2.bo)) ∧
    ∀ n1 g4 n2 g5, R q (CGoalL.next nex1.laz (jmp0 g2.bo)) region (cfEmitG (ckEpil tag body nex1.th) g2)
        = some (n1, g4) → lazyBound n1 region g4 = some (n2, g5) →
      GRes g goal (cfEmitG ⟨[], [Pole.hsp tag body], Termin.hop n2.th⟩ g5) ⟨n2.laz, jmp0 g5.bo⟩ := by
  obtain ⟨l0, b0, ⟨i0, d0, j0⟩, s0⟩ := simpleNextL_res hi e0
  obtain ⟨r1, b1, d1, i1, j1, m1⟩ := pastIfL_inv i0 j0 e1
  have iq : GInv (cfEmitG (ckEpil tag body nex1.th) g2) (CGoalL.next nex1.laz (jmp0 g2.bo)) :=
    ⟨linv_mono i1 (by rw [cf_emitG_re]; exact Nat.le_refl _) (by rw [cf_emitG_bo]; omega), by rw [cf_emitG_drop, d1, d0], jmpIn_jmp0 _ _⟩
  refine ⟨iq, fun n1 g4 n2 g5 e3 e4 => ?_⟩
  obtain ⟨l3, b3, i3, s3⟩ := Qr _ _ _ _ iq e3
  obtain ⟨rfl, r4, b4, d4⟩ := lazyBound_eq e4
  obtain ⟨i3l, d3, -⟩ := i3
  obtain ⟨L4, M4⟩ := linv_bound i3l
  rw [cf_emitG_re] at l3
  rw [cf_emitG_bo] at b3
  refine ⟨by rw [cf_emitG_re]; omega, by rw [cf_emitG_bo]; omega,
    ⟨linv_mono L4 (by rw [cf_emitG_re]; omega) (by rw [cf_emitG_bo]; omega), by rw [cf_emitG_drop, d4, d3],
      jmpIn_jmp0 _ _⟩, fun r hr => ?_⟩
  simp only at hr
  rw [M4] at hr
  rcases s3 r hr with e | e
  · left; rw [cf_emitG_re] at e; omega
  · simp only [gregs] at e
    rcases s0 r ((m1 r).1 e) with e' | e'
    · left; exact e'
    · right; exact e'

/-- **The kept static tag as a part** (`%bout`, `%xray`). -/
theorem partH_n11s_kept (h7 : slot? 7 ctx = some compK) {env : CallEnv} {snd : Nomm → NeedOrd → Bool}
    {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {tag : Nat} (hst : hintStatic tag = true)
    {q : Nomm} (body : Noun) {region : List Nat} (Q : PartH env snd msup ctx X q region)
    (hs : SoundAt ctx snd q) (hpa : PastAt ctx env.cod (Nomm.n11s tag q body)) :
    PartH env snd msup ctx X (Nomm.n11s tag q body) region := by
  refine ⟨fun goal g hi => ?_, fun goal g g' nex hi he => ?_, hpa⟩
  · exact comp_run_n11s_kept h7 env snd msup hst q body goal region g hs (fun nex0 g1 nex1 g2 e0 e1 =>
      Q.link _ _ (ck_steps (tag := tag) (body := body) Q.res hi e0 e1).1)
  · rw [runLCH_n11s_kept env snd msup hst] at he
    obtain ⟨nex0, g1, e0, he⟩ := bind_some he
    simp only [ckFrom] at he
    obtain ⟨nex1, g2, e1, he⟩ := bind_some he
    obtain ⟨epil, g3, e3, he⟩ := bind_some he
    rw [cf_emit_g] at e3
    simp only [Option.some.injEq, Prod.mk.injEq] at e3
    obtain ⟨rfl, rfl⟩ := e3
    simp only [ckTail] at he
    obtain ⟨n1, g4, e4, he⟩ := bind_some he
    obtain ⟨n2, g5, e5, he⟩ := bind_some he
    obtain ⟨prol, g6, e6, he⟩ := bind_some he
    rw [cf_emit_g] at e6
    simp only [Option.some.injEq, Prod.mk.injEq] at e6
    obtain ⟨rfl, rfl⟩ := e6
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact (ck_steps (tag := tag) (body := body) Q.res hi e0 e1).2 n1 g4 n2 g5 e4 e5

end Compiler
end Formalization
