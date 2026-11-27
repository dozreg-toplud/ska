import lemmas.Compiler.SkaPoke
import lemmas.Compiler.MockPill

/-!
# `road-pure`, `+mule:vi` and `+mute`

`+ska-poke` is `%-  road-pure  |.`, and `road-pure` (the gate at axis `62`
of `ana`) is

```hoon
=/  road-pure
  |*  =(trap *)
  ^+  $:trap
  =/  res  (~(mule vi |) trap)
  ?-  -.res
    %&  p.res
    %|  (mean p.res)
  ==
```

`+mule:vi` runs `+mute` and, on `%&`, runs the trap a second time directly
(`[%& p=$:tap]`); `+mute` runs `(mock [tap %9 2 %0 1] gul)` with `gul = ~`,
since `for` is `|`; `+mock` is `+mook` of `+mink`, and `+mean` never returns.
The Nock, read off the pill (`rpBat`, `rpMuleBat`, `rpMuteBat`,
`rpMeanArm` written out; the door `+vi` at arm `22526` of `layer4`, its arms
`+mule` at `6` and `+mute` at `15` of its battery; `+mean` at arm `2558` of
the core at axis `31` of the gate's context, the fifth layer of `hoon.hoon`):

* `rpBat`: `[8 [8 [8 [9 22526 0 255] 9 10 10 [6 7 [0 3] 1 1] 0 2] 9 2 10 [6 0 14] 0 2]
  6 [5 [1 0] 0 4] [0 5] 11 [%toss 5 [1 1] 0 4] 8 [9 2558 0 255] 9 2 10 [6 0 13] 0 2]`;
* `rpMuleBat`: `[8 [8 [9 23 0 7] 9 2 10 [6 0 14] 0 2]
  6 [5 [1 0] 0 4] [[1 0] 7 [0 14] 9 2 0 1] 11 [%toss 5 [1 1] 0 4] [1 1] 0 5]`;
* `rpMuteBat`: `[8 [6 [0 30] gul-gate 1 0] 8 [8 [9 1406 0 63] 9 2 10 [6 [7 [0 3] [0 14] 1 9 2 0 1] 0 6] 0 2]
  6 [5 [1 0] 0 4] [[1 0] 0 5] 6 [5 [1 1] 0 4] one 11 [%toss 5 [1 2] 0 4] [1 1] 0 5]`,
  `one` being `[8 sof [1 1] rest]` (the `%1` branch, `(soft path)` and `+smyt`);
* `rpMeanBat`: `[6 [5 [1 0] 0 6] [0 0] 11 [%mean [1 0 28] 0 1] 9 2 10 [6 0 13] 0 1]`.

So `road-pure` returns `y` exactly when `+mink` of the trap with `gul = ~`
ends in `%0` and the direct run returns `y` (`rp_run_iff`), and the gate
`+ska-poke` likewise (`ska_poke_gate_iff`).  `+mink` with `gul = ~` returns
`[%0 p]` exactly when `EvalH` (Nock, with opcode 9 stated by its arm and the
dynamic hint in two rules) gives `p` (`evalH_of_mink_nil`, with
`mink_of_evalH`), so the gate returns `y` exactly when the trap's run is an
`EvalH` run to `y` (`ska_poke_iff_evalH`).  `nock` is `Eval`, and `Eval` is
`EvalH`, so every return of the trap is such a run (`sp_trap_evalH`), and
the gate returns `y` exactly when the trap does, with no hypothesis
(`ska_poke_iff`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

set_option linter.unusedSimpArgs false

/-! ## The nouns -/

/-- `[9 2 0 1]`, the kick of a trap. -/
def rpK : Noun := C (A 9) (C (A 2) (C (A 0) (A 1)))

/-- The first half of `road-pure`: `(~(mule vi |) trap)`. -/
def rpMuleCall : Noun :=
  let vi := C (A 8) (C (C (A 9) (C (A 22526) (C (A 0) (A 255))))
    (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 1))))) (C (A 0) (A 2)))))))
  C (A 8) (C vi (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))

/-- The second half of `road-pure`: `?-  -.res  %&  p.res  %|  (mean p.res)  ==`. -/
def rpRest : Noun :=
  let mean := C (A 8) (C (C (A 9) (C (A 2558) (C (A 0) (A 255))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2)))))))
  let toss := C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 4))))) mean)
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 0) (A 5)) toss))

/-- The battery of `road-pure`. -/
def rpBat : Noun := C (A 8) (C rpMuleCall rpRest)

/-- The sample bunt of `road-pure`, kept whole. -/
noncomputable def rpSam : Noun := (slot? 250 ana).getD (A 0)

/-- The context of `road-pure`, kept whole. -/
noncomputable def rpCtx : Noun := (slot? 251 ana).getD (A 0)

theorem rp_at : slot? 62 ana = some (C rpBat (C rpSam rpCtx)) := by kernel_rfl

/-- The fifth layer of `hoon.hoon`, kept whole. -/
noncomputable def rpL5 : Noun := (slot? 31 rpCtx).getD (A 0)

theorem rp_l5 : slot? 31 rpCtx = some rpL5 := by kernel_rfl

theorem rp_l4 : slot? 63 rpCtx = some layer4 := by kernel_rfl

/-- The battery of `+mean`. -/
def rpMeanBat : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 0))
    (C (A 11) (C (C (A 0x6e61656d) (C (C (A 1) (C (A 0) (A 28))) (C (A 0) (A 1))))
      (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1))))))))))

/-- The arm `+mean`: the gate with the sample `~`. -/
def rpMeanArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) rpMeanBat) (C (A 0) (A 1))))

theorem rp_mean_at : slot? 2558 rpL5 = some rpMeanArm := by kernel_rfl

/-- The arm `+vi` of `layer4`, kept whole. -/
noncomputable def rpViArm : Noun := (slot? 22526 layer4).getD (A 0)

/-- The battery of the door `+vi`, kept whole. -/
noncomputable def rpViBat : Noun := (slot? 109 rpViArm).getD (A 0)

/-- The clue of the `%fast` hint of `+vi`, kept whole. -/
noncomputable def rpViClue : Noun := (slot? 123 rpViArm).getD (A 0)

theorem rp_vi_at : slot? 22526 layer4 = some (C (A 7) (C (C (A 8) (C (C (A 1) (A 0))
    (C (C (A 1) rpViBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) rpViClue))
      (C (A 0) (A 1)))))) := by kernel_rfl

/-- The bunt of `(trap)`, the sample of `+mule` and `+mute`, kept whole. -/
noncomputable def rpTapB : Noun := (slot? 125 rpViBat).getD (A 0)

/-- The clue of the `%fast` hint of `+mule`, kept whole. -/
noncomputable def rpMuleClue : Noun := (slot? 443 rpViBat).getD (A 0)

/-- The call of `+mute` in `+mule`. -/
def rpMuteCall : Noun :=
  C (A 8) (C (C (A 9) (C (A 23) (C (A 0) (A 7))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))

/-- The test of `+mule`: `?-  -.mud  %&  [%& p=$:tap]  %|  [%| p=p.mud]  ==`. -/
def rpMuleRest : Noun :=
  let yes := C (C (A 1) (A 0)) (C (A 7) (C (C (A 0) (A 14)) rpK))
  let no := C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 4)))))
    (C (C (A 1) (A 1)) (C (A 0) (A 5))))
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C yes no))

/-- The battery of the gate `+mule`. -/
def rpMuleBat : Noun := C (A 8) (C rpMuteCall rpMuleRest)

/-- The arm `+mule` of the door. -/
noncomputable def rpMuleArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) rpTapB) (C (C (A 1) rpMuleBat) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) rpMuleClue)) (C (A 0) (A 1)))))

theorem rp_mule_at : slot? 6 rpViBat = some rpMuleArm := by kernel_rfl

/-- The gate built by `?.  for  ~  ...` when `for` is `&`, kept whole. -/
noncomputable def rpGulX : Noun := (slot? 8118 rpViBat).getD (A 0)

/-- The `(soft path)` of the `%1` branch of `+mute`, kept whole. -/
noncomputable def rpSof : Noun := (slot? 1040378 rpViBat).getD (A 0)

/-- The rest of the `%1` branch of `+mute`, kept whole. -/
noncomputable def rpOneRest : Noun := (slot? 2080759 rpViBat).getD (A 0)

/-- The test of `+mute` after `+mock`: `%0`, `%1` (`[8 sof [1 1] rest]`), else `%2`. -/
noncomputable def rpMuteRest : Noun :=
  let t0 := C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))
  let b0 := C (C (A 1) (A 0)) (C (A 0) (A 5))
  let t1 := C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 4)))
  let one := C (A 8) (C rpSof (C (C (A 1) (A 1)) rpOneRest))
  let two := C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 4)))))
    (C (C (A 1) (A 1)) (C (A 0) (A 5))))
  C (A 6) (C t0 (C b0 (C (A 6) (C t1 (C one two)))))

/-- The call of `+mock` in `+mute`: `(mock [tap %9 2 %0 1] gul)`. -/
def rpMockCall : Noun :=
  C (A 8) (C (C (A 9) (C (A 1406) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 14)) (C (A 1) rpK)))) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))

/-- The battery of the gate `+mute`. -/
noncomputable def rpMuteBat : Noun :=
  let gul := C (A 6) (C (C (A 0) (A 30)) (C rpGulX (C (A 1) (A 0))))
  C (A 8) (C gul (C (A 8) (C rpMockCall rpMuteRest)))

/-- The arm `+mute` of the door. -/
noncomputable def rpMuteArm : Noun := C (A 8) (C (C (A 1) rpTapB) (C (C (A 1) rpMuteBat) (C (A 0) (A 1))))

theorem rp_mute_at : slot? 15 rpViBat = some rpMuteArm := by kernel_rfl

/-! ## `+mean` never returns -/

theorem rp_mean_loop (L5 : Noun) : ∀ (k : Nat) (a : Noun), iterN k (C rpMeanBat (C a L5)) rpMeanBat = none := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    rw [iterN_succ]
    conv => { lhs; arg 3; unfold rpMeanBat }
    cases a with
    | atom n => cases n <;> simp [nock_exec]
    | cell x y => simp [nock_exec, ih]

/-- **`+mean`** never returns, on any sample and in any context. -/
theorem rp_mean_none (L5 a : Noun) : nock (C rpMeanBat (C a L5)) rpMeanBat = none := by
  cases h : nock (C rpMeanBat (C a L5)) rpMeanBat with
  | none => rfl
  | some p =>
    obtain ⟨k, hk⟩ := iterN_complete h
    rw [rp_mean_loop] at hk
    cases hk

/-! ## `+mock` in layer 4 -/

/-- A `Lib` whose scry slam is Nock's; with `gul = ~` no field is read. -/
def rpLib : Lib := ⟨slamGate nock, fun _ => none, fun _ _ => none, fun _ => A 0⟩

theorem rpLib_slam : SlamIsNock rpLib := fun _ _ => rfl

theorem rp_mock_arm (c : Noun) :
    nock c mock.arm = some (C mock.battery (C (C (C (A 0) (A 0)) (A 0)) c)) := by
  nock_open mock.arm; simp only [nock_exec]

/-- `+mock` is `+mook` of `+mink`. -/
theorem rp_mock_split (ctx : Noun) (hmook : slot? 2810 ctx = some mook.arm)
    (hmk : slot? 22524 ctx = some mink.arm) (s f gul : Noun) :
    nock (C mock.battery (C (C (C s f) gul) ctx)) mock.battery
      = (nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery).bind
          fun y => nock (mookGate y ctx) mook.battery := by
  nock_open mock.battery
  simp [nock_exec, hmook, hmk, mook_arm, mink_arm, bind_bind_some]

theorem rp_mook_zero (ctx p : Noun) : nock (mookGate (C (A 0) p) ctx) mook.battery = some (C (A 0) p) := by
  nock_open mook.battery; simp [nock_exec]

theorem rp_mook_one (ctx p : Noun) : nock (mookGate (C (A 1) p) ctx) mook.battery = some (C (A 1) p) := by
  nock_open mook.battery; simp [nock_exec]

theorem rp_mook_two (ctx : Noun) (tr : Trace) (x : Noun)
    (h : nock (mookGate (Tone.two tr).toNoun ctx) mook.battery = some x) : ∃ q, x = C (A 2) q := by
  have hgate : nock (mookGate (Tone.two tr).toNoun ctx) mook.battery
      = nock (mookCore (twoN tr) ctx) mook.buc := by
    nock_open mook.battery
    simp [nock_exec, Tone.toNoun]
  rw [hgate] at h
  conv at h => lhs; arg 2; unfold mook.buc
  rw [nock_cell, nock_op1, Option.bind_some] at h
  obtain ⟨q, _, hq⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨q, (Option.some.inj hq).symm⟩

/-- What the pill's `+mock` returns on `[[s f] ~]`: `[%0 p]` when `+mink`
ends in `%0`, else a cell whose head is not `0`. -/
theorem rp_mock_cases (s f x : Noun)
    (h : nock (C mock.battery (C (C (C s f) (A 0)) layer4)) mock.battery = some x) :
    (∃ p, x = C (A 0) p ∧ Mink rpLib (A 0) [] s f (Tone.zero p)) ∨ ∃ n q, n ≠ 0 ∧ x = C (A n) q := by
  rw [rp_mock_split layer4 mook.arm_at mink.arm_at] at h
  obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨r, rfl, hr⟩ := (mink_pill_iff rpLib rpLib_slam s f (A 0) y).1 hy
  cases r with
  | zero p =>
    rw [Tone.toNoun, rp_mook_zero] at h
    cases h
    exact Or.inl ⟨p, rfl, hr⟩
  | one p =>
    rw [Tone.toNoun, rp_mook_one] at h
    cases h
    exact Or.inr ⟨1, p, by decide, rfl⟩
  | two tr =>
    obtain ⟨q, rfl⟩ := rp_mook_two layer4 tr x h
    exact Or.inr ⟨2, q, by decide, rfl⟩

theorem rp_mock_zero (s f p : Noun) (h : Mink rpLib (A 0) [] s f (Tone.zero p)) :
    nock (C mock.battery (C (C (C s f) (A 0)) layer4)) mock.battery = some (C (A 0) p) := by
  rw [rp_mock_split layer4 mook.arm_at mink.arm_at,
    (mink_pill_iff rpLib rpLib_slam s f (A 0) _).2 ⟨_, rfl, h⟩, Option.bind_some]
  exact rp_mook_zero layer4 p

/-! ## `+mute` -/

theorem rp_mute_run (T vb L4 : Noun) (hm : slot? 1406 L4 = some mock.arm) :
    nock (C rpMuteBat (C T (C vb (C (A 1) L4)))) rpMuteBat =
      (nock (C mock.battery (C (C (C T rpK) (A 0)) L4)) mock.battery).bind fun ton =>
        nock (C ton (C (A 0) (C rpMuteBat (C T (C vb (C (A 1) L4)))))) rpMuteRest := by
  conv => lhs; arg 2; unfold rpMuteBat
  unfold rpMockCall
  simp only [nock_exec, Option.bind_some, hm, rp_mock_arm]

theorem rp_mute_rest_zero (p G : Noun) : nock (C (C (A 0) p) G) rpMuteRest = some (C (A 0) p) := by
  unfold rpMuteRest; simp [nock_exec]

theorem rp_mute_rest_ne (n : Nat) (hn : n ≠ 0) (q G x : Noun)
    (hx : nock (C (C (A n) q) G) rpMuteRest = some x) : ∃ r, x = C (A 1) r := by
  unfold rpMuteRest at hx
  by_cases h1 : n = 1
  · subst h1
    have hne : (A 0 = A 1) = False := by simp
    simp only [nock_exec, Option.bind_some, hne, if_false, if_true] at hx
    obtain ⟨a, _, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨b, _, hx⟩ := Option.bind_eq_some_iff.1 hx
    exact ⟨b, (Option.some.inj hx).symm⟩
  · have h0 : (0 = n) = False := by simp; omega
    have h1' : (1 = n) = False := by simp; omega
    simp [nock_exec, h0, h1'] at hx
    exact ⟨q, hx.symm⟩

/-- What `+mute` returns: `[%& p]` when `+mink` ends in `[%0 p]`, else a
cell with head `%|`. -/
theorem rp_mute_cases (T : Noun) (x : Noun) (vb : Noun)
    (h : nock (C rpMuteBat (C T (C vb (C (A 1) layer4)))) rpMuteBat = some x) :
    (∃ p, x = C (A 0) p ∧ Mink rpLib (A 0) [] T rpK (Tone.zero p)) ∨ ∃ r, x = C (A 1) r := by
  rw [rp_mute_run T vb layer4 mock.arm_at] at h
  obtain ⟨ton, hton, h⟩ := Option.bind_eq_some_iff.1 h
  rcases rp_mock_cases T rpK ton hton with ⟨p, rfl, hp⟩ | ⟨n, q, hn, rfl⟩
  · rw [rp_mute_rest_zero] at h
    cases h
    exact Or.inl ⟨p, rfl, hp⟩
  · exact Or.inr (rp_mute_rest_ne n hn q _ x h)

theorem rp_mute_zero (T vb p : Noun) (h : Mink rpLib (A 0) [] T rpK (Tone.zero p)) :
    nock (C rpMuteBat (C T (C vb (C (A 1) layer4)))) rpMuteBat = some (C (A 0) p) := by
  rw [rp_mute_run T vb layer4 mock.arm_at, rp_mock_zero T rpK p h, Option.bind_some, rp_mute_rest_zero]

/-! ## `+mule` -/

theorem rp_mule_run (T vb L4 : Noun) (hmute : slot? 15 vb = some rpMuteArm) :
    nock (C rpMuleBat (C T (C vb (C (A 1) L4)))) rpMuleBat =
      (nock (C rpMuteBat (C T (C vb (C (A 1) L4)))) rpMuteBat).bind fun mud =>
        nock (C mud (C rpMuleBat (C T (C vb (C (A 1) L4))))) rpMuleRest := by
  conv => lhs; arg 2; unfold rpMuleBat
  unfold rpMuteCall
  simp only [nock_exec, Option.bind_some, hmute]
  unfold rpMuteArm
  simp only [nock_exec, Option.bind_some]

theorem rp_mule_rest_zero (p M T D : Noun) :
    nock (C (C (A 0) p) (C M (C T D))) rpMuleRest = (nock T rpK).bind fun y => some (C (A 0) y) := by
  unfold rpMuleRest; simp [nock_exec]

theorem rp_mule_rest_one (r G : Noun) : nock (C (C (A 1) r) G) rpMuleRest = some (C (A 1) r) := by
  unfold rpMuleRest; simp [nock_exec]

/-- What `+mule` returns: `[%& y]` when `+mink` of the trap ends in `%0` and
the direct run returns `y`, else a cell with head `%|`. -/
theorem rp_mule_cases (T vb x : Noun) (hmute : slot? 15 vb = some rpMuteArm)
    (h : nock (C rpMuleBat (C T (C vb (C (A 1) layer4)))) rpMuleBat = some x) :
    (∃ p, Mink rpLib (A 0) [] T rpK (Tone.zero p) ∧ ∃ y, nock T rpK = some y ∧ x = C (A 0) y) ∨
      ∃ r, x = C (A 1) r := by
  rw [rp_mule_run T vb layer4 hmute] at h
  obtain ⟨mud, hmud, h⟩ := Option.bind_eq_some_iff.1 h
  rcases rp_mute_cases T mud vb hmud with ⟨p, rfl, hp⟩ | ⟨r, rfl⟩
  · rw [rp_mule_rest_zero] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
    exact Or.inl ⟨p, hp, y, hy, (Option.some.inj h).symm⟩
  · rw [rp_mule_rest_one] at h
    exact Or.inr ⟨r, (Option.some.inj h).symm⟩

theorem rp_mule_zero (T vb p y : Noun) (hmute : slot? 15 vb = some rpMuteArm)
    (hp : Mink rpLib (A 0) [] T rpK (Tone.zero p)) (hy : nock T rpK = some y) :
    nock (C rpMuleBat (C T (C vb (C (A 1) layer4)))) rpMuleBat = some (C (A 0) y) := by
  rw [rp_mule_run T vb layer4 hmute, rp_mute_zero T vb p hp, Option.bind_some, rp_mule_rest_zero, hy,
    Option.bind_some]

/-! ## `road-pure` -/

theorem rp_bat_split (T ctx L4 vb clue : Noun) (hl4 : slot? 63 ctx = some L4)
    (hvi : slot? 22526 L4 = some (C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) vb) (C (A 0) (A 1)))))
      (C (A 11) (C (C (A 0x74736166) (C (A 1) clue)) (C (A 0) (A 1)))))))
    (hmule : slot? 6 vb = some rpMuleArm) :
    nock (C rpBat (C T ctx)) rpBat =
      (nock (C rpMuleBat (C T (C vb (C (A 1) L4)))) rpMuleBat).bind fun res =>
        nock (C res (C rpBat (C T ctx))) rpRest := by
  conv => lhs; arg 2; unfold rpBat
  unfold rpMuleCall
  simp only [nock_exec, Option.bind_some, hl4, hvi, hmule]
  unfold rpMuleArm
  simp only [nock_exec, Option.bind_some]

theorem rp_rest_zero (y S : Noun) : nock (C (C (A 0) y) S) rpRest = some y := by
  unfold rpRest; simp [nock_exec]

theorem rp_rest_one (r T ctx L5 : Noun) (hl5 : slot? 31 ctx = some L5)
    (hmean : slot? 2558 L5 = some rpMeanArm) :
    nock (C (C (A 1) r) (C rpBat (C T ctx))) rpRest = none := by
  have hne : (A 0 = A 1) = False := by simp
  unfold rpRest
  simp only [nock_exec, Option.bind_some, hl5, hmean, hne, if_false]
  unfold rpMeanArm
  simp [nock_exec, rp_mean_none]

/-- **`road-pure`** on a trap `T`, in a context with `layer4` at `63` and the
fifth layer at `31`, returns `y` exactly when `+mink` of `[T [9 2 0 1]]`
with no scry gate ends in `%0` and the direct run of `T` returns `y`. -/
theorem rp_run_iff (T ctx L5 y : Noun) (hl4 : slot? 63 ctx = some layer4) (hl5 : slot? 31 ctx = some L5)
    (hmean : slot? 2558 L5 = some rpMeanArm) :
    nock (C rpBat (C T ctx)) rpBat = some y ↔
      (∃ p, Mink rpLib (A 0) [] T rpK (Tone.zero p)) ∧ nock T rpK = some y := by
  rw [rp_bat_split T ctx layer4 rpViBat rpViClue hl4 rp_vi_at rp_mule_at]
  constructor
  · intro h
    obtain ⟨res, hres, h⟩ := Option.bind_eq_some_iff.1 h
    rcases rp_mule_cases T rpViBat res rp_mute_at hres with ⟨p, hp, y', hy', rfl⟩ | ⟨r, rfl⟩
    · rw [rp_rest_zero] at h
      cases h
      exact ⟨⟨p, hp⟩, hy'⟩
    · rw [rp_rest_one r T ctx L5 hl5 hmean] at h
      cases h
  · rintro ⟨⟨p, hp⟩, hy⟩
    rw [rp_mule_zero T rpViBat p y rp_mute_at hp hy, Option.bind_some, rp_rest_zero]

/-! ## The gate `+ska-poke` -/

/-- The trap that `+ska-poke` hands `road-pure`, on the sample `sam`. -/
noncomputable def spTrap (sam : Noun) : Noun := C spX (C spBat (C sam ana))

theorem sp_trap_kick (sam : Noun) : nock (spTrap sam) rpK = nock (spTrap sam) spX := by
  unfold rpK spTrap
  simp only [nock_op9, nock_op0, slot?_one, Option.bind_some]
  rfl

/-- **The gate `+ska-poke`** on the sample `sam` returns `y` exactly when
`+mink` of its trap with no scry gate ends in `%0` and the trap returns `y`. -/
theorem ska_poke_gate_iff (sam y : Noun) :
    nock (C spBat (C sam ana)) spBat = some y ↔
      (∃ p, Mink rpLib (A 0) [] (spTrap sam) rpK (Tone.zero p)) ∧ nock (spTrap sam) spX = some y := by
  rw [sp_bat_run, rp_at, Option.bind_some,
    show edit? 6 (C spX (C spBat (C sam ana))) (C rpBat (C rpSam rpCtx))
      = some (C rpBat (C (spTrap sam) rpCtx)) from rfl, Option.bind_some,
    show slot? 2 (C rpBat (C (spTrap sam) rpCtx)) = some rpBat from rfl, Option.bind_some,
    rp_run_iff (spTrap sam) rpCtx rpL5 y rp_l4 rp_l5 rp_mean_at, sp_trap_kick]

/-! ## `+mink` with no scry gate is `EvalH` -/

theorem rp_tz {x : Option Tone} {k : Noun → Option Tone} {p : Noun}
    (h : tbind x k = some (Tone.zero p)) : ∃ y, x = some (Tone.zero y) ∧ k y = some (Tone.zero p) := by
  rcases tbind_eq_some h with h | ⟨_, hnz⟩
  · exact h
  · exact absurd rfl (hnz p)

/-- One level of `+mink` with no scry gate that ends in `[%0 p]` is an
`EvalH` step, given the same of its calls. -/
theorem rp_evalH_step (lib : Lib) (go : Trace → Noun → Noun → Option Tone)
    (ih : ∀ t s f p, go t s f = some (Tone.zero p) → EvalH s f p) (t : Trace) (s f p : Noun)
    (h : minkStep lib (A 0) go t s f = some (Tone.zero p)) : EvalH s f p := by
  unfold minkStep at h
  split at h
  · obtain ⟨a, h1, h⟩ := rp_tz h
    obtain ⟨b, h2, h⟩ := rp_tz h
    cases h
    exact EvalH.cell (ih _ _ _ _ h1) (ih _ _ _ _ h2)
  · split at h
    · cases h
    · rename_i hs
      cases h
      exact EvalH.op0 (slot?_sound _ hs)
  · cases h
    exact EvalH.op1
  · obtain ⟨a, h1, h⟩ := rp_tz h
    obtain ⟨b, h2, h⟩ := rp_tz h
    exact EvalH.op2 (ih _ _ _ _ h1) (ih _ _ _ _ h2) (ih _ _ _ _ h)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    cases h
    exact EvalH.op3 (ih _ _ _ _ h1)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    split at h
    · cases h
    · cases h
      exact EvalH.op4 (ih _ _ _ _ h1)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    obtain ⟨b, h2, h⟩ := rp_tz h
    cases h
    exact EvalH.op5 (ih _ _ _ _ h1) (ih _ _ _ _ h2)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    split at h
    · exact EvalH.op6_zero (ih _ _ _ _ h1) (ih _ _ _ _ h)
    · exact EvalH.op6_one (ih _ _ _ _ h1) (ih _ _ _ _ h)
    · cases h
  · obtain ⟨a, h1, h⟩ := rp_tz h
    exact EvalH.op7 (ih _ _ _ _ h1) (ih _ _ _ _ h)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    exact EvalH.op8 (ih _ _ _ _ h1) (ih _ _ _ _ h)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    split at h
    · cases h
    · rename_i hs
      exact EvalH.op9 (ih _ _ _ _ h1) (slot?_sound _ hs) (ih _ _ _ _ h)
  · split at h
    · cases h
    · obtain ⟨a, h1, h⟩ := rp_tz h
      obtain ⟨b, h2, h⟩ := rp_tz h
      split at h
      · cases h
      · rename_i he
        cases h
        exact EvalH.op10 (ih _ _ _ _ h2) (ih _ _ _ _ h1) (edit?_sound _ he)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    cases h
    exact EvalH.op11_atom (ih _ _ _ _ h1)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    obtain ⟨b, h2, h⟩ := rp_tz h
    cases h
    exact EvalH.op11_cell (ih _ _ _ _ h1) (ih _ _ _ _ h2)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    obtain ⟨b, h2, h⟩ := rp_tz h
    cases h
    exact EvalH.op11_ctag (ih _ _ _ _ h1) (ih _ _ _ _ h2)
  · obtain ⟨a, h1, h⟩ := rp_tz h
    obtain ⟨b, h2, h⟩ := rp_tz h
    simp at h
  · cases h

/-- **`+mink` with no scry gate** ends in `[%0 p]` only on an `EvalH` run
to `p`, which is a Nock run (`EvalH.toEval`).  With `mink_of_evalH`, the two
are the same. -/
theorem evalH_of_minkF_nil (lib : Lib) :
    ∀ (n : Nat) (t : Trace) (s f p : Noun), minkF lib (A 0) n t s f = some (Tone.zero p) → EvalH s f p
  | 0, _, _, _, _, h => by simp [minkF] at h
  | n + 1, t, s, f, p, h => by
    rw [minkF_succ_eq] at h
    exact rp_evalH_step lib (minkF lib (A 0) n) (evalH_of_minkF_nil lib n) t s f p h

theorem evalH_of_mink_nil {lib : Lib} {s f p : Noun} (h : Mink lib (A 0) [] s f (Tone.zero p)) :
    EvalH s f p := by
  obtain ⟨n, hn⟩ := h
  exact evalH_of_minkF_nil lib n [] s f p hn

/-- **The gate `+ska-poke`** returns `y` exactly when the run of its trap is
an `EvalH` run to `y`, that is, a Nock run.  No hypothesis. -/
theorem ska_poke_iff_evalH (sam y : Noun) :
    nock (C spBat (C sam ana)) spBat = some y ↔ EvalH (spTrap sam) rpK y := by
  rw [ska_poke_gate_iff]
  constructor
  · rintro ⟨⟨p, hp⟩, hy⟩
    have he := evalH_of_mink_nil hp
    cases Eval.deterministic he.toEval (eval_of_nock (by rw [sp_trap_kick]; exact hy))
    exact he
  · intro he
    obtain ⟨n, hn⟩ := mink_of_evalH rpLib (A 0) he
    refine ⟨⟨y, n, hn []⟩, ?_⟩
    rw [← sp_trap_kick]
    exact nock_of_eval he.toEval

/-- `nock` is `Eval`, which is `EvalH`, so every return of the trap is an
`EvalH` run. -/
theorem sp_trap_evalH (sam y : Noun) (h : nock (spTrap sam) spX = some y) : EvalH (spTrap sam) rpK y := by
  rw [← sp_trap_kick] at h
  exact SkaModel.Eval.toEvalH (eval_of_nock h)

/-- **The gate `+ska-poke`** returns `y` exactly when its trap does.  No
hypothesis: `+mink` follows Nock, so the run under `+mink` that `road-pure`
makes first returns whenever the trap does. -/
theorem ska_poke_iff (sam y : Noun) :
    nock (C spBat (C sam ana)) spBat = some y ↔ nock (spTrap sam) spX = some y := by
  rw [ska_poke_gate_iff]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨n, hn⟩ := mink_of_evalH rpLib (A 0) (sp_trap_evalH sam y h)
    exact ⟨⟨y, n, hn []⟩, h⟩

end Compiler
end Formalization
