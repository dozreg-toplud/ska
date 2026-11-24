import lemmas.Compiler.OptLinkOnceGate

/-!
# `+optimize` linked

```hoon
++  optimize
  ~%  %optimize  ..ride  ~
  |=  s=straight
  ^-  straight-out
  =.  s
    |-  ^-  straight
    =^  changed=?  s  (optimize-once s)
    ?.  changed  s
    $(s s)
  ::
  s(blocks (switch-chains blocks.s))
```

The arm is `2941` of `optC` (`opt_at`, nouns by `tools/gen/optlink.py
opt`): the body runs the trap `optTrap` and then `+switch-chains` (arm `182`,
`sw_at`) on the blocks of its product (`optSw`).

* `SwitchLink P`: what the link assumes of `+switch-chains`: where
  `P.switch` returns on blocks with no `%lti`, the gate on the noun of the
  blocks returns the noun of the result.
* `opt_loop`: **where `optLoop fuel P n s` returns `s'`, the trap returns
  the noun of `s'`**, by induction on `n` from `oo_gate`.
* `opt_gate`: **where `optimizeF fuel P s` returns `s'` on a straight
  function whose blocks have no `%lti`, the gate of `+optimize` returns the
  noun of `s'`**, given `AliasLink P`, `TrimLink P` and `SwitchLink P`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The `%fast` hint of `+switch-chains`. -/
def optSwHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x736e696168632d686374697773) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The trap of `+optimize`: `+optimize-once` until no change. -/
def optTrap : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 180) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 30))) (C (A 0) (A 3)))))) (C (A 0) (A 30)))))))))))))

/-- `(switch-chains blocks.s)`. -/
def optSw : Noun :=
  (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))

/-- The gate body of `+optimize`. -/
def optBody : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 1) optTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 1)))) (C (A 10) (C (C (A 7) optSw) (C (A 0) (A 6))))))

/-- Its sample bunt. -/
def optBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (A 0)))

/-- Its `%fast` hint. -/
def optHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x657a696d6974706f) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+optimize`. -/
def optArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) optBunt) (C (C (A 1) optBody) (C (A 0) (A 1))))) optHint)

/-- `+optimize` is arm `2941` of `optC`. -/
theorem opt_at : slot? 2941 optC = some optArm := by kernel_rfl

@[nock_exec] theorem opt_arm (d : Noun) : nock d optArm = some (C optBody (C optBunt d)) := by
  unfold optArm optHint; generalize optBody = B; generalize optBunt = U; simp [nock_exec]

/-! ## `+switch-chains`, as a hypothesis -/

/-- The arm `+switch-chains` (axis `182` of `optC`), its body and bunt read
from the pill. -/
noncomputable def swArm : Noun := (slot? 182 optC).getD (A 0)
noncomputable def swBody : Noun := (slot? 109 swArm).getD (A 0)
noncomputable def swBunt : Noun := (slot? 53 swArm).getD (A 0)

noncomputable def swArmN : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) swBunt) (C (C (A 1) swBody) (C (A 0) (A 1))))) optSwHint)

theorem sw_at : slot? 182 optC = some swArmN := by kernel_rfl

@[nock_exec] theorem sw_arm (d : Noun) : nock d swArmN = some (C swBody (C swBunt d)) := by
  unfold swArmN optSwHint; generalize swBody = B; generalize swBunt = U; simp [nock_exec]

/-- **What the link of `+optimize` assumes of `+switch-chains`**: where
`P.switch` returns on blocks with no `%lti`, the gate on the noun of the
blocks returns the noun of the result. -/
def SwitchLink (P : Opt.Passes (TreapMap mugF)) : Prop :=
  ∀ (bl bs : TreapMap mugF Blob), NoLti bl → P.switch bl = some bs →
    nock (C swBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) swBody = some (HoonMap.toNoun Blob.toNoun bs)

/-! ## The loop -/

/-- **The trap of `+optimize`**: where `optLoop fuel P n s` returns `s'`,
the trap returns the noun of `s'`, which has no `%lti`. -/
theorem opt_loop (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P) (hT : TrimLink P) (fuel : Nat) :
    ∀ (n : Nat) (s s' : Straight (TreapMap mugF)), NoLti s.blocks → Opt.optLoop fuel P n s = some s' →
    NoLti s'.blocks ∧ nock (C optTrap (C optBody (C s.toNoun optC))) optTrap = some s'.toNoun := by
  intro n
  induction n with
  | zero => intro s s' hl h; simp [Opt.optLoop] at h
  | succ n ih =>
    intro s s' hl h
    simp only [Opt.optLoop, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    have hg := oo_gate P hA hT fuel s hl r hr
    have hl1 := optimizeOnce_noLti P hA hT fuel s hl r hr
    have h1a := oo_at
    obtain ⟨c, s1⟩ := r
    simp only at hg hl1 h
    cases c with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      refine ⟨hl1, ?_⟩
      conv => lhs; arg 2; unfold optTrap
      generalize optC = OC at hg h1a
      generalize Straight.toNoun s = SN at hg ⊢
      generalize Straight.toNoun s1 = SN1 at hg ⊢
      simp [nock_exec, h1a, oo_arm, hg, flag]
    | true =>
      simp only [if_true] at h
      obtain ⟨hl', hn⟩ := ih s1 s' hl1 h
      refine ⟨hl', ?_⟩
      conv => lhs; arg 2; unfold optTrap
      generalize optC = OC at hg h1a hn
      generalize Straight.toNoun s = SN at hg ⊢
      generalize Straight.toNoun s1 = SN1 at hg hn ⊢
      generalize optTrap = TR at hn ⊢
      simp [nock_exec, h1a, oo_arm, hg, flag, hn]

/-! ## The gate -/

/-- **`+optimize`**: where `optimizeF fuel P s` returns `s'` on a straight
function whose blocks have no `%lti`, the gate returns the noun of `s'`,
given the links of `+alias`, `+trim-trace-hints` and `+switch-chains`. -/
theorem opt_gate (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P) (hT : TrimLink P) (hS : SwitchLink P)
    (fuel : Nat) (s s' : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (h : Opt.optimizeF fuel P s = some s') :
    nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun := by
  simp only [Opt.optimizeF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨s1, h1, bs, hsw, rfl⟩ := h
  obtain ⟨hl1, hn⟩ := opt_loop P hA hT fuel fuel s s1 hl h1
  have hs := hS s1.blocks bs hl1 hsw
  have h1a := sw_at
  have e1 : s1.toNoun = C s1.need.toNoun (C (A s1.nargs) (HoonMap.toNoun Blob.toNoun s1.blocks)) := rfl
  have e2 : (Opt.withBlocks s1 bs).toNoun = C s1.need.toNoun (C (A s1.nargs) (HoonMap.toNoun Blob.toNoun bs)) := rfl
  rw [e2]
  rw [e1] at hn
  conv => lhs; arg 2; unfold optBody
  generalize optC = OC at hn hs h1a
  generalize Straight.toNoun s = SN at hn ⊢
  generalize optTrap = TR at hn ⊢
  generalize HoonMap.toNoun Blob.toNoun s1.blocks = B1 at hn hs ⊢
  generalize HoonMap.toNoun Blob.toNoun bs = BS at hs ⊢
  simp [nock_exec, hn, optSw, h1a, sw_arm, hs]

end Compiler
end Formalization
