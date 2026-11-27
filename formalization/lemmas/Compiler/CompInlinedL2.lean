import lemmas.Compiler.CompInlinedL
import lemmas.Compiler.Safe
import lemmas.Compiler.CompSccOfOne

/-!
# `+inlined`: the `%2` branch with an `info` (track Q)

```hoon
    [%2 *]
  =^  p  cache  $(nomm p.nomm)
  =^  q  cache  $(nomm q.nomm)
  =/  keep=^nomm  [%2 p q info.nomm]
  ?~  info.nomm  [keep cache]
  =/  c=bell  b.u.info.nomm
  ?.  &(?=(~ k.u.info.nomm) (safe-fol-fol q.nomm) !(hot c))
    [keep cache]
  =^  s=(set bell)  sccs.cache  (scc-of c calls.long-ska sccs.cache)
  ?.  ?=([* ~ ~] s)  [keep cache]
  ?:  (~(has in (~(gut by calls.long-ska) c ~)) c)  [keep cache]
  =^  m=^nomm  cache  inlined-loop(b c, cache cache)
  ?:  (gth (nomm-size m) inline-max)  [keep cache]
  [[%7 p m] cache]
```

`inl_b2` proves the hypothesis `h2` of `inl_trap` (`CompInlinedL.lean`)
from four facts about the parts the branch calls, each on the nouns:
* `hHot`: the gate `hot` (`HOT = [HB HS HC]`) on a bell `c` is `hot c`;
* `hCalls`: `(~(has in (~(gut by calls) c ~)) c)` is `calls c c`;
* `hScc`: on a cache with `I`, `+scc-of` (track P's `sccBat`) on `c`,
  `calls` and the `sccs` of the cache returns a set `S` with
  `sing S = single c` and new `sccs` that keep `I`;
* `hGo`: on a cache with `I`, the gate `+inlined` itself on `c` returns
  `go c` and a cache with `I`, when `go c` returns (the fuel induction
  hypothesis of the gate).
`+safe-fol-fol` (`safe_fol_fol_pill`), `+nomm-size` (`nsz_gate`) and `+gth`
are linked.  The `sccs` are the third field of `comp-cache`
(`cacheN C1 C2 C3 INL SURE`, `C3`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Glue

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `?=([* ~ ~] s)`: the set noun `s` has one element. -/
def sing : Noun → Bool
  | .cell _ (.cell (.atom 0) (.atom 0)) => true
  | _ => false

/-- The singleton test of the `%2` branch on any subject `[s x]`. -/
theorem sing_test (S X : Noun) :
    nock (C S X) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 5))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 11)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))
      = some (loob (sing S)) := by
  rcases S with s | ⟨x, y⟩
  · simp [nock_exec, sing, loob]
  rcases y with t | ⟨u, v⟩
  · simp [nock_exec, sing, loob]
  rcases u with u | ⟨u1, u2⟩ <;> rcases v with v | ⟨v1, v2⟩
  · by_cases hu : u = 0 <;> by_cases hv : v = 0
    · subst hu hv; simp [nock_exec, sing, loob, eqCode]
    · subst hu; simp [nock_exec, sing, loob, eqCode, hv, Ne.symm hv]
    · simp [nock_exec, sing, loob, eqCode, hu, Ne.symm hu]
    · simp [nock_exec, sing, loob, eqCode, hu, Ne.symm hu]
  · by_cases hu : u = 0
    · subst hu; simp [nock_exec, sing, loob, eqCode]
    · simp [nock_exec, sing, loob, eqCode, hu, Ne.symm hu]
  all_goals simp [nock_exec, sing, loob, eqCode]

/-- `sing_test` in the form `simp` leaves it in. -/
theorem sing_test' (S X : Noun) :
    ((pick (wut S) (C (A 6) (C (C (A 3) (C (A 0) (A 5))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 11)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))).bind fun next => nock (C S X) next) = some (loob (sing S)) := by
  have h := sing_test S X
  simp only [nock_exec] at h
  exact h

/-- The hypotheses of `inl_b2` on the parts the `%2` branch calls. -/
structure B2Env (calls : Bell → Bell → Bool) (hot single : Bell → Bool) (go : Bell → Option Nomm)
    (I : Noun → Prop) (HB HC CODE JETS CALLS JH : Noun) : Prop where
  hot : ∀ c : Bell, nock (C HB (C c.toNoun HC)) HB = some (loob (hot c))
  calls : ∀ c : Bell, ∃ out S, getF mugF c.toNoun CALLS = some out ∧ (out = A 0 ∧ S = A 0 ∨ out = C (A 0) S) ∧
    hasInF mugF c.toNoun S = some (calls c c)
  scc : ∀ CA (c : Bell), I CA → ∃ C1 C2 C3 INL SURE S SC', CA = cacheN C1 C2 C3 INL SURE ∧
    nock (C sccBat (C (C c.toNoun (C CALLS C3)) compK)) sccBat = some (C S SC') ∧
    sing S = single c ∧ I (cacheN C1 C2 SC' INL SURE)
  go : ∀ CA (c : Bell) m, I CA → go c = some m → ∃ CA', I CA' ∧
    nock (C inlBodyN (C (C c.toNoun (C (C CODE (C JETS CALLS)) (C JH CA))) compK)) inlBodyN
      = some (C m.toNoun CA')

theorem compK_ana : slot? 15 compK = some ana := by kernel_rfl

/-- **The `%2` branch with an `info`**: `h2` of `inl_trap`. -/
theorem inl_b2 {calls : Bell → Bell → Bool} {hot single : Bell → Bool} {go : Bell → Option Nomm}
    {I : Noun → Prop} {HB HS HC N B CODE JETS CALLS JH : Noun}
    (E : B2Env calls hot single go I HB HC CODE JETS CALLS JH) :
    ∀ p q c k, TrapP I (inlWalk calls hot single go) (C HB (C HS HC)) N inlBodyN B (C CODE (C JETS CALLS)) JH compK p →
      TrapP I (inlWalk calls hot single go) (C HB (C HS HC)) N inlBodyN B (C CODE (C JETS CALLS)) JH compK q →
      TrapP I (inlWalk calls hot single go) (C HB (C HS HC)) N inlBodyN B (C CODE (C JETS CALLS)) JH compK
        (Nomm.n2 p q (some (c, k))) := by
  intro p q c k ihp ihq CA nm' hI hw
  simp only [inlWalk, Option.bind_eq_some_iff] at hw
  obtain ⟨p', w1, q', w2, hw⟩ := hw
  obtain ⟨CA1, hI1, e1⟩ := ihp CA p' hI w1
  obtain ⟨CA2, hI2, e2⟩ := ihq CA1 q' hI1 w2
  have hL := compK_layer2
  have hL1 := inlK_layer1
  have hana := compK_ana
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  have hhot := E.hot c
  have ha := sccCore_arm
  rw [sccCore_compK] at ha
  have hst := sing_test
  conv => { arg 1; intro CA'; arg 2; lhs; arg 2; unfold inlTrap }
  unfold inlR at e1 e2
  cases k with
  | some v =>
    simp only [inlOK, Option.isNone_some, Bool.false_and, Bool.false_eq_true, if_false, Option.some.injEq] at hw
    subst hw
    refine ⟨CA2, hI2, ?_⟩
    generalize compK = KC at hL hL1 hana ha e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm]
  | none =>
  by_cases t1 : (safeFolFol q && !hot c) = true
  case neg =>
    have hok : inlOK calls hot single c none q = false := by
      cases h1 : safeFolFol q <;> cases h2 : hot c <;> simp_all [inlOK]
    simp only [hok, Bool.false_eq_true, if_false, Option.some.injEq] at hw
    subst hw
    refine ⟨CA2, hI2, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at t1
    generalize compK = KC at hL hL1 hana ha e1 e2 ⊢
    by_cases hs1 : safeFolFol q = true
    · have hh : hot c = true := by
        cases h : hot c
        · exact absurd ⟨hs1, h⟩ t1
        · rfl
      simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm, hs1, hh]
    · simp only [Bool.not_eq_true] at hs1
      simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm, hs1]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at t1
  obtain ⟨C1, C2, C3, INL, SURE, S, SC', rfl, hsc, hsing, hI3⟩ := E.scc CA2 c hI2
  by_cases hs : single c = true
  case neg =>
    have hok : inlOK calls hot single c none q = false := by
      simp only [inlOK, Option.isNone_none, Bool.true_and, t1.1, t1.2, hs]; simp
    simp only [hok, Bool.false_eq_true, if_false, Option.some.injEq] at hw
    subst hw
    refine ⟨cacheN C1 C2 SC' INL SURE, hI3, ?_⟩
    have hs' : sing S = false := by rw [hsing]; simpa using hs
    generalize compK = KC at hL hL1 hana ha e1 e2 hsc ⊢
    simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm, t1.1, t1.2, hsc, sing_test', hs']
  obtain ⟨out, S0, hg, hout, hhas⟩ := E.calls c
  have hhas' := has_in_gate layer2 gorIn_morIn_layer2.1 c.toNoun S0 (calls c c) hhas
  have hgut := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
    c.toNoun (A 0) CALLS out hg (by rcases hout with ⟨rfl, _⟩ | rfl; exact Or.inl rfl; exact Or.inr ⟨_, rfl⟩)
  have hgut' : nock (C by.gut.battery (C (C c.toNoun (A 0)) (C by.battery (C CALLS layer2)))) by.gut.battery
      = some S0 := by
    rw [hgut]; rcases hout with ⟨rfl, rfl⟩ | rfl <;> simp
  clear hgut
  have hs' : sing S = true := by rw [hsing]; exact hs
  by_cases hcc : calls c c = true
  · have hok : inlOK calls hot single c none q = false := by
      simp [inlOK, hcc]
    simp only [hok, Bool.false_eq_true, if_false, Option.some.injEq] at hw
    subst hw
    refine ⟨cacheN C1 C2 SC' INL SURE, hI3, ?_⟩
    generalize compK = KC at hL hL1 hana ha e1 e2 hsc ⊢
    simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm, t1.1, t1.2, hsc, sing_test', hs', hgut', hhas', hcc]
  have hok : inlOK calls hot single c none q = true := by
    simp only [Bool.not_eq_true] at hcc
    simp [inlOK, t1.1, t1.2, hs, hcc]
  simp only [hok, if_true, Option.bind_eq_some_iff, Option.some.injEq] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  obtain ⟨CA4, hI4, hg4⟩ := E.go _ c m hI3 hm
  refine ⟨CA4, hI4, ?_⟩
  simp only [cacheN] at hg4
  have hn := nsz_gate m
  have hgt := gth_gate layer1 arith_layer1.2.2.2.2.1 (nommSize 0 m) 48
  have hia := inl_imax_at
  have hna := nsz_at
  simp only [Bool.not_eq_true] at hcc
  by_cases hsz : inlineMax < nommSize 0 m
  · have hsz' : 48 < nommSize 0 m := hsz
    simp only [hsz, if_true]
    generalize compK = KC at hL hL1 hana ha e1 e2 hsc hg4 hn hia hna ⊢
    simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm, t1.1, t1.2, hsc, sing_test', hs', hgut', hhas', hcc, hg4, hn, nsz_arm, hgt, gth.arm_at, gth_arm, hia, hna, hsz']
  · have hsz' : ¬ 48 < nommSize 0 m := hsz
    simp only [hsz, if_false]
    generalize compK = KC at hL hL1 hana ha e1 e2 hsc hg4 hn hia hna ⊢
    simp [nock_exec, Nomm.toNoun, unitNoun, Tag.mean, inlB2, inlR, cacheN, e1, e2, hL, hL1, hana, hsa, safe_fol_fol_arm, hsf, hhot, loob, ha, sccHint, by.arm_at, by_arm, by.gut.arm_at, gut_arm, in.arm_at, in_arm, in.has.arm_at, has_in_arm, t1.1, t1.2, hsc, sing_test', hs', hgut', hhas', hcc, hg4, hn, nsz_arm, hgt, gth.arm_at, gth_arm, hia, hna, hsz']

end Compiler
end Formalization
