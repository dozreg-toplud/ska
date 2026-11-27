import lemmas.Compiler.CompInlinedL2

/-!
# `+inlined`: the gate, by induction on the fuel (track Q)

`inl_gate_fuel`: on every cache with `InlCoh` (the cache coherence), the
pill's gate `+inlined` on a bell `b` returns `inlinedM … fuel b` and a cache
with `InlCoh`, whenever the model returns.  The induction on the fuel is the
recursion `inlined-loop` (`B2Env.go` of `inl_b2`).
* Miss (`inl.cache` has no `b`): the nomm of `b` from `code.long-ska`
  (`CodeN`), the trap (`inl_trap` with `inl_b2`), the put into `inl.cache`.
* Hit: the stored nomm is `inlinedM` of `b` at some fuel (`InlCoh`), so it is
  the model's result at this fuel (`inlinedM_det`).

`InlCoh Q CA`: `CA` is `cacheN C1 C2 C3 INL SURE`, `Q` holds of the `sccs`
`C3`, `INL` is a map, and every entry `b ↦ v` of `INL` is `inlinedM` of `b`
at some fuel.  `Q` is any invariant of `sccs` under which `+scc-of` answers
the singleton test as `single` does (`SccQ`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Glue

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The model: the walk and `inlinedM` are monotone in the callee results -/

theorem inlWalk_mono {calls : Bell → Bell → Bool} {hot single : Bell → Bool} {go go' : Bell → Option Nomm}
    (h : ∀ c m, go c = some m → go' c = some m) :
    ∀ nm r, inlWalk calls hot single go nm = some r → inlWalk calls hot single go' nm = some r := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, e⟩
  | n0 a =>
    intro r hr
    exact hr
  | n1 k =>
    intro r hr
    exact hr
  | n3 p ihp =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, e⟩ := hr
    exact ⟨a0, ihp a0 w0, e⟩
  | n4 p ihp =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, e⟩ := hr
    exact ⟨a0, ihp a0 w0, e⟩
  | n5 p q ihp ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, e⟩
  | n6 p q r ihp ihq ihr =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, a2, w2, e⟩ := hr
    exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, a2, ihr a2 w2, e⟩
  | n7 p q ihp ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, e⟩
  | n10 a v q ihv ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihv a0 w0, a1, ihq a1 w1, e⟩
  | n11s t q body ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, e⟩ := hr
    exact ⟨a0, ihq a0 w0, e⟩
  | n11d t h q body ihh ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihh a0 w0, a1, ihq a1 w1, e⟩
  | n12 p q ihp ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, e⟩
  | mean p b q body k ihp ihq =>
    intro r hr
    simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨a0, w0, a1, w1, e⟩ := hr
    exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, e⟩
  | n2 p q info ihp ihq =>
    intro r hr
    cases info with
    | none =>
      simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨a0, w0, a1, w1, e⟩ := hr
      exact ⟨a0, ihp a0 w0, a1, ihq a1 w1, e⟩
    | some ck =>
      obtain ⟨c, k⟩ := ck
      simp only [inlWalk, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨a0, w0, a1, w1, e⟩ := hr
      refine ⟨a0, ihp a0 w0, a1, ihq a1 w1, ?_⟩
      by_cases hok : inlOK calls hot single c k q = true
      · simp only [hok, if_true, Option.bind_eq_some_iff] at e ⊢
        obtain ⟨m, hm, e⟩ := e
        exact ⟨m, h c m hm, e⟩
      · simp only [hok, Bool.false_eq_true, if_false] at e ⊢
        exact e

theorem inlinedM_mono {code : Bell → Option Nomm} {calls : Bell → Bell → Bool} {hot single : Bell → Bool} :
    ∀ f f', f ≤ f' → ∀ b m, inlinedM code calls hot single f b = some m →
      inlinedM code calls hot single f' b = some m := by
  intro f
  induction f with
  | zero => intro f' _ b m h; simp [inlinedM] at h
  | succ f ih =>
    intro f' hf b m h
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [inlinedM, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨nb, hnb, hw⟩ := h
    exact ⟨nb, hnb, inlWalk_mono (fun c m' hc => ih f'' (by omega) c m' hc) nb m hw⟩

theorem inlinedM_det {code : Bell → Option Nomm} {calls : Bell → Bell → Bool} {hot single : Bell → Bool}
    {f f' : Nat} {b : Bell} {m m' : Nomm} (h : inlinedM code calls hot single f b = some m)
    (h' : inlinedM code calls hot single f' b = some m') : m = m' := by
  have a := inlinedM_mono f (max f f') (Nat.le_max_left _ _) b m h
  have a' := inlinedM_mono f' (max f f') (Nat.le_max_right _ _) b m' h'
  rw [a] at a'
  exact Option.some.inj a'

/-! ## The cache coherence -/

theorem inl_bell_inj {a b : Bell} (h : a.toNoun = b.toNoun) : a = b := SkaModel.Ana.TKey.enc_inj a b h

theorem inl_getF_cases {M k : Noun} (hm : IsMap mugF M) :
    getF mugF k M = some (A 0) ∨ ∃ u, getF mugF k M = some (C (A 0) u) := by
  by_cases h : ∃ v, Get M k v
  · obtain ⟨v, hg⟩ := h
    exact Or.inr ⟨v, getF_some hm hg⟩
  · exact Or.inl (getF_none hm fun v hg => h ⟨v, hg⟩)

/-- **The coherence of the cache** for `+inlined`. -/
def InlCoh (code : Bell → Option Nomm) (calls : Bell → Bell → Bool) (hot single : Bell → Bool)
    (Q : Noun → Prop) (CA : Noun) : Prop :=
  ∃ C1 C2 C3 INL SURE, CA = cacheN C1 C2 C3 INL SURE ∧ Q C3 ∧ IsMap mugF INL ∧
    ∀ (b : Bell) v, getF mugF b.toNoun INL = some (C (A 0) v) →
      ∃ f m, inlinedM code calls hot single f b = some m ∧ v = m.toNoun

/-- `+scc-of` under the invariant `Q` of `sccs`: the singleton test is
`single`, and the new `sccs` keep `Q`. -/
def SccQ (CALLS : Noun) (single : Bell → Bool) (Q : Noun → Prop) : Prop :=
  ∀ SC (c : Bell), Q SC → ∃ S SC', nock (C sccBat (C (C c.toNoun (C CALLS SC)) compK)) sccBat = some (C S SC') ∧
    sing S = single c ∧ Q SC'

/-- `code.long-ska` (the noun `CODE`) holds the nomm of every bell of `code`. -/
def CodeN (CODE : Noun) (code : Bell → Option Nomm) : Prop :=
  ∀ b nb, code b = some nb → ∃ V, getF mugF b.toNoun CODE = some (C (A 0) V) ∧ slot? 2 V = some nb.toNoun

/-- `calls.long-ska` (the noun `CALLS`) answers `calls c c` through
`(~(has in (~(gut by calls) c ~)) c)`. -/
def CallsN (CALLS : Noun) (calls : Bell → Bell → Bool) : Prop :=
  ∀ c : Bell, ∃ out S, getF mugF c.toNoun CALLS = some out ∧ (out = A 0 ∧ S = A 0 ∨ out = C (A 0) S) ∧
    hasInF mugF c.toNoun S = some (calls c c)

/-! ## The gate `hot` -/

def inlHB : Noun := (slot? 29 inlHot).getD (A 0)
def inlHBunt : Noun := (slot? 13 inlHot).getD (A 0)

theorem inlHot_eq : inlHot = C (A 8) (C (C (A 1) inlHBunt) (C (C (A 1) inlHB) (C (A 0) (A 1)))) := by
  kernel_rfl

/-- The gate `hot` answers `hot` on every gate core of `+inlined` with this
`long-ska` and `jets-hot`. -/
def HotN (LONG JH : Noun) (hot : Bell → Bool) : Prop :=
  ∀ (c : Bell) B CA, nock (C inlHB (C c.toNoun (C (A 0) (C inlBodyN (C (C B (C LONG (C JH CA))) compK))))) inlHB
    = some (loob (hot c))

/-! ## The gate -/

/-- The gate `+inlined` returns `go b` on every cache with `I`. -/
def GateP (I : Noun → Prop) (LONG JH : Noun) (go : Bell → Option Nomm) : Prop :=
  ∀ CA (b : Bell) m, I CA → go b = some m → ∃ CA', I CA' ∧
    nock (C inlBodyN (C (C b.toNoun (C LONG (C JH CA))) compK)) inlBodyN = some (C m.toNoun CA')

/-- **`+inlined` is `inlinedM`**, at every fuel, on every cache with
`InlCoh`, which it keeps. -/
theorem inl_gate_fuel {code : Bell → Option Nomm} {calls : Bell → Bell → Bool} {hot single : Bell → Bool}
    {Q : Noun → Prop} {CODE JETS CALLS JH : Noun}
    (hcode : CodeN CODE code) (hhot : HotN (C CODE (C JETS CALLS)) JH hot) (hcalls : CallsN CALLS calls)
    (hQ : SccQ CALLS single Q) :
    ∀ fuel, GateP (InlCoh code calls hot single Q) (C CODE (C JETS CALLS)) JH (inlinedM code calls hot single fuel) := by
  intro fuel
  induction fuel with
  | zero => intro CA b m _ h; simp [inlinedM] at h
  | succ f ih =>
    intro CA b m hI hm
    have hmf := hm
    obtain ⟨C1, C2, C3, INL, SURE, rfl, hq, hmap, hcoh⟩ := hI
    rcases inl_getF_cases (k := b.toNoun) hmap with hmiss | ⟨u, hhit⟩
    · simp only [inlinedM, Option.bind_eq_some_iff] at hm
      obtain ⟨nb, hnb, hw⟩ := hm
      obtain ⟨V, hg, hv⟩ := hcode b nb hnb
      have E : B2Env calls hot single (inlinedM code calls hot single f) (InlCoh code calls hot single Q) inlHB
          (C (A 0) (C inlBodyN (C (C b.toNoun (C (C CODE (C JETS CALLS)) (C JH (cacheN C1 C2 C3 INL SURE))))
            compK))) CODE JETS CALLS JH :=
        { hot := fun c => hhot c _ _
          calls := hcalls
          scc := by
            intro CA c hI
            obtain ⟨D1, D2, D3, DI, DS, rfl, hq, hm, hc⟩ := hI
            obtain ⟨S, SC', h1, h2, h3⟩ := hQ D3 c hq
            exact ⟨D1, D2, D3, DI, DS, S, SC', rfl, h1, h2, ⟨D1, D2, SC', DI, DS, rfl, h3, hm, hc⟩⟩
          go := ih }
      have hI0 : InlCoh code calls hot single Q (cacheN C1 C2 C3 INL SURE) := ⟨C1, C2, C3, INL, SURE, rfl, hq, hmap, hcoh⟩
      obtain ⟨CA', hI', e⟩ := inl_trap calls hot single (inlinedM code calls hot single f) _
        (C inlHB (C inlHBunt (C (A 0) (C inlBodyN (C (C b.toNoun (C (C CODE (C JETS CALLS)) (C JH (cacheN C1 C2 C3 INL SURE))))
            compK))))) (A 0) inlBodyN b.toNoun (C CODE (C JETS CALLS)) JH compK (inl_b2 E) nb _ m hI0 hw
      obtain ⟨D1, D2, D3, DI, DS, rfl, hq', hmap', hcoh'⟩ := hI'
      obtain ⟨DI', hput, hmap'', -⟩ := putF_spec mugF DI b.toNoun m.toNoun hmap'
      refine ⟨cacheN D1 D2 D3 DI' DS, ⟨D1, D2, D3, DI', DS, rfl, hq', hmap'', ?_⟩, ?_⟩
      · intro b' v hb'
        rcases getF_put_cases hmap' hput hb' with ⟨hk, rfl⟩ | ⟨-, hold⟩
        · rw [inl_bell_inj hk]; exact ⟨f + 1, m, hmf, rfl⟩
        · exact hcoh' b' v hold
      · have hL := compK_layer2
        have hoff := inline_off_at
        have hg' := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun INL (A 0) hmiss
        have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun CODE V hg
        have hp := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 b.toNoun m.toNoun DI DI' hput
        obtain ⟨v1, v2, rfl⟩ : ∃ a b, V = C a b := by
          cases V with
          | atom _ => simp [nock_exec] at hv
          | cell a b => exact ⟨a, b, rfl⟩
        simp only [nock_exec, Option.some.injEq] at hv
        subst hv
        conv => { lhs; arg 2; unfold inlBodyN }
        unfold cacheN inlR at *
        generalize compK = KC at hL hoff e ⊢
        simp [nock_exec, hL, inlGet, inlMiss, inlInner, inlGot, inlAfter, inlHot_eq, by.arm_at, by_arm, by.get.arm_at,
          get_arm, hg', by.got.arm_at, got_arm, hgt, hoff, e, by.put.arm_at, put_arm, hp]
    · obtain ⟨f', m', hm', rfl⟩ := hcoh b u hhit
      have hmm := inlinedM_det hm' hmf
      subst hmm
      refine ⟨cacheN C1 C2 C3 INL SURE, ⟨C1, C2, C3, INL, SURE, rfl, hq, hmap, hcoh⟩, ?_⟩
      rw [← inlBody_eq]
      exact inl_gate_hit b.toNoun (C CODE (C JETS CALLS)) JH C1 C2 C3 INL SURE m'.toNoun hhit

end Compiler
end Formalization
