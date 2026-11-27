import lemmas.Compiler.PokeLinkOpt
import lemmas.Hoon.Layer2

/-!
# The jetted-root test of `%full` (`JetRootLinkR`), proved on states whose jet maps are maps

`jrP` (`Compiler/PokeLinkFull.lean`) is `(~(get by call.cole.jets) func)`,
then `(~(has by jets-hot) u.rin)`, then `(~(put by ~) 0 [~ ~ [%jsf func 0
u.rin]])`, on the door `by` of `hoon.hoon` (axis `2097151` of the core, that
is `layer2`, axis `262143` of the library).  Here:

* `jetRootP j h b`: the model of the test on the jets noun `j` and the hot
  noun `h` (`getF` of `call.cole` = axis `126` of `j`, then `getF` of `h`,
  then the one-block straight `jsfStraight`);
* `JetsGood j h`: `call.cole` is a map whose values are rings and `h` is a
  map (`IsMap mugF`), what the pill needs not to crash;
* `jrP_enc`: on every encoded state with `JetsGood`, `jrP` is `jetRootP`
  (with `get_gate`, `has_gate`, `put_gate` on `layer2`);
* `JetRootLinkG`: `JetRootLinkR` on the states where the jets state the
  model's `+ska-poke` returns, with the old hot noun, has `JetsGood`;
  `jetRootLinkG_of`: it holds for every `A` with `A.jetRoot = jetRootP`;
* `jetRootLinkR_of_good`: `JetRootLinkR` itself from `SkaJetsGood` (the
  model's `+ska-poke` returns `JetsGood` jets on every state), which is FALSE
  for `anaArmP` on states whose hot noun is not a map, so the composition is
  restated per state: `pokeN_fullAt`, `pokeModel_fullAt` take the jet-root
  equation and `OptInAt` at the state only, and `pokeModel_fullG` takes
  `JetsGood` of the new jets at the state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## The model -/

/-- The blob `[~ ~ [%jsf func 0 u]]`. -/
def jsfBlob (b : Bell) (n : Ring) : Blob := ⟨[], [], Termin.jsf b 0 n⟩

/-- `[[%this ~] 1 (~(put by ~) 0 [~ ~ [%jsf func 0 u]])]`. -/
def jsfStraight (b : Bell) (n : Ring) : Straight (TreapMap mugF) :=
  ⟨NeedOrd.this, 1, HoonMap.put HoonMap.empty 0 (jsfBlob b n)⟩

/-- **The model of the jetted-root test**: the value of the root bell in
`call.cole` (axis `126` of the jets noun), and whether `jets-hot` has it. -/
def jetRootP (j h : Noun) (b : Bell) : Option (Straight (TreapMap mugF)) :=
  match (slot? 126 j).bind (getF mugF b.toNoun) with
  | some (Noun.cell _ u) => if getF mugF u h = some (A 0) then none else some (jsfStraight b (OptDec.ringDec u))
  | _ => none

/-- **What the test needs not to crash**: `call.cole` is a map whose values
are rings, and `jets-hot` is a map. -/
def JetsGood (j h : Noun) : Prop :=
  (∃ cm, slot? 126 j = some cm ∧ IsMap mugF cm ∧ ∀ k v, Get cm k v → ∃ n : Ring, v = n.toNoun) ∧ IsMap mugF h

/-! ## The pill's test on encoded states -/

theorem corLib_hoon : slot? 262143 corLib = some layer2 := by kernel_rfl

theorem enc_hoon (fl : Flags) (st : PSt) : slot? 2097151 (enc fl st) = some layer2 := by
  have h : slot? 2097151 (enc fl st) = slot? 262143 corLib := by simp [enc, nock_exec]
  rw [h, corLib_hoon]

theorem enc_cole (fl : Flags) (st : PSt) : slot? 7486 (enc fl st) = slot? 126 st.jets := by
  simp [enc, stNoun, longNoun, nock_exec]

theorem enc_hot (fl : Flags) (st : PSt) : slot? 118 (enc fl st) = some st.hot := by
  simp [enc, stNoun, nock_exec]

theorem getF_isSome {a : Noun} (h : IsMap mugF a) (k : Noun) : ∃ o, getF mugF k a = some o := by
  by_cases e : ∃ v, Get a k v
  · obtain ⟨v, hv⟩ := e
    exact ⟨_, getF_some h hv⟩
  · exact ⟨_, getF_none h fun v hv => e ⟨v, hv⟩⟩

theorem getRaw_enc (fl : Flags) (st : PSt) (func cm out : Noun) (hc : slot? 126 st.jets = some cm)
    (h : getF mugF func cm = some out) : getRaw (enc fl st) func = some out := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := get_gate layer2 hgc func cm out h
  simp [getRaw, byArmO, gateAt, slamG, enc_hoon, enc_cole, hc, by.arm_at, by_arm, by.get.arm_at, get_arm,
    nock_exec, hg]

theorem hasRaw_enc (fl : Flags) (st : PSt) (u out : Noun) (h : getF mugF u st.hot = some out) :
    hasRaw (enc fl st) u = some (loob (decide (out ≠ A 0))) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := has_gate layer2 hgc u st.hot out h
  simp [hasRaw, byArmO, gateAt, slamG, enc_hoon, enc_hot, by.arm_at, by_arm, by.has.arm_at, has_arm,
    nock_exec, hg]

theorem jsfStraight_blocks (b : Bell) (n : Ring) :
    HoonMap.toNoun Blob.toNoun (jsfStraight b n).blocks =
      C (C (A 0) (Blob.toNoun (jsfBlob b n))) (C (A 0) (A 0)) := by
  have h := putF_hoonMap Blob.toNoun (HoonMap.empty : TreapMap mugF Blob) 0 (jsfBlob b n)
  rw [HoonMap.toNoun_empty] at h
  simp only [putF, Option.some.injEq] at h
  exact h.symm

theorem putRaw_enc (fl : Flags) (st : PSt) (b : Bell) (n : Ring) :
    putRaw (enc fl st) b.toNoun n.toNoun = some (HoonMap.toNoun Blob.toNoun (jsfStraight b n).blocks) := by
  have hgm : GorIn mugF layer2 ∧ MorIn mugF layer2 := gorIn_morIn_layer2
  have hp := put_gate layer2 hgm (A 0) (Blob.toNoun (jsfBlob b n)) (A 0) _ rfl
  rw [jsfStraight_blocks]
  simp only [jsfBlob, Blob.toNoun, Termin.toNoun, listNoun] at hp ⊢
  simp [putRaw, byArmO, gateAt, slamG, enc_hoon, by.arm_at, by_arm, by.put.arm_at, put_arm, nock_exec, hp]

/-- **The pill's jetted-root test is `jetRootP`** on every encoded state
whose jet maps are maps. -/
theorem jrP_enc (fl : Flags) (st : PSt) (b : Bell) (hg : JetsGood st.jets st.hot) :
    jrP (enc fl st) b.toNoun = some ((jetRootP st.jets st.hot b).map Straight.toNoun) := by
  obtain ⟨⟨cm, hc, hm, hv⟩, hh⟩ := hg
  obtain ⟨o, ho⟩ := getF_isSome hm b.toNoun
  unfold jrP jetRootP
  rw [getRaw_enc fl st b.toNoun cm o hc ho, hc]
  simp only [Option.bind_some, ho]
  rcases o with _ | ⟨x, u⟩
  · rfl
  · -- the value is `[~ u]` with `u` a ring
    have hu : x = A 0 ∧ ∃ n : Ring, u = n.toNoun := by
      by_cases e : ∃ v, Get cm b.toNoun v
      · obtain ⟨v, hgv⟩ := e
        have := getF_some hm hgv
        rw [ho, Option.some.injEq] at this
        cases this
        exact ⟨rfl, hv _ _ hgv⟩
      · have := getF_none hm fun v hv' => e ⟨v, hv'⟩
        rw [ho] at this
        cases this
    obtain ⟨rfl, n, rfl⟩ := hu
    obtain ⟨o2, ho2⟩ := getF_isSome hh n.toNoun
    simp only [hasRaw_enc fl st n.toNoun o2 ho2, ho2, Option.bind_some, OptDec.ringDec_toNoun]
    by_cases e2 : o2 = A 0
    · subst e2
      simp [loob]
    · have hl : loob (decide (o2 ≠ A 0)) = A 0 := by simp [loob, e2]
      rw [hl, if_neg (fun h => e2 (Option.some.inj h))]
      simp only [if_true, Option.map_some]
      rw [putRaw_enc]
      simp [jsfStraight, Straight.toNoun, NeedOrd.toNoun]

/-! ## The link -/

section Link

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))

/-- **`JetRootLinkR` on the states where the new jets have `JetsGood`.** -/
def JetRootLinkG (jr : Noun → Noun → Option (Option Noun)) : Prop :=
  ∀ (st : PSt) s f r, Ar.skaPoke s f st.long st.jets st.hot = some r → JetsGood r.2.2.1 st.hot →
    jr (enc fl { st with long := r.2.1, jets := r.2.2.1 }) r.1.toNoun =
      some ((Ar.jetRoot r.2.2.1 st.hot r.1).map Straight.toNoun)

/-- **The link of the jetted-root test, proved**, for every `A` whose
`jetRoot` is `jetRootP`. -/
theorem jetRootLinkG_of (hA : Ar.jetRoot = jetRootP) : JetRootLinkG fl Ar jrP := by
  intro st s f r _ hg
  rw [hA]
  exact jrP_enc fl { st with long := r.2.1, jets := r.2.2.1 } r.1 hg

/-- The model's `+ska-poke` returns jets with `JetsGood` on every state (with
the old hot noun).  False for `anaArmP` with any `jetsOf` where the hot noun
is not a map, so it is used per state below. -/
def SkaJetsGood : Prop :=
  ∀ (st : PSt) s f r, Ar.skaPoke s f st.long st.jets st.hot = some r → JetsGood r.2.2.1 st.hot

theorem jetRootLinkR_of_good (hA : Ar.jetRoot = jetRootP) (hG : SkaJetsGood Ar) : JetRootLinkR fl Ar jrP :=
  fun st s f r e => jetRootLinkG_of fl Ar hA st s f r e (hG st s f r e)

/-! ## The composition per state -/

/-- **`pokeN_full` per state**: the jet-root equation and `OptInAt` at the
state only. -/
theorem pokeN_fullAt {Cls : Straight (TreapMap mugF) → Prop}
    (hS : SkaLink fl Ar skaP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP) (st : PSt) (s f₁ f₂ : Noun)
    (hJ : ∀ r, Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot = some r →
      jrP (enc fl { st with long := r.2.1, jets := r.2.2.1 }) r.1.toNoun =
        some ((Ar.jetRoot r.2.2.1 st.hot r.1).map Straight.toNoun))
    (hIn : OptInAt Ar Cls st s (C f₁ f₂)) :
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s (C f₁ f₂))).map fun r => C r.1.toNoun r.2 := by
  rw [fullBranchIs fl st s f₁ f₂, liftPoke_enc_fl]
  unfold pillFull
  rw [hS]
  simp only [pokeS]
  cases e1 : Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [hJ r e1]
    simp only [Option.bind_some]
    cases e2 : Ar.jetRoot r.2.2.1 st.hot r.1 with
    | some out => simp [Prod.toNoun]
    | none =>
      simp only [Option.map_none]
      unfold compileStep
      rw [hC]
      cases e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some, if_true]
        rw [hM]
        cases e4 : compiledMono Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          rw [hO p.1 (hIn r q p e1 e2 e3 e4)]
          simp [Prod.toNoun]

/-- **`pokeModel` on every `%full` at a state**, with the links of
`+ska-poke`, `+scc-of`, `+compiled-mono` and of `+optimize` on a class, the
jetted-root test proved (`A.jetRoot = jetRootP`), and two facts of the model
at the state: the jets the model's `+ska-poke` returns have `JetsGood` with
the state's hot noun, and `OptInAt`. -/
theorem pokeModel_fullG {Cls : Straight (TreapMap mugF) → Prop} (hJA : Ar.jetRoot = jetRootP)
    (hS : SkaLink fl Ar skaP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (s f : Noun)
    (hG : ∀ r, Ar.skaPoke s f st.long st.jets st.hot = some r → JetsGood r.2.2.1 st.hot)
    (hIn : OptInAt Ar Cls st s f) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    exact pokeN_fullAt fl Ar hS hC hM hO st s f₁ f₂
      (fun r e => jetRootLinkG_of fl Ar hJA st s (C f₁ f₂) r e (hG r e)) hIn

end Link

end Compiler
end Formalization
