import lemmas.Compiler.OptLinkAlJReg

/-!
# `+alias`: `param-info` (phase 3 of the plan, README Gaps 13)

```hoon
  ++  param-info
    |=  ins=(list (unit info-reg))
    ^-  info-reg
    =/  have=(list info-reg)  (murn ins same)
    ?~  have  *info-reg
    =/  joined  (roll t.have |:([a=*info-reg b=i.have] (join-reg a b)))
    ?:  =((lent have) (lent ins))  joined
    joined(hed-of ~, tel-of ~, has-hed ~, has-tel ~, dec-of ~)
```

The body is cut by `tools/gen/optlink.py alias` into `alPIMurn` (`have`),
`alPIRoll` (`joined`, with the gate `alPIGate`), `alPILen` (the test) and
`alPIEdit` (the cleared facts).

* `UInfoRel n o`: the noun `n` of a `(unit info-reg)` holds the optional fact
  `o` (`~` for `none`, `[~ N]` with `InfoRel N x` for `some x`).
* `al_pinfo`: **`param-info` of a list of related units is related to
  `paramInfo`** of the model's list, in the core of the `|^` of `+alias`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- A `(unit info-reg)` noun holds an optional fact. -/
def UInfoRel (n : Noun) : Option Opt.InfoReg → Prop
  | none => n = A 0
  | some x => ∃ N, n = C (A 0) N ∧ InfoRel N x

/-- The subject of the body of `param-info`. -/
def alPIS (insN G Y Z : Noun) : Noun := C alPInfoB (C insN (alCtx alBat G Y Z))

/-- `(murn ins same)` on related units: the related facts that are there. -/
theorem pi_have : ∀ (L : List (Noun × Option Opt.InfoReg)), (∀ p ∈ L, UInfoRel p.1 p.2) →
    ∃ H : List (Noun × Opt.InfoReg), (∀ p ∈ H, InfoRel p.1 p.2) ∧
      (L.map Prod.fst).filterMap unitVal = H.map Prod.fst ∧ (L.map Prod.snd).filterMap id = H.map Prod.snd
  | [], _ => ⟨[], by simp, rfl, rfl⟩
  | (n, o) :: L, h => by
    obtain ⟨H, hH, h1, h2⟩ := pi_have L (fun p hp => h p (by simp [hp]))
    have h0 := h (n, o) (by simp)
    cases o with
    | none =>
      simp only [UInfoRel] at h0
      subst h0
      exact ⟨H, hH, by simp only [List.map_cons, List.filterMap_cons, unitVal]; exact h1, by simp [h2]⟩
    | some x =>
      obtain ⟨N, rfl, hN⟩ := h0
      refine ⟨(N, x) :: H, ?_, by simp [unitVal, h1], by simp [h2]⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hN
      · exact hH p hp

theorem pi_murn (L : List Noun) (hL : ∀ x ∈ L, x = A 0 ∨ ∃ h v, x = C h v) (G Y Z : Noun) :
    nock (alPIS (listN L) G Y Z) alPIMurn = some (listN (L.filterMap unitVal)) := by
  have hm := murn_gate layer2 homoIn_layer2 (C (A 0) (A 6)) (A 0) layer2 (fun x => x) L
    (fun x hx => ⟨by simp [nock_exec], hL x hx⟩)
  have hs := same_at
  have hma : ∀ c, nock c murn.arm = some (C murn.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) c)) := by
    intro c; nock_open murn.arm; simp only [nock_exec]
  have hL2 := optC_layer2
  unfold alPIS alCtx
  generalize optC = OC at hL2
  generalize alPInfoB = P
  generalize alBat = X
  simp [nock_exec, alPIMurn, hL2, murn.arm_at, hma, hs, sameArm, hm]

/-- The gate of the `+roll`: `(join-reg a b)`. -/
theorem pi_gate (G Y Z hv insN : Noun) {Nx Na : Noun} {x a : Opt.InfoReg} (hx : InfoRel Nx x)
    (ha : InfoRel Na a) :
    ∃ N, nock (C alPIGate (C (C Nx Na) (C hv (alPIS insN G Y Z)))) alPIGate = some N ∧
      InfoRel N (Opt.joinReg x a) := by
  obtain ⟨N, hN, hR⟩ := al_jreg alBat G Y Z hx ha
  refine ⟨N, ?_, hR⟩
  obtain ⟨R, hX⟩ : ∃ R, alBat = C (C (A 8) (C (C (A 1) alJRegBunt) (C (C (A 1) alJRegB) (C (A 0) (A 1))))) R :=
    ⟨_, rfl⟩
  unfold alJRS alCtx at hN
  unfold alPIS alCtx
  rw [hX] at hN ⊢
  generalize optC = OC at hN ⊢
  generalize alPInfoB = P
  simp [nock_exec, alPIGate, hN]

theorem pi_roll (G Y Z insN : Noun) (h : Noun × Opt.InfoReg) (t : List (Noun × Opt.InfoReg))
    (hh : InfoRel h.1 h.2) (ht : ∀ p ∈ t, InfoRel p.1 p.2) :
    ∃ N, nock (C (C h.1 (listN (t.map Prod.fst))) (alPIS insN G Y Z)) alPIRoll = some N ∧
      InfoRel N (t.foldl (fun s p => Opt.joinReg p.2 s) h.2) := by
  have hf : ∀ p ∈ t, ∀ s N s', InfoRel N s → some (Opt.joinReg p.2 s) = some s' →
      ∃ N', nock (C alPIGate (C (C p.1 N) (C (C h.1 (listN (t.map Prod.fst))) (alPIS insN G Y Z))))
        alPIGate = some N' ∧ InfoRel N' s' := by
    intro p hp s N s' hN e
    cases e
    exact pi_gate G Y Z _ insN (ht p hp) hN
  obtain ⟨N, hN, hR⟩ := roll_gate_rel Prod.fst InfoRel (fun p s => some (Opt.joinReg p.2 s)) layer2
    alPIGate (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) alJImmsBunt))))))
    (C (C h.1 (listN (t.map Prod.fst))) (alPIS insN G Y Z)) t h.2 h.1 _ hf hh
    (foldlM_some (fun s p => Opt.joinReg p.2 s) t h.2)
  refine ⟨N, ?_, hR⟩
  have hL2 := optC_layer2
  unfold alPIS alCtx at hN ⊢
  generalize optC = OC at hL2 hN ⊢
  generalize alPInfoB = P at hN ⊢
  generalize alBat = X at hN ⊢
  generalize listN (t.map Prod.fst) = T at hN ⊢
  simp [nock_exec, alPIRoll, hL2, roll.arm_at, roll_arm, hN]

theorem pi_len (G Y Z N : Noun) (hv ins : List Noun) :
    nock (C N (C (listN hv) (alPIS (listN ins) G Y Z))) alPILen
      = some (flag (decide (hv.length = ins.length))) := by
  have h1 := lent_gate layer2 hv
  have h2 := lent_gate layer2 ins
  have hL2 := optC_layer2
  unfold alPIS alCtx
  generalize optC = OC at hL2
  generalize alPInfoB = P
  generalize alBat = X
  by_cases e : hv.length = ins.length <;>
    simp [nock_exec, alPILen, hL2, lent.arm_at, lent_arm, h1, h2, eqCode, flag, e]

theorem pi_edit (x : Opt.InfoReg) (lb : Bool) (hs ts S : Noun) :
    nock (C (infoN x lb hs ts) S) alPIEdit =
      some (infoN { x with hedOf := [], telOf := [], hasHed := none, hasTel := none, decOf := none }
        lb (A 0) (A 0)) := by
  unfold infoN
  simp [nock_exec, alPIEdit, unitNoun_none]

/-- **`param-info`** of a list of units related to the model's list is related to `paramInfo`. -/
theorem al_pinfo (G Y Z : Noun) (L : List (Noun × Option Opt.InfoReg)) (hL : ∀ p ∈ L, UInfoRel p.1 p.2) :
    ∃ N, nock (alPIS (listN (L.map Prod.fst)) G Y Z) alPInfoB = some N ∧
      InfoRel N (Opt.paramInfo (L.map Prod.snd)) := by
  obtain ⟨H, hH, h1, h2⟩ := pi_have L hL
  have hu : ∀ x ∈ L.map Prod.fst, x = A 0 ∨ ∃ h v, x = C h v := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have := hL p hp
    generalize p.2 = o at this
    cases o with
    | none => exact Or.inl this
    | some y => obtain ⟨N, e, -⟩ := this; exact Or.inr ⟨_, _, e⟩
  have fm := pi_murn _ hu G Y Z
  rw [h1] at fm
  unfold Opt.paramInfo
  rw [h2]
  conv => enter [1, N, 1]; rw [show alPInfoB = C (A 8) (C alPIMurn (C (A 6) (C (C (A 5) (C (C (A 1) (A 0))
    (C (A 0) (A 2)))) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) alJImmsBunt)))))))
    (C (A 8) (C alPIRoll (C (A 6) (C alPILen (C (C (A 0) (A 2)) alPIEdit))))))))) from rfl]
  cases H with
  | nil =>
    refine ⟨infoN {} false (A 0) (A 0), ?_, false, A 0, A 0, rfl, sawRel_nil, sawRel_nil, rfl⟩
    simp [nock_exec, fm]
    rfl
  | cons h t =>
    obtain ⟨N, hN, hR⟩ := pi_roll G Y Z (listN (L.map Prod.fst)) h t (hH h (by simp))
      (fun p hp => hH p (by simp [hp]))
    have hl := pi_len G Y Z N ((h :: t).map Prod.fst) (L.map Prod.fst)
    simp only [List.map_cons, listN_cons] at hl
    have hlen : ((h :: t).map Prod.fst).length = (L.map Prod.fst).length ↔
        (h.2 :: t.map Prod.snd).length = (L.map Prod.snd).length := by simp
    simp only [List.map_cons]
    rw [List.foldl_map]
    by_cases e : (h.2 :: t.map Prod.snd).length = (L.map Prod.snd).length
    · refine ⟨N, ?_, ?_⟩
      · simp only [List.map_cons, listN_cons] at fm
        have e' : t.length + 1 = L.length := by simpa using e
        simp [nock_exec, fm, hN, hl, e', flag]
      · simpa [e] using hR
    · rw [if_neg e]
      obtain ⟨lb, hs, ts, rfl, -, -, hlb⟩ := hR
      refine ⟨_, ?_, lb, A 0, A 0, rfl, sawRel_nil, sawRel_nil, ?_⟩
      · simp only [List.map_cons, listN_cons] at fm
        have e' : ¬ t.length + 1 = L.length := by simpa using e
        simp [nock_exec, fm, hN, hl, e', flag, pi_edit]
      · exact hlb

end Compiler
end Formalization
