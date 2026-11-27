import lemmas.Compiler.CompRunDirectP

/-!
# The direct call of the case `%2` of `+run`: `+callee-sure` and `+callee-need`

README Gaps 19.  Two fields of `CallNoun` (the nouns the call reads of the
rest of the compiler) become facts about the context and `cache`:

* `csu_gate`: `+callee-sure` (door arm `4060`) is `env.sure b` when
  `sure.cache` (axis `31` of `cache`) holds `b`'s entry `env.sure b`, or no
  entry and `env.sure b` is `[%none ~]` (`SureNoun`; `sureNoun_of_map` on a
  map noun).
* `cne_read`: `+callee-need` (door arm `221180`) with no ring (`rin` is `~`,
  so `j` is `~`), in its read-only cases (`NeedRead`): `b` in `scc` (axis
  `12` of the context) with its need in `map-local` (axis `110`) or else in
  `top` (axis `222`); `b` not in `scc` with an entry in `nary.cache` (axis
  `2` of `cache`, `+callee-compiled`, door arm `13791`, `ccc_nary`).  The
  state is unchanged.  The case left out is `b` not in `scc` and not in
  `nary.cache`: `+callee-compiled` then runs `+scc-of` and
  `+compile-scc-in` and writes `sccs` and `cache` (`cccBig`, not linked).
* `CallNounR`, `callNoun_of_r`, `comp_run_n2_callR`: the call as
  `CompRunAtM` with these facts in place of the gates' runs.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## `+callee-sure` -/

theorem csu_bat : csuBat = C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 1531)
    (C (A 10) (C (C (A 6) (C (A 0) (A 0x3efef))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))))) (C (A 0) (A 2))))))) := by
  kernel_rfl

/-- **What `+callee-sure` reads**: `sure.cache` (axis `31` of `cache`) has
the entry `env.sure b` for `b`, or no entry and `env.sure b` is `[%none ~]`. -/
def SureNoun (env : CallEnv) (b : Bell) (x : GenRest) : Prop :=
  ∃ S, slot? 31 x.cache = some S ∧
    (getF mugF b.toNoun S = some (C (A 0) (env.sure b).toNoun) ∨
      (getF mugF b.toNoun S = some (A 0) ∧ env.sure b = NeedOrd.none))

/-- `SureNoun` on a map noun: the entry of `b`, if any, is `env.sure b`, and
`env.sure b` is `[%none ~]` when there is none. -/
theorem sureNoun_of_map {env : CallEnv} {b : Bell} {x : GenRest} {S : Noun} (hS : slot? 31 x.cache = some S)
    (hm : IsMap mugF S) (hv : ∀ v, Get S b.toNoun v → v = (env.sure b).toNoun)
    (hn : (∀ v, ¬ Get S b.toNoun v) → env.sure b = NeedOrd.none) : SureNoun env b x := by
  refine ⟨S, hS, ?_⟩
  by_cases h : ∃ v, Get S b.toNoun v
  · obtain ⟨v, hg⟩ := h
    exact Or.inl (by rw [getF_some hm hg, hv v hg])
  · have h' : ∀ v, ¬ Get S b.toNoun v := fun v hg => h ⟨v, hg⟩
    exact Or.inr ⟨getF_none hm h', hn h'⟩

/-- **`+callee-sure`** (door arm `4060`): `(~(gut by sure.cache.gen) b
[%none ~])` is `env.sure b`. -/
theorem csu_gate (hc : CompIn ctx) (env : CallEnv) (b : Bell) (x : GenRest) (hs : SureNoun env b x)
    (g : Gen (TreapMap mugF)) :
    nock (C csuBat (C b.toNoun (compCore g x ctx))) csuBat = some (env.sure b).toNoun := by
  obtain ⟨S, hS, hg⟩ := hs
  have hgut : nock (C by.gut.battery (C (C b.toNoun (C (A 0x656e6f6e) (A 0))) (C by.battery (C S layer2))))
      by.gut.battery = some (env.sure b).toNoun := by
    rcases hg with h | ⟨h, hn⟩
    · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun
        (C (A 0x656e6f6e) (A 0)) S _ h (Or.inr ⟨_, rfl⟩)
      simpa using this
    · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun
        (C (A 0x656e6f6e) (A 0)) S _ h (Or.inl rfl)
      rw [hn]
      simpa [NeedOrd.toNoun, Tag.none] using this
  conv => lhs; rw [csu_bat]
  simp [nock_exec, compCore, genNoun, hc, hS, by_arm, by.arm_at, by.gut.arm_at, gut_arm, hgut]

/-! ## `+callee-compiled` (door arm `13791`): the hit in `nary.cache` -/

/-- The battery of `+callee-compiled`. -/
noncomputable def cccBat : Noun := (slot? 29 ((slot? 13791 comp.door).getD (A 0))).getD (A 0)

/-- Its branch on a miss in `nary.cache`: `+scc-of`, `+compile-scc-in`, the
need of the callee in what it compiled (not linked). -/
noncomputable def cccBig : Noun := (slot? 958 ((slot? 13791 comp.door).getD (A 0))).getD (A 0)

theorem ccc_at : slot? 13791 comp.door
    = some (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) cccBat) (C (A 0) (A 1))))) := by
  kernel_rfl

theorem ccc_bat : cccBat = C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff))))
    (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7dfc))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2)
    (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))
    (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))
      (C cccBig (C (C (A 0) (A 10)) (C (A 0) (A 62))))))) := by
  kernel_rfl

/-- **`+callee-compiled` on a hit in `nary.cache`** (axis `2` of `cache`):
`[need.u.s gen]`, the state unchanged. -/
theorem ccc_nary (hc : CompIn ctx) (b : Bell) (x : GenRest) {N u nd : Noun} (hN : slot? 2 x.cache = some N)
    (hg : getF mugF b.toNoun N = some (C (A 0) u)) (hu : slot? 2 u = some nd) (g : Gen (TreapMap mugF)) :
    nock (C cccBat (C b.toNoun (compCore g x ctx))) cccBat = some (C nd (genNoun g x)) := by
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun N _ hg
  conv => lhs; rw [ccc_bat]
  simp [nock_exec, compCore, genNoun, hc, hN, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hu]

/-! ## `+callee-need` (door arm `221180`) -/

theorem cne_bat : cneBat = C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9)
    (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fabe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 0x7fffff)))) (C (A 9)
    (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103)
    (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 4086))) (C (A 0) (A 2))))))))))))
    (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))
    (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 381) (C (A 10)
    (C (C (A 6) (C (A 0) (A 2044))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62)))
    (C (A 0) (A 2)))))))) (C (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff))))
    (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fee))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1)
    (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9)
    (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (C (A 0) (A 126)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))))) (C (A 0) (A 2))))))))
    (C (A 0) (A 10))))))) (C (A 0) (A 126))) (C (A 8) (C (C (A 9) (C (A 0x55df) (C (A 0) (A 31)))) (C (A 9) (C (A 2)
    (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2))))))))))) (C (C (A 0) (A 5)) (C (A 0) (A 126))))))))) := by
  kernel_rfl

/-- **The read-only cases of `+callee-need` with no ring**: `b` in `scc`
(axis `12` of the context) with an entry in `map-local` (axis `110`, the
field `need` of the `straight`), or no entry there and the `gut` of `top`
(axis `222`, `[%none ~]` when absent); `b` not in `scc` with an entry in
`nary.cache` (`+callee-compiled`). -/
inductive NeedRead (ctx : Noun) (x : GenRest) (b : Bell) (nb : NeedOrd) : Prop where
  | loc {S ML u : Noun} : slot? 12 ctx = some S → hasInF mugF b.toNoun S = some true → slot? 110 ctx = some ML →
      getF mugF b.toNoun ML = some (C (A 0) u) → slot? 2 u = some nb.toNoun → NeedRead ctx x b nb
  | top {S ML TP : Noun} : slot? 12 ctx = some S → hasInF mugF b.toNoun S = some true → slot? 110 ctx = some ML →
      getF mugF b.toNoun ML = some (A 0) → slot? 222 ctx = some TP →
      (getF mugF b.toNoun TP = some (C (A 0) nb.toNoun) ∨ (getF mugF b.toNoun TP = some (A 0) ∧ nb = NeedOrd.none)) →
      NeedRead ctx x b nb
  | nary {S N u : Noun} : slot? 12 ctx = some S → hasInF mugF b.toNoun S = some false → slot? 2 x.cache = some N →
      getF mugF b.toNoun N = some (C (A 0) u) → slot? 2 u = some nb.toNoun → NeedRead ctx x b nb

/-- **`+callee-need` in its read-only cases, with no ring**: `nb` and the
state unchanged. -/
theorem cne_read (h7 : slot? 7 ctx = some compK) (b : Bell) (nb : NeedOrd) (x : GenRest)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hr : NeedRead ctx x b nb) (g : Gen (TreapMap mugF)) :
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x)) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨cole, hcl, hgc⟩ := hcole
  obtain ⟨jh, hjh⟩ := hhot
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole (A 0) hgc
  cases hr with
  | @loc S ML u hS hh hML hg hu =>
    have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S true hh
    have hgl := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun ML _ hg
    conv => lhs; rw [cne_bat]
    simp [nock_exec, compCore, genNoun, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
      biff.arm_at, biff_gate_nil, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hML, hgl, hu]
  | @top S ML TP hS hh hML hg hTP hgt' =>
    have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S true hh
    have hgl := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun ML _ hg
    have hgut : nock (C by.gut.battery (C (C b.toNoun (C (A 0x656e6f6e) (A 0))) (C by.battery (C TP layer2))))
        by.gut.battery = some nb.toNoun := by
      rcases hgt' with h | ⟨h, hn⟩
      · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun
          (C (A 0x656e6f6e) (A 0)) TP _ h (Or.inr ⟨_, rfl⟩)
        simpa using this
      · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun
          (C (A 0x656e6f6e) (A 0)) TP _ h (Or.inl rfl)
        rw [hn]
        simpa [NeedOrd.toNoun, Tag.none] using this
    conv => lhs; rw [cne_bat]
    simp [nock_exec, compCore, genNoun, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
      biff.arm_at, biff_gate_nil, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hML, hgl, hTP,
      by.gut.arm_at, gut_arm, hgut]
  | @nary S N u hS hh hN hg hu =>
    have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S false hh
    have hcc := ccc_nary hc b x hN hg hu g
    have hD := ccc_at
    simp only [compCore] at hcc
    conv => lhs; rw [cne_bat]
    generalize cccBat = CB at hcc hD
    simp only [compCore]
    generalize comp.door = Dr at hcc hD ⊢
    simp [nock_exec, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
      biff.arm_at, biff_gate_nil, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hD, hcc]

/-! ## The call with these facts -/

/-- **What the call reads, as facts on the context and `cache`**: no ring
(`cole`), `jets-hot` there (`hot`), `+callee-need` in a read-only case
(`need`), `sure.cache` (`sure`), and the push of `sof` `|` (`sof`, with
`b-sur` the noun of `env.sure b`). -/
structure CallNounR (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (x : GenRest) : Prop where
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  hot : ∃ jh, slot? 54 ctx = some jh
  need : NeedRead ctx x b nb
  sure : SureNoun env b x
  sof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj (A 1) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some (A 1)

theorem callNoun_of_r (h7 : slot? 7 ctx = some compK) {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {b : Bell}
    {nb : NeedOrd} {x : GenRest} (h : CallNounR env msup ctx p q b nb x) :
    CallNoun msup ctx p q b nb (env.sure b).toNoun x :=
  ⟨h.cole, h.hot, cne_read h7 b nb x h.cole h.hot h.need, csu_gate (comp_ctx_pill ctx h7).1 env b x h.sure, h.sof⟩

/-- **The call as `CompRunAtM` with `CallNounR`** (README Gaps 19):
`comp_run_n2_callM` with `+callee-need` and `+callee-sure` linked. -/
theorem comp_run_n2_callR (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) {region : List Nat} (P : PartL env msup ctx p region)
    (Q : PartL env msup ctx q region) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd) (goal : CGoalL CSet)
    (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false) :
    CompRunAtM env msup ctx (CallNounR env msup ctx p q b nb) (Nomm.n2 p q (some (b, Option.none))) goal region g :=
  fun x hx hr => comp_run_n2_callM h7 hcode env msup p q P Q b hcd nb goal g hinv hdr hri hnb hsof x hx
    ⟨_, callNoun_of_r h7 hr⟩

end Compiler
end Formalization
