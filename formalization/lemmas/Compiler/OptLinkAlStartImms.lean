import lemmas.Compiler.OptLinkAlStartInfo

/-!
# `+alias`: the immediates at the start (phase 10 of the plan, README Gaps 13)

```hoon
  =/  imms=(jug * @uvre)
    ?~  pre  ~
    %+  roll  t.pre
    |=  [o1=@uwoo acc=_(~(got by imms.gen) i.pre)]
    (join-imms acc (~(got by imms.gen) o1))
```

* `imms_got`: `(~(got by imms.gen) o)` on an `ImmsStoreRel` map.
* `al_img`: the gate of the `+roll`, by `al_jimms`.
* `al_imms`: **`imms` is `ImmsRel` to `aliasStartImms g pre`**, on the
  Hoon's `pre`; `aliasStartImms_perm` moves it to `g.rev o` (`ImmsEq`, under
  which `ImmsRel` holds: `immsRel_of_immsEq`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `(~(got by imms.gen) o)`. -/
theorem imms_got {IMMS : Noun} {m : Nat → Option Opt.AImms} (h : ImmsStoreRel IMMS m) {o : Nat}
    {x : Opt.AImms} (hx : m o = some x) :
    ∃ V, nock (C by.got.battery (C (A o) (C by.battery (C IMMS layer2)))) by.got.battery = some V ∧
      ImmsRel V x := by
  obtain ⟨V, hV⟩ := h.2.2 o x hx
  obtain ⟨o', x', e, hx', hr⟩ := h.2.1 _ _ hV
  cases e
  rw [hx] at hx'
  cases hx'
  exact ⟨V, got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _
    (getF_some h.1 hV), hr⟩

/-- `ImmsRel` moves along `ImmsEq`. -/
theorem immsRel_of_immsEq {N : Noun} {a b : Opt.AImms} (h : ImmsRel N a) (e : Opt.ImmsEq a b) : ImmsRel N b := by
  refine ⟨h.1, fun k v hg => ⟨sawRel_congr (h.2.1 k v hg).1 (e k), (h.2.1 k v hg).2⟩, fun k hk => h.2.2 k ?_⟩
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hk
  exact List.ne_nil_of_mem ((e k x).2 hx)

theorem immsRel_nil : ImmsRel (A 0) (fun _ => []) :=
  ⟨IsMap.nil, fun _ _ h => absurd h Get_atom, fun _ h => absurd rfl h⟩

/-- The arm `join-imms` of the battery. -/
def alJMArm : Noun := C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) alJImmsB) (C (A 0) (A 1))))

theorem alBat_jm : ∃ a1 a2 a3 a5, alBat = C a1 (C a2 (C a3 (C alJMArm (C a5 alWalk)))) :=
  ⟨_, _, _, _, rfl⟩

/-- **The gate of the `+roll`**: `(join-imms acc (~(got by imms.gen) o1))`. -/
theorem al_img {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (NA BL REV T X Y : Noun)
    (o1 : Nat) (N : Noun) (acc : Opt.AImms) (hN : ImmsRel N acc) (i1 : Opt.AImms) (h1 : g.imms o1 = some i1) :
    ∃ N', nock (C alImG (C (C (A o1) N) (C X (C Y (alWS GEN NA BL REV T))))) alImG = some N' ∧
      ImmsRel N' (Opt.joinImmsA acc i1) := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR⟩ := hg
  obtain ⟨V, hV, hVr⟩ := imms_got hM h1
  obtain ⟨N', hj, hN'⟩ := al_jimms alBat (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML R
    (flag g.folded)) alBodyCut (C NA (C BL (C REV T))) hN hVr
  refine ⟨N', ?_, hN'⟩
  obtain ⟨a1, a2, a3, a5, hX⟩ := alBat_jm
  unfold alJMArm at hX
  have hL := optC_layer2
  unfold alCtx at hj
  unfold alWS
  rw [hX] at hj ⊢
  unfold genN at hj ⊢
  generalize optC = OC at hL hj
  simp [nock_exec, alImG, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hV, hj]

/-- **`imms`**: the `join-imms` of the immediates of `pre`, the model's
`aliasStartImms` on the Hoon's list. -/
theorem al_imms {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (NA BL REV T INFO : Noun)
    (pre : List Nat) (m : Opt.AImms) (hm : Opt.aliasStartImms g pre = some m) :
    ∃ N, nock (C INFO (C (listNoun A pre) (alWS GEN NA BL REV T))) alImms = some N ∧ ImmsRel N m := by
  cases pre with
  | nil =>
    simp only [Opt.aliasStartImms, Option.some.injEq] at hm
    subst hm
    refine ⟨A 0, ?_, immsRel_nil⟩
    rw [alImms_cut]
    simp [nock_exec, alImmsC, listNoun]
  | cons p t =>
    simp only [Opt.aliasStartImms] at hm
    cases e0 : g.imms p with
    | none => rw [e0] at hm; cases hm
    | some m0 =>
      rw [e0] at hm
      simp only [Option.bind_some] at hm
      have hg' := hg
      obtain ⟨OLD, INFO', IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR⟩ := hg'
      obtain ⟨V0, hV0, hV0r⟩ := imms_got hM e0
      obtain ⟨N, hroll, hN⟩ := roll_gate_rel A ImmsRel
        (fun o1 acc => (g.imms o1).map fun i1 => Opt.joinImmsA acc i1)
        layer2 alImG (A 0) (C INFO (C (listNoun A (p :: t)) (alWS (genN (HoonMap.toNoun Blob.toNoun g.new) OLD
          INFO' IMMS LOC IMML R (flag g.folded)) NA BL REV T))) t m0 V0 m
        (fun o1 _ s N s' hs e => by
          cases e1 : g.imms o1 with
          | none => rw [e1] at e; cases e
          | some i1 =>
            rw [e1] at e
            cases e
            exact al_img hg NA BL REV T _ _ o1 N s hs i1 e1)
        hV0r hm
      refine ⟨N, ?_, hN⟩
      rw [← listNoun_map_listN] at hroll
      simp only [listNoun] at hroll
      have hL := optC_layer2
      unfold alWS at hroll ⊢
      unfold genN at hroll ⊢
      generalize optC = OC at hL hroll
      rw [alImms_cut]
      simp [nock_exec, alImmsC, listNoun, hL, roll.arm_at, roll_arm, by.arm_at, by_arm, by.got.arm_at, got_arm,
        hV0, hroll]

end Compiler
end Formalization
