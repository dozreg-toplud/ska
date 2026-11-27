import lemmas.Compiler.OptLinkAlStartUn

/-!
# `+alias`: the facts at the start, the entry and the join (phase 9 of the plan, README Gaps 13)

```hoon
  =^  info=(map @uvre info-reg)  gen
    ?~  pre
      =|  info=(map @uvre info-reg)
      =/  r=@uvre  0v0
      |-  ^+  [info gen]
      ?:  =(r n-args)  [info gen]
      =.  info  (~(put by info) r *info-reg)
      $(r `@uvre`+(r))
    :_  gen
    =/  info=(map @uvre info-reg)
      %+  roll  t.pre
      |=  [o1=@uwoo acc=_(~(got by info.gen) i.pre)]
      (join-info acc (~(got by info.gen) o1))
    ...
```

* `info_got`: `(~(got by info.gen) o)` on an `InfoStoreRel` map.
* `infoMapRel_put`: `+put:by` of a related fact.
* `infoMapRel_of_aInfoEq`: `InfoMapRel` moves along `AInfoEq`, so a result
  on the Hoon's order of `pre` holds of the model's (`aliasStart_perm`).
* `al_ent`: **the trap of the entry block** gives `entryInfo n-args`.
* `al_jng`, `al_jnroll`: **the `+roll` of `join-info` over `t.pre`** is the
  model's `foldlM` of `joinInfoA`, from the facts of `i.pre`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Maps of facts -/

/-- `(~(got by info.gen) o)`. -/
theorem info_got {INFO : Noun} {m : Nat → Option Opt.AInfo} (h : InfoStoreRel INFO m) {o : Nat}
    {x : Opt.AInfo} (hx : m o = some x) :
    ∃ V, nock (C by.got.battery (C (A o) (C by.battery (C INFO layer2)))) by.got.battery = some V ∧
      InfoMapRel V x := by
  obtain ⟨V, hV⟩ := h.2.2 o x hx
  obtain ⟨o', x', e, hx', hr⟩ := h.2.1 _ _ hV
  cases e
  rw [hx] at hx'
  cases hx'
  exact ⟨V, got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _
    (getF_some h.1 hV), hr⟩

/-- `+put:by` of a related fact under a register. -/
theorem infoMapRel_put {N v : Noun} {m : Opt.AInfo} {x : Opt.InfoReg} (h : InfoMapRel N m) (hv : InfoRel v x)
    (k : Nat) :
    ∃ N', nock (C by.put.battery (C (C (A k) v) (C by.battery (C N layer2)))) by.put.battery = some N' ∧
      InfoMapRel N' (Opt.updA m k (some x)) := by
  obtain ⟨out, hp, ho, hg⟩ := putF_spec mugF N (A k) v h.1
  refine ⟨out, put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, fun kn w hw => ?_,
    fun r y hy => ?_⟩
  · rcases (hg kn w).1 hw with ⟨rfl, rfl⟩ | ⟨hne, hw'⟩
    · exact ⟨k, x, rfl, by simp [Opt.updA], hv⟩
    · obtain ⟨r, y, rfl, hy, hr⟩ := h.2.1 _ _ hw'
      have : r ≠ k := fun e => hne (by rw [e])
      exact ⟨r, y, rfl, by simp [Opt.updA, this, hy], hr⟩
  · by_cases e : r = k
    · subst e; exact ⟨v, (hg _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · have hy' : m r = some y := by simpa [Opt.updA, e] using hy
      obtain ⟨w, hw⟩ := h.2.2 r y hy'
      exact ⟨w, (hg _ _).2 (Or.inr ⟨fun h' => e (Noun.atom.inj h'), hw⟩)⟩

/-- `InfoMapRel` moves along `AInfoEq`. -/
theorem infoMapRel_of_aInfoEq {N : Noun} {a b : Opt.AInfo} (h : InfoMapRel N a) (e : Opt.AInfoEq a b) :
    InfoMapRel N b := by
  refine ⟨h.1, fun k v hg => ?_, fun r y hy => ?_⟩
  · obtain ⟨r, x, rfl, hx, hr⟩ := h.2.1 k v hg
    have er := e r
    rw [hx] at er
    cases eb : b r with
    | none => rw [eb] at er; exact absurd er (by simp)
    | some y =>
      rw [eb] at er
      exact ⟨r, y, rfl, eb, infoRel_of_infoEq hr er⟩
  · have er := e r
    rw [hy] at er
    cases ea : a r with
    | none => rw [ea] at er; exact absurd er (by simp)
    | some x => exact h.2.2 r x ea

/-! ## The entry block -/

/-- The noun of `*info-reg`. -/
theorem infoRel_buntN : InfoRel (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))
    ({} : Opt.InfoReg) :=
  ⟨false, A 0, A 0, rfl, sawRel_nil, sawRel_nil, rfl⟩

/-- **The trap of the entry block**: from `r` up to `n-args`, `*info-reg`
under each register; the product is `[info gen]` with `info` the facts
`entryInfo n-args`. -/
theorem al_ent (PRE GEN BL REV TOPO : Noun) (nargs : Nat) :
    ∀ (n r : Nat), r + n = nargs → ∀ (I : Noun), InfoMapRel I (fun k => if k < r then some {} else none) →
      ∃ I', nock (C alEnT (C (A r) (C I (C PRE (alWS GEN (A nargs) BL REV TOPO))))) alEnT = some (C I' GEN) ∧
        InfoMapRel I' (Opt.entryInfo nargs) := by
  intro n
  induction n with
  | zero =>
    intro r hr I hI
    subst hr
    refine ⟨I, ?_, hI⟩
    unfold alWS
    nock_open alEnT
    simp [nock_exec]
  | succ n ih =>
    intro r hr I hI
    obtain ⟨I1, hp, hI1⟩ := infoMapRel_put hI infoRel_buntN r
    have hI1' : InfoMapRel I1 (fun k => if k < r + 1 then some {} else none) := by
      refine ⟨hI1.1, fun k v hg => ?_, fun q y hy => hI1.2.2 q y ?_⟩
      · obtain ⟨q, x, e, hx, hq⟩ := hI1.2.1 k v hg
        refine ⟨q, x, e, ?_, hq⟩
        by_cases e1 : q = r
        · subst e1; simpa [Opt.updA] using hx
        · have : (q < r + 1) = (q < r) := by apply propext; omega
          simpa [Opt.updA, e1, this] using hx
      · by_cases e1 : q = r
        · subst e1; simpa [Opt.updA] using hy
        · have : (q < r + 1) = (q < r) := by apply propext; omega
          simpa [Opt.updA, e1, this] using hy
    obtain ⟨I', h1, h2⟩ := ih (r + 1) (by omega) I1 hI1'
    refine ⟨I', ?_, h2⟩
    have hne : r ≠ nargs := by omega
    have hL := optC_layer2
    unfold alWS at h1 ⊢
    generalize optC = OC at hL h1
    rw [← h1]
    nock_open alEnT
    simp [nock_exec, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hp, hne, eqCode]

/-! ## The join over `pre` -/

/-- The arm `join-info` of the battery. -/
def alJIArm : Noun := C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) alJInfoB) (C (A 0) (A 1))))

theorem alBat_ji : ∃ a1 a2 a4 a5, alBat = C a1 (C a2 (C alJIArm (C a4 (C a5 alWalk)))) :=
  ⟨_, _, _, _, rfl⟩

/-- **The gate of the `+roll`**: `(join-info acc (~(got by info.gen) o1))`. -/
theorem al_jng {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (NA BL REV T PRE : Noun)
    (o1 : Nat) (N : Noun) (acc : Opt.AInfo) (hN : InfoMapRel N acc) (i1 : Opt.AInfo) (h1 : g.info o1 = some i1) :
    ∃ N', nock (C alJnG (C (C (A o1) N) (C PRE (alWS GEN NA BL REV T)))) alJnG = some N' ∧
      InfoMapRel N' (Opt.joinInfoA acc i1) := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR⟩ := hg
  obtain ⟨V, hV, hVr⟩ := info_got hI h1
  obtain ⟨N', hj, hN'⟩ := al_jinfo (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML R (flag g.folded))
    alBodyCut (C NA (C BL (C REV T))) hN hVr
  refine ⟨N', ?_, hN'⟩
  obtain ⟨a1, a2, a4, a5, hX⟩ := alBat_ji
  unfold alJIArm at hX
  have hL := optC_layer2
  unfold alCtx at hj
  unfold alWS
  rw [hX] at hj ⊢
  unfold genN at hj ⊢
  generalize optC = OC at hL hj
  simp [nock_exec, alJnG, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hV, hj]

/-- **The `+roll` of `join-info` over `t.pre`**, from the facts of `i.pre`:
the model's `foldlM` of `joinInfoA`. -/
theorem al_jnroll {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (NA BL REV T : Noun)
    (p : Nat) (t : List Nat) (i0 info : Opt.AInfo) (h0 : g.info p = some i0)
    (hf : t.foldlM (fun acc o1 => (g.info o1).map fun i1 => Opt.joinInfoA acc i1) i0 = some info) :
    ∃ N, nock (C (listNoun A (p :: t)) (alWS GEN NA BL REV T)) alJnRoll = some N ∧ InfoMapRel N info := by
  have hg' := hg
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR⟩ := hg'
  obtain ⟨V0, hV0, hV0r⟩ := info_got hI h0
  obtain ⟨N, hroll, hN⟩ := roll_gate_rel A InfoMapRel (fun o1 acc => (g.info o1).map fun i1 => Opt.joinInfoA acc i1)
    layer2 alJnG (A 0) (C (listNoun A (p :: t)) (alWS (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC
      IMML R (flag g.folded)) NA BL REV T)) t i0 V0 info
    (fun o1 _ s N s' hs e => by
      cases e1 : g.info o1 with
      | none => rw [e1] at e; cases e
      | some i1 =>
        rw [e1] at e
        cases e
        exact al_jng hg NA BL REV T _ o1 N s hs i1 e1)
    hV0r hf
  refine ⟨N, ?_, hN⟩
  rw [← listNoun_map_listN] at hroll
  simp only [listNoun] at hroll
  have hL := optC_layer2
  unfold alWS at hroll ⊢
  unfold genN at hroll ⊢
  generalize optC = OC at hL hroll
  rw [alJnRoll_cut]
  simp [nock_exec, alJnRollC, listNoun, hL, roll.arm_at, roll_arm, by.arm_at, by_arm, by.got.arm_at, got_arm,
    hV0, hroll]

end Compiler
end Formalization
