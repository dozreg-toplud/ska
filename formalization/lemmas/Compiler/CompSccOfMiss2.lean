import lemmas.Compiler.CompSccOfMiss

/-!
# The roll and the `got` of the miss of `+scc-of`, and the whole miss (track Q)

After `=/  sub`, the subject is `[sub M0]` (`M0 = scoM0 B CA SC CTX`).

* `sco_b1`, `sco_b2`: the two mold bunts of the roll's gates (`smB1`, the
  bunt of `s=(set bell)`, and `smB2`, of `m=bell`) read only the context
  (the hoon core and axis `31` of `ctx`), so they are the bunts on a subject
  of `~`s with the same context (`ScoBunts CTX`: both return there; not
  proved: arms `6098`, `382` of the hoon core's molds);
* `sco_gstep`: the roll's gate on `[s acc]` is `scoRollStep acc s`;
* `sco_roll`: `smRoll` (`+roll` over the list `+tarjan` returns) is
  `scoRoll`, given the list noun the pill's `+tarjan` returns on `sub`;
* `tjFinIs_listN`: the noun `TjFinIs FIN L` is `listN` of the `scoSetN` of
  the lists (`isSet_ext`);
* **`sco_miss`**: the whole miss `sccMiss` is `scoMiss`, at every fuel,
  given `TarjanLinkAt` on the `sub` it builds;
* **`sccG_miss`**: track P's `sccG` on a `sccs` without `b` is `scoMiss`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- A monadic fold whose steps on the members return what the model's do. -/
theorem sco_foldlM_mem {f g : Noun → Noun → Option Noun} :
    ∀ (l : List Noun), (∀ a x r, x ∈ l → f a x = some r → g a x = some r) →
      ∀ (a r : Noun), l.foldlM f a = some r → l.foldlM g a = some r := by
  intro l
  induction l with
  | nil => intro _ a r h0; simpa using h0
  | cons x xs ih =>
    intro h a r h0
    simp only [List.foldlM_cons] at h0 ⊢
    cases e : f a x with
    | none => rw [e] at h0; cases h0
    | some b =>
      rw [e] at h0
      rw [h a x b (by simp) e]
      exact ih (fun a y r hy hr => h a y r (by simp [hy]) hr) b r h0

/-- A cons formula whose head is a cell. -/
theorem sco_autocons {s f g a b : Noun} (hc : ∃ x y, f = C x y) (hf : nock s f = some a) (hg : nock s g = some b) :
    nock s (C f g) = some (C a b) := by
  obtain ⟨x, y, rfl⟩ := hc
  simp [nock_exec, hf, hg]

/-- The mold bunts of the roll's gates return on the context `CTX`. -/
def ScoBunts (CTX : Noun) : Prop :=
  (∃ E, nock (C (A 0) (C (A 0) (C (A 0) (C (A 0) CTX)))) smB1 = some E) ∧
    ∃ E, nock (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) CTX)))))) smB2 = some E

/-- `smB1` reads only the context at depth four. -/
theorem sco_b1 (a b c d CTX : Noun) :
    nock (C a (C b (C c (C d CTX)))) smB1 = nock (C (A 0) (C (A 0) (C (A 0) (C (A 0) CTX)))) smB1 := by
  rw [smB1_eq]
  simp [nock_exec]

/-- `smB2` reads only the context at depth six. -/
theorem sco_b2 (a b c d e f CTX : Noun) :
    nock (C a (C b (C c (C d (C e (C f CTX)))))) smB2
      = nock (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) CTX)))))) smB2 := by
  rw [smB2_eq]
  simp [nock_exec]

/-- The inner gate of the roll: `(~(put by acc) m s)`. -/
theorem sco_ibat {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (S acc SUB M1 M2 M3 E m N r : Noun)
    (h : putF mugF m S N = some r) :
    nock (C smIBat (C (C m N) (C smGBat (C (C S acc) (C SUB (C M1 (C M2 (C M3 CTX)))))))) smIBat = some r := by
  have hp := put_gate layer2 gorIn_morIn_layer2 m S N r h
  rw [smIBat_eq]
  simp [nock_exec, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hp]

/-- **The roll's gate** on `[s acc]` is `scoRollStep acc s`. -/
theorem sco_gstep {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (hB : ScoBunts CTX) (SUB M1 M2 M3 E : Noun)
    (S acc : Noun) (hS : Tree S) :
    ∀ r, scoRollStep acc S = some r →
      nock (C smGBat (C (C S acc) (C SUB (C M1 (C M2 (C M3 CTX)))))) smGBat = some r := by
  intro r h
  obtain ⟨E2, hE2⟩ := hB.2
  have hb2 := sco_b2 smGBat (C S acc) SUB M1 M2 M3 CTX
  rw [hE2] at hb2
  have hrep := tj_rep_gate in.battery layer2 smIBat E2 acc (C smGBat (C (C S acc) (C SUB (C M1 (C M2 (C M3 CTX))))))
    S hS
  have hf := sco_foldlM (f := fun acc m => putF mugF m S acc)
    (g := fun N m => nock (C smIBat (C (C m N) (C smGBat (C (C S acc) (C SUB (C M1 (C M2 (C M3 CTX)))))))) smIBat)
    (fun a m r hr => sco_ibat hL S acc SUB M1 M2 M3 E m a r hr) _ _ _ h
  have hr := hrep.trans hf
  have hcons : nock (C smGBat (C (C S acc) (C SUB (C M1 (C M2 (C M3 CTX)))))) (C smB2 (C (A 0) (A 13)))
      = some (C E2 acc) := sco_autocons ⟨_, _, smB2_eq⟩ hb2 (by simp [nock_exec])
  conv => lhs; arg 2; rw [smGBat_eq]
  simp [nock_exec, hL, hcons, in.arm_at, in_arm, in.rep.arm_at, rep_arm, hr]

/-- **The roll** over the list noun `+tarjan` returns on `sub`. -/
theorem sco_roll {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (h15 : slot? 15 CTX = some ana)
    (hB : ScoBunts CTX) (B CA SC SUB : Noun) (Ss : List Noun) (hS : ∀ S ∈ Ss, Tree S)
    (hT : nock (C tjBat (C SUB ana)) tjBat = some (listN Ss)) :
    ∀ r, scoRoll SC Ss = some r → nock (C SUB (scoM0 B CA SC CTX)) smRoll = some r := by
  intro r h
  obtain ⟨E1, hE1⟩ := hB.1
  have hb1 := sco_b1 SUB (A 0) sccBat (C B (C CA SC)) CTX
  rw [hE1] at hb1
  have hg := roll_gate_M layer2 smGBat E1 SC (C SUB (scoM0 B CA SC CTX))
    (fun S acc => nock (C smGBat (C (C S acc) (C SUB (scoM0 B CA SC CTX)))) smGBat) Ss (fun _ _ _ => rfl)
  have hf := sco_foldlM_mem (f := scoRollStep)
    (g := fun acc S => nock (C smGBat (C (C S acc) (C SUB (scoM0 B CA SC CTX)))) smGBat) Ss
    (fun a S r hm hr => sco_gstep hL hB SUB (A 0) sccBat (C B (C CA SC)) E1 S a (hS S hm) r hr) SC r h
  have hr := hg.trans hf
  have hana : slot? 2815 ana = some tjArm := by kernel_rfl
  simp only [scoM0] at hr
  have hcons : nock (C SUB (C (A 0) (C sccBat (C (C B (C CA SC)) CTX)))) (C smB1 (C (A 0) (A 123)))
      = some (C E1 SC) := sco_autocons ⟨_, _, smB1_eq⟩ hb1 (by simp [nock_exec])
  rw [smRoll_eq]
  simp [scoM0, nock_exec, hL, h15, hcons, smTj_eq, hana, tjArm_gate, hT, roll.arm_at, roll_arm, hr]

/-- The model's graph of a jug noun is `tjGraph`. -/
theorem scoGraph_eq (G : Noun) : scoMiss.tjGraphM G = tjGraph G := by
  unfold scoMiss.tjGraphM tjGraph
  congr 1

/-- **The noun of `+tarjan`'s list** is `listN` of the `scoSetN` of the
model's lists. -/
theorem tjFinIs_listN : ∀ (L : List (List Noun)) (FIN : Noun), TjFinIs FIN L →
    ∀ Ss, L.mapM scoSetN = some Ss → FIN = listN Ss ∧ ∀ S ∈ Ss, IsSet mugF S
  | [], FIN, h, Ss, hm => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at hm
    subst hm
    exact ⟨h, by simp⟩
  | l :: ls, FIN, h, Ss, hm => by
    obtain ⟨S, REST, rfl, hS, hR⟩ := h
    obtain ⟨S', hs1, hs2, hs3⟩ := scoSetN_spec l
    simp only [List.mapM_cons, hs1, Option.bind_eq_bind, Option.bind_some] at hm
    cases hr : ls.mapM scoSetN with
    | none => rw [hr] at hm; cases hm
    | some Ss' =>
      rw [hr] at hm
      simp only [Option.bind_some, pure, Option.some.injEq] at hm
      subst hm
      obtain ⟨h1, h2⟩ := tjFinIs_listN ls REST hR Ss' hr
      have heq : S = S' := isSet_ext hS.1 hs2 (fun k => (hS.2 k).trans (hs3 k).symm)
      subst heq; subst h1
      refine ⟨rfl, fun T hT => ?_⟩
      rcases List.mem_cons.1 hT with rfl | hT
      · exact hS.1
      · exact h2 T hT

/-- **`[(~(got by sccs) b) sccs]`** is `scoGot`. -/
theorem sco_got {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (B CA SC SUB : Noun) :
    ∀ r, scoGot B SC = some r → nock (C SUB (scoM0 B CA SC CTX)) smGot = some r := by
  intro r h
  unfold scoGot at h
  split at h
  · rename_i S hg
    simp only [Option.some.injEq] at h
    subst h
    have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B SC S hg
    rw [smGot_eq]
    simp [scoM0, nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hgt]
  · cases h

/-- **The miss of `+scc-of` is `scoMiss`**: at every fuel, whenever the
model returns, the pill's miss returns the same `[s sccs]`, given
`TarjanLinkAt` on the `sub` the loop builds. -/
theorem sco_miss {CTX : Noun} (hL : slot? 65535 CTX = some layer2) (h15 : slot? 15 CTX = some ana)
    (hB : ScoBunts CTX) (B CA SC : Noun) (hCA : CallsOK CA) (n : Nat)
    (hT : ∀ SUB, scoSub CA SC n [B] (A 0) = some SUB → TarjanLinkAt SUB) :
    ∀ r, scoMiss B CA SC n = some r → nock (scoM0 B CA SC CTX) sccMiss = some r := by
  intro r h
  unfold scoMiss at h
  cases hs : scoSub CA SC n [B] (A 0) with
  | none => rw [hs] at h; cases h
  | some SUB =>
    rw [hs, Option.bind_some] at h
    cases ht : tarjanM (scoMiss.tjGraphM SUB) with
    | none => rw [ht] at h; cases h
    | some L =>
      rw [ht, Option.bind_some] at h
      cases hm : L.mapM scoSetN with
      | none => rw [hm] at h; cases h
      | some Ss =>
        rw [hm, Option.bind_some] at h
        cases hr : scoRoll SC Ss with
        | none => rw [hr] at h; cases h
        | some SC' =>
          rw [hr, Option.bind_some] at h
          have hsub := sco_sub hL B CA SC hCA n SUB hs
          rw [scoGraph_eq] at ht
          obtain ⟨FIN, hfin, hpill⟩ := hT SUB hs L ht
          obtain ⟨hFIN, hsets⟩ := tjFinIs_listN L FIN hfin Ss hm
          subst hFIN
          have hroll := sco_roll hL h15 hB B CA SC SUB Ss (fun S hS => Tree.of_isSet (hsets S hS)) hpill SC' hr
          have hgot := sco_got hL B CA SC' SUB r h
          simp only [scoM0] at hsub hroll hgot
          rw [sccMiss_eq]
          simp [scoM0, nock_exec, hsub, smRest_eq, smRollE_eq, hroll, hgot]

/-- The core of `+scc-of` holds `ana` (the core of `+tarjan`) at axis `15`. -/
theorem sccCore_ana : slot? 15 sccCore = some ana := by kernel_rfl

/-- **Track P's `sccG` on a cache miss is `scoMiss`**: when `sccs` has no
entry for `b`, at every fuel, whenever the model returns, the gate returns
the same `[s sccs]`. -/
theorem sccG_miss (B CA SC : Noun) (hg : getF mugF B SC = some (A 0)) (hCA : CallsOK CA) (n : Nat)
    (hB : ScoBunts sccCore) (hT : ∀ SUB, scoSub CA SC n [B] (A 0) = some SUB → TarjanLinkAt SUB) :
    ∀ r, scoMiss B CA SC n = some r → sccG B CA SC = some r := by
  intro r h
  have hm := sco_miss sccCore_hoon sccCore_ana hB B CA SC hCA n hT r h
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg' := get_gate layer2 hgc B SC _ hg
  rw [sccG_eq, sccBat_run]
  have h1 : nock (C sccBat (C (C B (C CA SC)) sccCore)) sccGetF = some (A 0) := by
    simp [sccGetF, sccCore_hoon, by.arm_at, by_arm, by.get.arm_at, get_arm, nock_exec, hg']
  rw [h1]
  simp only [scoM0] at hm
  simp [sccTestF, nock_exec, hm]

end Compiler
end Formalization
