import lemmas.Compiler.PokeLinkTailCores

/-!
# `+uni-ju` linked (track P, README Gaps 23)

The cut of `+uni-ju` (arm `1404` of `ana`, `tools/gen/ujcut.py`) and its run
on jugs of sets: the `+rep:by` of `b` with the step `uniJuStep` (`put:by` of
`uni:in` of `get:ju`), `repO` in the order of `+rep:by`.

* `rep_loopP`, `rep_gateP`: `+rep:by` with a step that may crash, its
  equation asked only on the nodes (`Q`) and accumulators (`P`) it meets;
* `ujStep_run`: the step gate is `uniJuStep` on a node `[p q]` with `q` a
  set and an accumulator that is a jug of sets;
* **`uniJu_run`**: the gate `((uni-ju a) b)` of the pill is `uniJuO a b` on
  jugs of sets.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

-- BEGIN ujcut
/-- the arm `+uni-ju`: the wet gate on `a`, 134 cells: axis `1404` of `ana`. -/
def ujArm : Noun := (slot? 1404 ana).getD (A 0)
/-- the battery of the gate on `a`: the wet gate on `b`, 128 cells: axis `29` of `ujArm`. -/
def ujBatA : Noun := (slot? 29 ujArm).getD (A 0)
/-- the battery of the gate on `b`, 122 cells: axis `29` of `ujBatA`. -/
def ujBatB : Noun := (slot? 29 ujBatA).getD (A 0)
/-- the `+rep:by` of `b`, 114 cells: axis `15` of `ujBatB`. -/
def ujRep : Noun := (slot? 15 ujBatB).getD (A 0)
/-- the bunt of the sample of the step gate, 17 cells: axis `4062` of `ujRep`. -/
def ujSam : Noun := (slot? 4062 ujRep).getD (A 0)
/-- the battery of the step gate, 69 cells: axis `16253` of `ujRep`. -/
def ujStep : Noun := (slot? 16253 ujRep).getD (A 0)

theorem ujArm_eq : ujArm = (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) ujBatA) (C (A 0) (A 1))))) := by kernel_rfl
theorem ujBatA_eq : ujBatA = (C (A 8) (C (C (A 0) (A 6)) (C (C (A 1) ujBatB) (C (A 0) (A 1))))) := by kernel_rfl
theorem ujBatB_eq : ujBatB = (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 30)) ujRep))) := by kernel_rfl
theorem ujRep_eq : ujRep = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C ujSam (C (C (A 1) ujStep) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem ujSam_eq : ujSam = (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 0) (A 24)) (C (A 0) (A 0))))) (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 0) (A 25)) (C (A 0) (A 0)))))) (C (A 0) (A 30))) := by kernel_rfl
theorem ujStep_eq : ujStep = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) := by kernel_rfl

/-- `+uni-ju` is the arm `1404` of `ana`. -/
theorem ana_ujArm : slot? 1404 ana = some ujArm := by kernel_rfl
-- END ujcut

/-! ## `+rep:by` with a step that may crash -/

theorem rep_loopP (B ctx bp e bc : Noun) (f : Noun → Noun → Option Noun) (P Q : Noun → Prop)
    (hf : ∀ x acc, Q x → P acc → nock (C bp (C (C x acc) bc)) bp = f x acc)
    (hk : ∀ x acc out, Q x → P acc → f x acc = some out → P out) :
    ∀ (a : Noun), Tree a → ∀ acc, (∀ n ∈ preorder a, Q n) → P acc →
      nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C a ctx))))) by.rep.loop =
        repO f a acc := by
  intro a ht
  induction ht with
  | nil =>
    intro acc _ _
    nock_open by.rep.loop; simp [nock_exec, repO]
  | @node n l r htl htr ihl ihr =>
    intro acc hQ hP
    have hQn : Q n := hQ n (by simp [preorder])
    have hQl : ∀ m ∈ preorder l, Q m := fun m hm => hQ m (by simp [preorder, hm])
    have hQr : ∀ m ∈ preorder r, Q m := fun m hm => hQ m (by simp [preorder, hm])
    have hfn := hf n acc hQn hP
    cases hfa : f n acc with
    | none =>
      nock_open by.rep.loop
      simp [nock_exec, repO, hfn, hfa]
    | some a' =>
      have hPa := hk n acc a' hQn hP hfa
      have hl := ihl a' hQl hPa
      cases hla : repO f l a' with
      | none =>
        nock_open by.rep.loop
        simp [nock_exec, repO, hfn, hfa, hl, hla, tap_bind_bind]
      | some y =>
        have hPy := repO_keeps_on f P Q hk l a' y hQl hPa hla
        have hr := ihr y hQr hPy
        nock_open by.rep.loop
        simp [nock_exec, repO, hfn, hfa, hl, hla, hr, tap_bind_bind]

theorem rep_gateP (B ctx bp e acc bc : Noun) (f : Noun → Noun → Option Noun) (P Q : Noun → Prop)
    (hf : ∀ x acc, Q x → P acc → nock (C bp (C (C x acc) bc)) bp = f x acc)
    (hk : ∀ x acc out, Q x → P acc → f x acc = some out → P out) (a : Noun) (ht : Tree a)
    (hQ : ∀ n ∈ preorder a, Q n) (hP : P acc) :
    nock (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C a ctx)))) by.rep.battery = repO f a acc := by
  nock_open by.rep.battery
  simp only [nock_exec, rep_loopP B ctx bp e bc f P Q hf hk a ht acc hQ hP]

/-! ## The step and the gate -/

set_option maxHeartbeats 2000000 in
/-- **The step gate of `+uni-ju`** on a node `[p q]` with `q` a set and a
jug of sets: `uniJuStep`. -/
theorem ujStep_run (p q acc b a : Noun) (hq : IsSet mugF q) (hacc : JugSets acc) :
    nock (C ujStep (C (C (C p q) acc) (C ujBatB (C b (C ujBatA (C a ana)))))) ujStep = uniJuStep (C p q) acc := by
  obtain ⟨g, hg, hd⟩ : ∃ g, getF mugF p acc = some g ∧ IsSet mugF (unUnit g) := by
    by_cases hx : ∃ s, Get acc p s
    · obtain ⟨s, hs⟩ := hx
      exact ⟨_, getF_some hacc.1 hs, hacc.2 _ _ hs⟩
    · exact ⟨_, getF_none hacc.1 (fun v hv => hx ⟨v, hv⟩), IsMap.nil⟩
  have hget := ju_get_gate layer2 juIn_layer2 ju.battery p acc g hg
  obtain ⟨out, hR, -, -, -⟩ := uniP_of_sets _ (unUnit g) q (Nat.le_refl _) hd hq
  have huni := uni_in_gate (mug := mugF) layer2 gorIn_morIn_layer2 hR
  have huO : uniInO (unUnit g) q = some (if unUnit g = q then unUnit g else out) := by
    have hx : ∃ o, UniR mugF (unUnit g) q o := ⟨out, hR⟩
    unfold uniInO
    rw [dif_pos hx, uniR_det (Classical.choose_spec hx) hR]
  obtain ⟨o, ho, -, -⟩ := putF_spec mugF acc p (if unUnit g = q then unUnit g else out) hacc.1
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 p _ acc o ho
  have hR' : uniJuStep (C p q) acc = some o := by
    simp only [uniJuStep, juGetF, hg, Option.map_some, Option.bind_some, huO, ho]
  rw [hR', ujStep_eq]
  simp [nock_exec, ana_l2, by.arm_at, by_arm, by.put.arm_at, put_arm, in.arm_at, in_arm, in.uni.arm_at,
    uni_in_arm, ju.arm_at, ju_arm, ju.get.arm_at, ju_get_arm, hget, huni, hput]

set_option maxHeartbeats 2000000 in
/-- **`((uni-ju a) b)` of the pill on jugs of sets is `uniJuO a b`**: the
gate on `b` (its subject `[ujBatB [b [ujBatA [a ana]]]]`). -/
theorem uniJu_run (a b : Noun) (ha : JugSets a) (hb : JugSets b) :
    nock (C ujBatB (C b (C ujBatA (C a ana)))) ujBatB = uniJuO a b := by
  have hQ : ∀ n ∈ preorder b, ∃ p q, n = C p q ∧ IsSet mugF q := fun n hn => by
    obtain ⟨k, v, rfl, hk⟩ := (mem_preorder hb.1 n).1 hn
    exact ⟨k, v, rfl, hb.2 k v hk⟩
  have hrep := fun e => rep_gateP by.battery layer2 ujStep e a (C ujBatB (C b (C ujBatA (C a ana)))) uniJuStep
    JugSets (fun n => ∃ p q, n = C p q ∧ IsSet mugF q)
    (fun x acc hx hacc => by obtain ⟨p, q, rfl, hq⟩ := hx; exact ujStep_run p q acc b a hq hacc)
    (fun _ _ _ hq h e => uniJuStep_sets h hq e) b (Tree.of_isMap hb.1) hQ ha
  unfold uniJuO
  rcases Tree.of_isMap hb.1 with _ | @⟨n, l, r, _, _⟩
  · rw [ujBatB_eq]
    simp [nock_exec, repO]
  · obtain ⟨k, v, rfl, -⟩ := hQ n (by simp [preorder])
    rw [ujBatB_eq, ujRep_eq, ujSam_eq]
    simp [nock_exec, ana_l2, by.arm_at, by_arm, by.rep.arm_at, rep_arm]
    exact hrep _

/-! ## The edit of `jets.lon` (push 11) -/

/-- `((uni-ju pend.jets.lon) new-cores)` in `srJetsF`. -/
def ujCall : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 1404) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffe9e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))

theorem srJetsF_eq : srJetsF =
    C (A 10) (C (C (A 62) ujCall) (C (A 10) (C (C (A 30) (C (A 0) (A 0x1ffde))) (C (A 10) (C (C (A 14) (C (A 0) (A 0xffee))) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff6))) (C (A 10) (C (C (A 2) (C (A 0) (A 0x3ffa))) (C (A 0) (A 0x7fff4))))))))))) := rfl

theorem ujArm_run : nock ana ujArm = some (C ujBatA (C (A 0) ana)) := by
  rw [ujArm_eq]; simp [nock_exec]

theorem ujBatA_run (x c : Noun) : nock (C ujBatA (C x c)) ujBatA = some (C ujBatB (C x (C ujBatA (C x c)))) := by
  conv => lhs; arg 2; rw [ujBatA_eq]
  simp [nock_exec]

theorem ujCall_run (U pd nco : Noun) (hA : slot? 0xffff U = some ana) (hP : slot? 0xfffe9e U = some pd)
    (hN : slot? 2 U = some nco) :
    nock U ujCall = nock (C ujBatB (C nco (C ujBatA (C pd ana)))) ujBatB := by
  unfold ujCall
  simp [nock_exec, hA, ana_ujArm, ujArm_run, hP, hN, ujBatA_run]

set_option maxHeartbeats 2000000 in
/-- **The edit of `jets.lon` linked** (push 11): on the tail's subject with
`new-cores` pushed, whose regs are `[ro co ba ar nw]` and jets
`[r1 r2 r3 r4 pd cole]`, `pend` and `new-cores` jugs of sets, `srJetsF`
returns the regs' four maps and `uniJuO pd nco`. -/
theorem srJetsF_run (nco q ncN bkN g0 rN a b c g1 ro co ba ar nw e e0 r1 r2 r3 r4 pd cole mN cN caN vN sN hN
    pd' : Noun) (hp : JugSets pd) (hn : JugSets nco) (h : uniJuO pd nco = some pd') :
    nock (C nco (srT10 q ncN bkN g0 rN a b c (C g1 (C ro (C co (C ba (C ar nw))))) e e0
      (C r1 (C r2 (C r3 (C r4 (C pd cole))))) mN cN caN vN sN hN)) srJetsF =
      some (C ro (C co (C ba (C ar (C pd' cole))))) := by
  have hu := uniJu_run pd nco hp hn
  rw [h] at hu
  have hc := ujCall_run (C nco (srT10 q ncN bkN g0 rN a b c (C g1 (C ro (C co (C ba (C ar nw))))) e e0
      (C r1 (C r2 (C r3 (C r4 (C pd cole))))) mN cN caN vN sN hN)) pd nco
    (by simp [srT10, srS3x, srSk, srSam, nock_exec]) (by simp [srT10, srS3x, srSk, srSam, nock_exec])
    (by simp [nock_exec])
  rw [hu] at hc
  rw [srJetsF_eq]
  simp only [nock_exec, hc, Option.bind_some]

end Compiler
end Formalization
