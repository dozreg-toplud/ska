import lemmas.Compiler.CompStraightPre

/-!
# The `|^` core of `+to-straight`: `ren`, `+rewrite-input`, the test

The arm `$` of the `|^` core (`tsCoreBat`, battery axis `126`) is

`[7 [0 1] [8 RI [7 [10 [14 [0 5]] [0 1]] [7 [[0 4] [0 3]] [6 TEST REN MAP]]]]]`

with `RI` the call of `rewrite-input` (core arm `22`, battery axis `14`) on
`ned.nex`, `TEST` the test `&(run !proxies)`, `REN` the renaming branch
(`tsRenameBr`) and `MAP` the map path.  Here:

* `ts_ren`: the gate `ren` (`tsRenBat`) on the state that `ts_pre` reaches
  is `renReg sub 1` (`+lth`, `+add`, `+sub` of `layer1`).
* `ts_rer`: `rer` (battery axis `12`) with `proxies` `|` and `run` `&` is
  `[(ren r) gen]`.
* `ts_ri`: `rewrite-input` on `[%this sub]` from `gen = [0 0]` is
  `[[%this ~] [0 0]]`, the model's `rewriteInput` (`ts_ri_model`).
* `ts_dol`: the arm `$` on that state is the renaming branch on the subject
  `[[%this ~] core]` (the test is `&`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- **The gate `ren`** on the state of the core: `renReg sub 1`. -/
theorem ts_ren {ctx : Noun} (hc : CompIn ctx) (B Bo D G : Noun) (o q r : Nat) :
    nock (C tsRenBat (C (A r) (tsS7 B Bo (tsS0 D G ctx o q) q))) tsRenBat
      = some (A (renReg q 1 r)) := by
  have hl1 := ts_layer1 hc
  have hadd := add_gate layer1 decIn_layer1
  have hsub := sub_gate layer1 decIn_layer1
  have hlth := lth_gate layer1 decIn_layer1
  unfold renReg
  simp only [tsS0, tsS7, tsS5]
  generalize tsBat = T
  by_cases h1 : r < q
  · simp [nock_exec, tsRenBat, hl1, lth.arm_at, lth_arm, hlth, add.arm_at, add_arm, hadd, h1, loob]
  · by_cases h2 : r < q + 1
    · have hs : q ≤ r := by omega
      simp [nock_exec, tsRenBat, hl1, lth.arm_at, lth_arm, hlth, add.arm_at, add_arm, hadd, h1, h2,
        loob, Pill.sub.arm_at, sub_arm, hsub q r hs]
    · simp [nock_exec, tsRenBat, hl1, lth.arm_at, lth_arm, hlth, add.arm_at, add_arm, hadd, h1, h2,
        loob]

/-! ## The nouns of the core's arms -/

/-- The arm `$` of the `|^` core (battery axis `126`). -/
noncomputable def tsDolArm : Noun := (slot? 126 tsCoreBat).getD (A 0)
/-- The renaming branch of `$`. -/
noncomputable def tsRenameBr : Noun := (slot? 4094 tsDolArm).getD (A 0)
/-- The map path of `$`. -/
noncomputable def tsMapBr : Noun := (slot? 4095 tsDolArm).getD (A 0)

/-- **The arm `$`**: `rewrite-input` on `ned.nex`, the edit of `gen`, the
test `&(run !proxies)`, the two branches. -/
theorem ts_dol_at : slot? 126 tsCoreBat = some (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe8))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 0) (A 126)) (C (C (A 6) (C (C (A 6) (C (C (A 0) (A 2046)) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C tsRenameBr tsMapBr))))))))))) := by
  kernel_rfl

/-- The arm `rewrite-input` (battery axis `14`). -/
noncomputable def tsRiArm : Noun := (slot? 14 tsCoreBat).getD (A 0)
/-- The cases `^` and `%both` of the loop of `rewrite-input`. -/
noncomputable def tsRiRest : Noun := (slot? 122239 tsRiArm).getD (A 0)

/-- The body of the trap of `rewrite-input`: `?-  -.ned`, `%none`, `%this`
(`=.  gen  +:(rer r.ned)`), and the rest. -/
noncomputable def tsRiTrap : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 28)))) (C (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 28)))) (C (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 20) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 2)))))))) (C (A 0) (A 3))))) (C (A 0) (A 1)))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 0) (A 62))))) tsRiRest)))))

/-- The body of the gate `rewrite-input`: `?>  =(0 re-gen.gen)`, the trap. -/
noncomputable def tsRiBody : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (A 8) (C (C (A 1) tsRiTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 0))))

theorem ts_ri_at : slot? 14 tsCoreBat = some (C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) tsRiBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The arm `rer` (battery axis `12`). -/
noncomputable def tsRerArm : Noun := (slot? 12 tsCoreBat).getD (A 0)
/-- The branch of `rer` when the inputs are not a run (through `m.gen`). -/
noncomputable def tsRerMap : Noun := (slot? 959 tsRerArm).getD (A 0)

/-- The body of `rer`: `=?  r  proxies  (unproxy r)`, `?:  run  [(ren r) gen]`. -/
noncomputable def tsRerBody : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 6) (C (A 6) (C (C (A 0) (A 4094)) (C (C (A 8) (C (C (A 0) (A 8190)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 6)))))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 0) (A 254)) (C (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 30))) tsRerMap))))

theorem ts_rer_at : slot? 12 tsCoreBat = some (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) tsRerBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The gate `ren` as the gate of `+to-straight` pushed it. -/
noncomputable def tsRenG (BN D G ctx : Noun) (o sub : Nat) : Noun :=
  C tsRenBat (C (A 0) (tsS7 BN BN (tsS0 D G ctx o sub) sub))

/-- The state of the `|^` core with the blocks of the context of `ren`
named apart (`BN`) from the edited blocks (`B`). -/
noncomputable def tsSt (SB B Bo BN D G ctx : Noun) (o sub : Nat) : Noun :=
  tsCoreSt SB (tsRenG BN D G ctx o sub) B Bo (tsS0 D G ctx o sub) sub

/-- **`rer`** with `proxies` `|` and `run` `&`: `[(ren r) gen]`. -/
theorem ts_rer {ctx : Noun} (hc : CompIn ctx) (SB B Bo BN D G : Noun) (o sub r : Nat) :
    nock (C tsRerBody (C (A r) (tsSt SB B Bo BN D G ctx o sub))) tsRerBody
      = some (C (A (renReg sub 1 r)) (C (A 0) (A 0))) := by
  have hr := ts_ren hc BN BN D G o sub r
  unfold tsSt tsRenG
  simp only [tsCoreSt]
  generalize tsS7 BN BN (tsS0 D G ctx o sub) sub = X at hr ⊢
  simp only [tsS7, tsS5]
  generalize tsS0 D G ctx o sub = S0
  generalize tsCoreBat = K
  unfold tsRerBody
  generalize tsRerMap = M
  simp [nock_exec, hr]

/-- **The arm `$` up to its branches**: `rewrite-input` on `[%this sub]`
gives `[[%this ~] [0 0]]` (`rer` once, `gen` unchanged), the edit of `gen`
leaves the core as it was, and the test `&(run !proxies)` is `&`, so `$` is
the renaming branch on `[[%this ~] core]`. -/
theorem ts_dol {ctx : Noun} (hc : CompIn ctx) (SB B Bo BN D G : Noun) (o sub : Nat) :
    nock (tsSt SB B Bo BN D G ctx o sub) (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = nock (C (C (A 0x73696874) (A 0)) (tsSt SB B Bo BN D G ctx o sub)) tsRenameBr := by
  have hr := ts_rer hc SB B Bo BN D G o sub sub
  have hdol := ts_dol_at
  have hri := ts_ri_at
  have hrer := ts_rer_at
  unfold tsSt at hr ⊢
  generalize tsRenG BN D G ctx o sub = RG at hr ⊢
  simp only [tsCoreSt, tsS7, tsS5, tsS0, tsSample] at hr ⊢
  generalize tsBat = T at hr ⊢
  generalize tsCoreBat = K at hr hdol hri hrer ⊢
  unfold tsRiBody tsRiTrap at hri
  generalize tsRiRest = RR at hri
  generalize tsRenameBr = RB at hdol ⊢
  generalize tsMapBr = MB at hdol ⊢
  generalize tsRerBody = RBody at hr hrer ⊢
  simp [nock_exec, hdol, hri, hrer, hr]

/-- The model of the same step: `rewriteInput` on `[%this sub]` with
`proxies` `|` and `run` `&` is `NeedOrd.this` and leaves the state. -/
theorem ts_ri_model {Map : Type → Type} [HoonMap Map] (cond : Map (Nat × List Nat)) (sub : Nat) :
    rewriteInput (rer cond false true (renReg sub 1)) (Need.this sub) (0, HoonMap.empty)
      = some (NeedOrd.this, ((0, HoonMap.empty) : Nat × Map Nat)) := by
  simp [rewriteInput, rewriteInputGo, rer, bind, StateT.bind, pure, StateT.pure]

/-! ## The renaming branch: `(map-regs ren)`, `+count-args`, the `+rep:by` -/

/-- The body of the gate of the `+rep:by` of the renaming branch,
`|=  [[k=@uwoo b=blob] new=(map @uwoo blob)]`. -/
def tsGBody : Noun := (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 24)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 57)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 7) (C (A 1) (C (A 0x6d6f62) (A 0)))) (C (A 0) (A 25))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 120)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 487))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))))))))))))

/-- The bunt of the head of the sample of that gate: `[0 *blob]`. -/
def tsGE : Noun := C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))

/-- **The renaming branch**: `(map-regs ren)`, then `[input (count-args
input) (~(rep by blocks) gate)]`. -/
theorem ts_rb_at : slot? 4094 tsDolArm = some (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 762) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 6)) (C (C (A 8) (C (C (A 9) (C (A 0xbbbe) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C tsGE (A 0))) (C (C (A 1) tsGBody) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))))))) := by
  kernel_rfl

theorem ts_rb_eq : tsRenameBr = C (A 8) (C (C (A 8) (C (C (A 9) (C (A 762) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 6)) (C (C (A 8) (C (C (A 9) (C (A 0xbbbe) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C tsGE (A 0))) (C (C (A 1) tsGBody) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))) := by
  unfold tsRenameBr; rw [ts_rb_at]; rfl

/-- The arm `+map-regs` of the types core `compTypes` (arm `762`). -/
noncomputable def mrArm : Noun := (slot? 762 compTypes).getD (A 0)
/-- The gate `|=  b=blob` that `(map-regs ren)` returns. -/
noncomputable def mrInner : Noun := (slot? 1901 mrArm).getD (A 0)

/-- The body of the gate `+map-regs`: build the gate `mrInner`, then the
`%fast` hint `%map-regs`. -/
noncomputable def mrBody : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (C (C (A 1) mrInner) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x736765722d70616d) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1)))))

theorem mr_at : slot? 762 compTypes = some (C (A 8) (C (C (A 1) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) (C (C (A 1) mrBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The gate `rename = (map-regs ren)`. -/
noncomputable def tsRenameG (REN : Noun) : Noun :=
  C mrInner (C (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))) (C mrBody (C REN compTypes)))

/-- **`(map-regs ren)`**: the gate `mrInner` with `ren` in its context. -/
theorem mr_slam (REN : Noun) :
    nock (C mrBody (C REN compTypes)) mrBody = some (tsRenameG REN) := by
  unfold tsRenameG mrBody
  generalize mrInner = I
  simp [nock_exec]

/-- The arm `+count-args` of `K` (arm `0xbbbe`). -/
noncomputable def caArm : Noun := (slot? 0xbbbe compK).getD (A 0)
/-- The cases `^` and `%both` of `+count-args`. -/
noncomputable def caRest : Noun := (slot? 1919 caArm).getD (A 0)

noncomputable def caBody : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 1) (A 1)) caRest)))))

theorem ca_at : slot? 0xbbbe compK = some (C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) caBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The types core sits at axis `15` of the context. -/
theorem ts_types {ctx : Noun} (h7 : slot? 7 ctx = some compK) : slot? 15 ctx = some compTypes := by
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have := slot_spine (by omega) (by omega) h1 1
  simp only [show 2 ^ 1 * (7 + 1) - 1 = 15 from rfl,
    show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  rw [this]; rfl

/-- The subject of the `+rep:by` gate: `rename`, then `[input core]`. -/
noncomputable def tsY (SB B Bo BN D G ctx : Noun) (o sub : Nat) : Noun :=
  C (tsRenameG (tsRenG BN D G ctx o sub)) (C (C (A 0x73696874) (A 0)) (tsSt SB B Bo BN D G ctx o sub))

/-- **The renaming branch** on `[[%this ~] core]`: `[[%this ~] 1 r]` with
`r` the `+rep:by` of the gate `tsGBody` over the blocks `B` from `~`. -/
theorem ts_rename {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK)
    (SB B Bo BN D G : Noun) (o sub : Nat) :
    nock (C (C (A 0x73696874) (A 0)) (tsSt SB B Bo BN D G ctx o sub)) tsRenameBr
      = (nock (C by.rep.battery (C (C tsGBody (C (C tsGE (A 0)) (tsY SB B Bo BN D G ctx o sub)))
            (C by.battery (C B layer2)))) by.rep.battery).bind
          fun r => some (C (C (A 0x73696874) (A 0)) (C (A 1) r)) := by
  have h15 := ts_types h7
  have hmr := mr_at
  have hca := ca_at
  rw [ts_rb_eq]
  unfold tsY tsRenameG tsSt
  have hms := mr_slam (tsRenG BN D G ctx o sub)
  unfold tsRenameG at hms
  generalize tsRenG BN D G ctx o sub = RG at hms ⊢
  simp only [tsCoreSt, tsS7, tsS5, tsS0, tsSample]
  generalize tsBat = T
  generalize tsCoreBat = K
  unfold caBody at hca
  generalize caRest = CR at hca
  generalize mrBody = MB at hmr hms ⊢
  generalize tsGBody = GB
  simp [nock_exec, hc, h7, h15, hmr, hms, hca, by_arm, by.arm_at, by.rep.arm_at, rep_arm, Option.bind_assoc]

/-! ## The fold: `+rep:by` with a gate that may crash, against `renameBlocks` -/

/-- **The loop of `+rep` with a gate that may crash**, over a tree whose
nodes in pre-order are the nouns `pn p` of a list `L`: the gate on the node
`pn p` and an accumulator `toN s` is `gf p s` (a crash when `none`), and the
loop is `foldlM` of `gf` over `L`. -/
theorem rep_loop_list {α σ : Type} (pn : α → Noun) (toN : σ → Noun) (gf : α → σ → Option σ)
    (B ctx bp e bc : Noun) :
    ∀ (a : Noun), Tree a → ∀ (L : List α), preorder a = L.map pn → ∀ (s : σ),
    (∀ p ∈ L, ∀ s, nock (C bp (C (C (pn p) (toN s)) bc)) bp = (gf p s).map toN) →
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e (toN s)) bc)) (C B (C a ctx)))))
      by.rep.loop = (L.foldlM (fun s p => gf p s) s).map toN := by
  intro a ha
  induction ha with
  | nil =>
    intro L hL s _
    have hL0 : L = [] := by
      cases L with
      | nil => rfl
      | cons p L' => simp [preorder] at hL
    subst hL0
    nock_open by.rep.loop
    simp [nock_exec]
  | @node n l r _ _ ihl ihr =>
    intro L hL s hf
    simp only [preorder] at hL
    obtain ⟨p, L', rfl, hpn, hL'⟩ := List.map_eq_cons_iff.1 hL.symm
    obtain ⟨L1, L2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 hL'
    subst hpn
    have hn := hf p (by simp) s
    have hl := fun s' => ihl L1 h1.symm s' (fun x hx s => hf x (by simp [hx]) s)
    have hr := fun s' => ihr L2 h2.symm s' (fun x hx s => hf x (by simp [hx]) s)
    nock_open by.rep.loop
    cases e1 : gf p s with
    | none => simp [nock_exec, hn, e1]
    | some s1 =>
      have hl1 := hl s1
      cases e2 : L1.foldlM (fun s p => gf p s) s1 with
      | none =>
        rw [e2] at hl1
        simp [nock_exec, hn, e1, hl1, List.foldlM_append, e2]
      | some s2 =>
        rw [e2] at hl1
        simp [nock_exec, hn, e1, hl1, hr s2, List.foldlM_append, e2]

/-- The gate of `+rep` on such a tree. -/
theorem rep_gate_list {α σ : Type} (pn : α → Noun) (toN : σ → Noun) (gf : α → σ → Option σ)
    (B ctx bp e bc a : Noun) (ha : Tree a) (L : List α) (hL : preorder a = L.map pn) (s : σ)
    (hf : ∀ p ∈ L, ∀ s, nock (C bp (C (C (pn p) (toN s)) bc)) bp = (gf p s).map toN) :
    nock (C by.rep.battery (C (C bp (C (C e (toN s)) bc)) (C B (C a ctx)))) by.rep.battery
      = (L.foldlM (fun s p => gf p s) s).map toN := by
  nock_open by.rep.battery
  simp only [nock_exec, rep_loop_list pn toN gf B ctx bp e bc a ha L hL s hf]

/-- One step of the fold of the renaming branch, on a pair `(k, b)` of the
blocks: `keepBlock`, then the put at `k` when the block is kept. -/
def renameStep (bs : TreapMap mugF Blob) (ren : Nat → Nat) (new : TreapMap mugF Blob)
    (p : Nat × Blob) : Option (TreapMap mugF Blob) :=
  (keepBlock bs ren p.1 p.2).map fun kb => match kb with
    | Option.none => new
    | some b1 => HoonMap.put new p.1 b1

theorem ts_fold_keys (bs : TreapMap mugF Blob) (ren : Nat → Nat) :
    ∀ (L : List (Nat × Blob)), (∀ p ∈ L, HoonMap.get bs p.1 = some p.2) →
    ∀ (acc : Option (TreapMap mugF Blob)),
    (L.map Prod.fst).foldl (fun acc k => acc.bind fun new =>
        (HoonMap.get bs k).bind fun b => (keepBlock bs ren k b).map fun kb =>
          match kb with
          | Option.none => new
          | some b1 => HoonMap.put new k b1) acc
      = acc.bind fun a => L.foldlM (renameStep bs ren) a
  | [], _, acc => by cases acc <;> rfl
  | p :: L, hL, acc => by
    have hp := hL p (by simp)
    have ih := ts_fold_keys bs ren L (fun q hq => hL q (by simp [hq]))
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    cases acc with
    | none => rfl
    | some a =>
      simp only [Option.bind_some, hp, List.foldlM_cons]
      unfold renameStep
      cases keepBlock bs ren p.1 p.2 <;> rfl

/-- **`renameBlocks` on treaps is the fold over `rap`**, the order of
`+rep:by` (with the instance of `TreapList.lean`). -/
theorem renameBlocks_rap (bs : TreapMap mugF Blob) (ren : Nat → Nat) :
    renameBlocks bs ren = (TreapMap.rap bs).foldlM (renameStep bs ren) HoonMap.empty := by
  unfold renameBlocks
  rw [treapMap_keys]
  exact ts_fold_keys bs ren (TreapMap.rap bs) (fun p hp => by
    rw [hoonMap_get]; exact (TreapMap.mem_rap bs p.1 p.2).1 hp) (some HoonMap.empty)

/-! ## `TsCoreAt` from the link of the gate of the fold -/

/-- **The link of the gate of the `+rep:by` of the renaming branch**,
stated: on a pair `(k, b)` of the blocks `bs` and the accumulator `new`, the
gate `tsGBody` (`?:  &(!=(0w0 k) (bypassable & b))  new`, else `(rename
b(fin [%bom ~]))` with `fin` from `+chase-fin`, put at `k` by `+put:by`) is
`renameStep`.  Not proved: it needs `+bypassable` (core arm `46`), the gate
`mrInner` of `+map-regs` on a block with `fin` `[%bom ~]`, `+chase-fin` (core
arm `382`) and `+put:by` (`put_gate`). -/
def TsStepAt (ctx : Noun) : Prop :=
  ∀ (SB Bo BN D G : Noun) (o sub : Nat) (bs new : TreapMap mugF Blob) (p : Nat × Blob),
    p ∈ TreapMap.rap bs →
    nock (C tsGBody (C (C (Tr.pairNoun Blob.toNoun p) (HoonMap.toNoun Blob.toNoun new))
        (tsY SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub))) tsGBody
      = (renameStep bs (renReg sub 1) new p).map (HoonMap.toNoun Blob.toNoun)

/-- **`TsCoreAt` from the link of the gate of the fold**: the arm `$`
(`ts_dol`), the renaming branch (`ts_rename`), the `+rep:by` over the blocks
in pre-order (`rep_gate_list`, `TreapMap.preorder_toNoun`), and the model's
`renameBlocks` in the order of `rap` (`renameBlocks_rap`). -/
theorem ts_core_at {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK)
    (hst : TsStepAt ctx) : TsCoreAt ctx := by
  intro g x sub o start _ _
  generalize HoonMap.put (HoonMap.del g.blocks o) 0 start = bs
  change nock (tsSt (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun bs)
      (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door
      (genNoun g x) ctx o sub) (C (A 9) (C (A 190) (C (A 0) (A 1)))) = _
  rw [ts_dol hc, ts_rename hc h7]
  have ha : Tree (HoonMap.toNoun Blob.toNoun bs) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bs.2 Blob.toNoun)
  have hL : preorder (HoonMap.toNoun Blob.toNoun bs) = (TreapMap.rap bs).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bs
  have hrep := rep_gate_list (Tr.pairNoun Blob.toNoun) (HoonMap.toNoun Blob.toNoun)
    (fun p s => renameStep bs (renReg sub 1) s p) by.battery layer2 tsGBody tsGE
    (tsY (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun bs) (HoonMap.toNoun Blob.toNoun g.blocks)
      (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x) ctx o sub)
    _ ha _ hL HoonMap.empty (fun p hp s => hst _ _ _ _ _ o sub bs s p hp)
  rw [HoonMap.toNoun_empty] at hrep
  rw [hrep, renameBlocks_rap]
  cases (TreapMap.rap bs).foldlM (fun s p => renameStep bs (renReg sub 1) s p) HoonMap.empty <;> rfl

/-- **`TsAt` from the link of the gate of the fold.** -/
theorem ts_at_of_step {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK)
    (hst : TsStepAt ctx) : TsAt ctx :=
  ts_at_of_core hc (ts_core_at hc h7 hst)

/-- **The end of `+compile-unary` from its entry state, given the gate of
the fold of `+to-straight`**: `cu_finish_core` with `TsCoreAt` from
`ts_core_at`, so that only `TsStepAt` is assumed. -/
theorem cu_finish_step {ctx : Noun} (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod)
    (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (cache mono sup : Noun) (hst : TsStepAt ctx) :
    ((nock (crSubj mono n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) sup
        (compCore genEntry (cuRest cache) ctx)) crDol).bind (fun R =>
      (slot? 2 R).bind fun N => (slot? 3 R).bind fun G =>
        nock (C kerfBat (C N (C comp.door (C G ctx)))) kerfBat)).bind (fun K =>
      (slot? 4 K).bind fun O => (slot? 5 K).bind fun SUB => (slot? 3 K).bind fun G2 =>
        nock (C tsBat (C (tsSample O SUB) (C comp.door (C G2 ctx)))) tsBat)
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map Straight.toNoun :=
  cu_finish_core h7 hcode n hpu h6 ht cache mono sup
    (ts_core_at (comp_ctx_pill ctx h7).1 h7 hst)

/-! ## `+bypassable` -/

/-- The body of the gate `+bypassable` (core arm `46`, battery axis `30`). -/
def tsBypBody : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 54)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 110)))) (C (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 0) (A 12)) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 222)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))

theorem ts_byp_at : slot? 30 tsCoreBat = some (C (A 8) (C (C (A 1) tsGE) (C (C (A 1) tsBypBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- **`+bypassable`** on `[& b]`: `bypassable true b`. -/
theorem ts_byp (S : Noun) (b : Blob) :
    nock (C tsBypBody (C (C (A 0) (Blob.toNoun b)) S)) tsBypBody = some (loob (bypassable true b)) := by
  obtain ⟨par, body, fin⟩ := b
  cases par with
  | cons r rs => simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob]
  | nil =>
    cases body with
    | cons op ops => simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob]
    | nil =>
      cases fin with
      | hop t =>
        obtain ⟨args, there⟩ := t
        cases args <;> simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob,
          Termin.toNoun, Jmp.toNoun, Tag.hop]
      | _ => simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob, Termin.toNoun, Tag.hop,
          Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

end Compiler
end Formalization
