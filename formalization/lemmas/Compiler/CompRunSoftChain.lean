import lemmas.Compiler.CompRunSoftClass
import lemmas.Compiler.CompRunSoftTail

/-! # The corpus's soft members: a chain of `%7`s ending in the soft tail call (README Gaps 19 (g))

Five of the six `%done` compiles with a soft call (`swap` twice, `fld` twice, `rot3`; dumps of
`Ska/SccLoopRealData.lean`) are `[7 p1 [7 p2 .. [7 pk [2 [0 1] [1 f] [~ b ~]]]]]` with every
`pi` soft-free (cons, `%0`, `%1`, `%10`).  `+run` runs the call first (under the member's
`%done`), then each `pi` from the last to the first, at the soft map the call left.

* `SoftCallOk`: what the call takes (code entry, no ring, the need, `sof` in the model, the
  `call.cole` entry, `jets-hot`, and at every rest with `E` the need read, `sure.cache`, and the
  pill's `sof` `&`);
* `SoftChainOk`: the chain, with at each `%7` the `GInv` of the goal the run of `q` returns (a
  fact of the model `runLCS`, the result invariant not yet proved for a soft call);
* `yOkQ_of_S`: `YOkS` gives `YOkQ` at a fixed soft map for `Y` with `soft` kept;
* **`comp_run_softChain`**: the chain in the soft shape `CompRunAtXTS (runLCS env snd msup)`
  under `%done`, at every soft map, given the leaves `LeafQ` at every soft map. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **What the corpus's soft tail call takes**, at `msup`, for the rests with `E`. -/
def SoftCallOk (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (msup : Option Nomm) (f : Noun) (b : Bell) :
    Prop :=
  CodePure cod env b ∧ env.ring b = Option.none ∧ ∃ nb, env.need b = some nb ∧
    env.sof (made (Nomm.n0 1) msup) (Nomm.n0 1) (Nomm.n1 f) b nb = true ∧
    (∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)) ∧ (∃ jh, slot? 54 ctx = some jh) ∧
    ∀ x, E x → NeedRead ctx x b nb ∧ SureNoun env b x ∧ SofRetS env msup ctx (Nomm.n0 1) (Nomm.n1 f) b nb x

/-- **The chain of `%7`s ending in the soft tail call**, with the `GInv` of the goal each `q`
returns. -/
def SoftChainOk (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (cod ctx : Noun) (E : GenRest → Prop)
    (region : List Nat) : Option Nomm → Nomm → Prop
  | msup, Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)) => SoftCallOk env cod ctx E msup f b
  | _, Nomm.n7 p q => SoftFree p = true ∧ SoftChainOk env snd cod ctx E region (some p) q ∧
      ∀ gs nex gs1, runLCS (S := CSet) (Map := TreapMap mugF) env snd (some p) q CGoalL.done region gs
        = some (nex, gs1) → GInv gs1.g nex.goal
  | _, _ => False

/-- `YOkS` gives `YOkQ` at a fixed soft map, for `Y` with `soft` kept. -/
theorem yOkQ_of_S {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (h : YOkS X Y) (M : Noun) :
    YOkQ (fun x => x.soft = M) X (fun a c => Y a c ∧ c.soft = a.soft) :=
  ⟨fun x => ⟨h.refl x, rfl⟩, fun h1 h2 => ⟨h.trans h1.1 h2.1, h2.2.trans h1.2⟩,
    fun hx hy => hy.2.trans hx, fun hX hy => h.pres hX hy.1⟩

/-- **The corpus's soft members in the soft shape**: a `SoftChainOk` nomm under `%done` at every
soft map, against `runLCS env snd msup`, at `XN E msup` and any `Y` with `YOkS`, given the leaves
`%0` / `%1` at every soft map (`LeafQ`). -/
theorem comp_run_softChain (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop)
    (hYS : ∀ msup, YOkS (XN E msup) Y)
    (L : ∀ sm : TreapMap mugF SoftCall,
      LeafQ (fun x => x.soft = softMapNoun sm) env ctx (XN E) (fun a c => Y a c ∧ c.soft = a.soft))
    (region : List Nat) :
    ∀ (n : Nomm) (msup : Option Nomm), SoftChainOk env snd cod ctx E region msup n →
      ∀ gs, CompRunAtXTS (runLCS env snd msup) ctx (XN E msup) Y n CGoalL.done region gs
  | Nomm.n7 p q, msup, ⟨hp, hq, hres⟩, gs => by
    have IH := comp_run_softChain h7 hcode env snd E Y hYS L region q (some p) hq
    exact comp_run_n7TS (hYS msup) env snd msup p q CGoalL.done region gs (IH gs)
      (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
      (fun nex gs1 e => crxts_softFree h7 hcode env snd (XN E) Y gs1 (fun ms => yOkQ_of_S (hYS ms) _)
        (fun ms p' x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩) (L gs1.soft) p hp msup region nex.goal (hres gs nex gs1 e))
  | Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)), msup, hok, gs => by
    obtain ⟨hcd, hri, nb, hnb, hsof, hcole, hhot, hx⟩ := hok
    rintro x mono sup hs ⟨hE, rfl, rfl⟩
    obtain ⟨hrd, hsu, hso⟩ := hx x hE
    exact comp_run_n2_softTailR h7 hcode env snd msup f (pastAt_nd h7 hcode env.cod trivial) b hcd nb region gs
      hri hnb hsof (hYS msup).refl (hYS msup).trans (fun s h => (hYS msup).softY s h) x hs hcole hhot hrd hsu hso

end Compiler
end Formalization
