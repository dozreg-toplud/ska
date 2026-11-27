import lemmas.Compiler.CompCalleeComp
import lemmas.Ska.SccLoopSoftEq

/-! # The run of a member with soft calls: the shape the pill link takes (README Gaps 21.15)

`CompRunAtXT` (`CompCalleeComp.lean`) asks a rest with no soft key at the start
(`x.NoSoft`) and gives the noun of the model's `Gen` with the rest `x'` the threaded run leaves:
the soft map is not in the model.  With soft calls the pill writes `soft.gen` (`+soft-new`,
`+soft-bond`, `+soft-ask`), so the run of a member with a soft call is linked in the shape
**`CompRunAtXTS (runLCS env snd ~)`**: from a rest whose `soft` is the noun of the model's
`soft.gen` (`softMapNoun`), the pill's run gives the noun of the model's `Gen` and of its
`soft.gen`, the rest of the cache threaded as in `CompRunAtXT`.

* `SoftCall.toNoun`, `softMapNoun`: the nouns of `+$soft-call` (line 3005, `aux` `~`) and of
  `soft.gen`;
* `CompRunAtXTS`: the shape;
* **`crxts_of_xt`**: with no soft call (`sof` false at every call), a `CompRunAtXT` of `runLC`
  whose rests keep `soft` at `~` is a `CompRunAtXTS` of `runLCS` from an empty `soft.gen`
  (`runLCS_eq`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The noun of `+$soft-call`: `[kin b rin ned sur plain head last pro out aux req]`, `kin` the
cord `%call`, `%tail` or `%mean`, `aux` `~`. -/
def SoftCall.toNoun (c : SoftCall) : Noun :=
  C (A (if c.kin = 1 then 1818845556 else if c.kin = 0 then 1819042147 else 1851876717))
    (C c.b.toNoun (C (match c.rin with | none => A 0 | some r => C (A 0) r) (C c.ned.toNoun
      (C c.sur.toNoun (C (A c.plain) (C (A c.head) (C (A c.last) (C (A c.pro) (C (A c.out) (C (A 0)
        (c.req.foldr (fun (s, n) acc => C (C (A s) n.toNoun) acc) (A 0))))))))))))

/-- The noun of `soft.gen`. -/
def softMapNoun (m : TreapMap mugF SoftCall) : Noun := HoonMap.toNoun SoftCall.toNoun m

/-- **The threaded run link with soft calls**: from every rest whose `soft` is the noun of the
model's `soft.gen` and that `X` admits, the pill's `$` of `+run` gives the noun of the model's
product, its `Gen` and its `soft.gen`, with the rest `x'` (cache, `sofs`) that `Y` relates. -/
def CompRunAtXTS (R : Nomm → CGoalL CSet → List Nat → CMS (TreapMap mugF) (NextL CSet)) (ctx : Noun)
    (X : GenRest → Noun → Noun → Prop) (Y : GenRest → GenRest → Prop) (n : Nomm) (goal : CGoalL CSet)
    (region : List Nat) (gs : GenSf (TreapMap mugF)) : Prop :=
  ∀ (x : GenRest) (mono sup : Noun), x.soft = softMapNoun gs.soft → X x mono sup → ∃ x', Y x x' ∧
    nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore gs.g x ctx)) crDol
      = (R n goal region gs).map fun p =>
          C p.1.goal.toNoun (genNoun p.2.g { x' with soft := softMapNoun p.2.soft })

theorem softMapNoun_empty : softMapNoun (HoonMap.empty : TreapMap mugF SoftCall) = A 0 :=
  HoonMap.toNoun_empty _

theorem noSoft_of_nil {x : GenRest} (h : x.soft = A 0) : x.NoSoft := by
  intro o; unfold GenRest.SoftOut; rw [h]; rfl

/-- **Without soft calls, the threaded link of `runLC` is the one of `runLCS`.** -/
theorem crxts_of_xt (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (hsof : ∀ m p q b n, env.sof m p q b n = false) (sup : Option Nomm) {ctx : Noun}
    {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)} (hYs : ∀ x x', Y x x' → x'.soft = A 0)
    (h : CompRunAtXT (runLC env sup) ctx X Y n goal region g) :
    CompRunAtXTS (runLCS env snd sup) ctx X Y n goal region (GenSf.ofGen g) := by
  intro x mono sup' hx hX
  have hx0 : x.soft = A 0 := by rw [hx]; exact softMapNoun_empty
  obtain ⟨x', hY', he⟩ := h x mono sup' (noSoft_of_nil hx0) hX
  refine ⟨x', hY', ?_⟩
  have hx' : { x' with soft := A 0 } = x' := by
    have h0 := hYs _ _ hY'
    cases x'; simp only at h0 ⊢; rw [h0]
  show nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup' (compCore g x ctx)) crDol = _
  rw [he, runLCS_eq env snd hsof n sup goal region g]
  cases runLC env sup n goal region g with
  | none => rfl
  | some p =>
    simp only [Option.map_some, embS, GenSf.ofGen, softMapNoun_empty, hx']

end Compiler
end Formalization
