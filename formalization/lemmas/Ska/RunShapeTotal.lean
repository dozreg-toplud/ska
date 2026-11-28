import lemmas.Ska.RunShape

/-!
# Totality of the tests of `+run-shape` (track A, 2026-11-28)

`+run-shape` crashes (the model returns `none`) in `+sound` only where `+sound-far` does: a `%10` at
axis `0` on the product path (`+need-ord-edit` on `(cap 0)`), or a callee met with depth left that
has no code entry (`(~(got by code) b)`); that is `SfClosed env.cod 3` (`soundFar_some`).  `+need-soft`
crashes only on the sock `%void` (`needSoft_some`), `+hinted` only on a direct callee with no code
entry on its walk.  So the conditions of `RsClsM` and the `soft` clause of `ShapeCallT` are facts of
the nomm and the code table:

* **`soundS_total`**: `SfClosed env.cod 3 nom → soundS env nom ned ≠ none`.
* **`unsS_total`**: `SfClosed` of both branches `→ unsS env q r ned ≠ none`.
* `PureKnown`, **`hinted_total`**: every direct callee on the walk of `+hinted` has a `pure` flag.
* **`softTest_total`**: on a key `~`, `SfClosed` of `(made p sup)`, a `less` that is not `%void`
  and `PureKnown` of `p` and `q`; on a key `[~ k]` nothing.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

theorem orB_ne_none' {x y : Option Bool} (hx : x ≠ Option.none) (hy : y ≠ Option.none) : orB x y ≠ Option.none := by
  obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp hx
  obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp hy
  cases a <;> simp [orB]

/-- **`+sound` returns on every nomm closed for `+sound-far` at depth `3`.** -/
theorem soundS_total (env : ShapeEnv) {nom : Nomm} (h : SfClosed env.cod 3 nom) (ned : NeedOrd) :
    soundS env nom ned ≠ Option.none := by
  obtain ⟨s, hs⟩ := soundFar_some env.cod 3 nom h ned
  simp [soundS, hs]

/-- **`!&((sound q ned) (sound r ned))` returns** when both branches are closed. -/
theorem unsS_total (env : ShapeEnv) {q r : Nomm} (hq : SfClosed env.cod 3 q) (hr : SfClosed env.cod 3 r)
    (ned : NeedOrd) : unsS env q r ned ≠ Option.none := by
  obtain ⟨s, hs⟩ := soundFar_some env.cod 3 q hq ned
  obtain ⟨t, ht⟩ := soundFar_some env.cod 3 r hr ned
  obtain ⟨c, hc⟩ := andO_some (x := soundS env q ned) (y := soundS env r ned) ⟨s, hs⟩ ⟨t, ht⟩
  simp [unsS, hc]

/-- **Every direct callee on the walk of `+hinted` has a `pure` flag** (`%12` and `%mean` stop it). -/
def PureKnown (pu : Bell → Option Bool) : Nomm → Prop
  | Nomm.n3 p => PureKnown pu p
  | Nomm.n4 p => PureKnown pu p
  | Nomm.cons p q => PureKnown pu p ∧ PureKnown pu q
  | Nomm.n5 p q => PureKnown pu p ∧ PureKnown pu q
  | Nomm.n6 p q r => PureKnown pu p ∧ PureKnown pu q ∧ PureKnown pu r
  | Nomm.n7 p q => PureKnown pu p ∧ PureKnown pu q
  | Nomm.n10 _ v q => PureKnown pu v ∧ PureKnown pu q
  | Nomm.n2 p q (some (b, _)) => pu b ≠ Option.none ∧ PureKnown pu p ∧ PureKnown pu q
  | Nomm.n2 _ _ Option.none => True
  | Nomm.n11s _ q _ => PureKnown pu q
  | Nomm.n11d _ h q _ => PureKnown pu h ∧ PureKnown pu q
  | _ => True

/-- **`+hinted` returns** on every nomm of `PureKnown`. -/
theorem hinted_total (pu : Bell → Option Bool) : ∀ n, PureKnown pu n → hinted pu n ≠ Option.none
  | Nomm.n0 _, _ => by simp [hinted]
  | Nomm.n1 _, _ => by simp [hinted]
  | Nomm.n3 p, h => by simp only [hinted]; exact hinted_total pu p h
  | Nomm.n4 p, h => by simp only [hinted]; exact hinted_total pu p h
  | Nomm.mean _ _ _ _ _, _ => by simp [hinted]
  | Nomm.n12 _ _, _ => by simp [hinted]
  | Nomm.cons p q, h => by
    simp only [hinted]; exact orB_ne_none' (hinted_total pu p h.1) (hinted_total pu q h.2)
  | Nomm.n5 p q, h => by
    simp only [hinted]; exact orB_ne_none' (hinted_total pu p h.1) (hinted_total pu q h.2)
  | Nomm.n6 p q r, h => by
    simp only [hinted]
    exact orB_ne_none' (hinted_total pu p h.1) (orB_ne_none' (hinted_total pu q h.2.1) (hinted_total pu r h.2.2))
  | Nomm.n7 p q, h => by
    simp only [hinted]; exact orB_ne_none' (hinted_total pu p h.1) (hinted_total pu q h.2)
  | Nomm.n10 _ v q, h => by
    simp only [hinted]; exact orB_ne_none' (hinted_total pu v h.1) (hinted_total pu q h.2)
  | Nomm.n2 p q Option.none, _ => by simp [hinted]
  | Nomm.n2 p q (some (b, k)), h => by
    obtain ⟨hb, hp, hq⟩ := h
    simp only [hinted]
    refine orB_ne_none' ?_ (orB_ne_none' (hinted_total pu p hp) (hinted_total pu q hq))
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hb
    simp [hv]
  | Nomm.n11s _ q _, h => by
    simp only [hinted]; exact orB_ne_none' (by simp) (hinted_total pu q h)
  | Nomm.n11d _ hh q _, h => by
    simp only [hinted]
    exact orB_ne_none' (by simp) (orB_ne_none' (hinted_total pu hh h.1) (hinted_total pu q h.2))

/-- **The soft test of the direct call returns**: on a key `[~ k]` always; on a key `~` when
`(made p sup)` is closed for `+sound-far`, the callee's `less` is not `%void` (`+need-soft`) and the
callees on the walks of `+hinted` over `p` and `q` have `pure` flags. -/
theorem softTest_total (env : ShapeEnv) (p q : Nomm) (b : Bell) (k : Option Noun) (ned sur : NeedOrd)
    (sup : Option Nomm)
    (h : k = Option.none → SfClosed env.cod 3 (made p sup) ∧ b.less ≠ Sock.void ∧
      PureKnown env.pure p ∧ PureKnown env.pure q) :
    softTest env p q b k ned sur sup ≠ Option.none := by
  rcases k with _ | kk
  · obtain ⟨hsf, hv, hpp, hpq⟩ := h rfl
    obtain ⟨s, hs⟩ := soundFar_some env.cod 3 (made p sup) hsf ned
    simp only [softTest, soundS, hs, Option.bind_some]
    cases s with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨t, ht⟩ := needSoft_some ned sur b.less hv
      rw [ht]
      exact orB_ne_none' (by simp) (orB_ne_none' (hinted_total env.pure p hpp) (hinted_total env.pure q hpq))
  · simp [softTest]

end Comp
end SkaModel
end Formalization
