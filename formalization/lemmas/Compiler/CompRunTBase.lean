import lemmas.Compiler.CompCalleeComp

/-!
# The threaded run link: the invariant on rests (README Gaps 19 (g))

A miss of `+callee-need` compiles the callee's SCC and replaces `cache`
(`ccc_miss`), so a run of `+run` takes a rest `x` in and gives `x'` out
(`CompRunAtXT`).  What a composing case needs of the relation `Y` between the
rest a run starts at and the rest it ends at, and of the rest predicate `X`,
is stated once (`YOk`); the concrete relation is `Ext`.

* `YOk X Y`: `Y` reflexive, transitive, keeping `NoSoft` and `X`.
* `Ext x x'`: `soft` and `sofs` unchanged, and every entry of `nary.cache`
  (axis `2` of `cache`) and of `sure.cache` (axis `31`) is still there with
  the same value (a miss only adds fresh entries).  `ext_refl`, `ext_trans`,
  `ext_noSoft`.
* Monotone in `Ext`: `needRead_ext` (every read-only case of `+callee-need`
  that held at `x` holds at `x'`), `SureHit`, `sureHit_ext` (an entry of
  `sure.cache`), `sureNoun_of_hit`.  Not monotone: `SureNoun` by absence (the
  case `env.sure b = [%none ~]` with no entry), which a later run may rely on
  only through the facts of the miss that made the entry.
* `PartRT`: what a composing case takes of a threaded part.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **What a composing case needs of `X` and `Y`**: `Y` is a preorder whose
steps keep `NoSoft` and the rest predicate `X`. -/
structure YOk (X : GenRest → Noun → Noun → Prop) (Y : GenRest → GenRest → Prop) : Prop where
  refl : ∀ x, Y x x
  trans : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z
  soft : ∀ {x y : GenRest}, x.NoSoft → Y x y → y.NoSoft
  pres : ∀ {x y : GenRest} {mono sup : Noun}, X x mono sup → Y x y → X y mono sup

/-- Every entry of the map noun `N` is an entry of `N'` with the same value. -/
def MapSub (N N' : Noun) : Prop :=
  ∀ k u, getF mugF k N = some (C (A 0) u) → getF mugF k N' = some (C (A 0) u)

/-- The map at axis `a` of `cache` only gains entries from `x` to `x'`. -/
def CacheSub (a : Nat) (x x' : GenRest) : Prop :=
  ∀ N, slot? a x.cache = some N → ∃ N', slot? a x'.cache = some N' ∧ MapSub N N'

/-- **The rests a miss leaves** (README Gaps 19 (g)): `soft` and `sofs` as
they were, and `nary.cache` (axis `2`), `sure.cache` (axis `31`) only gain
entries.  Zero or more miss steps, each `+compile-scc-in` putting fresh
entries (`uni`), give `Ext`. -/
def Ext (x x' : GenRest) : Prop :=
  x'.soft = x.soft ∧ x'.sofs = x.sofs ∧ CacheSub 2 x x' ∧ CacheSub 31 x x'

theorem mapSub_refl (N : Noun) : MapSub N N := fun _ _ h => h

theorem mapSub_trans {N1 N2 N3 : Noun} (h1 : MapSub N1 N2) (h2 : MapSub N2 N3) : MapSub N1 N3 :=
  fun k u h => h2 k u (h1 k u h)

theorem cacheSub_refl (a : Nat) (x : GenRest) : CacheSub a x x := fun N h => ⟨N, h, mapSub_refl N⟩

theorem cacheSub_trans {a : Nat} {x y z : GenRest} (h1 : CacheSub a x y) (h2 : CacheSub a y z) : CacheSub a x z := by
  intro N hN
  obtain ⟨N1, h1', s1⟩ := h1 N hN
  obtain ⟨N2, h2', s2⟩ := h2 N1 h1'
  exact ⟨N2, h2', mapSub_trans s1 s2⟩

theorem ext_refl (x : GenRest) : Ext x x := ⟨rfl, rfl, cacheSub_refl 2 x, cacheSub_refl 31 x⟩

theorem ext_trans {x y z : GenRest} (h1 : Ext x y) (h2 : Ext y z) : Ext x z :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, cacheSub_trans h1.2.2.1 h2.2.2.1, cacheSub_trans h1.2.2.2 h2.2.2.2⟩

theorem ext_noSoft {x y : GenRest} (hx : x.NoSoft) (h : Ext x y) : y.NoSoft := by
  intro o
  have := hx o
  unfold GenRest.SoftOut at this ⊢
  rw [h.1]
  exact this

/-- `Ext` with a rest predicate closed under it is a `YOk`. -/
theorem yOk_ext {X : GenRest → Noun → Noun → Prop}
    (hX : ∀ {x y : GenRest} {mono sup : Noun}, X x mono sup → Ext x y → X y mono sup) : YOk X Ext :=
  ⟨ext_refl, ext_trans, ext_noSoft, hX⟩

/-- At `XM E msup`, `YOk` asks that `E` be closed under `Y`. -/
theorem yOk_xm {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} (msup : Option Nomm)
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hs : ∀ {x y : GenRest}, x.NoSoft → Y x y → y.NoSoft) (hE : ∀ {x y : GenRest}, E x → Y x y → E y) :
    YOk (XM E msup) Y :=
  ⟨hr, ht, hs, fun hX hy => ⟨hE hX.1 hy, hX.2.1, hX.2.2⟩⟩

/-- A threaded result from the current rest `x` is one from the rest `x0`
the lemma started at, given `Y x0 x`. -/
theorem xt_trans {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (hYk : YOk X Y)
    {x0 x : GenRest} (h0 : Y x0 x) {P : GenRest → Prop} (h : ∃ x', Y x x' ∧ P x') : ∃ x', Y x0 x' ∧ P x' := by
  obtain ⟨x', hy, hp⟩ := h
  exact ⟨x', hYk.trans h0 hy, hp⟩

/-! ## What is monotone in `Ext` -/

/-- **The read-only cases of `+callee-need` are monotone**: the cases `loc`
and `top` read only the context, the case `nary` an entry of `nary.cache`,
which `Ext` keeps. -/
theorem needRead_ext {x x' : GenRest} {b : Bell} {nb : NeedOrd} (h : NeedRead ctx x b nb) (he : Ext x x') :
    NeedRead ctx x' b nb := by
  cases h with
  | loc h1 h2 h3 h4 h5 => exact NeedRead.loc h1 h2 h3 h4 h5
  | top h1 h2 h3 h4 h5 h6 => exact NeedRead.top h1 h2 h3 h4 h5 h6
  | @nary S N u h1 h2 h3 h4 h5 =>
    obtain ⟨N', h3', hs⟩ := he.2.2.1 N h3
    exact NeedRead.nary h1 h2 h3' (hs _ _ h4) h5

/-- An entry of `b` in `sure.cache` with the value `env.sure b`. -/
def SureHit (env : CallEnv) (b : Bell) (x : GenRest) : Prop :=
  ∃ S, slot? 31 x.cache = some S ∧ getF mugF b.toNoun S = some (C (A 0) (env.sure b).toNoun)

theorem sureHit_ext {env : CallEnv} {b : Bell} {x x' : GenRest} (h : SureHit env b x) (he : Ext x x') :
    SureHit env b x' := by
  obtain ⟨S, hS, hg⟩ := h
  obtain ⟨S', hS', hs⟩ := he.2.2.2 S hS
  exact ⟨S', hS', hs _ _ hg⟩

theorem sureNoun_of_hit {env : CallEnv} {b : Bell} {x : GenRest} (h : SureHit env b x) : SureNoun env b x := by
  obtain ⟨S, hS, hg⟩ := h
  exact ⟨S, hS, Or.inl hg⟩

/-! ## A threaded part -/

/-- **What a composing case takes of a threaded part**: the threaded link on
every goal with `GInv`, the result, and `+past`. -/
structure PartRT (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (X : GenRest → Noun → Noun → Prop)
    (Y : GenRest → GenRest → Prop) (n : Nomm) (region : List Nat) : Prop where
  link : ∀ (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal →
    CompRunAtXT (runLCM env true msup) ctx X Y n goal region g
  res : ResForR (runLCM env true msup) n region
  past : PastAt ctx env.cod n

/-- **A part with no miss is a threaded part** for every reflexive `Y`. -/
theorem partRT_of_r {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop}
    {Y : GenRest → GenRest → Prop} (hY : ∀ x, Y x x) {n : Nomm} {region : List Nat}
    (P : PartR env msup ctx X n region) : PartRT env msup ctx X Y n region :=
  ⟨fun goal g hi => crxt_of_x hY (P.link goal g hi), P.res, P.past⟩

/-- A threaded part at `Y = (· = ·)` is a part. -/
theorem partR_of_rt_eq {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {n : Nomm}
    {region : List Nat} (P : PartRT env msup ctx X (· = ·) n region) : PartR env msup ctx X n region :=
  ⟨fun goal g hi => crx_of_xt_eq (P.link goal g hi), P.res, P.past⟩

end Compiler
end Formalization
