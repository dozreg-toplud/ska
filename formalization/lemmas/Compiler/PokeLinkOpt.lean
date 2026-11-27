import lemmas.Compiler.PokeLinkFull
import lemmas.Compiler.OptLinkTotalAvail

/-!
# The link of `+optimize` in the `%full` branch (`OptLink`), stated so that it is true

`OptLink A optP` (`Compiler/PokeLink.lean`) asks the pill's `+optimize` to
return on EVERY straight.  It does not: `+optimize-once` starts with
`(bb-topo blocks.s)`, which reads block `0` with `+got:by`, so a straight
with no blocks crashes (`tools/hoon/optempty.hoon`).  The model's
`A.optimize : Straight → Straight` is total, so no `A` makes `OptLink A optP`
true, and the theorems that assume it (`pokeN_full`, `pokeModel_full`) are
vacuous.  Restated here:

* `optimizeP`: the model's `+optimize` is the pill's, read back (the straight
  whose noun the gate returns, where it returns one; the input elsewhere);
* `OptTotal s`: the class where the pill's `+optimize` is proved to return,
  as track H and track D state it (`GateTotalN`, `OptTotalMono`), with the
  model's passes at some fuels;
* `OptLinkOn Cls A opt`: `OptLink` on the straights of `Cls`;
  `optLinkOn_optimizeP`: it holds for `OptTotal` and every `A` with
  `A.optimize = optimizeP` (and `optLinkOn_answers` on the larger class
  where the gate answers a straight);
* `optimizeP_ref`: on `OptTotal`, `optimizeP` is `optimizeF` with the pill's
  passes at some fuels, which is `OptRef`'s form (track G), and `optP_hpill`:
  the hypothesis `hpill` of `optRef_fragX'` / `optRef_of_total` for
  `optimizeP` on every straight of `OptTotal`;
* `optTotal_of_inv` (from `gateTotalN`: `StInv`, `DInvR`, `ReadsIn`),
  `optTotal_finishLUX`, `optTotal_finishLFX` (raw output of `FragX`);
* `OptInAt Cls A st s f`: the straight the model's `%full` hands to
  `+optimize` at the state `st` is in `Cls` (a statement on the model alone:
  track D's `OptTotalMono` on the class of the compile);
* `pokeN_fullO`, `pokeModel_fullO`: `pokeN_full`, `pokeModel_full` with
  `OptLinkOn Cls` and `OptInAt Cls` at the state in place of `OptLink`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- `optP` is the body of `+optimize` on the gate `optC` builds. -/
theorem optP_eq (s : Noun) : optP s = nock (C optBody (C s optC)) optBody := by
  simp [optP, slamAt, opt_at, opt_arm, nock_exec]

/-! ## The class where the pill's `+optimize` returns -/

/-- **The class of totality**: the pill's `+optimize` returns on `s` the noun
of the model's `optimizeF` with the pill's passes at some fuels (the form of
`GateTotalN`, `OptTotalMono`, `OptTotalNary`). -/
def OptTotal (s : Straight (TreapMap mugF)) : Prop :=
  ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
    Opt.switchChains sfuel⟩ s = some s' ∧ nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun

/-- The class where the pill's `+optimize` answers a straight (it contains
`OptTotal`). -/
def OptAnswers (s : Straight (TreapMap mugF)) : Prop :=
  ∃ s' : Straight (TreapMap mugF), optP s.toNoun = some s'.toNoun

theorem optAnswers_of_total {s : Straight (TreapMap mugF)} (h : OptTotal s) : OptAnswers s := by
  obtain ⟨_, _, s', _, h2⟩ := h
  exact ⟨s', by rw [optP_eq, h2]⟩

/-- **The model's `+optimize`: the pill's, read back.**  Where the gate
returns the noun of a straight, that straight (unique, `straight_toNoun_inj`);
elsewhere the input (a value the model never shows, since the pill crashes
there and `OptInAt` keeps the model's compile off those straights). -/
noncomputable def optimizeP (s : Straight (TreapMap mugF)) : Straight (TreapMap mugF) :=
  open Classical in if h : OptAnswers s then Classical.choose h else s

theorem optP_optimizeP {s : Straight (TreapMap mugF)} (h : OptAnswers s) :
    optP s.toNoun = some (optimizeP s).toNoun := by
  unfold optimizeP
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- On the class of totality, `optimizeP` is the model's `optimizeF` with the
pill's passes at some fuels: `OptRef`'s form (`Glue/RawOptIn.lean`). -/
theorem optimizeP_ref {s : Straight (TreapMap mugF)} (h : OptTotal s) :
    ∃ fuel sfuel, Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ s = some (optimizeP s) := by
  obtain ⟨sfuel, fuel, s', h1, h2⟩ := h
  have e := optP_optimizeP (optAnswers_of_total ⟨sfuel, fuel, s', h1, h2⟩)
  rw [optP_eq, h2, Option.some.injEq] at e
  rw [straight_toNoun_inj e] at h1
  exact ⟨fuel, sfuel, h1⟩

/-- The hypothesis `hpill` of track G's `optRef_fragX'` / `optRef_of_total`
for `optimizeP`, on every straight of `OptTotal`. -/
theorem optP_hpill {s : Straight (TreapMap mugF)} (h : OptTotal s) :
    nock (C optBody (C s.toNoun optC)) optBody = some (optimizeP s).toNoun := by
  rw [← optP_eq]
  exact optP_optimizeP (optAnswers_of_total h)

open Raw in
/-- **The class of totality from the facts of the raw output** (track H's
`gateTotalN` with `aliasRetN_of`): `StInv`, `DInvR`, `ReadsIn`. -/
theorem optTotal_of_inv {ρ : Nat → Nat} {L : List Nat} {s : Straight (TreapMap mugF)}
    (hI : StInv ρ L s.blocks) (hJ : Opt.DInvR s.blocks) (hR : ReadsIn s.nargs s.blocks) : OptTotal s :=
  gateTotalN ρ L (aliasRetN_of _ (fun l hl => Ana.pickR_mem l hl) ρ L) s hI hJ hR

section
variable {S : Type} [Comp.HoonSet S]

/-- The raw whole-subject code of every nomm of `FragX` is in the class. -/
theorem optTotal_finishLUX {nm : Nomm} (hf : Comp.FragX (S := S) nm) (hc : Comp.sixCount nm ≤ 255)
    {c' : Straight (TreapMap mugF)} (h : Comp.finishLU (S := S) (Map := TreapMap mugF) nm = some c') :
    OptTotal c' :=
  optimize_total_finishLUX hf hc h

/-- The raw n-ary code of every nomm of `FragX` (nothing baked) is in the
class. -/
theorem optTotal_finishLFX {nm : Nomm} (hf : Comp.FragX (S := S) nm) (hc : Comp.sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Comp.Need → Comp.Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight (TreapMap mugF)} (h : Comp.finishLF (S := S) (Map := TreapMap mugF) nm ord less bake = some c') :
    OptTotal c' :=
  optimize_total_finishLFX hf hc hbake h

end

/-! ## The link on a class -/

/-- **`OptLink` on the straights of `Cls`.** -/
def OptLinkOn (Cls : Straight (TreapMap mugF) → Prop) (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (opt : Noun → Option Noun) : Prop :=
  ∀ s, Cls s → opt s.toNoun = some (A.optimize s).toNoun

theorem optLink_iff_on (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (opt : Noun → Option Noun) :
    OptLink A opt ↔ OptLinkOn (fun _ => True) A opt :=
  ⟨fun h s _ => h s, fun h s => h s trivial⟩

/-- **The link of `+optimize`, proved**, on the class where the gate answers
a straight, for every `A` whose `optimize` is the pill's read back. -/
theorem optLinkOn_answers {A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    (hA : A.optimize = optimizeP) : OptLinkOn OptAnswers A optP := by
  intro s hs
  rw [hA]
  exact optP_optimizeP hs

/-- **The link of `+optimize`, proved, on the class of totality.** -/
theorem optLinkOn_optimizeP {A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    (hA : A.optimize = optimizeP) : OptLinkOn OptTotal A optP :=
  fun s hs => optLinkOn_answers hA s (optAnswers_of_total hs)

/-- `OptLinkOn` is antitone in the class. -/
theorem OptLinkOn.mono {Cls Cls' : Straight (TreapMap mugF) → Prop} {A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    {opt : Noun → Option Noun} (h : OptLinkOn Cls A opt) (hc : ∀ s, Cls' s → Cls s) : OptLinkOn Cls' A opt :=
  fun s hs => h s (hc s hs)

/-! ## `pokeModel` on `%full` with the link on a class -/

section Model

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))

/-- **The straight the model's `%full` hands to `+optimize`, at the state `st`
on `[s f]`, is in `Cls`**: after `+ska-poke`, past a root that is not a
jetted arm, `+scc-of` and `+compiled-mono` (cached or compiled).  A statement
on the model alone (on reached states, track D's `OptTotalMono` for the class
of the compile, with the cache holding only what the model compiled). -/
def OptInAt (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) (s f : Noun) : Prop :=
  ∀ r q p, Ar.skaPoke s f st.long st.jets st.hot = some r → Ar.jetRoot r.2.2.1 st.hot r.1 = none →
    Ar.sccOf r.1 r.2.1 st.cache.sccs = some q →
    compiledMono Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 = some p →
    Cls p.1

/-- **`pokeN_full` with the link of `+optimize` on a class**: at a state
whose `%full` hands `+optimize` a straight of `Cls`. -/
theorem pokeN_fullO {Cls : Straight (TreapMap mugF) → Prop}
    (hS : SkaLink fl Ar skaP) (hJ : JetRootLinkR fl Ar jrP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP) (st : PSt) (s f₁ f₂ : Noun)
    (hIn : OptInAt Ar Cls st s (C f₁ f₂)) :
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s (C f₁ f₂))).map fun r => C r.1.toNoun r.2 := by
  rw [fullBranchIs fl st s f₁ f₂, liftPoke_enc_fl]
  unfold pillFull
  rw [hS]
  simp only [pokeS]
  cases e1 : Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [hJ st s (C f₁ f₂) r e1]
    simp only [Option.bind_some]
    cases e2 : Ar.jetRoot r.2.2.1 st.hot r.1 with
    | some out => simp [Prod.toNoun]
    | none =>
      simp only [Option.map_none]
      unfold compileStep
      rw [hC]
      cases e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some, if_true]
        rw [hM]
        cases e4 : compiledMono Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          rw [hO p.1 (hIn r q p e1 e2 e3 e4)]
          simp [Prod.toNoun]

/-- **`pokeModel` on every `%full` at a state, with the link of `+optimize`
on a class.** -/
theorem pokeModel_fullO {Cls : Straight (TreapMap mugF) → Prop}
    (hS : SkaLink fl Ar skaP) (hJ : JetRootLinkR fl Ar jrP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (s f : Noun)
    (hIn : OptInAt Ar Cls st s f) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ => exact pokeN_fullO fl Ar hS hJ hC hM hO st s f₁ f₂ hIn

/-- **The same with `A.optimize = optimizeP`**: the link of `+optimize` is
gone; what is left of it is `OptInAt OptTotal` at the state. -/
theorem pokeModel_fullP (hA : Ar.optimize = optimizeP)
    (hS : SkaLink fl Ar skaP) (hJ : JetRootLinkR fl Ar jrP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (s f : Noun)
    (hIn : OptInAt Ar OptTotal st s f) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullO fl Ar hS hJ hC hM (optLinkOn_optimizeP hA) hAt st s f hIn

end Model

end Compiler
end Formalization
