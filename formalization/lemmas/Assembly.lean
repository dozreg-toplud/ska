import lemmas.Compiler.Connect
import lemmas.Compiler.PokeFrame
import lemmas.Compiler.ListMold
import lemmas.Compiler.Validate
import lemmas.Ska.Statements
import lemmas.Pill.Cue.Root
import lemmas.Compiler.OvumMold

/-!
# The assembly

`Loads`, `Meek`, `Weak`, `Converse` and `Halts` of `core/Statement.lean`, so
`Full`, from the hypotheses below and nothing else (`full_of`).  Each
hypothesis is a `def … : Prop` that names its owner; `Gap` lists them all.
This file is the remaining gap of the whole project.

The way through:

1. The pill's core is `core` of `lemmas/Pill` (`isCore_eq`, from `CueRoot`).
2. The outer `+poke` slams the inner one and puts its core back at axis `7`
   (`poke_iff`, proved here from the pill's Nock).
3. Every core that `Reach` allows is `[ob [interp.battery cr]]` with `CorIn cr`
   and `cr` reached by the model (`ReachI`) from the pill's `cor`
   (`reach_model`), by induction on `Reach` with `poke_iff`, `top_iff` and
   `mook_iff`.  `Reach` pokes any noun that is not a hot `%jets` and runs
   `+eval-mook` on any noun: `pokeValid` (from `OvumMold`) and `MookOther`
   say that the pill
   does nothing there that the model cannot follow.
4. On such cores the statements are the model's (`meek_reach`, `weak_reach`,
   `converse_reach`), through `top_iff`, `run_iff` and `mock_iff`.
-/

namespace Formalization
namespace Assembly

open Nock Pill SkaModel Hoon Compiler

/-! ## The outer `+poke` -/

/-- The outer battery: the head of the pill's core. -/
def ob : Noun :=
  match core with
  | Noun.cell b _ => b
  | Noun.atom _ => A 0

theorem core_eq : core = C ob (icore cor) := by kernel_rfl

/-- The battery of the gate that the outer `+poke` builds:
`=^  p=prod  ..^poke  (^poke ovo)`, then `[p ..poke]`. -/
def opokeBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 23) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 63) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 0) (A 2)) (C (A 0) (A 15)))))))))))

/-- The arm of the outer `+poke`, which builds its gate. -/
def opokeArm : Noun :=
  C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) opokeBat) (C (A 0) (A 1))))

theorem core_opoke : slot? Ska.axPoke core = some opokeArm := by
  unfold Ska.axPoke; kernel_rfl

theorem ob_opoke (cr : Noun) : slot? Ska.axPoke (C ob (icore cr)) = some opokeArm := by
  have h := core_opoke
  rw [core_eq] at h
  simpa [Ska.axPoke, nock_exec] using h

/-- The gate of the outer `+poke` slams the inner `+poke` of the compiler's
core `cr` (`pokeN`), and puts the core it returns back at `axInner`. -/
theorem opoke_run (cr ovo : Noun) :
    nock (C opokeBat (C ovo (C ob (icore cr)))) opokeBat =
      (pokeN cr ovo).bind fun r => match r with
        | Noun.cell p c' => some (C p (C ob (icore c')))
        | Noun.atom _ => none := by
  unfold pokeN
  nock_open opokeBat
  simp only [nock_exec, Ska.axPoke]
  cases h1 : slot? 23 cr with
  | none => simp
  | some a =>
  cases h2 : nock cr a with
  | none => simp [h2]
  | some g =>
  cases h3 : edit? 6 ovo g with
  | none => simp [h2, h3]
  | some g' =>
  cases h4 : slot? 2 g' with
  | none => simp [h2, h3, h4]
  | some f =>
  cases h5 : nock g' f with
  | none => simp [h2, h3, h4, h5]
  | some r =>
  cases r with
  | atom n => simp [nock_exec, h2, h3, h4, h5]
  | cell p c' => simp [nock_exec, h2, h3, h4, h5]

theorem opoke_pull (cr : Noun) :
    nock (C ob (icore cr)) (n3 (A 9) (A Ska.axPoke) (slot 1)) =
      some (C opokeBat (C (A 0) (C ob (icore cr)))) := by
  have h := ob_opoke cr
  simp only [Ska.axPoke] at h
  simp [Ska.axPoke, nock_exec, h, opokeArm]

/-- `Poke` of `core/Statement.lean` on a core of the pill's shape: the inner
`+poke` returns `[prod cr']`, and `cr'` goes back in. -/
theorem poke_iff (cr ovo prod core' : Noun) :
    Ska.Poke (C ob (icore cr)) ovo prod core' ↔
      ∃ cr', pokeN cr ovo = some (C prod cr') ∧ core' = C ob (icore cr') := by
  unfold Ska.Poke
  rw [pull_slam (opoke_pull cr), opoke_run]
  constructor
  · intro h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    cases r with
    | atom n => simp at h
    | cell p c' =>
      simp only [Option.some.injEq, Noun.cell.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c', hr, rfl⟩
  · rintro ⟨cr', h, rfl⟩
    simp [h]

/-! ## The hypotheses

Each is a `Prop` about the pill's Nock or about the models, named by what it
says, with the track that owns it.  `lib`, `pk` and `InvC` are parameters:
the Lean model of the arms of `hoon.hoon` that the models take as given, the
model of the compiler's `+poke` on states that are nouns, and the compiler's
invariant. -/

section
variable (lib : Lib) (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (InvC : Noun → Prop)

/-- The pill decodes to the noun `root` of `lemmas/Pill`.  Proved
(`cueRoot`), by `lemmas/CueRel.lean` and the generated `lemmas/Pill/Cue/`. -/
def CueRoot : Prop := cue pill = some root

theorem cueRoot : CueRoot := Pill.Cue.cue_pill

/-- The inner `+poke` of every compiler's core that the pill's `cor` reaches by
pokes and that keeps what the interpreter reads (`CorIn`) computes the model
`pk` on every ovum but a `%jets` that names a jet.  Owner: pill to model
(`lemmas/Compiler/`): `+poke` and the arms it calls, `+ska-poke`,
`+compiled-mono`, `+compiled-nary`, `+optimize` and the arms of the jets. -/
def PokeModel : Prop :=
  ∀ cr, CorIn cr → ∀ ov : Ovum, ¬ Ska.Hot ov.toNoun →
    pokeN cr ov.toNoun = (pk cr ov).map fun r => C r.1.toNoun r.2

/-- The mold `ovum` of the pill (arm `685` of `vcore`, which `+validate-ovum`
slams on `%full`, `%jets` and `%fast`) returns on a `%full` only when its tail
is a cell, and on a `%fast` only when its tail is a flag and a noun.  With it,
the poke crashes on every noun that is no ovum (`pokeValid`).  Proved
(`ovumMold`), in `lemmas/Compiler/OvumMold.lean`. -/
def OvumMold : Prop :=
  ∀ tl w, (slamAt vcore 685 (C (A Tag.full) tl) = some w → ∃ s f, tl = C s f) ∧
    (slamAt vcore 685 (C (A Tag.fast) tl) = some w → ∃ r p, tl = C (flag r) p)

theorem ovumMold : OvumMold := fun tl w => ⟨mold_full tl w, mold_fast tl w⟩

/-- The inner `+poke` crashes on every noun that is no ovum. -/
def PokeValid : Prop :=
  ∀ cr, CorIn cr → ∀ ovo x, pokeN cr ovo = some x → ∃ ov : Ovum, ovo = ov.toNoun

theorem pokeValid (hm : OvumMold) : PokeValid := by
  intro cr hc ovo x h
  obtain ⟨v, hv⟩ := pokeN_validates hc h
  obtain ⟨hd, tl, rfl, hj | ⟨hff, w, hw⟩ | ⟨rfl, b, m, bb, rfl, hbb⟩⟩ :=
    vovum_shape vcore vcore_cape vcore_bell ovo v hv
  · subst hj; exact ⟨Ovum.jets tl, rfl⟩
  · rcases hff with rfl | rfl
    · obtain ⟨s, f, rfl⟩ := (hm tl w).1 hw
      exact ⟨Ovum.full s f, rfl⟩
    · obtain ⟨r, p, rfl⟩ := (hm tl w).2 hw
      exact ⟨Ovum.fast r p, rfl⟩
  · refine ⟨Ovum.dire bb m, ?_⟩
    simp [Ovum.toNoun, bell_ofNoun_toNoun hbb]

/-- `+eval-mook` on a noun that is no tone leaves a core that it also leaves on
some tone.  `Reach` of `core/Statement.lean` runs `+eval-mook` on any noun,
the model only on tones.  On a noun that is not `[%2 *]` it returns the core
unchanged; on `[%2 x]` the state changes only through the `%meaf` frames it
renders, and the frames it skips or renders without the state can be
replaced by tone frames.  Owner: pill to model. -/
def MookOther : Prop :=
  ∀ cr, CorIn cr → ∀ ton x, nock (C eval_mook.battery (C ton (icore cr))) eval_mook.battery = some x →
    ∃ (t : Tone) (y z cr' : Noun), x = C y cr' ∧ nock (mookS cr t) eval_mook.battery = some (C z cr')

/-- The model of the compiler meets the contract from every state where
`InvC` holds.  Owner: the analysis and compilation tracks (`lemmas/Ska/`). -/
def Contract : Prop := Sound lib pk InvC

/-- The model of the compiler answers `%full` on every subject and every
formula that is a cell, from every state where `InvC` holds.  Owner: the
analysis track (termination). -/
def Halting : Prop := FullAnswers pk InvC

/-- The invariant holds of the compiler's core that the pill builds.  Owner:
the analysis track. -/
def InvStart : Prop := InvC cor

/-- Every poke that is not a `%jets` poke naming a jet keeps the invariant:
`%full` and `%dire` (also in `Contract`), `%fast`, and `%jets ~`.  Owner: the
analysis track. -/
def InvKept : Prop :=
  ∀ st ov p st', InvC st → ¬ HotOvum ov → pk st ov = some (p, st') → InvC st'

/-- `Lib.slam` slams as Nock does.  Owner: whoever fixes `lib`; it holds of a
`lib` whose `slam` is `slamGate nock`. -/
def LibSlam : Prop := SlamIsNock lib

/-- The formatting fields of `lib` are what the pill's `+mook` computes:
`RendLeafIs` (on `lib` alone), `+scow %p` (`HandIs`), `+smyt` with
`(soft path)` and `(soft spot)` (`RendRestIs`), `(soft tank)` (`SoftTankIs`)
and the cord of `+skip` (`SkipMsgIs`).  Owner: pill to model. -/
def LibFormat : Prop :=
  RendLeafIs lib ∧ HandIs lib mugF layer4 ∧ RendRestIs lib layer4 ∧ SoftTankIs lib layer4 ∧
    SkipMsgIs lib layer4

/-- The cord of `+eval-mook` (`EvalMookMsgIs`): `+scow %ud` and `+crip`.
Owner: pill to model.  (The list mold of layer 1, `ListMoldIs`, is proved:
`listMoldIs`.) -/
def MookFormat : Prop := EvalMookMsgIs lib

end

/-! ## The pill's core -/

theorem isCore_core (hcue : CueRoot) : Ska.IsCore core :=
  ⟨nok, trap, by rw [hcue, root_eq]; rfl, evalFuel_sound 252 core_evalFuel⟩

theorem isCore_eq (hcue : CueRoot) {core₀ : Noun} (h : Ska.IsCore core₀) : core₀ = core := by
  obtain ⟨nok', trap', hc, he⟩ := h
  rw [hcue, root_eq, Option.some.injEq] at hc
  simp only [n4, Noun.cell.injEq] at hc
  obtain ⟨-, rfl, rfl, -⟩ := hc
  exact Eval.deterministic he (evalFuel_sound 252 core_evalFuel)

theorem loads (hcue : CueRoot) : Ska.Loads := ⟨core, isCore_core hcue⟩

theorem corIn_cor : CorIn cor := by
  obtain ⟨_, _, h⟩ := core_shape
  exact h

theorem hot_of {ov : Ovum} (h : HotOvum ov) : Ska.Hot ov.toNoun := by
  cases ov with
  | jets p =>
    cases p with
    | atom n => exact h.elim
    | cell a b => exact ⟨a, b, rfl⟩
  | _ => exact h.elim

/-- `Mook` of `core/Statement.lean` on any noun leaves a core that it also
leaves on some tone. -/
theorem mook_other (hmo : MookOther) {cr : Noun} (hc : CorIn cr) {ton toon core' : Noun}
    (h : Ska.Mook (C ob (icore cr)) ton toon core') :
    ∃ (t : Tone) (z : Noun), Ska.Mook (C ob (icore cr)) t.toNoun z core' := by
  obtain ⟨e, gate, inner, he, hpg, hsl, hed⟩ := h
  rw [slot_core] at he
  subst he
  have h1 := (pull_slam (mook_pull cr)).1 ⟨gate, hpg, hsl⟩
  obtain ⟨t, y, z, cr', e1, h2⟩ := hmo cr hc ton _ h1
  simp only [Noun.cell.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨gate', hpg', hsl'⟩ := (pull_slam (mook_pull cr)).2 h2
  exact ⟨t, z, icore cr, gate', inner, (slot_core ob cr).2 rfl, hpg', hsl', hed⟩

/-! ## What the pill's core can become -/

section
variable {lib : Lib} {pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)}

theorem pokeIs_all (hpm : PokeModel pk) : ∀ cr, CorIn cr → PokeIs pk cr :=
  fun cr hc => pokeIs_of_frame hc (pokeFrame_corIn hc) (hpm cr hc)

/-- Every core that the pill's core can become is the outer battery over the
interpreter core of a compiler's core `cr` that keeps what the interpreter
reads and that the model reaches from the pill's `cor`. -/
theorem reach_model (hcue : CueRoot) (hslam : LibSlam lib) (hpm : PokeModel pk)
    (hpv : OvumMold) (hmo : MookOther) (hfmt : LibFormat lib)
    (hmf : MookFormat lib) {core₀ c : Noun} (h0 : Ska.IsCore core₀) (h : Ska.Reach core₀ c) :
    ∃ cr, c = C ob (icore cr) ∧ CorIn cr ∧ ReachI lib pk cor cr := by
  have hpk := pokeIs_all hpm
  have hbad : ∀ cr, CorIn cr → PokeDireBad cr := fun _ hc => pokeDireBad hc
  obtain ⟨hleaf, hhand, hrest, hst, hm⟩ := hfmt
  have hlist := listMoldIs
  have hmsg : EvalMookMsgIs lib := hmf
  have hrb := rendBaseIs_layer4 lib hleaf hhand hrest
  rw [isCore_eq hcue h0] at h
  induction h with
  | pill => exact ⟨cor, core_eq, corIn_cor, ReachI.start⟩
  | @poke c ovo prod core' _ hp hhot ih =>
    obtain ⟨cr, rfl, hc, hr⟩ := ih
    obtain ⟨cr', hn, rfl⟩ := (poke_iff cr ovo prod core').1 hp
    obtain ⟨ov, rfl⟩ := pokeValid hpv cr hc ovo _ hn
    have e := (hpk cr hc).1 ov hhot
    rw [hn] at e
    cases e1 : pk cr ov with
    | none => rw [e1] at e; cases e
    | some r =>
      rw [e1, Option.map_some, Option.some.injEq, Noun.cell.injEq] at e
      obtain ⟨-, rfl⟩ := e
      exact ⟨r.2, rfl, (hpk cr hc).2 ov r e1 hhot,
        ReachI.poke hr (p := r.1) e1 fun hh => hhot (hot_of hh)⟩
  | @top c s f gul ton core' _ ht ih =>
    obtain ⟨cr, rfl, hc, hr⟩ := ih
    obtain ⟨t, cr', -, rfl, he⟩ := (top_iff lib hslam pk hpk ob cr hc s f gul ton core').1 ht
    exact ⟨cr', rfl, (eval_top_of_model lib hslam pk hpk cr hc s f gul t cr' he).2,
      ReachI.top hr he⟩
  | @mook c ton toon core' _ hm' ih =>
    obtain ⟨cr, rfl, hc, hr⟩ := ih
    obtain ⟨t, z, hm2⟩ := mook_other hmo hc hm'
    obtain ⟨tn, cr', k, -, rfl, he⟩ :=
      (mook_iff lib hslam pk hpk hrb hst hm hlist hmsg hbad ob cr hc t z core').1 hm2
    exact ⟨cr', rfl, (eval_mook_le lib hslam pk hpk hrb hst hm hlist hmsg cr hc k t _ he).2,
      ReachI.mook hr he⟩

end

/-! ## The statements -/

section
variable {lib : Lib} {pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)}
  {InvC : Noun → Prop}

/-- Every hypothesis of the assembly, in one place. -/
structure Gap (lib : Lib) (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (InvC : Noun → Prop) : Prop where
  pokeModel : PokeModel pk
  mookOther : MookOther
  contract : Contract lib pk InvC
  halting : Halting pk InvC
  invStart : InvStart InvC
  invKept : InvKept pk InvC
  libSlam : LibSlam lib
  libFormat : LibFormat lib
  mookFormat : MookFormat lib

theorem Gap.reach (g : Gap lib pk InvC) {core₀ c : Noun} (h0 : Ska.IsCore core₀)
    (h : Ska.Reach core₀ c) : ∃ cr, c = C ob (icore cr) ∧ CorIn cr ∧ InvC cr := by
  obtain ⟨cr, rfl, hc, hr⟩ := reach_model cueRoot g.libSlam g.pokeModel ovumMold
    g.mookOther g.libFormat g.mookFormat h0 h
  exact ⟨cr, rfl, hc, reach_inv lib g.contract.toPokeSteps g.invKept g.invStart hr⟩

theorem meek_of (g : Gap lib pk InvC) : Ska.Meek := by
  intro core₀ c s f p gul h0 hr hA
  have hpk := pokeIs_all g.pokeModel
  obtain ⟨cr, rfl, hc, hr'⟩ := reach_model cueRoot g.libSlam g.pokeModel ovumMold
    g.mookOther g.libFormat g.mookFormat h0 hr
  obtain ⟨st', he⟩ := meek_reach lib g.contract g.halting g.invKept (gul := gul) g.invStart hr' hA
  exact ⟨_, (top_iff lib g.libSlam pk hpk ob cr hc s f gul _ _).2 ⟨_, st', rfl, rfl, he⟩⟩

theorem weak_of (g : Gap lib pk InvC) : Ska.Weak := by
  intro core₀ c s f gul toon h0 hr hm
  have hpk := pokeIs_all g.pokeModel
  obtain ⟨hleaf, hhand, hrest, hst, hmsg⟩ := g.libFormat
  have hlist := listMoldIs
  have hmm : EvalMookMsgIs lib := g.mookFormat
  have hrb := rendBaseIs_layer4 lib hleaf hhand hrest
  have e0 := isCore_eq cueRoot h0
  obtain ⟨cr, rfl, hc, hr'⟩ := reach_model cueRoot g.libSlam g.pokeModel ovumMold
    g.mookOther g.libFormat g.mookFormat h0 hr
  subst e0
  obtain ⟨t, rfl, ht⟩ := (mock_iff lib g.libSlam hleaf hhand hrest hst hmsg core core_layer4
    s f gul toon).1 hm
  obtain ⟨st'', hrun⟩ := weak_reach lib g.contract g.halting g.invKept g.invStart hr' ht
  exact ⟨_, (run_iff lib g.libSlam pk hpk hrb hst hmsg hlist hmm (fun _ hc => pokeDireBad hc) ob cr hc s f gul _ _).2
    ⟨t, st'', rfl, rfl, hrun⟩⟩

theorem converse_of (g : Gap lib pk InvC) : Ska.Converse := by
  intro core₀ c s f gul toon c' h0 hr hrun
  have hpk := pokeIs_all g.pokeModel
  obtain ⟨hleaf, hhand, hrest, hst, hmsg⟩ := g.libFormat
  have hlist := listMoldIs
  have hmm : EvalMookMsgIs lib := g.mookFormat
  have hrb := rendBaseIs_layer4 lib hleaf hhand hrest
  have e0 := isCore_eq cueRoot h0
  obtain ⟨cr, rfl, hc, hr'⟩ := reach_model cueRoot g.libSlam g.pokeModel ovumMold
    g.mookOther g.libFormat g.mookFormat h0 hr
  subst e0
  obtain ⟨tn, cr'', rfl, rfl, hR⟩ :=
    (run_iff lib g.libSlam pk hpk hrb hst hmsg hlist hmm (fun _ hc => pokeDireBad hc) ob cr hc s f gul _ _).1 hrun
  have hM := converse_reach lib g.contract g.invKept g.invStart hr' hR
  exact (mock_iff lib g.libSlam hleaf hhand hrest hst hmsg core core_layer4 s f gul _).2 ⟨tn, rfl, hM⟩

theorem halts_of (g : Gap lib pk InvC) : Ska.Halts := by
  intro core₀ c s f₁ f₂ h0 hr
  obtain ⟨cr, rfl, hc, hI⟩ := g.reach h0 hr
  obtain ⟨r, hr1⟩ := g.halting cr s f₁ f₂ hI
  have e := g.pokeModel cr hc (Ovum.full s (C f₁ f₂)) (nh_full _ _)
  rw [hr1, Option.map_some] at e
  exact ⟨r.1.toNoun, C ob (icore r.2), (poke_iff cr _ _ _).2 ⟨r.2, e, rfl⟩⟩

/-- **The assembly.**  The five statements of `core/Statement.lean`, from the
hypotheses of `Gap`. -/
theorem full_of (g : Gap lib pk InvC) : Ska.Full :=
  ⟨loads cueRoot, meek_of g, weak_of g, converse_of g, halts_of g⟩

end

end Assembly
end Formalization
