import lemmas.Compiler.EvalRend
import lemmas.KernelRfl
import core.Statement
import lemmas.Spec

/-!
# The statements of `core/Statement.lean` against the models

`Top`, `Mook`, `Run` and `Mock` of `core/Statement.lean` are relations on the
pill's own Nock, through `Eval`.  Here each holds exactly when the model of
`Ska/Interp.lean` or `Ska/Mink.lean` says so, on every core of the shape the
pill's core has: an outer battery `ob` over the interpreter core
`icore cr = [interp.battery cr]`, where the compiler's core `cr` keeps layers 2
and 4 at their axes (`CorIn`).  The pill's own core is of that shape
(`core_shape`).

The hypotheses that remain:

* `SlamIsNock lib`: the model slams the scry gate as Nock does.
* `PokeIs pk cr` for every `cr` with `CorIn cr`: the pill's inner `+poke`
  computes the model `pk` on every ovum and returns a core that keeps
  `CorIn`.  The Nock of `+poke` is not opened.
* For `Mook` and `Run`, the formatting facts of `mock_pill_iff`
  (`RendBaseIs`, from `RendLeafIs`, `HandIs`, `RendRestIs`; `SoftTankIs`,
  `SkipMsgIs`), the list mold of layer 1 (`ListMoldIs`), the cord of
  `+eval-mook` (`EvalMookMsgIs`), and, for the direction from the pill to the
  model, that the poke crashes on a `%dire` bell that `+validate-bell`
  rejects (`PokeDireBad`).
* For `Mock`, the same formatting facts.
* That the pill's core is `core` of `lemmas/Pill`, which rests on
  `cue pill = some root`; that is not proved (gap 2 of the README).

The axes of `core/Statement.lean` agree with the generated ones: `axEval` is
`3` (`core_interp`), `axInner` is `7`, `axTop` is `eval_top.axis`, `axMook`
is `eval_mook.axis`, `axHoon` is the axis of layer 4 (`core_layer4`) and
`axMock` is `mock.axis` (`axes_agree`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

theorem axes_agree :
    Ska.axTop = eval_top.axis ∧ Ska.axMook = eval_mook.axis ∧ Ska.axMock = mock.axis ∧
      Ska.axEval = 3 ∧ Ska.axInner = 7 ∧ Ska.axPoke = 23 := by
  decide

theorem core_layer4 : slot? Ska.axHoon core = some layer4 := by
  unfold Ska.axHoon; kernel_rfl

/-- The pill's core is an outer battery over the interpreter core of its
compiler's core `cor`, which keeps layers 2 and 4. -/
theorem core_shape : ∃ ob, core = C ob (icore cor) ∧ CorIn cor := by
  refine ⟨_, rfl, ?_, ?_, PokeReach.start⟩
  · unfold icore; kernel_rfl
  · unfold icore; kernel_rfl

theorem listNoun_id_inj : ∀ {a b : List Noun}, listNoun id a = listNoun id b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [listNoun] at h
  | _ :: _, [], h => by simp [listNoun] at h
  | x :: a, y :: b, h => by
    simp only [listNoun, id, Noun.cell.injEq] at h
    rw [h.1, listNoun_id_inj h.2]

theorem toon_toNoun_inj {a b : Toon} (h : a.toNoun = b.toNoun) : a = b := by
  cases a <;> cases b <;> simp only [Toon.toNoun, Noun.cell.injEq, Noun.atom.injEq] at h <;>
    first | (cases h; done) | simp_all | skip
  all_goals exact listNoun_id_inj h

/-- `Pull` and `Slam` of a gate whose arm builds `[battery [bunt context]]`. -/
theorem pull_slam {ctx battery bunt sam out : Noun} {axis : Nat}
    (hpull : nock ctx (n3 (A 9) (A axis) (slot 1)) = some (C battery (C bunt ctx))) :
    (∃ gate, Ska.Pull ctx axis gate ∧ Ska.Slam gate sam out) ↔
      nock (C battery (C sam ctx)) battery = some out := by
  constructor
  · rintro ⟨gate, hp, b, u, c, rfl, hs⟩
    rw [Ska.Pull, ← nock_eq_some_iff, hpull, Option.some.injEq] at hp
    simp only [Noun.cell.injEq] at hp
    obtain ⟨rfl, -, rfl⟩ := hp
    rw [← nock_eq_some_iff] at hs
    simpa [nock_exec] using hs
  · intro h
    refine ⟨_, (nock_eq_some_iff).1 hpull, battery, bunt, ctx, rfl, ?_⟩
    rw [← nock_eq_some_iff]
    simpa [nock_exec] using h

theorem slot_core (ob cr : Noun) {e : Noun} : Slot Ska.axEval (C ob (icore cr)) e ↔ e = icore cr := by
  rw [← slot?_iff]; simp [Ska.axEval, nock_exec, eq_comm]

theorem edit_core (ob cr inner core' : Noun) :
    Edit Ska.axInner inner (C ob (icore cr)) core' ↔ core' = C ob (icore inner) := by
  rw [← edit?_iff]; simp [Ska.axInner, nock_exec, eq_comm]

theorem mook_pull (cr : Noun) : nock (icore cr) (n3 (A 9) (A Ska.axMook) (slot 1)) =
    some (C eval_mook.battery (C (C (A 2) (A 0)) (icore cr))) := by
  have := eval_mook.arm_at cr
  simp only [eval_mook.axis] at this
  have harm : nock (icore cr) eval_mook.arm =
      some (C eval_mook.battery (C (C (A 2) (A 0)) (icore cr))) := by
    nock_open eval_mook.arm; simp only [nock_exec]
  simp [Ska.axMook, nock_exec, this, harm]

section
variable (lib : Lib) (hslam : SlamIsNock lib)
  (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (hpk : ∀ cr, CorIn cr → PokeIs pk cr)
include hslam hpk

/-- `Top` of `core/Statement.lean` on a core of the pill's shape is the
model's `EvalTop`. -/
theorem top_iff (ob cr : Noun) (hc : CorIn cr) (s f gul ton core' : Noun) :
    Ska.Top (C ob (icore cr)) s f gul ton core' ↔
      ∃ t cr', ton = t.toNoun ∧ core' = C ob (icore cr') ∧ EvalTop lib pk cr s f gul t cr' := by
  have hpull : nock (icore cr) (n3 (A 9) (A Ska.axTop) (slot 1)) =
      some (C eval_top.battery (C (C (C (A 0) (A 0)) (A 0)) (icore cr))) := by
    have := eval_top.arm_at cr
    simp only [eval_top.axis] at this
    simp [Ska.axTop, nock_exec, this, eval_top_arm]
  constructor
  · rintro ⟨e, gate, inner, he, hpg, hsl, hed⟩
    rw [slot_core] at he
    subst he
    rw [edit_core] at hed
    have h := (pull_slam hpull).1 ⟨gate, hpg, hsl⟩
    obtain ⟨t, cr', e1, he, -⟩ := eval_top_to_model lib hslam pk hpk cr hc s f gul _ h
    simp only [Noun.cell.injEq] at e1
    obtain ⟨e1a, e1b⟩ := e1
    exact ⟨t, cr', e1a, e1b ▸ hed, he⟩
  · rintro ⟨t, cr', rfl, rfl, he⟩
    have h := (eval_top_of_model lib hslam pk hpk cr hc s f gul t cr' he).1
    obtain ⟨gate, hpg, hsl⟩ := (pull_slam hpull).2 h
    exact ⟨icore cr, gate, cr', (slot_core ob cr).2 rfl, hpg, hsl, (edit_core ob cr cr' _).2 rfl⟩


variable (hrb : RendBaseIs lib layer4) (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4)
  (hlist : ListMoldIs) (hmsg : EvalMookMsgIs lib) (hbad : ∀ cr, CorIn cr → PokeDireBad cr)
include hrb hst hm hlist hmsg hbad

/-- `Mook` of `core/Statement.lean` on a core of the pill's shape, on the
encoding of a tone, is the model's `evalMook` at some level. -/
theorem mook_iff (ob cr : Noun) (hc : CorIn cr) (t : Tone) (toon core' : Noun) :
    Ska.Mook (C ob (icore cr)) t.toNoun toon core' ↔
      ∃ tn cr' m, toon = tn.toNoun ∧ core' = C ob (icore cr') ∧
        evalMook lib (SkaModel.interp lib pk m) m cr t = some (tn, cr') := by
  constructor
  · rintro ⟨e, gate, inner, he, hpg, hsl, hed⟩
    rw [slot_core] at he
    subst he
    rw [edit_core] at hed
    have h := (pull_slam (mook_pull cr)).1 ⟨gate, hpg, hsl⟩
    obtain ⟨tn, cr', m, e1, he⟩ :=
      (eval_mook_iff lib hslam pk hpk hrb hst hm hlist hmsg hbad cr hc t _).1 h
    simp only [Noun.cell.injEq] at e1
    obtain ⟨e1a, e1b⟩ := e1
    exact ⟨tn, cr', m, e1a, e1b ▸ hed, he⟩
  · rintro ⟨tn, cr', m, rfl, rfl, he⟩
    have h := (eval_mook_iff lib hslam pk hpk hrb hst hm hlist hmsg hbad cr hc t _).2
      ⟨tn, cr', m, rfl, he⟩
    obtain ⟨gate, hpg, hsl⟩ := (pull_slam (mook_pull cr)).2 h
    exact ⟨icore cr, gate, cr', (slot_core ob cr).2 rfl, hpg, hsl, (edit_core ob cr cr' _).2 rfl⟩

/-- `Run` of `core/Statement.lean` (`+eval-top`, then `+eval-mook` of its
tone) on a core of the pill's shape is the model's `RunI`. -/
theorem run_iff (ob cr : Noun) (hc : CorIn cr) (s f gul toon core'' : Noun) :
    Ska.Run (C ob (icore cr)) s f gul toon core'' ↔
      ∃ tn cr'', toon = tn.toNoun ∧ core'' = C ob (icore cr'') ∧
        RunI lib pk cr s f gul tn cr'' := by
  constructor
  · rintro ⟨ton, core', ht, hk⟩
    obtain ⟨t, cr', rfl, rfl, ⟨k1, hk1⟩⟩ := (top_iff lib hslam pk hpk ob cr hc s f gul _ _).1 ht
    have hT := (eval_top_of_model lib hslam pk hpk cr hc s f gul t cr' ⟨k1, hk1⟩)
    obtain ⟨tn, cr'', m, rfl, rfl, hm1⟩ :=
      (mook_iff lib hslam pk hpk hrb hst hm hlist hmsg hbad ob cr' hT.2 t _ _).1 hk
    -- the two runs at one level: from some level on for each
    obtain ⟨kk, hkk⟩ := iterN_complete hT.1
    obtain ⟨r, m0, hm0⟩ := (interp_ge lib hslam pk hpk kk).1 cr hc s f gul _ hkk
    obtain ⟨e0, -⟩ := top_val lib hslam pk hpk hc ⟨m0, hm0⟩ hkk
    have hx := (eval_mook_iff lib hslam pk hpk hrb hst hm hlist hmsg hbad cr' hT.2 t _).2
      ⟨tn, cr'', m, rfl, hm1⟩
    obtain ⟨v, m2, hm2⟩ := eval_mook_ge lib hslam pk hpk hrb hst hm hlist hmsg hbad cr' hT.2 t _ hx
    have hv := (eval_mook_le lib hslam pk hpk hrb hst hm hlist hmsg cr' hT.2 m2 t v
      (hm2 m2 (Nat.le_refl _))).1
    rw [hx, Option.some.injEq] at hv
    simp only [resN, Noun.cell.injEq] at e0
    obtain ⟨e0a, e0b⟩ := e0
    have hr : r = (t, cr') := Prod.ext (tone_toNoun_inj e0a).symm e0b.symm
    subst hr
    simp only [Noun.cell.injEq] at hv
    have hvv : v = (tn, cr'') := Prod.ext (toon_toNoun_inj hv.1).symm hv.2.symm
    subst hvv
    exact ⟨tn, cr'', rfl, rfl, max m0 m2, (t, cr').1, cr', hm0 _ (Nat.le_max_left _ _),
      hm2 _ (Nat.le_max_right _ _)⟩
  · rintro ⟨tn, cr'', rfl, rfl, k, t, cr', hk, hm1⟩
    have hT := (eval_top_of_model lib hslam pk hpk cr hc s f gul t cr' ⟨k, hk⟩)
    refine ⟨t.toNoun, C ob (icore cr'), (top_iff lib hslam pk hpk ob cr hc s f gul _ _).2
      ⟨t, cr', rfl, rfl, k, hk⟩, ?_⟩
    exact (mook_iff lib hslam pk hpk hrb hst hm hlist hmsg hbad ob cr' hT.2 t _ _).2
      ⟨tn, cr'', k, rfl, rfl, hm1⟩

end


/-- `Mock` of `core/Statement.lean` on a core whose layer 4 sits at `axHoon`
(the pill's core does, `core_layer4`) is the model's `Mock`. -/
theorem mock_iff (lib : Lib) (hslam : SlamIsNock lib) (hleaf : RendLeafIs lib)
    (hhand : HandIs lib mugF layer4) (hrest : RendRestIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (core : Noun)
    (h4 : slot? Ska.axHoon core = some layer4) (s f gul toon : Noun) :
    Ska.Mock core s f gul toon ↔ ∃ t, toon = t.toNoun ∧ SkaModel.Mock lib s f gul t := by
  have harm : nock layer4 mock.arm =
      some (C mock.battery (C (C (C (A 0) (A 0)) (A 0)) layer4)) := by
    nock_open mock.arm; simp [nock_exec]
  have hpull : nock layer4 (n3 (A 9) (A Ska.axMock) (slot 1)) =
      some (C mock.battery (C (C (C (A 0) (A 0)) (A 0)) layer4)) := by
    have := mock.arm_at
    simp only [mock.axis] at this
    simp [Ska.axMock, nock_exec, this, harm]
  have hiff := mock_pill_iff lib hslam hleaf hhand hrest hst hm s f gul toon
  constructor
  · rintro ⟨hoon, gate, hh, hpg, hsl⟩
    rw [← slot?_iff, h4, Option.some.injEq] at hh
    subst hh
    obtain ⟨t, ht, rfl⟩ := hiff.1 ((pull_slam hpull).1 ⟨gate, hpg, hsl⟩)
    exact ⟨t, rfl, ht⟩
  · rintro ⟨t, rfl, ht⟩
    obtain ⟨gate, hpg, hsl⟩ := (pull_slam hpull).2 (hiff.2 ⟨t, ht, rfl⟩)
    exact ⟨layer4, gate, slot?_iff.1 h4, hpg, hsl⟩

end Compiler
end Formalization
