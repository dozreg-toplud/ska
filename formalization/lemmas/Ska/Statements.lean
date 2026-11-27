import lemmas.Ska.Theorems

/-!
# The statements, for the models

The model-level versions of the two directions of `NockEquivalence` and of
`MockEquivalence` of `core/Statement.lean`, for any compiler that satisfies
the contract (`Sound`), and the same over every state the compiler reaches
(`ReachI`).

* `meek`: if Nock computes `p` (`Eval`), `+eval-top` returns `[%0 p]`.
  Needs `FullAnswers`, the model's `Halts`.
* `meek_conv`: if `+eval-top` with no scry gate returns `[%0 p]`, Nock
  computes `p`: `+mink` with no scry gate is sound (`eval_of_minkF_nil`).
* `weak`: what `+mock` returns, `+eval-top` then `+eval-mook` return.  Needs
  `FullAnswers`.
* `converse`: what `+eval-top` then `+eval-mook` return, `+mock` returns.
* `meek_cell_tag`: `meek` on a dynamic hint whose tag is a cell, which
  `+mink` and the interpreter reduce as Nock does.
-/

namespace Formalization
namespace SkaModel

open Nock

section
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

/-! ## Lists -/

theorem mapM_reverse_opt {α β : Type} (f : α → Option β) :
    ∀ (l : List α), l.reverse.mapM f = (l.mapM f).map List.reverse
  | [] => rfl
  | a :: l => by
    rw [List.reverse_cons, List.mapM_append, mapM_reverse_opt f l]
    simp only [List.mapM_cons, List.mapM_nil]
    cases f a <;> cases List.mapM f l <;> simp

theorem stopTag_ne {t : Nat} (h : stopTag t = true) : t ≠ Tag.meac ∧ t ≠ Tag.meaf := by
  simp only [stopTag, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> subst h <;> decide

theorem stopTag_lose : stopTag Tag.lose = true := by decide

/-! ## Rendering, forward -/

theorem evalRend_fwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) {k₁ : Nat} {st : σ}
    {x y : Frame} {z : Noun} (hI : InvC st) (hfr : FrameRel lib (needOf poke st) x y)
    (hz : rendF lib k₁ y = some z) :
    ∃ st₁, evalRend lib (interp lib poke (k₁ + 1)) (k₁ + 1) st x = some (z, st₁) ∧
      InvC st₁ ∧ needOf poke st ≤ needOf poke st₁ := by
  cases hfr with
  | @same tag d hst =>
    obtain ⟨h1, h2⟩ := stopTag_ne hst
    refine ⟨st, ?_, hI, Needs.le_refl _⟩
    simp only [evalRend, h1, h2, if_false]
    rw [rendF_le lib (Nat.le_succ k₁) _ _ hz]
    rfl
  | @meaf a vals h t nd hv hfit hfol hnd hsplit =>
    simp only [rendF, if_true] at hz
    cases hm : minkF lib (A 0) k₁ [] (C h t) h with
    | none => rw [hm] at hz; simp at hz
    | some r =>
      rw [hm] at hz
      have hargs : argsFor (needOf poke st) a false (C h t) = some vals := by
        simp [argsFor, hnd, hsplit]
      have hm' : minkF lib (A 0) k₁ [] (C h t) a.fol = some r := by rw [hfol]; exact hm
      obtain ⟨ton, st₁, hcall, hrel⟩ := (interp_fwd lib hS hF (k₁ + 1)).call st a false vals
        [] [] (A 0) (C h t) k₁ r hI (Nat.lt_succ_self _) hfit hargs Forall2.nil hm'
      obtain ⟨hI1, hle⟩ := (interp_steps lib hS.toPokeSteps (k₁ + 1)).call _ _ _ _ _ _ _ _ hI hcall
      refine ⟨st₁, ?_, hI1, hle⟩
      have hmc : Tag.meaf ≠ Tag.meac := by decide
      simp only [evalRend, hmc, if_false, if_true, nounList?_listNoun, Option.bind_some, hv,
        hcall]
      cases hrel <;> simp only [Option.some.injEq] at hz <;> simp [hz]
  | @meac n trap hm =>
    obtain ⟨h, t, rfl, hmk⟩ := hm
    simp only [rendF, if_true] at hz
    cases hm : minkF lib (A 0) k₁ [] (C h t) h with
    | none => rw [hm] at hz; simp at hz
    | some r =>
      rw [hm] at hz
      have := Mink.det ⟨k₁, hm⟩ hmk
      subst this
      simp only [Option.some.injEq] at hz
      subst hz
      exact ⟨st, rfl, hI, Needs.le_refl _⟩

theorem evalMookLoop_fwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) (k₁ : Nat) :
    ∀ (xs ys : List Frame) (zs out : List Noun) (st : σ), InvC st →
      Forall2 (FrameRel lib (needOf poke st)) xs ys → ys.mapM (rendF lib k₁) = some zs →
      ∃ st'', evalMookLoop lib (interp lib poke (k₁ + 1)) (k₁ + 1) st xs out =
        some (zs.reverse ++ out, st'')
  | [], [], zs, out, st, _, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨st, rfl⟩
  | x :: xs, y :: ys, zs, out, st, hI, Forall2.cons hxy hrest, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨z, hz, zs', hzs', rfl⟩ := h
    obtain ⟨st₁, hr, hI1, hle⟩ := evalRend_fwd lib hS hF hI hxy hz
    obtain ⟨st'', hl⟩ := evalMookLoop_fwd lib hS hF k₁ xs ys zs' (z :: out) st₁ hI1
      (hrest.imp fun _ _ => FrameRel.mono hle) hzs'
    refine ⟨st'', ?_⟩
    simp only [evalMookLoop, hr, Option.bind_some, hl, List.reverse_cons, List.append_assoc,
      List.singleton_append]

theorem evalMook_fwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) {k₁ : Nat} {st : σ}
    {ti tm : Tone} {toon : Toon} (hI : InvC st) (hrel : ToneRel lib (needOf poke st) ti tm)
    (h : mookF lib k₁ tm = some toon) :
    ∃ st'', evalMook lib (interp lib poke (k₁ + 1)) (k₁ + 1) st ti = some (toon, st'') := by
  cases hrel with
  | zero p => simp only [mookF, Option.some.injEq] at h; subst h; exact ⟨st, rfl⟩
  | one p => simp only [mookF, Option.some.injEq] at h; subst h; exact ⟨st, rfl⟩
  | @two ti tm hl =>
    simp only [mookF, Option.map_eq_some_iff] at h
    obtain ⟨zs, hzs, rfl⟩ := h
    have hsk := skip_forall2 lib (fun m => FrameRel.same (d := m) stopTag_lose) hl
    have hrev : ((skip lib (fun m => (Tag.lose, m)) tm).reverse).mapM (rendF lib k₁) =
        some zs.reverse := by
      rw [mapM_reverse_opt, hzs]; rfl
    obtain ⟨st'', hloop⟩ := evalMookLoop_fwd lib hS hF k₁ _ _ zs.reverse [] st hI hsk.reverse hrev
    refine ⟨st'', ?_⟩
    simp only [evalMook, hloop, List.reverse_reverse, List.append_nil, Option.map_some]

/-! ## Rendering, backward -/

theorem evalRend_bwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) {k : Nat} {st st₁ : σ} {x y : Frame} {z : Noun}
    (hI : InvC st) (hfr : FrameRel lib (needOf poke st) x y)
    (hev : evalRend lib (interp lib poke k) k st x = some (z, st₁)) :
    (∃ k', rendF lib k' y = some z) ∧ InvC st₁ ∧ needOf poke st ≤ needOf poke st₁ := by
  cases hfr with
  | @same tag d hst =>
    obtain ⟨h1, h2⟩ := stopTag_ne hst
    simp only [evalRend, h1, h2, if_false, Option.map_eq_some_iff, Prod.mk.injEq] at hev
    obtain ⟨tank, hr, rfl, rfl⟩ := hev
    exact ⟨⟨k, hr⟩, hI, Needs.le_refl _⟩
  | @meaf a vals h t nd hv hfit hfol hnd hsplit =>
    have hmc : Tag.meaf ≠ Tag.meac := by decide
    simp only [evalRend, hmc, if_false, if_true, nounList?_listNoun, Option.bind_some, hv,
      Option.bind_eq_some_iff] at hev
    obtain ⟨⟨ton, st'⟩, hcall, hev⟩ := hev
    obtain ⟨hI1, hle⟩ := (interp_steps lib hS.toPokeSteps k).call _ _ _ _ _ _ _ _ hI hcall
    have hargs : argsFor (needOf poke st) a false (C h t) = some vals := by
      simp [argsFor, hnd, hsplit]
    obtain ⟨r, ⟨k', hk'⟩, hrel⟩ := (interp_bwd lib hS k).call st a false vals [] (A 0) ton st'
      hI hcall (C h t) [] hfit hargs Forall2.nil
    rw [hfol] at hk'
    refine ⟨⟨k', ?_⟩, ?_⟩
    · simp only [rendF, if_true, hk']
      cases hrel with
      | zero p => simp only [Option.some.injEq, Prod.mk.injEq] at hev; simp [← hev.1]
      | one p => simp only [Option.some.injEq, Prod.mk.injEq] at hev; simp [← hev.1]
      | two _ => simp only [Option.some.injEq, Prod.mk.injEq] at hev; simp [← hev.1]
    · cases hrel <;> simp only [Option.some.injEq, Prod.mk.injEq] at hev <;> rw [← hev.2] <;>
        exact ⟨hI1, hle⟩
  | @meac n trap hm =>
    obtain ⟨h, t, rfl, k', hk'⟩ := hm
    simp only [evalRend, if_true, Option.some.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨⟨k', by simp only [rendF, if_true, hk']⟩, hI, Needs.le_refl _⟩

theorem evalMookLoop_bwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (k : Nat) :
    ∀ (xs ys : List Frame) (out res : List Noun) (st st'' : σ), InvC st →
      Forall2 (FrameRel lib (needOf poke st)) xs ys →
      evalMookLoop lib (interp lib poke k) k st xs out = some (res, st'') →
      ∃ k' zs, ys.mapM (rendF lib k') = some zs ∧ res = zs.reverse ++ out
  | [], [], out, res, st, st'', _, _, h => by
    simp only [evalMookLoop, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, [], rfl, by simp [h.1]⟩
  | x :: xs, y :: ys, out, res, st, st'', hI, Forall2.cons hxy hrest, h => by
    simp only [evalMookLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨z, st₁⟩, hr, h⟩ := h
    obtain ⟨⟨k₁, hk₁⟩, hI1, hle⟩ := evalRend_bwd lib hS hI hxy hr
    obtain ⟨k₂, zs', hzs', rfl⟩ := evalMookLoop_bwd lib hS k xs ys (z :: out) res st₁ st'' hI1
      (hrest.imp fun _ _ => FrameRel.mono hle) h
    refine ⟨max k₁ k₂, z :: zs', ?_, by simp⟩
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    exact ⟨z, rendF_le lib (Nat.le_max_left _ _) _ _ hk₁, zs',
      mapM_le (rendF_le lib (Nat.le_max_right _ _)) _ _ hzs', rfl⟩

theorem evalMook_bwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) {k : Nat} {st st'' : σ} {ti tm : Tone} {toon : Toon}
    (hI : InvC st) (hrel : ToneRel lib (needOf poke st) ti tm)
    (h : evalMook lib (interp lib poke k) k st ti = some (toon, st'')) :
    ∃ k', mookF lib k' tm = some toon := by
  cases hrel with
  | zero p =>
    simp only [evalMook, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, by rw [← h.1]; rfl⟩
  | one p =>
    simp only [evalMook, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, by rw [← h.1]; rfl⟩
  | @two ti tm hl =>
    simp only [evalMook, Option.map_eq_some_iff] at h
    obtain ⟨⟨out, st'⟩, hloop, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hsk := skip_forall2 lib (fun m => FrameRel.same (d := m) stopTag_lose) hl
    obtain ⟨k', zs, hzs, rfl⟩ := evalMookLoop_bwd lib hS k _ _ [] out st st' hI hsk.reverse hloop
    refine ⟨k', ?_⟩
    rw [mapM_reverse_opt] at hzs
    simp only [Option.map_eq_some_iff] at hzs
    obtain ⟨zs0, hzs0, rfl⟩ := hzs
    simp only [mookF, hzs0, Option.map_some, List.append_nil, List.reverse_reverse]

/-! ## The statements -/

/-- **`NockEquivalence`, for the models.**  If Nock computes `p` from `s`
and `f`, the interpreter returns `[%0 p]`, from any state where the
compiler's invariant holds and whatever the scry gate. -/
theorem meek (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) {st : σ} {s f p gul : Noun}
    (hI : InvC st) (h : Eval s f p) :
    ∃ st', EvalTop lib poke st s f gul (Tone.zero p) st' := by
  obtain ⟨n, hn⟩ := mink_of_evalH lib gul (Eval.toEvalH h)
  obtain ⟨ton, st', hrun, hrel⟩ :=
    (interp_fwd lib hS hF (n + 1)).nok st s f gul n _ hI (Nat.lt_succ_self _) (hn [])
  rw [hrel.zero_right] at hrun
  exact ⟨st', n + 1, hrun⟩

/-- **The converse of `meek`, with no scry gate.**  If the interpreter returns
`[%0 p]` on `s` and `f` with the scry gate `~`, from a state where the
compiler's invariant holds, Nock computes `p`: the run of `+mink` that the
interpreter stands for returns `[%0 p]` too (`interp_bwd`), and `+mink` with
no scry gate is sound (`eval_of_minkF_nil`). -/
theorem meek_conv (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) {st st' : σ} {s f p : Noun}
    (hI : InvC st) (h : EvalTop lib poke st s f (A 0) (Tone.zero p) st') : Eval s f p := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨tm, ⟨n, hn⟩, hrel⟩ := (interp_bwd lib hS k).nok st s f (A 0) _ st' hI hk
  cases hrel
  exact eval_of_minkF_nil lib n [] s f p hn

/-- **`MockEquivalence`, for the models.**  What `+mock` returns, the interpreter returns,
rendered by `+eval-mook`. -/
theorem weak (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) {st : σ} {s f gul : Noun}
    {toon : Toon} (hI : InvC st) (h : Mock lib s f gul toon) :
    ∃ st'', RunI lib poke st s f gul toon st'' := by
  obtain ⟨k₁, h⟩ := h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨tm, hmink, hmook⟩ := h
  obtain ⟨ti, st', hrun, hrel⟩ :=
    (interp_fwd lib hS hF (k₁ + 1)).nok st s f gul k₁ tm hI (Nat.lt_succ_self _) hmink
  obtain ⟨hI', -⟩ := (interp_steps lib hS.toPokeSteps (k₁ + 1)).nok _ _ _ _ _ _ hI hrun
  obtain ⟨st'', hm⟩ := evalMook_fwd lib hS hF hI' hrel hmook
  exact ⟨st'', k₁ + 1, ti, st', hrun, hm⟩

/-- **The other direction of `MockEquivalence`, for the models.**  What the interpreter returns, rendered,
`+mock` returns. -/
theorem converse (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) {st st'' : σ} {s f gul : Noun} {toon : Toon}
    (hI : InvC st) (h : RunI lib poke st s f gul toon st'') : Mock lib s f gul toon := by
  obtain ⟨k, ti, st', hrun, hm⟩ := h
  obtain ⟨tm, ⟨k₁, hk₁⟩, hrel⟩ := (interp_bwd lib hS k).nok st s f gul ti st' hI hrun
  obtain ⟨hI', -⟩ := (interp_steps lib hS.toPokeSteps k).nok _ _ _ _ _ _ hI hrun
  obtain ⟨k₂, hk₂⟩ := evalMook_bwd lib hS hI' hrel hm
  refine ⟨max k₁ k₂, ?_⟩
  rw [minkF_le lib gul (Nat.le_max_left _ _) _ _ _ _ hk₁, Option.bind_some]
  exact mookF_le lib (Nat.le_max_right _ _) _ _ hk₂

/-- A dynamic hint whose tag is a cell: Nock reduces
`[11 [[1 0] 1 0] 1 42]` to `42`, and so does the interpreter, from any state
where the compiler's invariant holds, as `+mink` does. -/
theorem meek_cell_tag (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) {st : σ} (s gul : Noun)
    (hI : InvC st) :
    let f := n3 (A 11) (C (C (A 1) (A 0)) (C (A 1) (A 0))) (C (A 1) (A 42))
    Eval s f (A 42) ∧ ∃ st', EvalTop lib poke st s f gul (Tone.zero (A 42)) st' := by
  intro f
  have heval := (eval_cell_tag lib gul s [] 0).1
  exact ⟨heval, meek lib hS hF hI heval⟩

/-! ## Over the states the compiler reaches -/

/-- A `%jets` poke that names a jet. -/
def HotOvum : Ovum → Prop
  | Ovum.jets (Noun.cell _ _) => True
  | _ => False

/-- The states that the state `st₀` can become: by pokes other than a `%jets`
poke that names a jet, and by runs of `+eval-top` and `+eval-mook`. -/
inductive ReachI (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) (st₀ : σ) : σ → Prop where
  | start : ReachI lib poke st₀ st₀
  | poke {st : σ} {ov : Ovum} {p : Prod Map} {st' : σ} :
      ReachI lib poke st₀ st → poke st ov = some (p, st') → ¬ HotOvum ov → ReachI lib poke st₀ st'
  | top {st : σ} {s f gul : Noun} {ton : Tone} {st' : σ} :
      ReachI lib poke st₀ st → EvalTop lib poke st s f gul ton st' → ReachI lib poke st₀ st'
  | mook {st : σ} {k : Nat} {ton : Tone} {toon : Toon} {st' : σ} :
      ReachI lib poke st₀ st → evalMook lib (interp lib poke k) k st ton = some (toon, st') →
      ReachI lib poke st₀ st'

theorem evalMookLoop_inv (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hP : PokeSteps poke InvC) (k : Nat) :
    ∀ (xs : List Frame) (out res : List Noun) (st st' : σ), InvC st →
      evalMookLoop lib (interp lib poke k) k st xs out = some (res, st') → InvC st'
  | [], out, res, st, st', hI, h => by
    simp only [evalMookLoop, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hI
  | x :: xs, out, res, st, st', hI, h => by
    simp only [evalMookLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨z, st₁⟩, hr, h⟩ := h
    refine evalMookLoop_inv lib hP k xs _ res st₁ st' ?_ h
    unfold evalRend at hr
    split at hr
    · simp only [Option.some.injEq, Prod.mk.injEq] at hr; rw [← hr.2]; exact hI
    · split at hr
      · split at hr
        · simp at hr
        · simp only [Option.bind_eq_some_iff] at hr
          obtain ⟨vs, -, a, -, ⟨ton, st₂⟩, hcall, hr⟩ := hr
          have := ((interp_steps lib hP k).call _ _ _ _ _ _ _ _ hI hcall).1
          cases ton <;> simp only [Option.some.injEq, Prod.mk.injEq] at hr <;> rw [← hr.2] <;>
            exact this
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hr
        obtain ⟨_, _, _, rfl⟩ := hr
        exact hI

/-- The compiler's invariant holds on every state that a state where it holds
can become. -/
theorem reach_inv (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hP : PokeSteps poke InvC)
    (hother : ∀ st ov p st', InvC st → ¬ HotOvum ov → poke st ov = some (p, st') → InvC st')
    {st₀ st : σ} (h₀ : InvC st₀) (h : ReachI lib poke st₀ st) : InvC st := by
  induction h with
  | start => exact h₀
  | poke _ hp hhot ih => exact hother _ _ _ _ ih hhot hp
  | top _ htop ih =>
    obtain ⟨k, hk⟩ := htop
    exact ((interp_steps lib hP k).nok _ _ _ _ _ _ ih hk).1
  | @mook st k ton toon st' _ hm ih =>
    cases ton with
    | zero p => simp only [evalMook, Option.some.injEq, Prod.mk.injEq] at hm; rw [← hm.2]; exact ih
    | one p => simp only [evalMook, Option.some.injEq, Prod.mk.injEq] at hm; rw [← hm.2]; exact ih
    | two tr =>
      simp only [evalMook, Option.map_eq_some_iff] at hm
      obtain ⟨⟨out, st''⟩, hloop, hm⟩ := hm
      simp only [Prod.mk.injEq] at hm
      rw [← hm.2]
      exact evalMookLoop_inv lib hP k _ _ _ _ _ ih hloop

/-- `meek` over every state the compiler reaches from `st₀`. -/
theorem meek_reach (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC)
    (hother : ∀ st ov p st', InvC st → ¬ HotOvum ov → poke st ov = some (p, st') → InvC st')
    {st₀ st : σ} {s f p gul : Noun} (h₀ : InvC st₀) (hr : ReachI lib poke st₀ st)
    (h : Eval s f p) : ∃ st', EvalTop lib poke st s f gul (Tone.zero p) st' :=
  meek lib hS hF (reach_inv lib hS.toPokeSteps hother h₀ hr) h

/-- `meek_conv` over every state the compiler reaches from `st₀`. -/
theorem meek_conv_reach (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC)
    (hother : ∀ st ov p st', InvC st → ¬ HotOvum ov → poke st ov = some (p, st') → InvC st')
    {st₀ st st' : σ} {s f p : Noun} (h₀ : InvC st₀) (hr : ReachI lib poke st₀ st)
    (h : EvalTop lib poke st s f (A 0) (Tone.zero p) st') : Eval s f p :=
  meek_conv lib hS (reach_inv lib hS.toPokeSteps hother h₀ hr) h

/-- `weak` over every state the compiler reaches from `st₀`. -/
theorem weak_reach (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC)
    (hother : ∀ st ov p st', InvC st → ¬ HotOvum ov → poke st ov = some (p, st') → InvC st')
    {st₀ st : σ} {s f gul : Noun} {toon : Toon} (h₀ : InvC st₀) (hr : ReachI lib poke st₀ st)
    (h : Mock lib s f gul toon) : ∃ st'', RunI lib poke st s f gul toon st'' :=
  weak lib hS hF (reach_inv lib hS.toPokeSteps hother h₀ hr) h

/-- `converse` over every state the compiler reaches from `st₀`. -/
theorem converse_reach (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC)
    (hother : ∀ st ov p st', InvC st → ¬ HotOvum ov → poke st ov = some (p, st') → InvC st')
    {st₀ st st'' : σ} {s f gul : Noun} {toon : Toon} (h₀ : InvC st₀) (hr : ReachI lib poke st₀ st)
    (h : RunI lib poke st s f gul toon st'') : Mock lib s f gul toon :=
  converse lib hS (reach_inv lib hS.toPokeSteps hother h₀ hr) h

end

end SkaModel
end Formalization
