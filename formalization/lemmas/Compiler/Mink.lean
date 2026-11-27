import lemmas.Iter
import lemmas.Hoon.Mink
import lemmas.Ska.Mink

/-!
`+mink` of the pill's `hoon.hoon` against the model `minkF` of
`lemmas/Ska/Mink.lean`.

The loop `$` of `+mink` runs on the `|^` core `minkCore (trN t) [[s f] gul] ctx`.
The proof goes in three steps.

1. `mink_loop_unfold`: one level of the loop, run by `nockW call`, is
   `NStep`, a Lean function that mirrors `minkStep` on nouns.  It takes the
   loop's calls to itself as `G` and the other calls (`frag`, `edit`, the scry
   gate, the `.*` of the hints) through `call`.  This is the only symbolic
   execution of the loop.
2. `NStep` is monotone in `G` and `call` (`nstep_mono`), and with `call = nock`
   and `G` the encoding of a model `go`, it is `minkStep go` encoded
   (`nstep_exact`).
3. Induction on the fuel of `minkF` gives what the model returns, the Nock
   returns; induction on the depth of calls (`iterN`) gives the converse.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- A trace as a noun. -/
abbrev trN (t : Trace) : Noun := listNoun Frame.toNoun t

/-- `[%2 trace]`. -/
abbrev twoN (t : Trace) : Noun := C (A 2) (trN t)

/-- `?.  ?=(%0 -.x)  x` on nouns: go on with the product of a `%0`, return any
other cell, crash on an atom. -/
def nb (x : Option Noun) (k : Noun → Option Noun) : Option Noun :=
  match x with
  | some (Noun.cell h p) => if A 0 = h then k p else some (C h p)
  | _ => none

/-- What `simp` makes of the Nock of `?.  ?=(%0 -.x)  x` followed by `F x`:
`nb`. -/
theorem nb_exec (x : Option Noun) (F : Noun → Option Noun) :
    (x.bind fun h => (slot? 2 h).bind fun r => if A 0 = r then F h else some h)
      = nb x (fun p => F (C (A 0) p)) := by
  rcases x with _ | (_ | ⟨h, p⟩)
  · rfl
  · simp [nb, slot_two, child]
  · by_cases e : A 0 = h
    · subst e; simp [nb, nock_exec]
    · simp [nb, e, nock_exec]

theorem bind_bind_some {α β γ : Type} (x : Option α) (f : α → β) (g : β → Option γ) :
    ((x.bind fun r => some (f r)).bind g) = x.bind fun r => g (f r) := by
  cases x <;> rfl

/-- A test of a noun against `0`, and the branch it picks. -/
theorem eq0_bind (o : Option Noun) (X Y : Noun) (K : Noun → Option Noun) :
    ((o.bind fun y => some (eqCode (A 0) y)).bind fun t => (pick t X Y).bind K)
      = o.bind fun y => if A 0 = y then K X else K Y := by
  rcases o with _ | y
  · rfl
  · by_cases e : A 0 = y
    · subst e; simp [eqCode]
    · simp [pick_eqCode, e]

/-- Slamming the gate that the arm `arm` of the core `S` builds, through `call`. -/
def slamArm (call : Noun → Noun → Option Noun) (S arm smp : Noun) : Option Noun :=
  (call S arm).bind fun g => (edit? 6 smp g).bind fun g' => (slot? 2 g').bind fun a => call g' a

/-- Slamming the gate `g` on `smp` through `call`. -/
def slamGate (call : Noun → Noun → Option Noun) (g smp : Noun) : Option Noun :=
  (edit? 6 smp g).bind fun g' => (slot? 2 g').bind fun a => call g' a

/-- The trace of a dynamic hint: the frame is pushed for the tags of `stopTag`. -/
def hintTrace (tag : Nat) (c : Noun) (t : Trace) : Trace :=
  if stopTag tag then (tag, c) :: t else t

/-- One level of the loop of `+mink` on nouns.  `G t s f` is the loop on the
trace `t`, the subject `s` and the formula `f`; `call` runs the other gates.
The cases are those of `minkStep`, in its order. -/
def NStep (ctx gul : Noun) (G : Trace → Noun → Noun → Option Noun)
    (call : Noun → Noun → Option Noun) (t : Trace) (s f : Noun) : Option Noun :=
  match f with
  | Noun.cell (Noun.cell a b) c =>
      nb (G t s (C a b)) fun ph => nb (G t s c) fun pt => some (C (A 0) (C ph pt))
  | Noun.cell (Noun.atom 0) (Noun.atom ax) =>
      (slamArm call (minkCore (trN t) (C (C s f) gul) ctx) mink.frag.arm (C (A ax) s)).bind
        fun part => if A 0 = part then some (twoN t) else
          (slot? 3 part).bind fun r => some (C (A 0) r)
  | Noun.cell (Noun.atom 1) k => some (C (A 0) k)
  | Noun.cell (Noun.atom 2) (Noun.cell b c) =>
      nb (G t s b) fun s' => nb (G t s c) fun f' => G t s' f'
  | Noun.cell (Noun.atom 3) b => nb (G t s b) fun p => some (C (A 0) (wut p))
  | Noun.cell (Noun.atom 4) b =>
      nb (G t s b) fun p => match p with
        | Noun.cell _ _ => some (twoN t)
        | Noun.atom a => some (C (A 0) (A (a + 1)))
  | Noun.cell (Noun.atom 5) (Noun.cell b c) =>
      nb (G t s b) fun x => nb (G t s c) fun y => some (C (A 0) (eqCode x y))
  | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) =>
      nb (G t s b) fun r => match r with
        | Noun.atom 0 => G t s c
        | Noun.atom 1 => G t s d
        | _ => some (twoN t)
  | Noun.cell (Noun.atom 7) (Noun.cell b c) => nb (G t s b) fun s' => G t s' c
  | Noun.cell (Noun.atom 8) (Noun.cell b c) => nb (G t s b) fun h => G t (C h s) c
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom ax) c) =>
      nb (G t s c) fun core =>
        (slamArm call (minkCore (trN t) (C (C s f) gul) ctx) mink.frag.arm (C (A ax) core)).bind
          fun arm => if A 0 = arm then some (twoN t) else (slot? 3 arm).bind fun a => G t core a
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom ax) v) tgt) =>
      if 0 = ax then some (twoN t) else
      nb (G t s tgt) fun tg => nb (G t s v) fun x =>
        (slamArm call (minkCore (trN t) (C (C s f) gul) ctx) mink.edit.arm
            (C (A ax) (C tg x))).bind
          fun m => if A 0 = m then some (twoN t) else (slot? 3 m).bind fun r => some (C (A 0) r)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag) nx) =>
      nb (G t s nx) fun p =>
        (call s (C (A 11) (C (A tag) (C (A 1) p)))).bind fun r => some (C (A 0) r)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) clue) nx) =>
      nb (G t s clue) fun c => nb (G (hintTrace tag c t) s nx) fun p =>
        (call s (C (A 11) (C (C (A tag) (C (A 1) c)) (C (A 1) p)))).bind fun r => some (C (A 0) r)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.cell x y) clue) nx) =>
      nb (G t s clue) fun c => nb (G t s nx) fun p =>
        (call s (C (A 11) (C (C (C x y) (C (A 1) c)) (C (A 1) p)))).bind fun r => some (C (A 0) r)
  | Noun.cell (Noun.atom 12) (Noun.cell ref path) =>
      nb (G t s ref) fun r => nb (G t s path) fun p =>
        if A 0 = gul then some (twoN t) else
        (slamGate call gul (C r p)).bind fun res =>
          if A 0 = res then some (C (A 1) p) else
          (slot? 3 res).bind fun ur =>
            if A 0 = ur then some (C (A 2) (C (C (A Tag.hunk) (C r p)) (trN t))) else
            (slot? 7 res).bind fun v => some (C (A 0) v)
  | _ => some (twoN t)

set_option linter.unusedSimpArgs false in
theorem mink_loop_unfold (ctx gul : Noun) (call : Noun → Noun → Option Noun) (t : Trace)
    (s f : Noun) :
    nockW call (minkCore (trN t) (C (C s f) gul) ctx) mink.loop
      = NStep ctx gul (fun t s f => call (minkCore (trN t) (C (C s f) gul) ctx) mink.loop) call
          t s f := by
  rcases f with k | ⟨k | ⟨a, b⟩, d⟩
  · conv => lhs; arg 3; unfold mink.loop
    simp [nock_exec, NStep]
  · match k, d with
    | 0, Noun.atom ax =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 0, Noun.cell _ _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 1, d =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 2, Noun.cell b c =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 2, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 3, b =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 4, b =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
      congr 1; funext p
      cases p <;> simp [nock_exec]
    | 5, Noun.cell b c =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 5, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 6, Noun.cell b (Noun.cell c e) =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
      congr 1; funext p
      rcases p with ((_ | _ | n) | ⟨_, _⟩) <;> simp
    | 6, Noun.cell _ (Noun.atom _) =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 6, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 7, Noun.cell b c =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 7, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 8, Noun.cell b c =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 8, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 9, Noun.cell (Noun.atom ax) c =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 9, Noun.cell (Noun.cell _ _) _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 9, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 10, Noun.cell (Noun.cell (Noun.atom ax) v) tgt =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]

    | 10, Noun.cell (Noun.cell (Noun.cell _ _) _) _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 10, Noun.cell (Noun.atom _) _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 10, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 11, Noun.cell (Noun.atom tag) nx =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 11, Noun.cell (Noun.cell (Noun.atom tag) clue) nx =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
      congr 1; funext c
      by_cases h1 : tag = Tag.hunk
      · subst h1; simp [stopTag, Tag.hunk, nock_exec, listNoun, Frame.toNoun]
      by_cases h2 : tag = Tag.hand
      · subst h2; simp [stopTag, Tag.hunk, Tag.hand, nock_exec, listNoun, Frame.toNoun]
      by_cases h3 : tag = Tag.mean
      · subst h3; simp [stopTag, Tag.hunk, Tag.hand, Tag.mean, nock_exec, listNoun, Frame.toNoun]
      by_cases h4 : tag = Tag.lose
      · subst h4; simp [stopTag, Tag.hunk, Tag.hand, Tag.mean, Tag.lose, nock_exec, listNoun, Frame.toNoun]
      by_cases h5 : tag = Tag.spot
      · subst h5; simp [stopTag, Tag.hunk, Tag.hand, Tag.mean, Tag.lose, Tag.spot, nock_exec, eqCode, listNoun, Frame.toNoun]
      simp only [Tag.hunk, Tag.hand, Tag.mean, Tag.lose, Tag.spot] at h1 h2 h3 h4 h5
      have e1 : ¬ (1802401128 = tag) := fun h => h1 h.symm
      have e2 : ¬ (1684955496 = tag) := fun h => h2 h.symm
      have e3 : ¬ (1851876717 = tag) := fun h => h3 h.symm
      have e4 : ¬ (1702063980 = tag) := fun h => h4 h.symm
      have e5 : ¬ (1953460339 = tag) := fun h => h5 h.symm
      simp [stopTag, Tag.hunk, Tag.hand, Tag.mean, Tag.lose, Tag.spot, nock_exec, eqCode, e1, e2, e3,
        e4, e5, h1, h2, h3, h4, h5]
    | 11, Noun.cell (Noun.cell (Noun.cell x y) clue) nx =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 11, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 12, Noun.cell r pa =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | 12, Noun.atom _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
    | n + 13, _ =>
      conv => lhs; arg 3; unfold mink.loop
      simp [nock_exec, nockW_ite, NStep, nb_exec, slamArm, slamGate, hintTrace, bind_bind_some,
        eq0_bind, Tag.hunk]
  · conv => lhs; arg 3; unfold mink.loop
    simp [nock_exec, NStep, nb_exec, eq0_bind]

/-! ## `NStep` is monotone -/

theorem nb_mono {x x' : Option Noun} {k k' : Noun → Option Noun} (hx : Below? x x')
    (hk : ∀ p, Below? (k p) (k' p)) : Below? (nb x k) (nb x' k') := by
  intro r h
  match x, h with
  | some (Noun.cell hd p), h =>
    rw [hx _ rfl]
    simp only [nb] at h ⊢
    split at h
    · rw [if_pos (by assumption)]; exact hk p r h
    · rw [if_neg (by assumption)]; exact h

theorem slamArm_mono {c1 c2 : Noun → Noun → Option Noun} (hc : ∀ s f, Below? (c1 s f) (c2 s f))
    (S arm smp : Noun) : Below? (slamArm c1 S arm smp) (slamArm c2 S arm smp) :=
  Below?.bind (hc _ _) fun _ => Below?.bind (Below?.refl _) fun _ =>
    Below?.bind (Below?.refl _) fun _ => hc _ _

theorem slamGate_mono {c1 c2 : Noun → Noun → Option Noun} (hc : ∀ s f, Below? (c1 s f) (c2 s f))
    (g smp : Noun) : Below? (slamGate c1 g smp) (slamGate c2 g smp) :=
  Below?.bind (Below?.refl _) fun _ => Below?.bind (Below?.refl _) fun _ => hc _ _

theorem ite_mono {c : Prop} [Decidable c] {x x' y y' : Option Noun} (hx : Below? x x')
    (hy : Below? y y') : Below? (if c then x else y) (if c then x' else y') := by
  split
  · exact hx
  · exact hy

theorem nstep_mono (ctx gul : Noun) {G1 G2 : Trace → Noun → Noun → Option Noun}
    {c1 c2 : Noun → Noun → Option Noun} (hG : ∀ t s f, Below? (G1 t s f) (G2 t s f))
    (hc : ∀ s f, Below? (c1 s f) (c2 s f)) (t : Trace) (s f : Noun) :
    Below? (NStep ctx gul G1 c1 t s f) (NStep ctx gul G2 c2 t s f) := by
  have R := fun {x : Option Noun} => Below?.refl x
  unfold NStep
  split
  · exact nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ => R
  · exact Below?.bind (slamArm_mono hc _ _ _) fun _ => ite_mono R R
  · exact R
  · exact nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ => hG _ _ _
  · exact nb_mono (hG _ _ _) fun _ => R
  · exact nb_mono (hG _ _ _) fun _ => R
  · exact nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ => R
  · refine nb_mono (hG _ _ _) fun r => ?_
    split
    · exact hG _ _ _
    · exact hG _ _ _
    · exact R
  · exact nb_mono (hG _ _ _) fun _ => hG _ _ _
  · exact nb_mono (hG _ _ _) fun _ => hG _ _ _
  · exact nb_mono (hG _ _ _) fun _ => Below?.bind (slamArm_mono hc _ _ _) fun _ =>
      ite_mono R (Below?.bind R fun _ => hG _ _ _)
  · exact ite_mono R (nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ =>
      Below?.bind (slamArm_mono hc _ _ _) fun _ => R)
  · exact nb_mono (hG _ _ _) fun _ => Below?.bind (hc _ _) fun _ => R
  · exact nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ => Below?.bind (hc _ _) fun _ => R
  · exact nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ => Below?.bind (hc _ _) fun _ => R
  · exact nb_mono (hG _ _ _) fun _ => nb_mono (hG _ _ _) fun _ =>
      ite_mono R (Below?.bind (slamGate_mono hc _ _) fun _ => R)
  · exact R

/-! ## `NStep` with `nock` is `minkStep` -/

theorem tbind_map (x : Option Tone) (k : Noun → Option Tone) :
    (tbind x k).map Tone.toNoun = nb (x.map Tone.toNoun) (fun p => (k p).map Tone.toNoun) := by
  rcases x with _ | (p | p | tr) <;> simp [tbind, nb, Tone.toNoun]

theorem slamArm_frag (tr smp ctx : Noun) (hc : MinkIn ctx) (ax : Nat) (n : Noun) :
    slamArm nock (minkCore tr smp ctx) mink.frag.arm (C (A ax) n) = some (unitN (slot? ax n)) := by
  simp [slamArm, nock_exec, mink_frag_gate tr smp ctx hc]

theorem slamArm_edit (tr smp ctx : Noun) (hc : MinkIn ctx) (ax : Nat) (hax : 1 ≤ ax) (tg v : Noun) :
    slamArm nock (minkCore tr smp ctx) mink.edit.arm (C (A ax) (C tg v))
      = some (unitN (edit? ax v tg)) := by
  simp [slamArm, nock_exec, mink_edit_gate tr smp ctx hc ax hax]

set_option linter.unusedSimpArgs false in
/-- With `call = nock` and the loop's calls to itself answered by a model
`go`, one level of the loop is `minkStep go`. -/
theorem nstep_exact (lib : Lib) (ctx gul : Noun) (hc : MinkIn ctx)
    (hslam : ∀ g x, lib.slam g x = slamGate nock g x)
    (go : Trace → Noun → Noun → Option Tone) (t : Trace) (s f : Noun) :
    NStep ctx gul (fun t s f => (go t s f).map Tone.toNoun) nock t s f
      = (minkStep lib gul go t s f).map Tone.toNoun := by
  rcases f with k | ⟨k | ⟨a, b⟩, d⟩
  · simp [NStep, minkStep, Tone.toNoun]
  · match k, d with
    | 0, Noun.atom ax =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
      cases slot? ax s <;> simp [unitN, nock_exec, Tone.toNoun]
    | 0, Noun.cell _ _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 1, d =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 2, Noun.cell b c =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 2, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 3, b =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 4, b =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
      congr 1; funext p; cases p <;> simp [Tone.toNoun]
    | 5, Noun.cell b c =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 5, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 6, Noun.cell b (Noun.cell c e) =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
      congr 1; funext r; rcases r with ((_ | _ | n) | ⟨_, _⟩) <;> simp [Tone.toNoun]
    | 6, Noun.cell _ (Noun.atom _) =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 6, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 7, Noun.cell b c =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 7, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 8, Noun.cell b c =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 8, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 9, Noun.cell (Noun.atom ax) c =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
      congr 1; funext core; cases slot? ax core <;> simp [unitN, nock_exec, Tone.toNoun]
    | 9, Noun.cell (Noun.cell _ _) _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 9, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 10, Noun.cell (Noun.cell (Noun.atom ax) v) tgt =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
      by_cases h0 : ax = 0
      · subst h0; simp [Tone.toNoun]
      have h0' : ¬ (0 = ax) := fun h => h0 h.symm
      simp only [h0, h0', if_false, slamArm_edit _ _ _ hc ax (by omega), tbind_map, Option.map_if]
      congr 1; funext tg; congr 1; funext x
      cases edit? ax x tg <;> simp [unitN, nock_exec, Tone.toNoun]
    | 10, Noun.cell (Noun.cell (Noun.cell _ _) _) _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 10, Noun.cell (Noun.atom _) _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 10, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 11, Noun.cell (Noun.atom tag) nx =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 11, Noun.cell (Noun.cell (Noun.atom tag) clue) nx =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam, hintTrace]
    | 11, Noun.cell (Noun.cell (Noun.cell _ _) _) _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 11, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | 12, Noun.cell r pa =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, ]
      congr 1; funext r; congr 1; funext p
      by_cases hg : gul = A 0
      · subst hg; simp [Tone.toNoun]
      have hg' : ¬ (A 0 = gul) := fun h => hg h.symm
      simp only [hg, hg', if_false, hslam]
      cases slamGate nock gul (C r p) with
      | none => rfl
      | some res =>
        rcases res with (_ | n) | ⟨x, (_ | m) | ⟨y, v⟩⟩ <;>
          simp [scryDecode, Tone.toNoun, nock_exec, listNoun, Frame.toNoun]
    | 12, Noun.atom _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
    | n + 13, _ =>
      simp [NStep, minkStep, tbind_map, Tone.toNoun, slamArm_frag _ _ _ hc, nock_exec, hslam]
  · simp [NStep, minkStep, tbind_map, Tone.toNoun]

/-! ## The loop of `+mink` computes `minkF` -/

/-- What the model asks of slamming the scry gate: it is Nock's slam, the
gate's arm `2` run on the gate with the sample at axis `6` replaced. -/
abbrev SlamIsNock (lib : Lib) : Prop := ∀ g x, lib.slam g x = slamGate nock g x

/-- What the model returns with fuel `n`, the Nock of the loop returns. -/
theorem mink_loop_of_model (lib : Lib) (ctx gul : Noun) (hc : MinkIn ctx) (hslam : SlamIsNock lib) :
    ∀ (n : Nat) (t : Trace) (s f : Noun) (r : Tone), minkF lib gul n t s f = some r →
      nock (minkCore (trN t) (C (C s f) gul) ctx) mink.loop = some r.toNoun
  | 0, _, _, _, _, h => by simp [minkF] at h
  | n + 1, t, s, f, r, h => by
    rw [nock_eq_nockW, mink_loop_unfold]
    rw [minkF_succ_eq] at h
    have hE : NStep ctx gul (fun t s f => (minkF lib gul n t s f).map Tone.toNoun) nock t s f
        = some r.toNoun := by
      rw [nstep_exact lib ctx gul hc hslam, h]; rfl
    refine nstep_mono ctx gul (fun t' s' f' x hx => ?_) (fun _ _ => Below?.refl _) t s f _ hE
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hx
    exact mink_loop_of_model lib ctx gul hc hslam n t' s' f' r' hr'

/-- What the loop returns with calls at most `k` deep, the model returns with
fuel `k`. -/
theorem mink_loop_to_model (lib : Lib) (ctx gul : Noun) (hc : MinkIn ctx) (hslam : SlamIsNock lib) :
    ∀ (k : Nat) (t : Trace) (s f x : Noun),
      iterN k (minkCore (trN t) (C (C s f) gul) ctx) mink.loop = some x →
      ∃ r, x = r.toNoun ∧ minkF lib gul k t s f = some r
  | 0, _, _, _, _, h => by simp [iterN] at h
  | k + 1, t, s, f, x, h => by
    rw [iterN_succ, mink_loop_unfold] at h
    have hG : ∀ t' s' f', Below? (iterN k (minkCore (trN t') (C (C s' f') gul) ctx) mink.loop)
        ((minkF lib gul k t' s' f').map Tone.toNoun) := by
      intro t' s' f' y hy
      obtain ⟨r', rfl, hr'⟩ := mink_loop_to_model lib ctx gul hc hslam k t' s' f' y hy
      rw [hr']; rfl
    have h2 := nstep_mono ctx gul hG (fun s f => iterN_sound k s f) t s f x h
    rw [nstep_exact lib ctx gul hc hslam] at h2
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact ⟨r, rfl, by rw [minkF_succ_eq]; exact hr⟩

/-! ## The gate `+mink` -/

@[nock_exec] theorem mink_arm (c : Noun) :
    nock c mink.arm = some (C mink.battery (C (C (C (A 0) (A 0)) (A 0)) c)) := by
  nock_open mink.arm; simp only [nock_exec]

/-- The gate pushes the empty trace and the `|^` core, and runs the loop. -/
theorem mink_gate_loop (ctx s f gul : Noun) :
    nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery
      = nock (minkCore (trN []) (C (C s f) gul) ctx) mink.loop := by
  nock_open mink.battery
  simp [nock_exec, listNoun]

/-- Slamming the pill's `+mink` on `[[s f] gul]` returns `x` exactly when the
model returns a tone `r` with some fuel, and `x` encodes `r`.  The context
gives `+cap` and `+mas` (`MinkIn`), and the scry gate is slammed as Nock slams
it (`SlamIsNock`). -/
theorem mink_gate_iff (lib : Lib) (ctx : Noun) (hc : MinkIn ctx) (hslam : SlamIsNock lib)
    (s f gul x : Noun) :
    nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery = some x ↔
      ∃ r, x = r.toNoun ∧ Mink lib gul [] s f r := by
  rw [mink_gate_loop]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := iterN_complete h
    obtain ⟨r, rfl, hr⟩ := mink_loop_to_model lib ctx gul hc hslam k [] s f x hk
    exact ⟨r, rfl, k, hr⟩
  · rintro ⟨r, rfl, n, hn⟩
    exact mink_loop_of_model lib ctx gul hc hslam n [] s f r hn

/-- What the model returns, the pill's `+mink` returns. -/
theorem mink_gate_of_model (lib : Lib) (ctx : Noun) (hc : MinkIn ctx) (hslam : SlamIsNock lib)
    (s f gul : Noun) (r : Tone) (h : Mink lib gul [] s f r) :
    nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery = some r.toNoun :=
  (mink_gate_iff lib ctx hc hslam s f gul _).mpr ⟨r, rfl, h⟩

/-- What the pill's `+mink` returns is the encoding of what the model returns. -/
theorem mink_gate_to_model (lib : Lib) (ctx : Noun) (hc : MinkIn ctx) (hslam : SlamIsNock lib)
    (s f gul x : Noun)
    (h : nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery = some x) :
    ∃ r, x = r.toNoun ∧ Mink lib gul [] s f r :=
  (mink_gate_iff lib ctx hc hslam s f gul x).mp h

end Compiler
end Formalization
