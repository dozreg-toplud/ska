import lemmas.Ska.CompBinaryN

/-!
# `[7 [0 axe] q]`: a `%0` run for a goal whose need has entries

When `q` has a `%6`, the need that the run of `q` returns has entries (lazy
blocks), and `p` of `[7 p q]` runs for a goal with entries.  For `p = [0 axe]`
the run is `+from` alone: it puts no op anywhere, and the need it returns has
the goal's entries at the same labels, each with its need moved under `axe`
(`fromL_ent`).  So the relation of the whole is that of `q`, carried over
(`runOKG_from`): the fill ops that the final pass puts at an entry fill its
moved need for the subject, which is its own need for the noun at `axe`
(`fillSem_from`).

This is the case of goals with entries in which the run of `p` puts no op in
the goal's lazy blocks, proved here without a relation for goals with
entries.  `runOKG_from'` (`CompEntryRun.lean`) derives it again from
`RunOKE` of `CompEntryGoal.lean`, which pairs the entries by label.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+from-sure` -/

theorem fromSure_dist {axe : Nat} {sur sur' : Sure S} (h : fromSure axe sur = some sur') (hd : Distinct sur.ned) :
    Distinct sur'.ned := by
  unfold fromSure at h
  by_cases h0 : axe = 0
  · simp [h0] at h
  by_cases hn : sur.ned = Need.none
  · simp only [h0, if_false, hn, if_true] at h
    split at h
    · cases h
    · cases h; trivial
  · simp only [h0, if_false, hn, Option.some.injEq] at h
    subst h; exact distinct_fromPath _ hd axe

/-- **A noun that fits the need of `+from-sure` has the axis, and the noun
there fits the old need** (the converse is in `fromSure_spec`). -/
theorem fromSure_fits {axe : Nat} {sur sur' : Sure S} (h : fromSure axe sur = some sur') (s : Noun)
    (hs : FitsS sur' s) : ∃ p, slot? axe s = some p ∧ FitsS sur p := by
  unfold fromSure at h
  have h0 : axe ≠ 0 := fun e => by simp [e] at h
  have ha : 1 ≤ axe := by omega
  by_cases hn : sur.ned = Need.none
  · simp only [h0, if_false, hn, if_true] at h
    by_cases h1 : axe = 1
    · simp [h1] at h
    simp only [h1, if_false, Option.some.injEq] at h
    subst h
    obtain ⟨_, hl⟩ := hs
    have hsm : (slot? axe s).isSome := by
      by_cases he : HoonSet.isEmpty sur.lok = true
      · simp only [he, if_true] at hl
        exact hl axe ((mem_setOne axe axe).mpr rfl)
      · simp only [he, if_false] at hl
        have hne : HoonSet.toList sur.lok ≠ [] := fun e => he ((HoonSet.isEmpty_iff _).mpr e)
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
        exact slot_isSome_of_peg ha hl hx
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsm
    refine ⟨p, hp, by rw [hn]; trivial, ?_⟩
    by_cases he : HoonSet.isEmpty sur.lok = true
    · intro x hx; rw [(HoonSet.isEmpty_iff _).mp he] at hx; cases hx
    · simp only [he, if_false] at hl
      exact (looks_setRun_peg ha _ s p hp).mp hl
  · simp only [h0, if_false, hn, Option.some.injEq] at h
    subst h
    obtain ⟨hf, hl⟩ := hs
    obtain ⟨p, hp, hf'⟩ := (fits_fromPath _ axe ha s).mp hf
    exact ⟨p, hp, hf', (looks_setRun_peg ha _ s p hp).mp hl⟩

/-- **What the fill ops of an entry do, carried under `axe`**: ops that fill
the moved need for `s` fill the old need for the noun at `axe` of `s`. -/
theorem fillSem_from {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {lo axe : Nat} {L L' : Sure S} {A : List Pole} {s0 s s' : Noun}
    (hf : fromSure axe L = some L') (hs : slot? axe s = some s') (h : FillSem lib O c gul st t ned lo L' A s0 s) :
    FillSem lib O c gul st t ned lo L A s0 s' := by
  obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hf
  intro R hR
  refine ⟨fun fL => ?_, fun nL => (h R hR).2 fun fL' => ?_⟩
  · obtain ⟨R', r, hh, k⟩ := (h R hR).1 (hfit s s' hs fL)
    obtain ⟨p, hp, hh'⟩ := hhold R' s hh
    rw [hs] at hp; cases hp
    exact ⟨R', r, hh', fun x hx hn => k x hx (fun hm => hn (hmem x hm))⟩
  · obtain ⟨p, hp, fp⟩ := fromSure_fits hf s fL'
    rw [hs] at hp; cases hp
    exact nL fp

/-! ## The entries of `+from` -/

/-- Two lists of entries with the same labels, the second the first's with
each need moved under `axe`. -/
inductive FromEnt (axe : Nat) : List (Nat × Lazy S) → List (Nat × Lazy S) → Prop
  | nil : FromEnt axe [] []
  | cons {o : Nat} {l l' : Lazy S} {a b : List (Nat × Lazy S)} :
      fromL axe l = some l' → FromEnt axe a b → FromEnt axe ((o, l) :: a) ((o, l') :: b)

theorem FromEnt.append {axe : Nat} {a b c d : List (Nat × Lazy S)} (h1 : FromEnt axe a b) (h2 : FromEnt axe c d) :
    FromEnt axe (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons hl _ ih => exact FromEnt.cons hl ih

theorem FromEnt.map_fst {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) :
    b.map Prod.fst = a.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

theorem FromEnt.length_eq {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) : b.length = a.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem FromEnt.mem_left {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) {e : Nat × Lazy S}
    (he : e ∈ a) : ∃ l', fromL axe e.2 = some l' ∧ (e.1, l') ∈ b := by
  induction h with
  | nil => cases he
  | cons hl _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hl, List.mem_cons_self⟩
    · obtain ⟨l', h1, h2⟩ := ih he
      exact ⟨l', h1, List.mem_cons_of_mem _ h2⟩

theorem FromEnt.mem_right {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) {e : Nat × Lazy S}
    (he : e ∈ b) : ∃ l, fromL axe l = some e.2 ∧ (e.1, l) ∈ a := by
  induction h with
  | nil => cases he
  | cons hl _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hl, List.mem_cons_self⟩
    · obtain ⟨l, h1, h2⟩ := ih he
      exact ⟨l, h1, List.mem_cons_of_mem _ h2⟩

mutual
/-- **The entries of `+from`** are the old entries, each moved under `axe`. -/
theorem fromL_ent (axe : Nat) : ∀ (L L' : Lazy S), fromL axe L = some L' → FromEnt axe (entries L) (entries L')
  | mk s f b, L', h => by
    unfold fromL at h
    split at h
    · rename_i hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      obtain ⟨s', _, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [entries_ofSure]
      exact FromEnt.nil
    · obtain ⟨s', _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f', hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [entries]
      exact (fromBonds_ent axe b b' hb).append (fromForks_ent axe f f' hf)

theorem fromForks_ent (axe : Nat) : ∀ (f f' : List (ForkE S)), fromForks axe f = some f' →
    FromEnt axe (forkEntries f) (forkEntries f')
  | [], f', h => by
    simp only [fromForks, Option.some.injEq] at h
    subst h; exact FromEnt.nil
  | ((oy, y), (on, n)) :: rest, f', h => by
    simp only [fromForks] at h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n', hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [forkEntries]
    exact ((FromEnt.cons hy (fromL_ent axe y y' hy)).append (FromEnt.cons hn (fromL_ent axe n n' hn))).append
      (fromForks_ent axe rest r hr)

theorem fromBonds_ent (axe : Nat) : ∀ (b b' : List (Nat × Lazy S)), fromBonds axe b = some b' →
    FromEnt axe (bondEntries b) (bondEntries b')
  | [], b', h => by
    simp only [fromBonds, Option.some.injEq] at h
    subst h; exact FromEnt.nil
  | (o, l) :: rest, b', h => by
    simp only [fromBonds] at h
    obtain ⟨l', hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [bondEntries]
    exact (FromEnt.cons hl (fromL_ent axe l l' hl)).append (fromBonds_ent axe rest r hr)
end

/-- The sure part of `+from` is `+from-sure` of the sure part. -/
theorem fromL_sure {axe : Nat} {L L' : Lazy S} (h : fromL axe L = some L') : fromSure axe L.sure = some L'.sure := by
  rcases L with ⟨s, f, b⟩
  unfold fromL at h
  split at h
  · obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hs
  · obtain ⟨s', hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨f', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hs

/-! ## The relation of `[7 [0 axe] q]` from that of `q` -/

theorem RunOKP.toG {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (h : RunOKP (Map := Map) lib nm goal g0 g1 nex) : RunOKG (Map := Map) lib nm goal g0 g1 nex :=
  ⟨h.ext, h.grow, h.cnd, h.lo, h.hi, h.ent, fun r hr => Or.inr (h.regs r hr), h.dist, h.eregs, h.labs, h.nodup,
    h.size, fun s hs => Or.inl (h.nec s hs), fun c ned σ O st t gul s0 s ag hned regs hh hn =>
      goalSem_mono (fun r hr => hr.1) _ _ (h.sem c ned σ O st t gul s0 s ag hned regs hh hn)⟩

theorem RunOKN.toG {lib : Lib} {nm : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (h : RunOKN (Map := Map) lib nm sur th g0 g1 nex) : RunOKG (Map := Map) lib nm (CGoal.next sur th) g0 g1 nex :=
  ⟨h.ext, h.grow, h.cnd, h.lo, h.hi, h.ent, h.regs, h.dist, h.eregs, h.labs, h.nodup, h.size, h.nec, h.sem⟩

/-- **`[7 [0 axe] q]` from `q`**: the relation of the run of `q` for any
fork-free goal carries over to the whole, whose need is `+from` of `q`'s. -/
theorem runOKG_from {lib : Lib} {axe : Nat} {q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nx : NextL S}
    {laz' : Lazy S} (hq : RunOKG (Map := Map) lib q goal g0 g1 nx) (hf : fromL axe nx.laz = some laz') :
    RunOKG (Map := Map) lib (Nomm.n7 (Nomm.n0 axe) q) goal g0 g1 ⟨laz', nx.th⟩ := by
  have hs := fromL_sure hf
  have E := fromL_ent axe _ _ hf
  obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hs
  refine ⟨hq.ext, hq.grow, hq.cnd, hq.lo, hq.hi, hq.ent, fun r hr => hq.regs r (hmem r hr), fromSure_dist hs hq.dist,
    fun e he => ?_, fun e he => ?_, ?_, ?_, fun s hs' => ?_, fun c ned σ O st t gul s0 s ag hned regs hh hn => ?_⟩
  · obtain ⟨l, hl, hm⟩ := E.mem_right he
    obtain ⟨d, rr⟩ := hq.eregs _ hm
    have hls := fromL_sure hl
    obtain ⟨_, _, _, hmem'⟩ := fromSure_spec (Map := Map) hls
    exact ⟨fromSure_dist hls d, fun r hr => rr r (hmem' r hr)⟩
  · obtain ⟨l, _, hm⟩ := E.mem_right he
    exact hq.labs (e.1, l) hm
  · show ((entries laz').map Prod.fst).Nodup
    rw [E.map_fst]; exact hq.nodup
  · show (entries laz').length ≤ 2 * sixCount (Nomm.n7 (Nomm.n0 axe) q)
    rw [E.length_eq]; simp only [sixCount]; have := hq.size; omega
  · simp only [pureEval]
    cases e : slot? axe s with
    | none => exact Or.inl rfl
    | some s' =>
      simp only [Option.bind_some]
      exact hq.nec s' (fun f => hs' (hfit s s' e f))
  · obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
    have agQ : AgreeP lib O c gul st t ned g0 g1 nx.laz s0 s' := by
      refine ⟨fun o h0 h1 hnm => ag.1 o h0 h1 (by rw [E.map_fst]; exact hnm), fun e he => ?_⟩
      obtain ⟨l', hl', hm'⟩ := E.mem_left he
      obtain ⟨A, th, b1, b2, fs⟩ := ag.2 _ hm'
      exact ⟨A, th, b1, b2, fillSem_from (fromL_sure hl') hs1 fs⟩
    have H := hq.sem c ned σ O st t gul s0 s' agQ hned regs hh' hn
    simp only [pureEval, hs1, Option.bind_some]
    exact H

/-- The case `%0` of `runL` for a goal `%next`, at an axis of at least `2`:
`+from`, with no op. -/
theorem runL_n0_next {axe : Nat} (ha : 2 ≤ axe) (laz : Lazy S) (th : Jmp) (region : List Nat) (g : Gen Map) :
    (runL (Nomm.n0 axe) (CGoalL.next laz th) region g : Option (NextL S × Gen Map)) =
      (fromL axe laz).map fun l => (⟨l, th⟩, g) := by
  unfold runL
  simp only [show axe ≠ 0 by omega, show axe ≠ 1 by omega, if_false, simpleNextL, bind_apply, pure_apply,
    Option.bind_some]
  cases fromL axe laz <;> rfl

theorem runL_seven_from {axe : Nat} (ha : 2 ≤ axe) {q : Nomm} {goal : CGoalL S} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (h : runL (Nomm.n7 (Nomm.n0 axe) q) goal region g0 = some (nex, g1)) :
    ∃ nx laz', runL q goal region g0 = some (nx, g1) ∧ fromL axe nx.laz = some laz' ∧ nex = ⟨laz', nx.th⟩ := by
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [NextL.goal, runL_n0_next ha] at h2
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨nx, l, h1, hl, rfl⟩

end Comp
end SkaModel
end Formalization
