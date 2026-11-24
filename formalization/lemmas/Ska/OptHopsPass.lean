import lemmas.Ska.OptHops
import lemmas.Ska.OptRegLe

/-!
# The moves of a merged hop

`+remove-hops` replaces the pass of a hop's arguments to the parameters of
the merged block by ops: `[%mov a p]` for an argument `a`, `[%imm 0 p]` for
an argument `~`, in the reverse order of the arguments (`hopSeg_eq`).  The
pass of the code before (`evalPassLoop`) and the ops of the code after
(`runMoves`) are both a run of pairs (`runPairs`), which differ in what an
argument `~` writes (poison before, `0` after) and in the order.  When the
parameters are distinct and no argument is a parameter, the order does not
matter (`runPairs_spec`: each parameter ends with what its argument held, every
other register is kept), so the registers after the ops sit above those after
the pass (`passRel_init`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

theorem nodup_rev {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup :=
  List.pairwise_reverse.mpr (h.imp fun h e => h e.symm)

/-- The op of one argument. -/
def argOp : Option Nat × Nat → Pole
  | (none, p) => Pole.imm (A 0) p
  | (some r, p) => Pole.mov r p

theorem hopSeg_eq : ∀ (as : List (Option Nat)) (ps : List Nat) (acc : List Pole),
    hopSeg as ps acc = if as.length = ps.length then some (((as.zip ps).reverse.map argOp) ++ acc) else none
  | [], [], acc => by simp [hopSeg]
  | [], _ :: _, acc => by simp [hopSeg]
  | _ :: _, [], acc => by simp [hopSeg]
  | a :: as, p :: ps, acc => by
    simp only [hopSeg]
    rw [hopSeg_eq as ps]
    cases a <;> simp [argOp]

/-- What an argument passes: `u0` for `~` (poison before, `0` after), the
register's unit otherwise. -/
def argVal (u0 : Option Noun) (R : Map (Option Noun)) : Option Nat → Option (Option Noun)
  | none => some u0
  | some r => HoonMap.get R r

/-- A run of argument and parameter pairs, in order. -/
def runPairs (u0 : Option Noun) : List (Option Nat × Nat) → Map (Option Noun) → Option (Map (Option Noun))
  | [], R => some R
  | (a, p) :: L, R => (argVal u0 R a).bind fun u => runPairs u0 L (HoonMap.put R p u)

theorem evalPassLoop_pairs : ∀ (as : List (Option Nat)) (ps : List Nat) (R : Map (Option Noun)),
    as.length = ps.length → evalPassLoop as ps R = runPairs none (as.zip ps) R
  | [], [], R, _ => by simp [evalPassLoop, runPairs]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, p :: ps, R, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    cases a with
    | none => simp [evalPassLoop, runPairs, argVal, poison, evalPassLoop_pairs as ps _ h]
    | some r =>
      simp only [evalPassLoop, runPairs, argVal, move, List.zip_cons_cons]
      cases HoonMap.get R r <;> simp [evalPassLoop_pairs as ps _ h]

/-- The ops `+remove-hops` writes for the arguments, run in order. -/
def runMoves : List Pole → Map (Option Noun) → Option (Map (Option Noun))
  | [], R => some R
  | Pole.imm n d :: ops, R => runMoves ops (store d n R)
  | Pole.mov s d :: ops, R => (move s d R).bind (runMoves ops)
  | _ :: _, _ => none

theorem runMoves_pairs : ∀ (L : List (Option Nat × Nat)) (R : Map (Option Noun)),
    runMoves (L.map argOp) R = runPairs (some (A 0)) L R
  | [], R => rfl
  | (none, p) :: L, R => by simp [runMoves, argOp, runPairs, argVal, store, runMoves_pairs L]
  | (some r, p) :: L, R => by
    simp only [List.map_cons, argOp, runMoves, runPairs, argVal, move]
    cases HoonMap.get R r <;> simp [runMoves_pairs L]

/-- No argument is a parameter. -/
def Disj (L : List (Option Nat × Nat)) : Prop := ∀ a p r, (a, p) ∈ L → a = some r → r ∉ L.map Prod.snd

theorem Disj.tail {a : Option Nat} {p : Nat} {L : List (Option Nat × Nat)} (h : Disj ((a, p) :: L)) : Disj L :=
  fun a' p' r h1 h2 hm => h a' p' r (List.mem_cons_of_mem _ h1) h2 (List.mem_cons_of_mem _ hm)

theorem argVal_put {u0 : Option Noun} {R : Map (Option Noun)} {p : Nat} {u : Option Noun} {a : Option Nat}
    (h : ∀ r, a = some r → r ≠ p) : argVal u0 (HoonMap.put R p u) a = argVal u0 R a := by
  cases a with
  | none => rfl
  | some r => simp [argVal, HoonMap.get_put, h r rfl]

theorem Disj.head_ne {a : Option Nat} {p : Nat} {L : List (Option Nat × Nat)} (h : Disj ((a, p) :: L))
    {a' : Option Nat} {p' : Nat} (hm : (a', p') ∈ (a, p) :: L) : ∀ r, a' = some r → r ≠ p :=
  fun r e hrp => h a' p' r hm e (by simp [hrp])

/-- **A run of distinct parameters from arguments that are none of them**:
each parameter ends with what its argument passes, every other register is
kept. -/
theorem runPairs_spec (u0 : Option Noun) : ∀ (L : List (Option Nat × Nat)) (R R1 : Map (Option Noun)),
    (L.map Prod.snd).Nodup → Disj L → runPairs u0 L R = some R1 →
    (∀ a p, (a, p) ∈ L → HoonMap.get R1 p = argVal u0 R a) ∧
    (∀ k, k ∉ L.map Prod.snd → HoonMap.get R1 k = HoonMap.get R k)
  | [], R, R1, _, _, h => by
    simp only [runPairs, Option.some.injEq] at h; subst h; simp
  | (a, p) :: L, R, R1, hn, hd, h => by
    simp only [runPairs] at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨ih1, ih2⟩ := runPairs_spec u0 L _ _ hn.2 hd.tail h
    refine ⟨fun a' p' hm => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.mp hm with e | hm'
      · cases e
        rw [ih2 p hn.1]; simp [HoonMap.get_put, hu]
      · rw [ih1 a' p' hm', argVal_put (hd.head_ne hm)]
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [ih2 k hk.2]; simp [HoonMap.get_put, hk.1]

theorem runPairs_src (u0 : Option Noun) : ∀ (L : List (Option Nat × Nat)) (R R1 : Map (Option Noun)),
    runPairs u0 L R = some R1 → Disj L → ∀ a p, (a, p) ∈ L → (argVal u0 R a).isSome
  | [], _, _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | (a, p) :: L, R, R1, h, hd, a', p', hm => by
    simp only [runPairs] at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    rcases List.mem_cons.mp hm with e | hm'
    · cases e; simp [hu]
    · rw [← argVal_put (u := u) (hd.head_ne hm)]
      exact runPairs_src u0 L _ _ h hd.tail a' p' hm'

theorem runPairs_some (u0 : Option Noun) : ∀ (L : List (Option Nat × Nat)) (R : Map (Option Noun)),
    Disj L → (∀ a p, (a, p) ∈ L → (argVal u0 R a).isSome) → ∃ R1, runPairs u0 L R = some R1
  | [], R, _, _ => ⟨R, rfl⟩
  | (a, p) :: L, R, hd, hs => by
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hs a p List.mem_cons_self)
    obtain ⟨R1, h1⟩ := runPairs_some u0 L (HoonMap.put R p u) hd.tail (fun a' p' hm => by
      rw [argVal_put (hd.head_ne (List.mem_cons_of_mem _ hm))]
      exact hs a' p' (List.mem_cons_of_mem _ hm))
    exact ⟨R1, by simp [runPairs, hu, h1]⟩

/-! ## The relation of a pending pass -/

/-- Ops of the kinds `+remove-hops` writes for arguments. -/
def MovOps (ops : List Pole) : Prop := ∀ q ∈ ops, (∃ n d, q = Pole.imm n d) ∨ (∃ s d, q = Pole.mov s d)

/-- The pass of the code before and the ops of the code after succeed
together, on registers in the order `RegLe`. -/
def PassRel (args : List (Option Nat)) (par : List Nat) (R : Map (Option Noun)) (ops : List Pole)
    (R' : Map (Option Noun)) : Prop :=
  (∀ Rb, evalPass args par R = some Rb → ∃ Ra, runMoves ops R' = some Ra ∧ RegLe Rb Ra) ∧
  (∀ Ra, runMoves ops R' = some Ra → ∃ Rb, evalPass args par R = some Rb ∧ RegLe Rb Ra)

theorem pairs_le {L : List (Option Nat × Nat)} {R R' Rb Ra : Map (Option Noun)} (h : RegLe R R')
    (hn : (L.map Prod.snd).Nodup) (hd : Disj L) (hb : runPairs none L R = some Rb)
    (ha : runPairs (some (A 0)) L.reverse R' = some Ra) : RegLe Rb Ra := by
  have hd' : Disj L.reverse := fun a p r hm e hr =>
    hd a p r (List.mem_reverse.mp hm) e (by simpa [List.map_reverse] using hr)
  have hn' : (L.reverse.map Prod.snd).Nodup := by rw [List.map_reverse]; exact nodup_rev hn
  obtain ⟨b1, b2⟩ := runPairs_spec none L R Rb hn hd hb
  obtain ⟨a1, a2⟩ := runPairs_spec (some (A 0)) L.reverse R' Ra hn' hd' ha
  intro k
  by_cases hk : k ∈ L.map Prod.snd
  · obtain ⟨⟨a, p⟩, hm, e⟩ := List.mem_map.mp hk
    simp only at e; subst e
    rw [b1 a p hm, a1 a p (List.mem_reverse.mpr hm)]
    cases a with
    | none => exact Or.inr ⟨rfl, A 0, rfl⟩
    | some r => exact h r
  · rw [b2 k hk, a2 k (by simpa [List.map_reverse] using hk)]
    exact h k

/-- **At a merged hop**, the ops of the code after and the pass of the code
before are related, given distinct parameters and no argument among them. -/
theorem passRel_init {args : List (Option Nat)} {par : List Nat} {R R' : Map (Option Noun)} {ops : List Pole}
    (h : RegLe R R') (hn : par.Nodup) (hc : ∀ r, some r ∈ args → r ∉ par) (hs : hopSeg args par [] = some ops) :
    MovOps ops ∧ args.length = par.length ∧ (ops = [] ↔ args = []) ∧ PassRel args par R ops R' := by
  rw [hopSeg_eq] at hs
  split at hs
  · rename_i hlen
    simp only [List.append_nil, Option.some.injEq] at hs
    subst hs
    have hsnd : (args.zip par).map Prod.snd = par := List.map_snd_zip (Nat.le_of_eq hlen.symm)
    have hd : Disj (args.zip par) := fun a p r hm e hr => by
      rw [hsnd] at hr; subst e; exact hc r (List.of_mem_zip hm).1 hr
    have hn' : ((args.zip par).map Prod.snd).Nodup := by rw [hsnd]; exact hn
    have hall : args.all (fun a => match a with | none => true | some r => !par.contains r) = true := by
      rw [List.all_eq_true]
      intro a ha
      cases a with
      | none => rfl
      | some r => simpa using hc r ha
    have hev : ∀ R0 : Map (Option Noun), evalPass args par R0 = runPairs none (args.zip par) R0 := fun R0 => by
      unfold evalPass; split
      · exact evalPassLoop_pairs args par R0 hlen
      · rename_i hne; exact absurd hall hne
    have hmv : runMoves ((args.zip par).reverse.map argOp) R' = runPairs (some (A 0)) (args.zip par).reverse R' :=
      runMoves_pairs _ R'
    have hd' : Disj (args.zip par).reverse := fun a p r hm e hr =>
      hd a p r (List.mem_reverse.mp hm) e (by simpa [List.map_reverse] using hr)
    refine ⟨?_, hlen, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨⟨a, p⟩, -, rfl⟩ := List.mem_map.mp hq
      cases a with
      | none => exact Or.inl ⟨_, _, rfl⟩
      | some r => exact Or.inr ⟨_, _, rfl⟩
    · simp only [List.map_eq_nil_iff, List.reverse_eq_nil_iff, List.zip_eq_nil_iff]
      constructor
      · rintro (h | h)
        · exact h
        · subst h; cases args with
          | nil => rfl
          | cons _ _ => simp at hlen
      · intro h; exact Or.inl h
    · intro Rb hb
      rw [hev] at hb
      have hsrc := runPairs_src none _ _ _ hb hd
      obtain ⟨Ra, ha⟩ := runPairs_some (some (A 0)) (args.zip par).reverse R' hd' (fun a p hm => by
        have := hsrc a p (List.mem_reverse.mp hm)
        cases a with
        | none => rfl
        | some r =>
          simp only [argVal] at this ⊢
          cases e : HoonMap.get R' r with
          | some _ => rfl
          | none => rw [(h.get_none r).mp e] at this; cases this)
      exact ⟨Ra, hmv ▸ ha, pairs_le h hn' hd hb ha⟩
    · intro Ra ha
      rw [hmv] at ha
      have hsrc := runPairs_src (some (A 0)) _ _ _ ha hd'
      obtain ⟨Rb, hb⟩ := runPairs_some none (args.zip par) R hd (fun a p hm => by
        have := hsrc a p (List.mem_reverse.mpr hm)
        cases a with
        | none => rfl
        | some r =>
          simp only [argVal] at this ⊢
          cases e : HoonMap.get R r with
          | some _ => rfl
          | none => rw [(h.get_none r).mpr e] at this; cases this)
      exact ⟨Rb, (hev R).trans hb, pairs_le h hn' hd hb ha⟩
  · cases hs

end Opt
end SkaModel
end Formalization
