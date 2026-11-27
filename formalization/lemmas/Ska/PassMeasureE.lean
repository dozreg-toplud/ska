import lemmas.Ska.PassMeasureI
import lemmas.Ska.PassMeasureA

/-!
# The measure of one entry (track F, Gaps 16)

The tuple `entryM bus d` of eight numbers of an entry `d` of the identity whose
subject sock is `bus`, compared lexicographically (`EntryLt`, well founded,
`entryLt_wf`):

1. `kS bus - kS less-code` (`less-code` rises in `kS` and stays at most `kS bus`);
2. `1` if the product is `%void`, else `0` (`%void` is the top of the product order);
3. `kS` of the product (it falls);
4. and 5. `mapL` and `mapA` of the map over the product's cape (`MapLt`);
6. `indiW dark indi` (`Ska/PassMeasureI.lean`);
7. and 8. cells and `|` leaves of `seek` (`msgCa_lex`).

`runDatum_entry_step`: a run leaves the five fields `changed` compares the same
(`EntrySame`) or lowers the tuple, on a tidy `bus`, for an old entry that is
`RunW`: its `less-code` is a mask of `bus`, its `indi` is normal and fixed by
`+lack:ca` of `dark`.  An old product `%void` is covered (`mergeProd_old_void`):
the product stays `%void` with the map, or leaves it.  `RunW` holds of the
bunt entry (`runW_bunt`) and of every entry `+run` writes, when the run's
`indi` is normal (`runW_runDatum`).  So an entry that only `+run` writes
changes finitely often (`entry_finite`).

`run_entry_step`: the same on the state-passing analysis (`Analysis.lean`):
a `+run` of a stack member on a state with `SInv` and `TInv` (kept by every
arm, `allPT`) leaves its entry the same or lowers its tuple, given that the
old entry is `RunW` and the run's `indi` is normal.  What is not proved: that
every stack member's entry is `RunW` (an entry written by a memo hit has the
`less-code` of another subject, but such an entry is never on the stack:
`analyzeStep` returns it without a push), and that the `indi` of `fol-loop`
is normal.  `tools/hoon/passmeasure.py` checks both at every run: over the
13,297 runs of the corpus (6,464 after an entry's first) the old `less-code`
was always a mask of `bus`, the old `indi` always fixed by `+lack:ca` of
`dark`, and the new `indi` always normal; 680 runs had an old product `%void`
(512 kept it, 168 left it).
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## `+run` on an old product `%void` -/

theorem msgAnno_void_void (ra σ : Noun) :
    msgAnno ⟨Sock.void, ra⟩ ⟨Sock.void, σ⟩ = ⟨Sock.void, σ⟩ := by
  rw [msgAnno.eq_def]
  split
  · rename_i e; exact e
  · rfl

theorem msgAnno_mk_void (c : Cape) (d ra σ : Noun) :
    msgAnno ⟨Sock.mk c d, ra⟩ ⟨Sock.void, σ⟩ = ⟨Sock.mk c d, ra⟩ := by
  rw [msgAnno.eq_def]
  split
  · rfl
  · rfl

/-- **The merge with an old product `%void`** keeps it (with its map) if the
run's product is `%void` too, else takes the run's. -/
theorem mergeProd_old_void (moved : Bool) (a : Anno) (σ : Noun) :
    mergeProd moved a ⟨Sock.void, σ⟩ = if a.sock = Sock.void then ⟨Sock.void, σ⟩ else a := by
  obtain ⟨sa, ra⟩ := a
  unfold mergeProd
  cases sa with
  | void =>
    simp only [if_true]
    split
    · exact msgAnno_void_void ra σ
    · by_cases e : (⟨Sock.void, ra⟩ : Anno) = ⟨Sock.void, σ⟩
      · rw [e, doubleInt.eq_def]; simp
      · exact doubleInt_void_left rfl e
  | mk c d =>
    simp only [reduceCtorEq, if_false]
    split
    · exact msgAnno_mk_void c d ra σ
    · exact doubleInt_void_right rfl (by simp) (by simp)

/-! ## The tuple -/

/-- Eight numbers, compared lexicographically. -/
abbrev M8 := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- The lexicographic order of `M8`. -/
def lexM8 : WellFoundedRelation M8 :=
  Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel
    (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))))))

/-- `1` for `%void`, else `0`. -/
def pvS (s : Sock) : Nat := if s = Sock.void then 1 else 0

/-- **The tuple of an entry** of the identity with subject sock `bus`. -/
def entryM (bus : Sock) (d : Datum) : M8 :=
  (kS bus - kS d.less, pvS d.prod, kS d.prod, mapL (darkOf d.prod) d.map, mapA (darkOf d.prod) d.map,
    indiW (darkOf bus) d.indi, cellsC d.seek, nosC d.seek)

/-- The order of entries: the tuple falls. -/
def EntryLt (bus : Sock) (d old : Datum) : Prop := lexM8.rel (entryM bus d) (entryM bus old)

theorem entryLt_wf (bus : Sock) : WellFounded (EntryLt bus) := InvImage.wf (entryM bus) lexM8.wf

/-- The five fields that `changed` of `+run` compares. -/
def EntrySame (d old : Datum) : Prop :=
  d.less = old.less ∧ d.prod = old.prod ∧ d.map = old.map ∧ d.indi = old.indi ∧ d.seek = old.seek

/-- **What the step needs of the old entry**: `less-code` is a mask of `bus`,
and `indi` is normal and fixed by `+lack:ca` of `dark`. -/
def RunW (bus : Sock) (d : Datum) : Prop :=
  (∃ c, d.less = Ca.app c bus) ∧ NormCape d.indi ∧ Ca.lack d.indi (darkOf bus) = d.indi

theorem runW_bunt {bus : Sock} (hb : Tidy bus) (hv : bus ≠ Sock.void) : RunW bus Datum.bunt :=
  ⟨⟨Cape.no, (app_no_tidy hb hv).symm⟩, trivial, lack_no_left _⟩

/-- **`+run` writes a `RunW` entry**, when the run's `indi` is normal. -/
theorem runW_runDatum (moved : Bool) {bus : Sock} (out : FolOut) (gen' : Gen) (old : Datum)
    (hb : Tidy bus) (hin : NormCape old.indi) (hg : NormCape gen'.indi) :
    RunW bus (runDatum moved bus out gen' old).1 := by
  refine ⟨⟨_, rfl⟩, ?_, runDatum_indi_lack moved out gen' old hb⟩
  simp only [runDatum]
  split
  · exact normCape_lack (normCape_msgCa_right _ _ hin)
  · exact normCape_lack hg

theorem kS_app_le {bus : Sock} (hb : Tidy bus) (c : Cape) : kS (Ca.app c bus) ≤ kS bus := by
  cases bus with
  | void => simp [Ca.app]
  | mk cb db =>
    rcases genZ_k (genZ_app c (Sock.mk cb db)) (tidy_norm hb) (by simp) with e | e
    · rw [e]; exact Nat.le_refl _
    · exact Nat.le_of_lt e

/-! ## The step -/

section
variable {bus : Sock} {d old : Datum}

theorem lex_less (h : kS bus - kS d.less < kS bus - kS old.less) : EntryLt bus d old :=
  Prod.Lex.left _ _ h

end

/-- **The step of an entry**: a `+run` on a tidy `bus` from a `RunW` entry with a
normal product and a normal map leaves the five fields the same or lowers the
tuple. -/
theorem runDatum_entry_step (moved : Bool) {bus : Sock} (out : FolOut) (gen' : Gen) (old : Datum)
    (hb : Tidy bus) (hw : RunW bus old) (hn : NormSock old.prod) (hp : PiNorm old.map) :
    EntrySame (runDatum moved bus out gen' old).1 old ∨ EntryLt bus (runDatum moved bus out gen' old).1 old := by
  obtain ⟨⟨c0, h0⟩, hin, hfix⟩ := hw
  have hlo : kS old.less ≤ kS bus := h0 ▸ kS_app_le hb c0
  obtain ⟨hl, hlb⟩ := runDatum_less_step moved out gen' old hb h0
  -- with `less-code`, the product and the map the same: `indi`, then `seek`
  have tail : (runDatum moved bus out gen' old).1.less = old.less →
      (runDatum moved bus out gen' old).1.prod = old.prod →
      (runDatum moved bus out gen' old).1.map = old.map →
      EntrySame (runDatum moved bus out gen' old).1 old ∨ EntryLt bus (runDatum moved bus out gen' old).1 old := by
    intro el ep em
    have pre : ∀ (x y : Nat × Nat × Nat), lexM8.rel
        (kS bus - kS old.less, pvS old.prod, kS old.prod, mapL (darkOf old.prod) old.map,
          mapA (darkOf old.prod) old.map, x)
        (kS bus - kS old.less, pvS old.prod, kS old.prod, mapL (darkOf old.prod) old.map,
          mapA (darkOf old.prod) old.map, y) ↔
        (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).rel x y := by
      intro x y
      constructor
      · intro h
        cases h with
        | left _ _ h => exact absurd h (Nat.lt_irrefl _)
        | right _ h =>
        cases h with
        | left _ _ h => exact absurd h (Nat.lt_irrefl _)
        | right _ h =>
        cases h with
        | left _ _ h => exact absurd h (Nat.lt_irrefl _)
        | right _ h =>
        cases h with
        | left _ _ h => exact absurd h (Nat.lt_irrefl _)
        | right _ h =>
        cases h with
        | left _ _ h => exact absurd h (Nat.lt_irrefl _)
        | right _ h => exact h
      · intro h
        exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ h))))
    obtain ⟨hi, _⟩ := runDatum_indi_seek moved bus out gen' old el ep em
    by_cases ei : (runDatum moved bus out gen' old).1.indi = old.indi
    · rcases runDatum_seek_lex moved bus out gen' old el ep em ei with es | es | es
      · exact Or.inl ⟨el, ep, em, ei, es⟩
      · right
        unfold EntryLt entryM
        rw [el, ep, em, ei, pre]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ es)
      · right
        unfold EntryLt entryM
        rw [el, ep, em, ei, pre]
        rw [es.1]
        exact Prod.Lex.right _ (Prod.Lex.right _ es.2)
    · rcases hi with hi | hi
      · exact absurd hi ei
      · right
        have s := (indi_merge_step (x := Ca.lack gen'.indi (darkOf bus)) hin hfix).2 (hi ▸ ei)
        rw [← hi] at s
        unfold EntryLt entryM
        rw [el, ep, em, pre]
        exact Prod.Lex.left _ _ s
  rcases hl with hl | hl
  · by_cases hv : old.prod = Sock.void
    · -- the old product is `%void`
      have hm := mergeProd_old_void moved out.prod old.map
      have ed : (runDatum moved bus out gen' old).1.prod =
          (mergeProd moved out.prod ⟨old.prod, old.map⟩).sock ∧
          (runDatum moved bus out gen' old).1.map = (mergeProd moved out.prod ⟨old.prod, old.map⟩).src :=
        ⟨rfl, rfl⟩
      rw [hv] at ed
      rw [hm] at ed
      by_cases ho : out.prod.sock = Sock.void
      · rw [if_pos ho] at ed
        exact tail hl (ed.1.trans hv.symm) ed.2
      · rw [if_neg ho] at ed
        right
        unfold EntryLt entryM
        rw [hl]
        refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
        show pvS (runDatum moved bus out gen' old).1.prod < pvS old.prod
        rw [ed.1, hv]
        simp [pvS, ho]
    · obtain ⟨hpr, hpv⟩ := runDatum_prod_step moved bus out gen' old hv hn
      rcases hpr with hpr | hpr
      · rcases runDatum_map_step moved bus out gen' old hv hp hpr with hm | hm
        · exact tail hl hpr hm
        · right
          unfold EntryLt entryM
          rw [hl, hpr]
          refine Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ ?_))
          rcases hm with hm | ⟨e, hm⟩
          · exact Prod.Lex.left _ _ hm
          · rw [e]; exact Prod.Lex.right _ (Prod.Lex.left _ _ hm)
      · right
        unfold EntryLt entryM
        rw [hl]
        refine Prod.Lex.right _ ?_
        have e1 : pvS (runDatum moved bus out gen' old).1.prod = pvS old.prod := by simp [pvS, hv, hpv]
        rw [e1]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ hpr)
  · right
    exact lex_less (by omega)

/-- **An entry that only `+run` writes changes finitely often**: there is no
infinite sequence of entries, each a change of the one before by a `+run`
from a `RunW` entry with a normal product and map, on a tidy `bus`. -/
theorem entry_finite {bus : Sock} (f : Nat → Datum)
    (hstep : ∀ k, ¬ EntrySame (f (k + 1)) (f k) → EntryLt bus (f (k + 1)) (f k))
    (hch : ∀ k, ¬ EntrySame (f (k + 1)) (f k)) : False := by
  have wf := entryLt_wf bus
  have key : ∀ d, Acc (EntryLt bus) d → ∀ k, f k = d → False := by
    intro d hacc
    induction hacc with
    | intro x _ ih =>
      intro k hk
      exact ih (f (k + 1)) (hk ▸ hstep k (hch k)) (k + 1) rfl
  exact key (f 0) (wf.apply _) 0 rfl

/-! ## On the state-passing analysis -/

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **The step of an entry on the real analysis**: a `+run` of a stack member
`id` on a state with `SInv` and `TInv` leaves the entry of `id` the same in the
five fields or lowers its tuple, when the old entry is `RunW` (true of the bunt
entry and of every entry `+run` writes, `runW_bunt`, `runW_runDatum`). -/
theorem run_entry_step (env : Env R) (memoF : Memo M) (n : Nat) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {r : Nat × Bool × Bool} (hi : SInv st) (ht : TInv st) (hid : id ∈ st.stk)
    (h : run env memoF n id index st = some (r, st'))
    (hw : ∀ d, gCore st.g id = some d → RunW id.1 d) :
    ∃ old new, gCore st.g id = some old ∧ gCore st'.g id = some new ∧
      (EntrySame new old ∨ EntryLt id.1 new old) := by
  obtain ⟨old, moved, out, gen', ho, hn⟩ := run_entry env memoF n hi hid h
  obtain ⟨hti, _, hpo, hmo⟩ := ht.g_tp id old ho
  exact ⟨old, _, ho, hn, runDatum_entry_step moved out gen' old hti (hw old ho) (tidy_norm hpo) hmo⟩

end Ana

end SkaModel
end Formalization
