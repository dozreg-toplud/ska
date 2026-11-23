import lemmas.Ska.CompStraight
import lemmas.Ska.Contract

/-!
# Entering the function that `+to-straight` makes

`toStraight_entry`: if the model of `+to-straight` returns `c'` for the
blocks `blocks`, the input need `ned` and the entry `o`, and the blocks go
down (`Down`), then entering `c'` with the arguments that `split` takes out
of a subject `s` does what block `o` of `blocks` does from registers that
hold `s` as `ned` asks.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-! ## The fold over the blocks -/

section Fold
variable [HoonMapKeys Map] {bs : Map Blob} {ren : Nat → Nat}

/-- What the fold has done for the keys `done`. -/
def FoldInv (bs : Map Blob) (ren : Nat → Nat) (done : List Nat) (m : Map Blob) : Prop :=
  (∀ k ∈ done, ∀ b, HoonMap.get bs k = some b → ∃ kb, keepBlock bs ren k b = some kb ∧ HoonMap.get m k = kb) ∧
    ∀ k, k ∉ done → HoonMap.get m k = Option.none

theorem renameFold_none (ks : List Nat) :
    ks.foldl (fun acc k => acc.bind fun new =>
      (HoonMap.get bs k).bind fun b => (keepBlock bs ren k b).map fun kb =>
        match kb with
        | Option.none => new
        | some b1 => HoonMap.put new k b1) (Option.none : Option (Map Blob)) = Option.none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa using ih

theorem renameFold_spec : ∀ (ks done : List Nat) (m new : Map Blob), FoldInv bs ren done m →
    ks.foldl (fun acc k => acc.bind fun new =>
      (HoonMap.get bs k).bind fun b => (keepBlock bs ren k b).map fun kb =>
        match kb with
        | Option.none => new
        | some b1 => HoonMap.put new k b1) (some m) = some new → FoldInv bs ren (done ++ ks) new
  | [], done, m, new, hi, h => by simp at h; subst h; simpa using hi
  | x :: ks, done, m, new, hi, h => by
    simp only [List.foldl_cons, Option.bind_some] at h
    cases hb : HoonMap.get bs x with
    | none => rw [hb] at h; simp only [Option.bind_none] at h; rw [renameFold_none] at h; cases h
    | some b =>
      rw [hb] at h
      cases hk : keepBlock bs ren x b with
      | none => rw [Option.bind_some, hk] at h; simp only [Option.map_none] at h; rw [renameFold_none] at h; cases h
      | some kb =>
        rw [Option.bind_some, hk, Option.map_some] at h
        have := renameFold_spec ks (done ++ [x]) _ new ?_ h
        · simpa using this
        refine ⟨fun k hkd b' hb' => ?_, fun k hkd => ?_⟩
        · by_cases e : k = x
          · subst e
            rw [hb] at hb'; cases hb'
            refine ⟨kb, hk, ?_⟩
            cases kb with
            | none =>
              by_cases hd : k ∈ done
              · obtain ⟨kb', hk', hm⟩ := hi.1 k hd b hb
                rw [hk] at hk'; cases hk'; exact hm
              · exact hi.2 k hd
            | some b1 => simp [HoonMap.get_put]
          · have hkd' : k ∈ done := by simpa [e] using hkd
            obtain ⟨kb', hk', hm⟩ := hi.1 k hkd' b' hb'
            refine ⟨kb', hk', ?_⟩
            cases kb with
            | none => exact hm
            | some b1 => simp [HoonMap.get_put, e, hm]
        · have e : k ≠ x := fun e => hkd (by simp [e])
          have hkd' : k ∉ done := fun h' => hkd (by simp [h'])
          cases kb with
          | none => exact hi.2 k hkd'
          | some b1 => simp [HoonMap.get_put, e, hi.2 k hkd']

theorem renameBlocks_spec {new : Map Blob} (h : renameBlocks bs ren = some new) :
    ∀ k b, HoonMap.get bs k = some b → ∃ kb, keepBlock bs ren k b = some kb ∧ HoonMap.get new k = kb := by
  have := renameFold_spec (bs := bs) (ren := ren) (HoonMapKeys.keys bs) [] HoonMap.empty new
    ⟨fun k hk => by simp at hk, fun k _ => HoonMap.get_empty k⟩ h
  intro k b hb
  exact this.1 k (by simpa using (HoonMapKeys.mem_keys bs k).mpr (by simp [hb])) b hb

end Fold

/-! ## Runs of registers -/

theorem isRun_iff : ∀ (ins : List Nat) (r0 i : Nat), isRun ins r0 i = true ↔ ins = List.range' (r0 + i) ins.length
  | [], _, _ => by simp [isRun]
  | r :: rs, r0, i => by
    simp only [isRun, Bool.and_eq_true, beq_iff_eq, List.length_cons, List.range'_succ, List.cons.injEq,
      isRun_iff rs r0 (i + 1)]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, by rw [h]; simp [Nat.add_assoc]⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, by rw [h]; simp [Nat.add_assoc]⟩

theorem renReg_inj (r0 n : Nat) : Inj (renReg r0 n) := by
  intro a b h
  simp only [renReg] at h
  repeat' split at h
  all_goals omega

theorem get_regsFrom : ∀ (vs : List Noun) (k : Nat) (m : Map (Option Noun)) (x : Nat),
    HoonMap.get (regsFrom k vs m) x = if k ≤ x ∧ x < k + vs.length then vs[x - k]? else HoonMap.get m x
  | [], k, m, x => by simp only [regsFrom, List.length_nil, Nat.add_zero]; rw [if_neg (by omega)]
  | v :: vs, k, m, x => by
    simp only [regsFrom, get_regsFrom vs (k + 1), HoonMap.get_put, List.length_cons]
    by_cases e : x = k
    · subst e; rw [if_neg (by omega), if_pos rfl, if_pos (by omega), Nat.sub_self]; rfl
    · by_cases h1 : k + 1 ≤ x ∧ x < k + 1 + vs.length
      · rw [if_pos h1, if_pos (by omega)]
        have : x - k = (x - (k + 1)) + 1 := by omega
        rw [this]; simp
      · rw [if_neg h1, if_neg e, if_neg (by omega)]

/-- The registers of the entry, renamed back: argument `i` in `r0 + i`. -/
theorem renRel_entry (r0 : Nat) (args : List Noun) :
    RenRel (renReg r0 args.length) (regsFrom r0 args (HoonMap.empty : Map (Option Noun))) (regsOf args) := by
  intro r
  simp only [SkaModel.read, regsOf, get_regsFrom, HoonMap.get_empty, renReg]
  by_cases h1 : r < r0
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    by_cases h2 : r < r0 + args.length
    · rw [if_pos h2, if_pos (by omega), if_pos (by omega)]; simp
    · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]

/-- Registers that hold the arguments that `split` takes out of `s` hold
`s` as the need asks, when the need's registers are a run. -/
theorem holds_of_split : ∀ (ned : Need) (k : Nat) (s : Noun) (a : List Noun) (R : Map (Option Noun)),
    flattenNeed ned = List.range' k (flattenNeed ned).length →
    SkaModel.split (needToOrd ned) s = some a →
    a.length = (flattenNeed ned).length ∧
      ((∀ i, i < a.length → SkaModel.read (k + i) R = a[i]?) → HoldsN ned R s)
  | Need.none, k, s, a, R, _, h => by
    simp [needToOrd, SkaModel.split] at h; subst h; simp [flattenNeed, HoldsN]
  | Need.this r, k, s, a, R, hf, h => by
    simp [needToOrd, SkaModel.split] at h; subst h
    simp only [flattenNeed, List.length_singleton, List.range'_one, List.cons.injEq, and_true] at hf
    subst hf
    refine ⟨rfl, fun hr => ?_⟩
    have := hr 0 (by simp); simpa [HoldsN] using this
  | Need.pair p q, k, s, a, R, hf, h => by
    cases s with
    | atom _ => simp [needToOrd, SkaModel.split] at h
    | cell u v =>
      simp only [needToOrd, SkaModel.split, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a1, h1, a2, h2, rfl⟩ := h
      simp only [flattenNeed, List.length_append] at hf ⊢
      rw [← List.range'_append_1] at hf
      obtain ⟨hp, hq⟩ := List.append_inj hf (by simp)
      obtain ⟨l1, hp'⟩ := holds_of_split p k u a1 R hp h1
      obtain ⟨l2, hq'⟩ := holds_of_split q (k + (flattenNeed p).length) v a2 R hq h2
      refine ⟨by simp [l1, l2], fun hr => ⟨hp' fun i hi => ?_, hq' fun i hi => ?_⟩⟩
      · rw [hr i (by first | omega | (simp only [List.length_append, List.length_cons] at *; omega))]; simp [List.getElem?_append_left hi]
      · rw [← l1, Nat.add_assoc, hr _ (by first | omega | (simp only [List.length_append, List.length_cons] at *; omega))]
        simp [List.getElem?_append_right]
  | Need.both r p q, k, s, a, R, hf, h => by
    cases s with
    | atom _ => simp [needToOrd, SkaModel.split] at h
    | cell u v =>
      simp only [needToOrd, SkaModel.split, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a1, h1, a2, h2, rfl⟩ := h
      simp only [flattenNeed, List.length_cons, List.length_append, List.range'_succ, List.cons.injEq] at hf ⊢
      obtain ⟨rfl, hf⟩ := hf
      rw [← List.range'_append_1] at hf
      obtain ⟨hp, hq⟩ := List.append_inj hf (by simp)
      obtain ⟨l1, hp'⟩ := holds_of_split p (r + 1) u a1 R hp h1
      obtain ⟨l2, hq'⟩ := holds_of_split q (r + 1 + (flattenNeed p).length) v a2 R hq h2
      refine ⟨by simp [l1, l2], fun hr => ⟨?_, hp' fun i hi => ?_, hq' fun i hi => ?_⟩⟩
      · have := hr 0 (by simp); simpa using this
      · rw [show r + 1 + i = r + (i + 1) by omega, hr (i + 1) (by first | omega | (simp only [List.length_append, List.length_cons] at *; omega))]
        simp [List.getElem?_append_left hi]
      · rw [← l1, show r + 1 + a1.length + i = r + (a1.length + i + 1) by omega, hr _ (by first | omega | (simp only [List.length_append, List.length_cons] at *; omega))]
        simp [List.getElem?_append_right]

/-! ## The entry -/

/-- **Entering what `+to-straight` makes.**  The program `c` holds the
blocks; entering `c'` on the arguments `split` takes out of `s` does what
block `o` of `c` does from registers that hold `s` as `ned` asks. -/
theorem toStraight_entryR [HoonMapKeys Map] {ρ : Nat → Nat} {blocks : Map Blob} {c : Straight Map} {ned : Need}
    {o : Nat} {c' : Straight Map} (h : toStraight blocks ned o = some c') (hdb : DownRk ρ blocks)
    (hd : DownRk ρ c.blocks)
    (hag : ∀ k, k ≠ o → HoonMap.get c.blocks k = HoonMap.get blocks k) :
    c'.need = needToOrd ned ∧ ∃ start, HoonMap.get blocks o = some start ∧
      ∀ (lib : Lib) {σ : Type} (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun),
        SkaModel.split c'.need s = some args → ∃ R : Map (Option Noun), HoldsN ned R s ∧
          execEntry lib O st c' args t gul = execBlob lib O c gul st R t start [] := by
  unfold toStraight at h
  simp only at h
  split at h
  · cases h
  rename_i hrun
  simp only [Bool.not_eq_false] at hrun
  cases hst : HoonMap.get blocks o with
  | none => rw [hst] at h; cases h
  | some start =>
    rw [hst, Option.bind_some] at h
    obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨rfl, start, rfl, ?_⟩
    intro lib σ O st s args t gul hsp
    have ho1 : 1 ≤ o := (hdb o start hst).1
    generalize hins_def : flattenNeed ned = ins at hrun hnew
    generalize hr0 : ins.headD 0 = r0 at hrun hnew
    have hins : ins = List.range' r0 ins.length := by
      have := (isRun_iff ins r0 0).mp hrun; simpa using this
    obtain ⟨hlen, hholds⟩ := holds_of_split ned r0 s args (regsFrom r0 args (HoonMap.empty : Map (Option Noun))) (hins_def ▸ hins) hsp
    rw [hins_def] at hlen
    refine ⟨regsFrom r0 args (HoonMap.empty : Map (Option Noun)), hholds fun i hi => ?_, ?_⟩
    · simp only [SkaModel.read, get_regsFrom, HoonMap.get_empty]
      rw [if_pos (by omega)]; simp
    have hren := renRel_entry (Map := Map) r0 args
    rw [hlen] at hren
    generalize hbs : HoonMap.put (HoonMap.del blocks o) 0 start = bs at hnew
    have hsim : Sim c ⟨needToOrd ned, countArgs (needToOrd ned), new⟩ bs (renReg r0 ins.length) o ρ := by
      refine ⟨renReg_inj _ _, hd, fun k h0 hk => ?_, ?_, fun k b hb hk hby => ?_⟩
      · simp [← hbs, HoonMap.get_put, HoonMap.get_del, h0, hk, hag k hk]
      · simp [← hbs, HoonMap.get_put, HoonMap.get_del, show o ≠ 0 by omega]
      · have hk0 : k ≠ 0 := by have := (hd k b hb).1; omega
        have hbs : HoonMap.get bs k = some b := by
          simp [← hbs, HoonMap.get_put, HoonMap.get_del, hk0, hk, ← hag k hk, hb]
        obtain ⟨kb, hkb, hget⟩ := renameBlocks_spec hnew k b hbs
        simp only [keepBlock, hk0, hby, ne_eq, not_false_eq_true, and_false, if_false] at hkb
        obtain ⟨fin', hf, rfl⟩ := Option.map_eq_some_iff.mp hkb
        exact ⟨fin', hf, hget⟩
    have hbs0 : HoonMap.get bs 0 = some start := by simp [← hbs, HoonMap.get_put]
    obtain ⟨kb, hkb, hget⟩ := renameBlocks_spec hnew 0 start hbs0
    simp only [keepBlock, ne_eq, not_true_eq_false, false_and, if_false] at hkb
    obtain ⟨fin', hf, rfl⟩ := Option.map_eq_some_iff.mp hkb
    simp only [execEntry, hget, Option.bind_some]
    exact (sim_block hsim lib O gul (ρ o) start (hdb o start hst).2 fin' hf st _ _ t [] hren).symm

/-- **Entering what `+to-straight` makes**, for blocks that jump only down. -/
theorem toStraight_entry [HoonMapKeys Map] {blocks : Map Blob} {c : Straight Map} {ned : Need} {o : Nat}
    {c' : Straight Map} (h : toStraight blocks ned o = some c') (hdb : Down blocks) (hd : Down c.blocks)
    (hag : ∀ k, k ≠ o → HoonMap.get c.blocks k = HoonMap.get blocks k) :
    c'.need = needToOrd ned ∧ ∃ start, HoonMap.get blocks o = some start ∧
      ∀ (lib : Lib) {σ : Type} (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun),
        SkaModel.split c'.need s = some args → ∃ R : Map (Option Noun), HoldsN ned R s ∧
          execEntry lib O st c' args t gul = execBlob lib O c gul st R t start [] :=
  toStraight_entryR h hdb.rank hd.rank hag

end Comp
end SkaModel
end Formalization
