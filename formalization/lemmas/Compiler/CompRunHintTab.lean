import lemmas.Compiler.CompRunHintCall
import lemmas.Compiler.CompRunHintEx
import lemmas.Compiler.CompSofCode

/-!
# `HintSoundC` from the code table (README Gaps 25)

`comp_run_hintC` asks `SoundAt ctx snd q` under every kept hint (`HintSoundC`):
`+sound` on the hinted formula returns the model's `snd`.  With `snd` the
model of `+sound` on the table itself (`sfSnd cod`, `+sound-far` at depth `3`
over `nommOf cod`), `SoundAt` holds as soon as `+sound-far` returns on `q`
(`soundAt_sf`, from `SfClosed`), and that follows from the table:

* `hintBells n`: the callee of every direct call in `n`, under hints too;
  `sfBells_hint`: the callees on the product path are among them.
* **`hintSound_of_tab`**: `HintSoundC ctx (sfSnd cod) n` for every `n` with
  `Bake.NoAx0` whose `hintBells` have entries, in a table closed for
  `+sound-far` (`SfTable (nommOf cod)`: every nomm of the table has no `%10`
  at axis `0` on its product path and an entry for each callee there).
* `entries_of_calls`: with `CodeAna cod` (the facts of the analysis on
  `code.long-ska`, `CompSofCode.lean`), every callee of a member of `HintOkC`
  whose calls meet `CallOk` (`HintCallsC`) has a nomm entry.
* **`comp_run_hint_tab`**: `comp_run_hintC` at `snd = sfSnd cod` with
  `SfTable` and the entries of the callees in place of `HintSoundC`;
  **`comp_run_hint_ana`**: with `CodeAna cod` alone.

The table condition, checked on the real compiler (`tools/hoon/hinttab.hoon`):
after each of 16 pokes in a row, every entry of `code.long-ska` has
`Bake.NoAx0`, `SfNoAx0`, and an entry for every callee on its product path
and for every direct call anywhere in it.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The callees of every direct call** in a nomm, under hints too. -/
def hintBells : Nomm → List Bell
  | Nomm.cons p q => hintBells p ++ hintBells q
  | Nomm.n0 _ => []
  | Nomm.n1 _ => []
  | Nomm.n2 p q Option.none => hintBells p ++ hintBells q
  | Nomm.n2 p q (some (b, _)) => b :: (hintBells p ++ hintBells q)
  | Nomm.n3 p => hintBells p
  | Nomm.n4 p => hintBells p
  | Nomm.n5 p q => hintBells p ++ hintBells q
  | Nomm.n6 p q r => hintBells p ++ hintBells q ++ hintBells r
  | Nomm.n7 p q => hintBells p ++ hintBells q
  | Nomm.n10 _ v q => hintBells v ++ hintBells q
  | Nomm.n11s _ q _ => hintBells q
  | Nomm.n11d _ h q _ => hintBells h ++ hintBells q
  | Nomm.n12 p q => hintBells p ++ hintBells q
  | Nomm.mean p _ q _ _ => hintBells p ++ hintBells q

/-- The callees on the product path are callees. -/
theorem sfBells_hint : ∀ (n : Nomm) (b : Bell), b ∈ sfBells n → b ∈ hintBells n
  | Nomm.cons p q, b, h => by
    simp only [sfBells, hintBells, List.mem_append] at h ⊢
    exact h.imp (sfBells_hint p b) (sfBells_hint q b)
  | Nomm.n6 p q r, b, h => by
    simp only [sfBells, hintBells, List.mem_append] at h ⊢
    exact h.elim (fun m => Or.inl (Or.inr (sfBells_hint q b m))) (fun m => Or.inr (sfBells_hint r b m))
  | Nomm.n7 p q, b, h => by
    simp only [sfBells, hintBells, List.mem_append] at h ⊢
    exact Or.inr (sfBells_hint q b h)
  | Nomm.n10 _ v q, b, h => by
    simp only [sfBells, hintBells, List.mem_append] at h ⊢
    exact h.imp (sfBells_hint v b) (sfBells_hint q b)
  | Nomm.n11s _ q _, b, h => by
    simp only [sfBells, hintBells] at h ⊢; exact sfBells_hint q b h
  | Nomm.n11d _ _ q _, b, h => by
    simp only [sfBells, hintBells, List.mem_append] at h ⊢; exact Or.inr (sfBells_hint q b h)
  | Nomm.mean _ _ q _ _, b, h => by
    simp only [sfBells, hintBells, List.mem_append] at h ⊢; exact Or.inr (sfBells_hint q b h)
  | Nomm.n2 _ _ (some (b0, _)), b, h => by
    simp only [sfBells, List.mem_singleton] at h; subst h; simp [hintBells]
  | Nomm.n2 _ _ Option.none, b, h => by simp [sfBells] at h
  | Nomm.n0 _, b, h => by simp [sfBells] at h
  | Nomm.n1 _, b, h => by simp [sfBells] at h
  | Nomm.n3 _, b, h => by simp [sfBells] at h
  | Nomm.n4 _, b, h => by simp [sfBells] at h
  | Nomm.n5 _ _, b, h => by simp [sfBells] at h
  | Nomm.n12 _ _, b, h => by simp [sfBells] at h

/-- **`+sound` under a kept hint** returns `sfSnd cod`, for a formula with
`Bake.NoAx0` whose callees have entries, in a table closed for `+sound-far`. -/
theorem soundAt_tab (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (ht : SfTable (nommOf cod)) {q : Nomm} (ha : Bake.NoAx0 q)
    (hb : ∀ b ∈ hintBells q, ∃ m, nommOf cod b = some m) : SoundAt ctx (sfSnd cod) q :=
  soundAt_sf h7 hcode (sfClosed_of_table ht 3 q (sfNoAx0_of_noAx0 q ha) fun b m => hb b (sfBells_hint q b m))

/-- **`HintSoundC` from a closed table**: every nomm with `Bake.NoAx0` whose
callees (under hints too) have entries, in a table closed for `+sound-far`,
meets `SoundAt` under each kept hint for `snd = sfSnd cod`. -/
theorem hintSound_of_tab (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (ht : SfTable (nommOf cod)) :
    ∀ (n : Nomm), Bake.NoAx0 n → (∀ b ∈ hintBells n, ∃ m, nommOf cod b = some m) →
      HintSoundC ctx (sfSnd cod) n
  | Nomm.cons p q, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n0 _, _, _ => by simp only [HintSoundC]
  | Nomm.n1 _, _, _ => by simp only [HintSoundC]
  | Nomm.n2 p q Option.none, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n2 p q (some (b0, k)), ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_cons, List.mem_append] at hb
    simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inr (Or.inl m)),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr (Or.inr m))⟩
  | Nomm.n3 p, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells] at hb; simp only [HintSoundC]
    exact hintSound_of_tab h7 hcode ht p ha hb
  | Nomm.n4 p, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells] at hb; simp only [HintSoundC]
    exact hintSound_of_tab h7 hcode ht p ha hb
  | Nomm.n5 p q, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n6 p q r, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inl (Or.inl m)),
      hintSound_of_tab h7 hcode ht q ha.2.1 fun b m => hb b (Or.inl (Or.inr m)),
      hintSound_of_tab h7 hcode ht r ha.2.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n7 p q, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n10 _ v q, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht v ha.2.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n11s _ q _, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells] at hb; simp only [HintSoundC]
    exact ⟨fun _ => soundAt_tab h7 hcode ht ha hb, hintSound_of_tab h7 hcode ht q ha hb⟩
  | Nomm.n11d _ h q _, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨fun _ => soundAt_tab h7 hcode ht ha.2 fun b m => hb b (Or.inr m),
      hintSound_of_tab h7 hcode ht h ha.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n12 p q, ha, hb => by
    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundC]
    exact ⟨hintSound_of_tab h7 hcode ht p ha.1 fun b m => hb b (Or.inl m),
      hintSound_of_tab h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.mean _ _ _ _ _, _, _ => by simp only [HintSoundC]

/-- **The callees of a member of the class have nomm entries**, from
`CodeAna` and the code entries of its calls (`CallOk` in `HintCallsC`). -/
theorem entries_of_calls {cod : Noun} {env : CallEnv} {E : GenRest → Prop} (hana : CodeAna cod) :
    ∀ (n : Nomm), HintOkC n = true → ∀ (ms : Option Nomm), HintCallsC env cod ctx E ms n →
      ∀ b ∈ hintBells n, ∃ m, nommOf cod b = some m
  | Nomm.cons p q, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana p h.1 ms hc.1 b) (entries_of_calls hana q h.2 ms hc.2 b)
  | Nomm.n0 _, _, _, _, b, hb => by simp [hintBells] at hb
  | Nomm.n1 _, _, _, _, b, hb => by simp [hintBells] at hb
  | Nomm.n2 p q Option.none, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana p h.1 ms hc.1 b) (entries_of_calls hana q h.2 ms hc.2 b)
  | Nomm.n2 p q (some (b0, Option.none)), h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_cons, List.mem_append] at hb
    rcases hb with e | e | e
    · subst e
      obtain ⟨V, hg, -⟩ := hc.1.1
      exact (sofBell_code hana hg).1
    · exact entries_of_calls hana p h.1 ms hc.2.1 b e
    · exact entries_of_calls hana q h.2 ms hc.2.2 b e
  | Nomm.n2 _ _ (some (_, some _)), h, _, _, _, _ => by simp [HintOkC] at h
  | Nomm.n3 p, h, ms, hc, b, hb => by
    simp only [HintOkC] at h; simp only [HintCallsC] at hc; simp only [hintBells] at hb
    exact entries_of_calls hana p h ms hc b hb
  | Nomm.n4 p, h, ms, hc, b, hb => by
    simp only [HintOkC] at h; simp only [HintCallsC] at hc; simp only [hintBells] at hb
    exact entries_of_calls hana p h ms hc b hb
  | Nomm.n5 p q, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana p h.1 ms hc.1 b) (entries_of_calls hana q h.2 ms hc.2 b)
  | Nomm.n6 p q r, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    rcases hb with (e | e) | e
    · exact entries_of_calls hana p h.1.1 ms hc.1 b e
    · exact entries_of_calls hana q h.1.2 ms hc.2.1 b e
    · exact entries_of_calls hana r h.2 ms hc.2.2 b e
  | Nomm.n7 p q, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana p h.1 ms hc.1 b) (entries_of_calls hana q h.2 (some p) hc.2 b)
  | Nomm.n10 _ v q, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana v h.1.2 ms hc.1 b) (entries_of_calls hana q h.2 ms hc.2 b)
  | Nomm.n11s _ q _, h, ms, hc, b, hb => by
    simp only [HintOkC] at h; simp only [HintCallsC] at hc; simp only [hintBells] at hb
    exact entries_of_calls hana q h ms hc b hb
  | Nomm.n11d _ hh q _, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana hh h.1 ms hc.1 b) (entries_of_calls hana q h.2 ms hc.2 b)
  | Nomm.n12 p q, h, ms, hc, b, hb => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hc
    simp only [hintBells, List.mem_append] at hb
    exact hb.elim (entries_of_calls hana p h.1 ms hc.1 b) (entries_of_calls hana q h.2 ms hc.2 b)
  | Nomm.mean _ _ _ _ _, h, _, _, _, _ => by simp [HintOkC] at h

/-- **The run link with hints, `+sound` from the table**: `comp_run_hintC` at
`snd = sfSnd cod` (the model of `+sound` on the table of `ctx`), with a table
closed for `+sound-far` and nomm entries for the callees of `n` in place of
`HintSoundC`. -/
theorem comp_run_hint_tab (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (ht : SfTable (nommOf cod)) (env : CallEnv) (E : GenRest → Prop) (n : Nomm) (hn : HintOkC n = true)
    (msup : Option Nomm) (region : List Nat) (hd : HintCallsC env cod ctx E msup n)
    (he : ∀ b ∈ hintBells n, ∃ m, nommOf cod b = some m) :
    PartH env (sfSnd cod) msup ctx (XM E msup) n region :=
  comp_run_hintC h7 hcode env (sfSnd cod) E n hn msup region hd
    (hintSound_of_tab h7 hcode ht n (noAx0_of_hintC n hn) he)

/-- **The run link with hints, from the facts of the analysis**: every
member of `HintOkC` whose direct calls (under hints too) meet `CallOk` is a
`PartH` at `XM E msup` against `runLCH env (sfSnd cod) true msup`, given
`CodeAna cod` of the code table. -/
theorem comp_run_hint_ana (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (hana : CodeAna cod) (env : CallEnv) (E : GenRest → Prop) (n : Nomm) (hn : HintOkC n = true)
    (msup : Option Nomm) (region : List Nat) (hd : HintCallsC env cod ctx E msup n) :
    PartH env (sfSnd cod) msup ctx (XM E msup) n region :=
  comp_run_hint_tab h7 hcode (sfTable_code hana) env E n hn msup region hd
    (entries_of_calls hana n hn msup hd)

/-- **`comp_run_hint_ana` on every goal with `GInv`.** -/
theorem comp_run_hint_anaX (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (hana : CodeAna cod) (env : CallEnv) (E : GenRest → Prop) (n : Nomm) (hn : HintOkC n = true)
    (msup : Option Nomm) (region : List Nat) (hd : HintCallsC env cod ctx E msup n)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup) n goal region g :=
  (comp_run_hint_ana h7 hcode hana env E n hn msup region hd).link goal g hi

end Compiler
end Formalization
