import lemmas.Glue.Entry

/-!
# `EntryOK` with a PATH guard: the `%clq` yes-edge (track G, eighth pass)

LEDGER 2.c.  `entryOK_of` (`Glue/Entry.lean`) asks `CelGuard`: every
`%hed s` / `%tal s` of a reachable block comes after a `%cel s` of its own
body.  That is FALSE on the raw code of a direct call: `+mono-try-call`
emits the split block `[hed r rh, tal r rt] hop ..` and, right after it, the
block `[clq r (jmp0 split) (jmp0 fail)]`, so the split is guarded by the
TERMINATOR of the block that jumps to it (`Ska/CompDirectMCheck.lean`, case
`%dt`: block 4 `[hed 2 4, tal 2 3]`, entered from block 5 `clq 2 (jmp0 4)
(jmp0 2)`).

* `ClqYes f s o`: `f` is `%clq s z w` whose no-edge `w` does not go to `o`;
  so a run that takes an edge of `f` into `o` found a cell in `s`.
* `EntryCell bl o s`: `o` is not the entry and every reachable block that
  jumps to `o` ends with `ClqYes _ s o`.
* `CelGuardP bl`: every split of `s` at op `i` of a reachable block is
  guarded by a `%cel s` of the body (as in `CelGuard`), OR the block has
  `EntryCell _ s`, `s` is not a parameter of it, and no op before `i`
  writes `s`.  `celGuardP_of`: `CelGuard` gives it.
* `CellP bl y`: at a configuration of block `y.lab`, a register with
  `EntryCell`, not a parameter, not written by the ops already run, holds a
  cell.  `EInvP = EInv ∧ CellP`, kept by every step (`einvP_step`).
* **`entryOK_ofP`**: `EntryOK` from `DefFirst`, `ReadsIn`, `NoPoison`,
  `CelGuardP` and at least `nargs` entry values.

The check (`Glue/EntryPathCheck.lean`): `CelGuardP` holds on the raw code of
the seven direct calls of `Ska/CompDirectMCheck.lean`, on 5,040 more direct
calls made from `enumCX`, on the indirect calls of `enumCX`, and on the
OPTIMIZED code of all of them; `CelGuard` fails on every raw direct call
with a split.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Path

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] {σ : Type}

/-! ## The path guard -/

/-- **`f` is a `%clq s` whose no-edge does not go to `o`**: a run that takes
an edge of `f` into `o` read a cell in `s`. -/
def ClqYes (f : Termin) (s o : Nat) : Prop := ∃ z w, f = Termin.clq s z w ∧ w.there ≠ o

/-- **Block `o` is entered only through yes-edges of `%clq s`**: it is not
the entry, and every reachable block with a jump to `o` ends with
`ClqYes _ s o`. -/
def EntryCell (bl : Map Blob) (o s : Nat) : Prop :=
  o ≠ 0 ∧ ∀ o' b' j, Reach bl o' → HoonMap.get bl o' = some b' → j ∈ getJmps b'.fin → j.there = o →
    ClqYes b'.fin s o

/-- No op of the first `i` of the body writes `s`. -/
def NoWriteBefore (body : List Pole) (i s : Nat) : Prop :=
  ∀ l, l < i → ∀ q, body[l]? = some q → aliasDst q ≠ some s

/-- **The path guard**: every `%hed s` / `%tal s` of a reachable block comes
after a `%cel s` of its body with no write of `s` between, or the block is
entered only through yes-edges of `%clq s`, `s` is not one of its
parameters and no op before the split writes `s`. -/
def CelGuardP (bl : Map Blob) : Prop :=
  ∀ o b i p s, Reach bl o → HoonMap.get bl o = some b → b.body[i]? = some p → splitReg p = some s →
    (∃ j : Nat, j < i ∧ b.body[j]? = some (Pole.cel s) ∧
      ∀ l, j < l → l < i → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s) ∨
    (EntryCell bl o s ∧ s ∉ b.par ∧ NoWriteBefore b.body i s)

/-- **`CelGuard` is the special case with no path guard.** -/
theorem celGuardP_of {bl : Map Blob} (h : CelGuard bl) : CelGuardP bl :=
  fun o b i p s ho hb hp hs => Or.inl (h o b i p s ho hb hp hs)

/-! ## The cell facts of a configuration -/

/-- **The cell facts of the entry edge**: at a configuration of block
`y.lab`, a register with `EntryCell`, not a parameter of the block, and not
written by the ops already run, holds a cell. -/
def CellP (bl : Map Blob) (y : Cfg σ Map) : Prop :=
  ∀ b s, HoonMap.get bl y.lab = some b → EntryCell bl y.lab s → s ∉ b.par →
    NoWriteBefore b.body (b.body.length - y.b.body.length) s → ∃ x z, read s y.regs = some (C x z)

/-- **The invariant with the path guard.** -/
def EInvP (n : Nat) (bl : Map Blob) (y : Cfg σ Map) : Prop := EInv n bl y ∧ CellP bl y

/-- `+eval-pass` writes only the parameters. -/
theorem evalPassLoop_keep : ∀ (args : List (Option Nat)) (par : List Nat) (regs R : Map (Option Noun)),
    evalPassLoop args par regs = some R → ∀ k, k ∉ par → HoonMap.get R k = HoonMap.get regs k
  | [], par, regs, R, h, k, hk => by
    simp only [evalPassLoop] at h
    split at h
    · cases h; rfl
    · cases h
  | _ :: _, [], _, _, h, _, _ => by simp [evalPassLoop] at h
  | a :: args, q :: par, regs, R, h, k, hk => by
    simp only [evalPassLoop] at h
    have hkq : k ≠ q := fun e => hk (by rw [e]; exact List.mem_cons_self ..)
    have hk' : k ∉ par := fun m => hk (List.mem_cons_of_mem _ m)
    cases a with
    | none =>
      simp only [Option.bind_some] at h
      rw [evalPassLoop_keep args par _ R h k hk']
      simp only [poison, HoonMap.get_put]; rw [if_neg (fun e => hkq (by rw [e]))]
    | some r =>
      obtain ⟨R1, hm, h⟩ := Option.bind_eq_some_iff.mp h
      rw [evalPassLoop_keep args par R1 R h k hk']
      unfold move at hm
      obtain ⟨u, _, rfl⟩ := Option.map_eq_some_iff.mp hm
      simp only [HoonMap.get_put]; rw [if_neg (fun e => hkq (by rw [e]))]

/-- A taken `%clq` edge into `o` whose no-edge goes elsewhere read a cell. -/
theorem clq_cell {regs : Map (Option Noun)} {f : Termin} {s o : Nat} {j : Jmp} (hc : ClqYes f s o)
    (ht : taken regs f = some j) (hj : j.there = o) : ∃ x z, read s regs = some (C x z) := by
  obtain ⟨z, w, rfl, hw⟩ := hc
  simp only [taken, Option.map_eq_some_iff] at ht
  obtain ⟨v, hv, hjv⟩ := ht
  cases v with
  | cell x y => exact ⟨x, y, hv⟩
  | atom => simp only at hjv; subst hjv; exact absurd hj hw

/-- **`EInvP` is kept by every step.** -/
theorem einvP_step {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat}
    (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn n c.blocks) (hP : NoPoison c.blocks)
    {x y : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c gul x e y) (hx : EInvP n c.blocks x) :
    EInvP n c.blocks y := by
  refine ⟨einv_step hD hR hP hs hx.1, ?_⟩
  obtain ⟨⟨p, b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩, hc⟩ := hx
  cases hs with
  | @pass R hne hR' =>
    intro b2 s hb2 he hs hw
    have hpar : x.b.par = b.par := by
      rcases hph with ⟨h1, -, -, -⟩ | ⟨h1, h2, _⟩
      · exact h1
      · exact absurd (by simp [h1, h2] at hne) id
    unfold evalPass at hR'
    split at hR'
    · have hk := evalPassLoop_keep _ _ _ _ hR' s (by rw [hpar]; rw [hb] at hb2; cases hb2; exact hs)
      unfold read; rw [hk]
      exact hc b2 s hb2 he hs hw
    · cases hR'
  | @op p0 rest n' R t' st' hp0 hq hbo hpole =>
    intro b2 s hb2 he hs hw
    rw [hb] at hb2; cases hb2
    obtain ⟨-, -, hle, -, -, -⟩ := phase2_of hph hp0 hq
    rw [hbody] at hbo
    have hget : b.body[i]? = some p0 := by rw [← List.head?_drop, hbo]; rfl
    have hlt : i < b.body.length := by
      rcases Nat.lt_or_ge i b.body.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hget; cases hget
    have hlen : rest.length = b.body.length - (i + 1) := by
      have := congrArg List.length hbo; simp at this; omega
    have hxl : x.b.body.length = b.body.length - i := by rw [hbody]; simp
    have hw' : NoWriteBefore b.body (b.body.length - x.b.body.length) s := by
      intro l hl q hq; exact hw l (by simp only; omega) q hq
    have hi : aliasDst p0 ≠ some s := hw i (by simp only; omega) p0 hget
    obtain ⟨hkeep, -⟩ := execPole_zero hpole
    obtain ⟨u, v, huv⟩ := hc b s hb he hs hw'
    exact ⟨u, v, by unfold read at huv ⊢; rw [hkeep s hi]; exact huv⟩
  | @jump j b' hp0 hq hbo ht hb' =>
    intro b2 s hb2 he hs hw
    have hj : j ∈ getJmps b.fin := by rw [← hfin]; exact taken_mem ht
    have hcq := he.2 x.lab b j (bpath_reach hB rfl) hb hj rfl
    rw [hfin] at ht
    exact clq_cell hcq ht rfl

theorem einvP_steps {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat}
    (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn n c.blocks) (hP : NoPoison c.blocks)
    {x y : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es y) (hx : EInvP n c.blocks x) :
    EInvP n c.blocks y := by
  induction hs with
  | refl => exact hx
  | step s _ ih => exact ih (einvP_step hD hR hP s hx)

theorem einvP_entry {n : Nat} {bl : Map Blob} {b0 : Blob} (hb0 : HoonMap.get bl 0 = some b0) {vals : List Noun}
    (hn : n ≤ vals.length) (st : σ) (t : Trace) :
    EInvP n bl (⟨0, b0, [], regsOf vals, t, st⟩ : Cfg σ Map) :=
  ⟨einv_entry hb0 hn st t, fun _ _ _ he => absurd rfl he.1⟩

/-- The split at op `i` of the current block reads a cell. -/
theorem split_cell {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat}
    (hG : CelGuardP c.blocks) {y : Cfg σ Map} (hy : EInvP n c.blocks y) (hp : y.params = []) (hq : y.b.par = [])
    {p : Pole} {rest : List Pole} (hbo : y.b.body = p :: rest) {s : Nat} (hs : splitReg p = some s) :
    ∃ x z, read s y.regs = some (C x z) := by
  obtain ⟨⟨p', b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩, hc⟩ := hy
  obtain ⟨-, -, hle, -, -, hcel⟩ := phase2_of hph hp hq
  have hget : b.body[i]? = some p := by rw [← List.head?_drop, ← hbody, hbo]; rfl
  rcases hG y.lab b i p s (bpath_reach hB rfl) hb hget hs with ⟨j, hj, hjc, hw⟩ | ⟨he, hns, hw⟩
  · exact hcel j s hj hjc hw
  · have hlen : y.b.body.length = b.body.length - i := by rw [hbody]; simp
    exact hc b s hb he hns (by intro l hl q hq; exact hw l (by omega) q hq)

/-! ## `EntryOK` -/

/-- **`EntryOK` from the static facts with the PATH guard**: `DefFirst`,
`ReadsIn` at the argument count, `NoPoison`, `CelGuardP`, and at least
`nargs` entry values; for every oracle, scry gate, state and trace. -/
theorem entryOK_ofP {c : Straight Map} (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn c.nargs c.blocks)
    (hP : NoPoison c.blocks) (hG : CelGuardP c.blocks) {vals : List Noun} (hn : c.nargs ≤ vals.length)
    (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) : EntryOK lib O c gul st vals t := by
  have inv : ∀ es y, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y →
      EInvP c.nargs c.blocks y := by
    rintro es y ⟨b0, hb0, hs⟩
    exact einvP_steps hD hR hP hs (einvP_entry hb0 hn st t)
  have rd : ∀ es y, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y → y.params = [] →
      y.b.par = [] → ∀ k, ((∃ p rest, y.b.body = p :: rest ∧ k ∈ aliasReads p) ∨
        (y.b.body = [] ∧ k ∈ finRegs y.b.fin)) → Present y.regs k ∧ Pure y.regs := by
    intro es y hy hp hq k hk
    obtain ⟨⟨p, b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩, -⟩ := inv es y hy
    have h2 := phase2_of hph hp hq
    refine ⟨reads_present hD hR hB hb hpast h2 ?_, hpure⟩
    rcases hk with ⟨p0, rest, hbo, hk⟩ | ⟨hbo, hk⟩
    · left; rw [← hbody, hbo]; exact hk
    · right; rw [hbody] at hbo; rw [← hfin]
      exact ⟨by have := List.drop_eq_nil_iff.mp hbo; have := h2.2.2.1; omega, hk⟩
  refine ⟨fun es y k hy hk => ?_, fun es y k hy hk => ?_, fun es y p rest hy hp hq hbo hsa => ?_⟩
  · obtain ⟨hp, hq, hk⟩ := hk
    have hk' : (∃ p rest, y.b.body = p :: rest ∧ k ∈ aliasReads p) ∨ (y.b.body = [] ∧ k ∈ finRegs y.b.fin) := by
      rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, hk⟩
      · exact Or.inl ⟨p, rest, hb, poleReads_sub hk⟩
      · exact Or.inr ⟨hb, finReads_sub hk⟩
    obtain ⟨h1, h2⟩ := rd es y hy hp hq k hk'
    exact read_of_present h2 h1
  · obtain ⟨⟨p, b, i, -, -, -, -, -, -, hph⟩, -⟩ := inv es y hy
    rcases hph with ⟨-, -, ha, -⟩ | ⟨-, hp, -⟩
    · exact ha k hk
    · rw [hp] at hk; cases hk
  · have val : ∀ k, k ∈ aliasReads p → ∃ v, read k y.regs = some v := fun k hk => by
      obtain ⟨h1, h2⟩ := rd es y hy hp hq k (Or.inl ⟨p, rest, hbo, hk⟩)
      exact read_of_present h2 h1
    cases p with
    | imm a d => simp [execPole, localPole]
    | mov s d =>
      obtain ⟨h1, -⟩ := rd es y hy hp hq s
        (Or.inl ⟨_, rest, hbo, mem_erase_last (l := [s]) (List.mem_singleton_self s)⟩)
      unfold Present at h1
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h1
      simp [execPole, localPole, move, hu]
    | con a b d =>
      obtain ⟨va, ha⟩ := val a (poleReads_sub (gul := gul) (p := Pole.con a b d) (by simp [poleReads]))
      obtain ⟨vb, hb⟩ := val b (poleReads_sub (gul := gul) (p := Pole.con a b d) (by simp [poleReads]))
      simp [execPole, localPole, ha, hb]
    | hed s d =>
      obtain ⟨x, z, hxz⟩ := split_cell (lib := lib) (O := O) (gul := gul) hG (inv es y hy) hp hq hbo rfl
      simp [execPole, localPole, hxz]
    | tal s d =>
      obtain ⟨x, z, hxz⟩ := split_cell (lib := lib) (O := O) (gul := gul) hG (inv es y hy) hp hq hbo rfl
      simp [execPole, localPole, hxz]
    | _ => simp [safeAssign] at hsa

/-- **The old theorem is the special case** (`CelGuard` gives `CelGuardP`). -/
theorem entryOK_of' {c : Straight Map} (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn c.nargs c.blocks)
    (hP : NoPoison c.blocks) (hG : CelGuard c.blocks) {vals : List Noun} (hn : c.nargs ≤ vals.length)
    (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) : EntryOK lib O c gul st vals t :=
  entryOK_ofP hD hR hP (celGuardP_of hG) hn lib O gul st t

end

end Glue
end SkaModel
end Formalization
