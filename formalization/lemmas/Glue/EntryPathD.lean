import lemmas.Glue.EntryPath

/-!
# `EntryOK` with a cell ANNOTATION: the guard that survives `+optimize`

LEDGER 2.c (track G, eighth pass).  `CelGuardP` (`Glue/EntryPath.lean`)
holds on raw code with calls, but NOT on optimized code
(`Glue/EntryPathCheck.lean`: `+optimize` of `[2 [6 [0 2] [0 3] [0 1]] [0
1]]` leaves `[cel 0, hed 0 10]` in block 0 and moves `[tal 0 13]` into the
yes block 7 of its `%brn`: the `%cel` is in a PREDECESSOR).  The guard
that covers both is a must-be-a-cell annotation `K` of the labels, checked
edge by edge (a data-flow certificate):

* `CellOut K o b s`: at the end of block `o` (body `b`), `s` holds a cell:
  `K o s` and no op of the body writes `s`, or a `%cel s` of the body with
  no write of `s` after it;
* `CelAnn bl K`: `K` names no parameter, nothing at `0`; along every edge
  of a reachable block into `o'` with `K o' s`, the block ends with
  `ClqYes _ s o'` or `CellOut`; and every split of `s` in a reachable block
  has a `%cel s` before it in the body or `K o s` with no write before.

**`entryOK_ofK`**: `EntryOK` from `DefFirst`, `ReadsIn`, `NoPoison` and
`CelAnn bl K` for some `K`.  `celAnn_of_P`: `CelGuardP` gives a `K`
(`EntryCell` and no parameter), so `entryOK_ofP` is the special case.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Path

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] {σ : Type}

/-- At the end of block `o` with blob `b`, `s` holds a cell: by the
annotation with no write in the body, or by a `%cel s` with no write
after it. -/
def CellOut (K : Nat → Nat → Prop) (o : Nat) (b : Blob) (s : Nat) : Prop :=
  (K o s ∧ NoWriteBefore b.body b.body.length s) ∨
    ∃ j, j < b.body.length ∧ b.body[j]? = some (Pole.cel s) ∧
      ∀ l, j < l → l < b.body.length → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s

/-- **A must-be-a-cell annotation of the labels, checked edge by edge.** -/
structure CelAnn (bl : Map Blob) (K : Nat → Nat → Prop) : Prop where
  par : ∀ o b s, HoonMap.get bl o = some b → K o s → s ∉ b.par
  zero : ∀ s, ¬ K 0 s
  edge : ∀ o b j s, Reach bl o → HoonMap.get bl o = some b → j ∈ getJmps b.fin → K j.there s →
    ClqYes b.fin s j.there ∨ CellOut K o b s
  split : ∀ o b i p s, Reach bl o → HoonMap.get bl o = some b → b.body[i]? = some p → splitReg p = some s →
    (∃ j : Nat, j < i ∧ b.body[j]? = some (Pole.cel s) ∧
      ∀ l, j < l → l < i → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s) ∨
    (K o s ∧ NoWriteBefore b.body i s)

/-- **`CelGuardP` is an annotation**: `K o s` = `EntryCell bl o s` and `s`
is no parameter of `o`. -/
theorem celAnn_of_P {bl : Map Blob} (h : CelGuardP bl) :
    CelAnn bl (fun o s => EntryCell bl o s ∧ ∀ b, HoonMap.get bl o = some b → s ∉ b.par) where
  par := fun o b s hb hk => hk.2 b hb
  zero := fun s hk => hk.1.1 rfl
  edge := fun o b j s ho hb hj hk => Or.inl (hk.1.2 o b j ho hb hj rfl)
  split := fun o b i p s ho hb hp hs => by
    rcases h o b i p s ho hb hp hs with h1 | ⟨he, hn, hw⟩
    · exact Or.inl h1
    · exact Or.inr ⟨⟨he, fun b' hb' => by rw [hb] at hb'; cases hb'; exact hn⟩, hw⟩

/-- The cell facts of the annotation at a configuration. -/
def CellK (bl : Map Blob) (K : Nat → Nat → Prop) (y : Cfg σ Map) : Prop :=
  ∀ b s, HoonMap.get bl y.lab = some b → K y.lab s →
    NoWriteBefore b.body (b.body.length - y.b.body.length) s → ∃ x z, read s y.regs = some (C x z)

def EInvK (n : Nat) (bl : Map Blob) (K : Nat → Nat → Prop) (y : Cfg σ Map) : Prop :=
  EInv n bl y ∧ CellK bl K y

theorem einvK_step {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat} {K : Nat → Nat → Prop}
    (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn n c.blocks) (hP : NoPoison c.blocks) (hK : CelAnn c.blocks K)
    {x y : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c gul x e y) (hx : EInvK n c.blocks K x) :
    EInvK n c.blocks K y := by
  refine ⟨einv_step hD hR hP hs hx.1, ?_⟩
  obtain ⟨⟨p, b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩, hc⟩ := hx
  cases hs with
  | @pass R hne hR' =>
    intro b2 s hb2 hk hw
    have hpar : x.b.par = b.par := by
      rcases hph with ⟨h1, -, -, -⟩ | ⟨h1, h2, _⟩
      · exact h1
      · exact absurd (by simp [h1, h2] at hne) id
    unfold evalPass at hR'
    split at hR'
    · have hk' := evalPassLoop_keep _ _ _ _ hR' s (by rw [hpar]; rw [hb] at hb2; cases hb2; exact hK.par _ _ _ hb hk)
      unfold read; rw [hk']
      exact hc b2 s hb2 hk hw
    · cases hR'
  | @op p0 rest n' R t' st' hp0 hq hbo hpole =>
    intro b2 s hb2 hk hw
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
    obtain ⟨u, v, huv⟩ := hc b s hb hk hw'
    exact ⟨u, v, by unfold read at huv ⊢; rw [hkeep s hi]; exact huv⟩
  | @jump j b' hp0 hq hbo ht hb' =>
    intro b2 s hb2 hk hw
    have hj : j ∈ getJmps b.fin := by rw [← hfin]; exact taken_mem ht
    obtain ⟨-, -, hle, -, -, hcel⟩ := phase2_of hph hp0 hq
    have hi : i = b.body.length := by
      rw [hbody] at hbo; have := List.drop_eq_nil_iff.mp hbo; omega
    rcases hK.edge x.lab b j s (bpath_reach hB rfl) hb hj hk with hcq | ⟨hk0, hw0⟩ | ⟨j0, hj0, hjc, hw0⟩
    · rw [hfin] at ht; exact clq_cell hcq ht rfl
    · exact hc b s hb hk0 (by rw [hbo]; simpa using hw0)
    · exact hcel j0 s (by omega) hjc (fun l h1 h2 q hq => hw0 l h1 (by omega) q hq)

theorem einvK_steps {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat} {K : Nat → Nat → Prop}
    (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn n c.blocks) (hP : NoPoison c.blocks) (hK : CelAnn c.blocks K)
    {x y : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es y) (hx : EInvK n c.blocks K x) :
    EInvK n c.blocks K y := by
  induction hs with
  | refl => exact hx
  | step s _ ih => exact ih (einvK_step hD hR hP hK s hx)

theorem splitK_cell {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat} {K : Nat → Nat → Prop}
    (hK : CelAnn c.blocks K) {y : Cfg σ Map} (hy : EInvK n c.blocks K y) (hp : y.params = []) (hq : y.b.par = [])
    {p : Pole} {rest : List Pole} (hbo : y.b.body = p :: rest) {s : Nat} (hs : splitReg p = some s) :
    ∃ x z, read s y.regs = some (C x z) := by
  obtain ⟨⟨p', b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩, hc⟩ := hy
  obtain ⟨-, -, hle, -, -, hcel⟩ := phase2_of hph hp hq
  have hget : b.body[i]? = some p := by rw [← List.head?_drop, ← hbody, hbo]; rfl
  rcases hK.split y.lab b i p s (bpath_reach hB rfl) hb hget hs with ⟨j, hj, hjc, hw⟩ | ⟨hk, hw⟩
  · exact hcel j s hj hjc hw
  · have hlen : y.b.body.length = b.body.length - i := by rw [hbody]; simp
    exact hc b s hb hk (by intro l hl q hq; exact hw l (by omega) q hq)

/-- **`EntryOK` from `DefFirst`, `ReadsIn`, `NoPoison` and a cell
annotation**, for every oracle, scry gate, state and trace. -/
theorem entryOK_ofK {c : Straight Map} {K : Nat → Nat → Prop} (hD : DefFirst c.blocks)
    (hR : Compiler.ReadsIn c.nargs c.blocks) (hP : NoPoison c.blocks) (hK : CelAnn c.blocks K)
    {vals : List Noun} (hn : c.nargs ≤ vals.length)
    (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) : EntryOK lib O c gul st vals t := by
  have inv : ∀ es y, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y →
      EInvK c.nargs c.blocks K y := by
    rintro es y ⟨b0, hb0, hs⟩
    exact einvK_steps hD hR hP hK hs ⟨einv_entry hb0 hn st t, fun _ s _ hk => absurd hk (hK.zero s)⟩
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
      obtain ⟨x, z, hxz⟩ := splitK_cell (lib := lib) (O := O) (gul := gul) hK (inv es y hy) hp hq hbo rfl
      simp [execPole, localPole, hxz]
    | tal s d =>
      obtain ⟨x, z, hxz⟩ := splitK_cell (lib := lib) (O := O) (gul := gul) hK (inv es y hy) hp hq hbo rfl
      simp [execPole, localPole, hxz]
    | _ => simp [safeAssign] at hsa

/-- `entryOK_ofP` again, through the annotation. -/
theorem entryOK_ofP' {c : Straight Map} (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn c.nargs c.blocks)
    (hP : NoPoison c.blocks) (hG : CelGuardP c.blocks) {vals : List Noun} (hn : c.nargs ≤ vals.length)
    (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) : EntryOK lib O c gul st vals t :=
  entryOK_ofK hD hR hP (celAnn_of_P hG) hn lib O gul st t

end

end Glue
end SkaModel
end Formalization
