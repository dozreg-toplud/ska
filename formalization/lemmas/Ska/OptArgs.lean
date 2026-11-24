import lemmas.Ska.OptHopsSim
import lemmas.Ska.OptBranch
import lemmas.Ska.OptMiddleSim

/-!
# `ArgsOK` through the proved passes, and `Keeps` of the three

`+remove-empty-middle` keeps the code only on entries with `ArgsOK`
(`OptMiddleSim.lean`), so `Keeps` carries `ArgsOK` beside `ReadsOK`
(`EntryOK`).  The two other proved passes keep `ArgsOK` (given `ReadsOK`,
which their backward simulations use): `+remove-useless-branching` because
its relation has the same arguments and registers (`rub_argsOK`),
`+remove-hops` because `HopI` has the same arguments with registers in
`RegLe`, which are there together (`RegLe.get_none`), and `HopII` has none
pending after (`hops_argsOK_of`).

With them, `Keeps` of each proved pass: `rub_keeps` (no hypothesis),
`hops_keeps_of` and `hops_keeps` (the hypotheses of `hops_keepsR_of`),
`hopsKeeps` (the statement `HopsKeeps`), and `middle_keeps` (`PassOK` of the
input and of the result, from `middle_keeps_of`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- **`+remove-useless-branching` keeps `ArgsOK`.** -/
theorem rub_argsOK (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeUselessBranching c.blocks = some (ch, bl')) (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun)
    (st : σ) (vals : List Noun) (t : Trace) (hok : ReadsOK lib O c gul st vals t)
    (ha : ArgsOK lib O c gul st vals t) : ArgsOK lib O (withBlocks c bl') gul st vals t := by
  have hbl' : RubBlocks c.blocks (withBlocks c bl').blocks := rub_blocks h
  rintro es' y' k ⟨b0'', hb0'', hs'⟩ hk
  cases hb0 : HoonMap.get c.blocks 0 with
  | none => rw [(hbl' 0).1 hb0] at hb0''; cases hb0''
  | some b0 =>
    obtain ⟨e0, he0, hb0'⟩ := (hbl' 0).2 b0 hb0
    rw [hb0'] at hb0''; cases hb0''
    have hr0 : RubRel c.blocks (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
        ⟨0, rubBlob b0 e0, [], regsOf vals, t, st⟩ := ⟨rfl, rfl, rfl, rfl, e0, he0, Or.inl rfl⟩
    have hok' : ∀ es y k, Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y → ReadsAt gul y k →
        ∃ v, read k y.regs = some v := fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
    obtain ⟨es, y, hs, hr⟩ := rub_bwd (c' := withBlocks c bl') hbl' hok' hs' (Steps.refl _) hr0
    rw [hr.2.1]
    rw [hr.1] at hk
    exact ha es y k ⟨b0, hb0, hs⟩ hk

/-- **`+remove-hops` keeps `ArgsOK`.** -/
theorem hops_argsOK_of {fuel : Nat} (c : Straight Map) {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (HH : HopsHyp c.blocks rev topo) (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel c.blocks rev topo = some (ch, bl')) (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun)
    (st : σ) (vals : List Noun) (t : Trace) (hok : ReadsOK lib O c gul st vals t)
    (ha : ArgsOK lib O c gul st vals t) : ArgsOK lib O (withBlocks c bl') gul st vals t := by
  have H : HopsBlocks c.blocks rev topo (withBlocks c bl').blocks := hops_blocks hn h0 h
  obtain ⟨m0, hm0, b0, T, F, hb0, hmt, rfl⟩ := H.zero
  rintro es' y' k ⟨b0'', hb0'', hs'⟩ hk
  rw [hm0] at hb0''; cases hb0''
  have hr0 : HopRel c.blocks rev (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
      ⟨0, merge b0 T F, [], regsOf vals, t, st⟩ :=
    Or.inl ⟨b0, T, F, rfl, rfl, Reach.zero, hb0, hmt, rfl, RegLe.refl _, rfl, rfl⟩
  have hok' : ∀ es y k, Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y → ReadsAt gul y k →
      ∃ v, read k y.regs = some v := fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
  obtain ⟨es, y, hs, hn'⟩ := hop_bwd (c' := withBlocks c bl') HH H hok' hs' (Steps.refl _) hr0
  rcases hn' with ⟨-, -, -, b1, T1, F1, ops, -, -, -, -, hp', -⟩ | ⟨b1, T1, F1, hI, -⟩
  · rw [hp'] at hk; simp at hk
  · obtain ⟨-, -, -, -, -, hp', hR, -, -⟩ := hI
    rw [hp'] at hk
    have hy := ha es y k ⟨b0, hb0, hs⟩ hk
    cases e : HoonMap.get y'.regs k with
    | none => rw [(hR.get_none k).mp e] at hy; simp at hy
    | some _ => rfl

/-- **`+remove-useless-branching` keeps `LocalOK`**: an op of the code after
is an op of the code before at the same place, or an epilogue `%equ`, `%lob`,
which `+get-reg-safe-assignment` does not name. -/
theorem rub_localOK (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeUselessBranching c.blocks = some (ch, bl')) (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun)
    (st : σ) (vals : List Noun) (t : Trace) (hok : ReadsOK lib O c gul st vals t)
    (hl : LocalOK lib O c gul st vals t) : LocalOK lib O (withBlocks c bl') gul st vals t := by
  have hbl' : RubBlocks c.blocks (withBlocks c bl').blocks := rub_blocks h
  rintro es' y' p rest ⟨b0'', hb0'', hs'⟩ hp hq hb hsa
  cases hb0 : HoonMap.get c.blocks 0 with
  | none => rw [(hbl' 0).1 hb0] at hb0''; cases hb0''
  | some b0 =>
    obtain ⟨e0, he0, hb0'⟩ := (hbl' 0).2 b0 hb0
    rw [hb0'] at hb0''; cases hb0''
    have hr0 : RubRel c.blocks (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
        ⟨0, rubBlob b0 e0, [], regsOf vals, t, st⟩ := ⟨rfl, rfl, rfl, rfl, e0, he0, Or.inl rfl⟩
    have hok' : ∀ es y k, Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y → ReadsAt gul y k →
        ∃ v, read k y.regs = some v := fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
    obtain ⟨es, y, hs, hr⟩ := rub_bwd (c' := withBlocks c bl') hbl' hok' hs' (Steps.refl _) hr0
    obtain ⟨hpe, hre, hte, hste, e, he, hyb⟩ := hr
    rw [hre, hte, hste]
    rcases hyb with hyb | ⟨-, -, hbd0, -, hyb⟩
    · rw [hyb] at hb hq
      simp only [rubBlob] at hb hq
      cases hbd : y.b.body with
      | nil =>
        rw [hbd, List.nil_append] at hb
        exfalso
        rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, -, -, -, hf⟩
        · simp at hb
        · rcases hf with ⟨s, -, h1⟩ | ⟨s, -, h1⟩ | ⟨l, r, -, h1⟩ | ⟨s, -, h1⟩ <;> rw [h1] at hb <;>
            (try simp at hb) <;>
            (obtain ⟨rfl, -⟩ := hb; simp [safeAssign] at hsa)
      | cons p0 r0 =>
        rw [hbd, List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, -⟩ := hb
        exact hl es y p0 r0 ⟨b0, hb0, hs⟩ (by rw [← hpe]; exact hp) hq hbd hsa
    · rw [hyb] at hb
      simp only at hb
      rw [hbd0] at hb; cases hb

/-- **`+remove-useless-branching` keeps the code.** -/
theorem rub_keeps (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeUselessBranching c.blocks = some (ch, bl')) : Keeps c (withBlocks c bl') :=
  keeps_of_R (rub_keepsR c h) fun lib σ O gul st vals t ⟨hok, ha, hl⟩ =>
    ⟨rub_argsOK c h lib σ O gul st vals t hok ha, rub_localOK c h lib σ O gul st vals t hok hl⟩

/-- An op of the merged moves (`%imm` or `%mov`) at the head of moves that
succeed does not crash. -/
theorem movop_isSome {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {t : Trace} {q : Pole}
    {ops : List Pole} {R Ra : Map (Option Noun)} (hq : (∃ n d, q = Pole.imm n d) ∨ (∃ s d, q = Pole.mov s d))
    (h : runMoves (q :: ops) R = some Ra) : (execPole lib O gul st q R t).isSome := by
  rcases hq with ⟨n, d, rfl⟩ | ⟨s, d, rfl⟩
  · simp [execPole, localPole]
  · simp only [runMoves, Option.bind_eq_some_iff] at h
    obtain ⟨R1, h1, -⟩ := h
    simp [execPole, localPole, h1]

/-- **`+remove-hops` keeps `LocalOK`**: an op of the code after at the same
place as the code before is that op on registers above (`RegLe`), and a
merged move runs on the way to a pass that succeeds before (`ArgsOK`, the
check of `+eval-pass`, the counts that `hopSeg` matched). -/
theorem hops_localOK_of {fuel : Nat} (c : Straight Map) {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (HH : HopsHyp c.blocks rev topo) (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel c.blocks rev topo = some (ch, bl')) (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun)
    (st : σ) (vals : List Noun) (t : Trace) (hok : ReadsOK lib O c gul st vals t)
    (ha : ArgsOK lib O c gul st vals t) (hl : LocalOK lib O c gul st vals t) :
    LocalOK lib O (withBlocks c bl') gul st vals t := by
  have H : HopsBlocks c.blocks rev topo (withBlocks c bl').blocks := hops_blocks hn h0 h
  obtain ⟨m0, hm0, b0, T, F, hb0, hmt, rfl⟩ := H.zero
  rintro es' y' p rest ⟨b0'', hb0'', hs'⟩ hp hq hb hsa
  rw [hm0] at hb0''; cases hb0''
  have hr0 : HopRel c.blocks rev (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
      ⟨0, merge b0 T F, [], regsOf vals, t, st⟩ :=
    Or.inl ⟨b0, T, F, rfl, rfl, Reach.zero, hb0, hmt, rfl, RegLe.refl _, rfl, rfl⟩
  have hok' : ∀ es y k, Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y → ReadsAt gul y k →
      ∃ v, read k y.regs = some v := fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
  obtain ⟨es, y, hs, hn'⟩ := hop_bwd (c' := withBlocks c bl') HH H hok' hs' (Steps.refl _) hr0
  rcases hn' with ⟨ht', hst', -, b1, T1, F1, ops, -, -, hpne, hxb, -, hne, hmov, hb', hlen, hck, hpr⟩ |
      ⟨b1, T1, F1, ⟨ht', hst', -, -, -, hp', hR, -, hb'⟩, hnf⟩
  · have hargs : ∀ k, some k ∈ y.params → (HoonMap.get y.regs k).isSome := fun k hk => ha es y k ⟨b0, hb0, hs⟩ hk
    have hpass : (evalPass y.params b1.par y.regs).isSome := by
      rw [evalPass_ok (fun a ha k e => hck k (e ▸ ha))]
      exact passLoop_some _ _ _ hlen (fun k hk => hargs k hk)
    obtain ⟨Rb, hRb⟩ := Option.isSome_iff_exists.mp hpass
    obtain ⟨Ra, hRa, -⟩ := hpr.1 Rb hRb
    rw [hb'] at hb
    obtain ⟨q, ops', rfl⟩ : ∃ q ops', ops = q :: ops' := by
      cases ops with
      | nil => exact absurd rfl hne
      | cons q ops' => exact ⟨q, ops', rfl⟩
    simp only [List.cons_append, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact movop_isSome (hmov _ List.mem_cons_self) hRa
  · rw [hb'] at hb hq
    simp only at hb hq
    rw [hp'] at hp
    have hbd : ∃ rest0, y.b.body = p :: rest0 := by
      cases hbd : y.b.body with
      | nil =>
        rw [hbd, List.nil_append] at hb
        rcases hnf with h1 | h1 | h1 | ⟨rfl, -⟩
        · exact absurd hp h1
        · exact absurd hq h1
        · exact absurd hbd h1
        · cases hb
      | cons p0 r0 =>
        rw [hbd, List.cons_append, List.cons.injEq] at hb
        exact ⟨r0, by rw [hb.1]⟩
    obtain ⟨rest0, hbd⟩ := hbd
    have h1 := hl es y p rest0 ⟨b0, hb0, hs⟩ hp hq hbd hsa
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨ton, R1, t1, s1⟩ := r1
    obtain ⟨R1', hR1', -⟩ := (execPole_le lib O gul y.st p y.t hR (execPole_reads h1)).fwd hr1
    rw [ht', hst', hR1']; rfl

/-- **`+remove-hops` keeps the code**, given what the simulation needs of
`rev` and `topo` (`HopsHyp`), `topo` without duplicates and `0` first. -/
theorem hops_keeps_of {fuel : Nat} (c : Straight Map) {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (HH : HopsHyp c.blocks rev topo) (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel c.blocks rev topo = some (ch, bl')) : Keeps c (withBlocks c bl') :=
  keeps_of_R (hops_keepsR_of c HH hn h0 h) fun lib σ O gul st vals t ⟨hok, ha, hl⟩ =>
    ⟨hops_argsOK_of c HH hn h0 h lib σ O gul st vals t hok ha,
      hops_localOK_of c HH hn h0 h lib σ O gul st vals t hok ha hl⟩


/-- **`+remove-hops` keeps the code**, on a `topo` with `TopoOK`, its
`+rev-cfg`, distinct parameters and jumps that pass the check of
`+eval-pass`. -/
theorem hops_keeps {fuel : Nat} (c : Straight Map) {topo : List Nat} {ch : Bool} {bl' : Map Blob}
    (ht : TopoOK c.blocks topo) (hnd : ParNodup c.blocks) (hpc : PassOK c.blocks)
    (h : removeHops fuel c.blocks (revCfg c.blocks topo) topo = some (ch, bl')) : Keeps c (withBlocks c bl') :=
  hops_keeps_of c ⟨ht.2.2.2.1, fun _ _ _ ho hb hj => revCfg_mem ho hb hj, hnd, hpc⟩ ht.1 ht.2.1 h

/-- **The preservation statement of `+remove-hops` holds.** -/
theorem hopsKeeps (fuel : Nat) : HopsKeeps (Map := Map) fuel :=
  fun c _ _ _ ht hnd hpc h => hops_keeps c ht hnd hpc h

/-- **`+remove-empty-middle` keeps `LocalOK`**: an op of the code after is
the op of the code before at the same place, on registers that agree on
those it mentions (`MidI`). -/
theorem middle_localOK {fuel : Nat} (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeEmptyMiddle fuel c.blocks = some (ch, bl')) (hpc : PassOK c.blocks) (hpc' : PassOK bl')
    (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (vals : List Noun) (t : Trace)
    (hargs : ArgsOK lib O c gul st vals t) (hl : LocalOK lib O c gul st vals t) :
    LocalOK lib O (withBlocks c bl') gul st vals t := by
  have HB : MidBlocks fuel c.blocks (withBlocks c bl').blocks := mid_blocks h
  rintro es' y' p rest ⟨b0'', hb0'', hs'⟩ hp hq hb hsa
  cases e : HoonMap.get c.blocks 0 with
  | none =>
    have e' : HoonMap.get (withBlocks c bl').blocks 0 = none := (HB 0).1 e
    rw [e'] at hb0''; cases hb0''
  | some b0 =>
    obtain ⟨f', hf', e'⟩ := (HB 0).2 b0 e
    rw [e'] at hb0''; cases hb0''
    have hr0 : MidI fuel c.blocks (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
        ⟨0, { b0 with fin := f' }, [], regsOf vals, t, st⟩ :=
      ⟨rfl, rfl, rfl, rfl, by simp, by simp, fun k _ => rfl, b0, f', e, hf', Or.inl rfl, rfl⟩
    obtain ⟨es, y, hs, hn⟩ := mid_bwd HB hpc hpc' hs'
      (fun es z k hz hk => hargs es z k ⟨b0, e, hz⟩ hk) hr0
    obtain ⟨-, ht, hst, hm, -, -, hag, b1, f1, -, -, -, hb'⟩ := hn
    rw [hb'] at hb hq
    simp only at hb hq
    rw [hp] at hm
    have hp0 : y.params = [] := (nil_of_map hm).mpr rfl
    have h1 := hl es y p rest ⟨b0, e, hs⟩ hp0 hq hb hsa
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨ton, R1, t1, s1⟩ := r1
    have hS : ∀ k ∈ poleRegs p, Live c.blocks y k := fun k hk => Or.inr ⟨hp0, hq, op_blobRegs hb hk⟩
    obtain ⟨R1', hR1', -⟩ := (execPole_agr lib O gul y.st p y.t hag hS).fwd hr1
    rw [ht, hst, hR1']; rfl

/-- **`+remove-empty-middle` keeps the code**, given `PassOK` of its input
and of its result. -/
theorem middle_keeps {fuel : Nat} (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeEmptyMiddle fuel c.blocks = some (ch, bl')) (hpc : PassOK c.blocks) (hpc' : PassOK bl') :
    Keeps c (withBlocks c bl') := by
  obtain ⟨hp, hs⟩ := middle_keeps_of c h hpc hpc'
  refine ⟨rfl, rfl, hp, fun lib σ O gul st vals t ⟨hr, ha, hl⟩ => ?_⟩
  obtain ⟨e, r, a⟩ := hs lib σ O gul st vals t ha
  exact ⟨e, r hr, a, middle_localOK c h hpc hpc' lib σ O gul st vals t ha hl⟩

end Opt
end SkaModel
end Formalization
