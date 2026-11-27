import lemmas.Ska.OptAliasPlainDriver

/-!
# Raw `+comp` output and the optimizer's invariant: the tools on blocks

README Gaps 14.  The fields of `OptIn` (`OptAliasPlainDriver.lean`) that are
about registers, in forms that a run of `+comp` can be followed with:

* `Defd bl r`: `r` has a definition (a parameter or an op) somewhere in
  `bl`; `DefUniq bl`: at most one, over all blocks, which gives `DefOnceR`
  (`defOnceR_of_defUniq`) and `r ∈ allDefs bl ↔ Defd bl r` (`mem_allDefs`).
* `Live bl k r`: some path from block `k` reads `r` before any definition
  of it (a parameter, an earlier op, an earlier block of the path).
  `defFirst_of_live`: `DefFirst` holds when no register that has a
  definition is live at block `0`.  Code is built backwards, from the
  continuation, so liveness is what a run can state about the code it made.
* `NoTr bl`: no trace hint op; then `TrimBr bl (fun _ => [])`
  (`trimBr_of_noTr`).
* The algebra of liveness: `OpsRF A r` (the ops `A` read `r` before
  writing it), `opsRF_append`, the block forms, and `live_frame`: liveness at
  a label below `L` does not see the blocks at labels from `L` on when
  every block below `L` jumps down.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt

variable {Map : Type → Type} [HoonMap Map]

/-! ## Definitions over all blocks -/

/-- `r` has a definition in `bl`. -/
def Defd (bl : Map Blob) (r : Nat) : Prop := ∃ s, DefSite bl r s

/-- Every register has at most one definition, over all blocks. -/
def DefUniq (bl : Map Blob) : Prop := ∀ r s s', DefSite bl r s → DefSite bl r s' → s = s'

theorem defOnceR_of_defUniq {bl : Map Blob} (h : DefUniq bl) : DefOnceR bl :=
  fun r s s' _ hs _ hs' => h r s s' hs hs'

/-- The destinations of a list of ops. -/
def defsOf (A : List Pole) : List Nat := A.filterMap aliasDst

theorem mem_defsOf {A : List Pole} {r : Nat} : r ∈ defsOf A ↔ ∃ op ∈ A, aliasDst op = some r := by
  simp [defsOf, List.mem_filterMap]

theorem defsOf_append (A B : List Pole) : defsOf (A ++ B) = defsOf A ++ defsOf B := by
  simp [defsOf, List.filterMap_append]

theorem defsOf_cons (op : Pole) (A : List Pole) : defsOf (op :: A) = (aliasDst op).toList ++ defsOf A := by
  cases h : aliasDst op <;> simp [defsOf, List.filterMap_cons, h]

theorem mem_blockDefs {b : Blob} {r : Nat} : r ∈ blockDefs b ↔ r ∈ b.par ∨ r ∈ defsOf b.body := by
  simp [blockDefs, defsOf]

/-- A definition at a place of a block is a member of its definitions. -/
theorem defSite_mem {bl : Map Blob} {r : Nat} :
    ∀ {s : Nat × Option Nat}, DefSite bl r s → ∃ b, HoonMap.get bl s.1 = some b ∧ r ∈ blockDefs b
  | (o, none), ⟨b, hb, hm⟩ => ⟨b, hb, List.mem_append_left _ hm⟩
  | (o, some i), ⟨b, op, hb, hop, hd⟩ =>
    ⟨b, hb, List.mem_append_right _ (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hop, hd⟩)⟩

/-- A member of the definitions of a block is defined at a place of it. -/
theorem defSite_of_mem {bl : Map Blob} {o r : Nat} {b : Blob} (hb : HoonMap.get bl o = some b)
    (h : r ∈ blockDefs b) : ∃ s, s.1 = o ∧ DefSite bl r s := by
  rcases mem_blockDefs.mp h with h | h
  · exact ⟨(o, none), rfl, b, hb, h⟩
  · obtain ⟨op, hop, hd⟩ := mem_defsOf.mp h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hop
    exact ⟨(o, some i), rfl, b, op, hb, hi, hd⟩

theorem defd_iff {bl : Map Blob} {r : Nat} : Defd bl r ↔ ∃ o b, HoonMap.get bl o = some b ∧ r ∈ blockDefs b := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨b, hb, hm⟩ := defSite_mem hs
    exact ⟨s.1, b, hb, hm⟩
  · rintro ⟨o, b, hb, hm⟩
    obtain ⟨s, -, hs⟩ := defSite_of_mem hb hm
    exact ⟨s, hs⟩

theorem mem_allDefs [MapKeys Map] {bl : Map Blob} {r : Nat} : r ∈ allDefs bl ↔ Defd bl r := by
  rw [defd_iff]
  unfold allDefs
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨o, -, h⟩
    cases hb : HoonMap.get bl o with
    | none => rw [hb] at h; simp at h
    | some b => rw [hb] at h; exact ⟨o, b, hb, h⟩
  · rintro ⟨o, b, hb, h⟩
    exact ⟨o, (MapKeys.mem_keys bl o).mpr (by rw [hb]; rfl), by rw [hb]; exact h⟩

/-! ## Liveness -/

/-- The ops `A` read `r` before any of them writes it. -/
def OpsRF : List Pole → Nat → Prop
  | [], _ => False
  | op :: A, r => r ∈ aliasReads op ∨ (aliasDst op ≠ some r ∧ OpsRF A r)

/-- Block `b` reads `r` before it defines it: not a parameter, and read by an
op before any op writes it or by the end when no op writes it. -/
def BlockRF (b : Blob) (r : Nat) : Prop :=
  r ∉ b.par ∧ (OpsRF b.body r ∨ (r ∉ defsOf b.body ∧ r ∈ finRegs b.fin))

/-- **`r` is live at block `k`**: some path from `k` reads `r` before any
definition of it. -/
inductive Live (bl : Map Blob) : Nat → Nat → Prop
  | here {k : Nat} {b : Blob} {r : Nat} : HoonMap.get bl k = some b → BlockRF b r → Live bl k r
  | next {k : Nat} {b : Blob} {j : Jmp} {r : Nat} : HoonMap.get bl k = some b → j ∈ getJmps b.fin →
      Live bl j.there r → r ∉ blockDefs b → Live bl k r

theorem live_iff {bl : Map Blob} {k r : Nat} :
    Live bl k r ↔ ∃ b, HoonMap.get bl k = some b ∧
      (BlockRF b r ∨ ∃ j ∈ getJmps b.fin, Live bl j.there r ∧ r ∉ blockDefs b) := by
  constructor
  · intro h
    cases h with
    | here hb hr => exact ⟨_, hb, Or.inl hr⟩
    | next hb hj hl hd => exact ⟨_, hb, Or.inr ⟨_, hj, hl, hd⟩⟩
  · rintro ⟨b, hb, hr | ⟨j, hj, hl, hd⟩⟩
    · exact Live.here hb hr
    · exact Live.next hb hj hl hd

theorem opsRF_append {A B : List Pole} {r : Nat} :
    OpsRF (A ++ B) r ↔ OpsRF A r ∨ (r ∉ defsOf A ∧ OpsRF B r) := by
  induction A with
  | nil => simp [OpsRF, defsOf]
  | cons op A ih =>
    simp only [List.cons_append, OpsRF, ih, defsOf_cons, List.mem_append]
    cases h : aliasDst op with
    | none => simp [or_assoc]
    | some d =>
      simp only [Option.toList_some, List.mem_singleton, ne_eq, Option.some.injEq]
      by_cases e : d = r
      · subst e; simp
      · simp [e, Ne.symm e, or_assoc]

/-- A read of an op at place `i`, with no write of `r` before it, is a read
before any write. -/
theorem opsRF_of_read : ∀ (A : List Pole) (i : Nat) {r : Nat},
    r ∈ ((A.drop i).head?.map aliasReads).getD [] → r ∉ defsOf (A.take i) → OpsRF A r
  | [], i, r, h, _ => by simp at h
  | op :: A, 0, r, h, _ => by simp at h; exact Or.inl h
  | op :: A, i + 1, r, h, hn => by
    simp only [List.drop_succ_cons, List.take_succ_cons, defsOf_cons, List.mem_append, not_or] at h hn
    refine Or.inr ⟨fun e => hn.1 (by rw [e]; simp), opsRF_of_read A i h hn.2⟩

theorem take_length_eq {α : Type} {l : List α} {i : Nat} (h : i = l.length) : l.take i = l := by
  subst h; exact List.take_length

/-! ## `DefFirst` from liveness -/

/-- Liveness walks back along a path of blocks that do not define `r`. -/
theorem live_back {bl : Map Blob} {r : Nat} :
    ∀ {l : List Nat}, BPath bl l → ∀ {o : Nat} {p : List Nat}, l = o :: p → Live bl o r →
      (∀ o' ∈ p, ∀ b', HoonMap.get bl o' = some b' → r ∉ blockDefs b') → Live bl 0 r := by
  intro l hp
  induction hp with
  | start => intro o p e hl _; cases e; exact hl
  | @step p o b j hp hb hj ih =>
    intro o' p' e hl hn
    cases e
    have hnb : r ∉ blockDefs b := hn o List.mem_cons_self b hb
    exact ih rfl (Live.next hb hj hl hnb) fun o'' ho'' b'' hb'' => hn o'' (List.mem_cons_of_mem _ ho'') b'' hb''

/-- **`DefFirst` from liveness**: no register with a definition is live at
block `0`. -/
theorem defFirst_of_live [MapKeys Map] {bl : Map Blob} (h : ∀ r, Live bl 0 r → ¬ Defd bl r) :
    DefFirst bl := by
  intro o p b hp hb i r hr hd
  refine Classical.byContradiction fun hc => ?_
  simp only [not_or, not_exists, not_and] at hc
  obtain ⟨hpar, htake, hpath⟩ := hc
  have hrf : BlockRF b r := by
    refine ⟨hpar, ?_⟩
    rcases hr with hr | ⟨hi, hr⟩
    · exact Or.inl (opsRF_of_read b.body i hr htake)
    · rw [take_length_eq hi] at htake
      exact Or.inr ⟨htake, hr⟩
  have hl := live_back hp rfl (Live.here hb hrf) fun o' ho' b' hb' hm => hpath o' ho' b' hb' hm
  exact h r hl (mem_allDefs.mp hd)

/-! ## `TrimBr` without trace hints -/

/-- The ops that `+trim-trace-hints` reads as trace hints. -/
def trOp : Pole → Bool
  | Pole.hdp .. | Pole.hde .. | Pole.hmp .. | Pole.hme .. | Pole.hcp .. | Pole.hce .. => true
  | _ => false

/-- No block has a trace hint op. -/
def NoTr (bl : Map Blob) : Prop := ∀ k b, HoonMap.get bl k = some b → ∀ op ∈ b.body, trOp op = false

theorem brOp_nil {op : Pole} (h : trOp op = false) : brOp [] op = some [] := by
  cases op <;> simp_all [trOp, brOp, traceKey]

theorem brBody_nil : ∀ {l : List Pole}, (∀ op ∈ l, trOp op = false) → brBody [] l = some []
  | [], _ => rfl
  | op :: l, h => by
    simp only [brBody, brOp_nil (h op List.mem_cons_self), Option.bind_some]
    exact brBody_nil fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **Without trace hints the empty stack brackets them.** -/
theorem trimBr_of_noTr {bl : Map Blob} (h : NoTr bl) : TrimBr bl (fun _ => []) :=
  ⟨rfl, fun o b _ hb => ⟨[], brBody_nil (h o b hb), fun _ _ => rfl⟩⟩

/-! ## Liveness and blocks that do not change -/

/-- Every block below `L` jumps to labels below its own. -/
def DownBelow (bl : Map Blob) (L : Nat) : Prop :=
  ∀ x b, x < L → HoonMap.get bl x = some b → ∀ j ∈ getJmps b.fin, j.there < x

theorem live_frame_to {bl bl' : Map Blob} {L : Nat} (hd : DownBelow bl L)
    (he : ∀ x, x < L → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (h : Live bl' k r) (hk : k < L) :
    Live bl k r := by
  induction h with
  | @here k b r hb hr => rw [he k hk] at hb; exact Live.here hb hr
  | @next k b j r hb hj _ hd' ih =>
    rw [he k hk] at hb
    exact Live.next hb hj (ih (Nat.lt_trans (hd k b hk hb j hj) hk)) hd'

theorem live_frame_of {bl bl' : Map Blob} {L : Nat} (hd : DownBelow bl L)
    (he : ∀ x, x < L → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (h : Live bl k r) (hk : k < L) :
    Live bl' k r := by
  induction h with
  | @here k b r hb hr => rw [← he k hk] at hb; exact Live.here hb hr
  | @next k b j r hb hj _ hd' ih =>
    have hlt := hd k b hk hb j hj
    rw [← he k hk] at hb
    exact Live.next hb hj (ih (Nat.lt_trans hlt hk)) hd'

/-- **Liveness below `L` sees only the blocks below `L`.** -/
theorem live_frame {bl bl' : Map Blob} {L : Nat} (hd : DownBelow bl L)
    (he : ∀ x, x < L → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (hk : k < L) :
    Live bl' k r ↔ Live bl k r :=
  ⟨fun h => live_frame_to hd he h hk, fun h => live_frame_of hd he h hk⟩

end Raw
end SkaModel
end Formalization
