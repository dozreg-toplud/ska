import lemmas.Ska.CompNestPick

/-!
# The final pass on `FragP`

`finishLF_compDoneP`: on a nomm of `FragP` for `%done` with at most 255
`%6`, the final pass with the whole of `+to-straight` returns code that does
what `+mink` does, on every subject that has the axes the bell's cape says
it has.  The run makes no proxy register (`RunOKP.cnd`), so `+to-straight`
takes its renaming path; `+coerce-lazy` fills the entry block and every lazy
block of the tree from the input registers (`coerceLazyL_spec`), which is
what `RunOKP.sem` asks.  `finishLF_bellContractP`: so the final pass meets
the contract of its bell, and `crash_iffP`: the compiled code crashes
exactly when the nomm does, so it never crashes on a part of the subject
that only a branch not taken reads, at any depth of nesting.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The final pass on `FragP` for `%done` meets the relation at the entry.** -/
theorem finishLF_compDoneP [HoonMapKeys Map] (lib : Lib) {nm : Nomm} (hf : FragP (S := S) CGoal.done nm)
    (hcount : sixCount nm ≤ 255) {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord less bake = some c') : CompDoneOn lib c' nm (CapeAxes less) := by
  rw [finishLF_eq hbake (fun _ _ h1 => (runP_ok (Map := Map) lib hf trivial trivial hcount (by simp [gen0]) rfl h1).cnd)] at h
  unfold finishL at h
  obtain ⟨⟨nex, g4⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  have R := runP_ok (Map := Map) lib hf trivial trivial hcount (by simp [gen0]) rfl h1
  simp only at h
  split at h
  · cases h
  rename_i hargs
  simp only [ne_eq, Decidable.not_not] at hargs
  obtain ⟨⟨nedF, g5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [hbake, List.map_nil] at h
  obtain ⟨⟨u8, g8⟩, h8, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u9, g9⟩, h9, hts⟩ := Option.bind_eq_some_iff.mp h
  have d4 : g4.drop = false := R.ext.2.2.1
  obtain ⟨⟨k5, rfl⟩, l5, dist5, mem5⟩ := needOrdAllocRegs_spec ord g4 _ nedF h5
  simp only at l5 mem5
  obtain ⟨B, fin, hB⟩ : ∃ B fin, HoonMap.get g4.blocks nex.th.there = some ⟨[], B, fin⟩ := by
    rcases R.ent with ⟨b, hb, hp⟩ | e
    · exact ⟨b.body, b.fin, by rw [hb, ← hp]⟩
    · exact e.elim
  have regs4 : ∀ r, NMem nex.laz.sure.ned r → r < g4.re := fun r hr => (R.regs r hr).2
  -- `+coerce-lazy`
  obtain ⟨bo8, dr8, re8, oth8, Froot, Fents⟩ := coerceLazyL_spec h8 d4 dist5 (fun r hr => (mem5 r hr).2)
    ⟨R.dist, fun r hr => Nat.lt_of_lt_of_le (regs4 r hr) l5,
      fun r hr hl => by have := (mem5 r hr).1; have := regs4 r hl; omega⟩
    (fun e he => ⟨(R.eregs e he).1, fun r hr => Nat.lt_of_lt_of_le ((R.eregs e he).2 r hr).2 l5,
      fun r hr hl => by have := (mem5 r hr).1; have := ((R.eregs e he).2 r hl).2; omega⟩)
    (List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨e, he, he'⟩ := List.mem_map.mp hm
      have := (R.labs e he).2.1; omega, R.nodup⟩)
  have d8 : g8.drop = false := dr8.trans d4
  have F9 := front_addOps h9 d8
  obtain ⟨A0, hA0, semA0⟩ := Froot B fin hB
  have hB9 : HoonMap.get g9.blocks nex.th.there = some ⟨[], A0 ++ B, fin⟩ := by
    have := F9.blk _ _ hA0; simpa using this
  have hents : ∀ e ∈ entries nex.laz, ∃ A th, HoonMap.get g4.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
      HoonMap.get g9.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t s,
        CapeAxes less s → FillSem lib O c gul st t nedF k5 e.2.sure A s := by
    intro e he
    obtain ⟨_, lt, th, hth⟩ := R.labs e he
    obtain ⟨A, hA, sA⟩ := Fents e he [] (Termin.hop th) hth
    refine ⟨A, th, hth, ?_, sA⟩
    rw [F9.other _ (by omega), hA, List.append_nil]
  have oth9 : ∀ o, o ≠ nex.th.there → o ∉ (entries nex.laz).map Prod.fst →
      HoonMap.get g9.blocks o = HoonMap.get g4.blocks o := fun o h1 h2 =>
    (F9.other o h1).trans (oth8 o h1 h2)
  -- every block goes down
  have D4 : Down g4.blocks := R.grow.down (fun k b hb => by simp [gen0, HoonMap.get_empty] at hb) (by simp [gen0])
  have D9 : Down g9.blocks := down_of_fins D4 fun k b' hk => by
    by_cases e1 : k = nex.th.there
    · subst e1; rw [hB9] at hk; cases hk; exact ⟨_, hB, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e2
      obtain ⟨A, th, h4, h9', _⟩ := hents e he
      rw [h9'] at hk; cases hk; exact ⟨_, h4, rfl⟩
    · rw [oth9 k e1 e2] at hk; exact ⟨b', hk, rfl⟩
  -- the program with the entry block of the run
  let c1 : Straight Map := ⟨NeedOrd.none, 0, HoonMap.put g9.blocks nex.th.there ⟨[], B, fin⟩⟩
  have hc1o : HoonMap.get c1.blocks nex.th.there = some ⟨[], B, fin⟩ := by simp [c1, HoonMap.get_put]
  have hag : ∀ k, k ≠ nex.th.there → HoonMap.get c1.blocks k = HoonMap.get g9.blocks k := fun k hk => by
    simp [c1, HoonMap.get_put, hk]
  have D1 : Down c1.blocks := by
    intro k b hk
    by_cases e : k = nex.th.there
    · subst e; rw [hc1o] at hk; cases hk; exact D4 _ _ hB
    · rw [hag k e] at hk; exact D9 k b hk
  obtain ⟨_, start, hst, hent⟩ := toStraight_entry hts D9 D1 hag
  rw [hB9] at hst; cases hst
  intro σ O st s args t gul hP hsp
  obtain ⟨R0, hR0, he⟩ := hent lib O st s args t gul hsp
  rw [he]
  have hj : nex.th = jmp0 nex.th.there := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hargs; simp at hargs; subst hargs; rfl
  have ag : AgreeP lib O c1 gul st t nedF gen0 g4 nex.laz s := by
    refine ⟨fun o _ _ hnl => ?_, fun e he => ?_⟩
    · by_cases e : o = nex.th.there
      · subst e; rw [hc1o, hB]
      · rw [hag o e, oth9 o e hnl]
    · obtain ⟨A, th, h4, h9', sA⟩ := hents e he
      refine ⟨A, th, h4, ?_, (sA lib σ O c1 gul st t s hP).mono l5⟩
      rw [hag _ (by have := (R.labs e he).2.1; omega), h9']
  have dj : ∀ x, NMem nedF x → ¬ NMem nex.laz.sure.ned x := fun x hx hl => by
    have := (mem5 x hx).1; have := regs4 x hl; omega
  obtain ⟨SoF, SoC⟩ := semA0 lib σ O c1 gul st t s hP R0 hR0
  rw [pureTone]
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := SoF fo
    rw [hr1]
    have hn1 : HoldsN nedF R1 s := HoldsN.agree nedF (fun x hx => kr1 x (Or.inl hx) (dj x hx)) hR0
    have := R.sem c1 nedF σ O st t gul s ag (fun r hr => (mem5 r hr).1) R1 hh1 hn1
    simp only [GoalSem] at this
    rw [hj, goJ_jmp0 _ _ _ _ hc1o] at this
    exact this
  · rw [SoC fo, R.nec s fo]; rfl

/-- **The final pass meets the contract on `FragP` for `%done`**, when the nomm has at
most 255 `%6`, nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishLF_bellContractP [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragP (S := S) CGoal.done nm) (hcount : sixCount nm ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' := by
  have hc' := finishLF_compDoneP lib hf hcount hbake h
  refine bellContract_of_compDoneOn hok hp hA (fun σ O st s args t gul hs hsp => ?_) N
  rw [hbl] at hs
  exact hc' σ O st s args t gul (fun axe h1 ha => capeAxes_of_fits axe h1 cape data s hn hs ha) hsp

/-- **The compiled code of a `FragP` for `%done` nomm crashes exactly when the nomm
does**, on every subject that has the axes the cape says it has. -/
theorem crash_iffP [HoonMapKeys Map] (lib : Lib) {nm : Nomm} (hf : FragP (S := S) CGoal.done nm) (hcount : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) nm ord less bake = some c') {σ : Type} (O : Oracle σ) (st : σ)
    (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval nm s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval nm s = some v := by
  rw [finishLF_compDoneP lib hf hcount hbake h σ O st s args t gul hP hsp, pureTone]
  constructor
  · cases pureEval nm s <;> simp [toneOf]
  · intro v; cases pureEval nm s <;> simp [toneOf]

/-- `FragP` for `%done` contains `Frag6`. -/
theorem fragP_of_frag6 {nm : Nomm} (h : Frag6 (S := S) nm) : FragP (S := S) CGoal.done nm := by
  rcases h with h | ⟨c, a, b, rfl, hc, ha, hb⟩
  · exact FragP.frag h
  · exact FragP.six (fun z o => FragP.frag (hc z o)) (FragP.frag ha) (FragP.frag hb)

theorem sixCount_frag6 {nm : Nomm} (h : Frag6 (S := S) nm) : sixCount nm ≤ 1 := by
  rcases h with h | ⟨c, a, b, rfl, hc, ha, hb⟩
  · rw [sixCount_frag h]; omega
  · simp only [sixCount, sixCount_frag (hc (jmp0 0) (jmp0 0)), sixCount_frag ha, sixCount_frag hb]; omega

/-- **`finishLF_bellContract6` again, as a case of `FragP`.** -/
theorem finishLF_bellContract6' [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : Frag6 (S := S) nm) {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractP hok hp hA (fragP_of_frag6 hf) (by have := sixCount_frag6 hf; omega) hbl hn hbake h N

end Comp
end SkaModel
end Formalization
