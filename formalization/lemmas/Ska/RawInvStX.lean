import lemmas.Ska.RawInvWholeX
import lemmas.Ska.RawInvEApart
import lemmas.Compiler.OptLinkTotalAlias

/-!
# Raw `+comp` output on `FragX`: the facts of `StInv` and `ReadsIn` through the final pass

README Gaps 14 and 13, track D.  Track H's totality of `+optimize` asks of
its input `StInv ρ L` (`OptLinkTotalInv.lean`: a rank, `Closed`, `ArityOK`,
a block `0`, `TwoNA`, the labels in `L`), `DInvR` (= `OptIn`, proved for
`FragX` in `RawInvEApart.lean` and `RawInvWholeX.lean`) and, since
`not_aliasRet`, `ReadsIn nargs` (`OptLinkTotalAlias.lean`).  Here, for the
output of `+to-straight` on the renaming path (directly, or through the
unproxied blocks of the map path):

* `Closed` and the block `0` need nothing of the raw blocks: `+chase`
  fails on a jump to a label with no block, and lands on a block that is
  not bypassable, which the fold keeps (`renameBlocks_spec`); the entry
  is always kept at `0`.
* `ArityOK` and `TwoNA` come from the raw blocks: a chased jump is the jump
  itself or the hop of a block it passed (`chase_rawR`), the target's
  parameters are renamed, so their number is kept; on a two-way end the
  chase runs in branch mode, which passes only hops without arguments
  (`chase_nil`, `chaseFin_two`).
* `ReadsIn`: a register read on a reachable block and defined nowhere is
  live at `0` (`readsIn_of_live`), so it is the image of a register live
  at the raw entry, which the prologue makes an input (`stOut_ren`, the
  liveness part of `optIn_renOutR`).

`stOut_ren` is the core, `stIn_toStraight_prep` (n-ary) and `stIn_prepN`
(through the unproxied blocks) the forms the two final passes use.  The
prologues keep parameters and ends (`arityOK_prep`, `twoNA_prep`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]

/-! ## The prologues keep parameters and ends -/

theorem arityOK_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') (h : Compiler.ArityOK bl) :
    Compiler.ArityOK bl' := by
  intro o b' j b2' ho hj hb2
  obtain ⟨b, hb, rfl⟩ := get_prep hP ho
  obtain ⟨b2, hb2', rfl⟩ := get_prep hP hb2
  exact h o b j b2 hb hj hb2'

theorem twoNA_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') (h : Compiler.TwoNA bl) :
    Compiler.TwoNA bl' := by
  intro o b' j ho h2 hj
  obtain ⟨b, hb, rfl⟩ := get_prep hP ho
  exact h o b j hb h2 hj

/-! ## `ReadsIn` from liveness at `0` -/

theorem defsOf_take {A : List Pole} {i r : Nat} (h : r ∈ defsOf (A.take i)) : r ∈ defsOf A :=
  ((List.take_sublist i A).filterMap aliasDst).subset h

/-- **`ReadsIn` from liveness**: if every register live at `0` that has no
definition is below `n`, every register a reachable block reads is defined
or below `n`. -/
theorem readsIn_of_live [MapKeys Map] {bl : Map Blob} {n : Nat} (h : ∀ r, Live bl 0 r → ¬ Defd bl r → r < n) :
    Compiler.ReadsIn n bl := by
  intro o b i r hr hb hra
  by_cases hd : r ∈ allDefs bl
  · exact Or.inl hd
  · right
    have nd : ¬ Defd bl r := fun d => hd (mem_allDefs.mpr d)
    have nb : r ∉ blockDefs b := fun e => nd (defd_iff.mpr ⟨o, b, hb, e⟩)
    obtain ⟨p, hp⟩ := Opt.awi_reach_bpath hr
    have hrf : BlockRF b r := by
      refine ⟨fun e => nb (mem_blockDefs.mpr (Or.inl e)), ?_⟩
      rcases hra with hra | ⟨-, hra⟩
      · exact Or.inl (opsRF_of_read b.body i hra fun e => nb (mem_blockDefs.mpr (Or.inr (defsOf_take e))))
      · exact Or.inr ⟨fun e => nb (mem_blockDefs.mpr (Or.inr e)), hra⟩
    exact h r (live_back hp rfl (Live.here hb hrf) fun o' _ b' hb' hm => nd (defd_iff.mpr ⟨o', b', hb', hm⟩)) nd

/-! ## The chase in branch mode -/

section Chase
variable {blocks bs : Map Blob} {o : Nat}

/-- **In branch mode a jump without arguments is chased to one without
arguments**: it passes only hops without arguments. -/
theorem chase_nil {ρ : Nat → Nat} (hd : DownRk ρ blocks) (hbs : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    (hbo : HoonMap.get bs o = Option.none) :
    ∀ n (j j' : Jmp), ρ j.there < n → 1 ≤ j.there → chase bs true j = some j' → j.args = [] → j'.args = []
  | 0, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, j, j', hn, h1, hc, ha => by
    rw [chase] at hc
    have ho : j.there ≠ o := fun e => by rw [e, hbo] at hc; simp at hc
    rw [hbs _ (by omega) ho] at hc
    cases hb : HoonMap.get blocks j.there with
    | none => rw [hb] at hc; simp at hc
    | some b =>
      rw [hb] at hc
      simp only [Option.bind_eq_bind, Option.bind_some] at hc
      split at hc
      · rename_i t heq
        by_cases hby : bypassable true b = true
        · rw [if_pos hby, if_pos ha] at hc
          have hdt := (hd _ _ hb).2 t (by simp [finJumps, heq])
          obtain ⟨t', rfl⟩ := bypassable_shape hby
          simp only [Termin.hop.injEq] at heq
          subst t'
          have ht : t.args = [] := by simpa [bypassable] using hby
          exact chase_nil hd hbs hbo n t j' (by omega) hdt.1 hc ht
        · rw [if_neg hby] at hc
          cases hc; exact ha
      · cases hc; exact ha

end Chase

/-- The jumps of a two-way end after `+chase-fin` are chased in branch mode. -/
theorem chaseFin_two {bs : Map Blob} {ren : Nat → Nat} {fin fin' : Termin} (hc : chaseFin bs ren fin = some fin')
    (h2 : Compiler.twoWay fin' = true) : Compiler.twoWay fin = true ∧
      ∀ j'' ∈ getJmps fin', ∃ j ∈ getJmps fin, ∃ j', chase bs true j = some j' ∧ j'' = renJmp ren j' := by
  cases fin with
  | clq s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    refine ⟨rfl, fun j'' hm => ?_⟩
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], o'', ho, rfl⟩
  | eqq l q z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    refine ⟨rfl, fun j'' hm => ?_⟩
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], o'', ho, rfl⟩
  | brn s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    refine ⟨rfl, fun j'' hm => ?_⟩
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], o'', ho, rfl⟩
  | brz s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    refine ⟨rfl, fun j'' hm => ?_⟩
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], o'', ho, rfl⟩
  | hop t =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨t', -, rfl⟩ := hc
    simp [Compiler.twoWay] at h2
  | jmp a v => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [Compiler.twoWay] at h2
  | jmf a v n => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [Compiler.twoWay] at h2
  | jsp a s => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [Compiler.twoWay] at h2
  | jsf a s n => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [Compiler.twoWay] at h2
  | don s => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [Compiler.twoWay] at h2
  | bom x =>
    cases x with
    | none => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [Compiler.twoWay] at h2
    | some x =>
      simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨j, -, rfl⟩ := hc
      simp [Compiler.twoWay] at h2
  | lti n s z o' => simp [chaseFin] at hc

/-- A block not bypassable in some mode is not bypassable in branch mode. -/
theorem bypassable_true_of {br : Bool} {b : Blob} (h : bypassable br b = false) : bypassable true b = false := by
  rcases b with ⟨par, body, fin⟩
  cases br <;> cases par <;> cases body <;> cases fin <;> simp_all [bypassable]

/-! ## The core -/

section Out
variable [HoonMapKeys Map]

/-- **The facts of `StInv` after the renaming path, and the liveness at
`0`**, for any output map whose blocks are the kept blocks of `bs` (`hnew`,
`hnew'`): `Closed` and the block `0` from the success of the chase alone,
`ArityOK` and `TwoNA` from the raw blocks, and every register live at `0`
the image of one the raw entry reads first, which `hl` makes a member of
`ned`. -/
theorem stOut_ren {blocks : Map Blob} {ned : Need} {o : Nat} {start : Blob}
    (hst : HoonMap.get blocks o = some start) {bs : Map Blob} (hbs0 : HoonMap.get bs 0 = some start)
    (hbso : HoonMap.get bs o = Option.none) (hbsk : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    {ren : Nat → Nat} (hi : Inj ren) (hsurj : ∀ r', ∃ r, ren r = r') {new : Map Blob}
    (hnew : ∀ k b', HoonMap.get new k = some b' → ∃ b, HoonMap.get bs k = some b ∧ keepBlock bs ren k b = some (some b'))
    (hnew' : ∀ k b, HoonMap.get bs k = some b → ∃ kb, keepBlock bs ren k b = some kb ∧ HoonMap.get new k = kb)
    {ρ : Nat → Nat} (hd : DownRk ρ blocks) (har : Compiler.ArityOK blocks) (htw : Compiler.TwoNA blocks)
    (hl : ∀ r, Live blocks o r → NMem ned r) :
    Compiler.Closed new ∧ Compiler.ArityOK new ∧ (HoonMap.get new 0).isSome ∧ Compiler.TwoNA new ∧
      ∀ r', Live new 0 r' → ∃ r, ren r = r' ∧ NMem ned r := by
  have ho1 : 1 ≤ o := (hd o start hst).1
  -- the output blocks
  have OUT : ∀ k b', HoonMap.get new k = some b' → ∃ b fin', HoonMap.get blocks (labOf o k) = some b ∧
      chaseFin bs ren b.fin = some fin' ∧ b' = renB ren b fin' ∧ (k ≠ 0 → k ≠ o) := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := hnew k b' hk
    simp only [keepBlock] at hkb
    split at hkb
    · cases hkb
    obtain ⟨fin', hf, e⟩ := Option.map_eq_some_iff.mp hkb
    simp only [Option.some.injEq] at e
    by_cases k0 : k = 0
    · subst k0; rw [hbs0] at hb; cases hb
      exact ⟨start, fin', by simp [labOf, hst], hf, e.symm, fun h => absurd rfl h⟩
    · have kno : k ≠ o := fun ek => by rw [ek, hbso] at hb; cases hb
      rw [hbsk k k0 kno] at hb
      exact ⟨b, fin', by simp [labOf, k0, hb], hf, e.symm, fun _ => kno⟩
  have rjump : ∀ k b, HoonMap.get blocks k = some b → ∀ j ∈ getJmps b.fin, 1 ≤ j.there ∧ ρ j.there < ρ k :=
    fun k b hb j hj => (hd k b hb).2 j (by rw [← getJmps_eq]; exact hj)
  have CF : ∀ k b' , HoonMap.get new k = some b' → ∃ b fin', HoonMap.get blocks (labOf o k) = some b ∧
      chaseFin bs ren b.fin = some fin' ∧ b' = renB ren b fin' ∧
      (∀ n s z o', fin' ≠ Termin.lti n s z o') ∧
      (∀ j'' ∈ getJmps fin', ∃ j ∈ getJmps b.fin, ∃ br j', chase bs br j = some j' ∧ j'' = renJmp ren j') ∧
      (∀ r, ren r ∈ finRegs fin' → r ∈ finRegs b.fin ∨ ∃ j ∈ getJmps b.fin, Live blocks j.there r) := by
    intro k b' hk
    obtain ⟨b, fin', hb, hf, rfl, -⟩ := OUT k b' hk
    obtain ⟨n1, n2, n3⟩ := chaseFin_rawR hd hbsk hbso hi (fun j hj => (rjump _ b hb j hj).1) hf
    exact ⟨b, fin', hb, hf, rfl, n1, n2, n3⟩
  have CR := fun (j : Jmp) br j' (h1 : 1 ≤ j.there) (h : chase bs br j = some j') =>
    chase_rawR hd hbsk hbso (ρ j.there + 1) j br j' (Nat.lt_succ_self _) h1 h
  -- jumps of the output
  have JO : ∀ k b' j'', HoonMap.get new k = some b' → j'' ∈ getJmps b'.fin →
      ∃ b j br j', HoonMap.get blocks (labOf o k) = some b ∧ j ∈ getJmps b.fin ∧ chase bs br j = some j' ∧
        j'' = renJmp ren j' := by
    intro k b' j'' hk hj
    obtain ⟨b, fin', hb, -, rfl, -, n2, -⟩ := CF k b' hk
    obtain ⟨j, hjm, br, j', hc, rfl⟩ := n2 j'' hj
    exact ⟨b, j, br, j', hb, hjm, hc, rfl⟩
  -- a chased jump lands on a block of the output, with the raw parameters renamed
  have KT : ∀ (j : Jmp) br j', 1 ≤ j.there → chase bs br j = some j' →
      ∃ b2', HoonMap.get new j'.there = some b2' ∧ ∃ bt, HoonMap.get blocks j'.there = some bt ∧
        b2'.par.length = bt.par.length := by
    intro j br j' h1 hc
    obtain ⟨-, hno, h1', ⟨bt, hbt, hby⟩, -⟩ := CR j br j' h1 hc
    have hbs' : HoonMap.get bs j'.there = some bt := by rw [hbsk _ (by omega) hno]; exact hbt
    obtain ⟨kb, hkb, hg⟩ := hnew' _ bt hbs'
    have hby' : bypassable true bt = false := bypassable_true_of hby
    have hkb' : keepBlock bs ren j'.there bt =
        (chaseFin bs ren bt.fin).map fun fin => some ⟨bt.par.map ren, bt.body.map (renPole ren), fin⟩ := by
      simp only [keepBlock, hby', Bool.false_eq_true, and_false, if_false]
    rw [hkb'] at hkb
    obtain ⟨fin', -, rfl⟩ := Option.map_eq_some_iff.mp hkb
    exact ⟨_, hg, bt, hbt, by simp⟩
  -- liveness of the output is raw liveness
  have LO : ∀ k r', Live new k r' → ∃ r, ren r = r' ∧ Live blocks (labOf o k) r := by
    intro k r' hlv
    induction hlv with
    | @here k b' r' hk hr =>
      obtain ⟨b, fin', hb, -, rfl, -, -, n3⟩ := CF k b' hk
      obtain ⟨r, rfl⟩ := hsurj r'
      refine ⟨r, rfl, ?_⟩
      obtain ⟨hpar, hr⟩ := hr
      simp only [renB] at hpar hr
      have hpar' : r ∉ b.par := fun e => hpar ((mem_map_inj hi).mpr e)
      rcases hr with hr | ⟨hnd, hf⟩
      · exact Live.here hb ⟨hpar', Or.inl ((opsRF_ren hi b.body).mp hr)⟩
      · rw [defsOf_ren, mem_map_inj hi] at hnd
        rcases n3 r hf with e | ⟨j, hj, hlj⟩
        · exact Live.here hb ⟨hpar', Or.inr ⟨hnd, e⟩⟩
        · exact Live.next hb hj hlj (fun e => by
            rcases mem_blockDefs.mp e with e | e
            · exact hpar' e
            · exact hnd e)
    | @next k b' j'' r' hk hj _ hnb ih =>
      obtain ⟨r, rfl, hl'⟩ := ih
      obtain ⟨b, j, br, j', hb, hjm, hc, rfl⟩ := JO k b' j'' hk hj
      obtain ⟨b0, fin', hb0, -, e0, -⟩ := OUT k b' hk
      rw [hb] at hb0; cases hb0
      have hj1 := (rjump _ b hb j hjm).1
      obtain ⟨-, -, h1', -, hlv, -, -, -, -⟩ := CR j br j' hj1 hc
      simp only [renJmp, labOf_pos h1'] at hl'
      refine ⟨r, rfl, Live.next hb hjm (hlv r hl') fun e => hnb ?_⟩
      rw [e0, blockDefs_renB]; exact (mem_map_inj hi).mpr e
  refine ⟨fun k b' j'' hk hj => ?_, fun k b' j'' b2 hk hj hb2 => ?_, ?_, fun k b' j'' hk h2 hj => ?_,
    fun r' hlv => ?_⟩
  · -- `Closed`
    obtain ⟨b, j, br, j', hb, hjm, hc, rfl⟩ := JO k b' j'' hk hj
    obtain ⟨b2', hg, -⟩ := KT j br j' (rjump _ b hb j hjm).1 hc
    simp only [renJmp, hg]; rfl
  · -- `ArityOK`
    obtain ⟨b, j, br, j', hb, hjm, hc, rfl⟩ := JO k b' j'' hk hj
    obtain ⟨b2', hg, bt, hbt, hlen⟩ := KT j br j' (rjump _ b hb j hjm).1 hc
    simp only [renJmp] at hb2 ⊢
    rw [hg] at hb2; cases hb2
    rw [List.length_map, hlen]
    obtain ⟨-, -, -, -, -, -, hor, -, -⟩ := CR j br j' (rjump _ b hb j hjm).1 hc
    rcases hor with e | ⟨m, bm, -, hbm, hjm'⟩
    · rw [e] at hbt ⊢; exact har _ b j bt hb hjm hbt
    · exact har m bm j' bt hbm hjm' hbt
  · -- the block `0`
    obtain ⟨kb, hkb, hg⟩ := hnew' 0 start hbs0
    have hkb' : keepBlock bs ren 0 start =
        (chaseFin bs ren start.fin).map fun fin => some ⟨start.par.map ren, start.body.map (renPole ren), fin⟩ := by
      simp only [keepBlock, ne_eq, not_true_eq_false, false_and, if_false]
    rw [hkb'] at hkb
    obtain ⟨fin', -, rfl⟩ := Option.map_eq_some_iff.mp hkb
    rw [hg]; rfl
  · -- `TwoNA`
    obtain ⟨b, fin', hb, hf, rfl, -⟩ := OUT k b' hk
    simp only [renB] at h2 hj
    obtain ⟨hb2, hj2⟩ := chaseFin_two hf h2
    obtain ⟨j, hjm, j', hc, rfl⟩ := hj2 j'' hj
    have hja := htw _ b j hb hb2 hjm
    have := chase_nil hd hbsk hbso (ρ j.there + 1) j j' (Nat.lt_succ_self _) (rjump _ b hb j hjm).1 hc hja
    simp [renJmp, this]
  · -- liveness at `0`
    obtain ⟨r, rfl, hl0⟩ := LO 0 r' hlv
    simp only [labOf, if_true] at hl0
    exact ⟨r, rfl, hl r hl0⟩

/-! ## The two final passes -/

theorem countArgs_flatten : ∀ ned : Need, countArgs (needToOrd ned) = (flattenNeed ned).length
  | Need.none => rfl
  | Need.this _ => rfl
  | Need.pair p q => by
    simp only [needToOrd, countArgs, flattenNeed, List.length_append, countArgs_flatten p, countArgs_flatten q]
  | Need.both _ h t => by
    simp only [needToOrd, countArgs, flattenNeed, List.length_cons, List.length_append, countArgs_flatten h,
      countArgs_flatten t]

/-- The renaming of a run of inputs takes each input below their number. -/
theorem renReg_lt_of_run {ned : Need} (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true)
    {r : Nat} (hr : NMem ned r) :
    renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length r < (flattenNeed ned).length := by
  have hm := (mem_flatten ned r).mpr hr
  rw [isRun_iff] at hrun
  generalize (flattenNeed ned).headD 0 = r0 at hrun ⊢
  generalize ens : flattenNeed ned = ins at hrun hm ⊢
  rw [hrun] at hm
  simp only [List.mem_range'_1] at hm
  simp only [renReg]
  split
  · omega
  · split
    · omega
    · omega

/-- **The facts of `StInv` and the liveness at `0` after `+to-straight`
on the renaming path**, for blocks that are raw blocks with ops in front
(the n-ary final pass): the hypotheses of `optIn_toStraight_prep` that
speak of liveness, plus `ArityOK` and `TwoNA` of the raw blocks. -/
theorem stIn_toStraight_prep {bl bl' : Map Blob} {P : Nat → List Pole} {K : Nat → Nat → Prop}
    {ned : Need} {o : Nat} {c' : Straight Map}
    (hP : Prep P bl bl') (hrk : DownRk (upRk bl) bl) (har : Compiler.ArityOK bl) (htw : Compiler.TwoNA bl)
    (hK : ∀ k r, K k r → r ∈ defsOf (P k)) (hl : ∀ r, ¬ LiveK bl K o r)
    (hX : ∀ k r, OpsRF (P k) r → NMem ned r) (h : toStraight bl' ned o = some c') :
    Compiler.Closed c'.blocks ∧ Compiler.ArityOK c'.blocks ∧ (HoonMap.get c'.blocks 0).isSome ∧
      Compiler.TwoNA c'.blocks ∧ ∀ r', Live c'.blocks 0 r' → r' < c'.nargs := by
  have e : upRk bl' = upRk bl := funext (upRk_prep hP)
  have rk' : DownRk (upRk bl') bl' := by rw [e]; exact downRk_prep hP hrk
  unfold toStraight at h
  simp only at h
  split at h
  · cases h
  rename_i hrun
  have hrun' : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true := by simpa using hrun
  cases hst : HoonMap.get bl' o with
  | none => rw [hst] at h; cases h
  | some start =>
  rw [hst, Option.bind_some] at h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only
  have hi : Inj (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length) := renReg_inj _ _
  have hsurj := renReg_surj ((flattenNeed ned).headD 0) (flattenNeed ned).length
  generalize hbs : HoonMap.put (HoonMap.del bl' o) 0 start = bs at hnew
  have ho1 : 1 ≤ o := (rk' o start hst).1
  have hbs0 : HoonMap.get bs 0 = some start := by simp [← hbs, HoonMap.get_put]
  have hbso : HoonMap.get bs o = Option.none := by
    simp [← hbs, HoonMap.get_put, HoonMap.get_del, show o ≠ 0 by omega]
  have hbsk : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get bl' k := fun k h0 hk => by
    simp [← hbs, HoonMap.get_put, HoonMap.get_del, h0, hk]
  obtain ⟨c1, c2, c3, c4, c5⟩ := stOut_ren hst hbs0 hbso hbsk hi hsurj (fun k b' hk => renameBlocks_get hnew hk)
    (renameBlocks_spec hnew) rk' (arityOK_prep hP har) (twoNA_prep hP htw)
    (fun r hr => live_entry_of_prep hP hK hl hX hr)
  refine ⟨c1, c2, c3, c4, fun r' hlv => ?_⟩
  obtain ⟨r, rfl, hr⟩ := c5 r' hlv
  rw [countArgs_flatten]
  exact renReg_lt_of_run hrun' hr

/-- **`stIn_toStraight_prep` for any output of the renaming path** (the
whole-subject final pass, through the unproxied blocks): the hypotheses of
`optIn_prepN` that speak of liveness, plus `ArityOK` and `TwoNA` of the raw
blocks and the converse `hnew'` of `hnew`. -/
theorem stIn_prepN {bl bl' : Map Blob} {P : Nat → List Pole} {K : Nat → Nat → Prop}
    {ned : Need} {o : Nat}
    (hP : Prep P bl bl') (hrk : DownRk (upRk bl) bl) (har : Compiler.ArityOK bl) (htw : Compiler.TwoNA bl)
    (hK : ∀ k r, K k r → r ∈ defsOf (P k)) (hl : ∀ r, ¬ LiveK bl K o r)
    (hX : ∀ k r, OpsRF (P k) r → NMem ned r)
    {start : Blob} (hst : HoonMap.get bl' o = some start) {bs : Map Blob} (hbs0 : HoonMap.get bs 0 = some start)
    (hbso : HoonMap.get bs o = Option.none) (hbsk : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get bl' k)
    {ren : Nat → Nat} (hi : Inj ren) (hsurj : ∀ r', ∃ r, ren r = r') {new : Map Blob}
    (hnew : ∀ k b', HoonMap.get new k = some b' → ∃ b, HoonMap.get bs k = some b ∧ keepBlock bs ren k b = some (some b'))
    (hnew' : ∀ k b, HoonMap.get bs k = some b → ∃ kb, keepBlock bs ren k b = some kb ∧ HoonMap.get new k = kb) :
    Compiler.Closed new ∧ Compiler.ArityOK new ∧ (HoonMap.get new 0).isSome ∧ Compiler.TwoNA new ∧
      ∀ r', Live new 0 r' → ∃ r, ren r = r' ∧ NMem ned r := by
  have e : upRk bl' = upRk bl := funext (upRk_prep hP)
  have rk' : DownRk (upRk bl') bl' := by rw [e]; exact downRk_prep hP hrk
  exact stOut_ren hst hbs0 hbso hbsk hi hsurj hnew hnew' rk' (arityOK_prep hP har) (twoNA_prep hP htw)
    (fun r hr => live_entry_of_prep hP hK hl hX hr)

end Out

/-! ## The top theorems, given the run's raw facts -/

section Top
variable {S : Type} [HoonSet S] [HoonMapKeys Map]

/-- **What the run-level induction owes** (open, checked by `stB` on all of
`enumX`): the raw blocks of the top run of `nm` meet `ArityOK` and `TwoNA`. -/
def RunAT (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ nex g1, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
    Compiler.ArityOK g1.blocks ∧ Compiler.TwoNA g1.blocks

variable [MapKeys Map]

/-- **The facts of `StInv` and the liveness at `0` of the n-ary code of
`FragX`**, given `RunAT`.  Generated from the text of `optIn_finishLFX_of`
with `lazOK_run` for its hypothesis and `stIn_toStraight_prep` for the
final call. -/
theorem stIn_finishLFX_of {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) (hat : RunAT S Map nm)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') :
    Compiler.Closed c'.blocks ∧ Compiler.ArityOK c'.blocks ∧ (HoonMap.get c'.blocks 0).isSome ∧
      Compiler.TwoNA c'.blocks ∧ ∀ r', Live c'.blocks 0 r' → r' < c'.nargs := by
  have O : ∀ {nex : NextL S} {g1 : Comp.Gen Map},
      runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
      RunOKP (Map := Map) lib0 nm (CGoal.done : CGoal S) gen0 g1 nex :=
    fun h1 => (runX_ok lib0 hf).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
  rw [finishLF_eq hbake (fun _ _ h1 => (O h1).cnd)] at h
  unfold finishL at h
  obtain ⟨⟨nex, g1⟩, h1, hA⟩ := Option.bind_eq_some_iff.mp h
  simp only at hA
  split at hA
  · cases hA
  obtain ⟨⟨nedF, g2⟩, h2, hB⟩ := Option.bind_eq_some_iff.mp hA
  rw [hbake] at hB
  simp only [List.map_nil] at hB
  obtain ⟨⟨u3, g3⟩, h3, hC⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨⟨u4, g4⟩, h4, hT⟩ := Option.bind_eq_some_iff.mp hC
  have R := O h1
  obtain ⟨LA, LD⟩ := lazOK_run hf hc h1
  -- the run
  obtain ⟨S1, -, -, -, L1⟩ := runX_rawIHX_up (S := S) (Map := Map) hf CGoal.done [] gen0 g1 nex (fun _ _ => False)
    (KVan.none _) sip_gen0X trivial trivial trivial trivial (fun _ _ e => e) hc trivial h1
  have hl : ∀ r, ¬ LiveK g1.blocks (lazK nex.th.there nex.laz) nex.th.there r := fun r hl' =>
    L1 r (hl'.mono fun x y h => h.elim False.elim id)
  have haa : ArgsAboveR (upRk g1.blocks) g1.blocks := argsAboveR_upRk_of_xup S1.x
  have hrk : DownRk (upRk g1.blocks) g1.blocks :=
    downRk_of_growU R.grow (fun k => by simp [gen0, HoonMap.get_empty]) (by simp [gen0])
  -- the input need
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  subst e2
  have l2' : g1.re ≤ k2 := l2
  -- `+coerce-lazy`
  have I0 : CoI (Xup (Map := Map)) (upRk g1.blocks) g1.bo nedF k2 ((nex.th.there, nex.laz) :: entries nex.laz)
      { g1 with re := k2 } := by
    refine ⟨sip_reg S1 l2, Nat.le_refl _, fun r hr => ⟨(mF r hr).2, fun d => ?_⟩, LA, fun e he => ?_⟩
    · have := S1.defd_lt d; have := (mF r hr).1; omega
    · have rg : ∀ r, NMem e.2.sure.ned r → r < g1.re := fun r hr => by
        rcases List.mem_cons.mp he with rfl | he'
        · exact (R.regs r hr).2
        · exact ((R.eregs e he').2 r hr).2
      refine ⟨?_, ?_, fun r hr => ⟨by have := rg r hr; omega, fun m => ?_, LD e he r hr⟩⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · rcases R.ent with ⟨b, hb, -, -⟩ | hj
          · exact ⟨b, hb⟩
          · exact hj.elim
        · obtain ⟨-, -, th, hb⟩ := R.labs e he'
          exact ⟨_, hb⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · exact R.dist
        · exact (R.eregs e he').1
      · have := rg r hr; have := (mF r m).1; omega
  obtain ⟨I3, P, pP, kP, rP, -⟩ := coerceLazyL_prepI (S := S) (Map := Map)
    (CoI (Xup (Map := Map)) (upRk g1.blocks) g1.bo nedF k2)
    (fun _ _ _ _ _ _ hI hs => coI_step hI hs) I0 h3
  -- the empty bake
  obtain ⟨S4, b4, hb4, e4, -, -⟩ := sip_addOps I3.1 (opsOK_nil g3) h4
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k => by
    rw [e4]
    by_cases e : k = nex.th.there
    · subst e; rw [get_put_self, hb4, pre_nil]
    · rw [get_put_ne e]
  have pP4 : Prep P g1.blocks g4.blocks := fun k => by rw [get4 k]; exact pP k
  exact stIn_toStraight_prep (K := lazK nex.th.there nex.laz) pP4 hrk (hat nex g1 h1).1 (hat nex g1 h1).2
    (fun k r hk => by obtain ⟨e, he, rfl, hr⟩ := hk; exact kP e he r hr) hl rP hT

/-- **The same for the whole-subject code of `FragX`.**  Generated from the
text of `optIn_finishLUX`: the hop block of `+kerf` goes to the entry, which
has no parameter (`Entry`), and `stIn_prepN` replaces `optIn_prepN`, with
the converse of the fold from `renameBlocks_ren`. -/
theorem stIn_finishLUX {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) (hat : RunAT S Map nm)
    {c' : Straight Map} (h : finishLU (S := S) (Map := Map) nm = some c') :
    Compiler.Closed c'.blocks ∧ Compiler.ArityOK c'.blocks ∧ (HoonMap.get c'.blocks 0).isSome ∧
      Compiler.TwoNA c'.blocks ∧ ∀ r', Live c'.blocks 0 r' → r' < c'.nargs := by
  unfold finishLU at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o, sub⟩, g7⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  have R : RunOKP (Map := Map) lib0 nm (CGoal.done : CGoal S) gen0 g1 nex :=
    (runX_ok lib0 hf).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
  obtain ⟨LA, LD⟩ := lazOK_run hf hc h1
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := runX_rawIHX_up (S := S) (Map := Map) hf CGoal.done [] gen0 g1 nex
    (fun _ _ => False) (KVan.none _) sip_gen0X trivial trivial trivial trivial (fun _ _ e => e) hc trivial h1
  have hl1 : ∀ r, ¬ LiveK g1.blocks (lazK nex.th.there nex.laz) nex.th.there r := fun r hl' =>
    L1 r (hl'.mono fun x y h => h.elim False.elim id)
  have hcnd : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by
    rw [R.cnd]; simp [gen0, HoonMap.get_empty]
  -- `+kerf`: the hop block
  simp only [kerf] at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  have gee : ge = g1.emitted ⟨[], [], Termin.hop nex.th⟩ := by
    have he' := he
    rw [emit_apply] at he'
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    exact he'.2.symm
  obtain ⟨Se, eo, ee, qe, boe⟩ := sip_emit S1 (emitOK_hop a1 hi1) he
  obtain ⟨r, g3, h3, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨e2o, e2s⟩, e2g⟩ := h2
  subst e2o e2s e2g eo
  rw [kern_eq] at h3
  obtain ⟨r0, g5, h5, h3⟩ := bind_some h3
  have c5 : g5.cond = g1.cond := by
    rw [re_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    rw [← h5.2, gee]; rfl
  obtain ⟨S5, er0, q5, b5, o5⟩ := sip_re Se h5
  subst er0
  obtain ⟨g6, g6', h6, h3⟩ := bind_some h3
  rw [get_apply] at h6
  simp only [Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rw [S5.drop] at h3
  simp only [Bool.false_eq_true, if_false] at h3
  obtain ⟨⟨⟩, g7', h7, h3⟩ := bind_some h3
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨e3r, e3g⟩ := h3
  subst e3r
  rw [walkLazy_flat, e3g] at h7
  have h7' : walkList (kernGate ge.re g1.bo) ((g1.bo, nex.laz) :: wentries nex.laz) g5 = some ((), g3) := by
    simp only [walkList]; exact h7
  -- the state before the walk
  have hbo5 : HoonMap.get g5.blocks g1.bo = some ⟨[], [], Termin.hop nex.th⟩ := by rw [b5, ee]; exact get_put_self
  have below5 : ∀ k, k < g1.bo → HoonMap.get g5.blocks k = HoonMap.get g1.blocks k := fun k hk => by
    rw [b5, ee, get_put_ne (by omega)]
  have dd5 : ∀ y, Defd g5.blocks y ↔ Defd g1.blocks y := fun y => by
    rw [b5, ee, defd_put (S1.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have I0 : KI (S := S) Xup (upRk g1.blocks) g1.bo ge.re ((g1.bo, nex.laz) :: wentries nex.laz) g5 := by
    refine ⟨S5, by omega, fun k v hv => ?_, fun y _ => by rw [c5, hcnd], fun d => ?_, ?_, fun e he => ?_⟩
    · rw [c5, hcnd] at hv; cases hv
    · have := S1.defd_lt ((dd5 _).mp d); omega
    · have LA' := List.pairwise_cons.mp LA
      exact needsApart_perm ((wentries_perm nex.laz).symm.cons _) (List.pairwise_cons.mpr ⟨LA'.1, LA'.2⟩)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨⟨_, hbo5⟩, R.dist, fun y hy => ⟨by have := (R.regs y hy).2; omega,
          fun d => LD (nex.th.there, nex.laz) List.mem_cons_self y hy ((dd5 y).mp d)⟩⟩
      · have hm : e ∈ entries nex.laz := (wentries_perm nex.laz).mem_iff.mp he'
        obtain ⟨-, lt, th', hb⟩ := R.labs e hm
        exact ⟨⟨_, by rw [below5 _ (by omega)]; exact hb⟩, (R.eregs e hm).1, fun y hy =>
          ⟨by have := ((R.eregs e hm).2 y hy).2; omega,
            fun d => LD e (List.mem_cons_of_mem _ hm) y hy ((dd5 y).mp d)⟩⟩
  obtain ⟨I7, P, pP, kP, rP, -⟩ := kernList_prep ge.re g1.bo _ g5 g3 I0 h7'
  obtain ⟨S7, -, ck7, dk7, ns7, -, -⟩ := I7
  -- the final pass: the map path is the renaming path of the unproxied blocks
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at h
  simp only [flattenNeed, List.headD, List.length] at h
  obtain ⟨start, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  generalize hu : (fun r => if hasProxies g3.cond then unproxy g3.cond r else r) = u
  have uN : ∀ x, HoonMap.get g3.cond x = Option.none → u x = x := fun x hx => by
    rw [← hu]; simp only; split
    · exact unproxy_none hx
    · rfl
  have uK : ∀ x v, HoonMap.get g3.cond x = some v → u x = v.1 := fun x v hx => by
    have hp : hasProxies g3.cond = true := by
      unfold hasProxies
      cases e : HoonMapKeys.keys g3.cond with
      | nil =>
        have := (HoonMapKeys.mem_keys g3.cond x).mpr (by simp [hx])
        rw [e] at this; cases this
      | cons _ _ => rfl
    rw [← hu]; simp only [hp, if_true, unproxy, hx]
  have uLow : ∀ x, x ≤ ge.re → u x = x := fun x hx => uN x (by
    cases e : HoonMap.get g3.cond x with
    | none => rfl
    | some v => have := (ck7 x v e).1; omega)
  have uD : ∀ x, Defd g3.blocks x → u x = x := fun x d => uN x (dk7 x d)
  have hpr : proxRen g3.cond (hasProxies g3.cond) (renReg ge.re 1) = renReg ge.re 1 ∘ u := by
    rw [← hu]; rfl
  rw [hpr] at hnew
  -- ranks
  have rk5 : DownRk (upRk g5.blocks) g5.blocks := by
    have G : GrowU (gen0 : Comp.Gen Map) ge := by
      rw [gee]
      exact R.grow.trans (growU_emit (fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨lo1, hi1⟩) (R.grow.up upBelow_gen0))
    rw [b5]; exact downRk_of_growU G (fun k => by simp [gen0, HoonMap.get_empty]) (by simp [gen0])
  have RD := rankDown_start (downRk_prep pP rk5) hst
  have gs8 := get_mapVals (renBlob u) (HoonMap.put (HoonMap.del g3.blocks g1.bo) 0 start)
  have g8 := get_mapVals (renBlob u) g3.blocks
  have hnew8 : ∀ k b', HoonMap.get new k = some b' →
      ∃ b, HoonMap.get (mapVals (renBlob u) (HoonMap.put (HoonMap.del g3.blocks g1.bo) 0 start)) k = some b ∧
        keepBlock (mapVals (renBlob u) (HoonMap.put (HoonMap.del g3.blocks g1.bo) 0 start)) (renReg ge.re 1) k b =
          some (some b') := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := renameBlocks_get hnew hk
    refine ⟨renBlob u b, by rw [gs8, hb]; rfl, ?_⟩
    rw [keepBlock_ren RD gs8]; exact hkb
  -- the unproxied blocks are the raw blocks with the unproxied ops in front
  have P8 : Prep (fun k => (P k).map (renPole u)) g5.blocks (mapVals (renBlob u) g3.blocks) := by
    intro k
    rw [g8, pP k]
    cases hb : HoonMap.get g5.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      have fx : renBlob u b = b := by
        rw [renBlob_congr (P := (· < g5.re)) (v := id) (fun x hx => by simp only [id]; exact uLow x (by omega))
          (S5.regs k b hb), renBlob_id]
      rw [renBlob_pre, fx]
  have DB : ∀ k b8, HoonMap.get (mapVals (renBlob u) g3.blocks) k = some b8 →
      ∃ b, HoonMap.get g3.blocks k = some b ∧ b8 = renBlob u b ∧ blockDefs b8 = blockDefs b := by
    intro k b8 hk
    rw [g8] at hk
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hk
    refine ⟨b, hb, rfl, ?_⟩
    rw [blockDefs_renBlob]; exact map_fix (fun x hx => uD x (defd_iff.mpr ⟨k, b, hb, hx⟩))
  have dd8 : ∀ y, Defd (mapVals (renBlob u) g3.blocks) y → Defd g3.blocks y := fun y d => by
    obtain ⟨k, b8, hk, hm⟩ := defd_iff.mp d
    obtain ⟨b, hb, -, e⟩ := DB k b8 hk
    rw [e] at hm; exact defd_iff.mpr ⟨k, b, hb, hm⟩
  have bn8 : BlkNodup (mapVals (renBlob u) g3.blocks) := fun k b8 hk => by
    obtain ⟨b, hb, -, e⟩ := DB k b8 hk; rw [e]; exact S7.nd k b hb
  have bx8 : Cross (mapVals (renBlob u) g3.blocks) := fun k k' b8 b8' y hk hk' hne m m' => by
    obtain ⟨b, hb, -, e⟩ := DB k b8 hk
    obtain ⟨b', hb', -, e'⟩ := DB k' b8' hk'
    rw [e] at m; rw [e'] at m'
    exact S7.cr k k' b b' y hb hb' hne m m'
  have nt8 : NoTr (mapVals (renBlob u) g3.blocks) := fun k b8 hk op hop => by
    obtain ⟨b, hb, rfl, -⟩ := DB k b8 hk
    simp only [renBlob, List.mem_map] at hop
    obtain ⟨op0, h0, rfl⟩ := hop
    rw [tr_ren]; exact S7.tr k b hb op0 h0
  have g10 : g1.bo ≠ 0 := by have := S1.bo1; omega
  -- the raw facts on the blocks before the walk: the hop block of `+kerf` goes to the entry
  have ar1 := (hat nex g1 h1).1
  have tw1 := (hat nex g1 h1).2
  have get5 : ∀ k, HoonMap.get g5.blocks k = HoonMap.get (HoonMap.put g1.blocks g1.bo ⟨[], [], Termin.hop nex.th⟩) k :=
    fun k => by rw [b5, ee]
  have AR5 : Compiler.ArityOK g5.blocks := by
    intro k b j b2 hk hj hb2
    rw [get5] at hk hb2
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨ne, hk⟩
    · simp only [getJmps, List.mem_singleton] at hj
      subst hj
      rw [get_put_ne (by omega)] at hb2
      rcases R.ent with ⟨b0, hb0, hp, ha⟩ | hj
      · rw [hb0] at hb2; cases hb2; simp [hp, ha]
      · exact hj.elim
    · have := S1.jlt hk hj
      rw [get_put_ne (by omega)] at hb2
      exact ar1 k b j b2 hk hj hb2
  have TW5 : Compiler.TwoNA g5.blocks := by
    intro k b j hk h2 hj
    rw [get5] at hk
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨ne, hk⟩
    · simp [Compiler.twoWay] at h2
    · exact tw1 k b j hk h2 hj
  have hK8 : ∀ k y, lazK g1.bo nex.laz k y → y ∈ defsOf ((P k).map (renPole u)) := by
    intro k y hk
    obtain ⟨e, he, rfl, hy⟩ := hk
    have he' : e ∈ (g1.bo, nex.laz) :: wentries nex.laz := by
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((wentries_perm _).mem_iff.mpr he)
    have yl : y < g1.re := by
      rcases List.mem_cons.mp he with rfl | he
      · exact (R.regs y hy).2
      · exact ((R.eregs e he).2 y hy).2
    rw [defsOf_ren, ← uLow y (by omega)]
    exact List.mem_map_of_mem (kP e he' y hy)
  have hl8 : ∀ y, ¬ LiveK g5.blocks (lazK g1.bo nex.laz) g1.bo y := by
    intro y hlv
    rcases hlv with ⟨hb, hrf, -⟩ | ⟨hb, hj, hl', -, hk⟩
    · rw [hbo5] at hb; cases hb
      simp [BlockRF, OpsRF, finRegs, jmpRegs, a1] at hrf
    · rw [hbo5] at hb; cases hb
      simp only [getJmps, List.mem_singleton] at hj
      subst hj
      exact hl1 y (liveK_frame below5 (fun k b hb j hj => S1.jlt hb hj)
        (fun hm => hk ⟨(g1.bo, nex.laz), List.mem_cons_self, rfl, hm⟩) hl' hi1)
  have hX8 : ∀ k y, OpsRF ((P k).map (renPole u)) y → NMem (Need.this ge.re) y := by
    intro k y hy
    obtain ⟨x, rfl, hx⟩ := opsRF_ren_back _ hy
    simp only [NMem]
    rcases rP k x hx with rfl | ⟨t, ht⟩
    · exact uLow _ (Nat.le_refl _)
    · exact uK x _ ht
  obtain ⟨c1, c2, c3, c4, c5⟩ := stIn_prepN (K := lazK g1.bo nex.laz) (ned := Need.this ge.re) P8 rk5 AR5 TW5
    hK8 hl8 hX8 (by rw [g8, hst]; rfl) (by rw [gs8]; simp [HoonMap.get_put])
    (by rw [gs8]; simp [HoonMap.get_put, HoonMap.get_del, g10])
    (fun k k0 ko => by rw [gs8, g8]; simp [HoonMap.get_put, HoonMap.get_del, k0, ko])
    (renReg_inj _ _) (renReg_surj _ _) hnew8 (renameBlocks_ren RD gs8 hnew)
  refine ⟨c1, c2, c3, c4, fun r' hlv => ?_⟩
  obtain ⟨r, rfl, hr⟩ := c5 r' hlv
  simp only [NMem] at hr
  subst hr
  simp [renReg, needToOrd, countArgs]

end Top

end Raw
end SkaModel
end Formalization
