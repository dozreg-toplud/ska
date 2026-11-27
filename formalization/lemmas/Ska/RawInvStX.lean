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

end Out

end Raw
end SkaModel
end Formalization
