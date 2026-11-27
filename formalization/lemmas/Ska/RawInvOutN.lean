import lemmas.Ska.RawInvTopX

/-!
# Raw `+comp` output: `OptIn` of any output the renaming path describes

README Gaps 14, the whole-subject pass on `FragX`.  `optIn_toStraightR`
and `optIn_toStraight_prep` take the equation of `toStraight`.  On the
whole-subject pass `+to-straight` takes its map path (`+kern` makes
proxies), which on a run of inputs renames by `ren ∘ unproxy`
(`toStraightF_run`), and `renameBlocks_ren` of track C says label by label
that its output is the renaming path by `ren` of the unproxied blocks.  So
here the same two theorems for any output map `new` whose every block is a
block of the renaming path by an injective `ren` of the blocks `bs` (the raw
blocks with the start block moved to `0`):

* **`optIn_renOutR`**: `optIn_toStraightR` with `new` in place of the
  equation, generated from its text (the preamble that unfolds `toStraight`
  replaced by the hypotheses it derived, and `renameBlocks_get` by `hnew`);
* **`optIn_prepN`**: `optIn_toStraight_prep` the same way.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem optIn_renOutR [MapKeys Map] {blocks : Map Blob} {ned : Need} {o : Nat} {start : Blob}
    (hst : HoonMap.get blocks o = some start) {bs : Map Blob} (hbs0 : HoonMap.get bs 0 = some start)
    (hbso : HoonMap.get bs o = Option.none) (hbsk : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    {ren : Nat → Nat} (hi : Inj ren) (hsurj : ∀ r', ∃ r, ren r = r') {new : Map Blob}
    (hnew : ∀ k b', HoonMap.get new k = some b' → ∃ b, HoonMap.get bs k = some b ∧ keepBlock bs ren k b = some (some b'))
    {ρ : Nat → Nat} (hd : DownRk ρ blocks) (hn : BlkNodup blocks) (hx : Cross blocks)
    (ht : NoTr blocks) (hp : DownPar blocks)
    (hl : ∀ r, Live blocks o r → NMem ned r) (hin : ∀ r, NMem ned r → ¬ Defd blocks r) : OptIn new := by
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
  -- paths of the output are raw paths
  have RO : ∀ x z, RFrom new x z → RFrom blocks (labOf o x) (labOf o z) := by
    intro x z hr
    induction hr with
    | refl => exact RFrom.refl _
    | @step x z b' j'' hb' hj _ ih =>
      obtain ⟨b, j, br, j', hb, hjm, hc, rfl⟩ := JO x b' j'' hb' hj
      have hj1 := (rjump _ b hb j hjm).1
      obtain ⟨-, -, h1', -, -, -, -, hrf, -⟩ := CR j br j' hj1 hc
      simp only [renJmp, labOf_pos h1'] at ih
      exact (RFrom.one hb hjm).trans (hrf.trans ih)
  -- definitions of the output are renamed raw ones
  have DO : ∀ r', Defd new r' → ∃ r, ren r = r' ∧ Defd blocks r := by
    intro r' d
    obtain ⟨k, b', hk, hm⟩ := defd_iff.mp d
    obtain ⟨b, fin', hb, -, rfl, -⟩ := OUT k b' hk
    rw [blockDefs_renB] at hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact ⟨r, rfl, defd_iff.mpr ⟨_, b, hb, hr⟩⟩
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
  -- the fields
  have bn : BlkNodup new := fun k b' hk => by
    obtain ⟨b, fin', hb, -, rfl, -⟩ := OUT k b' hk
    rw [blockDefs_renB]; exact nodup_map_inj hi (hn _ b hb)
  have bx : Cross new := by
    intro k1 k2 b1' b2' r h1 h2 hne m1 m2
    obtain ⟨b1, f1, hb1, -, rfl, n1⟩ := OUT k1 b1' h1
    obtain ⟨b2, f2, hb2, -, rfl, n2⟩ := OUT k2 b2' h2
    rw [blockDefs_renB] at m1 m2
    obtain ⟨x, hx1, rfl⟩ := List.mem_map.mp m1
    have hx2 := (mem_map_inj hi).mp m2
    have hlab : labOf o k1 ≠ labOf o k2 := by
      simp only [labOf]
      by_cases a : k1 = 0 <;> by_cases c : k2 = 0
      · exact absurd (a.trans c.symm) hne
      · simp only [a, c, if_true, if_false]; exact fun e => n2 c e.symm
      · simp only [a, c, if_true, if_false]; exact n1 a
      · simp only [a, c, if_false]; exact hne
    exact hx _ _ b1 b2 x hb1 hb2 hlab hx1 hx2
  have dp : DownPar new := by
    intro y b' j'' hy hj r'' hr z bz hz hbz hpz
    obtain ⟨b, j, br, j', hb, hjm, hc, rfl⟩ := JO y b' j'' hy hj
    have hj1 := (rjump _ b hb j hjm).1
    obtain ⟨-, -, h1', -, -, -, hor, -, -⟩ := CR j br j' hj1 hc
    simp only [renJmp, List.mem_map] at hr
    obtain ⟨a, ha, ea⟩ := hr
    cases a with
    | none => cases ea
    | some r =>
      simp only [Option.map_some, Option.some.injEq] at ea
      subst ea
      have hrz := RO _ _ hz
      simp only [renJmp, labOf_pos h1'] at hrz
      obtain ⟨bz0, fz, hbz0, -, ez, -⟩ := OUT z bz hbz
      rw [ez] at hpz
      have hpz' : r ∈ bz0.par := (mem_map_inj hi).mp hpz
      rcases hor with e | ⟨m, bm, -, hbm, hjm'⟩
      · rw [e] at ha hrz; exact hp _ b j hb hjm r ha _ bz0 hrz hbz0 hpz'
      · exact hp m bm j' hbm hjm' r ha _ bz0 hrz hbz0 hpz'
  refine ⟨parNodup_of bn, downPar_passOK dp, ⟨fun k => ρ (labOf o k), ?_⟩, dp, ⟨_, trimBr_of_noTr ?_⟩, ?_, ?_,
    defOnceR_of_defUniq (defUniq_of bn bx)⟩
  · intro k b' j'' hk hj
    obtain ⟨b, j, br, j', hb, hjm, hc, rfl⟩ := JO k b' j'' hk hj
    have hjr := rjump _ b hb j hjm
    obtain ⟨hle, -, h1', -⟩ := CR j br j' hjr.1 hc
    simp only [renJmp, labOf_pos h1']
    omega
  · intro k b' hk op hop
    obtain ⟨b, fin', hb, -, rfl, -⟩ := OUT k b' hk
    simp only [renB, List.mem_map] at hop
    obtain ⟨op0, h0, rfl⟩ := hop
    rw [tr_ren]; exact ht _ b hb op0 h0
  · refine defFirst_of_live fun r' hlv d => ?_
    obtain ⟨r, rfl, hl0⟩ := LO 0 r' hlv
    simp only [labOf, if_true] at hl0
    obtain ⟨x, ex, dx⟩ := DO _ d
    rw [hi _ _ ex] at dx
    exact hin r (hl r hl0) dx
  · intro k b' hk n s z o' e
    obtain ⟨b, fin', hb, -, rfl, n1, -⟩ := CF k b' hk
    exact n1 n s z o' e


/-- **`optIn_toStraight_prep` for any output of the renaming path.** -/
theorem optIn_prepN [MapKeys Map] {bl bl' : Map Blob} {P : Nat → List Pole} {K : Nat → Nat → Prop}
    {ned : Need} {o : Nat}
    (hP : Prep P bl bl') (hrk : DownRk (upRk bl) bl) (haa : ArgsAboveR (upRk bl) bl)
    (hK : ∀ k r, K k r → r ∈ defsOf (P k)) (hl : ∀ r, ¬ LiveK bl K o r)
    (hn : BlkNodup bl') (hx : Cross bl') (ht : NoTr bl')
    (hX : ∀ k r, OpsRF (P k) r → NMem ned r) (hin : ∀ r, NMem ned r → ¬ Defd bl' r)
    {start : Blob} (hst : HoonMap.get bl' o = some start) {bs : Map Blob} (hbs0 : HoonMap.get bs 0 = some start)
    (hbso : HoonMap.get bs o = Option.none) (hbsk : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get bl' k)
    {ren : Nat → Nat} (hi : Inj ren) (hsurj : ∀ r', ∃ r, ren r = r') {new : Map Blob}
    (hnew : ∀ k b', HoonMap.get new k = some b' → ∃ b, HoonMap.get bs k = some b ∧ keepBlock bs ren k b = some (some b')) :
    OptIn new := by
  have e : upRk bl' = upRk bl := funext (upRk_prep hP)
  have rk' : DownRk (upRk bl') bl' := by rw [e]; exact downRk_prep hP hrk
  have aa' : ArgsAboveR (upRk bl') bl' := argsAboveR_upRk_prep hP haa
  exact optIn_renOutR hst hbs0 hbso hbsk hi hsurj hnew rk' hn hx ht (downPar_of_argsR aa' (jdownR_of_downRk rk'))
    (fun r hr => live_entry_of_prep hP hK hl hX hr) hin

end Raw
end SkaModel
end Formalization
