import lemmas.Ska.RawInvOut

/-!
# Raw `+comp` output: `OptIn` after `+to-straight`

README Gaps 14.  **`optIn_toStraight`**: when the blocks given to the
renaming path of `+to-straight` jump down (`Down`), define each register
once (`BlkNodup`, `Cross`), have no trace hint op (`NoTr`), pass no argument
that is a parameter of a block reachable from the target (`DownPar`), and
leave live at the entry only registers of the input need, which nothing
defines, the output meets `OptIn`.  The output's label `k` stands for the
raw label `labOf o k` (`0` for the entry `o`); output paths are raw paths
through the bypassed blocks (`rFrom_out`), and output liveness is raw
liveness of the renamed registers (`live_out`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem renameBlocks_get {bs : Map Blob} {ren : Nat → Nat} {new : Map Blob} (h : renameBlocks bs ren = some new)
    {k : Nat} {b' : Blob} (hk : HoonMap.get new k = some b') :
    ∃ b, HoonMap.get bs k = some b ∧ keepBlock bs ren k b = some (some b') := by
  have F := renameFold_spec (bs := bs) (ren := ren) (HoonMapKeys.keys bs) [] HoonMap.empty new
    ⟨fun k hk => by simp at hk, fun k _ => HoonMap.get_empty k⟩ h
  cases hb : HoonMap.get bs k with
  | none =>
    have : k ∉ [] ++ HoonMapKeys.keys bs := fun hm => by
      have := (HoonMapKeys.mem_keys bs k).mp (by simpa using hm)
      rw [hb] at this; cases this
    rw [F.2 k this] at hk; cases hk
  | some b =>
    obtain ⟨kb, hkb, hget⟩ := F.1 k (by simpa using (HoonMapKeys.mem_keys bs k).mpr (by simp [hb])) b hb
    rw [hk] at hget; subst hget
    exact ⟨b, rfl, hkb⟩

/-- The raw label of an output label. -/
def labOf (o k : Nat) : Nat := if k = 0 then o else k

theorem labOf_pos {o k : Nat} (h : 1 ≤ k) : labOf o k = k := by simp [labOf]; omega

/-- **The eight fields of `OptIn` after `+to-straight`.** -/
theorem optIn_toStraight [MapKeys Map] {blocks : Map Blob} {ned : Need} {o : Nat} {c' : Straight Map}
    (h : toStraight blocks ned o = some c') (hd : Down blocks) (hn : BlkNodup blocks) (hx : Cross blocks)
    (ht : NoTr blocks) (hp : DownPar blocks)
    (hl : ∀ r, Live blocks o r → NMem ned r) (hin : ∀ r, NMem ned r → ¬ Defd blocks r) : OptIn c'.blocks := by
  unfold toStraight at h
  simp only at h
  split at h
  · cases h
  cases hst : HoonMap.get blocks o with
  | none => rw [hst] at h; cases h
  | some start =>
  rw [hst, Option.bind_some] at h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only
  generalize hren : renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length = ren at hnew
  have hi : Inj ren := by rw [← hren]; exact renReg_inj _ _
  have hsurj : ∀ r', ∃ r, ren r = r' := by rw [← hren]; exact renReg_surj _ _
  generalize hbs : HoonMap.put (HoonMap.del blocks o) 0 start = bs at hnew
  have ho1 : 1 ≤ o := (hd o start hst).1
  have hbs0 : HoonMap.get bs 0 = some start := by simp [← hbs, HoonMap.get_put]
  have hbso : HoonMap.get bs o = Option.none := by
    simp [← hbs, HoonMap.get_put, HoonMap.get_del, show o ≠ 0 by omega]
  have hbsk : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k := fun k h0 hk => by
    simp [← hbs, HoonMap.get_put, HoonMap.get_del, h0, hk]
  -- the output blocks
  have OUT : ∀ k b', HoonMap.get new k = some b' → ∃ b fin', HoonMap.get blocks (labOf o k) = some b ∧
      chaseFin bs ren b.fin = some fin' ∧ b' = renB ren b fin' ∧ (k ≠ 0 → k ≠ o) := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := renameBlocks_get hnew hk
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
  have rjump : ∀ k b, HoonMap.get blocks k = some b → ∀ j ∈ getJmps b.fin, 1 ≤ j.there ∧ j.there < k :=
    fun k b hb j hj => (hd k b hb).2 j (by rw [← getJmps_eq]; exact hj)
  have CF : ∀ k b' , HoonMap.get new k = some b' → ∃ b fin', HoonMap.get blocks (labOf o k) = some b ∧
      chaseFin bs ren b.fin = some fin' ∧ b' = renB ren b fin' ∧
      (∀ n s z o', fin' ≠ Termin.lti n s z o') ∧
      (∀ j'' ∈ getJmps fin', ∃ j ∈ getJmps b.fin, ∃ br j', chase bs br j = some j' ∧ j'' = renJmp ren j') ∧
      (∀ r, ren r ∈ finRegs fin' → r ∈ finRegs b.fin ∨ ∃ j ∈ getJmps b.fin, Live blocks j.there r) := by
    intro k b' hk
    obtain ⟨b, fin', hb, hf, rfl, -⟩ := OUT k b' hk
    obtain ⟨n1, n2, n3⟩ := chaseFin_raw hd hbsk hbso hi (fun j hj => (rjump _ b hb j hj).1) hf
    exact ⟨b, fin', hb, hf, rfl, n1, n2, n3⟩
  have CR := fun (j : Jmp) br j' (h1 : 1 ≤ j.there) (h : chase bs br j = some j') =>
    chase_raw hd hbsk hbso (j.there + 1) j br j' (Nat.lt_succ_self _) h1 h
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
  refine ⟨parNodup_of bn, downPar_passOK dp, ⟨labOf o, ?_⟩, dp, ⟨_, trimBr_of_noTr ?_⟩, ?_, ?_,
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

end Raw
end SkaModel
end Formalization
