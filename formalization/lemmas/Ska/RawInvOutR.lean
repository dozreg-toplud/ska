import lemmas.Ska.RawInvOutMain

/-!
# Raw `+comp` output: `OptIn` after `+to-straight` for blocks that go down in a rank

README Gaps 14, the class `FragX`.  `optIn_toStraight` of
`RawInvOutMain.lean` asks that the blocks jump to lower labels (`Down`),
which the fork blocks of `%6` under `%next` do not: they hop up to the join.
Here the same with any rank `ρ` (`DownRk ρ`, `ρ := upRk` of `CompGrowU.lean`
for `FragX`): `chase_rawR` (a chased jump has rank at most the target's),
`chaseFin_rawR`, and **`optIn_toStraightR`**.  Generated from the text of
`chase_raw`, `chaseFin_raw` and `optIn_toStraight` with `Down blocks`
replaced by `DownRk ρ blocks`, the fuel bound and the first conclusion of
`chase_raw` stated on ranks, and the output's rank `ρ ∘ labOf o`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]

section Chase
variable {blocks bs : Map Blob} {o : Nat}

/-- **A chased jump**: a label at or below the target, not the entry, whose
block is kept, reached through blocks that define nothing and read only the
arguments of their hops; the chased jump is the jump itself or a jump of one
of the blocks passed. -/
theorem chase_rawR {ρ : Nat → Nat} (hd : DownRk ρ blocks) (hbs : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    (hbo : HoonMap.get bs o = Option.none) :
    ∀ n (j : Jmp) (br : Bool) (j' : Jmp), ρ j.there < n → 1 ≤ j.there → chase bs br j = some j' →
    ρ j'.there ≤ ρ j.there ∧ j'.there ≠ o ∧ 1 ≤ j'.there ∧
      (∃ b', HoonMap.get blocks j'.there = some b' ∧ bypassable br b' = false) ∧
      (∀ r, Live blocks j'.there r → Live blocks j.there r) ∧
      (∀ r ∈ jmpRegs j', r ∈ jmpRegs j ∨ Live blocks j.there r) ∧
      (j' = j ∨ ∃ m bm, RFrom blocks j.there m ∧ HoonMap.get blocks m = some bm ∧ j' ∈ getJmps bm.fin) ∧
      RFrom blocks j.there j'.there ∧ (j.args ≠ [] → j' = j)
  | 0, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, j, br, j', hn, h1, hc => by
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
        by_cases hby : bypassable br b = true
        · rw [if_pos hby] at hc
          by_cases ha : j.args = []
          · rw [if_pos ha] at hc
            have hdt := (hd _ _ hb).2 t (by simp [finJumps, heq])
            obtain ⟨hle, hno, h1', hb', hlv, hjr, hor, hrf, -⟩ := chase_rawR hd hbs hbo n t br j' (by omega) hdt.1 hc
            obtain ⟨t', rfl⟩ := bypassable_shape hby
            simp only [Termin.hop.injEq] at heq
            subst t'
            have hjt : t ∈ getJmps (Termin.hop t) := by simp [getJmps]
            have lt : ∀ r, Live blocks t.there r → Live blocks j.there r := fun r hl =>
              Live.next hb hjt hl (by simp [blockDefs])
            refine ⟨by omega, hno, h1', hb', fun r hl => lt r (hlv r hl), fun r hr => ?_, ?_,
              RFrom.step hb hjt hrf, fun e => absurd ha e⟩
            · right
              rcases hjr r hr with e | e
              · exact Live.here hb ⟨by simp, Or.inr ⟨by simp [defsOf], by simpa [finRegs] using e⟩⟩
              · exact lt r e
            · right
              rcases hor with e | ⟨m, bm, hm, hbm, hjm⟩
              · subst e; exact ⟨j.there, _, RFrom.refl _, hb, hjt⟩
              · exact ⟨m, bm, RFrom.step hb hjt hm, hbm, hjm⟩
          · rw [if_neg ha] at hc; simp at hc
        · rw [if_neg hby] at hc
          cases hc
          exact ⟨Nat.le_refl _, ho, h1, ⟨b, hb, by simpa using hby⟩, fun _ h => h, fun r hr => Or.inl hr,
            Or.inl rfl, RFrom.refl _, fun _ => rfl⟩
      · cases hc
        refine ⟨Nat.le_refl _, ho, h1, ⟨b, hb, ?_⟩, fun _ h => h, fun r hr => Or.inl hr, Or.inl rfl,
          RFrom.refl _, fun _ => rfl⟩
        rename_i hne
        rcases b with ⟨par, body, fin⟩
        cases par <;> cases body <;> cases fin <;> simp_all [bypassable]

end Chase

section Out
variable {blocks bs : Map Blob} {o : Nat}

/-- **The end of a block, chased and renamed**: no `%lti`, each jump the
renamed chase of a jump of the end, and each register it reads the image of
one the end reads or one live at a target. -/
theorem chaseFin_rawR {ρ : Nat → Nat} (hd : DownRk ρ blocks) (hbs : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    (hbo : HoonMap.get bs o = Option.none) {ren : Nat → Nat} (hi : Inj ren) {fin fin' : Termin}
    (hj : ∀ j ∈ getJmps fin, 1 ≤ j.there) (hc : chaseFin bs ren fin = some fin') :
    (∀ n s z o', fin' ≠ Termin.lti n s z o') ∧
    (∀ j'' ∈ getJmps fin', ∃ j ∈ getJmps fin, ∃ br j', chase bs br j = some j' ∧ j'' = renJmp ren j') ∧
    (∀ r, ren r ∈ finRegs fin' → r ∈ finRegs fin ∨ ∃ j ∈ getJmps fin, Live blocks j.there r) := by
  have CR := fun (j : Jmp) br j' (h1 : 1 ≤ j.there) (h : chase bs br j = some j') =>
    chase_rawR hd hbs hbo (ρ j.there + 1) j br j' (Nat.lt_succ_self _) h1 h
  have jr : ∀ (j : Jmp) br j', 1 ≤ j.there → chase bs br j = some j' → ∀ r, ren r ∈ jmpRegs (renJmp ren j') →
      r ∈ jmpRegs j ∨ Live blocks j.there r := fun j br j' h1 h r hr => by
    rw [jmpRegs_ren, mem_map_inj hi] at hr
    exact (CR j br j' h1 h).2.2.2.2.2.1 r hr
  cases fin with
  | clq s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    have hz1 := hj z (by simp [getJmps])
    have ho1 := hj o' (by simp [getJmps])
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => ?_, fun r hr => ?_⟩
    · simp [getJmps] at hm
      rcases hm with rfl | rfl
      · exact ⟨z, by simp [getJmps], true, z', hz, rfl⟩
      · exact ⟨o', by simp [getJmps], true, o'', ho, rfl⟩
    · simp only [finRegs, List.mem_cons, List.mem_append] at hr
      rcases hr with e | e | e
      · exact Or.inl (by simp [finRegs, hi _ _ e])
      · rcases jr z true z' hz1 hz r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨z, by simp [getJmps], e⟩
      · rcases jr o' true o'' ho1 ho r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨o', by simp [getJmps], e⟩
  | eqq l q z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    have hz1 := hj z (by simp [getJmps])
    have ho1 := hj o' (by simp [getJmps])
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => ?_, fun r hr => ?_⟩
    · simp [getJmps] at hm
      rcases hm with rfl | rfl
      · exact ⟨z, by simp [getJmps], true, z', hz, rfl⟩
      · exact ⟨o', by simp [getJmps], true, o'', ho, rfl⟩
    · simp only [finRegs, List.mem_cons, List.mem_append] at hr
      rcases hr with e | e | e | e
      · exact Or.inl (by simp [finRegs, hi _ _ e])
      · exact Or.inl (by simp [finRegs, hi _ _ e])
      · rcases jr z true z' hz1 hz r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨z, by simp [getJmps], e⟩
      · rcases jr o' true o'' ho1 ho r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨o', by simp [getJmps], e⟩
  | brn s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    have hz1 := hj z (by simp [getJmps])
    have ho1 := hj o' (by simp [getJmps])
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => ?_, fun r hr => ?_⟩
    · simp [getJmps] at hm
      rcases hm with rfl | rfl
      · exact ⟨z, by simp [getJmps], true, z', hz, rfl⟩
      · exact ⟨o', by simp [getJmps], true, o'', ho, rfl⟩
    · simp only [finRegs, List.mem_cons, List.mem_append] at hr
      rcases hr with e | e | e
      · exact Or.inl (by simp [finRegs, hi _ _ e])
      · rcases jr z true z' hz1 hz r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨z, by simp [getJmps], e⟩
      · rcases jr o' true o'' ho1 ho r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨o', by simp [getJmps], e⟩
  | brz s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    have hz1 := hj z (by simp [getJmps])
    have ho1 := hj o' (by simp [getJmps])
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => ?_, fun r hr => ?_⟩
    · simp [getJmps] at hm
      rcases hm with rfl | rfl
      · exact ⟨z, by simp [getJmps], true, z', hz, rfl⟩
      · exact ⟨o', by simp [getJmps], true, o'', ho, rfl⟩
    · simp only [finRegs, List.mem_cons, List.mem_append] at hr
      rcases hr with e | e | e
      · exact Or.inl (by simp [finRegs, hi _ _ e])
      · rcases jr z true z' hz1 hz r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨z, by simp [getJmps], e⟩
      · rcases jr o' true o'' ho1 ho r e with e | e
        · exact Or.inl (by simp [finRegs, e])
        · exact Or.inr ⟨o', by simp [getJmps], e⟩
  | hop t =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨t', ht, rfl⟩ := hc
    have ht1 := hj t (by simp [getJmps])
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => ?_, fun r hr => ?_⟩
    · simp [getJmps] at hm; subst hm
      exact ⟨t, by simp [getJmps], false, t', ht, rfl⟩
    · simp only [finRegs] at hr
      rcases jr t false t' ht1 ht r hr with e | e
      · exact Or.inl (by simp [finRegs, e])
      · exact Or.inr ⟨t, by simp [getJmps], e⟩
  | jmp a v =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => ?_⟩
    simp only [finRegs] at hr ⊢; exact Or.inl ((mem_map_inj hi).mp hr)
  | jmf a v n =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => ?_⟩
    simp only [finRegs] at hr ⊢; exact Or.inl ((mem_map_inj hi).mp hr)
  | jsp a s =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => ?_⟩
    simp only [finRegs, List.mem_singleton] at hr ⊢; exact Or.inl (hi _ _ hr)
  | jsf a s n =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => ?_⟩
    simp only [finRegs, List.mem_singleton] at hr ⊢; exact Or.inl (hi _ _ hr)
  | don s =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    refine ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => ?_⟩
    simp only [finRegs, List.mem_singleton] at hr ⊢; exact Or.inl (hi _ _ hr)
  | bom m =>
    cases m with
    | none =>
      simp only [chaseFin, Option.some.injEq] at hc; subst hc
      exact ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => by simp [finRegs] at hr⟩
    | some x =>
      simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨j, -, rfl⟩ := hc
      exact ⟨fun _ _ _ _ e => (by cases e), fun j'' hm => (by simp [getJmps] at hm), fun r hr => by simp [finRegs] at hr⟩
  | lti n s z o' => simp [chaseFin] at hc

end Out

section Main
variable [HoonMapKeys Map]

theorem optIn_toStraightR [MapKeys Map] {blocks : Map Blob} {ned : Need} {o : Nat} {c' : Straight Map}
    (h : toStraight blocks ned o = some c') {ρ : Nat → Nat} (hd : DownRk ρ blocks) (hn : BlkNodup blocks) (hx : Cross blocks)
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

end Main

end Raw
end SkaModel
end Formalization
