import lemmas.Ska.RawInvInto

/-!
# Raw `+comp` output: through `+to-straight`

README Gaps 14.  The renaming path of `+to-straight` (`toStraight` of
`CompTop.lean`) renames registers by the bijection `renReg r0 n`, moves the
entry block to `0`, drops the bypassable blocks and chases the jumps past
them.  `optIn_toStraight`: blocks that jump down (`Down`), define each
register once (`BlkNodup`, `Cross`), have no trace hint op, no argument of
a jump that is a parameter of a block reachable from its target
(`DownPar`), and no register live at the entry but registers of the input
need, which nothing defines, give an output with **all eight fields of
`OptIn`**.

* `mem_aliasReads`: the registers an op reads are its sources (`srcs`).
* `renReg_surj`: the renaming is onto, so every output register is the
  image of one register.
* `chase_raw`: a chased jump keeps its arguments, goes to a label at or
  below the target, not the entry, kept in the output, through bypassable
  blocks (no definitions, no reads: liveness and reachability pass).
* `out_block`, `out_of_block`: the output blocks are the renamed kept blocks.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]

/-! ## Reads and renaming -/

/-- The registers an op reads (its registers other than the destination). -/
def srcs : Pole → List Nat
  | Pole.imm _ _ => []
  | Pole.mov s _ => [s]
  | Pole.inc s _ => [s]
  | Pole.con h t _ => [h, t]
  | Pole.hed s _ => [s]
  | Pole.tal s _ => [s]
  | Pole.spy e p _ => [e, p]
  | Pole.nok u f _ => [u, f]
  | Pole.cal _ v _ => v
  | Pole.caf _ v _ _ => v
  | Pole.cam _ v _ _ => v
  | Pole.csl _ s _ => [s]
  | Pole.csf _ s _ _ => [s]
  | Pole.csm _ s _ _ => [s]
  | Pole.cel p => [p]
  | Pole.lob p => [p]
  | Pole.equ l r => [l, r]
  | Pole.hsp _ _ => []
  | Pole.hse _ _ => []
  | Pole.hdp _ p _ => [p]
  | Pole.hde _ p _ => [p]
  | Pole.hmp _ v _ => v
  | Pole.hme _ v _ => v
  | Pole.hcp _ _ => []
  | Pole.hce _ _ => []

theorem mem_erase_snoc {r d : Nat} : ∀ (l : List Nat), r ∈ (l ++ [d]).erase d ↔ r ∈ l
  | [] => by simp
  | x :: l => by
    by_cases e : x = d
    · subst e; simp [or_comm]
    · simp only [List.cons_append, List.erase_cons, beq_iff_eq, e, if_false, List.mem_cons, mem_erase_snoc l]

theorem erase1 {r d : Nat} : r ∈ [d].erase d ↔ False := by simp
theorem erase2 {r a d : Nat} : r ∈ [a, d].erase d ↔ r = a := by
  have := mem_erase_snoc (r := r) (d := d) [a]; simpa using this
theorem erase3 {r a c d : Nat} : r ∈ [a, c, d].erase d ↔ r = a ∨ r = c := by
  have := mem_erase_snoc (r := r) (d := d) [a, c]; simpa using this
theorem erase_head {r d : Nat} {v : List Nat} : r ∈ (d :: v).erase d ↔ r ∈ v := by simp

theorem mem_aliasReads {op : Pole} {r : Nat} : r ∈ aliasReads op ↔ r ∈ srcs op := by
  cases op <;> simp only [aliasReads, aliasDst, srcs, Opt.poleRegs, erase1, erase2, erase3, erase_head,
    List.mem_cons, List.mem_nil_iff, or_false]

theorem srcs_ren (ren : Nat → Nat) (op : Pole) : srcs (renPole ren op) = (srcs op).map ren := by
  cases op <;> simp [srcs, renPole]

theorem dst_ren (ren : Nat → Nat) (op : Pole) : aliasDst (renPole ren op) = (aliasDst op).map ren := by
  cases op <;> simp [aliasDst, renPole]

theorem tr_ren (ren : Nat → Nat) (op : Pole) : trOp (renPole ren op) = trOp op := by
  cases op <;> rfl

theorem mem_map_inj {ren : Nat → Nat} (hi : Inj ren) {r : Nat} {l : List Nat} : ren r ∈ l.map ren ↔ r ∈ l := by
  constructor
  · intro h; obtain ⟨x, hx, e⟩ := List.mem_map.mp h; rw [hi x r e] at hx; exact hx
  · intro h; exact List.mem_map.mpr ⟨r, h, rfl⟩

theorem reads_ren {ren : Nat → Nat} (hi : Inj ren) (op : Pole) {r : Nat} :
    ren r ∈ aliasReads (renPole ren op) ↔ r ∈ aliasReads op := by
  rw [mem_aliasReads, mem_aliasReads, srcs_ren, mem_map_inj hi]

theorem defsOf_ren (ren : Nat → Nat) (A : List Pole) : defsOf (A.map (renPole ren)) = (defsOf A).map ren := by
  induction A with
  | nil => rfl
  | cons op A ih => rw [List.map_cons, defsOf_cons, defsOf_cons, ih, dst_ren]; cases aliasDst op <;> simp

theorem opsRF_ren {ren : Nat → Nat} (hi : Inj ren) {r : Nat} :
    ∀ (A : List Pole), OpsRF (A.map (renPole ren)) (ren r) ↔ OpsRF A r
  | [] => Iff.rfl
  | op :: A => by
    simp only [List.map_cons, OpsRF, reads_ren hi, dst_ren, opsRF_ren hi A]
    cases h : aliasDst op with
    | none => simp
    | some d =>
      simp only [Option.map_some, ne_eq, Option.some.injEq]
      constructor
      · rintro (e | ⟨e, e'⟩)
        · exact Or.inl e
        · exact Or.inr ⟨fun e2 => e (by rw [e2]), e'⟩
      · rintro (e | ⟨e, e'⟩)
        · exact Or.inl e
        · exact Or.inr ⟨fun e2 => e (hi _ _ e2), e'⟩

theorem renReg_surj (r0 n r' : Nat) : ∃ r, renReg r0 n r = r' := by
  by_cases h1 : r' < n
  · exact ⟨r' + r0, by unfold renReg; split <;> (try split) <;> omega⟩
  · by_cases h2 : r' < r0 + n
    · exact ⟨r' - n, by unfold renReg; split <;> (try split) <;> omega⟩
    · exact ⟨r', by unfold renReg; split <;> (try split) <;> omega⟩

/-! ## Chasing -/

section Chase
variable {blocks bs : Map Blob} {o : Nat}

/-- **A chased jump**: a label at or below the target, not the entry, whose
block is kept, reached through blocks that define nothing and read only the
arguments of their hops; the chased jump is the jump itself or a jump of one
of the blocks passed. -/
theorem chase_raw (hd : Down blocks) (hbs : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    (hbo : HoonMap.get bs o = Option.none) :
    ∀ n (j : Jmp) (br : Bool) (j' : Jmp), j.there < n → 1 ≤ j.there → chase bs br j = some j' →
    j'.there ≤ j.there ∧ j'.there ≠ o ∧ 1 ≤ j'.there ∧
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
            obtain ⟨hle, hno, h1', hb', hlv, hjr, hor, hrf, -⟩ := chase_raw hd hbs hbo n t br j' (by omega) hdt.1 hc
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

theorem nodup_map_inj {f : Nat → Nat} (hi : Inj f) : ∀ {l : List Nat}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun hm => hx ((mem_map_inj hi).mp hm), nodup_map_inj hi hl⟩

theorem getJmps_eq (f : Termin) : getJmps f = finJumps f := by cases f <;> rfl

theorem jmpRegs_ren (ren : Nat → Nat) (j : Jmp) : jmpRegs (renJmp ren j) = (jmpRegs j).map ren := by
  rcases j with ⟨args, there⟩
  simp only [jmpRegs, renJmp]
  induction args with
  | nil => rfl
  | cons a args ih => cases a <;> simp [List.filterMap_cons, ih]

theorem blockDefs_renB (ren : Nat → Nat) (b : Blob) (fin : Termin) :
    blockDefs (renB ren b fin) = (blockDefs b).map ren := by
  have := defsOf_ren ren b.body
  simp only [defsOf] at this
  simp only [blockDefs, renB, List.map_append, this]

section Out
variable {blocks bs : Map Blob} {o : Nat}

/-- **The end of a block, chased and renamed**: no `%lti`, each jump the
renamed chase of a jump of the end, and each register it reads the image of
one the end reads or one live at a target. -/
theorem chaseFin_raw (hd : Down blocks) (hbs : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get blocks k)
    (hbo : HoonMap.get bs o = Option.none) {ren : Nat → Nat} (hi : Inj ren) {fin fin' : Termin}
    (hj : ∀ j ∈ getJmps fin, 1 ≤ j.there) (hc : chaseFin bs ren fin = some fin') :
    (∀ n s z o', fin' ≠ Termin.lti n s z o') ∧
    (∀ j'' ∈ getJmps fin', ∃ j ∈ getJmps fin, ∃ br j', chase bs br j = some j' ∧ j'' = renJmp ren j') ∧
    (∀ r, ren r ∈ finRegs fin' → r ∈ finRegs fin ∨ ∃ j ∈ getJmps fin, Live blocks j.there r) := by
  have CR := fun (j : Jmp) br j' (h1 : 1 ≤ j.there) (h : chase bs br j = some j') =>
    chase_raw hd hbs hbo (j.there + 1) j br j' (Nat.lt_succ_self _) h1 h
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

end Raw
end SkaModel
end Formalization
