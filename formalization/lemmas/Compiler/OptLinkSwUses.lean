import lemmas.Compiler.OptLinkSwNouns

/-!
# `+switch-chains`: `uses`

```hoon
  =/  uses=(map @uvre @ud)
    =/  put
      |=  [r=@uvre acc=(map @uvre @ud)]
      (~(put by acc) r +((~(gut by acc) r 0)))
    %-  ~(rep by blocks)
    |=  [[o=@uwoo b=blob] acc=(map @uvre @ud)]
    =.  acc  (roll par.b put(acc acc))
    =.  acc  (roll (get-regs fin.b) put(acc acc))
    %+  roll  body.b
    |=  [op=pole acc=_acc]
    (roll (get-regs op) put(acc acc))
```

The Hoon keeps the counts in a map that never holds `0` (every `+put:by`
puts a successor), the model `usesOf` counts the mentions of a register in
the list of `blobMentions` of the blocks in the order of `rap`.

* `UsesRel N f`: `N` is a map whose value at each register `r` with `0 < f r`
  is `f r`, with no other key.
* `uses_gut`, `uses_put`: `+gut:by` at a register and `+put:by` of its
  successor.
* `sw_putg`, `sw_opg`, `sw_repg`: the gate `put`, the gate of the `+roll`
  over the ops, the gate of the `+rep:by`.
* `sw_uses`: **`uses` is a map related to `usesOf`**, on blocks with no
  `%lti`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Maps of counts of registers -/

/-- The value at a key noun of the map of the counts `f`. -/
def usesLook (f : Nat → Nat) : Noun → Option Noun
  | Noun.atom r => if 0 < f r then some (A (f r)) else none
  | _ => none

/-- The noun `N` is the map of the counts `f`. -/
def UsesRel (N : Noun) (f : Nat → Nat) : Prop := IsMap mugF N ∧ ∀ kn, look N kn = usesLook f kn

theorem usesRel_nil : UsesRel (A 0) (fun _ => 0) :=
  ⟨IsMap.nil, fun kn => by cases kn <;> simp [look_nil, usesLook]⟩

/-- **`(~(gut by acc) r 0)`**: the count of `r`. -/
theorem uses_gut {N : Noun} {f : Nat → Nat} (h : UsesRel N f) (r : Nat) :
    nock (C by.gut.battery (C (C (A r) (A 0)) (C by.battery (C N layer2)))) by.gut.battery
      = some (A (f r)) := by
  have hl := h.2 (A r)
  simp only [usesLook] at hl
  by_cases hp : 0 < f r
  · rw [if_pos hp] at hl
    have hg := getF_some h.1 ((look_get h.1 _ _).1 hl)
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inr ⟨_, rfl⟩)]
    simp
  · rw [if_neg hp] at hl
    have hg := getF_none h.1 (fun v hv => by rw [← look_get h.1] at hv; rw [hl] at hv; cases hv)
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inl rfl)]
    have : f r = 0 := by omega
    simp [this]

/-- One more mention of `r`. -/
def bump (f : Nat → Nat) (r : Nat) : Nat → Nat := fun x => if x = r then f r + 1 else f x

/-- **`(~(put by acc) r +(n))`** with `n` the count of `r`. -/
theorem uses_put {N : Noun} {f : Nat → Nat} (h : UsesRel N f) (r : Nat) :
    ∃ N', nock (C by.put.battery (C (C (A r) (A (f r + 1))) (C by.battery (C N layer2)))) by.put.battery
      = some N' ∧ UsesRel N' (bump f r) := by
  obtain ⟨out, hp, ho, hg⟩ := putF_spec mugF N (A r) (A (f r + 1)) h.1
  refine ⟨out, put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, fun kn => ?_⟩
  rw [look_put ho h.1 hg, h.2 kn]
  by_cases e : kn = A r
  · subst e; simp [usesLook, bump]
  · rw [if_neg e]
    cases kn with
    | cell _ _ => rfl
    | atom x =>
      have hx : x ≠ r := fun hx => e (by rw [hx])
      simp [usesLook, bump, hx]

/-- `bump` over a list of registers. -/
def bumps (f : Nat → Nat) (rs : List Nat) : Nat → Nat := rs.foldl bump f

theorem bumps_append (f : Nat → Nat) (rs rs' : List Nat) : bumps f (rs ++ rs') = bumps (bumps f rs) rs' := by
  simp [bumps, List.foldl_append]

theorem bumps_apply : ∀ (rs : List Nat) (f : Nat → Nat) (x : Nat), bumps f rs x = f x + rs.count x
  | [], f, x => by simp [bumps]
  | r :: rs, f, x => by
    show bumps (bump f r) rs x = _
    rw [bumps_apply rs (bump f r) x]
    simp only [bump, List.count_cons]
    by_cases e : x = r
    · subst e; simp; omega
    · simp [e, Ne.symm e]

/-! ## The gates -/

/-- The subject after `rev`: `[rev [topo gate]]`. -/
def swS2 (BL TOPO REV : Noun) : Noun := C REV (C TOPO (swG BL))

/-- The core of the gate `put` as `uses` makes it. -/
def swPC (BL TOPO REV : Noun) : Noun := C swPutB (C (C (A 0) (A 0)) (swS2 BL TOPO REV))

/-- **The gate `put`**: one more mention of `r`. -/
theorem sw_putg (BL TOPO REV : Noun) (r : Nat) (N : Noun) (f : Nat → Nat) (h : UsesRel N f) :
    ∃ N', nock (C swPutB (C (C (A r) N) (swS2 BL TOPO REV))) swPutB = some N' ∧ UsesRel N' (bump f r) := by
  obtain ⟨N', hp, hR⟩ := uses_put h r
  refine ⟨N', ?_, hR⟩
  have hg := uses_gut h r
  have hL := optC_layer2
  unfold swS2 swG
  generalize optC = OC at hL
  simp [nock_exec, swPutB, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, by.gut.arm_at, gut_arm, hg, hp]

/-- `+roll` of the gate `put` over a list of registers. -/
theorem sw_roll_put (BL TOPO REV : Noun) (rs : List Nat) (N : Noun) (f : Nat → Nat) (h : UsesRel N f) :
    ∃ N', nock (C roll.battery (C (C (listNoun A rs) (C swPutB (C (C (A 0) N) (swS2 BL TOPO REV)))) layer2))
      roll.battery = some N' ∧ UsesRel N' (bumps f rs) := by
  have := roll_gate_rel A UsesRel (fun r f => some (bump f r)) layer2 swPutB (A 0) (swS2 BL TOPO REV) rs f N
    (bumps f rs) (fun r _ f N f' hR hf => by
      simp only [Option.some.injEq] at hf
      subst hf
      exact sw_putg BL TOPO REV r N f hR) h (by rw [foldlM_some]; rfl)
  rw [← listNoun_map_listN] at this
  exact this

/-- The subject of the gate of the `+rep:by`: `[swRepG [[[o b] acc] [put S2]]]`. -/
def swRG (o : Nat) (bN ACC BL TOPO REV : Noun) : Noun :=
  C swRepG (C (C (C (A o) bN) ACC) (C (swPC BL TOPO REV) (swS2 BL TOPO REV)))

/-- **The gate of the `+roll` over the ops**: `+get-regs` of the op, then
the gate `put` rolled over them. -/
theorem sw_opg (o : Nat) (bN ACC0 ACC1 BL TOPO REV : Noun) (op : Pole) (N : Noun) (f : Nat → Nat)
    (h : UsesRel N f) :
    ∃ N', nock (C swOpG (C (C op.toNoun N) (swRG o bN ACC1 BL TOPO REV))) swOpG = some N' ∧
      UsesRel N' (bumps f (Opt.poleRegs op)) := by
  obtain ⟨N', hr, hR⟩ := sw_roll_put BL TOPO REV (Opt.poleRegs op) N f h
  refine ⟨N', ?_, hR⟩
  have hL := optC_layer2
  have hT := optC_types
  have hgr := gr_at
  have hgp := gr_gate_pole op
  unfold swRG swPC swS2 swG at *
  generalize optC = OC at hL hT hr
  generalize compTypes = CT at hT hgr hgp
  simp [nock_exec, swOpG, hL, hT, hgr, gr_arm, hgp, roll.arm_at, roll_arm, hr]

theorem bumps_flatMap : ∀ (ops : List Pole) (f : Nat → Nat),
    ops.foldl (fun f op => bumps f (Opt.poleRegs op)) f = bumps f (ops.flatMap Opt.poleRegs)
  | [], f => rfl
  | op :: ops, f => by
    rw [List.foldl_cons, bumps_flatMap ops, List.flatMap_cons, bumps_append]

/-- **The gate of the `+rep:by`** on a block whose terminator is not `%lti`:
every register the block mentions counted once more. -/
theorem sw_repg (BL TOPO REV : Noun) (o : Nat) (b : Blob) (hb : finPlain b.fin = true) (N : Noun)
    (f : Nat → Nat) (h : UsesRel N f) :
    ∃ N', nock (swRG o b.toNoun N BL TOPO REV) swRepG = some N' ∧ UsesRel N' (bumps f (Opt.blobMentions b)) := by
  obtain ⟨N0, hr0, hR0⟩ := sw_roll_put BL TOPO REV b.par N f h
  obtain ⟨N1, hr1, hR1⟩ := sw_roll_put BL TOPO REV (Opt.finRegs b.fin) N0 _ hR0
  have hroll := roll_gate_rel Pole.toNoun UsesRel (fun op f => some (bumps f (Opt.poleRegs op))) layer2 swOpG
    poleBunt (swRG o b.toNoun N1 BL TOPO REV) b.body
    (bumps (bumps f b.par) (Opt.finRegs b.fin)) N1
    (bumps f (Opt.blobMentions b)) (fun op _ g M g' hR hf => by
      simp only [Option.some.injEq] at hf
      subst hf
      exact sw_opg o b.toNoun N1 N1 BL TOPO REV op M g hR) hR1 (by
      rw [foldlM_some, bumps_flatMap]
      simp [Opt.blobMentions, bumps_append])
  obtain ⟨N2, hr2, hR2⟩ := hroll
  refine ⟨N2, ?_, hR2⟩
  rw [← listNoun_map_listN] at hr2
  have hL := optC_layer2
  have hT := optC_types
  have hgr := gr_at
  have hgf := gr_gate_fin b.fin hb
  have hpm := pole_mold_at
  have hpg := pole_gate
  have hps := pole_gate_bat
  have hpb := pole_bunt'
  unfold swRG swPC swS2 swG at *
  obtain ⟨par, body, fin⟩ := b
  simp only [Blob.toNoun] at hr0 hr1 hr2 ⊢
  generalize optC = OC at hL hT hr0 hr1 hr2
  generalize compTypes = CT at hT hgr hgf hpm hpg
  generalize poleGateBat = PB at hps hpb
  generalize poleGate = PG at hpg hps hpb
  conv => lhs; arg 2; unfold swRepG
  simp [nock_exec, hL, hT, hgr, gr_arm, hgf, roll.arm_at, roll_arm, hr0, hr1, hr2, hpm, hpg, hps, hpb]

/-! ## `uses` -/

theorem flatMap_keys_rap (bl : TreapMap mugF Blob) :
    (Opt.MapKeys.keys bl).flatMap (fun o => ((HoonMap.get bl o).map Opt.blobMentions).getD [])
      = (TreapMap.rap bl).flatMap (fun p => Opt.blobMentions p.2) := by
  rw [optKeys_eq, List.flatMap_map]
  have e : ∀ L : List (Nat × Blob), (∀ p ∈ L, HoonMap.get bl p.1 = some p.2) →
      L.flatMap (fun p => ((HoonMap.get bl p.1).map Opt.blobMentions).getD [])
        = L.flatMap (fun p => Opt.blobMentions p.2) := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons p L ih =>
      intro hL
      rw [List.flatMap_cons, List.flatMap_cons, hL p (by simp), ih (fun q hq => hL q (by simp [hq]))]
      rfl
  exact e _ (rap_get bl)

/-- The counts of the model are those of `usesOf`. -/
theorem bumps_usesOf (bl : TreapMap mugF Blob) :
    (TreapMap.rap bl).foldl (fun f p => bumps f (Opt.blobMentions p.2)) (fun _ => 0) = Opt.usesOf bl := by
  funext r
  have e : ∀ (L : List (Nat × Blob)) (f : Nat → Nat),
      L.foldl (fun f p => bumps f (Opt.blobMentions p.2)) f = bumps f (L.flatMap fun p => Opt.blobMentions p.2) := by
    intro L
    induction L with
    | nil => intro f; rfl
    | cons p L ih => intro f; rw [List.foldl_cons, ih, List.flatMap_cons, bumps_append]
  rw [e, bumps_apply, Opt.usesOf, flatMap_keys_rap]
  simp

/-- **`uses`** on the noun of a treap of blocks with no `%lti`: a map
related to `usesOf`. -/
theorem sw_uses (bl : TreapMap mugF Blob) (hl : NoLti bl) (TOPO REV : Noun) :
    ∃ U, nock (swS2 (HoonMap.toNoun Blob.toNoun bl) TOPO REV) swUses = some U ∧ UsesRel U (Opt.usesOf bl) := by
  have ha : Tree (HoonMap.toNoun Blob.toNoun bl) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bl.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bl) = (TreapMap.rap bl).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bl
  have h := rep_gate_rel (Tr.pairNoun Blob.toNoun) UsesRel (fun p f => some (bumps f (Opt.blobMentions p.2)))
    by.battery layer2 swRepG (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))))
    (C (swPC (HoonMap.toNoun Blob.toNoun bl) TOPO REV) (swS2 (HoonMap.toNoun Blob.toNoun bl) TOPO REV))
    _ ha _ hP (fun _ => 0) (Opt.usesOf bl) (A 0) (by rw [foldlM_some, bumps_usesOf]) usesRel_nil
    (fun p hp f N f' hR hf => by
      simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨o, b⟩ := p
      exact sw_repg (HoonMap.toNoun Blob.toNoun bl) TOPO REV o b (hl o b (rap_get bl _ hp)) N f hR)
  obtain ⟨U, hU, hR⟩ := h
  refine ⟨U, ?_, hR⟩
  have hb : C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (A 0) = swRepB := rfl
  rw [hb] at hU
  have hL := optC_layer2
  unfold swPC swS2 swG at *
  generalize optC = OC at hL hU
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hU
  simp [nock_exec, swUses, hL, by.arm_at, by_arm, by.rep.arm_at, rep_arm, hU]

end Compiler
end Formalization
