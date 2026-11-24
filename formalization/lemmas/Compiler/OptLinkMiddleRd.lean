import lemmas.Compiler.OptLinkMiddleGate
import lemmas.Hoon.MapFolds

/-!
# `+remove-empty-middle`: `readers`

`readers` is `~` unless some block is empty, has parameters and ends in a
`%hop` (`+any:by` with the test `remAnyG`); then it is the `+rep:by` over the
blocks with the gate `remRdG`, which puts the block's label under every
register `+get-regs` names in its terminator and its ops (`+put:ju`, the gate
`remPutG`, rolled over the registers; the gate `remOpG` rolled over the
ops).  The model reads `readersOf` (`Ska/OptMiddle.lean`), the labels whose
blocks mention a register.

* `JugRel J f`: the noun `J` is a map whose set at every register `p` is a
  set of atoms with the members of `f p`.
* `jug_put`: `+put:ju` against `updL`.
* `rd_step`: the gate of the `+rep:by` against `rdStep`, which adds the
  block's label under the registers of `blobRegs`.
* `rd_readers`: **the computation of `readers` returns a noun with `RdOK`**,
  on treaps of blocks with no `%lti`.
* `rem_gate`: **where `removeEmptyMiddle fuel` returns `(changed, new)` on a
  treap of blocks with no `%lti`, the gate of `+remove-empty-middle` returns
  `[changed new]`.**
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Jugs of registers to labels -/

/-- The noun `J` is a map whose set at every register `p` holds the atoms of
`f p`. -/
def JugRel (J : Noun) (f : Nat → List Nat) : Prop :=
  IsMap mugF J ∧ ∀ p, ∃ out, getF mugF (A p) J = some out ∧ SawRel (unUnit out) (f p)

theorem jugRel_nil : JugRel (A 0) (fun _ => []) := ⟨IsMap.nil, fun p => ⟨A 0, rfl, sawRel_nil⟩⟩

/-- The label `o` added under the register `r`. -/
def updL (f : Nat → List Nat) (r o : Nat) : Nat → List Nat := fun p => if p = r then o :: f p else f p

/-- **`+put:ju`** of a register and a label. -/
theorem jug_put {J : Noun} {f : Nat → List Nat} (h : JugRel J f) (r o : Nat) :
    ∃ J', nock (C ju.put.battery (C (C (A r) (A o)) (C ju.battery (C J layer2)))) ju.put.battery = some J' ∧
      JugRel J' (updL f r o) := by
  obtain ⟨out, hg, hS⟩ := h.2 r
  obtain ⟨e, hpe, hse, hhe⟩ := putInF_spec mugF (unUnit out) (A o) hS.1
  obtain ⟨J', hpJ, hmJ, hgJ⟩ := putF_spec mugF J (A r) e h.1
  have hj : juPutF mugF (A r) (A o) J = some J' := by
    simp [juPutF, juGetF, hg, hpe, hpJ]
  refine ⟨J', ju_put_gate layer2 juIn_layer2' _ _ _ _ hj, hmJ, fun p => ?_⟩
  have hga := getF_after_put h.1 hmJ hgJ (A p)
  by_cases e1 : p = r
  · subst e1
    refine ⟨C (A 0) e, by simp [hga], hse, fun k => ?_⟩
    simp only [unUnit] at *
    rw [hhe, hS.2 k]
    simp only [updL, if_true, List.mem_cons]
    constructor
    · rintro (rfl | ⟨n, hn, rfl⟩)
      · exact ⟨o, Or.inl rfl, rfl⟩
      · exact ⟨n, Or.inr hn, rfl⟩
    · rintro ⟨n, rfl | hn, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨n, hn, rfl⟩
  · obtain ⟨out', hg', hS'⟩ := h.2 p
    have hne : A p ≠ A r := fun e => e1 (Noun.atom.inj e)
    refine ⟨out', by rw [hga, if_neg hne, hg'], ?_⟩
    simpa [updL, e1] using hS'

/-- `updL` over a list of registers. -/
def updLs (f : Nat → List Nat) (rs : List Nat) (o : Nat) : Nat → List Nat := rs.foldl (fun f r => updL f r o) f

theorem updLs_cons (f : Nat → List Nat) (r : Nat) (rs : List Nat) (o : Nat) :
    updLs f (r :: rs) o = updLs (updL f r o) rs o := rfl

theorem updLs_append (f : Nat → List Nat) (rs rs' : List Nat) (o : Nat) :
    updLs f (rs ++ rs') o = updLs (updLs f rs o) rs' o := by
  simp [updLs, List.foldl_append]

/-! ## The gates of the `+rep:by` that makes `readers` -/

/-- The subject of the gate of the `+rep:by`: `[remRdG [[[o b] acc] [remBody [blocks optC]]]]`. -/
def rdRG (o : Nat) (bN ACC BL : Noun) : Noun := C remRdG (C (C (C (A o) bN) ACC) (C remBody (C BL optC)))

/-- **The gate `put`**: `+put:ju` of the register and the label `o`. -/
theorem rd_putg (o : Nat) (bN ACC BL : Noun) (r : Nat) (N : Noun) (f : Nat → List Nat) (h : JugRel N f) :
    ∃ N', nock (C remPutG (C (C (A r) N) (rdRG o bN ACC BL))) remPutG = some N' ∧ JugRel N' (updL f r o) := by
  obtain ⟨J', hj, hJ'⟩ := jug_put h r o
  refine ⟨J', ?_, hJ'⟩
  have hL := optC_layer2
  unfold rdRG
  generalize optC = OC at hL
  simp [nock_exec, remPutG, hL, ju.arm_at, ju_arm, ju.put.arm_at, ju_put_arm, hj]

/-- `+roll` of the gate `put` over a list of registers. -/
theorem rd_roll_put (o : Nat) (bN ACC BL : Noun) (rs : List Nat) (N : Noun) (f : Nat → List Nat)
    (h : JugRel N f) :
    ∃ N', nock (C roll.battery (C (C (listNoun A rs) (C remPutG (C (C (A 0) N) (rdRG o bN ACC BL)))) layer2))
      roll.battery = some N' ∧ JugRel N' (updLs f rs o) := by
  have := roll_gate_rel A JugRel (fun r f => some (updL f r o)) layer2 remPutG (A 0) (rdRG o bN ACC BL) rs f N
    (updLs f rs o) (fun r _ f N f' hR hf => by
      simp only [Option.some.injEq] at hf
      subst hf
      exact rd_putg o bN ACC BL r N f hR) h (by rw [foldlM_some]; rfl)
  rw [← listNoun_map_listN] at this
  exact this

/-- The core of the gate `put` as the gate of the `+rep:by` builds it. -/
def rdPG (o : Nat) (bN ACC BL : Noun) : Noun := C remPutG (C (C (A 0) (A 0)) (rdRG o bN ACC BL))

/-- **The gate of the `+roll` over the ops**: `+get-regs` of the op, then the
gate `put` rolled over them. -/
theorem rd_opg (o : Nat) (bN ACC0 ACC1 BL : Noun) (op : Pole) (N : Noun) (f : Nat → List Nat) (h : JugRel N f) :
    ∃ N', nock (C remOpG (C (C op.toNoun N) (C (rdPG o bN ACC0 BL) (rdRG o bN ACC1 BL)))) remOpG = some N' ∧
      JugRel N' (updLs f (Opt.poleRegs op) o) := by
  obtain ⟨N', hr, hR⟩ := rd_roll_put o bN ACC0 BL (Opt.poleRegs op) N f h
  refine ⟨N', ?_, hR⟩
  have hL := optC_layer2
  have hT := optC_types
  have hgr := gr_at
  have hgp := gr_gate_pole op
  unfold rdPG rdRG at *
  generalize optC = OC at hL hT hr
  generalize compTypes = CT at hT hgr hgp
  simp [nock_exec, remOpG, hL, hT, hgr, gr_arm, hgp, roll.arm_at, roll_arm, hr]

theorem updLs_flatMap (o : Nat) : ∀ (ops : List Pole) (f : Nat → List Nat),
    ops.foldl (fun f op => updLs f (Opt.poleRegs op) o) f = updLs f (ops.flatMap Opt.poleRegs) o
  | [], f => rfl
  | op :: ops, f => by
    rw [List.foldl_cons, updLs_flatMap o ops, List.flatMap_cons, updLs_append]

/-- The step of the model of `readers`: the label `o` under every register
its block mentions. -/
def rdStep (f : Nat → List Nat) (p : Nat × Blob) : Nat → List Nat := updLs f (Opt.blobRegs p.2) p.1

/-- **The gate of the `+rep:by` that makes `readers`** on a block whose
terminator is not `%lti`. -/
theorem rd_step (BL : Noun) (o : Nat) (b : Blob) (hb : finPlain b.fin = true) (N : Noun) (f : Nat → List Nat)
    (h : JugRel N f) :
    ∃ N', nock (rdRG o b.toNoun N BL) remRdG = some N' ∧ JugRel N' (rdStep f (o, b)) := by
  obtain ⟨N1, hr1, hR1⟩ := rd_roll_put o b.toNoun N BL (Opt.finRegs b.fin) N f h
  have hroll := roll_gate_rel Pole.toNoun JugRel (fun op f => some (updLs f (Opt.poleRegs op) o)) layer2 remOpG
    poleBunt (C (rdPG o b.toNoun N BL) (rdRG o b.toNoun N1 BL)) b.body (updLs f (Opt.finRegs b.fin) o) N1
    (rdStep f (o, b)) (fun op _ g M g' hR hf => by
      simp only [Option.some.injEq] at hf
      subst hf
      exact rd_opg o b.toNoun N N1 BL op M g hR) hR1 (by
      rw [foldlM_some, updLs_flatMap]
      simp [rdStep, Opt.blobRegs, updLs_append])
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
  unfold rdPG at hr2
  unfold rdRG at *
  obtain ⟨par, body, fin⟩ := b
  simp only [Blob.toNoun] at hr1 hr2 ⊢
  generalize optC = OC at hL hT hr1 hr2
  generalize compTypes = CT at hT hgr hgf hpm hpg
  generalize poleGateBat = PB at hps hpb
  generalize poleGate = PG at hpg hps hpb
  conv => lhs; arg 2; unfold remRdG
  simp [nock_exec, hL, hT, hgr, gr_arm, hgf, roll.arm_at, roll_arm, hr1, hr2, hpm, hpg, hps, hpb, remBuntF]

/-! ## The `+rep:by` that makes `readers` -/

/-- The model of `readers`, as lists. -/
def rdF (L : List (Nat × Blob)) : Nat → List Nat := L.foldl rdStep (fun _ => [])

theorem mem_updLs (f : Nat → List Nat) (o : Nat) : ∀ (rs : List Nat) (p x : Nat),
    x ∈ updLs f rs o p ↔ x ∈ f p ∨ (x = o ∧ p ∈ rs)
  | [], p, x => by simp [updLs]
  | r :: rs, p, x => by
    rw [updLs_cons, mem_updLs (updL f r o) o rs p x]
    unfold updL
    by_cases e : p = r
    · subst e; by_cases hx : x = o <;> simp [hx]
    · simp [e]

theorem mem_rdF_gen : ∀ (L : List (Nat × Blob)) (f : Nat → List Nat) (p x : Nat),
    x ∈ L.foldl rdStep f p ↔ x ∈ f p ∨ ∃ b, (x, b) ∈ L ∧ p ∈ Opt.blobRegs b
  | [], f, p, x => by simp
  | q :: L, f, p, x => by
    rw [List.foldl_cons, mem_rdF_gen L (rdStep f q) p x]
    unfold rdStep
    rw [mem_updLs]
    obtain ⟨o, b⟩ := q
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨b', h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨b, List.mem_cons_self, h⟩
      · exact Or.inr ⟨b', List.mem_cons_of_mem _ h1, h2⟩
    · rintro (h | ⟨b', h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 h1 with e | h1
        · simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact Or.inl (Or.inr ⟨rfl, h2⟩)
        · exact Or.inr ⟨b', h1, h2⟩

/-- The rep of `readers` on the noun of a treap of blocks with no `%lti`. -/
theorem rd_rep (bl : TreapMap mugF Blob) (hl : NoLti bl) :
    ∃ RD, nock (C by.rep.battery (C (C remRdG (C remRdB (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC))))
        (C by.battery (C (HoonMap.toNoun Blob.toNoun bl) layer2)))) by.rep.battery = some RD ∧
      JugRel RD (rdF (TreapMap.rap bl)) := by
  have ha : Tree (HoonMap.toNoun Blob.toNoun bl) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bl.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bl) = (TreapMap.rap bl).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bl
  have h := rep_gate_rel (Tr.pairNoun Blob.toNoun) JugRel (fun p f => some (rdStep f p)) by.battery layer2 remRdG
    (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC))
    _ ha _ hP (fun _ => []) (rdF (TreapMap.rap bl)) (A 0) (by rw [foldlM_some]; rfl) jugRel_nil
    (fun p hp f N f' hR hf => by
      simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨o, b⟩ := p
      exact rd_step (HoonMap.toNoun Blob.toNoun bl) o b (hl o b (rap_get bl _ hp)) N f hR)
  have hb : C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (A 0) = remRdB := by
    simp [remRdB, remAnyB]
  rw [hb] at h
  exact h

/-! ## The test of the `+any:by` -/

/-- The test: an empty block with parameters that ends in a `%hop`. -/
def anyTest (b : Blob) : Bool :=
  !b.par.isEmpty && b.body.isEmpty && match b.fin with | Termin.hop _ => true | _ => false

theorem rem_anyg (b : Blob) (ctx : Noun) :
    nock (C remAnyG (C b.toNoun ctx)) remAnyG = some (loob (anyTest b)) := by
  obtain ⟨par, body, fin⟩ := b
  cases par <;> cases body <;> cases fin <;>
    simp [nock_exec, remAnyG, Blob.toNoun, Termin.toNoun, listNoun, anyTest, loob, Tag.hop, Tag.clq, Tag.eqq,
      Tag.brn, Tag.brz, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-- `+any:by` over a treap of blocks, in the order of its loop. -/
def anyT (g : Blob → Bool) : Tr Blob → Bool
  | Tr.nil => false
  | Tr.node _ v l r => g v || anyT g l || anyT g r

theorem any_loop_tr (B ctx fp fs fc : Noun) (g : Blob → Bool)
    (hg : ∀ b : Blob, nock (C fp (C b.toNoun fc)) fp = some (loob (g b))) :
    ∀ t : Tr Blob, nock (C by.any.loop (C by.any.battery (C (C fp (C fs fc)) (C B (C (t.toNoun Blob.toNoun) ctx)))))
      by.any.loop = some (loob (anyT g t))
  | Tr.nil => by nock_open by.any.loop; simp [nock_exec, Tr.toNoun, anyT, loob]
  | Tr.node k v l r => by
    have hl := any_loop_tr B ctx fp fs fc g hg l
    have hr := any_loop_tr B ctx fp fs fc g hg r
    nock_open by.any.loop
    cases e1 : g v <;> cases e2 : anyT g l <;> cases e3 : anyT g r <;>
      simp [nock_exec, Tr.toNoun, anyT, hg, e1, e2, e3, hl, hr, loob]

theorem anyT_iff (g : Blob → Bool) : ∀ t : Tr Blob, anyT g t = true ↔ ∃ p ∈ t.pre, g p.2 = true
  | Tr.nil => by simp [anyT, Tr.pre]
  | Tr.node k v l r => by
    simp only [anyT, Tr.pre, Bool.or_eq_true, anyT_iff g l, anyT_iff g r, List.mem_cons, List.mem_append]
    constructor
    · rintro ((h | ⟨p, hp, h⟩) | ⟨p, hp, h⟩)
      · exact ⟨(k, v), Or.inl rfl, h⟩
      · exact ⟨p, Or.inr (Or.inl hp), h⟩
      · exact ⟨p, Or.inr (Or.inr hp), h⟩
    · rintro ⟨p, rfl | hp | hp, h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨p, hp, h⟩)
      · exact Or.inr ⟨p, hp, h⟩

theorem any_gate_tr (B ctx fp fs fc : Noun) (g : Blob → Bool)
    (hg : ∀ b : Blob, nock (C fp (C b.toNoun fc)) fp = some (loob (g b))) (t : Tr Blob) :
    nock (C by.any.battery (C (C fp (C fs fc)) (C B (C (t.toNoun Blob.toNoun) ctx)))) by.any.battery
      = some (loob (anyT g t)) := by
  nock_open by.any.battery
  simp only [nock_exec, any_loop_tr B ctx fp fs fc g hg t]

/-! ## `readers` -/

theorem sawRel_congr {S : Noun} {l l' : List Nat} (h : SawRel S l) (e : ∀ x, x ∈ l ↔ x ∈ l') : SawRel S l' :=
  ⟨h.1, fun k => by rw [h.2 k]; simp only [e]⟩

theorem mem_readersOf (bl : TreapMap mugF Blob) (p x : Nat) :
    x ∈ Opt.readersOf bl p ↔ ∃ b, HoonMap.get bl x = some b ∧ p ∈ Opt.blobRegs b := by
  unfold Opt.readersOf
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    cases e : HoonMap.get bl x with
    | none => rw [e] at h; simp at h
    | some b => rw [e] at h; exact ⟨b, rfl, by simpa using h⟩
  · rintro ⟨b, hb, hp⟩
    refine ⟨(Opt.MapKeys.mem_keys bl x).2 (by rw [hb]; rfl), ?_⟩
    rw [hb]; simpa using hp

/-- **`readers`**: on a treap of blocks with no `%lti`, its computation
returns a noun with `RdOK`. -/
theorem rd_readers (bl : TreapMap mugF Blob) (hl : NoLti bl) :
    ∃ RD, nock (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) remReaders = some RD ∧ RdOK bl RD := by
  have hL := optC_layer2
  have hany := any_gate_tr by.battery layer2 remAnyG remAnyB (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC))
    anyTest (fun b => rem_anyg b _) bl.1
  rw [← hoonMap_toNoun] at hany
  obtain ⟨RD, hrep, hJ⟩ := rd_rep bl hl
  have hanyA : ∀ c, nock c by.any.arm = some (C by.any.battery (C (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0)))) c)) := by
    intro c; nock_open by.any.arm; simp only [nock_exec]
  cases ht : anyT anyTest bl.1 with
  | true =>
    refine ⟨RD, ?_, ?_⟩
    · rw [ht] at hany
      conv => lhs; arg 2; unfold remReaders
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hany hrep
      generalize optC = OC at hL hany hrep
      simp [nock_exec, hL, by.arm_at, by_arm, by.any.arm_at, hanyA, hany, loob, by.rep.arm_at, rep_arm, hrep]
    · intro o nex t p hnex hb hf hp
      obtain ⟨out, hg, hS⟩ := hJ.2 p
      refine ⟨out, hg, sawRel_congr hS fun x => ?_⟩
      rw [rdF, mem_rdF_gen, mem_readersOf]
      simp only [List.not_mem_nil, false_or]
      constructor
      · rintro ⟨b, hb', hp'⟩; exact ⟨b, (TreapMap.mem_rap bl x b).1 hb', hp'⟩
      · rintro ⟨b, hb', hp'⟩; exact ⟨b, (TreapMap.mem_rap bl x b).2 hb', hp'⟩
  | false =>
    refine ⟨A 0, ?_, ?_⟩
    · rw [ht] at hany
      conv => lhs; arg 2; unfold remReaders
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hany hrep
      generalize optC = OC at hL hany hrep
      simp [nock_exec, hL, by.arm_at, by_arm, by.any.arm_at, hanyA, hany, loob]
    · intro o nex t p hnex hb hf hp
      exfalso
      have hm : (o, nex) ∈ bl.1.pre := (TreapMap.mem_rap bl o nex).2 hnex
      have : anyT anyTest bl.1 = true := (anyT_iff anyTest bl.1).2 ⟨(o, nex), hm, by
        obtain ⟨par, body, fin⟩ := nex
        simp only at hb hf hp
        subst hb; subst hf
        cases par with
        | nil => simp at hp
        | cons _ _ => rfl⟩
      rw [ht] at this
      cases this

/-! ## The gate -/

/-- **`+remove-empty-middle`**: where `removeEmptyMiddle fuel` returns
`(changed, new)` on a treap of blocks with no `%lti`, the gate returns
`[changed new]`. -/
theorem rem_gate (bl : TreapMap mugF Blob) (hl : NoLti bl) (fuel : Nat) (r : Bool × TreapMap mugF Blob)
    (h : Opt.removeEmptyMiddle fuel bl = some r) :
    nock (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) remBody = some (remN r) := by
  obtain ⟨RD, hRD, hR⟩ := rd_readers bl hl
  exact rem_gate_of bl fuel r h RD hRD hR

end Compiler
end Formalization
