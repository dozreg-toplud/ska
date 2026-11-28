import lemmas.Compiler.CompRunShapeSix
import lemmas.Compiler.CompRunShapeBranchCut
import lemmas.Compiler.CompLeapLazyGate

/-!
# The link of `+laze-branch` (track A, 2026-11-28)

`+laze-branch` (door arm `0x15576`, `lbrGate`, cut in `CompRunShapeBranchCut.lean`) against
`lazeBranch` of `Ska/RunShape.lean`, on every `laze` (forks and bonds to any depth), from every
state, under `CompIn ctx` and `K` at axis `7` of `ctx`.  The gate `+spin`s `lbrG1` over the
forks (four identifiers by `+id`, then the two recursive calls) and `lbrG2` over the bonds (two
identifiers, one recursive call), then gives both halves by `+turn` of `+head` and `+tail`.

* `lbr_arm`, `lbr_door`: the arm builds its gate.
* `lbrFE`, `lbrBE`: one fork and one bond of the model; `branchF_spin`, `branchB_spin`: the
  model's loops are `spinM` of them.
* The gates of the two `+spin`s, from the recursive call (`LbrAt`): `lbr_bstep` (one bond, in
  one `simp`), `lbr_fstep` (one fork, cut at its pushes `lbrF5`, `lbrF6`, `lbrF7`: `lbr_fA` the
  edit of `gen` and the four `+id`s, `lbr_fB` and `lbr_fC` the two recursive calls; in one `simp`
  the proof term was too big for the kernel).
* The gate in parts: `lbr_gate_split`, `lbr_s1` (the `+spin` over the forks, `spin_gate_T`),
  `lbr_r1`, `lbr_s2` (over the bonds), `lbr_r2` (the halves by `+turn` of `+head` / `+tail`).
* **`lbr_all`**: the gate on `laz` at the door `rsDoor st y ctx` is
  `(lazeBranch laz st).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (rsGenNoun p.2 y)`
  (mutual induction `lbr_allN`, `lbr_forks`, `lbr_bonds`).
* **`lbr_call`**: the call `[7 [0 1] 8 [9 0x15576 0 127] 9 2 10 [6 0 2037] 0 2]` of `rs6Kerf`,
  on a subject with the door at axis `127` and the `laze` at axis `1013`.
* **`lazeBranch_nz`**: both halves keep `LzNZ` (with `branchF_nz`, `branchB_nz`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

theorem lbr_arm (d : Noun) : nock d lbrArm = some (C lbrGate (C lbrBunt d)) := by
  unfold lbrArm; simp [nock_exec]

/-- The arm `+laze-branch` on the door gives the gate `lbrGate`. -/
theorem lbr_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0x15576) (C (A 0) (A 1))))
    = some (C lbrGate (C lbrBunt (C comp.door y))) := by
  simp [nock_exec, lbr_at', lbr_arm]

/-! ## The bunt of `laze` -/

/-- The bunt of `laze` from `K`: the mold at arm `0x575ee` of `K`, slammed on its own sample. -/
def lbrLzbF : Noun := C (A 7) (C (C (A 9) (C (A 0x575ee) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

noncomputable def lbrLzbV : Noun := (evalFuel 2000 compK lbrLzbF).getD (A 0)

theorem lbr_lzb : nock compK lbrLzbF = some lbrLzbV := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

theorem lbr_lb_at (T : Noun) (ax : Nat) (h : slot? ax T = some compK) :
    nock T (C (A 7) (C (C (A 9) (C (A 0x575ee) (C (A 0) (A ax)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
      = some lbrLzbV := by
  have hb := lbr_lzb
  unfold lbrLzbF at hb
  simp only [nock_op7, nock_op9, nock_op0, h, slot?_one, Option.bind_some] at hb ⊢
  exact hb

theorem lbr_lb1 (T : Noun) (h : slot? 127 T = some compK) : nock T lbrLb1 = some lbrLzbV := by
  unfold lbrLb1; exact lbr_lb_at T 127 h

theorem lbr_lb2 (T : Noun) (h : slot? 255 T = some compK) : nock T lbrLb2 = some lbrLzbV := by
  unfold lbrLb2; exact lbr_lb_at T 255 h

/-! ## The model, as `spinM` -/

/-- One fork of `+laze-branch`, in the model: four identifiers, then the two halves of each
branch. -/
noncomputable def lbrFE (e : (Nat × Laze CSet) × (Nat × Laze CSet)) :
    RSt CSet → Option ((((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet)))
      × RSt CSet) := fun s =>
  (lazeBranch e.1.2 { idg := s.idg + 1 + 1 + 1 + 1, sofs := s.sofs }).bind fun r =>
    (lazeBranch e.2.2 r.2).map fun q =>
      ((((s.idg, r.1.1), (s.idg + 1 + 1, q.1.1)), ((s.idg + 1, r.1.2), (s.idg + 1 + 1 + 1, q.1.2))), q.2)

/-- One bond of `+laze-branch`, in the model. -/
noncomputable def lbrBE (e : Nat × Laze CSet) :
    RSt CSet → Option (((Nat × Laze CSet) × (Nat × Laze CSet)) × RSt CSet) := fun s =>
  (lazeBranch e.2 { idg := s.idg + 1 + 1, sofs := s.sofs }).map fun r =>
    (((s.idg, r.1.1), (s.idg + 1, r.1.2)), r.2)

theorem branchF_spin : ∀ (f : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (st : RSt CSet),
    branchF f st = spinM lbrFE f st
  | [], st => rfl
  | ((oy, y), (on, n)) :: rest, st => by
    have ih := branchF_spin rest
    simp only [branchF, spinM, lbrFE, idS, bind, StateT.bind, pure, StateT.pure]
    cases e1 : lazeBranch y { idg := st.idg + 1 + 1 + 1 + 1, sofs := st.sofs } with
    | none => simp [e1]
    | some r =>
      obtain ⟨⟨y0, y1⟩, s1⟩ := r
      cases e2 : lazeBranch n s1 with
      | none => simp [e1, e2]
      | some q =>
        obtain ⟨⟨n0, n1⟩, s2⟩ := q
        cases e3 : spinM lbrFE rest s2 with
        | none => simp [e1, e2, e3, ih]
        | some t => simp [e1, e2, e3, ih]

theorem branchB_spin : ∀ (b : List (Nat × Laze CSet)) (st : RSt CSet),
    branchB b st = spinM lbrBE b st
  | [], st => rfl
  | (o, l) :: rest, st => by
    have ih := branchB_spin rest
    simp only [branchB, spinM, lbrBE, idS, bind, StateT.bind, pure, StateT.pure]
    cases e1 : lazeBranch l { idg := st.idg + 1 + 1, sofs := st.sofs } with
    | none => simp [e1]
    | some r =>
      obtain ⟨⟨l0, l1⟩, s1⟩ := r
      cases e3 : spinM lbrBE rest s1 with
      | none => simp [e1, e3, ih]
      | some t => simp [e1, e3, ih]

/-! ## The gate on every `laze` -/

/-- The noun of what `+laze-branch` returns. -/
noncomputable def lbrN (y : RsRest) (p : (Laze CSet × Laze CSet) × RSt CSet) : Noun :=
  C (C p.1.1.toNoun p.1.2.toNoun) (rsGenNoun p.2 y)

/-- The gate of `+laze-branch` on `l` is the model, from every state. -/
def LbrAt (ctx : Noun) (y : RsRest) (l : Laze CSet) : Prop :=
  ∀ st : RSt CSet, nock (C lbrGate (C l.toNoun (C comp.door (C (rsGenNoun st y) ctx)))) lbrGate
    = (lazeBranch l st).map (lbrN y)

/-- **One bond**: the gate of the `+spin` over the bonds, from the recursive call on the bond's
`laze`. -/
theorem lbr_bstep (y : RsRest) (o : Nat) (l : Laze CSet) (hl : LbrAt ctx y l) (s : RSt CSet) (FK L G0 : Noun) :
    nock (C lbrG2 (C (C (lzbE (o, l)) (rsGenNoun s y)) (C FK (C lbrGate (C L (C comp.door (C G0 ctx)))))))
      lbrG2 = (lbrBE (o, l) s).map fun r => C (C (lzbE r.1.1) (lzbE r.1.2)) (rsGenNoun r.2 y) := by
  have ihl := hl { idg := s.idg + 1 + 1, sofs := s.sofs }
  unfold lbrG2
  cases e1 : lazeBranch l { idg := s.idg + 1 + 1, sofs := s.sofs } with
  | none =>
    rw [e1] at ihl
    simp [nock_exec, lzbE, lzp_id_at', rs_id, lbr_at', lbr_arm, ihl, lbrBE, e1]
  | some r =>
    rw [e1] at ihl
    simp [nock_exec, lzbE, lzp_id_at', rs_id, lbr_at', lbr_arm, ihl, lbrBE, e1, lbrN]

/-- The subject of the fork gate after `=.  gen  gen-acc`: the gate, its sample `[e gs]`, the core
`[lbrGate [L door]]` with `gen` at `g`. -/
def lbrT (ctx E GS L g : Noun) : Noun := C lbrG1 (C (C E GS) (C lbrGate (C L (C comp.door (C g ctx)))))

/-- The fork gate up to the first recursive call: `=.  gen  gen-acc`, the four `+id`s. -/
theorem lbr_fA (y : RsRest) (E L G0 : Noun) (s : RSt CSet) :
    nock (lbrT ctx E (rsGenNoun s y) L G0) lbrG1
      = nock (C (A (s.idg + 1 + 1 + 1)) (C (A (s.idg + 1 + 1)) (C (A (s.idg + 1)) (C (A s.idg)
          (lbrT ctx E (rsGenNoun s y) L (rsGenNoun { idg := s.idg + 1 + 1 + 1 + 1, sofs := s.sofs } y))))))
        lbrF5 := by
  conv => lhs; arg 2; unfold lbrG1
  generalize lbrF5 = F
  simp [nock_exec, lzp_id_at', rs_id, lbrT]

/-- The first recursive call, on `laz.y`. -/
theorem lbr_fB (y : RsRest) (oy on : Nat) (yl nl : Laze CSet) (hy : LbrAt ctx y yl) (GS L : Noun)
    (a0 a1 a2 a3 : Nat) (st : RSt CSet) :
    nock (C (A a3) (C (A a2) (C (A a1) (C (A a0)
        (lbrT ctx (C (C (A oy) yl.toNoun) (C (A on) nl.toNoun)) GS L (rsGenNoun st y)))))) lbrF5
      = (lazeBranch yl st).bind fun r => nock (C (C r.1.1.toNoun r.1.2.toNoun) (C (A a3) (C (A a2) (C (A a1)
          (C (A a0) (lbrT ctx (C (C (A oy) yl.toNoun) (C (A on) nl.toNoun)) GS L (rsGenNoun r.2 y))))))) lbrF6 := by
  have h := hy st
  conv => lhs; arg 2; unfold lbrF5
  generalize lbrF6 = F
  cases e : lazeBranch yl st with
  | none =>
    rw [e] at h
    simp [nock_exec, lbr_at', lbr_arm, lbrT, h]
  | some r =>
    rw [e] at h
    simp [nock_exec, lbr_at', lbr_arm, lbrT, h, lbrN]

/-- The second recursive call, on `laz.n`, and the product. -/
theorem lbr_fC (y : RsRest) (oy on : Nat) (yl nl : Laze CSet) (hn : LbrAt ctx y nl) (GS L Y0 Y1 : Noun)
    (a0 a1 a2 a3 : Nat) (st : RSt CSet) :
    nock (C (C Y0 Y1) (C (A a3) (C (A a2) (C (A a1) (C (A a0)
        (lbrT ctx (C (C (A oy) yl.toNoun) (C (A on) nl.toNoun)) GS L (rsGenNoun st y))))))) lbrF6
      = (lazeBranch nl st).map fun q => C (C (C (C (A a0) Y0) (C (A a2) q.1.1.toNoun))
          (C (C (A a1) Y1) (C (A a3) q.1.2.toNoun))) (rsGenNoun q.2 y) := by
  have h := hn st
  conv => lhs; arg 2; unfold lbrF6
  cases e : lazeBranch nl st with
  | none =>
    rw [e] at h
    simp [nock_exec, lbr_at', lbr_arm, lbrT, h]
  | some r =>
    rw [e] at h
    simp [nock_exec, lbr_at', lbr_arm, lbrT, h, lbrN, lbrF7]

/-- **One fork**: the gate of the `+spin` over the forks, from the recursive calls on the
`laze`s of both branches. -/
theorem lbr_fstep (y : RsRest) (oy on : Nat) (yl nl : Laze CSet) (hy : LbrAt ctx y yl) (hn : LbrAt ctx y nl)
    (s : RSt CSet) (L G0 : Noun) :
    nock (C lbrG1 (C (C (lzfE ((oy, yl), (on, nl))) (rsGenNoun s y)) (C lbrGate (C L (C comp.door (C G0 ctx))))))
      lbrG1 = (lbrFE ((oy, yl), (on, nl)) s).map fun r => C (C (lzfE r.1.1) (lzfE r.1.2)) (rsGenNoun r.2 y) := by
  have hA := lbr_fA (ctx := ctx) y (lzfE ((oy, yl), (on, nl))) L G0 s
  unfold lbrT at hA
  rw [hA]
  simp only [lzfE]
  rw [show C lbrG1 (C (C (C (C (A oy) yl.toNoun) (C (A on) nl.toNoun)) (rsGenNoun s y)) (C lbrGate (C L (C comp.door
      (C (rsGenNoun { idg := s.idg + 1 + 1 + 1 + 1, sofs := s.sofs } y) ctx)))))
      = lbrT ctx (C (C (A oy) yl.toNoun) (C (A on) nl.toNoun)) (rsGenNoun s y) L
          (rsGenNoun { idg := s.idg + 1 + 1 + 1 + 1, sofs := s.sofs } y) from rfl]
  rw [lbr_fB y oy on yl nl hy]
  unfold lbrFE
  simp only
  cases e1 : lazeBranch yl { idg := s.idg + 1 + 1 + 1 + 1, sofs := s.sofs } with
  | none => rfl
  | some r =>
    simp only [Option.bind_some]
    rw [lbr_fC y oy on yl nl hn]
    cases lazeBranch nl r.2 <;> rfl

/-! ## The gate -/

/-- The gate's core on `[sur fk bd]`, with `gen` at `g`. -/
noncomputable def lbrS (ctx : Noun) (sur : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (g : Noun) : Noun :=
  C lbrGate (C (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C g ctx)))

theorem lbr_gate_split (S : Noun) : nock S lbrGate = (nock S lbrS1).bind fun P => nock (C P S) lbrR1 := by
  conv => lhs; arg 2; unfold lbrGate
  generalize lbrS1 = F
  generalize lbrR1 = G
  simp [nock_exec]

/-- The `+spin` over the forks. -/
theorem lbr_s1 (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (y : RsRest) (sur : SureO CSet)
    (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) (st : RSt CSet)
    (hF : ∀ e ∈ fk, ∀ (s : RSt CSet) (L G0 : Noun),
      nock (C lbrG1 (C (C (lzfE e) (rsGenNoun s y)) (C lbrGate (C L (C comp.door (C G0 ctx)))))) lbrG1
        = (lbrFE e s).map fun r => C (C (lzfE r.1.1) (lzfE r.1.2)) (rsGenNoun r.2 y)) :
    nock (lbrS ctx sur fk bd (rsGenNoun st y)) lbrS1
      = (branchF fk st).map fun r => C (listN (r.1.map fun x => C (lzfE x.1) (lzfE x.2))) (rsGenNoun r.2 y) := by
  have hsp := spin_arm_l2
  rw [spin_gate_eq] at hsp
  have hs1 := spin.arm_at
  have hSpin := spin_gate_T lzfE
    (fun x : ((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet)) =>
      C (lzfE x.1) (lzfE x.2)) (fun s => rsGenNoun s y) layer2 spinIn_layer2
    lbrG1 (C (C (C (A 0) lbrLzbV) (C (A 0) lbrLzbV)) (rsGenNoun st y)) (lbrS ctx sur fk bd (rsGenNoun st y))
    lbrFE fk st (fun e he s => by unfold lbrS; exact hF e he s _ _)
  rw [← branchF_spin] at hSpin
  have hb := lbr_lb1 (lbrS ctx sur fk bd (rsGenNoun st y)) (by simp [lbrS, nock_exec, h7])
  unfold lbrS at hSpin hb ⊢
  conv => lhs; arg 2; unfold lbrS1
  generalize lbrG1 = G1 at hSpin ⊢
  simp [nock_exec, lbrBF1, hb, hc, hs1, spin.axis, hsp, hSpin]

/-- The edit of `gen` after the first `+spin`, then the second and the rest. -/
theorem lbr_r1 (sur : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (FN G0 G1 : Noun) :
    nock (C (C FN G1) (lbrS ctx sur fk bd G0)) lbrR1
      = (nock (C FN (lbrS ctx sur fk bd G1)) lbrS2).bind fun P => nock (C P (C FN (lbrS ctx sur fk bd G1))) lbrR2 := by
  conv => lhs; arg 2; unfold lbrR1
  generalize lbrS2 = F
  generalize lbrR2 = G
  simp [nock_exec, lbrS]

/-- The `+spin` over the bonds. -/
theorem lbr_s2 (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (y : RsRest) (sur : SureO CSet)
    (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) (st : RSt CSet) (FN : Noun)
    (hB : ∀ e ∈ bd, ∀ (s : RSt CSet) (FK L G0 : Noun),
      nock (C lbrG2 (C (C (lzbE e) (rsGenNoun s y)) (C FK (C lbrGate (C L (C comp.door (C G0 ctx)))))))
        lbrG2 = (lbrBE e s).map fun r => C (C (lzbE r.1.1) (lzbE r.1.2)) (rsGenNoun r.2 y)) :
    nock (C FN (lbrS ctx sur fk bd (rsGenNoun st y))) lbrS2
      = (branchB bd st).map fun r => C (listN (r.1.map fun x => C (lzbE x.1) (lzbE x.2))) (rsGenNoun r.2 y) := by
  have hsp := spin_arm_l2
  rw [spin_gate_eq] at hsp
  have hs1 := spin.arm_at
  have hSpin := spin_gate_T lzbE
    (fun x : (Nat × Laze CSet) × (Nat × Laze CSet) => C (lzbE x.1) (lzbE x.2)) (fun s => rsGenNoun s y) layer2
    spinIn_layer2 lbrG2 (C (C (A 0) lbrLzbV) (rsGenNoun st y)) (C FN (lbrS ctx sur fk bd (rsGenNoun st y)))
    lbrBE bd st (fun e he s => by unfold lbrS; exact hB e he s _ _ _)
  rw [← branchB_spin] at hSpin
  have hb := lbr_lb2 (C FN (lbrS ctx sur fk bd (rsGenNoun st y))) (by simp [lbrS, nock_exec, h7])
  unfold lbrS at hSpin hb ⊢
  conv => lhs; arg 2; unfold lbrS2
  generalize lbrG2 = G2 at hSpin ⊢
  simp [nock_exec, lbrBF2, hb, hc, hs1, spin.axis, hsp, hSpin]

/-- The edit of `gen` after the second `+spin`, and the two halves by `+turn`. -/
theorem lbr_r2 (hc : CompIn ctx) (sur : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (G0 G2 : Noun)
    (fs : List (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))))
    (bs : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    nock (C (C (listN (bs.map fun x => C (lzbE x.1) (lzbE x.2))) G2)
        (C (listN (fs.map fun x => C (lzfE x.1) (lzfE x.2))) (lbrS ctx sur fk bd G0))) lbrR2
      = some (C (C (Laze.mk sur (fs.map Prod.fst) (bs.map Prod.fst)).toNoun
          (Laze.mk sur (fs.map Prod.snd) (bs.map Prod.snd)).toNoun) G2) := by
  have hT1 := turn_head lzfE lzfE fs
  have hT2 := turn_tail lzfE lzfE fs
  have hT3 := turn_head lzbE lzbE bs
  have hT4 := turn_tail lzbE lzbE bs
  conv => lhs; arg 2; unfold lbrR2
  simp only [lz_toNoun_mk]
  unfold lbrS
  simp [nock_exec, lbrFin, hc, turn.arm_at, turn_arm, head_at, head_arm, tail_at, tail_arm, hT1, hT2, hT3, hT4]

/-! ## `+laze-branch` on every `laze` -/

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (y : RsRest)
include hc h7

mutual
/-- `+laze-branch` on every `laze`, from every state. -/
theorem lbr_allN : ∀ (laz : Laze CSet), LbrAt ctx y laz
  | Laze.mk sur fk bd => by
    intro st
    have hF := lbr_forks fk
    have hB := lbr_bonds bd
    rw [lz_toNoun_mk]
    rw [show C lbrGate (C (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))
        (C comp.door (C (rsGenNoun st y) ctx))) = lbrS ctx sur fk bd (rsGenNoun st y) from rfl]
    rw [lbr_gate_split, lbr_s1 hc h7 y sur fk bd st hF]
    cases eF : branchF fk st with
    | none => simp [lazeBranch, eF, bind, StateT.bind]
    | some r =>
      obtain ⟨fs, st1⟩ := r
      simp only [Option.map_some, Option.bind_some]
      rw [lbr_r1, lbr_s2 hc h7 y sur fk bd st1 _ hB]
      cases eB : branchB bd st1 with
      | none => simp [lazeBranch, eF, eB, bind, StateT.bind]
      | some r2 =>
        obtain ⟨bs, st2⟩ := r2
        simp only [Option.map_some, Option.bind_some]
        rw [lbr_r2 hc]
        simp [lazeBranch, eF, eB, bind, StateT.bind, pure, StateT.pure, lbrN]

/-- The gate of the `+spin` over the forks. -/
theorem lbr_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), ∀ e ∈ fk,
    ∀ (s : RSt CSet) (L G0 : Noun),
    nock (C lbrG1 (C (C (lzfE e) (rsGenNoun s y)) (C lbrGate (C L (C comp.door (C G0 ctx)))))) lbrG1
      = (lbrFE e s).map fun r => C (C (lzfE r.1.1) (lzfE r.1.2)) (rsGenNoun r.2 y)
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, yl), (on, nl)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact lbr_fstep y oy on yl nl (lbr_allN yl) (lbr_allN nl)
    · exact lbr_forks rest e he'

/-- The gate of the `+spin` over the bonds. -/
theorem lbr_bonds : ∀ (bd : List (Nat × Laze CSet)), ∀ e ∈ bd,
    ∀ (s : RSt CSet) (FK L G0 : Noun),
    nock (C lbrG2 (C (C (lzbE e) (rsGenNoun s y)) (C FK (C lbrGate (C L (C comp.door (C G0 ctx)))))))
      lbrG2 = (lbrBE e s).map fun r => C (C (lzbE r.1.1) (lzbE r.1.2)) (rsGenNoun r.2 y)
  | [], e, he => absurd he List.not_mem_nil
  | (o, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact lbr_bstep y o l (lbr_allN l)
    · exact lbr_bonds rest e he'
end

end

/-- **`+laze-branch` is `lazeBranch`** at the door of `+run-shape`, on every `laze` (forks and
bonds to any depth), from every state and rest of `gen`, under `CompIn ctx` and `K` at axis `7`
of `ctx`: the two halves and the new `gen` (only `id-gen` moves). -/
theorem lbr_all (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (laz : Laze CSet) (st : RSt CSet) (y : RsRest) :
    nock (C lbrGate (C laz.toNoun (rsDoor st y ctx))) lbrGate
      = (lazeBranch laz st).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (rsGenNoun p.2 y) :=
  lbr_allN hc h7 y laz st

/-! ## Both halves keep `LzNZ` -/

mutual
/-- **`+laze-branch` keeps `LzNZ`**: both halves look at no axis `0` when the `laze` does not
(each half has the same sure parts, and the halves of the inner `laze`s). -/
theorem lazeBranch_nz : ∀ (laz : Laze CSet) (st : RSt CSet) (r : Laze CSet × Laze CSet) (st1 : RSt CSet),
    LzNZ laz → lazeBranch laz st = some (r, st1) → LzNZ r.1 ∧ LzNZ r.2
  | Laze.mk s f b, st, r, st1, ⟨hs, hf, hb⟩, e => by
    have e' : (do
        let fs ← branchF f
        let bs ← branchB b
        pure (Laze.mk s (fs.map Prod.fst) (bs.map Prod.fst), Laze.mk s (fs.map Prod.snd) (bs.map Prod.snd))
          : SM CSet (Laze CSet × Laze CSet)) st = some (r, st1) := by
      rw [← e]; simp only [lazeBranch]
    simp only [bind, StateT.bind, branchF_spin, branchB_spin] at e'
    cases eF : spinM lbrFE f st with
    | none => simp [eF] at e'
    | some p =>
      obtain ⟨fs, s1⟩ := p
      cases eB : spinM lbrBE b s1 with
      | none => simp [eF, eB] at e'
      | some q =>
        obtain ⟨bs, s2⟩ := q
        simp [eF, eB, pure, StateT.pure] at e'
        obtain ⟨rfl, -⟩ := e'
        obtain ⟨hf1, hf2⟩ := branchF_nz f st fs s1 hf eF
        obtain ⟨hb1, hb2⟩ := branchB_nz b s1 bs s2 hb eB
        exact ⟨⟨hs, hf1, hb1⟩, ⟨hs, hf2, hb2⟩⟩

theorem branchF_nz : ∀ (f : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (st : RSt CSet)
    (fs : List (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))))
    (st1 : RSt CSet), LzNZF f → spinM lbrFE f st = some (fs, st1) →
      LzNZF (fs.map Prod.fst) ∧ LzNZF (fs.map Prod.snd)
  | [], st, fs, st1, _, e => by
    simp only [spinM, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]; exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, st, fs, st1, ⟨hy, hn, hr⟩, e => by
    simp only [spinM] at e
    cases e1 : lbrFE ((oy, y), (on, n)) st with
    | none => simp [e1] at e
    | some p =>
      obtain ⟨x, s1⟩ := p
      cases e2 : spinM lbrFE rest s1 with
      | none => simp [e1, e2] at e
      | some q =>
        obtain ⟨xs, s2⟩ := q
        simp [e1, e2] at e
        obtain ⟨rfl, -⟩ := e
        obtain ⟨hr1, hr2⟩ := branchF_nz rest s1 xs s2 hr e2
        unfold lbrFE at e1
        cases ey : lazeBranch y { idg := st.idg + 1 + 1 + 1 + 1, sofs := st.sofs } with
        | none => simp [ey] at e1
        | some ry =>
          obtain ⟨ly, sy⟩ := ry
          cases en : lazeBranch n sy with
          | none => simp [ey, en] at e1
          | some rn =>
            obtain ⟨ln, sn⟩ := rn
            simp [ey, en] at e1
            obtain ⟨rfl, -⟩ := e1
            obtain ⟨hy1, hy2⟩ := lazeBranch_nz y _ ly sy hy ey
            obtain ⟨hn1, hn2⟩ := lazeBranch_nz n sy ln sn hn en
            exact ⟨⟨hy1, hn1, hr1⟩, ⟨hy2, hn2, hr2⟩⟩

theorem branchB_nz : ∀ (b : List (Nat × Laze CSet)) (st : RSt CSet)
    (bs : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (st1 : RSt CSet), LzNZB b →
      spinM lbrBE b st = some (bs, st1) → LzNZB (bs.map Prod.fst) ∧ LzNZB (bs.map Prod.snd)
  | [], st, bs, st1, _, e => by
    simp only [spinM, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]; exact ⟨trivial, trivial⟩
  | (o, l) :: rest, st, bs, st1, ⟨hl, hr⟩, e => by
    simp only [spinM] at e
    cases e1 : lbrBE (o, l) st with
    | none => simp [e1] at e
    | some p =>
      obtain ⟨x, s1⟩ := p
      cases e2 : spinM lbrBE rest s1 with
      | none => simp [e1, e2] at e
      | some q =>
        obtain ⟨xs, s2⟩ := q
        simp [e1, e2] at e
        obtain ⟨rfl, -⟩ := e
        obtain ⟨hr1, hr2⟩ := branchB_nz rest s1 xs s2 hr e2
        unfold lbrBE at e1
        cases el : lazeBranch l { idg := st.idg + 1 + 1, sofs := st.sofs } with
        | none => simp [el] at e1
        | some rl =>
          obtain ⟨ll, sl⟩ := rl
          simp [el] at e1
          obtain ⟨rfl, -⟩ := e1
          obtain ⟨hl1, hl2⟩ := lazeBranch_nz l _ ll sl hl el
          exact ⟨⟨hl1, hr1⟩, ⟨hl2, hr2⟩⟩
end

/-- **The call of `+laze-branch` in the case `%6`** (`[9 0x15576 0 127]` with the sample at
`2037` of `rs6Kerf`): on a subject with the door of `+run-shape` at axis `127` and the `laze`
at axis `1013`, the call is `lazeBranch`. -/
theorem lbr_call (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (T : Noun) (laz : Laze CSet) (st : RSt CSet)
    (y : RsRest) (hd : slot? 127 T = some (rsDoor st y ctx)) (hl : slot? 1013 T = some laz.toNoun) :
    nock T (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x15576) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2037))) (C (A 0) (A 2))))))))))
      = (lazeBranch laz st).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (rsGenNoun p.2 y) := by
  have h := lbr_allN hc h7 y laz st
  simp only [rsDoor] at hd
  generalize lazeBranch laz st = R at h ⊢
  simp [nock_exec, hd, hl, lbr_at', lbr_arm, h]
  rfl

end Compiler
end Formalization

