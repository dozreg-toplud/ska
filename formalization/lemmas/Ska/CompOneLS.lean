import lemmas.Ska.CompFiveLS
import lemmas.Ska.CompMedeE

/-!
# The constant `[1 k]` under a flat lazy goal

README Gaps 12.31.  `+mede` (`medeL`) emits the block `[hop th]` and walks
the goal's lazy need with the gate `medeGate`: at its own block and at
every goal entry it puts the ops of `+mede`'s loop, which write `k` into the
registers of the need after `+sure-require-look`, or crash where `k` has not
the need's shape (`+crash-need` with the atom as an immediate).  The result
asks nothing and has no entry, and its jump is the new block.

The ops read no register, so the run meets `RunOKLS` with `x = false` and
`[1 k]` meets `LOKS false` at every goal (`lokS_n1`).  The one fact beyond
`medeGate_ok` is that those ops mention only the registers of the need and
registers allocated in the walk (`medeLoop_specR`, `MedePR`,
`medeGateR_ok`), which are no keys of the final `cond`: unproxying leaves
them alone (`unproxy_ops`).

* `medeLoop_specR`: `medeLoop_spec` with `RegsIn` of the ops.
* `MedePR`, `medePR_mono`, `medeGateR_ok`: the walk's property with the
  registers.
* `runOKL_n1`: `RunOKL` of `[1 k]` under `%next L th`, any lazy `L` whose
  entries' blocks have bodies.
* `lokS_n1`: `[1 k]` meets `LOKS false`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The registers of the ops of `+mede` -/

/-- **The loop of `+mede`, with the registers of its ops**: those of the
need and those allocated in the loop. -/
theorem medeLoop_specR {o : Nat} (P : Nat → Prop) : ∀ (som : Noun) (ned : Need) (g0 g1 : Gen Map) (u : Unit),
    medeLoop o som ned g0 = some (u, g1) → g0.drop = false →
    (∀ x, NMem ned x → P x) → (∀ x, g0.re ≤ x → x < g1.re → P x) →
    ∃ A, Front o g0 g1 A ∧ RegsIn P A ∧ ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t regs,
      Distinct ned →
      (Fits ned som → ∃ regs', Runs lib O c gul st t A regs regs' ∧ HoldsN ned regs' som ∧
        ∀ r, ¬ NMem ned r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      (¬ Fits ned som → Crashes lib O c gul st t A regs)
  | som, Need.none, g0, g1, u, h, _, _, _ => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], ⟨fun B fin h => h, fun _ _ => rfl, rfl, rfl, Nat.le_refl _⟩, RegsIn.nil P,
      fun _ _ _ _ _ _ _ regs _ =>
      ⟨fun _ => ⟨regs, Runs.nil regs, trivial, fun _ _ => rfl⟩, fun hn => absurd trivial hn⟩⟩
  | som, Need.this r, g0, g1, u, h, hd, hn, _ => by
    simp only [medeLoop] at h
    refine ⟨_, front_addOps h hd, RegsIn.cons (fun x hx => by
      simp only [poleRegs, List.mem_singleton] at hx; subst hx; exact hn _ rfl) (RegsIn.nil P),
      fun _ _ _ _ _ _ _ regs _ => ⟨fun _ => ⟨_, runs_imm som r regs,
      read_store_eq r som regs, fun r' hr' => read_store_ne (by simpa [NMem] using hr') _ _⟩,
      fun hn => absurd trivial hn⟩⟩
  | Noun.atom n, Need.pair p q, g0, g1, u, h, hd, hn, hr => by
    simp only [medeLoop] at h
    have h' := h
    simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h'
    have F := front_re (front_addOps h' hd)
    have hre : g1.re = g0.re + 1 := (addOps_spec h' hd).elim fun b ⟨_, e⟩ => by rw [e]
    refine ⟨_, F, ?_, fun lib σ O c gul st t regs _ => ⟨fun hf => by simp [Fits] at hf,
      fun _ => crashes_imm_cel _ _ _ regs⟩⟩
    refine RegsIn.cons (fun x hx => ?_) (RegsIn.cons (fun x hx => ?_) (fun p' hp' x hx => ?_))
    · simp only [poleRegs, List.mem_singleton] at hx; subst hx; exact hr _ (Nat.le_refl _) (by omega)
    · simp only [poleRegs, List.mem_singleton] at hx; subst hx; exact hr _ (Nat.le_refl _) (by omega)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp'
      simp only [poleRegs, List.mem_singleton] at hx; subst hx
      exact hn _ ((mem_flatten _ _).mp hy)
  | Noun.atom n, Need.both r p q, g0, g1, u, h, hd, hn, hr => by
    simp only [medeLoop] at h
    have h' := h
    simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h'
    have F := front_re (front_addOps h' hd)
    have hre : g1.re = g0.re + 1 := (addOps_spec h' hd).elim fun b ⟨_, e⟩ => by rw [e]
    refine ⟨_, F, ?_, fun lib σ O c gul st t regs _ => ⟨fun hf => by simp [Fits] at hf,
      fun _ => crashes_imm_cel _ _ _ regs⟩⟩
    refine RegsIn.cons (fun x hx => ?_) (RegsIn.cons (fun x hx => ?_) (fun p' hp' x hx => ?_))
    · simp only [poleRegs, List.mem_singleton] at hx; subst hx; exact hr _ (Nat.le_refl _) (by omega)
    · simp only [poleRegs, List.mem_singleton] at hx; subst hx; exact hr _ (Nat.le_refl _) (by omega)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp'
      simp only [poleRegs, List.mem_singleton] at hx; subst hx
      exact hn _ ((mem_flatten _ _).mp hy)
  | Noun.cell a b, Need.pair p q, g0, g1, u, h, hd, hn, hr => by
    simp only [medeLoop] at h
    obtain ⟨u1, g', h1, h2⟩ := bind_some h
    have le2 : g'.re ≤ g1.re := by
      obtain ⟨A2, F2, _⟩ := medeLoop_spec (o := o) b q g' g1 u h2 (by
        obtain ⟨A1, F1, _⟩ := medeLoop_spec (o := o) a p g0 g' u1 h1 hd
        exact F1.drop.trans hd)
      exact F2.le
    obtain ⟨A1, F1, R1, S1⟩ := medeLoop_specR P a p g0 g' u1 h1 hd (fun x hx => hn x (Or.inl hx))
      (fun x hx hx' => hr x hx (Nat.lt_of_lt_of_le hx' le2))
    obtain ⟨A2, F2, R2, S2⟩ := medeLoop_specR P b q g' g1 u h2 (F1.drop.trans hd) (fun x hx => hn x (Or.inr hx))
      (fun x hx hx' => hr x (Nat.le_trans F1.le hx) hx')
    refine ⟨A2 ++ A1, F1.trans F2, R2.append R1, fun lib σ O c gul st t regs hdist => ?_⟩
    obtain ⟨dp, dq, dpq⟩ := hdist
    refine ⟨fun hf => ?_, fun hn => ?_⟩
    · obtain ⟨regs2, R2, H2, K2⟩ := (S2 lib σ O c gul st t regs dq).1 hf.2
      obtain ⟨regs1, R1, H1, K1⟩ := (S1 lib σ O c gul st t regs2 dp).1 hf.1
      refine ⟨regs1, R2.append R1, ⟨H1, HoldsN.agree q (fun x hx => K1 x fun hp => dpq x hp hx) H2⟩,
        fun r hr => (K1 r fun h => hr (Or.inl h)).trans (K2 r fun h => hr (Or.inr h))⟩
    · by_cases hq : Fits q b
      · obtain ⟨regs2, R2, _, _⟩ := (S2 lib σ O c gul st t regs dq).1 hq
        exact Crashes.append_right R2 ((S1 lib σ O c gul st t regs2 dp).2 fun hp => hn ⟨hp, hq⟩)
      · exact Crashes.append_left ((S2 lib σ O c gul st t regs dq).2 hq)
  | Noun.cell a b, Need.both r p q, g0, g1, u, h, hd, hn, hr => by
    simp only [medeLoop] at h
    obtain ⟨u0, g', h0, h'⟩ := bind_some h
    have F0 := front_addOps h0 hd
    obtain ⟨u1, g'', h1, h2⟩ := bind_some h'
    have le2 : g''.re ≤ g1.re := by
      obtain ⟨A2, F2, _⟩ := medeLoop_spec (o := o) b q g'' g1 u h2 (by
        obtain ⟨A1, F1, _⟩ := medeLoop_spec (o := o) a p g' g'' u1 h1 (F0.drop.trans hd)
        exact F1.drop.trans (F0.drop.trans hd))
      exact F2.le
    obtain ⟨A1, F1, R1, S1⟩ := medeLoop_specR P a p g' g'' u1 h1 (F0.drop.trans hd)
      (fun x hx => hn x (Or.inr (Or.inl hx)))
      (fun x hx hx' => hr x (Nat.le_trans F0.le hx) (Nat.lt_of_lt_of_le hx' le2))
    obtain ⟨A2, F2, R2, S2⟩ := medeLoop_specR P b q g'' g1 u h2 (F1.drop.trans (F0.drop.trans hd))
      (fun x hx => hn x (Or.inr (Or.inr hx))) (fun x hx hx' => hr x (Nat.le_trans F0.le (Nat.le_trans F1.le hx)) hx')
    refine ⟨A2 ++ (A1 ++ [Pole.imm (C a b) r]), (F0.trans F1).trans F2,
      R2.append (R1.append (RegsIn.cons (fun x hx => by
        simp only [poleRegs, List.mem_singleton] at hx; subst hx; exact hn _ (Or.inl rfl)) (RegsIn.nil P))),
      fun lib σ O c gul st t regs hdist => ?_⟩
    obtain ⟨dp, dq, dpq, rp, rq⟩ := hdist
    refine ⟨fun hf => ?_, fun hn => ?_⟩
    · obtain ⟨regs2, R2, H2, K2⟩ := (S2 lib σ O c gul st t regs dq).1 hf.2
      obtain ⟨regs1, R1, H1, K1⟩ := (S1 lib σ O c gul st t regs2 dp).1 hf.1
      refine ⟨_, R2.append (R1.append (runs_imm _ r regs1)), ⟨read_store_eq _ _ _, ?_, ?_⟩, ?_⟩
      · exact HoldsN.agree p (fun x hx => read_store_ne (fun e => rp (by rw [← e]; exact hx)) _ _) H1
      · exact HoldsN.agree q (fun x hx => (read_store_ne (fun e => rq (by rw [← e]; exact hx)) _ _).trans
          (K1 x fun hp => dpq x hp hx)) H2
      · intro r' hr'
        rw [read_store_ne (fun e => hr' (Or.inl e))]
        exact (K1 r' fun h => hr' (Or.inr (Or.inl h))).trans (K2 r' fun h => hr' (Or.inr (Or.inr h)))
    · by_cases hq : Fits q b
      · obtain ⟨regs2, R2, _, _⟩ := (S2 lib σ O c gul st t regs dq).1 hq
        exact Crashes.append_right R2
          (Crashes.append_left ((S1 lib σ O c gul st t regs2 dp).2 fun hp => hn ⟨hp, hq⟩))
      · exact Crashes.append_left ((S2 lib σ O c gul st t regs dq).2 hq)

/-- **The walk's property of `+mede` with the registers of the ops**: those
of the sure need and those allocated in the walk. -/
def MedePR (som : Noun) (lo hi : Nat) (o : Nat) (sur : Sure S) (A : List Pole) : Prop :=
  MedeP (Map := Map) som lo hi o sur A ∧ RegsIn (fun x => NMem sur.ned x ∨ (lo ≤ x ∧ x < hi)) A

theorem medePR_mono (som : Noun) : PMono (MedePR (S := S) (Map := Map) som) := by
  intro lo hi lo' hi' o s A h h1 h2
  exact ⟨medeP_mono som lo hi lo' hi' o s A h.1 h1 h2,
    h.2.mono fun x hx => hx.imp_right fun ⟨a, b⟩ => ⟨Nat.le_trans h1 a, Nat.lt_of_lt_of_le b h2⟩⟩

theorem medeGateR_ok (som : Noun) : GateOK (MedePR (S := S) (Map := Map) som) (medeGate (S := S) (Map := Map) som) := by
  intro o l g g' h hd
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  have F0 := (medeLoop_spec som ned _ _ () h2 hd)
  obtain ⟨A, F, RA, SP⟩ := medeLoop_specR (o := o) (fun x => NMem l.sure.ned x ∨ (g.re ≤ x ∧ x < g'.re))
    som ned _ _ () h2 hd
    (fun x hx => (L.mem x hx).imp_right fun ⟨a, b⟩ => ⟨a, by
      obtain ⟨_, F', _⟩ := F0; exact Nat.lt_of_lt_of_le b F'.le⟩)
    (fun x hx hx' => Or.inr ⟨Nat.le_trans L.le hx, hx'⟩)
  have kc := (kc_medeLoop o som ned).keep _ _ _ h2
  refine ⟨F.bo, F.drop, Nat.le_trans L.le F.le, kc, fun o' ho => F.other o' (fun e => ho (by simp [e])),
    fun e he => ?_⟩
  simp only [List.mem_singleton] at he; subst he
  refine ⟨A, fun B fin hb => F.blk B fin hb, fun lib σ O c gul st t regs hdis hlt => ?_, RA⟩
  have dn := L.dist hdis hlt
  obtain ⟨S1, S2⟩ := SP lib σ O c gul st t regs dn
  have fit : ∀ n, Fits ned n ↔ FitsS l.sure n := fun n => (L.fits n).trans Iff.rfl
  refine ⟨fun f => ?_, fun nf => S2 fun f' => nf ((fit som).mp f')⟩
  obtain ⟨R, r1, r2, r3⟩ := S1 ((fit som).mpr f)
  refine ⟨R, r1, holdsS_of_sure L r2, fun r hn hl => r3 r fun hm => ?_⟩
  rcases L.mem r hm with h' | h'
  · exact hn h'
  · exact hl ⟨h'.1, Nat.lt_of_lt_of_le h'.2 F.le⟩


/-! ## `[1 k]` under a lazy goal -/

/-- **`[1 k]` under `%next L th`, any lazy `L`** (`+mede`): the block
`[hop th]` with the constant's ops in front, the goal entries' blocks with
the same ops in front of their bodies, no product register, no entry.  With
the fronts at the state level (`FrontsS`, no witness). -/
theorem runOKL_n1 (lib : Lib) {k : Noun} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (h : runL (Nomm.n1 k) (CGoalL.next L th) region g0 = some (nex, g1))
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hta : th.args = []) (hd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) :
    nex = ⟨ofSure Sure.bunt, jmp0 g0.bo⟩ ∧
    RunOKL (Map := Map) lib (Nomm.n1 k) L th (fun _ => Need.none) (fun _ => A 0) g0 g1 nex ∧
    FrontsS (Map := Map) (pureWit (Nomm.n1 k) (fun _ => Need.none) (fun _ => A 0)) false g0 g1 L nex := by
  simp only [runL, medeL_eq, bind_apply, emit_apply, Option.bind_some, get_apply] at h
  simp only [emitted_drop, d0, Bool.false_eq_true, if_false] at h
  obtain ⟨⟨o', gW⟩, hX, hP⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, g3, hW, h5⟩ := bind_some hX
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5 hP
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g0.emitted ⟨[], [], Termin.hop th⟩ := ⟨_, rfl⟩
  rw [← hgE] at hW
  have dE : gE.drop = false := by simp [hgE, emitted_drop, d0]
  have bE : HoonMap.get gE.blocks g0.bo = some ⟨[], [], Termin.hop th⟩ := by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put]
  have oE : ∀ o, o ≠ g0.bo → HoonMap.get gE.blocks o = HoonMap.get g0.blocks o := fun o ho => by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put, ho]
  have nlab : g0.bo ∉ (entries L).map Prod.fst := fun hm => by
    obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (hlab e he).1; omega
  have W := walkLazy_ok (medePR_mono k) (medeGateR_ok k) g0.bo L gE g3 hW dE
    (by simp only [List.map_cons, List.nodup_cons]; exact ⟨nlab, hnd⟩)
  have reE : gE.re = g0.re := by rw [hgE]; rfl
  have boE : gE.bo = g0.bo + 1 := by rw [hgE]; rfl
  have kE : gE.cond = g0.cond := by rw [hgE]; rfl
  have c3 : g3.cond = g0.cond := W.cnd.trans kE
  have le3 : g0.re ≤ g3.re := reE ▸ W.le
  -- no register of the ops is a key of a `cond` that agrees with the final one
  have cond0 : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g0.cond x with
    | none => rfl
    | some _ => have := hcb x (by simp [e]); omega
  have fix : ∀ cf : Map (Nat × List Nat), (∀ kk, kk < g3.re → HoonMap.get cf kk = HoonMap.get g3.cond kk) →
      ∀ (sur : Sure S) (A : List Pole), (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
      RegsIn (fun x => NMem sur.ned x ∨ (gE.re ≤ x ∧ x < g3.re)) A → A.map (renPole (unproxy cf)) = A :=
    fun cf hcf sur A hs hA => renOps_fix (P := fun x => NMem sur.ned x ∨ (gE.re ≤ x ∧ x < g3.re))
      (fun x hx => unproxy_none (by
        rcases hx with hx | ⟨a, b⟩
        · rw [hcf x (by have := (hs x hx).1; omega), c3]; exact (hs x hx).2
        · rw [hcf x b, c3]; exact cond0 x (by omega))) hA
  -- the block of `+mede`
  obtain ⟨Ao, hAo, PAo⟩ := W.at_ (g0.bo, L) List.mem_cons_self
  have bo3 : HoonMap.get g3.blocks g0.bo = some ⟨[], Ao ++ [], Termin.hop th⟩ := hAo [] _ bE
  have other3 : ∀ o, o ≠ g0.bo → o ∉ (entries L).map Prod.fst →
      HoonMap.get g3.blocks o = HoonMap.get g0.blocks o := fun o h1' h2' =>
    (W.other o (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨h1', h2'⟩)).trans (oE o h1')
  have ent3 : ∀ e ∈ entries L, ∃ A, (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ →
      HoonMap.get g3.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧ MedePR (Map := Map) k gE.re g3.re e.1 e.2.sure A :=
    fun e he => by
      obtain ⟨A, hA, hPA⟩ := W.at_ e (List.mem_cons_of_mem _ he)
      exact ⟨A, fun B fin hb => hA B fin (by rw [oE _ (by have := (hlab e he).1; omega)]; exact hb), hPA⟩
  have bo3' : g3.bo = g0.bo + 1 := W.bo.trans boE
  have hgrow : Grow g0 g3 := by
    refine ⟨by omega, W.drop.trans (dE.trans d0.symm), fun kk b hk hb => ?_, fun kk b' hb' => ?_⟩
    · by_cases hm : kk ∈ (entries L).map Prod.fst
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        obtain ⟨B, th', hB⟩ := (hlab e he).2
        obtain ⟨A, hA, _⟩ := ent3 e he
        rw [hB] at hb; cases hb
        exact ⟨_, hA B _ hB, rfl, rfl⟩
      · exact ⟨b, (other3 kk (by omega) hm).trans hb, rfl, rfl⟩
    · by_cases e0 : kk = g0.bo
      · subst e0; rw [bo3] at hb'; cases hb'
        refine Or.inr ⟨Nat.le_refl _, by omega, fun j hj => ?_⟩
        simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨h1, h2⟩
      · by_cases hm : kk ∈ (entries L).map Prod.fst
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          obtain ⟨B, th', hB⟩ := (hlab e he).2
          obtain ⟨A, hA, _⟩ := ent3 e he
          rw [hA B _ hB] at hb'; cases hb'
          exact Or.inl ⟨_, hB, rfl, rfl⟩
        · rw [other3 kk e0 hm] at hb'
          exact Or.inl ⟨b', hb', rfl, rfl⟩
  have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
  have nb : ∀ r, ¬ NMem (Sure.bunt : Sure S).ned r := fun r hr => by simp [Sure.bunt, NMem] at hr
  refine ⟨rfl, ⟨le3, by omega, W.drop.trans (dE.trans d0.symm), fun o ho hn => other3 o (by omega) hn,
    hgrow.toU hu, condFresh_of_eq le3 c3, by simp [jmp0]; omega, by simp [jmp0]; omega,
    Or.inl ⟨_, bo3, rfl, rfl⟩, fun r hr => absurd hr (nb r), trivial,
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    (by rw [e0]; simp), fun _ r hr => hr.elim, fun s hs => absurd (fitsS_bunt s) hs,
    fun r hr => absurd hr (nb r), fun e he => (by rw [e0] at he; cases he), fun e he => ?_, ?_⟩, fun e he => ?_⟩
  · -- the front of `RunOKL`
    obtain ⟨A, hA, hPA⟩ := ent3 e he
    refine ⟨A, hA, fun cf hcf => Or.inr ⟨by rw [e0]; simp, ?_⟩⟩
    rw [fix cf hcf e.2.sure A (hed e he).2 hPA.2]
    intro lib σ O c gul st t ned A0 s0 s v hned hev hfill R hR
    simp only [pureEval, Option.some.injEq] at hev; subst hev
    obtain ⟨R1, r1, _, k1⟩ := (hfill R hR.1).1 (fitsS_bunt s)
    obtain ⟨S1, S2⟩ := hPA.1 lib σ O c gul st t R1 (hed e he).1 (fun r hr => by rw [reE]; exact ((hed e he).2 r hr).1)
    refine ⟨fun f => ?_, fun nf => Crashes.append_right r1 (S2 nf)⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, Runs.append r1 r2, hh2, fun x hx hn => (k2 x hn ?_).trans (k1 x ?_ (nb x))⟩
    · rintro ⟨a, b⟩
      rcases hx with (hx | hx) | hx
      · have := hned x hx; omega
      · exact hx.elim
      · omega
    · rcases hx with (hx | hx) | hx
      · exact Or.inl hx
      · exact hx.elim
      · exact Or.inr (by omega)
  · -- the `sem`
    intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    show GoalSemD lib O c gul st _ regs t (jmp0 g0.bo) L.sure th Need.none (A 0) (pureEval (Nomm.n1 k) s)
    have hc : HoonMap.get c.blocks g0.bo = some ⟨[], Ao ++ [], Termin.hop th⟩ := by
      rw [ag.1 g0.bo (Nat.le_refl _) (by omega) (by rw [e0]; simp), bo3]
      have := fix cf hcf L.sure Ao hsl PAo.2
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, renFin,
        renJmp_nil _ hta, this]
    simp only [pureEval, GoalSemD]
    obtain ⟨S1, S2⟩ := PAo.1 lib σ O c gul st t regs hd (fun r hr => by rw [reE]; exact (hsl r hr).1)
    rw [goJ_jmp0 _ _ _ _ hc]
    refine ⟨fun f => ?_, fun nf => S2 nf [] _⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, hh2.1, trivial, fun r hr => k2 r hr.2 (fun ⟨a, b⟩ => ?_), by rw [r2 [] _, execBlob_hop]⟩
    rcases hr.1 with x | x
    · omega
    · have := hned r x; omega
  · -- the fronts at the state level
    obtain ⟨A, hA, hPA⟩ := ent3 e he
    refine ⟨A, hA, fun cf hcf => Or.inr ⟨by rw [e0]; simp, ?_⟩⟩
    rw [fix cf hcf e.2.sure A (hed e he).2 hPA.2]
    refine ⟨fun r hr => absurd hr (nb r), fun s v d w _ r _ hr => absurd hr (nb r),
      fun _ _ _ _ _ _ => fitsS_bunt _, fun lib σ O c gul st t R s v d w hq _ _ _ => ?_⟩
    obtain ⟨hv, rfl, rfl⟩ := hq
    simp only [pureEval, Option.some.injEq] at hv; subst hv
    obtain ⟨S1, S2⟩ := hPA.1 lib σ O c gul st t R (hed e he).1 (fun r hr => by rw [reE]; exact ((hed e he).2 r hr).1)
    refine ⟨fun f => ?_, fun nf => S2 nf⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, r2, hh2, fun x hx hn => k2 x hn (fun ⟨a, b⟩ => ?_)⟩
    rcases hx with hx | hx | hx
    · omega
    · omega
    · exact hx.elim


/-- **`[1 k]` meets `LOKS false`** for a formula whose `+mink` is the
constant: `runOKL_n1` with `RunOKL.toLC`, the fronts as `FrontsS`; the jump
is the new block, the result asks nothing and has no entry. -/
theorem lokS_n1 (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {k : Noun}
    (M : MinkEq lib P f (Nomm.n1 k)) : LOKS (S := S) (Map := Map) false lib N env P f (Nomm.n1 k) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g1 nex} _ b0 d0 hu hcl hcb
    h1 h2 hta ht hsd hsl hlab hnd hed hfl _ hce hr => ?_⟩
  · rw [runLC_eq env _ rfl] at h
    simp only [runL] at h
    obtain ⟨o, g', _, h'⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    trivial
  · rw [runLC_eq env _ rfl] at hr
    obtain ⟨rfl, R, FS⟩ := runOKL_n1 (Map := Map) lib hr d0 hu hcb h1 h2 hta hsd hsl hlab hnd hed
    have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
    exact ⟨⟨_, { toRunOKLB := (R.toLC M).toB (P := P) (N := N), fs := FS }⟩,
      (by rw [e0]; exact fun h => (by cases h)), Or.inr (Nat.le_refl _),
      ⟨rfl, fun e he => (by cases he)⟩, fun e he => (by rw [e0] at he; cases he)⟩

/-- **`[1 k]` under `%done` meets `DoneOK`**: the block `[imm k r] don r`,
through `UOKC` of the fragment (as `[0 0]` in `callTree_done`). -/
theorem n1_doneB (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {k : Noun}
    (M : MinkEq lib P f (Nomm.n1 k)) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup (Nomm.n1 k) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  have U := uokc_of_uok (S := S) (Map := Map) lib env
    (uok_x lib (FragX.frag (S := S) (nm := Nomm.n1 k) fun _ => trivial)) M
  have R := U.run (sup := sup) (goal := CGoal.done) (region := region) trivial trivial trivial trivial trivial
    (by simp [Comp.sixCount]) b0 d0 hu hcl hcb (fun r hr => hr.elim) hr
  rw [runLC_eq env _ rfl] at hr
  simp only [runL, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨R.toB, by simp [entries_ofSure], flat_ofSure _, trivial, by simp [entries_ofSure]⟩

end Comp
end SkaModel
end Formalization
