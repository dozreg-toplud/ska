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


/-! ## The cons with a hinted tail and a flagged head -/

/-- **The cons with a hinted tail of `LOKS false` and a head of `LOKSF`**
(`lokS_cons_run` with the head's run patched): the head runs under the
parked goal, or under the tail's goal half when it asks nothing, both
flag-free. -/
theorem lokS_cons_runH (lib : Lib) {N : Needs} (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y)
    (Kp : (p.pure = true ∧ MinkEq lib P fh p) ∨ hinted env.cod p = some true)
    (Kq : (q.pure = true ∧ MinkEq lib P ft q) ∨ hinted env.cod q = some true)
    (Jq : hinted env.cod q = some true → JNewLS (S := S) (Map := Map) env q)
    (hqh : hinted env.cod q = some true)
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fh p) (Sq : LOKS (S := S) (Map := Map) false lib N env P ft q)
    {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcount : sixCount (Nomm.cons p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hta : th.args = [])
    (ht : th.there ∉ (entries L).map Prod.fst) (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfl : Flat L) (hcs : Clean L.sure.ned) (hce : ∀ e ∈ entries L, Clean e.2.sure.ned)
    (hr : runLC env sup (Nomm.cons p q) (CGoalL.next L th) region g0 = some (nex, g1)) :
    (∃ Q, RunOKLS (Map := Map) lib N P (C fh ft) L th Q false g0 g1 nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧ g0.bo ≤ nex.th.there ∧ Flat nex.laz ∧
      (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  have e : (runLC env sup (Nomm.cons p q) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, g'', hs, hr⟩ := bind_some hr
  simp only at hr
  obtain ⟨nexh, gb, hph, hr⟩ := bind_some hr
  obtain ⟨nexq, g1', h3, hr⟩ := bind_some hr
  obtain ⟨nexq', g1'', hp2, hr⟩ := bind_some hr
  obtain ⟨nexp, g2, h4, hcp⟩ := bind_some hr
  -- the two `+past`s
  have pcase : (nexh = ⟨hed, jmp0 o⟩ ∧ gb = g'' ∧ ((∀ x, FitsS hed.sure x) ∨ TotalC lib P ft)) ∨
      (hinted env.cod q = some true ∧
        nexh = ⟨Lazy.mk Sure.bunt [] ((g''.bo, Lazy.mk hed.sure hed.fork []) :: hed.bond), jmp0 g''.bo⟩ ∧
        gb = (g''.emitted ⟨[], [], Termin.hop (jmp0 o)⟩).tagged g''.bo region) := by
    rcases Kq with ⟨qp, Mq⟩ | hq
    · rw [pastL_pure _ _ qp, pure_apply] at hph
      simp only [Option.some.injEq, Prod.mk.injEq] at hph
      exact Or.inl ⟨hph.1.symm, hph.2.symm, Or.inr (totalC_of_minkEq Mq)⟩
    · rcases pastL_hinted hq hph with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2, Or.inl (fun x => fitsS_trivial en es x)⟩
      · exact Or.inr ⟨hq, x1, x2⟩
  have FH : FlagFree nexh.laz := by
    rcases pastL_hinted hqh hph with ⟨x1, -, en, -⟩ | ⟨x1, -⟩ <;> rw [x1]
    · exact Or.inl en
    · exact Or.inl rfl
  have tcase : (nexq' = nexq ∧ g1'' = g1' ∧ ((∀ s, FitsS nexq.laz.sure s) ∨ TotalC lib P fh)) ∨
      (nexq' = ⟨Lazy.mk Sure.bunt [] ((g1'.bo, Lazy.mk nexq.laz.sure nexq.laz.fork []) :: nexq.laz.bond),
          jmp0 g1'.bo⟩ ∧
        g1'' = (g1'.emitted ⟨[], [], Termin.hop nexq.th⟩).tagged g1'.bo region) := by
    rcases Kp with ⟨pp, Mp⟩ | hp
    · rw [pastL_pure _ _ pp, pure_apply] at hp2
      simp only [Option.some.injEq, Prod.mk.injEq] at hp2
      exact Or.inl ⟨hp2.1.symm, hp2.2.symm, Or.inr (totalC_of_minkEq Mp)⟩
    · rcases pastL_hinted hp hp2 with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2, Or.inl (fun x => fitsS_trivial en es x)⟩
      · exact Or.inr ⟨x1, x2⟩
  have eL := entries_flat hfl
  obtain ⟨sH, sT, gS, bh, bt, hsS, hSB, rfl, rfl⟩ := splitL_flat hfl hs
  -- the sure part (as `consLC_runN`)
  have hok : GoalOK g0 (CGoal.next L.sure th) := ⟨hsd, fun r hr => (hsl r hr).1⟩
  have hkg : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none := fun r hr => (hsl r hr).2
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok hsS
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hok.1 hok.2
  obtain ⟨G2, eo', lt2, _⟩ := split_down hsS h1 h2 d0
  simp only at eo'
  subst eo
  have CS := clean_split hsS hcs
  simp only at CS
  have c2 : gS.cond = g0.cond := (kc_split _).keep _ _ _ hsS
  have d2 : gS.drop = false := E2.2.2.1.trans d0
  have G2U : GrowU g0 gS := G2.toU hu
  have u2 : UpBelow gS := G2U.up hu
  have lt2' : ∀ (n : Need), (∀ y, NMem n y → NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < gS.re)) →
      ∀ y, NMem n y → y < gS.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y a) E2.1
    · exact a
  have cl2 : Clear gS := hcl0.growU G2U
  have cf2 : CondFresh g0 gS := condFresh_of_eq E2.1 c2
  have cb2 : CondBelow gS := cf2.below hcb
  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo gS :=
    (keepsA_split (P := fun r => HoonMap.get g0.cond r = Option.none) d0 hkg (jmpIn_nil hta)
      (fun r hr => condBelow_none hcb hr) hsS).1.ab _ (aboveIn_start _ g0)
  have BS : BelowIn g0.bo gS :=
    (keeps_split d0 (fun r hr => hok.2 r hr) (jmpIn_nil hta) hsS).1.bel _ (belowIn_start g0)
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < gS.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < gS.bo → (HoonMap.get gS.blocks k).map (unproxyBlob cf) = HoonMap.get gS.blocks k := by
    intro cf hcf k h0 h1'
    have u0 : ∀ x, x < gS.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
    have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
    cases hg : HoonMap.get gS.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1' hg), renBlob_congr u1 (AS k b h0 h1' hg), renBlob_id]
  have hblk : ∀ (c : Straight Map), Agree c g0 gS →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS sH x → FitsS sT y → HoldsN sH.ned regs x →
        HoldsN sT.ned regs y →
          GoalSem lib O c gul st (Keep g0 gS (CGoal.next L.sure th)) regs t (jmp0 g0.bo) (CGoal.next L.sure th)
            (some (C x y)) := by
    intro c hc σ O st' regs t gul x y fx fy hx hy
    refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st' t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩
  have hnot : ∀ x y, ¬ FitsS sH x ∨ ¬ FitsS sT y → ¬ FitsS L.sure (C x y) := fun x y hn hf => by
    rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  have Mf := fun {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone} (_ : P s)
      (hm : minkF lib gul n tm s (C fh ft) = some r) => minkF_consG hfh hm
  have Mb := fun {s gul : Noun} {tm : Trace} {rh : Tone} (_ : P s) (hh : Mink lib gul tm s fh rh) =>
    mink_consG_bwd (ft := ft) hfh hh
  -- the bonds
  have hblS : ∀ e ∈ L.bond, ∃ B fin, HoonMap.get gS.blocks e.1 = some ⟨[], B, fin⟩ := fun e he => by
    obtain ⟨hlt, B, th', hb⟩ := hlab e (by rw [eL]; exact he)
    exact ⟨B, _, by rw [E2.2.2.2 _ hlt]; exact hb⟩
  obtain ⟨PB, PBP, PBo, fbh, fbt, ebh, ebt, SPL⟩ := splitAt_of_splitBs (Map := Map) (sh0 := sH) (st0 := sT) hfl.2 hSB
    d2 (by rw [← eL]; exact hnd) hblS
    (fun e he => ⟨(hed e (by rw [eL]; exact he)).1, fun x hx => by
      have := ((hed e (by rw [eL]; exact he)).2 x hx).1; have := E2.1; omega⟩)
    (fun e he => hce e (by rw [eL]; exact he))
  -- the halves
  have fH : Flat (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) :=
    flat_mk (fun e he => fbh e (List.mem_filter.mp he).1)
  have fT : Flat (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) :=
    flat_mk (fun e he => fbt e (List.mem_filter.mp he).1)
  have eH := entries_flat fH
  have eT := entries_flat fT
  have hhl : ∀ e ∈ (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond, e.1 ∈ L.bond.map Prod.fst := fun e he => by
    rw [← ebh]; exact List.mem_map_of_mem (List.mem_filter.mp he).1
  have htl : ∀ e ∈ (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))).bond, e.1 ∈ L.bond.map Prod.fst := fun e he => by
    rw [← ebt]; exact List.mem_map_of_mem (List.mem_filter.mp he).1
  have hnL : (L.bond.map Prod.fst).Nodup := by rw [← eL]; exact hnd
  have hhn : ((mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond.map Prod.fst).Nodup :=
    (show (bh.map Prod.fst).Nodup by rw [ebh]; exact hnL).sublist (List.Sublist.map _ List.filter_sublist)
  have htn : ((mk sT [] (bt.filter fun e => !(lazyEmpty e.2))).bond.map Prod.fst).Nodup :=
    (show (bt.map Prod.fst).Nodup by rw [ebt]; exact hnL).sublist (List.Sublist.map _ List.filter_sublist)
  have labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    exact (hlab e (by rw [eL]; exact he)).1
  have halfE : ∀ (half : Bool) e, e ∈ (if half then (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond
      else (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))).bond) → ∃ eb ∈ L.bond, ∃ sh st,
      SplitAt (Map := Map) eb (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))
        (PB eb.1) gS.re g''.re sh st ∧ e = (eb.1, ofSure (if half then sh else st)) := by
    intro half e he
    cases half
    · simp only [Bool.false_eq_true, if_false] at he ⊢
      obtain ⟨eb, heb, ee⟩ := List.mem_map.mp (htl e he)
      obtain ⟨sh, st, SA⟩ := SPL eb heb
      rcases SA.int with a | ⟨a, _⟩
      · exact ⟨eb, heb, sh, st, SA, eq_of_label htn he a ee.symm⟩
      · exact absurd (by rw [ee]; exact List.mem_map_of_mem he) a
    · simp only [if_true] at he ⊢
      obtain ⟨eb, heb, ee⟩ := List.mem_map.mp (hhl e he)
      obtain ⟨sh, st, SA⟩ := SPL eb heb
      rcases SA.inh with a | ⟨a, _⟩
      · exact ⟨eb, heb, sh, st, SA, eq_of_label hhn he a ee.symm⟩
      · exact absurd (by rw [ee]; exact List.mem_map_of_mem he) a
  have d'' : g''.drop = false := PBP.drop.trans d2
  have u'' : UpBelow g'' := PBP.upBelow u2
  have cl'' : Clear g'' := PBP.clear cl2
  have cb'' : CondBelow g'' := PBP.condBelow cb2
  have c'' : g''.cond = g0.cond := PBP.cond.trans c2
  have bo'' : g''.bo = gS.bo := PBP.bo
  have re'' : gS.re ≤ g''.re := PBP.re
  have re0 := E2.1
  have nk'' : ∀ x, (NMem L.sure.ned x ∨ (∃ e ∈ L.bond, NMem e.2.sure.ned x) ∨ g0.re ≤ x) →
      HoonMap.get g''.cond x = Option.none := fun x hx => by
    rw [c'']
    rcases hx with a | ⟨e, he, a⟩ | a
    · exact hkg x a
    · exact ((hed e (by rw [eL]; exact he)).2 x a).2
    · exact condBelow_none hcb a
  -- the head's park, as facts about `gb` and `nexh`
  have PK : Ext g'' gb ∧ GrowU g'' gb ∧ gb.cond = g''.cond ∧ gb.re = g''.re ∧ g''.bo ≤ gb.bo ∧
      gb.drop = false ∧ (∀ k, k < g''.bo → HoonMap.get gb.blocks k = HoonMap.get g''.blocks k) ∧
      1 ≤ nexh.th.there ∧ g0.bo ≤ nexh.th.there ∧ nexh.th.there < gb.bo ∧ nexh.th.args = [] := by
    rcases pcase with ⟨rfl, rfl, _⟩ | ⟨_, rfl, rfl⟩
    · exact ⟨Ext.refl _, GrowU.refl _, rfl, rfl, Nat.le_refl _, d'', fun _ _ => rfl, b0, Nat.le_refl _,
        by simp only [jmp0]; omega, rfl⟩
    · refine ⟨(ext_emit _ _).trans (ext_tagged _ _ _), (growU_emit (b := ⟨[], [], Termin.hop (jmp0 g0.bo)⟩)
        (fun j hj => by simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; omega) u'').trans
        (growU_tagged _ _ _), by rw [tagged_cond]; rfl, by simp [Gen.emitted], by simp [Gen.emitted],
        by simp [Gen.emitted, d''], fun k hk => ?_, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
        by simp [jmp0, Gen.emitted], rfl⟩
      simp only [tagged_blocks, Gen.emitted, d'', Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
      rw [if_neg (by omega)]
  obtain ⟨hgb, hgbU, hgbc, hgbre, bgb, dgb, kgb, j1, j0, j2, ja⟩ := PK
  have ugb : UpBelow gb := hgbU.up u''
  have clgb : Clear gb := cl''.growU hgbU
  have cbgb : CondBelow gb := (condFresh_of_eq (by omega) hgbc).below cb''
  have HG : (nexh.th = jmp0 g0.bo ∧ nexh.laz = (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) ∧
        ((∀ x, FitsS (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).sure x) ∨ TotalC lib P ft)) ∨
      (nexh.th = jmp0 g''.bo ∧
        nexh.laz = Lazy.mk Sure.bunt [] ((g''.bo, ofSure (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).sure) :: (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond) ∧
        g''.bo < gb.bo ∧ HoonMap.get gb.blocks g''.bo = some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ ∧
        hinted env.cod q = some true) := by
    rcases pcase with ⟨rfl, rfl, hf⟩ | ⟨hq, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, hf⟩
    · refine Or.inr ⟨rfl, rfl, by simp [Gen.emitted], ?_, hq⟩
      simp only [tagged_blocks, Gen.emitted, d'', Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  -- the tail
  have hcq : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have hcp' : sixCount p ≤ 255 := by simp only [sixCount] at hcount; omega
  obtain ⟨⟨Qt, Rq⟩, jq1, jq2, fq, cqE⟩ := Sq.run (sup := sup) (region := region) (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))))
    (th := nexh.th) hcq (by omega) dgb ugb clgb cbgb j1 j2 ja
    (fun hm => by
      rw [eT] at hm
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := labL _ (htl e he); omega)
    Dt (fun x hx => ⟨by have := lt2' _ Mt x hx; omega, by rw [hgbc]; exact nk'' x (by
      rcases Mt x hx with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inr a.1))⟩)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
      exact ⟨by omega, _, th', by rw [kgb _ (by omega)]; exact PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)⟩)
    (by rw [eT]; exact htn)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      refine ⟨SA.dt, fun x hx => ?_⟩
      rw [hgbc]
      rcases SA.mt x hx with a | a
      · exact ⟨by have := ((hed eb (by rw [eL]; exact heb)).2 x a).1; omega, nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
      · exact ⟨by omega, nk'' x (Or.inr (Or.inr (by omega)))⟩)
    fT CS.2
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      exact SA.ct) h3
  have JQ : hinted env.cod q = some true → gb.bo ≤ nexq.th.there := fun hq => Jq hq (sup := sup) (region := region) (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))))
    (th := nexh.th) hcq (by omega) dgb ugb clgb cbgb j1 j2 ja
    (fun hm => by
      rw [eT] at hm
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := labL _ (htl e he); omega)
    Dt (fun x hx => ⟨by have := lt2' _ Mt x hx; omega, by rw [hgbc]; exact nk'' x (by
      rcases Mt x hx with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inr a.1))⟩)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
      exact ⟨by omega, _, th', by rw [kgb _ (by omega)]; exact PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)⟩)
    (by rw [eT]; exact htn)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      refine ⟨SA.dt, fun x hx => ?_⟩
      rw [hgbc]
      rcases SA.mt x hx with a | a
      · exact ⟨by have := ((hed eb (by rw [eL]; exact heb)).2 x a).1; omega, nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
      · exact ⟨by omega, nk'' x (Or.inr (Or.inr (by omega)))⟩)
    fT CS.2
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      exact SA.ct) h3
  have bq0 := Rq.bo
  -- the tail with its `+past`
  have Rq' : RunOKLS (Map := Map) lib N P ft (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) nexh.th Qt false gb g1'' nexq' := by
    rcases tcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Rq
    · exact Rq.past (fun r hr => by have := lt2' _ Mt r hr; omega) (fun e he => by
        rw [eT] at he; have := labL _ (htl e he); omega) ja (Rq.drop.trans dgb) (Rq.grow.up ugb) region
  have fq' : Flat nexq'.laz ∧ (∀ e ∈ entries nexq'.laz, Clean e.2.sure.ned) ∧ Clean nexq'.laz.sure.ned ∧
      ((∀ s, FitsS nexq'.laz.sure s) ∨ TotalC lib P fh) := by
    rcases tcase with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl⟩
    · exact ⟨fq, cqE, Sq.clean (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))) CS.2 h3, hf⟩
    · have fl : Flat (Lazy.mk (Sure.bunt : Sure S) [] ((g1'.bo, Lazy.mk nexq.laz.sure nexq.laz.fork []) ::
          nexq.laz.bond)) := flat_mk (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · show Lazy.mk nexq.laz.sure nexq.laz.fork [] = ofSure nexq.laz.sure
          rw [fq.1]; rfl
        · exact fq.2 e he)
      refine ⟨fl, fun e he => ?_, trivial, Or.inl (fun s => fitsS_bunt s)⟩
      rw [entries_flat fl] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Sq.clean (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))) CS.2 h3
      · exact cqE e (by rw [entries_flat fq]; exact he)
  have JT : nexq'.th.there ∉ (entries nexh.laz).map Prod.fst ∧ g0.bo ≤ nexq'.th.there := by
    have tq : g0.bo ≤ nexq'.th.there ∧
        (hinted env.cod q = some true → gb.bo ≤ nexq'.th.there) := by
      rcases tcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
      · refine ⟨?_, fun hq => JQ hq⟩
        rcases jq2 with a | a
        · rw [a]; exact j0
        · omega
      · simp only [jmp0]; exact ⟨by omega, fun _ => by omega⟩
    refine ⟨fun hm => ?_, tq.1⟩
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have fLh : Flat nexh.laz := by
      rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
      · exact fH
      · exact flat_mk (fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · rfl
          · exact fbh e (List.mem_filter.mp he).1)
    rw [entries_flat fLh] at he
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, e3, -, hq⟩
    · rw [e1] at he; have := labL _ (hhl e he); have := tq.1; omega
    · rw [e1] at he
      rcases List.mem_cons.mp he with rfl | he
      · have := tq.2 hq; simp at ee; omega
      · have := labL _ (hhl e he); have := tq.1; omega
  -- the head's goal
  have fLh : Flat nexh.laz := by
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
    · exact fH
    · exact flat_mk (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact fbh e (List.mem_filter.mp he).1)
  have eLh := entries_flat fLh
  have mH : ∀ e ∈ entries nexh.laz, e ∈ entries (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) ∨
      (e = (g''.bo, ofSure sH) ∧ g''.bo < gb.bo ∧
        HoonMap.get gb.blocks g''.bo = some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) := fun e he => by
    rw [eLh] at he
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, e2, e3, -⟩
    · rw [e1] at he; exact Or.inl (by rw [eH]; exact he)
    · rw [e1] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨rfl, e2, e3⟩
      · exact Or.inl (by rw [eH]; exact he)
  have sLh : nexh.laz.sure = sH ∨ nexh.laz.sure = Sure.bunt := by
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have nLh : ((entries nexh.laz).map Prod.fst).Nodup := by
    rw [eLh]
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
    · exact hhn
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hhn⟩
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have ee' : e.1 = g''.bo := ee
      have := labL _ (hhl e he); omega
  have cLh : Clean nexh.laz.sure.ned := by
    rcases sLh with e | e <;> rw [e]
    · exact CS.1
    · trivial
  -- the head
  have u1 : UpBelow g1'' := Rq'.grow.up ugb
  have cl1 : Clear g1'' := clgb.growU Rq'.grow
  have cb1 : CondBelow g1'' := Rq'.cfr.below cbgb
  have hq1 := Rq'.lo
  have hq2 := Rq'.hi
  have rq := Rq'.re
  have bq := Rq'.bo
  have regH : ∀ x, NMem sH.ned x → x < g1''.re ∧ HoonMap.get g1''.cond x = Option.none := fun x hx =>
    ⟨by have := lt2' _ Mh x hx; omega, by
      rw [Rq'.cfr.get_lt (by have := lt2' _ Mh x hx; omega), hgbc]
      exact nk'' x (by
        rcases Mh x hx with a | a
        · exact Or.inl a
        · exact Or.inr (Or.inr a.1))⟩
  obtain ⟨⟨Qh, Rp⟩, jp1, jp2, fp, cpE⟩ := Sp.run (sup := sup) (region := region) (L := nexh.laz) FH hcp' (by omega)
    (Rq'.drop.trans dgb) u1 cl1 cb1 hq1 hq2 (nextArgs_nil Rq'.ent ja) JT.1
    (by rcases sLh with e | e <;> rw [e]
        · exact Dh
        · trivial)
    (fun x hx => by
      rcases sLh with e | e <;> rw [e] at hx
      · exact regH x hx
      · simp [Sure.bunt, NMem] at hx)
    (fun e he => by
      rcases mH e he with he | ⟨rfl, lt, hb⟩
      · rw [eH] at he
        obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
        obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
        have hb'' : HoonMap.get gb.blocks eb.1 = some ⟨[], PB eb.1 ++ B, Termin.hop th'⟩ := by
          rw [kgb _ (by omega)]; exact PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)
        refine ⟨by omega, ?_⟩
        by_cases hm : eb.1 ∈ (entries (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))).map Prod.fst
        · obtain ⟨e0, h0, e0e⟩ := List.mem_map.mp hm
          obtain ⟨F0, hF0, -⟩ := Rq'.front e0 h0
          rw [← e0e] at hb''
          exact ⟨_, th', by rw [← e0e]; exact hF0 _ _ hb''⟩
        · exact ⟨_, th', by rw [Rq'.keep _ (by omega) hm]; exact hb''⟩
      · refine ⟨by omega, [], jmp0 g0.bo, ?_⟩
        rw [Rq'.keep _ lt (fun hm => by
          rw [eT] at hm
          obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
          have := labL _ (htl e he); omega)]
        exact hb)
    nLh
    (fun e he => by
      rcases mH e he with he | ⟨rfl, -, -⟩
      · rw [eH] at he
        obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
        refine ⟨SA.dh, fun x hx => ?_⟩
        rcases SA.mh x hx with a | a
        · have := ((hed eb (by rw [eL]; exact heb)).2 x a).1
          exact ⟨by omega, by rw [Rq'.cfr.get_lt (by omega), hgbc]; exact nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
        · exact ⟨by omega, by rw [Rq'.cfr.get_lt (by omega), hgbc]; exact nk'' x (Or.inr (Or.inr (by omega)))⟩
      · exact ⟨Dh, regH⟩)
    fLh cLh
    (fun e he => by
      rcases mH e he with he | ⟨rfl, -, -⟩
      · rw [eH] at he
        obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
        exact SA.ch
      · exact CS.1) h4
  -- the copy
  obtain ⟨n, g3', r, hc, hM, rfl⟩ := copyL_flat' fp fq'.1 hcp
  obtain ⟨R, hth, eth, fR, cR, lR⟩ := pairLS_ok (Fin := fun _ _ _ x y r => r = Tone.zero (C x y))
    (FinB := fun _ _ x y r => r = Tone.zero (C x y)) (hed := mk sH [] (bh.filter fun e => !(lazyEmpty e.2)))
    (tel := mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) Mf Mb (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    hfl hnL hkg
    (fun e he => ⟨(hlab e (by rw [eL]; exact he)).1, (hlab e (by rw [eL]; exact he)).2,
      (hed e (by rw [eL]; exact he)).1, (hed e (by rw [eL]; exact he)).2⟩)
    hok E2 G2U c2 hcb Mh Mt Dht PBP PBo fH fT SPL hhl htl hhn htn hgb hgbU hgbc hgbre
    (HG.imp id (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)) fq'.2.2.2
    Rq' Rp fq'.1 fp fq'.2.1 cpE fq'.2.2.1 (Sp.clean (L := nexh.laz) cLh h4) hc hM hu d0 hfix
    (fun _ _ _ x y r hn hr => Or.inr ⟨C x y, hr, hnot x y hn⟩)
    (fun _ _ x y hn => ⟨_, rfl, Or.inr ⟨C x y, rfl, hnot x y hn⟩⟩)
    (fun c hc σ Inv ν O n gul hS hF st' regs t tm x y n' r _ hI htr fx fy hx hy hr => by
      subst hr
      exact goalSemC_of_goalSem hI htr _ (some (C x y)) (hblk c hc σ O st' regs t gul x y fx fy hx hy))
    (fun c hc σ Inv ν O gul hS hB st' regs t tm x y hI htr fx fy hx hy res _ =>
      ⟨_, rfl, goalSemC_of_goalSem hI htr _ (some (C x y)) (hblk c hc σ O st' regs t gul x y fx fy hx hy)⟩)
  refine ⟨⟨_, R⟩, fun hm => ?_, hth, fR, cR⟩
  obtain ⟨e', he', ee⟩ := List.mem_map.mp hm
  have := lR e' he'
  have hthe : (pairRes n r nexq'.laz.bond nexp.laz.bond).th = n.th := rfl
  rw [hthe, eth] at ee
  simp only [jmp0] at ee
  omega

/-! ## The sure part stays clean -/


/-- **The cons with a hinted tail meets `LOKS false`** when the tail does
and the head meets `LOKSF` (`lokS_consS` with `lokS_cons_runH`). -/
theorem lokS_consH (lib : Lib) {N : Needs} (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y)
    (Kp : (p.pure = true ∧ MinkEq lib P fh p) ∨ hinted env.cod p = some true)
    (Kq : (q.pure = true ∧ MinkEq lib P ft q) ∨ hinted env.cod q = some true)
    (Jq : hinted env.cod q = some true → JNewLS (S := S) (Map := Map) env q)
    (hqh : hinted env.cod q = some true)
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fh p) (Sq : LOKS (S := S) (Map := Map) false lib N env P ft q) :
    LOKS (S := S) (Map := Map) false lib N env P (C fh ft) (Nomm.cons p q) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab hnd hed
    hfl hcs hce hr => (fun ⟨a, b, c, d, e⟩ => ⟨a, b, Or.inr c, d, e⟩)
      (lokS_cons_runH lib env hfh Kp Kq Jq hqh Sp Sq hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl
        hlab hnd hed hfl hcs hce hr)⟩
  have e : (runLC env sup (Nomm.cons p q) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, g'', hs, hr⟩ := bind_some hr
  simp only at hr
  obtain ⟨nexh, gb, hph, hr⟩ := bind_some hr
  obtain ⟨nexq, g1', h3, hr⟩ := bind_some hr
  obtain ⟨nexq', g1'', hp2, hr⟩ := bind_some hr
  obtain ⟨nexp, g2, h4, hcp⟩ := bind_some hr
  unfold splitL at hs
  obtain ⟨o', g5, h5, hs⟩ := bind_some hs
  obtain ⟨⟨hd', tl'⟩, g6, h6, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hs
  have CS := clean_splitLoop h6 hc
  -- the head's goal: `hed` or the bunt of `+past`
  have ch : Clean nexh.laz.sure.ned := by
    rcases Kq with ⟨qp, -⟩ | hq
    · rw [pastL_pure _ _ qp, pure_apply] at hph
      simp only [Option.some.injEq, Prod.mk.injEq] at hph
      rw [← hph.1]; exact CS.1
    · rcases pastL_hinted hq hph with ⟨x1, -⟩ | ⟨x1, -⟩
      · rw [x1]; exact CS.1
      · rw [x1]; trivial
  have cq := Sq.clean CS.2 h3
  have cq' : Clean nexq'.laz.sure.ned := by
    rcases Kp with ⟨pp, -⟩ | hp
    · rw [pastL_pure _ _ pp, pure_apply] at hp2
      simp only [Option.some.injEq, Prod.mk.injEq] at hp2
      rw [← hp2.1]; exact cq
    · rcases pastL_hinted hp hp2 with ⟨x1, -⟩ | ⟨x1, -⟩
      · rw [x1]; exact cq
      · rw [x1]; trivial
  have cp := Sp.clean ch h4
  unfold copyL at hcp
  obtain ⟨oc, g7, h7, hcp⟩ := bind_some hcp
  obtain ⟨laz, g8, h8, hcp⟩ := bind_some hcp
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hcp
  obtain ⟨rfl, rfl⟩ := hcp
  exact clean_copyLazyL h8 cp cq'


/-- **The jump of the cons with a hinted tail is a block it made.** -/
theorem jNewLS_consH (lib : Lib) {N : Needs} (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y)
    (Kp : (p.pure = true ∧ MinkEq lib P fh p) ∨ hinted env.cod p = some true)
    (Kq : (q.pure = true ∧ MinkEq lib P ft q) ∨ hinted env.cod q = some true)
    (Jq : hinted env.cod q = some true → JNewLS (S := S) (Map := Map) env q)
    (hqh : hinted env.cod q = some true)
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fh p) (Sq : LOKS (S := S) (Map := Map) false lib N env P ft q) :
    JNewLS (S := S) (Map := Map) env (Nomm.cons p q) :=
  fun hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    (lokS_cons_runH lib env hfh Kp Kq Jq hqh Sp Sq hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs
      hce hr).2.2.1

end Comp
end SkaModel
end Formalization
