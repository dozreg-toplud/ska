import lemmas.Ska.CompSevenLS
import lemmas.Ska.CompNCFour

/-!
# `[4 p]` under a flat lazy goal, `p` any nomm with `LOKS`

README Gaps 12.28.  Under `%next L th` the `%4` case of `run` is
`+collapse-lazy-atom` (`CollPre`: the register `d` the increment writes, the
label `there` it hops to, the ops at the goal's entries), the block
`[inc arg d] hop there` and the run of `p` under `%next (lazy-from-reg arg)`
into it.  The proof follows the indirect call: `incLB` puts the block of the
increment behind `p`'s run (as `nokLB`), `collLS` puts the collapse in front
(as `kerfLB`, with `collLC`'s conversion of the goal).  The fronts read `d`:
the goal's sure register (`x = true`, `holdsN_atom_mem`) or a fresh one held
by the witness (`fourWit`).

* `atomWit`, `incLB`: the block of the increment behind the run of `p`.
* `fourWit`, `collLS`: the collapse in front, `RunOKLS` with `x = true`.
* `lokS_four_run`, `lokS_four`, `jNewLS_four`: `[4 p]` meets `LOKS true`
  when `p` meets `LOKS` (any flag), and its jump is always a block it made.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The block of the increment behind the operand -/

/-- The witness relation of a run whose product is an atom and that put no
op in front of a goal entry. -/
def atomWit : Wit := fun _ v d _ => (∃ m, v = A m) ∧ d = Need.none

/-- **The block of the increment behind the operand's run** (`nokLB` for
`%4`): `RunOKLB` of the operand for `fb` under `%next (lazy-from-reg arg)
(jmp0 o)`, from the state with the block `[inc arg pro] hop there` made at
`o`, is `RunOKLB` of `[4 fb]` under `%next (lazy-from-reg pro) (jmp0
there)` from the state before, with products atoms (`atomWit`). -/
theorem incLB {lib : Lib} {P : Noun → Prop} {f fb : Noun} (M : MinkC4 lib P f fb)
    {g2 g3 g' : Gen Map} {nex : NextL S} {th' pro : Nat} {Q : Wit} {x : Bool}
    (hpro : pro < g2.re) (hpk : HoonMap.get g2.cond pro = Option.none) (cb2 : CondBelow g2)
    (r3 : g3.re = g2.re + 1) (b3 : g3.bo = g2.bo + 1) (cn3 : g3.cond = g2.cond) (E3 : Ext g2 g3)
    (G3 : GrowU g2 g3)
    (k3o : HoonMap.get g3.blocks g2.bo = some ⟨[], [Pole.inc g2.re pro], Termin.hop (jmp0 th')⟩)
    (R : RunOKLB (Map := Map) lib P fb (ofSure (lazyReg g2.re)) (jmp0 g2.bo) Q x g3 g' nex) :
    RunOKLB (Map := Map) lib P f (ofSure (lazyReg pro)) (jmp0 th') atomWit false g2 g' nex := by
  have e0 : entries (ofSure (lazyReg g2.re : Sure S)) = [] := entries_ofSure _
  have e1 : entries (ofSure (lazyReg pro : Sure S)) = [] := entries_ofSure _
  have rl := R.re
  have bl := R.bo
  have nk : ∀ x, g2.re ≤ x → HoonMap.get g2.cond x = Option.none := fun x hx => condBelow_none cb2 hx
  have kN : HoonMap.get g'.blocks g2.bo = some ⟨[], [Pole.inc g2.re pro], Termin.hop (jmp0 th')⟩ := by
    rw [R.keep _ (by omega) (by rw [e0]; simp)]; exact k3o
  have lab' : ∀ e ∈ entries nex.laz, g3.bo ≤ e.1 := fun e he => by
    rcases (R.labs e he).1 with h | h
    · rw [e0] at h; cases h
    · exact h.1
  -- the block of the increment in any code that agrees with the run
  have hbN : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (ned : Need) (s0 s : Noun),
      AgreeLB lib O c gul st t cf ned g2 g' nex.laz s0 s →
      HoonMap.get c.blocks g2.bo = some ⟨[], [Pole.inc g2.re pro], Termin.hop (jmp0 th')⟩ := by
    intro cf hcf c σ O gul st t ned s0 s ag
    have hc : ∀ x, x < g3.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun x hx => by
      rw [hcf x (by omega), R.cfr.get_lt hx, cn3]
    rw [ag.1 g2.bo (Nat.le_refl _) (by omega) (fun hm => by
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega), kN]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
      renJmp_nil _ (show (jmp0 th').args = [] from rfl)]
    rw [unproxy_none (by rw [hc _ (by omega)]; exact nk _ (Nat.le_refl _)),
      unproxy_none (by rw [hc _ (by omega)]; exact hpk)]
  have hK : ∀ (ned : Need) z, ((z < g2.re ∨ NMem ned z) ∧ ¬ NMem (lazyReg pro : Sure S).ned z) → z ≠ pro :=
    fun ned z hz e => hz.2 (by subst e; simp [lazyReg, NMem])
  have hK3 : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ z,
      ((z < g2.re ∨ NMem ned z) ∧ ¬ NMem (lazyReg pro : Sure S).ned z) →
      ((z < g3.re ∨ NMem ned z) ∧ ¬ NMem (ofSure (lazyReg g2.re : Sure S)).sure.ned z) := fun ned hned z hz =>
    ⟨hz.1.imp (fun h => by omega) id, fun hm => by
      simp only [ofSure, sure_mk, lazyReg, NMem] at hm
      rcases hz.1 with h | h
      · omega
      · have := hned z h; omega⟩
  -- the shared part of the two `sem` clauses: through the block of the increment
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g2 g' nex.laz s0 s) → (∀ x, NMem ned x → g'.re ≤ x) →
      Forall2 (FrameRel lib (ν st)) t tm → ∀ rb,
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g3.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg g2.re : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg g2.re : Sure S)).sure (jmp0 g2.bo) (Q s) rb →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g2.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg pro : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg pro : Sure S)).sure (jmp0 th') (atomWit s) (incTone tm rb) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rb G
    have hb := hbN cf hcf c σ O gul st t ned s0 s (ag st)
    cases rb with
    | one q => exact G
    | two t' => exact G
    | zero x =>
      obtain ⟨st1, R1, d, w, hI1, hν1, _, hh1, _, k1, e3⟩ := G.1 (fitsS_lazyReg _ x)
      have hx : SkaModel.read g2.re R1 = some x := hh1
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st1) R1 t _ _ hb
      cases x with
      | atom n =>
        rw [show [Pole.inc g2.re pro] = [Pole.inc g2.re pro] ++ [] from rfl, runs_inc hx, execBlob_hop] at hj
        simp only [incTone]
        refine ⟨fun _ => ⟨st1, store pro (A (n + 1)) R1, Need.none, A 0, hI1, hν1, ⟨⟨n + 1, rfl⟩, rfl⟩,
          read_store_eq _ _ _, trivial, fun z hz => ?_, e3.trans hj⟩, fun nf => absurd (fitsS_lazyReg _ _) nf⟩
        rw [read_store_ne (hK ned z hz)]
        exact k1 z (hK3 ned hned z hz)
      | cell u v =>
        rw [show [Pole.inc g2.re pro] = [Pole.inc g2.re pro] ++ [] from rfl, crashes_inc hx] at hj
        exact ⟨Tone.two t, st1, hI1, hν1, e3.trans hj, ToneRel.two (frames_mono hν1 htr)⟩
  refine ⟨by omega, by omega, R.drop.trans E3.2.2.1, fun o ho hn => ?_, G3.trans R.grow,
    (condFresh_of_eq (by omega) cn3).trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).1.elim (fun h => (by rw [e0] at h; cases h))
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup,
    fun s v d w r hq hr => (by obtain ⟨_, rfl⟩ := hq; exact hr.elim),
    fun s hs hf => ?_, R.ncond, R.econd, fun e he => (by rw [e1] at he; cases he), ?_, ?_⟩
  · rw [R.keep o (by omega) (by rw [e0]; simp), E3.2.2.2 o ho]
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, kN, rfl, rfl⟩
  · rcases R.regs r hr with h | h
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h
      exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · rcases (R.eregs e he).2 r hr with ⟨e0', h0, _⟩ | h | h
    · rw [e0] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · have N := R.nec s hs hf
    have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg g2.re : Sure S) (jmp0 g2.bo)) tm r →
        r = Tone.two tm := fun hb => by
      rcases hb with e | ⟨q, _, hq⟩
      · exact e
      · exact absurd (fitsS_lazyReg _ q) hq
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
      rw [bad (N.1 gul n' tm rb hb)]
      exact Or.inl rfl
    · obtain ⟨rb, hmb, hbad⟩ := N.2 gul tm
      refine ⟨_, M.bwd hs hmb, ?_⟩
      rw [bad hbad]
      exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g3 g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rb
      (R.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb ag3 hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g3 g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨rb, hmb, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag3 hned regs hh hn
      res hres
    exact ⟨_, M.bwd hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rb G⟩

/-! ## `+collapse-lazy-atom` in front -/

/-- **The witness relation of `[4 p]` under a lazy goal**: the product is
an atom; the register `d` the increment writes is the goal's (the witness
asks nothing, the fronts read `d` as a goal register) or a fresh one that
holds the product. -/
def fourWit (L : Lazy S) (d : Nat) : Wit := fun _ v dd w => (∃ m, v = A m) ∧
  ((NMem L.sure.ned d ∧ dd = Need.none) ∨ (¬ NMem L.sure.ned d ∧ dd = Need.this d ∧ w = v))

/-- **`+collapse-lazy-atom` in front of the rest of `[4 p]`, under a lazy
goal** (`collLC` for `RunOKLB`, every shape of the sure need): `CollPre`
from `g0` to `g2` with the register `r` and the label `there`, and
`RunOKLB` of the rest under `%next (lazy-from-reg r) (jmp0 there)` whose
result entries are fresh, give `RunOKLS` under `%next L th` with `x = true`
and the witness `fourWit L r`; no result entry is at a goal label. -/
theorem collLS {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {g0 g2 g1 : Gen Map}
    {r there : Nat} {nex : NextL S} (CP : CollPre L th g0 g2 r there)
    (hu : UpBelow g0) (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re)
    (hec : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfr : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → g2.re ≤ x)
    (R : RunOKLB (Map := Map) lib P f (ofSure (lazyReg r)) (jmp0 there) atomWit false g2 g1 nex) :
    RunOKLS (Map := Map) lib P f L th (fourWit L r) true g0 g1 nex := by
  have e2 : entries (ofSure (lazyReg r : Sure S)) = [] := entries_ofSure _
  have Re : Ext g2 g1 := ⟨R.re, R.bo, R.drop, fun o ho => R.keep o ho (by rw [e2]; simp)⟩
  have rl := R.re
  have bl := R.bo
  have c1 := CP.le
  have c2 := CP.bo1
  have rlt := CP.rlt
  have hth : th.args = [] := CP.args
  have lab' : ∀ e ∈ entries nex.laz, g2.bo ≤ e.1 := fun e he =>
    (R.labs e he).1.elim (fun h => by rw [e2] at h; cases h) (fun h => h.1)
  have hcf2 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun cf hcf x hx =>
    (hcf x (by omega)).trans (R.cfr.get_lt hx)
  have ur : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      unproxy cf r = r := fun cf hcf => unproxy_none (by rw [hcf2 cf hcf r rlt]; exact CP.rkey)
  have rne : ∀ x, (x < g0.re ∨ g1.re ≤ x) → ¬ NMem L.sure.ned x → x ≠ r := fun x hx hn e => by
    subst e
    rcases CP.rreg with h | h
    · exact hn h
    · rcases hx with hx | hx <;> omega
  -- the conversion of the rest's goal into the goal's
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
      Forall2 (FrameRel lib (ν st)) t tm → ∀ rt,
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g2.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg r : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg r : Sure S)).sure (jmp0 there) (atomWit s) rt →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
        L.sure th (fourWit L r s) rt := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rt G
    cases rt with
    | one q => exact G
    | two t' => exact G
    | zero p =>
      obtain ⟨st1, R1, dd, w, hI1, hν1, ⟨⟨m, rfl⟩, _⟩, hp1, _, k1, e1⟩ := G.1 (fitsS_lazyReg _ _)
      have hr1 : SkaModel.read r R1 = some (A m) := hp1
      have kk : ∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs := fun x hx =>
        k1 x ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun e =>
          rne x (hx.1.imp id (fun h => hned x h)) hx.2 e⟩
      rcases CP.shape with ⟨eth, -, hfa, hfit⟩ | ⟨eth, ebo, hnf, F, hF, hPF⟩
      · -- every atom fits: the collapse hops to `th`
        subst eth
        refine ⟨fun _ => ?_, fun nf => absurd (hfa m) nf⟩
        by_cases hin : NMem L.sure.ned r
        · exact ⟨st1, R1, Need.none, A 0, hI1, hν1, ⟨⟨m, rfl⟩, Or.inl ⟨hin, rfl⟩⟩, (hfit R1 m hr1).1, trivial, kk,
            by rw [e1, jmp0_of_args hth]⟩
        · exact ⟨st1, R1, Need.this r, A m, hI1, hν1, ⟨⟨m, rfl⟩, Or.inr ⟨hin, rfl, rfl⟩⟩, (hfit R1 m hr1).1, hr1,
            kk, by rw [e1, jmp0_of_args hth]⟩
      · -- no atom fits: the collapse hops to its block `[%bom ~]`
        refine ⟨fun hf => absurd hf (hnf m), fun _ => ?_⟩
        subst eth
        have hcb0 : HoonMap.get c.blocks g0.bo =
            some ⟨[], F.map (renPole (unproxy cf)), Termin.bom Option.none⟩ := by
          rw [(ag st1).1 g0.bo (Nat.le_refl _) (by omega) (fun hm => by
            obtain ⟨e, he', e1⟩ := List.mem_map.mp hm; have := lab' e he'; omega), Re.2.2.2 _ (by omega), hF]
          simp [unproxyBlob, renBlob, renFin]
        have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st1) R1 t _ _ hcb0
        obtain ⟨S1, S2⟩ := hPF (unproxy cf) (ur cf hcf)
          (fun x hx => by simp only [NMem] at hx; rw [hx]; exact ur cf hcf)
          (fun x hx => by simp only [unproxy, hcf2 cf hcf x hx]) lib σ O c gul st1 t R1 m hr1
        refine ⟨Tone.two t, st1, hI1, hν1, ?_, ToneRel.two (frames_mono hν1 htr)⟩
        rw [e1, hj, ← List.append_nil (F.map (renPole (unproxy cf)))]
        by_cases fT : FitsS (⟨Need.this r, L.sure.lok⟩ : Sure S) (A m)
        · obtain ⟨R', hr', -, -⟩ := S1 fT
          rw [hr', execBlob_bom']
        · exact S2 fT [] _
  have agR : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun), (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) →
      ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g2 g1 nex.laz s0 s :=
    fun cf c ned σ O gul t s0 s ag st' => agreeLB_mono (ag st') (by omega)
  -- the fronts at the state level: the collapse's ops read `r`
  have FS : FrontsS (Map := Map) (fourWit L r) true g0 g1 L nex := by
    intro e he
    obtain ⟨A0, hA, hP⟩ := CP.at_ e he
    have hlt := hlab e he
    refine ⟨A0, fun B fin hb => by rw [Re.2.2.2 _ (by omega)]; exact hA B fin hb,
      fun cf hcf => Or.inr ⟨fun hm => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; omega, ?_⟩⟩
    refine ⟨fun x hx => by simp [Sure.bunt, NMem] at hx, fun s v d w _ x _ hx => by simp [Sure.bunt, NMem] at hx,
      fun s v d w _ _ => fitsS_bunt s, fun lib σ O c gul st t R0 s v d w hq _ hd hE => ?_⟩
    rw [gsE_true] at hE
    obtain ⟨⟨m, rfl⟩, hw⟩ := hq
    have hr0 : SkaModel.read r R0 = some (A m) := by
      rcases hw with ⟨hin, rfl⟩ | ⟨_, rfl, rfl⟩
      · exact holdsN_atom_mem hE hin
      · exact hd
    obtain ⟨S1, S2⟩ := hP (unproxy cf) (ur cf hcf) (fun x hx => unproxy_none (by
        have hx1 := hec e he x hx
        rw [hcf2 cf hcf x (by omega), CP.pfor.1.get_lt hx1.1]; exact hx1.2))
      (fun x hx => by simp only [unproxy, hcf2 cf hcf x hx]) lib σ O c gul st t R0 m hr0
    refine ⟨fun fv => ?_, S2⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 fv
    exact ⟨R2, r2, hh2, fun x _ hn' => k2 x hn'⟩
  have dreg : ∀ s v d w x, fourWit L r s v d w → NMem d x → g0.re ≤ x ∧ x < g1.re := fun s v d w x hq hx => by
    obtain ⟨_, ⟨_, rfl⟩ | ⟨hin, rfl, _⟩⟩ := hq
    · exact hx.elim
    · simp only [NMem] at hx; subst hx; exact ⟨CP.rreg.resolve_left hin, by omega⟩
  have eup : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → x < g1.re := fun e he x hx => by
    rcases (R.eregs e he).2 x hx with ⟨e0, h0, _⟩ | h | h
    · rw [e2] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; omega
    · exact h.2
  refine ⟨⟨by omega, by omega, Re.2.2.1.trans CP.drop, fun o ho hn' => by rw [Re.2.2.2 o (by omega), CP.other o ho hn'],
    (CP.grow.toU hu).trans R.grow, CP.pfor.1.trans R.cfr, R.lo, R.hi, ?_, fun x hx => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun x hx => Or.inr (Or.inr ⟨by have := hfr e he x hx; omega, eup e he x hx⟩)⟩,
    fun e he => ⟨Or.inr ⟨by have := lab' e he; omega, (R.labs e he).1.elim (fun h => by rw [e2] at h; cases h)
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup,
    dreg, fun s hs hf => ?_, R.ncond, R.econd,
    FS.toFront (by omega) hsl (fun e he y hy hm => by
      rw [gsE_true] at hy; have := hfr e he y hm; have := hsl y hy; omega) dreg, ?_, ?_⟩, FS⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rcases CP.shape with ⟨eth, -⟩ | ⟨eth, ebo, -, F, hF, -⟩
      · exact Or.inr (by rw [e, eth]; exact jmp0_of_args hth)
      · rw [e, eth]; exact Or.inl ⟨_, (Re.2.2.2 g0.bo (by omega)).trans hF, rfl, rfl⟩
  · rcases R.regs x hx with h | h
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; subst h
      rcases CP.rreg with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · obtain ⟨N1, N2⟩ := R.nec s hs hf
    have bad : ∀ {tm : Trace} {rt : Tone}, BadC (CGoal.next (lazyReg r : Sure S) (jmp0 there)) tm rt →
        BadC (CGoal.next L.sure th) tm rt := fun h => by
      rcases h with e | ⟨q, _, nq⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg _ q) nq
    exact ⟨fun gul n tm rt hm => bad (N1 gul n tm rt hm), fun gul tm => by
      obtain ⟨rt, hm, hb⟩ := N2 gul tm; exact ⟨rt, hm, bad hb⟩⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s rt hI htr hs hm ag hned regs hh hn
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rt
      (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s rt hI htr hs hm (agR cf c ned σ O gul t s0 s ag) hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rt, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs (agR cf c ned σ O gul t s0 s ag)
      hned regs hh hn res hres
    exact ⟨rt, hm, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rt G⟩

/-! ## `[4 p]` under a flat lazy goal -/

/-- **The `%4` case of `run` under `%next L th`**, with `collPick`. -/
theorem runLC_n4_next (env : CallEnv) (sup : Option Nomm) (p : Nomm) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.n4 p) (CGoalL.next L th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨L, th⟩
      let (pro, th') ← collPick th a
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
  conv => lhs; unfold runLC
  rfl

/-- **`[4 p]` whose operand meets `LOKS` (any flag), under a flat lazy
goal**, from a state as `LOKS.run` asks: `RunOKLS` with `x = true` and the
witness `fourWit L d`, the jump a new block at none of the result's
entries, the result flat with clean entries.  `collapsePre_spec`, the block
of the increment, the operand's `LOKS` under `%next (lazy-from-reg arg)
(jmp0 o)` (a flat goal with no entry), `incLB`, `collLS`. -/
theorem lokS_four_run (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun} {xp : Bool}
    (M : MinkC4 lib P f fb) (Sp : LOKS (S := S) (Map := Map) xp lib env P fb p)
    {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcount : sixCount (Nomm.n4 p) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hta : th.args = [])
    (ht : th.there ∉ (entries L).map Prod.fst) (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hr : runLC env sup (Nomm.n4 p) (CGoalL.next L th) region g0 = some (nex, g1)) :
    (∃ Q, RunOKLS (Map := Map) lib P f L th Q true g0 g1 nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧ g0.bo ≤ nex.th.there ∧ Flat nex.laz ∧
      (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  rw [runLC_n4_next] at hr
  obtain ⟨a, gA, hc2, h⟩ := bind_some hr
  obtain ⟨⟨d, th'⟩, g2, hm, h⟩ := bind_some h
  have CP := collapsePre_spec hc2 hm d0 hcb (fun x hx => (hsl x hx).1) (fun x hx => (hsl x hx).2)
    (List.nodup_cons.mpr ⟨ht, hnd⟩)
    (fun e he => ⟨(hlab e he).1, by obtain ⟨B, th'', hb⟩ := (hlab e he).2; exact ⟨B, _, hb⟩⟩)
    (fun e he x hx => ((hed e he).2 x hx).1)
  simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply] at h
  obtain ⟨g3, hg3⟩ : ∃ g3 : Gen Map, g3 = { g2 with re := g2.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [Pole.inc g2.re d], Termin.hop (jmp0 th')⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g3.emitted blk := ⟨_, rfl⟩
  have hbo3 : g3.bo = g2.bo := by rw [hg3]
  have hre3 : g3.re = g2.re + 1 := by rw [hg3]
  have hcn3 : g3.cond = g2.cond := by rw [hg3]
  have hdr3 : g3.drop = false := by rw [hg3]; exact CP.drop.trans d0
  rw [← hg3, ← hblk, ← hgE] at h
  have hboE : gE.bo = g2.bo + 1 := by rw [hgE, emitted_bo, hbo3]
  have hreE : gE.re = g2.re + 1 := by rw [hgE, emitted_re, hre3]
  have hcnE : gE.cond = g2.cond := by rw [hgE, ← hcn3]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr3
  have hbE : HoonMap.get gE.blocks g2.bo = some blk := by rw [hgE, ← hbo3]; exact emitted_get g3 blk hdr3
  have c1 := CP.le
  have c2 := CP.bo1
  have hth' : 1 ≤ th' ∧ th' < g2.bo := by
    rcases CP.shape with ⟨e, eb, -⟩ | ⟨e, eb, -⟩ <;> (rw [e]; omega)
  have G2E : Grow g2 gE := by
    have g23 : Grow g2 g3 := by rw [hg3]; exact grow_re g2
    have g3E : Grow g3 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk]; exact jumpsBelow_hop (j := jmp0 th') hth'.1 (by simp only [jmp0]; omega)
    exact g23.trans g3E
  have GU2 : GrowU g0 g2 := CP.grow.toU hu
  have hu2 : UpBelow g2 := GU2.up hu
  have GU : GrowU g2 gE := G2E.toU hu2
  have E2E : Ext g2 gE := by rw [hgE, hg3]; exact (ext_re _).trans (ext_emit _ _)
  have cb2 : CondBelow g2 := CP.pfor.1.below hcb
  have cbE : CondBelow gE := fun x hx => by rw [hcnE] at hx; have := cb2 x hx; omega
  have eR : entries (ofSure (lazyReg g2.re : Sure S)) = [] := entries_ofSure _
  obtain ⟨⟨Qp, Rp⟩, pne, pj, pfl, pec⟩ := Sp.run (sup := sup) (L := ofSure (lazyReg g2.re)) (th := jmp0 g2.bo)
    (region := region) (by simpa only [sixCount] using hcount) (by omega) hdE (GU.up hu2)
    ((hcl0.growU GU2).growU GU) cbE
    (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) rfl (by rw [eR]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by omega, by rw [hcnE]; exact condBelow_none cb2 (Nat.le_refl _)⟩)
    (fun e he => by rw [eR] at he; cases he) (by rw [eR]; simp) (fun e he => by rw [eR] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [eR] at he; cases he) h
  have RA := incLB (Map := Map) M (g2 := g2) (g3 := gE) (pro := d) (th' := th') CP.rlt CP.rkey cb2 hreE hboE hcnE
    E2E GU (by rw [hbE, hblk]) Rp.toRunOKLB
  have hfr : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → g2.re ≤ x := fun e he x hx => by
    rcases (Rp.eregs e he).2 x hx with ⟨e0, h0, _⟩ | h | h
    · rw [eR] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; omega
    · omega
  have RS := collLS (Map := Map) CP hu (fun e he => (hlab e he).1) (fun x hx => (hsl x hx).1)
    (fun e he x hx => (hed e he).2 x hx) hfr RA
  refine ⟨⟨_, RS⟩, pne, ?_, pfl, pec⟩
  rcases pj with e | e
  · rw [e]; simp only [jmp0]; omega
  · omega

/-- **`[4 p]` meets `LOKS true`** when its operand meets `LOKS` (any flag),
for a formula `f` whose `+mink` is the increment of the operand's. -/
theorem lokS_four (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun} {xp : Bool}
    (M : MinkC4 lib P f fb) (Sp : LOKS (S := S) (Map := Map) xp lib env P fb p) :
    LOKS (S := S) (Map := Map) true lib env P f (Nomm.n4 p) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun {sup L th region g0 g1 nex} hcount b0 d0 hu hcl hcb
    h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr => ?_⟩
  · obtain ⟨arg, o, gX, h⟩ := runLC_n4_last (fun z o h => by cases h) hr
    exact Sp.clean (L := ofSure (lazyReg arg)) trivial h
  · obtain ⟨H, ne, j, fl, ec⟩ := lokS_four_run lib env M Sp hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd
      hed hr
    exact ⟨H, ne, Or.inr j, fl, ec⟩

/-- **The jump of `[4 p]` is always a block it made.** -/
theorem jNewLS_four (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun} {xp : Bool}
    (M : MinkC4 lib P f fb) (Sp : LOKS (S := S) (Map := Map) xp lib env P fb p) :
    JNewLS (S := S) (Map := Map) env (Nomm.n4 p) := by
  intro sup L th region g0 g1 nex hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr
  exact (lokS_four_run lib env M Sp hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hr).2.2.1

end Comp
end SkaModel
end Formalization
