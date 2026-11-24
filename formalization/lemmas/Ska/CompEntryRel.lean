import lemmas.Ska.CompSevenOne
import lemmas.Ska.CompRelX

/-!
# The relaxed `sem` for goals with entries

README Gaps 12.2.  The strict `RunOKE` (`CompEntryGoal.lean`) asks the input
registers `ned` to lie at or above the end of the run, in its `sem` and in
`FrontSem`.  Here both take `InR` of the run for its goal
`%next laz.sure th` instead: from the end on, below the start and outside the
goal's sure need, or in the result's sure need.

* `FrontER`: the front clause of `RunOKE` with that hypothesis (`FrontK` at
  `InR`).  `[0 axe]` meets it with no use of the hypothesis
  (`frontER_n0`, from `fillSem_from`), and `[1 k]` because `+mede` writes
  only the entries' own registers and the registers it allocates, which
  `InR` excludes from `ned` (`runOKE_n1R`, through `runOKE_n1K`).  The
  registers of the goal's entries need not be excluded from `ned`: the
  front of a fill keeps only registers outside the filled need, and the
  ops `F` of `+mede` at one entry write that entry's registers and fresh
  ones only.
* `semGR_sevenE`: `runOKG_sevenE` with the relaxed `sem`: `SemGR` of `q`,
  `SemNR` and `FrontER` of `p` give `SemGR` of `[7 p q]`.  It needs neither
  `hgm` nor `nf` of the strict form, and no disjointness: `KeepI` keeps the
  input registers whatever they are.
* `semPR_seven1`: `[7 [1 k] q]` for `%done` with `q` in `FragX`, the relaxed
  counterpart of `runOKP_seven1`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The relaxed front clause of `RunOKE`**: `FrontK` with `InR` of the run
for its goal `%next laz.sure th`. -/
abbrev FrontER (nm : Nomm) (laz : Lazy S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  FrontK (Map := Map) (InR (CGoal.next laz.sure th) g0 g1 nex.laz.sure.ned) nm laz g0 g1 nex

/-- For `%done` and `%pick` the two relaxed `sem` agree; this direction
needs no hypothesis. -/
theorem SemPR.toG {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (h : SemPR (Map := Map) lib nm goal g0 g1 nex) : SemGR (Map := Map) lib nm goal g0 g1 nex :=
  fun c ned σ O st t gul s0 s ag hned regs hh hn =>
    goalSem_mono (fun _ hr => hr.elim (fun e => Or.inl e.1) Or.inr) goal _ (h c ned σ O st t gul s0 s ag hned regs hh hn)

/-- **`[0 axe]` for a goal with entries: the relaxed front.** -/
theorem frontER_n0 {axe : Nat} {laz laz' : Lazy S} {th : Jmp} {g : Gen Map} (hf : fromL axe laz = some laz') :
    FrontER (Map := Map) (Nomm.n0 axe) laz th g g ⟨laz', th⟩ :=
  frontK_n0 hf

/-- **`[1 k]` for a goal with entries: the relaxed front and `sem`.** -/
theorem runOKE_n1R (lib : Lib) {k : Noun} {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (h : runL (Nomm.n1 k) (CGoalL.next laz th) region g0 = some (nex, g1))
    (d0 : g0.drop = false) (hu : UpBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hd : Distinct laz.sure.ned) (hreg : ∀ r, NMem laz.sure.ned r → r < g0.re)
    (hed : ∀ e ∈ entries laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → r < g0.re)
    (hnd : ((entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩) :
    FrontER (Map := Map) (Nomm.n1 k) laz th g0 g1 nex ∧ SemNR (Map := Map) lib (Nomm.n1 k) laz.sure th g0 g1 nex := by
  obtain ⟨RE, FK, SK, hl⟩ := runOKE_n1K lib h d0 hu h1 h2 hd hreg hed hnd hlab
  have re := RE.re
  have nb : ∀ r, ¬ NMem nex.laz.sure.ned r := fun r hr => by
    rw [hl] at hr; simp [ofSure, Sure.bunt, NMem] at hr
  refine ⟨FK _ (fun x hx ⟨a, b⟩ => ?_), fun c ned σ O st t gul s0 s ag hned regs _ _ => SK _ (fun r hr => ?_) c ned
    σ O st t gul s0 s ag regs⟩
  · rcases hx with e | ⟨e, _⟩ | e
    · omega
    · omega
    · exact nb x e
  · rcases hr with ⟨e, e'⟩ | e
    · exact ⟨e', fun ⟨a, _⟩ => by omega⟩
    · rcases hned r e with x | ⟨x, x'⟩ | x
      · exact ⟨fun hm => by have := hreg r hm; omega, fun ⟨_, b⟩ => by omega⟩
      · exact ⟨x', fun ⟨a, _⟩ => by omega⟩
      · exact (nb r x).elim

/-- **`[7 p q]` when `p` runs for a goal with entries, with the relaxed
`sem`**: `SemGR` of `q` and the relaxed front and `sem` of `p` for the goal
the run of `q` returns give `SemGR` of the whole. -/
theorem semGR_sevenE {lib : Lib} {p q : Nomm} {goal : CGoal S} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (hq : RunOKG (Map := Map) lib q goal g0 g1 nx) (Sq : SemGR (Map := Map) lib q goal g0 g1 nx)
    (hp : RunOKE (Map := Map) lib p nx.laz nx.th g1 g2 nex) (Fp : FrontER (Map := Map) p nx.laz nx.th g1 g2 nex)
    (Sp : SemNR (Map := Map) lib p nx.laz.sure nx.th g1 g2 nex) :
    SemGR (Map := Map) lib (Nomm.n7 p q) goal g0 g2 nex := by
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have q1 := hq.ext.1
  have q2 := hq.ext.2.1
  have p1 := hp.re
  have notq : ∀ r, r < g0.re → ¬ GMem goal r → ¬ NMem nx.laz.sure.ned r := fun r h1 h2 hm => by
    rcases hq.regs r hm with h | h
    · exact h2 h
    · omega
  have hnedP : ∀ r, NMem ned r → InR (Map := Map) (CGoal.next nx.laz.sure nx.th) g1 g2 nex.laz.sure.ned r :=
    fun r hr => by
      rcases hned r hr with h | ⟨h1, h2⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by omega, notq r h1 h2⟩)
      · exact Or.inr (Or.inr h)
  have hnedQ : ∀ r, NMem ned r → InR (Map := Map) goal g0 g1 nx.laz.sure.ned r := fun r hr => by
    rcases hned r hr with h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · rcases hp.regs r h with h' | h'
      · exact Or.inr (Or.inr h')
      · exact Or.inl h'.1
  have agP : AgreeP lib O c gul st t ned g1 g2 nex.laz s0 s :=
    ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans q2 h0) h1 hnl, ag.2⟩
  have Sp' := Sp c ned σ O st t gul s0 s agP hnedP regs hh hn
  show GoalSem lib O c gul st _ regs t nex.th goal (pureEval (Nomm.n7 p q) s)
  cases ev : pureEval p s with
  | none =>
    rw [ev] at Sp'
    have e7 : pureEval (Nomm.n7 p q) s = none := by simp [pureEval, ev]
    rw [e7]; exact goalSem_none goal Sp'
  | some v =>
    rw [ev] at Sp'
    have e7 : pureEval (Nomm.n7 p q) s = pureEval q v := by simp [pureEval, ev]
    rw [e7]
    have agQ : AgreeP lib O c gul st t ned g0 g1 nx.laz s0 v := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hm
          rcases hp.labs e' he' with h | ⟨a, _, _⟩
          · exact hnl h
          · omega
        rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 hp.bo) hn2, hp.keep o h1 hnl]
      · obtain ⟨x, y, th, hb⟩ := hq.labs e he
        obtain ⟨F, hF, hFS⟩ := Fp e he
        have hb2 := hF [] (Termin.hop th) hb
        rw [List.append_nil] at hb2
        rcases hFS with ⟨L', hm', fs⟩ | ⟨hnm, fs⟩
        · obtain ⟨A, th', h4, h9, sA⟩ := ag.2 _ hm'
          rw [hb2] at h4
          simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h4
          obtain ⟨rfl, rfl⟩ := h4
          refine ⟨A, th, hb, h9, ?_⟩
          have := fs lib σ O c gul st t ned A s0 s v hnedP ev sA
          rwa [List.append_nil] at this
        · refine ⟨F, th, hb, ?_, ?_⟩
          · rw [ag.1 e.1 x (by have := hp.bo; have := hq.hi; omega) hnm, hb2]
          · have := fs lib σ O c gul st t ned [] s0 s v hnedP ev fillSem_bunt_nil
            rwa [List.nil_append] at this
    by_cases f : FitsS nx.laz.sure v
    · obtain ⟨R, hR, kR, e⟩ := Sp'.1 f
      have hnR : HoldsN ned R s0 := HoldsN.agree ned (fun r hr => kR r (Or.inr hr)) hn
      have Sq' := Sq c ned σ O st t gul s0 v agQ hnedQ R ⟨hR, f.2⟩ hnR
      refine goalSem_pre (fun r hr => kR r ?_) e goal _ Sq'
      rcases hr with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by omega, notq r h1 h2⟩
      · exact Or.inr h
    · rcases hq.nec v f with e' | ⟨w, e'', x⟩
      · rw [e']; exact goalSem_none goal (Sp'.2 f)
      · rw [e'']; exact goalSem_gnot goal x (Sp'.2 f)

/-- **`[7 [1 k] q]` for `%done` with the relaxed `sem`**, `q` in `FragX`
with at most 255 `%6`: the relaxed counterpart of `runOKP_seven1`. -/
theorem semPR_seven1 (lib : Lib) {k : Noun} {q : Nomm} (hf : FragX (S := S) q) (hcount : sixCount q ≤ 255)
    {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0)
    (h : runL (Nomm.n7 (Nomm.n1 k) q) (CGoalL.done : CGoalL S) region g0 = some (nex, g2)) :
    SemPR (Map := Map) lib (Nomm.n7 (Nomm.n1 k) q) CGoal.done g0 g2 nex := by
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (runX_ok (Map := Map) lib hf).1 trivial trivial hcount b0 d0 hu h1
  have Sq := (runX_semR (Map := Map) lib hf).1 trivial trivial trivial hcount b0 d0 hu hcl h1
  have a1 : g1.drop = false := Rq.ext.2.2.1.trans d0
  have a2 : UpBelow g1 := Rq.grow.up hu
  have a3 : ∀ r, NMem nx.laz.sure.ned r → r < g1.re := fun r hr => (Rq.regs r hr).2
  have a4 : ∀ e ∈ entries nx.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → r < g1.re :=
    fun e he => ⟨(Rq.eregs e he).1, fun r hr => ((Rq.eregs e he).2 r hr).2⟩
  have a5 : ∀ e ∈ entries nx.laz, e.1 < g1.bo ∧ ∃ B fin, HoonMap.get g1.blocks e.1 = some ⟨[], B, fin⟩ :=
    fun e he => by
      obtain ⟨_, b, th, hb⟩ := Rq.labs e he
      exact ⟨by have := Rq.hi; omega, [], Termin.hop th, hb⟩
  have RE := runOKE_n1 lib h2 a1 a2 Rq.lo Rq.hi Rq.dist a3 a4 Rq.nodup a5
  obtain ⟨FE, SE⟩ := runOKE_n1R lib h2 a1 a2 Rq.lo Rq.hi Rq.dist a3 a4 Rq.nodup a5
  exact SemGR.toP (show NotNext (CGoal.done : CGoal S) from trivial)
    (semGR_sevenE Rq.toG (SemPR.toG Sq) RE FE SE)

end Comp
end SkaModel
end Formalization
