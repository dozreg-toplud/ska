import lemmas.Ska.CompGenClassH

/-!
# The plumbing of the general cons's sure part: `consSemPre_of`

README Gaps 12.39, item 12.  `ConsSemPre` of the cons taken apart
(`ConsGAt`), from the parts' frames, growth, no re-pointing and `ResG`:

* the copy's root block at `g3.bo` (its ops fill both parts' sure needs from
  the merged one, then the hop to `np.th`, a jump without arguments);
* the split's root block at `g0.bo` (kept by both parts, no label of
  theirs, and no copy op there): its ops build `L.sure` from the halves;
* the parts' `AgreeG` from the whole's: at a part's fresh label the whole's
  fill, then the copy's ops there (`ci2_fill_copy`; the other part has no
  entry at that label), and off the labels the blocks are the whole's.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section Fill
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

/-- **A fill, then the copy's ops at the label**: the fill of the merged
needs `Ms`, then ops that build `Fs ++ Ts` from them, is a fill of
`Fs ++ Ts` from any input need that gives the first one's. -/
theorem ci2_fill_copy {ned N' : Need} {lo1 lo' lo3 : Nat} {Ms Fs Ts : List (Sure S)} {A Pc : List Pole}
    {s0 x' s : Noun}
    (hA : FillSemL (Map := Map) lib O c gul st t ned lo1 Ms A s0 s)
    (hN : ∀ R : Map (Option Noun), HoldsN N' R x' → HoldsN ned R s0)
    (hk : ∀ x, (NMem N' x ∨ x < lo') → (NMem ned x ∨ x < lo1) ∧ ¬ (lo3 ≤ x ∧ x < lo1))
    (Cfit : (∀ M ∈ Ms, FitsS M s) ↔ (∀ F ∈ Fs, FitsS F s) ∧ (∀ T ∈ Ts, FitsS T s))
    (Creg : ∀ M ∈ Ms, ∀ y, NMem M.ned y → (∃ F ∈ Fs ++ Ts, NMem F.ned y) ∨ (lo3 ≤ y ∧ y < lo1))
    (Crun : ∀ R : Map (Option Noun), (∀ M ∈ Ms, HoldsN M.ned R s) →
      ∃ R', Runs lib O c gul st t Pc R R' ∧ (∀ F ∈ Fs ++ Ts, HoldsN F.ned R' s) ∧
        ∀ y, (∀ F ∈ Fs ++ Ts, ¬ NMem F.ned y) → SkaModel.read y R' = SkaModel.read y R) :
    FillSemL lib O c gul st t N' lo' (Fs ++ Ts) (A ++ Pc) x' s := by
  intro R hR
  have hR0 := hN R hR
  have fitAll : (∀ L ∈ Fs ++ Ts, FitsS L s) → ∀ M ∈ Ms, FitsS M s := fun h => Cfit.mpr
    ⟨fun F hF => h F (List.mem_append_left _ hF), fun T hT => h T (List.mem_append_right _ hT)⟩
  refine ⟨fun hf => ?_, fun ⟨L, hL, nf⟩ => ?_⟩
  · obtain ⟨R1, r1, h1, k1⟩ := (hA R hR0).1 (fitAll hf)
    obtain ⟨R2, r2, h2, k2⟩ := Crun R1 (fun M hM => (h1 M hM).1)
    refine ⟨R2, r1.append r2, fun F hF => ⟨h2 F hF, (hf F hF).2⟩, fun x hx hnx => ?_⟩
    obtain ⟨hx1, hx2⟩ := hk x hx
    rw [k2 x hnx]
    refine k1 x hx1 (fun M hM hm => ?_)
    rcases Creg M hM x hm with ⟨F, hF, hFm⟩ | h
    · exact hnx F hF hFm
    · exact hx2 h
  · by_cases fm : ∀ M ∈ Ms, FitsS M s
    · exfalso
      obtain ⟨f1, f2⟩ := Cfit.mp fm
      rcases List.mem_append.mp hL with h | h
      · exact nf (f1 L h)
      · exact nf (f2 L h)
    · have : ∃ M ∈ Ms, ¬ FitsS M s := Classical.byContradiction fun ne =>
        fm fun M hM => Classical.byContradiction fun nf' => ne ⟨M, hM, nf'⟩
      exact Crashes.append_left ((hA R hR0).2 this)

/-- The empty fill of no need. -/
theorem ci2_fill_nil {ned : Need} {lo : Nat} {s0 s : Noun} :
    FillSemL (Map := Map) lib O c gul st t ned lo ([] : List (Sure S)) [] s0 s :=
  fun R _ => ⟨fun _ => ⟨R, Runs.nil R, fun _ h => by simp at h, fun _ _ _ => rfl⟩,
    fun ⟨_, h, _⟩ => by simp at h⟩

end Fill

theorem ci2_atL_eq (l : Lazy S) (o : Nat) : suresAt l o = atL (entries l) o := rfl

/-- **`ConsSemPre` of the general cons** from the parts' class facts. -/
theorem consSemPre_of (lib : Lib) : ConsSemPreOf S Map lib := by
  intro L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np Qq Qp CA G Fq Gq Nq Rq Fp Gp Np Rp
  have Pq := premG_tel CA G
  have Pp := premG_hed CA G Fq Gq
  have d3 : g3.drop = false := Fp.drop.trans (Fq.drop.trans CA.dS)
  have CO := CA.copyOK d3 Rp.lu Rq.lu
  have HA := halvesApart_split CA G
  have CP : CopyPreAt (Map := Map) (g3.emitted ⟨[], [], Termin.hop np.th⟩) ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) :=
    cc_copyPreAt_re (emitted_re _ _).symm (copyPreG Fq Fp Pq Pp Rq Rp HA)
  obtain ⟨PC, PPC, OC, AC⟩ := CopyOKL.runAt CO
  have bo1 : g1.bo = g3.bo + 1 := PPC.bo
  have re1 : g3.re ≤ g1.re := PPC.re
  have cd1 : g1.cond = g3.cond := PPC.cond
  have boS := CA.boS
  have bq := Fq.bo
  have bp := Fp.bo
  have r0 := CA.reS
  have r1 := Fq.re
  have r2 := Fp.re
  have b0 := G.bo
  have CB3 : CondBelow g3 := Fp.cfr.below (Fq.cfr.below (CA.condBelowS G))
  -- `cond` below the split's end is the goal's
  have c01 : ∀ x, x < gS.re → HoonMap.get g1.cond x = HoonMap.get g0.cond x := fun x hx => by
    rw [cd1]
    rcases Fp.cfr.2 x with e3 | h3
    · rw [e3]
      rcases Fq.cfr.2 x with e2 | h2
      · rw [e2, CA.condS]
      · omega
    · omega
  -- the labels
  have ltLm : ∀ o ∈ (entries L).map Prod.fst, o < g0.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact (G.goal.lab e he).2.1
  have lp : ∀ e ∈ entries np.laz, e.1 < g0.bo ∨ (g2.bo ≤ e.1 ∧ e.1 < g3.bo) := fun e he => by
    rcases (Fp.labs e he).1 with h | h
    · obtain ⟨e1, he1, h1⟩ := List.mem_map.mp h
      exact Or.inl (by rw [← h1]; exact ltLm _ (CA.labH e1 he1))
    · exact Or.inr h
  have lq : ∀ e ∈ entries nq.laz, e.1 < g0.bo ∨ (gS.bo ≤ e.1 ∧ e.1 < g2.bo) := fun e he => by
    rcases (Fq.labs e he).1 with h | h
    · obtain ⟨e1, he1, h1⟩ := List.mem_map.mp h
      exact Or.inl (by rw [← h1]; exact ltLm _ (CA.labT e1 he1))
    · exact Or.inr h
  have lpm : ∀ o ∈ (entries np.laz).map Prod.fst, o < g0.bo ∨ (g2.bo ≤ o ∧ o < g3.bo) := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact lp e he
  have lqm : ∀ o ∈ (entries nq.laz).map Prod.fst, o < g0.bo ∨ (gS.bo ≤ o ∧ o < g2.bo) := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact lq e he
  have lhm : ∀ o ∈ (entries hed).map Prod.fst, o < g0.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact ltLm _ (CA.labH e he)
  have ltm : ∀ o ∈ (entries tel).map Prod.fst, o < g0.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact ltLm _ (CA.labT e he)
  obtain ⟨-, QN⟩ := Raw.lab_copyL
    (Q := fun o => o ∈ (entries np.laz).map Prod.fst ∨ o ∈ (entries nq.laz).map Prod.fst) CA.cp Rp.lu Rq.lu
    (fun e he => Or.inl (List.mem_map_of_mem he)) (fun e he => Or.inr (List.mem_map_of_mem he))
  have lnex : ∀ o ∈ (entries nex.laz).map Prod.fst,
      o ∈ (entries np.laz).map Prod.fst ∨ o ∈ (entries nq.laz).map Prod.fst := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact QN e he
  have nexAt : ∀ o, o ∉ (entries np.laz).map Prod.fst → o ∉ (entries nq.laz).map Prod.fst →
      o ∉ (entries nex.laz).map Prod.fst := fun o h1 h2 h => (lnex o h).elim h1 h2
  have pcz : ∀ o, o ≠ g3.bo → o ∉ (entries np.laz).map Prod.fst → o ∉ (entries nq.laz).map Prod.fst →
      PC o = [] := fun o h0 h1 h2 => OC o (fun hm => by
    rw [List.map_append, List.mem_append, List.map_cons, List.mem_cons, List.map_cons, List.mem_cons] at hm
    rcases hm with (h | h) | (h | h)
    · exact h0 h
    · exact h1 h
    · exact h0 h
    · exact h2 h)
  -- the registers of the copy's ops
  have goodC : ∀ k x, ((∃ F ∈ atL ((g3.bo, np.laz) :: entries np.laz) k ++ atL ((g3.bo, nq.laz) :: entries nq.laz) k,
      NMem F.ned x) ∨ (g3.re ≤ x ∧ x < g1.re)) → x < g1.re ∧ HoonMap.get g1.cond x = Option.none := by
    intro k x hx
    rw [cd1]
    rcases hx with ⟨F, hF, hm⟩ | ⟨h1, h2⟩
    · rcases List.mem_append.mp hF with hF | hF
      · obtain ⟨e, he, -, rfl⟩ := mem_atL hF
        rcases List.mem_cons.mp he with rfl | he
        · obtain ⟨o, cn⟩ := cd_np_sure CA G Fq Fp hm
          refine ⟨?_, cn⟩
          rcases o with o | o
          · have := G.goal.sregs x o; omega
          · omega
        · obtain ⟨o, cn⟩ := cd_np_ent CA G Fq Fp he hm
          refine ⟨?_, cn⟩
          rcases o with ⟨e0, he0, o⟩ | o | o
          · have := (G.goal.eregs e0 he0).2 x o; omega
          · have := G.goal.sregs x o; omega
          · omega
      · obtain ⟨e, he, -, rfl⟩ := mem_atL hF
        rcases List.mem_cons.mp he with rfl | he
        · obtain ⟨o, cn⟩ := cd_nq_sure CA G Fq Fp hm
          refine ⟨?_, cn⟩
          rcases o with o | o
          · have := G.goal.sregs x o; omega
          · omega
        · obtain ⟨o, cn⟩ := cd_nq_ent CA G Fq Fp he hm
          refine ⟨?_, cn⟩
          rcases o with ⟨e0, he0, o⟩ | o | o
          · have := (G.goal.eregs e0 he0).2 x o; omega
          · have := G.goal.sregs x o; omega
          · omega
    · exact ⟨h2, condBelow_none CB3 h1⟩
  have regsPC : ∀ k, RegsIn (fun x => x < g1.re ∧ HoonMap.get g1.cond x = Option.none) (PC k) := fun k =>
    RegsIn.mono (fun x hx => goodC k x hx) (AC k (CP k).1 (CP k).2).2.2.2.1
  have fixO : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ A : List Pole, RegsIn (fun x => x < g1.re ∧ HoonMap.get g1.cond x = Option.none) A →
      A.map (renPole (unproxy cf)) = A := fun cf hcf A hA =>
    renOps_fix (P := fun x => x < g1.re ∧ HoonMap.get g1.cond x = Option.none)
      (fun x hx => unproxy_none (by rw [hcf x hx.1]; exact hx.2)) hA
  -- the copy's root
  have lt3p : ∀ o ∈ (entries np.laz).map Prod.fst, o < g3.bo := fun o ho => by
    rcases lpm o ho with h | h <;> omega
  have lt3q : ∀ o ∈ (entries nq.laz).map Prod.fst, o < g3.bo := fun o ho => by
    rcases lqm o ho with h | h <;> omega
  have n3p : g3.bo ∉ (entries np.laz).map Prod.fst := fun h => by have := lt3p _ h; omega
  have n3q : g3.bo ∉ (entries nq.laz).map Prod.fst := fun h => by have := lt3q _ h; omega
  have n3x : g3.bo ∉ (entries nex.laz).map Prod.fst := nexAt _ n3p n3q
  have aM : atL ((g3.bo, nex.laz) :: entries nex.laz) g3.bo = [nex.laz.sure] := by
    rw [ci_atL_self, cj_atL_nil n3x]
  have aF : atL ((g3.bo, np.laz) :: entries np.laz) g3.bo = [np.laz.sure] := by
    rw [ci_atL_self, cj_atL_nil n3p]
  have aT : atL ((g3.bo, nq.laz) :: entries nq.laz) g3.bo = [nq.laz.sure] := by
    rw [ci_atL_self, cj_atL_nil n3q]
  have C0 := AC g3.bo (CP g3.bo).1 (CP g3.bo).2
  rw [aF, aT, aM] at C0
  obtain ⟨Cfit0, -, -, -, Crun0⟩ := C0
  have npta : np.th.args = [] := by
    rcases Fp.ent with ⟨_, _, _, a⟩ | e
    · exact a
    · simp only [GoalJ] at e; rw [e]; exact Pp.ta
  have b13 : HoonMap.get g1.blocks g3.bo = some ⟨[], PC g3.bo ++ [], Termin.hop np.th⟩ := by
    rw [PPC.get, emitted_get g3 _ d3]; rfl
  -- the split's root
  obtain ⟨hdj, hreg0⟩ := ci_es G.goal
  obtain ⟨PS, PPS, -, SA⟩ := SplitOKL.runAt CA.sp.toL hdj hreg0
  have n0h : g0.bo ∉ (entries hed).map Prod.fst := fun h => by have := lhm _ h; omega
  have n0t : g0.bo ∉ (entries tel).map Prod.fst := fun h => by have := ltm _ h; omega
  have n0L : g0.bo ∉ (entries L).map Prod.fst := fun h => by have := ltLm _ h; omega
  have n0p : g0.bo ∉ (entries np.laz).map Prod.fst := fun h => by rcases lpm _ h with h | h <;> omega
  have n0q : g0.bo ∉ (entries nq.laz).map Prod.fst := fun h => by rcases lqm _ h with h | h <;> omega
  have n0x : g0.bo ∉ (entries nex.laz).map Prod.fst := nexAt _ n0p n0q
  have aE : atL ((g0.bo, L) :: entries L) g0.bo = [L.sure] := by rw [ci_atL_self, cj_atL_nil n0L]
  have aH : atL ((g0.bo, hed) :: entries hed) g0.bo = [hed.sure] := by rw [ci_atL_self, cj_atL_nil n0h]
  have aTs : atL ((g0.bo, tel) :: entries tel) g0.bo = [tel.sure] := by rw [ci_atL_self, cj_atL_nil n0t]
  have S0 := SA g0.bo
  rw [aE, aH, aTs] at S0
  obtain ⟨Sfit, -, -, Srun⟩ := S0
  have P00 := CA.sp
  obtain ⟨P0, PP0, -, A0⟩ := P00
  have eP : PS g0.bo = P0 g0.bo := ch_pref_uniq PPS PP0 CA.eo
  have regsS : RegsIn (fun x => x < g1.re ∧ HoonMap.get g1.cond x = Option.none) (PS g0.bo) := by
    rw [eP]
    obtain ⟨ps, eps, pE, -, -, sP, -⟩ := A0 g0.bo
    rw [eps]
    refine ch_regsIn_flatten _ ps (fun pp hp => ?_)
    have hp1 : pp.1 ∈ atL ((g0.bo, L) :: entries L) g0.bo := pE.mem_iff.mp (List.mem_map_of_mem hp)
    rw [aE, List.mem_singleton] at hp1
    have ra := (sP pp hp).ra (fun x => HoonMap.get g0.cond x = Option.none)
      (fun r hr => by rw [hp1] at hr; exact G.nc r hr) (fun r hr => condBelow_none G.cb hr)
    have rb := (sP pp hp).rb (fun r hr => by rw [hp1] at hr; exact G.goal.sregs r hr)
    intro qq hq x hx
    have hx' : x < gS.re := rb qq hq x hx
    exact ⟨by omega, by rw [c01 x hx']; exact ra qq hq x hx⟩
  have pc0 : PC g0.bo = [] := pcz g0.bo (by omega) n0p n0q
  have b10 : HoonMap.get g1.blocks g0.bo = some ⟨[], PS g0.bo ++ [], Termin.hop th⟩ := by
    rw [PPC.get, ci_emitted_ne _ _ (by omega : g0.bo ≠ g3.bo), Fp.keep g0.bo (by omega) n0h,
      Fq.keep g0.bo (by omega) n0t, PPS.get, CA.eo, pc0]
    simp [preBody]
  -- the parts' fresh labels: the block in `g1` is the copy's ops then the part's
  have offQ : ∀ o, o < g2.bo → o ∉ (entries hed).map Prod.fst → o ≠ g3.bo →
      o ∉ (entries np.laz).map Prod.fst → o ∉ (entries nq.laz).map Prod.fst →
      HoonMap.get g1.blocks o = HoonMap.get g2.blocks o := fun o h1 h2 h3 h4 h5 => by
    rw [PPC.get, ci_emitted_ne _ _ h3, pcz o h3 h4 h5, Fp.keep o h1 h2]
    cases HoonMap.get g2.blocks o <;> simp [preBody]
  have offP : ∀ o, o ≠ g3.bo → o ∉ (entries np.laz).map Prod.fst → o ∉ (entries nq.laz).map Prod.fst →
      HoonMap.get g1.blocks o = HoonMap.get g3.blocks o := fun o h3 h4 h5 => by
    rw [PPC.get, ci_emitted_ne _ _ h3, pcz o h3 h4 h5]
    cases HoonMap.get g3.blocks o <;> simp [preBody]
  refine
    { copy := ?_, split := ?_, sfit := ?_, cfit := ?_, agP := ?_, agQ := ?_, re0 := r0,
      c3 := fun k _ => by rw [cd1], c2 := fun k hk => ?_, reS := r1, re2 := r2, re3 := re1,
      qk := fun x hx => ?_, hk := fun x hx => ⟨HA.hlo.1 x hx, fun m => HA.ss x hx m⟩,
      tlo := fun x hx => HA.tlo.1 x hx, llo := fun x hx => by have := G.goal.sregs x hx; omega,
      lt1 := fun x hx => ?_, orig := fun x hx0 hx => ?_ }
  · -- the copy's root block
    intro cf hcf c hc σ O gul st t regs s hh
    have blk : HoonMap.get c.blocks g3.bo = some ⟨[], PC g3.bo, Termin.hop np.th⟩ := by
      rw [hc g3.bo (by omega) (by omega) n3x, b13]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, fixO cf hcf _ (regsPC _),
        renFin, renJmp_nil _ npta]
    obtain ⟨R', r, hF, k⟩ := Crun0 lib σ O c gul st t regs s
      (fun M hM => by rw [List.mem_singleton.mp hM]; exact hh.1)
    obtain ⟨f1, f2⟩ := (Cfit0 s).mp (fun M hM => by rw [List.mem_singleton.mp hM]; exact fitsS_of_holdsS hh)
    refine ⟨R', ?_, ⟨hF _ (by simp), (f1 _ (by simp)).2⟩, ⟨hF _ (by simp), (f2 _ (by simp)).2⟩,
      fun y h1 h2 => k y (fun F hF => ?_)⟩
    · have e1 := r [] (Termin.hop np.th)
      simp only [List.append_nil] at e1
      rw [CA.eth, goJ_jmp0 regs t g3.bo _ blk, e1, execBlob_hop]
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl
      · exact h1
      · exact h2
  · -- the split's root block
    intro cf hcf c hc
    refine ⟨PS g0.bo, ?_, fun σ O gul st' t R x y hx hy => ?_⟩
    · rw [hc g0.bo (Nat.le_refl _) (by omega) n0x, b10]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, fixO cf hcf _ regsS,
        renFin, renJmp_nil _ G.ta]
    · obtain ⟨R', r, hL, k⟩ := Srun lib σ O c gul st' t R x y
        (fun H hH => by rw [List.mem_singleton.mp hH]; exact hx) (fun T hT => by rw [List.mem_singleton.mp hT]; exact hy)
      exact ⟨R', r, hL _ (List.mem_singleton_self _),
        fun z hz => k z (fun L' hL' => by rw [List.mem_singleton.mp hL']; exact hz)⟩
  · intro x y
    have := Sfit x y
    simp only [List.mem_singleton, forall_eq] at this
    exact this
  · intro z
    have := Cfit0 z
    simp only [List.mem_singleton, forall_eq] at this
    exact this
  · -- `p`'s agreement
    intro cf hcf c ned σ O gul s0 s hned ag st' t'
    obtain ⟨ag1, ag2⟩ := ag st' t'
    refine ⟨fun o h1 h2 h3 => ?_, fun o ho h1 => ?_⟩
    · have hq : o ∉ (entries nq.laz).map Prod.fst := fun h => by rcases lqm o h with h | h <;> omega
      rw [ag1 o (by omega) (by omega) (nexAt o h3 hq), offP o (by omega) h3 hq]
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      have le3 : e.1 < g3.bo := by rcases lp e he with h | h <;> omega
      have hq : e.1 ∉ (entries nq.laz).map Prod.fst := fun h => by rcases lqm _ h with h | h <;> omega
      have ne3 : g3.bo ≠ e.1 := by omega
      obtain ⟨-, B3, j3, blk3⟩ := Fp.labs e he
      have hb1 : HoonMap.get g1.blocks e.1 = some ⟨[], PC e.1 ++ B3, Termin.hop j3⟩ := by
        rw [PPC.get, ci_emitted_ne _ _ (Ne.symm ne3), blk3]; rfl
      have fixPC := fixO cf hcf _ (regsPC e.1)
      have C1 := AC e.1 (CP e.1).1 (CP e.1).2
      rw [ci_atL_ne np.laz _ ne3, ci_atL_ne nq.laz _ ne3, ci_atL_ne nex.laz _ ne3, cj_atL_nil hq] at C1
      obtain ⟨Cfit, Creg, -, -, Crun⟩ := C1
      have hk : ∀ x, (NMem ned x ∨ x < g3.re) → (NMem ned x ∨ x < g1.re) ∧ ¬ (g3.re ≤ x ∧ x < g1.re) :=
        fun x hx => by
          rcases hx with h | h
          · have := hned x h; exact ⟨Or.inl h, by omega⟩
          · exact ⟨Or.inr (by omega), by omega⟩
      by_cases hm : e.1 ∈ (entries nex.laz).map Prod.fst
      · obtain ⟨A, B, th1, hg1, hcb, hfill⟩ := ag2 e.1 hm (by omega)
        rw [hb1] at hg1
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg1
        obtain ⟨rfl, rfl⟩ := hg1
        refine ⟨A ++ PC e.1, B3, j3, blk3, ?_, ?_⟩
        · rw [hcb, List.map_append, fixPC, List.append_assoc]
        · have := ci2_fill_copy (lo3 := g3.re) (Ts := []) (Pc := PC e.1) hfill (fun R h => h) hk (Cfit s)
            (fun M hM => (Creg M hM).2) (fun R hR => Crun lib σ O c gul st' t' R s hR)
          rw [List.append_nil] at this
          exact this
      · refine ⟨PC e.1, B3, j3, blk3, ?_, ?_⟩
        · rw [ag1 e.1 (by omega) (by omega) hm, hb1]
          simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_append, fixPC, renFin]
        · have h0 : FillSemL (Map := Map) lib O c gul st' t' ned g1.re (atL (entries nex.laz) e.1) [] s0 s := by
            rw [cj_atL_nil hm]; exact ci2_fill_nil
          have := ci2_fill_copy (lo3 := g3.re) (Ts := []) (Pc := PC e.1) h0 (fun R h => h) hk (Cfit s)
            (fun M hM => (Creg M hM).2) (fun R hR => Crun lib σ O c gul st' t' R s hR)
          rw [List.append_nil, List.nil_append] at this
          exact this
  · -- `q`'s agreement
    intro cf hcf c ned σ O gul s0 s dp wp hned hdp ag st' t'
    obtain ⟨ag1, ag2⟩ := ag st' t'
    refine ⟨fun o h1 h2 h3 => ?_, fun o ho h1 => ?_⟩
    · have hp : o ∉ (entries np.laz).map Prod.fst := fun h => by rcases lpm o h with h | h <;> omega
      have hh : o ∉ (entries hed).map Prod.fst := fun h => by have := lhm o h; omega
      rw [ag1 o (by omega) (by omega) (nexAt o hp h3), offQ o h2 hh (by omega) hp h3]
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      have le2 : e.1 < g2.bo := by rcases lq e he with h | h <;> omega
      have hp : e.1 ∉ (entries np.laz).map Prod.fst := fun h => by rcases lpm _ h with h | h <;> omega
      have hh : e.1 ∉ (entries hed).map Prod.fst := fun h => by have := lhm _ h; omega
      have ne3 : g3.bo ≠ e.1 := by omega
      obtain ⟨-, B2, j2, blk2⟩ := Fq.labs e he
      have hb1 : HoonMap.get g1.blocks e.1 = some ⟨[], PC e.1 ++ B2, Termin.hop j2⟩ := by
        rw [PPC.get, ci_emitted_ne _ _ (Ne.symm ne3), Fp.keep e.1 le2 hh, blk2]; rfl
      have fixPC := fixO cf hcf _ (regsPC e.1)
      have C1 := AC e.1 (CP e.1).1 (CP e.1).2
      rw [ci_atL_ne np.laz _ ne3, ci_atL_ne nq.laz _ ne3, ci_atL_ne nex.laz _ ne3, cj_atL_nil hp] at C1
      obtain ⟨Cfit, Creg, -, -, Crun⟩ := C1
      have hk : ∀ x, (NMem (Need.pair ned dp) x ∨ x < g2.re) →
          (NMem ned x ∨ x < g1.re) ∧ ¬ (g3.re ≤ x ∧ x < g1.re) := fun x hx => by
        rcases hx with (h | h) | h
        · have := hned x h; exact ⟨Or.inl h, by omega⟩
        · have := hdp x h; exact ⟨Or.inr (by omega), by omega⟩
        · exact ⟨Or.inr (by omega), by omega⟩
      have hN : ∀ R : Map (Option Noun), HoldsN (Need.pair ned dp) R (C s0 wp) → HoldsN ned R s0 :=
        fun R h => h.1
      by_cases hm : e.1 ∈ (entries nex.laz).map Prod.fst
      · obtain ⟨A, B, th1, hg1, hcb, hfill⟩ := ag2 e.1 hm (by omega)
        rw [hb1] at hg1
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg1
        obtain ⟨rfl, rfl⟩ := hg1
        refine ⟨A ++ PC e.1, B2, j2, blk2, ?_, ?_⟩
        · rw [hcb, List.map_append, fixPC, List.append_assoc]
        · have := ci2_fill_copy (lo3 := g3.re) (Fs := []) (Pc := PC e.1) hfill hN hk (Cfit s)
            (fun M hM => (Creg M hM).2) (fun R hR => Crun lib σ O c gul st' t' R s hR)
          rw [List.nil_append] at this
          exact this
      · refine ⟨PC e.1, B2, j2, blk2, ?_, ?_⟩
        · rw [ag1 e.1 (by omega) (by omega) hm, hb1]
          simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_append, fixPC, renFin]
        · have h0 : FillSemL (Map := Map) lib O c gul st' t' ned g1.re (atL (entries nex.laz) e.1) [] s0 s := by
            rw [cj_atL_nil hm]; exact ci2_fill_nil
          have := ci2_fill_copy (lo3 := g3.re) (Fs := []) (Pc := PC e.1) h0 hN hk (Cfit s)
            (fun M hM => (Creg M hM).2) (fun R hR => Crun lib σ O c gul st' t' R s hR)
          rw [List.nil_append, List.nil_append] at this
          exact this
  · rw [cd1]
    rcases Fp.cfr.2 k with e | h
    · exact e
    · omega
  · rcases Fq.regs x hx with h | h
    · exact ⟨by have := HA.tlo.1 x h; omega, fun m => HA.ss x m h⟩
    · exact ⟨h.2, fun m => by have := HA.hlo.1 x m; omega⟩
  · rcases hx with h | h | h | h
    · rcases (cd_np_sure CA G Fq Fp h).1 with h' | h'
      · have := G.goal.sregs x h'; omega
      · omega
    · rcases (cd_nq_sure CA G Fq Fp h).1 with h' | h'
      · have := G.goal.sregs x h'; omega
      · omega
    · have := HA.hlo.1 x h; omega
    · have := HA.tlo.1 x h; omega
  · rcases hx with h | h | h | h
    · rcases (cd_np_sure CA G Fq Fp h).1 with h' | h'
      · exact h'
      · omega
    · rcases (cd_nq_sure CA G Fq Fp h).1 with h' | h'
      · exact h'
      · omega
    · rcases (CA.halfH G).sr x h with h' | h'
      · exact h'
      · omega
    · rcases (CA.halfT G).sr x h with h' | h'
      · exact h'
      · omega

end Comp
end SkaModel
end Formalization
