import lemmas.Ska.CompNest

/-!
# Nested `[6 c a b]` under `%done`: what the code does

`RunOKD nm g0 g1 nex`: the relation for one run of `runL` for `%done` on
`FragD`.  The lazy need `nex.laz` may have forks at any depth.  The state
grew, every lazy block of the need (`entries`) was allocated in the run,
is the block `⟨[], [], hop th⟩` and lies below the block `nex` enters,
their labels are distinct, and the registers of every need in the tree
were allocated in the run.  `sem`: in a program that holds the blocks of
`g1` outside the lazy blocks and, at each lazy block, ops in front that
fill the need taken there from the input registers `ned` (`AgreeF`),
entering `nex` with the sure part held and the input registers holding the
subject does what `+mink` does.  `nec`: only the sure part is checked at
the entry; the needs in the forks are checked in their lazy blocks, that
is only on the branch taken.

`runD_ok`: `runL` meets `RunOKD` on `FragD` when the nomm has at most 255
`%6`, so that `+lazy-shut` does not fire.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The program holds the run's blocks, with filling ops in front of the
lazy blocks of `laz`.** -/
def AgreeF (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = HoonMap.get g1.blocks o) ∧
  ∀ e ∈ entries laz, ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧ FillSem lib O c gul st t ned 0 e.2.sure A s

/-- **The relation for one run of `runL` for `%done`.** -/
structure RunOKD (lib : Lib) (nm : Nomm) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : Grow g0 g1
  cnd : g1.cond = g0.cond
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : ∃ B fin, HoonMap.get g1.blocks nex.th.there = some ⟨[], B, fin⟩
  regs : ∀ r, NMem nex.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
    AgreeF lib O c gul st t ned g0 g1 nex.laz s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
    goJ lib O c gul st regs t nex.th = some (toneOf t (pureEval nm s), st)

/-! ## Helpers -/

theorem ext_tagged (g : Gen Map) (o : Nat) (region : List Nat) : Ext g (g.tagged o region) := by
  unfold Gen.tagged; split
  · exact Ext.refl g
  · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ => rfl⟩

theorem ext_sixGenL (g2 : Gen Map) th0 th1 region : Ext g2 (sixGenL g2 th0 th1 region) :=
  ((ext_emit _ _).trans (ext_emit _ _)).trans ((ext_tagged _ _ _).trans (ext_tagged _ _ _))

theorem grow_sixGenL {g2 : Gen Map} {th0 th1 : Jmp} (region : List Nat) (h0 : JumpsBelow (Termin.hop th0) g2.bo)
    (h1 : JumpsBelow (Termin.hop th1) (g2.bo + 1)) : Grow g2 (sixGenL g2 th0 th1 region) :=
  ((grow_emit h0).trans (grow_emit (by simpa [emitted_bo] using h1))).trans
    ((grow_tagged _ _ _).trans (grow_tagged _ _ _))

theorem sixGenL_get_y {g2 : Gen Map} (th0 th1 : Jmp) (region : List Nat) (hd : g2.drop = false) :
    HoonMap.get (sixGenL g2 th0 th1 region).blocks g2.bo = some ⟨[], [], Termin.hop th0⟩ := by
  simp only [sixGenL, tagged_blocks]
  rw [get_emitted_ne (by simp [emitted_bo])]; exact emitted_get g2 _ hd

theorem sixGenL_get_n {g2 : Gen Map} (th0 th1 : Jmp) (region : List Nat) (hd : g2.drop = false) :
    HoonMap.get (sixGenL g2 th0 th1 region).blocks (g2.bo + 1) = some ⟨[], [], Termin.hop th1⟩ := by
  simp only [sixGenL, tagged_blocks]
  exact emitted_get (g2.emitted _) _ (by simp [emitted_drop, hd])

theorem ext_addOps_nil {o : Nat} {g g' : Gen Map} {u : Unit} (h : addOps o [] g = some (u, g')) : Ext g g' := by
  obtain ⟨A, r, b, d⟩ := addOps_nil h
  exact ⟨Nat.le_of_eq r.symm, Nat.le_of_eq b.symm, d, fun k _ => A k⟩

theorem entries_six (s : Sure S) (y n : Nat) (l0 l1 : Lazy S) :
    entries (mk s [((y, l0), (n, l1))] []) = (y, l0) :: entries l0 ++ ((n, l1) :: entries l1) := by
  simp [entries, bondEntries, forkEntries]

theorem fillSem_run {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {L : Sure S} {A : List Pole} {s : Noun} (F : FillSem lib O c gul st t ned 0 L A s)
    {R : Map Noun} (hR : HoldsN ned R s) (dj : ∀ x, NMem ned x → ¬ NMem L.ned x) (th : Jmp) :
    (FitsS L s → ∃ R', HoldsS L R' s ∧ HoldsN ned R' s ∧
      execBlob lib O c gul st R t ⟨[], A, Termin.hop th⟩ [] = goJ lib O c gul st R' t th) ∧
    (¬ FitsS L s → execBlob lib O c gul st R t ⟨[], A, Termin.hop th⟩ [] = some (Tone.two t, st)) := by
  refine ⟨fun f => ?_, fun f => ?_⟩
  · obtain ⟨R', hr, hh, k⟩ := (F R hR).1 f
    refine ⟨R', hh, HoldsN.agree ned (fun x hx => k x (Or.inl hx) (dj x hx)) hR, ?_⟩
    have := hr [] (Termin.hop th)
    rw [List.append_nil] at this
    rw [this, execBlob_hop]
  · have := (F R hR).2 f [] (Termin.hop th)
    rwa [List.append_nil] at this

/-! ## The fragment without `%6` -/

theorem runOKD_frag (lib : Lib) {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S)) {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (h : runL nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1)) : RunOKD lib nm g0 g1 nex := by
  rw [show (CGoalL.done : CGoalL S) = CGoal.toL CGoal.done from rfl, runL_frag hf] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have R := run_ok lib nm CGoal.done g0 g n hf trivial trivial hr
  have D := run_down (S := S) (Map := Map) nm CGoal.done g0 g n trivial b0 d0 hr
  have en : entries (Next.toL n).laz = [] := entries_ofSure _
  refine ⟨R.ext, D.grow, (kc_run nm CGoal.done).keep g0 n g hr, D.lo, D.hi, ?_, fun r hr => ?_, R.dist, by simp [Next.toL, entries_ofSure], by simp [Next.toL, entries_ofSure], by simp [Next.toL, entries_ofSure],
    by simp [Next.toL, entries_ofSure], fun s hs => ?_, ?_⟩
  · rcases D.entry with ⟨b, hb, hp⟩ | e
    · exact ⟨b.body, b.fin, by rw [show (Next.toL n).th = n.th from rfl, hb, ← hp]⟩
    · exact e.elim
  · rcases R.regs r hr with e | e
    · exact e.elim
    · exact e
  · rcases R.nec s hs with e | ⟨_, _, e⟩
    · exact e
    · exact e.elim
  · intro c ned σ O st t gul s ag _ regs hh _
    exact R.sem d0 c (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure])) σ O st s regs t gul hh

/-! ## The case `%6` -/

theorem pureEval_n6 (c a b : Nomm) (s : Noun) : pureEval (Nomm.n6 c a b) s = (pureEval c s).bind fun v =>
    match v with
    | Noun.atom 0 => pureEval a s
    | Noun.atom 1 => pureEval b s
    | _ => none := rfl

theorem mem_labels_six (s : Sure S) (y n : Nat) (l0 l1 : Lazy S) (o : Nat) :
    o ∈ (entries (mk s [((y, l0), (n, l1))] [])).map Prod.fst ↔
      o = y ∨ o ∈ (entries l0).map Prod.fst ∨ o = n ∨ o ∈ (entries l1).map Prod.fst := by
  rw [entries_six]
  simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem labels_bound {es : List (Nat × Lazy S)} {P : Nat → Prop} (h : ∀ e ∈ es, P e.1) :
    ∀ o ∈ es.map Prod.fst, P o := by
  intro o ho
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
  exact h e he

/-- **`runL` meets `RunOKD` on `FragD`** when the nomm has at most 255 `%6`. -/
theorem runD_ok (lib : Lib) {nm : Nomm} (hf : FragD (S := S) nm) : ∀ {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S}, sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false →
    runL nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) → RunOKD (Map := Map) lib nm g0 g1 nex := by
  induction hf with
  | frag hf => intro region g0 g1 nex _ b0 d0 h; exact runOKD_frag lib hf b0 d0 h
  | @six c a b hc _ _ iha ihb =>
    intro region g0 g4 nex hcount b0 d0 h
    obtain ⟨x1, x0, nc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := runL_six_doneL hc h
    have c6 : sixCount c = 0 := sixCount_frag (hc (jmp0 0) (jmp0 0))
    simp only [sixCount] at hcount
    have Rb := ihb (by omega) b0 d0 h1
    have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
    have b1 : 1 ≤ g1.bo := Nat.le_trans b0 Rb.ext.2.1
    have Ra := iha (by omega) b1 d1 h2
    have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
    have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
    have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
    have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
      apply lazyBig_entries
      rw [entries_six]; simp only [List.length_append, List.length_cons]
      have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
    obtain ⟨hadd, rfl⟩ := hrest hbig
    -- the test
    have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
    have Rc := run_ok lib c _ _ g3 nc (hc _ _) trivial trivial h3
    have Dc := run_down (S := S) (Map := Map) c (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) _ g3 nc
      ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
        by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩ (by simp only [sixGenL_bo]; omega) dG h3
    have d3 : g3.drop = false := Dc.grow.drop.trans dG
    have bG3 : g2.bo + 2 ≤ g3.bo := by have := Dc.grow.bo; simpa using this
    obtain ⟨A4, r4, bo4, _⟩ := addOps_nil hadd
    simp only [emitted_re, emitted_bo] at r4 bo4
    -- the states
    have E2 : Ext g2 (sixGenL g2 x0.th x1.th region) := ext_sixGenL _ _ _ _
    have E4 : Ext g3 g4 := (ext_emit g3 _).trans (ext_addOps_nil hadd)
    have E24 : Ext g2 g4 := E2.trans (Rc.ext.trans E4)
    have E14 : Ext g1 g4 := Ra.ext.trans E24
    have E04 : Ext g0 g4 := Rb.ext.trans E14
    have re01 := Rb.ext.1
    have re12 := Ra.ext.1
    have re24 := E24.1
    have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k hk =>
      (A4 k).trans (get_emitted_ne hk)
    have h4o : HoonMap.get g4.blocks g3.bo = some ⟨[], [], Termin.hop nc.th⟩ :=
      (A4 g3.bo).trans (emitted_get g3 _ d3)
    have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k =
        HoonMap.get (sixGenL g2 x0.th x1.th region).blocks k := fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
    have h4y : HoonMap.get g4.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
      rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_y _ _ _ d2
    have h4n : HoonMap.get g4.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
      rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_n _ _ _ d2
    have h42 : ∀ k, k < g2.bo → HoonMap.get g4.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
    have h41 : ∀ k, k < g1.bo → HoonMap.get g4.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
    -- the labels
    have la : ∀ e ∈ entries x0.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
      ⟨(Ra.labs e he).1, Nat.lt_trans (Ra.labs e he).2.1 Ra.hi⟩
    have lb : ∀ e ∈ entries x1.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
      ⟨(Rb.labs e he).1, Nat.lt_trans (Rb.labs e he).2.1 Rb.hi⟩
    have la' := labels_bound (P := fun o => g1.bo ≤ o ∧ o < g2.bo) la
    have lb' := labels_bound (P := fun o => g0.bo ≤ o ∧ o < g1.bo) lb
    have labAll : ∀ o ∈ (entries (mk ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩
        [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] [])).map Prod.fst, g0.bo ≤ o ∧ o ≤ g2.bo + 1 := by
      intro o ho
      rcases (mem_labels_six _ _ _ _ _ o).mp ho with e | e | e | e
      · omega
      · have := la' o e; omega
      · omega
      · have := lb' o e; omega
    have en := entries_six (⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩ : Sure S) g2.bo (g2.bo + 1)
      x0.laz x1.laz
    have reB : ∀ r, g1.re ≤ r → r < g2.re → g0.re ≤ r ∧ r < g4.re := fun r h1 h2 => ⟨by omega, by omega⟩
    have reA : ∀ r, g0.re ≤ r → r < g1.re → g0.re ≤ r ∧ r < g4.re := fun r h1 h2 => ⟨h1, by omega⟩
    refine ⟨E04, ?_, ?_, by simp only [jmp0]; omega, by simp only [jmp0]; omega, ⟨[], Termin.hop nc.th, h4o⟩,
      fun r hr => ?_, Rc.dist, ?_, ?_, ?_, ?_, fun s hs => ?_, ?_⟩
    · -- grow
      exact Rb.grow.trans (Ra.grow.trans ((grow_sixGenL region (jumpsBelow_hop Ra.lo Ra.hi)
        (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).trans
        (Dc.grow.trans ((grow_emit (jumpsBelow_hop Dc.lo Dc.hi)).trans (grow_addOps hadd)))))
    · -- cond
      rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond, (kc_run c _).keep _ _ _ h3, sixGenL_cond, Ra.cnd, Rb.cnd]
    · -- regs
      rcases Rc.regs r hr with e | e
      · exact e.elim
      · simp only [sixGenL_re] at e; exact ⟨by omega, by omega⟩
    · -- eregs
      rw [en]
      intro e he
      simp only [List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | (rfl | he)
      · exact ⟨Ra.dist, fun r hr => reB r (Ra.regs r hr).1 (Ra.regs r hr).2⟩
      · exact ⟨(Ra.eregs e he).1, fun r hr => reB r ((Ra.eregs e he).2 r hr).1 ((Ra.eregs e he).2 r hr).2⟩
      · exact ⟨Rb.dist, fun r hr => reA r (Rb.regs r hr).1 (Rb.regs r hr).2⟩
      · exact ⟨(Rb.eregs e he).1, fun r hr => reA r ((Rb.eregs e he).2 r hr).1 ((Rb.eregs e he).2 r hr).2⟩
    · -- labs
      rw [en]
      intro e he
      simp only [List.mem_append, List.mem_cons] at he
      simp only [jmp0]
      rcases he with (rfl | he) | (rfl | he)
      · exact ⟨by omega, by omega, x0.th, h4y⟩
      · obtain ⟨l1, l2, th, hth⟩ := Ra.labs e he
        have := la e he
        exact ⟨by omega, by omega, th, (h42 _ this.2).trans hth⟩
      · exact ⟨by omega, by omega, x1.th, h4n⟩
      · obtain ⟨l1, l2, th, hth⟩ := Rb.labs e he
        have := lb e he
        exact ⟨l1, by omega, th, (h41 _ this.2).trans hth⟩
    · -- nodup
      rw [en, List.map_append, List.nodup_append]
      simp only [List.map_cons, List.nodup_cons, List.mem_cons]
      refine ⟨⟨fun hm => by have := la' _ hm; omega, Ra.nodup⟩, ⟨fun hm => by have := lb' _ hm; omega, Rb.nodup⟩,
        fun x hx y hy => ?_⟩
      have hx' : g1.bo ≤ x ∧ x ≤ g2.bo := by
        rcases hx with e | e
        · omega
        · have := la' x e; omega
      rcases hy with e | e
      · omega
      · have := lb' y e; omega
    · -- size
      rw [en]; simp only [List.length_append, List.length_cons, sixCount]
      have := Ra.size; have := Rb.size; omega
    · -- nec
      have fo' : ¬ FitsS nc.laz s := fun f => hs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
      rw [pureEval_n6]
      rcases Rc.nec s fo' with e | ⟨_, _, e⟩
      · rw [e]; rfl
      · exact e.elim
    · -- sem
      intro cc ned σ O st t gul s ag hned regs hh hn
      have notLab : ∀ o, g0.bo ≤ o → o < g4.bo → (g2.bo + 2 ≤ o ∨
          (g1.bo ≤ o ∧ o < g2.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
          (o < g1.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
          HoonMap.get cc.blocks o = HoonMap.get g4.blocks o := by
        intro o h0 h1 hc'
        refine ag.1 o h0 h1 fun hm => ?_
        rcases (mem_labels_six _ _ _ _ _ o).mp hm with e | e | e | e
        · omega
        · have := la' o e
          rcases hc' with x | x | x
          · omega
          · exact x.2.2 e
          · omega
        · omega
        · have := lb' o e
          rcases hc' with x | x | x
          · omega
          · omega
          · exact x.2 e
      have hc3 : HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop nc.th⟩ :=
        (notLab g3.bo (by omega) (by omega) (Or.inl (by omega))).trans h4o
      have agC : Agree cc (sixGenL g2 x0.th x1.th region) g3 := fun o h0 h1 => by
        simp only [sixGenL_bo] at h0
        rw [notLab o (by omega) (by omega) (Or.inl h0), h4k o (by omega)]
      have agA : AgreeF lib O cc gul st t ned g1 g2 x0.laz s := by
        refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
        · rw [notLab o (by omega) (by omega) (Or.inr (Or.inl ⟨h0, h1, hnl⟩)), h42 o h1]
        · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e (by rw [en]; simp [he])
          exact ⟨A, th, (h42 _ (la e he).2).symm.trans hg, hcb, hF⟩
      have agB : AgreeF lib O cc gul st t ned g0 g1 x1.laz s := by
        refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
        · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr ⟨h1, hnl⟩)), h41 o h1]
        · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e (by rw [en]; simp [he])
          exact ⟨A, th, (h41 _ (lb e he).2).symm.trans hg, hcb, hF⟩
      -- a lazy block
      have lazyBlk : ∀ (o : Nat) (x : NextL S) (nm' : Nomm) (gA gB : Gen Map),
          (o, x.laz) ∈ entries (mk ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩
            [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) →
          HoonMap.get g4.blocks o = some ⟨[], [], Termin.hop x.th⟩ → RunOKD (Map := Map) lib nm' gA gB x →
          AgreeF lib O cc gul st t ned gA gB x.laz s → gB.re ≤ g4.re →
          ∀ R2, HoldsN ned R2 s → goJ lib O cc gul st R2 t (jmp0 o) = some (toneOf t (pureEval nm' s), st) := by
        intro o x nm' gA gB hm hb R agX hre R2 hR2
        obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 _ hm
        rw [hb] at hg
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
        subst hg
        have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
          have := hned y hy; have := (R.regs y hy').2; omega
        rw [goJ_jmp0 _ _ _ _ hcb]
        by_cases f : FitsS x.laz.sure s
        · obtain ⟨R3, hh3, hn3, e3⟩ := (fillSem_run hF hR2 dj x.th).1 f
          rw [e3]
          exact R.sem cc ned σ O st t gul s agX (fun r hr => Nat.le_trans hre (hned r hr)) R3 hh3 hn3
        · rw [(fillSem_run hF hR2 dj x.th).2 f, R.nec s f]; rfl
      have Hc := Rc.sem dG cc agC σ O st s regs t gul ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩
      have keepF : ∀ R2, (∀ r, Keep (sixGenL g2 x0.th x1.th region) g3
          (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) r →
          SkaModel.read r R2 = SkaModel.read r regs) → HoldsN ned R2 s :=
        fun R2 k2 => HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr (by have := hned x hx; omega), fun e => e⟩) hn
      show goJ lib O cc gul st regs t (jmp0 g3.bo) = _
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop, pureEval_n6]
      cases ec : pureEval c s with
      | none => rw [ec] at Hc; exact Hc
      | some v =>
        rw [ec] at Hc
        rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
        · obtain ⟨R2, k2, e2⟩ := Hc; rw [e2]
          exact lazyBlk g2.bo x0 a g1 g2 (by rw [en]; simp) h4y Ra agA (by omega) R2 (keepF R2 k2)
        · obtain ⟨R2, k2, e2⟩ := Hc; rw [e2]
          exact lazyBlk (g2.bo + 1) x1 b g0 g1 (by rw [en]; simp) h4n Rb agB (by omega) R2 (keepF R2 k2)
        · exact Hc
        · exact Hc

end Comp
end SkaModel
end Formalization
