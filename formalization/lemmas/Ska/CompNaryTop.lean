import lemmas.Ska.CompUnproxyTop
import lemmas.Ska.CompLBDone
import lemmas.Ska.CompFourTop

/-!
# The n-ary top with calls

README Gaps 18.15 (a), (b).  The n-ary code of a nomm (`finishLFC`, the final
pass of `+compile-scc-in`) is the run under `%done`, then
`+need-ord-alloc-regs` of the bell's need, `+coerce-lazy` from those
registers into the run's lazy need at the entry block and at every lazy
entry, and `+to-straight` with the proxies the run made.  `finishTopF_genB`
is `finishTop_genB` (the whole-subject top, `+kerf`) for this top: from what
the run's relation says at the run's jump (`hsem`, with the program agreeing
with the run's blocks at every state, `AgreeUB`), it gives the same of the
code entered with the split of the subject by the code's need, on every
subject with the axes of the cape.

The ops `+coerce-lazy` puts in front of a block name only the final need's
registers (at or above the run's `re`, so no key of `cond`, `CondBelow`), the
registers of the need taken there (no keys, `ncond` / `econd`) and registers
it allocates (above every key), by `coerceLazyL_regs`, so `unproxy` leaves
them alone (`unproxy_ops`): this is the `RegsIn` clause the plan named, and
`coerceLazyL_spec`'s `FillSem` of the ops as they are is then the `FillSem`
of the program's ops.  The entry block must be no lazy entry (`DoneOK.nent`).

`finishLFC_contractGB` is `finishLUC_contractGB` for the n-ary code: from
`DoneOK` of the run, both halves of the contract on every subject of `P` with
the cape's axes, entered with its split.  `finishLFC_contractCallTreeA`,
`finishLFC_bellContractCallTreeA`: so the n-ary code of every member of
track C's `CallTreeA` (indirect calls, `%7`, `%4`, `%3`, `%5`, `%1`) meets the
bell contract at `x = false`.  Checked first: `CompNaryTopEx.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The n-ary top** (`finishTop_genB` with `+need-ord-alloc-regs`,
`+coerce-lazy` and `+to-straight` in place of `+kerf`): what `hsem` says of
the run's jump, the code entered with the split of a subject with the cape's
axes does. -/
theorem finishTopF_genB (lib : Lib) {g1 : Gen Map} {nex : NextL S} (R : TopSB g1 nex)
    (hent : Entry g1 (CGoal.done : CGoal S) nex.th)
    (hnent : nex.th.there ∉ (entries nex.laz).map Prod.fst)
    (Φ : (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop)
    (hsem : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      (∀ st' : σ, AgreeUB lib O c gul st' t cf ned gen0 g1 nex.laz s s) → (∀ r, NMem ned r → g1.re ≤ r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
      Φ σ O st t gul s (goJ lib O c gul st regs t nex.th))
    (hnec : ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → Φ σ O st t gul s (some (Tone.two t, st)))
    {ord : NeedOrd} {less : Cape} {nedF : Need} {g2 g3 g4 : Gen Map}
    (h2 : needOrdAllocRegs ord g1 = some (nedF, g2))
    (h3 : coerceLazyL nedF less nex.th.there nex.laz g2 = some ((), g3))
    (h4 : addOps nex.th.there [] g3 = some ((), g4))
    {c' : Straight Map} (hts : toStraightF g4.cond g4.blocks nedF nex.th.there = some c') :
    ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun),
      CapeAxes less s → SkaModel.split c'.need s = some args →
      Φ σ O st t gul s (execEntry lib O st c' args t gul) := by
  have hrun := isRun_needOrdAllocRegs h2
  have c5 := (kc_needOrdAllocRegs ord).keep g1 nedF g2 h2
  have c8 := (kc_coerceLazyL nedF less _ _).keep g2 () g3 h3
  have c9 := (KC.addOps' _ _).keep g3 () g4 h4
  have hc9 : g4.cond = g1.cond := by rw [c9, c8, c5]
  rw [hc9] at hts
  have d1 : g1.drop = false := R.ext.2.2.1
  obtain ⟨⟨k5, rfl⟩, l5, dist5, mem5⟩ := needOrdAllocRegs_spec ord g1 _ nedF h2
  simp only at l5 mem5
  -- the keys of `cond` lie below `g1.re`
  have cb1 : CondBelow g1 := R.cfr.below condBelow_gen0
  have nk : ∀ x, g1.re ≤ x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g1.cond x with
    | none => rfl
    | some _ => have := cb1 x (by simp [e]); omega
  have PA : ∀ (L : Need), (∀ r, NMem L r → HoonMap.get g1.cond r = Option.none) → ∀ A : List Pole,
      RegsIn (fun x => NMem nedF x ∨ NMem L x ∨ g1.re ≤ x) A → A.map (renPole (unproxy g1.cond)) = A :=
    fun L hL A hA => unproxy_ops (hA.mono fun x hx => by
      rcases hx with hx | hx | hx
      · exact nk x (mem5 x hx).1
      · exact hL x hx
      · exact nk x hx)
  obtain ⟨B, fin, hB⟩ : ∃ B fin, HoonMap.get g1.blocks nex.th.there = some ⟨[], B, fin⟩ := by
    rcases hent with ⟨b, hb, hp, _⟩ | e
    · exact ⟨b.body, b.fin, by rw [hb, ← hp]⟩
    · exact e.elim
  have regs1 : ∀ r, NMem nex.laz.sure.ned r → r < g1.re := fun r hr => (R.regs r hr).2
  have hnd : (nex.th.there :: (entries nex.laz).map Prod.fst).Nodup := List.nodup_cons.mpr ⟨hnent, R.nodup⟩
  -- `+coerce-lazy`
  obtain ⟨bo8, dr8, re8, oth8, Froot, Fents⟩ := coerceLazyL_spec h3 d1 dist5 (fun r hr => (mem5 r hr).2)
    ⟨R.dist, fun r hr => Nat.lt_of_lt_of_le (regs1 r hr) l5,
      fun r hr hl => by have := (mem5 r hr).1; have := regs1 r hl; omega⟩
    (fun e he => ⟨(R.eregs e he).1, fun r hr => Nat.lt_of_lt_of_le ((R.eregs e he).2 r hr).2 l5,
      fun r hr hl => by have := (mem5 r hr).1; have := ((R.eregs e he).2 r hl).2; omega⟩) hnd
  obtain ⟨Rroot, Rents⟩ := coerceLazyL_regs h3 d1 hnd
  have d3 : g3.drop = false := dr8.trans d1
  have F4 := front_addOps h4 d3
  obtain ⟨A0, hA0, semA0⟩ := Froot B fin hB
  have uA0 : A0.map (renPole (unproxy g1.cond)) = A0 := by
    obtain ⟨A0', hA0', RA0⟩ := Rroot B fin hB
    rw [hA0] at hA0'
    simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hA0'
    rw [List.append_cancel_right hA0'.1]
    exact PA _ R.ncond A0' (RA0.mono fun x hx => hx.elim Or.inl fun hx => hx.elim (fun h => Or.inr (Or.inl h))
      fun h => Or.inr (Or.inr (Nat.le_trans l5 h)))
  have hB4 : HoonMap.get g4.blocks nex.th.there = some ⟨[], A0 ++ B, fin⟩ := by
    have := F4.blk _ _ hA0; simpa using this
  have hents : ∀ e ∈ entries nex.laz, ∃ A Be th, HoonMap.get g1.blocks e.1 = some ⟨[], Be, Termin.hop th⟩ ∧
      HoonMap.get g4.blocks e.1 = some ⟨[], A ++ Be, Termin.hop th⟩ ∧ A.map (renPole (unproxy g1.cond)) = A ∧
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t s,
        CapeAxes less s → FillSem lib O c gul st t nedF k5 e.2.sure A s s := by
    intro e he
    obtain ⟨_, lt, Be, th, hth⟩ := R.labs e he
    have ne : e.1 ≠ nex.th.there := fun eq => hnent (eq ▸ List.mem_map_of_mem he)
    obtain ⟨A, hA, sA⟩ := Fents e he Be (Termin.hop th) hth
    obtain ⟨A', hA', RA⟩ := Rents e he Be (Termin.hop th) hth
    rw [hA] at hA'
    simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hA'
    refine ⟨A, Be, th, hth, ?_, ?_, sA⟩
    · rw [F4.other _ ne, hA]
    · rw [List.append_cancel_right hA'.1]
      exact PA _ (R.econd e he) A' (RA.mono fun x hx => hx.elim Or.inl fun hx => hx.elim
        (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr (Nat.le_trans l5 h)))
  have oth4 : ∀ o, o ≠ nex.th.there → o ∉ (entries nex.laz).map Prod.fst →
      HoonMap.get g4.blocks o = HoonMap.get g1.blocks o := fun o h1 h2 =>
    (F4.other o h1).trans (oth8 o h1 h2)
  -- every block goes down
  have D1 : DownRk (upRk g1.blocks) g1.blocks := downRk_gen0 R.grow
  have D4 : DownRk (upRk g1.blocks) g4.blocks := downRk_of_fins D1 fun k b' hk => by
    by_cases e1 : k = nex.th.there
    · subst e1; rw [hB4] at hk; cases hk; exact ⟨_, hB, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e2
      obtain ⟨A, Be, th, h1', h4', _⟩ := hents e he
      rw [h4'] at hk; cases hk; exact ⟨_, h1', rfl⟩
    · rw [oth4 k e1 e2] at hk; exact ⟨b', hk, rfl⟩
  -- the program: the unproxied blocks, with the entry block of the run
  let c1 : Straight Map := ⟨NeedOrd.none, 0, HoonMap.put (mapVals (unproxyBlob g1.cond) g4.blocks) nex.th.there
    (unproxyBlob g1.cond ⟨[], B, fin⟩)⟩
  have hc1o : HoonMap.get c1.blocks nex.th.there = some (unproxyBlob g1.cond ⟨[], B, fin⟩) := by
    simp [c1, HoonMap.get_put]
  have hag : ∀ k, k ≠ nex.th.there → HoonMap.get c1.blocks k = (HoonMap.get g4.blocks k).map (unproxyBlob g1.cond) :=
    fun k hk => by simp [c1, HoonMap.get_put, hk, get_mapVals]
  have Dc : DownRk (upRk g1.blocks) c1.blocks := by
    intro k b hk
    by_cases e : k = nex.th.there
    · subst e; rw [hc1o] at hk; cases hk; exact downRk_unproxy _ (D1 _ _ hB)
    · rw [hag k e] at hk
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact downRk_unproxy _ (D4 k b0 hb0)
  obtain ⟨_, start, hst, hentry⟩ := toStraightF_entryU hts hrun D4 Dc hag
  rw [hB4] at hst; cases hst
  intro σ O st s args t gul hP hsp
  obtain ⟨R0, hR0, he⟩ := hentry lib O st s args t gul hsp
  rw [he]
  have hub : unproxyBlob g1.cond ⟨[], A0 ++ B, fin⟩ =
      ⟨[], A0 ++ B.map (renPole (unproxy g1.cond)), renFin (unproxy g1.cond) fin⟩ := by
    simp only [unproxyBlob, renBlob, List.map_append, uA0, List.map_nil]
  rw [hub]
  have hj : nex.th = jmp0 nex.th.there := by
    have ha := R.args
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at ha; simp only at ha; subst ha; rfl
  have ag : ∀ st' : σ, AgreeUB lib O c1 gul st' t g1.cond nedF gen0 g1 nex.laz s s := fun st' => by
    refine ⟨fun o _ _ hnl => ?_, fun e he => ?_⟩
    · by_cases e : o = nex.th.there
      · subst e; rw [hc1o, hB]; rfl
      · rw [hag o e, oth4 o e hnl]
    · obtain ⟨A, Be, th, h1', h4', uA, sA⟩ := hents e he
      have ne : e.1 ≠ nex.th.there := fun eq => hnent (eq ▸ List.mem_map_of_mem he)
      refine ⟨A, Be, th, h1', ?_, (sA lib σ O c1 gul st' t s hP).mono l5⟩
      rw [hag _ ne, h4']
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_append, uA, renFin]
  have dj : ∀ x, NMem nedF x → ¬ NMem nex.laz.sure.ned x := fun x hx hl => by
    have := (mem5 x hx).1; have := regs1 x hl; omega
  obtain ⟨SoF, SoC⟩ := semA0 lib σ O c1 gul st t s hP R0 hR0
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := SoF fo
    rw [hr1]
    have hn1 : HoldsN nedF R1 s := HoldsN.agree nedF (fun x hx => kr1 x (Or.inl hx) (dj x hx)) hR0
    have := hsem g1.cond (fun _ _ => rfl) c1 nedF σ O st t gul s ag (fun r hr => (mem5 r hr).1) R1 hh1 hn1
    rw [hj, goJ_jmp0 _ _ _ _ hc1o] at this
    simpa only [unproxyBlob, renBlob, List.map_nil] using this
  · rw [SoC fo]; exact hnec σ O st t gul s fo

/-- **The n-ary contract from `DoneOK` under `%done`** (`finishLUC_contractGB`
for `finishLFC`): the n-ary code of a nomm whose run for `%done` from `gen0`
meets `DoneOK` at the needs `N` meets both halves of the contract for `N` on
every subject of `P` with the cape's axes, entered with its split. -/
theorem finishLFC_contractGB (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → DoneOK lib N P f gen0 gE nex)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c : Straight Map} (h : finishLFC (S := S) env nm ord less bake = some c) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s f args c ∧ ContractBwd lib N s f args c := by
  unfold finishLFC at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have D := hR hr
  have R := D.run
  simp only at h
  split at h
  · cases h
  obtain ⟨⟨nedF, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [hbake, List.map_nil] at h
  obtain ⟨⟨u3, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u4, g4⟩, h4, hts⟩ := Option.bind_eq_some_iff.mp h
  have T : TopSB gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTopF_genB lib T R.ent D.nent (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) h2 h3 h4 hts
  have B := finishTopF_genB lib T R.ent D.nent (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) h2 h3 h4 hts
  intro s hs hca args hsp
  refine ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩
  · exact F σ O st s args ti gul hca hsp Inv ν n tm r hs hN hS hF hm hI htr
  · exact B σ O st s args ti gul hca hsp Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The n-ary contract of a bell** from `DoneOK` of its run on the bell's
subjects, when nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishLFC_bellContractGB {lib : Lib} {env : CallEnv} {bl : Bell} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → DoneOK lib N (SkaModel.Fits bl.less) bl.fol gen0 gE nex)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) env nm ord cape bake = some c) : BellContract lib N bl false c := by
  intro s hs args hargs
  simp only [Bool.false_eq_true, if_false] at hargs
  rw [hbl] at hs
  have hca : CapeAxes cape s := fun axe h1 ha => capeAxes_of_fits axe h1 cape data s hn hs ha
  rw [← hbl] at hs
  exact finishLFC_contractGB lib N hR hbake h s hs hca args hargs

/-- **The n-ary contract of `CallTreeA`**: the n-ary code of every nomm of
track C's class meets both halves of the contract for its formula, on every
subject with the cape's axes, entered with its split. -/
theorem finishLFC_contractCallTreeA (lib : Lib) (env : CallEnv) (P : Noun → Prop) {b : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeA b f nm) {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (hc : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) (N : Needs) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s f args c ∧ ContractBwd lib N s f args c :=
  finishLFC_contractGB lib N (fun hr => callTreeA_done (S := S) (Map := Map) lib env h P (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr) hbake hc

/-- **The n-ary bell contract of `CallTreeA`** (`x = false`), when nothing is
baked and the bell's cape has no `[| |]`. -/
theorem finishLFC_bellContractCallTreeA {lib : Lib} {bl : Bell} {b : Bool} {nm : Nomm} (h : CallTreeA b bl.fol nm)
    {env : CallEnv} {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape)
    {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c : Straight Map} (hc : finishLFC (S := S) (Map := Map) env nm ord cape bake = some c) (N : Needs) :
    BellContract lib N bl false c :=
  finishLFC_bellContractGB N (fun hr => callTreeA_done (S := S) (Map := Map) lib env h _ (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr) hbl hn hbake hc

end Comp
end SkaModel
end Formalization
