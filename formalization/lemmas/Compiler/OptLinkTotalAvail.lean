import lemmas.Ska.OptAliasFirst
import lemmas.Compiler.OptLinkTotalFinal

/-!
# `+alias` keeps `ReadsIn N` (track H, Gaps 13)

Track E's availability invariant (`TAv`, `TInvA` of `OptAliasAvail.lean`) at
**`UN bl N y := y ∈ allDefs bl ∨ y < N`**, which needs no path: the
immediates, the registers facts name and the `old` of every register done are
defined before or below `N`.  `Done` is cut to `UN` (`DoneS ∧ UN`): a
register done with no definition keeps its name, and a register read is in
`UN` by `ReadsIn N` (`bodyOK_restrict`, `bodyDone_restrict`).  The entry
facts `entryInfo nargs` name nothing.  `TInvU` is `TInvA` at `UN` without the
edges (taken from `TInvA`, `tav_at`); **`tavU_start`**, **`tavU_pre`**,
**`tavU_step`**, **`tavU_walk`**, **`tavU_at`** are copies of `tav_start`,
`tav_pre`, `tav_step`, `tav_walk`, `tav_at` at `UN`.

**`alias_readsIn`**: the body of `alias_defFirst`, with its `hr0` (the read
is defined before) replaced by the case split: a renamed read `old y` that
`tav_pre` gives as undefined before is below `N` by `tavU_pre`.
**`aliasReadsN`**: `AliasReadsN` (`OptLinkTotalFinal.lean`) for every `pick`
that picks a member, so **`gateTotalN`** and the final corollaries
**`optimize_total_finishLFX`** and **`optimize_total_finishLUX`** hold with no
hypothesis on the optimizer.  The decidable form of the invariant is checked
in `OptLinkTotalAvailCheck.lean`.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel Opt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- **The registers defined before or below `N`.** -/
def UN (bl : Map Blob) (N : Nat) (y : Nat) : Prop := y ∈ allDefs bl ∨ y < N

theorem asSrc_reads {op : Pole} {x : Nat} (h : x ∈ asSrc op) : x ∈ aliasReads op := by
  cases op <;> simp only [asSrc, List.mem_cons, List.not_mem_nil, or_false] at h
  all_goals simp only [aliasReads, aliasDst, poleRegs]
  case mov s d => exact av_erase2.mpr h
  case inc s d => exact av_erase2.mpr h
  case con a b d => exact av_erase3.mpr h
  case hed s d => exact av_erase2.mpr h
  case tal s d => exact av_erase2.mpr h
  case cel p => exact List.mem_singleton.mpr h
  case lob p => exact List.mem_singleton.mpr h

/-- `BodyOK` with `Done` cut to the registers of `U`, when every source is in
`U`. -/
theorem bodyOK_restrict {Cl : Nat → Prop} (U : Nat → Prop) : ∀ (ops : List Pole) (Def Done Done' : Nat → Prop),
    BodyOK Cl ops Def Done → (∀ op ∈ ops, ∀ x ∈ asSrc op, U x) → (∀ x, Done x → U x → Done' x) →
    BodyOK Cl ops Def Done'
  | [], _, _, _, _, _, _ => trivial
  | op :: l, Def, Done, Done', ⟨hs, hd, hb⟩, hU, hD => by
    refine ⟨fun x hx => hD x (hs x hx) (hU op List.mem_cons_self x hx), hd, ?_⟩
    exact bodyOK_restrict U l _ _ _ hb (fun op' h' => hU op' (List.mem_cons_of_mem _ h'))
      (fun x hx hu => hx.imp_left (fun h => hD x h hu))

theorem bodyDone_restrict {Cl U : Nat → Prop} : ∀ (ops : List Pole) (D D' : Nat → Prop) (x : Nat),
    bodyDone Cl ops D x → (∀ y, D y → U y → D' y) → U x → bodyDone Cl ops D' x
  | [], _, _, x, h, hD, hu => hD x h hu
  | _ :: l, _, _, x, h, hD, hu => bodyDone_restrict l _ _ x h (fun y hy hu' => hy.imp_left (fun h => hD y h hu')) hu

/-- **The availability invariant at `UN`**: `TInvA` (`OptAliasAvail.lean`)
with `AvP` replaced by `UN`, without the edges. -/
structure TInvU (bl G : Map Blob) (N : Nat) (pre : List Nat) (g : AGen Map) : Prop where
  ends : ∀ q b j lq mq p, q ∈ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin →
    g.info q = some lq → g.imms q = some mq → BPath G (q :: p) →
    (∀ n r, r ∈ mq n → UN bl N r) ∧ (∀ r i x, lq r = some i → ANames i x → UN bl N x)
  glob : ∀ d q b j p, q ∈ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin → d ∈ blockDefs b →
    ClR bl d → (∀ o' i, DeadFill bl d o' i → o' ∉ pre) → BPath G (q :: p) → UN bl N (g.old d)

theorem tavU_init {bl G : Map Blob} {N : Nat} {rev : Map (List Nat)} : TInvU bl G N [] (aliasInit (Map := Map) rev) where
  ends := fun _ _ _ _ _ _ hq => absurd hq List.not_mem_nil
  glob := fun _ _ _ _ _ hq => absurd hq List.not_mem_nil

/-- **`TAv` at `UN` at the start of a walked block** (a copy of `tav_start`). -/
theorem tavU_start {bl G : Map Blob} (hS : AliasSSAB bl) (hGs : TargetsSub bl G) {N nargs : Nat} {pre l : List Nat}
    {o : Nat} {g : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hI : SInv bl (pre ++ o :: l) pre g)
    (hA : TInvA bl G pre g) (hU : TInvU bl G N pre g) (hGq : ∀ q ∈ pre, HoonMap.get G q = HoonMap.get g.new q)
    {b : Blob} (hb : HoonMap.get bl o = some b) {p : List Nat} (hπG : BPath G (o :: p))
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : (if g.rev o = [] then some (entryInfo nargs) else aliasStart g o (g.rev o)) = some info)
    (him : aliasStartImms g (g.rev o) = some imms) (hed : aliasEdges g o (g.rev o) = some edges)
    (hpa : aliasPars g b.par edges info = some loc0) :
    TAv ⟨g.old, loc0, imms⟩ (UN bl N) (fun d => DoneS bl pre p b d ∧ UN bl N d) := by
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hπ : BPath bl (o :: p) := bpath_sub hGs hπG
  have hR : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hparold : ∀ x ∈ b.par, ClR bl x → g.old x = x := fun x hx hc =>
    awi_self hS ht hI.oldw hc (awi_par_notDefW hS.1 hR hb hx hopre)
  have hold : ∀ d, DoneS bl pre p b d ∧ UN bl N d → UN bl N (g.old d) := by
    intro d ⟨⟨hd, hc, hf⟩, hu⟩
    rcases hd with hd | hd | ⟨o'', ho'', b'', hb'', hd⟩
    · rw [tav_undef hI.oldw hd]; exact hu
    · rw [hparold d hd hc]; exact Or.inl (bdef_allDefs hb (List.mem_append_left _ hd))
    · obtain ⟨b3, j3, hb3, hj3⟩ := bdef_jumps hπ rfl o'' ho''
      rw [hb''] at hb3; cases hb3
      obtain ⟨p'', hp'', -⟩ := bpath_suffix hπG rfl o'' ho''
      exact hU.glob d o'' b'' j3 p'' (sst_path_pre ht hopre hπ o'' ho'') hb'' hj3 hd hc hf hp''
  cases p with
  | nil =>
    have ho0 : o = 0 := by cases hπG; rfl
    subst ho0
    have h0 : g.rev 0 = [] := awa_rev_zero ht hI.rev
    rw [if_pos h0] at hst
    cases hst
    rw [h0] at him hed
    simp only [aliasStartImms, Option.some.injEq] at him
    subst him
    simp [aliasEdges] at hed
    subst hed
    have hloc : ∀ r i, loc0 r = some i → i = {} := by
      intro r i hr
      rcases sst_pars_nil b.par _ loc0 hpa r i hr with hr | ⟨-, hr⟩
      · simp only [entryInfo] at hr
        split at hr
        · cases hr; rfl
        · cases hr
      · exact hr
    exact ⟨fun n r hr => absurd hr List.not_mem_nil,
      fun r i x hr hx => by rw [hloc r i hr] at hx; exact absurd hx ab_nm_empty, hold⟩
  | cons q p' =>
    obtain ⟨hπq, pbq, jg, hpbq, hjg, hjgo⟩ : BPath G (q :: p') ∧ ∃ pb j, HoonMap.get G q = some pb ∧
        j ∈ getJmps pb.fin ∧ j.there = o := by
      cases hπG with
      | step hp hb' hj => exact ⟨hp, _, _, hb', hj, rfl⟩
    obtain ⟨bq, jq, hbq, hjq, hjqo⟩ : ∃ bq jq, HoonMap.get bl q = some bq ∧ jq ∈ getJmps bq.fin ∧ jq.there = o := by
      cases hπ with
      | step _ hb' hj => exact ⟨_, _, hb', hj, rfl⟩
    have hRq : Reach bl q := ssk_bpath_reach hπ q (List.mem_cons_of_mem _ List.mem_cons_self)
    have hqpre : q ∈ pre := awr_pre ht (ht.2.2.2.1 q hRq) hbq hjq hjqo
    have hpbq' : HoonMap.get g.new q = some pbq := by rw [← hGq q hqpre]; exact hpbq
    have hq : q ∈ g.rev o := by rw [← hjgo]; exact hA.lst q pbq jg hqpre hpbq' hjg (hjgo ▸ hopre)
    have h0 : g.rev o ≠ [] := List.ne_nil_of_mem hq
    rw [if_neg h0] at hst
    obtain ⟨lq, mq, hlq, hmq, -, -, -⟩ := hI.ends q bq jq pbq hqpre hbq hjq hpbq'
    obtain ⟨himq, hnq⟩ := hU.ends q bq jq lq mq p' hqpre hbq hjq hlq hmq hπq
    refine ⟨fun n r hr => himq n r (ast_imms_sub him hq hmq n r hr), ?_, hold⟩
    have hN := ast_start_names hst hq hlq
    exact (ast_pars_names (D := UN bl N) hlq
      (fun r i y hr hy => hnq r i y hr hy) b.par edges info loc0 jg.args hpa
      (aedge_mem hed hq hpbq' hjg hjgo) (fun r i y hr hy => by
        obtain ⟨i', hi', hy'⟩ := hN r i y hr hy
        exact hnq r i' y hi' hy')).1

/-- **`TAv` at `UN` at a place of a walked block** before every dead fill (a
copy of `tav_pre`), given `ReadsIn N`. -/
theorem tavU_pre {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {bl G : Map Blob}
    (hD : DInvS bl) (hGs : TargetsSub bl G) {N nargs : Nat} (hRd : ReadsIn N bl) {pre l : List Nat}
    {o : Nat} {g : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hI : SInv bl (pre ++ o :: l) pre g)
    (hA : TInvA bl G pre g) (hU : TInvU bl G N pre g) (hGq : ∀ q ∈ pre, HoonMap.get G q = HoonMap.get g.new q)
    {b : Blob} (hb : HoonMap.get bl o = some b) {p : List Nat} (hπG : BPath G (o :: p))
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : (if g.rev o = [] then some (entryInfo nargs) else aliasStart g o (g.rev o)) = some info)
    (him : aliasStartImms g (g.rev o) = some imms) (hed : aliasEdges g o (g.rev o) = some edges)
    (hpa : aliasPars g b.par edges info = some loc0) {m : Nat} (hm : ∀ k r, k < m → ¬ DeadFill bl r o k)
    {outa : List Pole} {sta : ABody}
    (hba : Opt.aliasBody pick (b.body.take m) ⟨g.old, loc0, imms⟩ = some (outa, sta)) :
    TAv sta (UN bl N) (bodyDone (ClR bl) (b.body.take m) (fun d => DoneS bl pre p b d ∧ UN bl N d)) := by
  have hS : AliasSSAB bl := hD.2.1
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hπ : BPath bl (o :: p) := bpath_sub hGs hπG
  have hR : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hab0 := awa_abinv_mono (sst_start hS ht hI hb hR hst him hed hpa) (fun _ h => h)
    (Done' := fun d => DoneS bl pre p b d ∧ UN bl N d) (fun x hx => sst_doneS ht hopre hπ hx.1)
  have hBO0 := awi_bodyOK hS hD.1.1.2.1 hπ hb hm hopre (Done := DoneS bl pre p b) (awi_doneS_body hopre)
  have hBO := bodyOK_restrict (UN bl N) _ _ _ (fun d => DoneS bl pre p b d ∧ UN bl N d) hBO0
    (fun op hop x hx => by
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hop
      rw [List.getElem?_take] at hk
      split at hk
      · exact hRd o b k x hR hb (Or.inl (by rw [List.head?_drop, hk]; exact asSrc_reads hx))
      · cases hk)
    (fun x hx hu => ⟨hx, hu⟩)
  have hT0 := tavU_start hS hGs ht hI hA hU hGq hb hπG hst him hed hpa
  refine tav_mono (tav_body hpick _ _ _ _ _ outa sta hba hab0 hBO hT0) (fun y hy => ?_) (fun _ h => h)
  rcases hy with hy | hy
  · exact hy
  · exact Or.inl (bdef_allDefs hb (List.mem_append_right _
      (List.mem_filterMap.mpr (by
        obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp (abody_dsts hba hy)
        exact ⟨op, List.mem_of_mem_take hop, hd⟩))))

end

/-! ## The induction over `topo` -/

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map] {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob}
  {topo : List Nat} {rev : Map (List Nat)} {gF : AGen Map}

/-- **One block of the walk keeps `TInvU`** (a copy of `tav_step`). -/
theorem tavU_step (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (hRd : ReadsIn nargs bl)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) {pre l : List Nat} {o : Nat} {g g' : AGen Map}
    (hto : topo = pre ++ o :: l) (h1 : aliasWalk pick nargs bl pre (aliasInit rev) = some g)
    (h2 : aliasBlock pick nargs bl g o = some g') (hU : TInvU bl gF.new nargs pre g) :
    TInvU bl gF.new nargs (pre ++ [o]) g' := by
  have hS : AliasSSAB bl := hD.2.1
  have ht : TopoOK bl (pre ++ o :: l) := hto ▸ hT.1.1
  have hI := sst_pre hpick hD hT hto h1
  have hA := tav_at hpick hD hT h hto h1
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hol : o ∉ l := fun h' => ((List.nodup_append.mp ht.1).2.1 |> List.nodup_cons.mp).1 h'
  have hoo : o ∈ pre ++ [o] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have h3 : aliasWalk pick nargs bl l g' = some gF := by
    have e := h
    rw [hto, awa_walk_append, h1, Option.bind_some] at e
    simp only [aliasWalk, h2, Option.bind_some] at e
    exact e
  have hGs : TargetsSub bl gF.new := alias_targetsSub hT h
  have hGo : HoonMap.get gF.new o = HoonMap.get g'.new o := ((awk_walk l g' gF h3).2 o hol).2.2
  have hGq : ∀ q ∈ pre, HoonMap.get gF.new q = HoonMap.get g.new q := by
    intro q hq
    have hql : q ∉ l := fun h' => (List.nodup_append.mp ht.1).2.2 q hq q (List.mem_cons_of_mem _ h') rfl
    have hqo : q ≠ o := fun e => hopre (e ▸ hq)
    rw [((awk_walk l g' gF h3).2 q hql).2.2, ((awk_block h2).2 q hqo).2.2]
  have hnew0 : HoonMap.get g.new o = none := by
    cases e : HoonMap.get g.new o with
    | none => rfl
    | some _ => exact absurd (hI.news o (by rw [e]; rfl)) hopre
  have walked : ∀ p, BPath gF.new (o :: p) → ¬ (g.rev o = [] ∧ o ≠ 0) := by
    intro p hπ hd
    have := bpathG_some hT h hπ rfl
    rw [hGo, sst_drop_new h2 hd, hnew0] at this
    cases this
  refine ⟨fun q b j lq mq p hq hb hj hlq hmq hπ => ?_, fun d q b j p hq hb hj hdd hc hf hπ => ?_⟩
  · rcases List.mem_append.mp hq with hq | hq
    · have hqo : q ≠ o := fun e => hopre (e ▸ hq)
      obtain ⟨c1, c2, -⟩ := (awk_block h2).2 q hqo
      exact hU.ends q b j lq mq p hq hb hj (c1 ▸ hlq) (c2 ▸ hmq) hπ
    · have e := List.mem_singleton.mp hq
      subst e
      have hd := walked p hπ
      obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h2 hd
      rw [hb] at e3; cases e3
      subst e8
      simp only [as_upd_self, Option.some.injEq] at hlq hmq
      subst hlq hmq
      have hnf : ∀ k r, k < b.body.length → ¬ DeadFill bl r q k := fun k r _ hdf => by
        obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
        rw [hb] at hb3; cases hb3; rw [hu] at hj; simp [getJmps] at hj
      have hT0 := tavU_pre hpick hD hGs hRd ht hI hA hU hGq hb hπ e1 e2 e4 e5 hnf
        (by rw [List.take_length]; exact e6)
      exact ⟨fun n r hr => hT0.imm n r hr, fun r i x hr hx => hT0.names r i x hr hx⟩
  · have hπb : BPath bl (q :: p) := bpath_sub hGs hπ
    have hRq : Reach bl q := ssk_bpath_reach hπb q List.mem_cons_self
    rcases List.mem_append.mp hq with hq | hq
    · have hqo : q ≠ o := fun e => hopre (e ▸ hq)
      have hlive : ∃ s, LiveDef bl d s ∧ s.1 = q := by
        rcases List.mem_append.mp hdd with hm | hm
        · exact ⟨(q, none), awi_par_live hRq hb hm, rfl⟩
        · obtain ⟨i, op, hi, he⟩ := bdef_idx hm
          exact ⟨(q, some i), awi_jump_live hRq hb hj hi he, rfl⟩
      obtain ⟨s, hs, hsq⟩ := hlive
      rw [awi_frame_step ht hI.rev h2 (fun hR b' hb' hm => by
        obtain ⟨k, op, hk, he⟩ := bdef_idx hm
        by_cases hdf : DeadFill bl d o k
        · exact hf o k hdf hoo
        · have e := hS.1 d s (o, some k) hs ⟨hR, ⟨b', op, hb', hk, he⟩, fun i hi => by cases hi; exact hdf⟩
          rw [e] at hsq
          exact hqo hsq.symm)]
      exact hU.glob d q b j p hq hb hj hdd hc (fun o' i hdf ho' => hf o' i hdf (List.mem_append_left _ ho')) hπ
    · have e := List.mem_singleton.mp hq
      subst e
      have hd := walked p hπ
      obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h2 hd
      rw [hb] at e3; cases e3
      subst e8
      show UN bl nargs (rb.2.old d)
      rcases List.mem_append.mp hdd with hm | hm
      · have hnd : d ∉ b.body.filterMap aliasDst := fun hm2 => by
          obtain ⟨k, op, hk, he⟩ := bdef_idx hm2
          by_cases hdf : DeadFill bl d q k
          · exact hf q k hdf hoo
          · have e := hS.1 d (q, none) (q, some k) (awi_par_live hRq hb hm)
              ⟨hRq, ⟨b, op, hb, hk, he⟩, fun i hi => by cases hi; exact hdf⟩
            simp at e
        rw [awk_body_old b.body _ rb.1 rb.2 e6 d hnd]
        dsimp only
        rw [awi_self hS ht hI.oldw hc (awi_par_notDefW hS.1 hRq hb hm hopre)]
        exact Or.inl (bdef_allDefs hb (List.mem_append_left _ hm))
      · have hnf : ∀ k r, k < b.body.length → ¬ DeadFill bl r q k := fun k r _ hdf => by
          obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
          rw [hb] at hb3; cases hb3; rw [hu] at hj; simp [getJmps] at hj
        have hT0 := tavU_pre hpick hD hGs hRd ht hI hA hU hGq hb hπ e1 e2 e4 e5 hnf
          (by rw [List.take_length]; exact e6)
        rw [List.take_length] at hT0
        exact hT0.old d (awa_bodyDone_dst _ _ _ hm hc)

/-- **`TInvU` along a part of the walk.** -/
theorem tavU_walk (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (hRd : ReadsIn nargs bl) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) :
    ∀ (l pre r : List Nat) (g g' : AGen Map), topo = pre ++ l ++ r →
      aliasWalk pick nargs bl pre (aliasInit rev) = some g → TInvU bl gF.new nargs pre g →
      aliasWalk pick nargs bl l g = some g' → TInvU bl gF.new nargs (pre ++ l) g'
  | [], pre, r, g, g', _, _, hU, hw => by
    simp only [aliasWalk, Option.some.injEq] at hw; subst hw; simpa using hU
  | o :: l, pre, r, g, g', hto, h1, hU, hw => by
    simp only [aliasWalk] at hw
    obtain ⟨g1, h2, hw⟩ := Option.bind_eq_some_iff.mp hw
    have hU1 := tavU_step hpick hD hT hRd h (l := l ++ r) (by simpa using hto) h1 h2 hU
    have h1' : aliasWalk pick nargs bl (pre ++ [o]) (aliasInit rev) = some g1 := by
      rw [awa_walk_append, h1, Option.bind_some]; simp only [aliasWalk, h2, Option.bind_some]
    have := tavU_walk hpick hD hT hRd h l (pre ++ [o]) r g1 g' (by simpa using hto) h1' hU1 hw
    simpa using this

/-- **`TInvU` at the point a block is walked.** -/
theorem tavU_at (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (hRd : ReadsIn nargs bl) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) {pre l : List Nat}
    {o : Nat} {g : AGen Map} (hto : topo = pre ++ o :: l) (h1 : aliasWalk pick nargs bl pre (aliasInit rev) = some g) :
    TInvU bl gF.new nargs pre g := by
  have := tavU_walk hpick hD hT hRd h pre [] (o :: l) _ g (by simpa using hto) rfl tavU_init h1
  simpa using this

/-- **`+alias` keeps `ReadsIn`**: the body of `alias_defFirst`, with the case
split on a renamed read that `tav_pre` gives as undefined before. -/
theorem alias_readsIn (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (hRd : ReadsIn nargs bl) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) :
    ReadsIn nargs gF.new := by
  have hS : AliasSSAB bl := hD.2.1
  have ht := hT.1.1
  have hGs := alias_targetsSub hT h
  intro o b' i r hro hb' hread
  obtain ⟨p, hπG⟩ := awi_reach_bpath hro
  obtain ⟨pre, l, g1, g2, b, st0, rb, rf, hto, h1, h2, h3, hne, hb, hA0, hrb, hrf, -, hbe⟩ :=
    aw_new ht hT.2 h hb'
  obtain ⟨info, imms, b1, edges, loc0, rb1, rf1, e1, e2, e3, e4, e5, e6, e7, -⟩ := awa_block_parts h2 hne
  rw [hb] at e3; cases e3
  have e0 := aStart_of_parts e1 e2 e4 e5
  rw [hA0] at e0; cases e0
  subst hbe
  have hI := sst_pre hpick hD hT hto h1
  have hA := tav_at hpick hD hT h hto h1
  have hU := tavU_at hpick hD hT hRd h hto h1
  have ht' : TopoOK bl (pre ++ o :: l) := hto ▸ ht
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht'.1).2.2 o h' o List.mem_cons_self rfl
  have hGq : ∀ q ∈ pre, HoonMap.get gF.new q = HoonMap.get g1.new q := by
    intro q hq
    have hql : q ∉ l := fun h' => (List.nodup_append.mp ht'.1).2.2 q hq q (List.mem_cons_of_mem _ h') rfl
    have hqo : q ≠ o := fun e => hopre (e ▸ hq)
    rw [((awk_walk l g2 gF h3).2 q hql).2.2, ((awk_block h2).2 q hqo).2.2]
  have hπ : BPath bl (o :: p) := bpath_sub hGs hπG
  have hRo : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hdefb : ∀ x ∈ blockDefs ({ par := b.par, body := rb.1, fin := rf.1 } : Blob), x ∈ allDefs gF.new :=
    fun x hx => bdef_allDefs hb' hx
  have fin : ∀ outa : List Pole, rb.1.take i = outa →
      (AvP bl gF.new p r ∨ r ∈ b.par ∨ r ∈ outa.filterMap aliasDst) → UN bl nargs r →
      r ∈ allDefs gF.new ∨ r < nargs := by
    intro outa he hav hu
    rcases hav with (hav | ⟨o', -, b'', hb'', hd⟩) | hav | hav
    · rcases hu with hu | hu
      · exact absurd hu hav
      · exact Or.inr hu
    · exact Or.inl (bdef_allDefs hb'' hd)
    · exact Or.inl (hdefb r (List.mem_append_left _ hav))
    · rw [← he] at hav
      obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp hav
      exact Or.inl (hdefb r (List.mem_append_right _ (List.mem_filterMap.mpr ⟨op, List.mem_of_mem_take hop, hd⟩)))
  rcases hread with hread | ⟨hi, hrf'⟩
  · -- a read of an op after
    obtain ⟨op', hop', hrd⟩ : ∃ op', rb.1[i]? = some op' ∧ r ∈ aliasReads op' := by
      simp only at hread
      rw [List.head?_drop] at hread
      cases hx : rb.1[i]? with
      | none => rw [hx] at hread; simp at hread
      | some op' => rw [hx] at hread; exact ⟨op', rfl, by simpa using hread⟩
    obtain ⟨k, op, sta, outa, st1, hk, hba, hl, hop⟩ := abody_at b.body _ rb.1 rb.2 hrb i op' hop'
    have e := aop_rename hop
    subst e
    obtain ⟨y, hy, rfl⟩ := areads_rename sta.old op hrd
    have hm : ∀ k' r', k' < k → ¬ DeadFill bl r' o k' := by
      intro k' r' hk' hdf
      obtain ⟨b5, hb5, -, -, himm, -⟩ := hdf
      rw [hb] at hb5; cases hb5
      have hmem : (b.body.drop k')[k - k']? = some op := by
        rw [List.getElem?_drop, show k' + (k - k') = k by omega]; exact hk
      obtain ⟨n, d, rfl⟩ := himm op (List.mem_of_getElem? hmem)
      simp [aliasReads, aliasDst, poleRegs] at hy
    have hT0 := tav_pre hpick hD hGs ht' hI hA hGq hb hπG e1 e2 e4 e5 hm hba
    have hTU := tavU_pre hpick hD hGs hRd ht' hI hA hU hGq hb hπG e1 e2 e4 e5 hm hba
    have hyr : ReadAt b k y := Or.inl (by rw [List.head?_drop, hk]; exact hy)
    have hdone := awa_read_done hS hπ hb hopre (k := k) (x := y) hyr
    have hdoneU := bodyDone_restrict _ _ (fun d => DoneS bl pre p b d ∧ UN bl nargs d) y hdone
      (fun x hx hu => ⟨hx, hu⟩) (hRd o b k y hRo hb hyr)
    have hsplit := hrb
    rw [← List.take_append_drop k b.body, aliasBody_append, hba, Option.bind_some] at hsplit
    obtain ⟨⟨outb, st'⟩, -, es⟩ := Option.map_eq_some_iff.mp hsplit
    have htake : rb.1.take i = outa := by rw [← es, ← hl]; exact List.take_left
    exact fin outa htake (hT0.old y hdone) (hTU.old y hdoneU)
  · -- a read of the end after
    simp only at hi hrf'
    by_cases hbom : ∃ u, b.fin = Termin.bom u
    · obtain ⟨u, hu⟩ := hbom
      rw [hu] at hrf
      simp only [aliasFin, Option.some.injEq] at hrf
      rw [← hrf] at hrf'
      simp [finRegs] at hrf'
    · have hm : ∀ k r', k < b.body.length → ¬ DeadFill bl r' o k := fun k r' _ hdf => by
        obtain ⟨b5, hb5, hu, -⟩ := hdf
        rw [hb] at hb5; cases hb5; exact hbom hu
      have hba : Opt.aliasBody pick (b.body.take b.body.length) ⟨g1.old, loc0, imms⟩ = some rb := by
        rw [List.take_length]; exact hrb
      have hT0 := tav_pre hpick hD hGs ht' hI hA hGq hb hπG e1 e2 e4 e5 hm hba
      have hTU := tavU_pre hpick hD hGs hRd ht' hI hA hU hGq hb hπG e1 e2 e4 e5 hm hba
      obtain ⟨y, hy, rfl⟩ := afin_regs hrf (hD.2.2 o b hb) r hrf'
      have hyr : ReadAt b b.body.length y := Or.inr ⟨rfl, hy⟩
      have hdone := awa_read_done hS hπ hb hopre (k := b.body.length) (x := y) hyr
      have hdoneU := bodyDone_restrict _ _ (fun d => DoneS bl pre p b d ∧ UN bl nargs d) y hdone
        (fun x hx hu => ⟨hx, hu⟩) (hRd o b _ y hRo hb hyr)
      exact fin rb.1 (by rw [hi]; exact List.take_length) (hT0.old y hdone) (hTU.old y hdoneU)

end

/-! ## `AliasReadsN` and the totality of `+optimize` -/

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- **`AliasReadsN` holds** for every `pick` that picks a member. -/
theorem aliasReadsN {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) :
    AliasReadsN Map pick := by
  intro N bl topo rev f bl' hJ hT hR h
  obtain ⟨gF, hw, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact alias_readsIn hpick (dInvR_dInvS hJ) hT hR hw

end

open Comp Raw Pill Hoon in
/-- **`GateTotalN`** (track D's `RawInvStX.lean`), with no hypothesis. -/
theorem gateTotalN : GateTotalN := gateTotalN_of (aliasReadsN fun l hl => Ana.pickR_mem l hl)

section
open Comp Raw Pill Hoon
variable {S : Type} [HoonSet S]

open Pill Hoon in
/-- **The pill's `+optimize` returns on the raw n-ary code of every nomm of
`FragX`**, with no hypothesis on the optimizer. -/
theorem optimize_total_finishLFX {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight (TreapMap mugF)} (h : finishLF (S := S) (Map := TreapMap mugF) nm ord less bake = some c') :
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c' = some s' ∧ nock (C optBody (C c'.toNoun optC)) optBody = some s'.toNoun :=
  opt_total_finishLFX' (aliasReadsN fun l hl => Ana.pickR_mem l hl) hf hc hbake h

open Pill Hoon in
/-- **The same for the raw whole-subject code.** -/
theorem optimize_total_finishLUX {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    {c' : Straight (TreapMap mugF)} (h : finishLU (S := S) (Map := TreapMap mugF) nm = some c') :
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c' = some s' ∧ nock (C optBody (C c'.toNoun optC)) optBody = some s'.toNoun :=
  opt_total_finishLUX' (aliasReadsN fun l hl => Ana.pickR_mem l hl) hf hc h

end

end Compiler
end Formalization
