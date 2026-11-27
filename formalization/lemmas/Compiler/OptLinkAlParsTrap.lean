import lemmas.Compiler.OptLinkAlPars

/-!
# `+alias`: the parameter trap and phase 12 (README Gaps 13)

```hoon
  =^  par-new=(list @uvre)  gen
    =/  edges=...  ...
    =|  out=(list @uvre)
    |-  ^-  [(list @uvre) _gen]
    ?~  par.bob  [(flop out) gen]
    =/  new  i.par.bob
    =/  ins=(list (unit info-reg))
      %+  turn  edges
      |=  [p=@uwoo args=(list (unit @uvre))]
      ?>  ?=(^ args)
      ?~  i.args  ~
      `(~(got by (~(got by info.gen) p)) u.i.args)
    =.  info-local.gen  (~(put by info-local.gen) new (param-info ins))
    =.  out  [new out]
    %=  $
      par.bob  t.par.bob
      edges  (turn edges |=([p=@uwoo args=(list (unit @uvre))] [p ?>(?=(^ args) t.args)]))
    ==
```

* `alPTC`: the trap's core `[trap [out [edges [bob [imms [info [pre S]]]]]]]`.
* `al_pain`: the gate of `ins` (`alPaIn`) is `UInfoRel` to the model's
  `aliasIn` (`+got:by` on `info.gen`, then on the facts of `p`).
* `al_patl`: the gate that drops the first argument (`alPaTl`).
* `al_part`: **the trap is the model's `aliasPars`**, by induction on the
  parameters: `par-new` is `out` reversed before the parameters, and
  `info-local` is `InfoMapRel` to the model's facts.
* `al_pars_perm`, **`al_pars`**: phase 12 on the Hoon's `pre`; the result is
  moved to the model's `g.rev o` by `aliasPars_edges_perm`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The core of the parameter trap. -/
def alPTC (OUT EDGES PAR BR IMMS INF PRE GEN NA BL REV TOPO : Noun) : Noun :=
  C alParTC (C OUT (C EDGES (C (C PAR BR) (C IMMS (C INF (C PRE (alWS GEN NA BL REV TOPO)))))))

/-- `+got:by` on a map of facts (as `loc_got` of `OptLinkAlBodyLoc.lean`,
which cannot be imported beside `OptLinkAlStartInfo.lean`). -/
theorem infoMap_got {LOC : Noun} {m : Opt.AInfo} (h : InfoMapRel LOC m) {r : Nat} {x : Opt.InfoReg}
    (hx : m r = some x) :
    ∃ N, InfoRel N x ∧
      nock (C by.got.battery (C (A r) (C by.battery (C LOC layer2)))) by.got.battery = some N := by
  obtain ⟨N, hN⟩ := h.2.2 r x hx
  obtain ⟨r', x', e, hx', hrel⟩ := h.2.1 _ _ hN
  have e' : r = r' := Noun.atom.inj e
  subst e'
  rw [hx] at hx'
  cases hx'
  exact ⟨N, hrel, got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _
    (getF_some h.1 hN)⟩

/-- **The gate of `ins`**: `?>  ?=(^ args)`, `~` for `~`, else the facts of
`u.i.args` in the store of `p`. -/
theorem al_pain (g : Opt.AGen (TreapMap mugF)) {INFO : Noun} (hI : InfoStoreRel INFO g.info)
    (e : Nat × List (Option Nat)) (y : Option Opt.InfoReg) (he : Opt.aliasIn g e = some y)
    (X OUT EDGES PAR BR IMMS INF PRE NEW OLD IMMSg LOC IMML RV F NA BL REV TOPO : Noun) :
    ∃ N, nock (C alPaIn (C (edgeN e) (C X (alPTC OUT EDGES PAR BR IMMS INF PRE
        (genN NEW OLD INFO IMMSg LOC IMML RV F) NA BL REV TOPO)))) alPaIn = some N ∧ UInfoRel N y := by
  obtain ⟨p, args⟩ := e
  cases args with
  | nil => simp [Opt.aliasIn] at he
  | cons a t =>
    cases a with
    | none =>
      simp only [Opt.aliasIn, Option.some.injEq] at he
      subst he
      refine ⟨A 0, ?_, rfl⟩
      unfold alPTC alWS genN
      simp [nock_exec, alPaIn, edgeN, listNoun, unitNoun]
    | some u =>
      simp only [Opt.aliasIn] at he
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 he
      obtain ⟨ip, hip, hu⟩ := Option.bind_eq_some_iff.1 hx
      obtain ⟨V, hV, hVr⟩ := info_got hI hip
      obtain ⟨N, hN, hgN⟩ := infoMap_got hVr hu
      refine ⟨C (A 0) N, ?_, N, rfl, hN⟩
      have hL := optC_layer2
      unfold alPTC alWS genN
      generalize optC = OC at hL
      simp [nock_exec, alPaIn, edgeN, listNoun, unitNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hV, hgN]

/-- **The gate that drops the first argument**: `[p ?>(?=(^ args) t.args)]`. -/
theorem al_patl (e : Nat × List (Option Nat)) (he : e.2 ≠ []) (X : Noun) :
    nock (C alPaTl (C (edgeN e) X)) alPaTl = some (edgeN (e.1, e.2.tail)) := by
  obtain ⟨p, args⟩ := e
  cases args with
  | nil => exact absurd rfl he
  | cons a t => simp [nock_exec, alPaTl, edgeN, listNoun]

theorem aliasIn_args {g : Opt.AGen (TreapMap mugF)} :
    ∀ {edges : List (Nat × List (Option Nat))} {ins : List (Option Opt.InfoReg)},
      edges.mapM (Opt.aliasIn g) = some ins → ∀ e ∈ edges, e.2 ≠ []
  | [], _, _, e, he => by simp at he
  | (p, args) :: t, ins, h, e, he => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    cases ea : Opt.aliasIn g (p, args) with
    | none => rw [ea] at h; cases h
    | some y =>
      rw [ea] at h
      cases et : t.mapM (Opt.aliasIn g) with
      | none => rw [et] at h; simp at h
      | some r =>
        rcases List.mem_cons.1 he with rfl | he
        · intro h0
          simp only at h0
          subst h0
          simp [Opt.aliasIn] at ea
        · exact aliasIn_args et e he

/-- The arm `param-info` of the battery. -/
def alPIArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alPInfoB) (C (A 0) (A 1))))

theorem alBat_pi : ∃ a1 a2 a3 a4, alBat = C a1 (C a2 (C a3 (C a4 (C alPIArm alWalk)))) :=
  ⟨_, _, _, _, rfl⟩

/-- **The parameter trap** is the model's `aliasPars`: on `ps` (the rest of
`par.bob`), the edges `edges`, `out` the noun of `outl` and `info-local`
related to `loc`, it gives `[(flop out) gen]` with `out` grown by `ps`, and
`info-local` related to the model's result. -/
theorem al_part (g : Opt.AGen (TreapMap mugF)) {INFO : Noun} (hI : InfoStoreRel INFO g.info)
    (NEW OLD IMMSg IMML RV F NA BL REV TOPO BR IMMS INF PRE : Noun) :
    ∀ (ps : List Nat) (edges : List (Nat × List (Option Nat))) (loc loc' : Opt.AInfo) (LOC : Noun)
      (outl : List Nat), InfoMapRel LOC loc → Opt.aliasPars g ps edges loc = some loc' →
      ∃ LOC', InfoMapRel LOC' loc' ∧
        nock (alPTC (listNoun A outl) (listNoun edgeN edges) (listNoun A ps) BR IMMS INF PRE
          (genN NEW OLD INFO IMMSg LOC IMML RV F) NA BL REV TOPO) alParTC
          = some (C (listNoun A (outl.reverse ++ ps)) (genN NEW OLD INFO IMMSg LOC' IMML RV F)) := by
  intro ps
  induction ps with
  | nil =>
    intro edges loc loc' LOC outl hL h
    simp only [Opt.aliasPars, Option.some.injEq] at h
    subst h
    refine ⟨LOC, hL, ?_⟩
    have hf := flop_gate layer2 homoIn_layer2 (outl.map A)
    rw [← List.map_reverse, ← listNoun_map_listN, ← listNoun_map_listN] at hf
    have hL2 := optC_layer2
    unfold alPTC alWS genN
    generalize optC = OC at hL2
    nock_open alParTC
    simp [nock_exec, listNoun, hL2, flop.arm_at, flop_arm, hf]
  | cons x ps ih =>
    intro edges loc loc' LOC outl hLOC h
    simp only [Opt.aliasPars] at h
    obtain ⟨ins, hins, h⟩ := Option.bind_eq_some_iff.1 h
    -- the gate of `ins`
    obtain ⟨L, hLr, hLs, hturn⟩ := turn_gate_rel edgeN UInfoRel (Opt.aliasIn g) layer2 homoIn_layer2 alPaIn
      (C (A 0) (A 0)) (C (A x) (alPTC (listNoun A outl) (listNoun edgeN edges) (C (A x) (listNoun A ps)) BR IMMS
        INF PRE (genN NEW OLD INFO IMMSg LOC IMML RV F) NA BL REV TOPO)) edges ins hins
      (fun e _ y he => al_pain g hI e y he _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    -- `param-info`
    obtain ⟨N, hN, hNr⟩ := al_pinfo (genN NEW OLD INFO IMMSg LOC IMML RV F) alBodyCut (C NA (C BL (C REV TOPO))) L hLr
    rw [hLs] at hNr
    -- `+put:by`
    obtain ⟨LOC1, hput, hLOC1⟩ := infoMapRel_put hLOC hNr x
    -- the tails of the edges
    have hargs := aliasIn_args hins
    have htl : ∀ X, nock (C turn.battery (C (C (listN (edges.map edgeN)) (C alPaTl (C (C (A 0) (A 0)) X))) layer2))
        turn.battery = some (listN ((edges.map fun e => (e.1, e.2.tail)).map edgeN)) := fun X =>
      turn_gate_some edgeN edgeN layer2 homoIn_layer2 alPaTl (C (A 0) (A 0)) X (fun e => (e.1, e.2.tail)) edges
        (fun e he => al_patl e (hargs e he) _)
    obtain ⟨LOC', hLOC', hrec⟩ := ih (edges.map fun e => (e.1, e.2.tail)) _ loc' LOC1 (x :: outl) hLOC1 h
    refine ⟨LOC', hLOC', ?_⟩
    have e1 : outl.reverse ++ x :: ps = (x :: outl).reverse ++ ps := by simp
    rw [e1, ← hrec]
    simp only [← listNoun_map_listN] at hturn hN htl
    obtain ⟨a1, a2, a3, a4, hX⟩ := alBat_pi
    unfold alPIArm at hX
    have hL2 := optC_layer2
    unfold alPIS alCtx at hN
    simp only [listNoun]
    unfold alPTC alWS at hturn ⊢
    unfold genN at hturn hN ⊢
    rw [hX] at hturn hN ⊢
    generalize optC = OC at hL2 hturn hN ⊢
    nock_open alParTC
    simp [nock_exec, hL2, eqCode, turn.arm_at, turn_arm, hturn, by.arm_at, by_arm, by.put.arm_at, put_arm, hput,
      hN, htl]

/-! ## Phase 12 -/

/-- `GenRelL` moves along `AInfoEq` of the facts of `info-local`. -/
theorem GenRelL.of_aInfoEq {g : Opt.AGen (TreapMap mugF)} {loc loc' : Opt.AInfo} {imml : Opt.AImms} {N : Noun}
    (h : GenRelL g loc imml N) (e : Opt.AInfoEq loc loc') : GenRelL g loc' imml N := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, REV, hN, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨OLD, INFO, IMMS, LOC, IMML, REV, hN, h1, h2, h3, h4, infoMapRel_of_aInfoEq h5 e, h6⟩

/-- **Phase 12 on the Hoon's `pre`**: on a `gen` related to `g` with facts
`loc`, `alPars` returns `[par.bob gen']`, `gen'` related to `g` with the facts
of `aliasPars` on the edges of `aliasEdges g o pre`. -/
theorem al_pars_perm {g : Opt.AGen (TreapMap mugF)} {loc : Opt.AInfo} {imml : Opt.AImms} {GEN : Noun}
    (hg : GenRelL g loc imml GEN) (hn : Opt.NoLti g.new) (IMMS INF NA BL REV T : Noun) (o : Nat)
    (pre : List Nat) (b : Blob) (edges : List (Nat × List (Option Nat))) (loc' : Opt.AInfo)
    (he : Opt.aliasEdges g o pre = some edges) (hp : Opt.aliasPars g b.par edges loc = some loc') :
    ∃ GEN', GenRelL g loc' imml GEN' ∧
      nock (C b.toNoun (C IMMS (C INF (C (listNoun A pre) (alWS GEN NA BL REV (C (A o) T)))))) alPars
        = some (C (listNoun A b.par) GEN') := by
  obtain ⟨OLD, INFO, IMMSg, LOC, IMML, R, rfl, hO, hI, hM, hR, hLOC, hIML⟩ := hg
  have hE := al_edges g hn o pre (Blob.toNoun b) IMMS INF OLD INFO IMMSg LOC IMML R (flag g.folded) NA BL REV T
  rw [he, Option.map_some] at hE
  obtain ⟨LOC', hLOC', htrap⟩ := al_part g hI (HoonMap.toNoun Blob.toNoun g.new) OLD IMMSg IMML R (flag g.folded)
    NA BL REV (C (A o) T) (C (listNoun Pole.toNoun b.body) b.fin.toNoun) IMMS INF (listNoun A pre) b.par edges loc
    loc' LOC [] hLOC hp
  refine ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMSg LOC' IMML R (flag g.folded),
    ⟨OLD, INFO, IMMSg, LOC', IMML, R, rfl, hO, hI, hM, hR, hLOC', hIML⟩, ?_⟩
  simp only [List.reverse_nil, List.nil_append, listNoun] at htrap
  rw [show Blob.toNoun b = C (listNoun A b.par) (C (listNoun Pole.toNoun b.body) b.fin.toNoun) from rfl] at hE ⊢
  unfold alPS at hE
  unfold alPTC at htrap
  simp [nock_exec, alPars, alEdges_cut, alParT_cut, hE, htrap]

/-- **Phase 12**: on a `gen` related to `g` with facts `loc` (after phases 9
to 11), with `pre` the Hoon's list (`al_pre`: no duplicates, the members of
`g.rev o`) and `RevNodup g.rev`, `NoLti g.new` of the walk's invariants, where
the model's `aliasEdges g o (g.rev o)` and `aliasPars` return, `alPars`
returns `[par.bob gen']` with `gen'` related to `g` and the model's facts
`loc'`, imms unchanged. -/
theorem al_pars {g : Opt.AGen (TreapMap mugF)} {loc : Opt.AInfo} {imml : Opt.AImms} {GEN : Noun}
    (hg : GenRelL g loc imml GEN) (hr : Opt.RevNodup g.rev) (hn : Opt.NoLti g.new)
    (IMMS INF NA BL REV T : Noun) (o : Nat) (pre : List Nat) (hd : pre.Nodup) (hm : ∀ x, x ∈ pre ↔ x ∈ g.rev o)
    (b : Blob) (edges : List (Nat × List (Option Nat))) (loc' : Opt.AInfo)
    (he : Opt.aliasEdges g o (g.rev o) = some edges) (hp : Opt.aliasPars g b.par edges loc = some loc') :
    ∃ GEN', GenRelL g loc' imml GEN' ∧
      nock (C b.toNoun (C IMMS (C INF (C (listNoun A pre) (alWS GEN NA BL REV (C (A o) T)))))) alPars
        = some (C (listNoun A b.par) GEN') := by
  have hP := al_pre_perm hr hd hm
  have h := Opt.aliasPars_edges_perm g o b.par hP (Opt.aInfoEq_equiv.refl loc)
  rw [he, Option.bind_some, hp] at h
  cases eH : Opt.aliasEdges g o pre with
  | none => rw [eH] at h; simp at h
  | some edgesH =>
    rw [eH, Option.bind_some] at h
    cases eP : Opt.aliasPars g b.par edgesH loc with
    | none => rw [eP] at h; simp at h
    | some locH =>
      rw [eP] at h
      obtain ⟨GEN', hG', hN⟩ := al_pars_perm hg hn IMMS INF NA BL REV T o pre b edgesH locH eH eP
      exact ⟨GEN', hG'.of_aInfoEq h, hN⟩

end Compiler
end Formalization
