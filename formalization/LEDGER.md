# LEDGER: what `Full` rests on (track G, 2026-11-27)

`Full` (`core/Statement.lean`) is proved by `Assembly.full_of` from one
structure, `Assembly.Gap lib pk InvC`, with eight fields.  This file traces
each field down to its OPEN LEAVES.  Every declaration named here is checked
to exist in `lemmas/Glue/AuditGlue.lean` (`#check`), and the theorems of
`lemmas/Glue/` have their axioms printed there (all three:
`propext`, `Classical.choice`, `Quot.sound`).  A line that could not be
verified is marked *not checked*.

Words: PROVED (a theorem, name and file, with its class of inputs), OPEN (no
theorem; stated as a `def … : Prop` where one exists), *composition only*
(follows from proved pieces and a definitional choice, but no theorem is
written yet).

## 0. The one route that exists, and the parameters it fixes

`full_of` uses, besides the eight fields, only proved facts: `cueRoot`
(`Assembly.lean`), `ovumMold`, `pokeValid`, `listMoldIs`, `pokeDireBad`,
`mookOtherTwo_of`, `rendBaseIs_layer4`, `pokeFrame_corIn`, `pokeIs_of_frame`.

The fields `contract`, `halting`, `invStart` and `invKept` are about a model
`pk : Noun → Ovum → Option (Prod × Noun)` on NOUNS.  The only theorems that
produce them are `PokeM.gap_of_comp` (`Ska/PokeAna.lean`) and
`PokeM.fullAnswers_lift` (`Ska/PokeModel.lean`), and they fix

- `pk := liftPoke enc (pokeS A)` and `InvC := liftInv enc (InvS lib ref)`,
  for an injective `enc : CSt M Map J H CR → Noun` (no `enc` is defined
  anywhere: OPEN, no owner);
- `A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf` (a
  definitional choice of `A`; it moves the work to `pokeModel`);
- `ref : Ref M Map J H`, the reference compiler, a free parameter that
  `CompHyp` ties to `A` and to the models.

So `pokeModel` must be proved for that same `pk`: the pill's `+poke` must
compute `liftPoke enc (pokeS A)` on every core of `PokeReach`.

## 1. `pokeModel : PokeModel pk`

Statement: on every compiler core `cr` with `CorIn cr` (layers 2 and 4 in
place, `PokeReach cr`), and every ovum but a hot `%jets`, the pill's inner
`+poke` (`pokeN`) returns `(pk cr ov).map fun r => C r.1.toNoun r.2`.

PROVED around it: the frame of `+poke` on every `CorIn` core
(`pokeFrame_corIn`, `pokeIs_of_frame`, `Compiler/PokeFrame.lean`); that it
validates first (`pokeN_validates`, `Compiler/Validate.lean`); `%dire` on a
bad bell (`pokeDireBad`).

With `pk := liftPoke enc (pokeS A)`, the leaves:

1.1 OPEN, no owner: `enc`, with `cor` and every `PokeReach` core in its
    image (the pill must never return a core that encodes no state).
1.2 OPEN, no owner: `+ska-poke` of the pill is `anaArm …` on the decoded
    state.  PROVED pieces (README Gaps 9): `ska_poke_iff`
    (`Compiler/RoadPure.lean`: the gate as a trap), `ska_poke_ana_iff_pill`,
    `analyze_iff`, `fol_loop_iff`, `resolve_iff` (both directions against
    the fuelled models, given `AnaIs`, `RegisterFastIs`).  No file of
    `lemmas/Compiler/` mentions `anaArm` (grep), so the composition is not
    written.
1.3 OPEN, tracks A, I, K: `A.compileUnary` is the pill's `+compile-unary`.
    PROVED: `cu_gate_scc_one_six_ts` and `cu_gate_scc_one_six_fol_ts`
    (`Compiler/CompStraightMapSix.lean`) for a ONE-bell SCC with
    `NoSelfCall`, `SixOk nm`, `FinSure env nm`, `NoBakeOneC`, `Bake.NoAx0`
    (or `FolMade`), output `finishLFC … (sccSur p.1 cape) cape (fun n => (n, []))`
    and `finishLUC env n`; `cu_gate_six_ts` given the noun that
    `+compile-scc-in` returns (`hcsi`).  Direct calls at `mono &`:
    `comp_run_dir`, `res_dir` (`Compiler/CompRunRClass.lean`, class `DirOk`:
    `%6` and direct calls anywhere; outside: memo key, ring, `%11`, `%12`),
    not yet a `cu_gate` (Gaps 19 items (a) to (g)).
1.4 OPEN, track I: `A.compileScc` is the pill's `+compile-scc`.  The loop is
    modelled (`SccLoop.lean`: `loop_end`, `final_member`, `final_keeps`
    under `Hyp`); the pill link of `csiFix` (956 of 2,488 cells) is not
    started.
1.5 PROVED on `FragX`, track H: `A.optimize` is the pill's `+optimize` on the
    raw code: `optimize_total_finishLUX`, `optimize_total_finishLFX`
    (`Compiler/OptLinkTotalAvail.lean`: some fuels, some `s'`, the pill
    returns `s'.toNoun`), `opt_gate` (`Compiler/OptLinkOpt.lean`) on any
    straight given `AliasLink`, `TrimLink`, `SwitchLink`.  OPEN outside
    `FragX` (input side, track D).
1.6 OPEN, no owner: `+scc-of`, the jetted-root branch of `%full`
    (`A.jetRoot`), the `%jets` and `%fast` branches (`A.jetsPoke`,
    `A.fastPoke`), `+compiled-mono` / `+compiled-nary` and the `%dire`
    branch as the pill runs them (modelled arm by arm in `PokeModel.lean`,
    link *not checked*).

## 2. `contract : Sound lib pk InvC`

Chain: `Gap.contract` = `(gap_of_comp A hC hA enc henc).1`; `hC : CompHyp A lib ref`.
`CompHyp` comes from

- `compHyp_of_pieces` (`Ska/CompHypOf.lean`, 2026-11-24) from `CompPieces`, or
- NEW `Glue.compHyp_of_piecesO` (`lemmas/Glue/RawOptIn.lean`) from
  `CompPiecesO`: `CompPieces` with `rawDInv` (`DInvS`) replaced by
  `RawOptIn` (track D's `OptIn`) and `optEq`, `optAlias`, `optSSA` replaced
  by `OptRef` (on reference forms, `A.optimize` is `optimizeF` with the
  pill's passes `aliasM (pickR M')`, `trimTraceHints`, `switchChains sfuel`
  at fuels chosen per form).  `Glue.keeps_of_optIn` gives `Opt.Keeps` from
  them by `optimize_keeps_optIn`.  Both theorems end in `CompHyp`, so the
  new route plugs into `gap_of_comp` unchanged.
- NEW `Glue.compHyp_of_fragX`: `CompHyp` from `CompRestO` alone when every
  compiled nomm is in `FragXM` (`FragX`, at most 255 `%6`) and every n-ary
  one in `FragXN` (the same, nothing baked).  `RawOptIn`
  (`Glue.rawOptIn_fragX`, from `optIn_finishLUX`, `optIn_finishLFX`),
  `rawMono` (`Glue.rawMono_fragX`, from `rawMono_fragU`) and `rawNary`
  (`Glue.rawNary_fragX`, from `rawNary_fragU`) are discharged.
- NEW `Glue.optRef_fragX`: `OptRef FinMap A lib ref` on `FragX` from track
  H's totality, given `hpill` (`A.optimize` is what the pill's `+optimize`
  returns on each reference form, a part of 1.5) and `hinj`
  (`Straight.toNoun` is injective on `TreapMap mugF`: OPEN, no owner, small).

The fields of `CompRestO` / `CompPiecesO` (the same as `CompRest`'s where
the name is the same):

2.a `refMono`, `refNary` (the reference compiler is `finishLUC` /
    `finishLFC` on the code table's nomm / the nomm of `+inlined`): OPEN.
    With `ref :=` the pill's compiler these are the pill link of 1.3 and 1.4
    read as functions; see mismatch M3 (direct calls are `finishLUCM`).
2.b `rawMono : RawMono S Map lib FM`, PROVED on:
    `FragUM` (`rawMono_fragU`: call-free `FragU`, `%6`, at most 255 `%6`),
    `FragXM` (`Glue.rawMono_fragX`, inside `FragUM`),
    `FragUFG` (`rawMono_fragUFG`, `CompHypOfFragF.lean`: indirect calls in
    parts of calls, `[7 p q]` with calls; contains `FragUEG`, `FragUDG`,
    `FragUCG`), `NCG` (`rawMono_NCG`, `CompHypOfNC.lean`: the class `NC` at
    level 0, contains `FragUFG`).  Direct calls: `finishLUCM_bellContractCallTreeD`,
    `finishLUCM_contractTailP` are about `finishLUCM`, not `finishLUC`
    (M3), and `CallTreeD` depends on `env` and `N` (M3).
    `rawNary : RawNary S Map lib FN`, PROVED only on `FragUN`
    (`rawNary_fragU`: call-free `FragU`, nothing baked) and `FragXN`.
    `finishLF_bellContractX` (`CompFragX.lean`) is the same class.
2.b' `inFragM`, `inFragN` (every compiled nomm is in the class): OPEN; FALSE
    for the classes proved so far on real code (direct calls, `%11` hints:
    `NC` has no `%11` constructor (grep of `CompNC.lean`), baked n-ary
    code).  Owners: C (`%6` with calls, `CallTree6`), J (n-ary with
    calls), K (class `DirOk`), D (raw invariants with calls).
2.c `RawOptIn`: PROVED on `FragX` (`Glue.rawOptIn_fragX`).  With indirect
    calls (class `PlainN`, no `%6`): checked on 3,960 nomms
    (`RawInvCheckCX.lean`), `runATC_plain` (`Ska/RawInvCAT.lean`) proves
    `Closed`, `ArityOK`, `TwoNA` only; `OptIn` OPEN, track D.
    `rawEntry` (`Opt.EntryOK` of every entry of the raw code on a fitting
    subject): OPEN, no owner (no theorem concludes `EntryOK`; grep finds it
    only as a hypothesis, `alias_args`).
2.d `optRef : OptRef M' A lib ref`: PROVED on `FragX` from `hpill`, `hinj`
    (`Glue.optRef_fragX`); OPEN outside.
2.e `inlAnnot` (the nomm of `+inlined` stands for the bell's formula,
    `Annot`): OPEN, no owner (`+inlined` is not modelled).
2.g `callee : CalleeNeeds (D.env …) (refN A ref …)`: OPEN, track I.  Within
    an SCC it is the fixed point of `+compile-scc-in`; `final_member`,
    `final_keeps` (`Ska/SccLoop.lean`) prove (b), (c) of Gaps 18.12 under
    `Hyp` (`kidsOnly`, `shape` = the DISABLED `shape-check` assert,
    `msgSelf`, `msgAbs` unproved).  Hot-jet callees: untested (field doc).
2.h `unary`, `scc` (the compile gives the reference forms and keeps
    `CacheOK`): OPEN, tracks A, I (with 1.3, 1.4).  `answers` (the compiler
    returns on every bell the reference answers): OPEN, no owner; needs the
    sweep loop of `+compile-scc-in` to end (track I: no measure, always 3
    sweeps on 23 SCCs) and `+optimize` to return (1.5).  `stable` (what is
    compiled survives `+ska-poke`): OPEN, no owner.  `jetRoot`, `jets`,
    `fast`: OPEN, no owner.

## 3. `halting : FullAnswers pk InvC`

Chain: `fullAnswers_lift henc` of `FullAnswers (pokeS A) (InvS lib ref)`,
which `fullAnswers_of_loops` (`Ska/PokeHalt.lean`) gives from `hC`, `hA`,
`AnaEnds`, `BakeEnds`, `RootAnswers` (`FinalEnds` PROVED:
`finalEnds_always`).  NEW `Glue.fullAnswers_of_cg`: the same with
`AnaEnds` replaced by `CgHalts` and `∀ L, InvB lib L → MemoNoCallees L.memo`,
for the analysis fuel `anaFuel env regOf` (`anaEnds_of_N`,
`anaEndsN_of_halts`, `anaHalts_of_cgHalts`).

3.1 `CgHalts lib env regOf` (`Ska/AnaEnds.lean`: `+ska-callgraph` returns at
    some fuel): OPEN, track F.  `passLoop_returns_fin` (`PassMeasureB.lean`)
    reduces the pass loop to `FinPushes`, OPEN; the old bound is false
    (re-pushes, `tools/hoon/repush.hoon`); `passOn_old` (`PassStab.lean`)
    proved; candidate measures A and D fail on traces.
3.2 `MemoNoCallees` under `InvB`: *composition only* once it is a field of
    the invariant (M8): kept by `memoNoCallees_skaPoke`, true of the empty
    memo (`memoNoCallees_empty`).
3.3 `BakeEnds` (the worklist of `+bake-graph` ends within `bf`): OPEN, no
    owner.  PROVED around it: `bakeLoop_mono` (more fuel is harmless),
    `bakeLoop_grows`; no measure.
3.4 `RootAnswers` (the reference compiler gives the root bell a form):
    OPEN, no owner; the same totality as 2.h `answers`.
3.5 `hC : CompHyp`: as in section 2.

## 4. `invStart : InvC cor`

Chain: `(gap_of_comp …).2.2` gives `liftInv enc (InvS lib ref)` of
`enc ⟨⟨∅, ∅, ∅⟩, jets, hot, ⟨∅, ∅, ∅, rest⟩⟩` for every `jets hot rest`
(`invS_init`, inside `gap_of`; the component does not use `hC`, but
`gap_of_comp` takes it).
Leaf 4.1, OPEN, no owner: `cor = enc ⟨⟨∅, ∅, ∅⟩, jets, hot, ⟨∅, ∅, ∅, rest⟩⟩`
for some `jets hot rest`, i.e. the pill's compiler starts with an empty
code table, memo, variants and caches (*not checked* on the pill).

## 5. `invKept : InvKept pk InvC`

Chain: `(gap_of_comp …).2.1`, the same hypotheses as section 2 (`CompHyp`,
`hA`, `enc` injective); nothing else.

## 6. `libSlam : SlamIsNock lib`

*Composition only*: holds by `rfl` for any `lib` whose `slam` is
`slamGate nock` (`Compiler/Mink.lean`).  The other fields of `lib` stay free
(the compile-side theorems quantify over every `lib`).

## 7. `libFormat`

`RendLeafIs lib ∧ HandIs lib mugF layer4 ∧ RendRestIs lib layer4 ∧ SoftTankIs lib layer4 ∧ SkipMsgIs lib layer4`
(`Compiler/Mook.lean`).
7.1 `RendLeafIs`, `HandIs`: *composition only* by the choice of
    `lib.rendBase` (`rendLeaf` on its tags, the pill's `+scow %p` on
    `%hand`; `rendLeaf Tag.hand _ = none`, so the two do not clash).  No
    theorem written.
7.2 `RendRestIs` (`+smyt` through `(soft path)`, `(soft spot)`, for EVERY
    `ton`), `SoftTankIs` (`(soft tank)` returns a unit on every noun),
    `SkipMsgIs` (the cord of `+skip`, for every `ton`): OPEN, no owner
    (README Gaps 7: `+scow`, `+smyt`, `+crip`, `+soft` not proved).  They
    are not choices: each needs the pill's gate to RETURN and not to depend
    on `ton`.

## 8. `mookFormat : EvalMookMsgIs lib`

OPEN, no owner: the cord of `+eval-mook` on every `CorIn` core is
`lib.skipMsg (yel - 1024)`, the same value `SkipMsgIs` asks at layer 4
(`+scow %ud`, `+crip`).

## 9. MISMATCHES

M1. `DInvS` (old `rawDInv`) vs `OptIn` / `DInvR` (track D).  Old route:
    `CompRest.keeps` uses `optimize_keeps_ssaR` with `optAlias :
    DriverRestSSA` at `DInvS`.  The header of `Ska/OptAliasOnce.lean` says
    `AliasOnceB` is false (`not_aliasOnceB`) and the driver's conclusion
    fails on blocks with `DInvS` (`w_opt`), "so no field closes it" (I did
    not re-derive that `DriverRestSSA` with the pill's `aliasM` is false:
    *not checked*).  RECONCILED: `Glue.CompPiecesO` (`RawOptIn`, `OptRef`)
    with `optimize_keeps_optIn`; nothing in the new route mentions `DInvS`.
M2. `optEq : ∀ s, optimizeF (D.optFuel s) D.optP s = some (A.optimize s)`
    asks the model on EVERY straight with ONE `sfuel` (`D.sfuel` in
    `optAlias`), while the totality theorems give fuels per raw straight of
    `FragX` (`∃ sfuel fuel s'`).  RECONCILED by `OptRef` (reference forms
    only, fuels per form) and `Glue.optRef_fragX`, up to `hinj`
    (`Straight.toNoun` injective: OPEN, no owner).
M3. `runLC` vs `runLCM env true`.  `refMono` says the whole-subject
    reference is `finishLUC` (`runLC`); the Hoon at `mono &` compiles a
    direct call as `finishLUCM` (`runLCM env true`).  They agree on
    `noDirect` nomms (`finishLUCM_eq`, `runLCM_eq`); `FragX` is `noDirect`
    (`noDirect_of_fragX`); for `NCG`, `FragUFG`: *not checked*.  Tracks J
    and K prove direct calls against `finishLUCM` / `runLCM env true`
    (`finishLUCM_bellContractCallTreeD`, `comp_run_dir`), and `CallTreeD lib
    env N P x f nm` depends on `env` and `N`, which `RawMono`'s class
    `FM : Nomm → Prop` cannot see.  TO RECONCILE: restate `refMono` with
    `finishLUCM` (the bridge to the present classes is `finishLUCM_eq` once
    each is shown `noDirect`), and give `RawMono` a class
    `FM : CallEnv → Needs → Bell → Nomm → Prop`.  DONE of the first half:
    `Glue.RawMonoM` (`RawMono` against `finishLUCM`), `Glue.rawMonoM_of`
    (from `RawMono` on any class of `noDirect` nomms), `Glue.rawMonoM_fragX`.
    Left: `refMono` with `finishLUCM` (a `CompRestO` variant) and the class
    with `env`, `N`.  No owner (glue, next step of this track).
M4. `sccSur` vs `shapeCol`.  The pill link (`cu_gate_scc_one_six_ts`) puts
    `ord = sccSur p.1 cape` under `FinSure env nm`; `FinSure` is FALSE when
    a `%6` result reaches the top, and `sccSur` differs from the Hoon's
    `ord` on 32 of 34 forked cases (track A, `shapeCol_sccSur`,
    `shapeCol_finSure`).  `CompRest.refNary` takes `D.ord` as a parameter
    and `RawNary` holds for every `ord`, so the model side needs nothing;
    the pill link must output `shapeCol` and link `+coerce-lazy` over forks
    and bonds (track A).
M5. Baking.  `RawNary` is proved only with nothing baked (`FragUN`,
    `FragXN`: `∀ ned, bake ned = (ned, [])`), the pill link only under
    `NoBakeOneC`.  The compiler bakes (`+bake-need` of `less.b`, not
    modelled).  Class too small; no owner.
M6. `NoSelfCall` and one-bell SCCs.  The `cu_gate` tops are for one bell
    with no self call; recursion needs `csiFix` (track I, not started) and
    `Hyp` of `SccLoop.lean`.
M7. `callee` and `shape`.  `final_member` / `final_keeps` assume `shape`,
    which is the `shape-check` assert that the Hoon has switched OFF, so the
    Hoon does not establish it; `msgAbs` unproved; no termination measure
    for the sweep loop (track I).
M8. `MemoNoCallees` is not a field of `InvB` / `InvS`, but `CgHalts` and
    `AnaHalts` assume it and `AnaEnds` quantifies over every `InvB` state.
    TO RECONCILE: add it to `InvS` (kept: `memoNoCallees_skaPoke`; start:
    `memoNoCallees_empty`); owner of `PokeModel.lean` / `PokeBake.lean`
    (none running).
M9. Fuel.  `fullAnswers_of_cg` needs `hA` at the fuel `anaFuel env regOf`
    (a `Classical.choose`); `pokeModel` must then link the pill's
    `+ska-poke` (no fuel) to `anaArm` at that fuel: fine where the fuelled
    models are monotone (`skaPoke_fuel_le`), *not checked* as a theorem.
M10. `FinPushes` vs the old bound `B`: the bound is false on the real
    compiler (track F), `FinPushes` open.  Not a wrong statement any more.
M11. `pokeModel` over `liftPoke`: needs every `PokeReach` core to encode a
    state (1.1) and `cor` to be the empty state (4.1); no `enc` exists.

## 10. OPEN LEAVES, in order of what blocks the most

1. `refMono` / `refNary` / `unary` / `scc` with the pill link of
   `+compile-unary` and `+compile-scc` (1.3, 1.4, 2.a, 2.h): pill link of
   `csiFix` (956 of 2,488 cells) plus `cu_gate` for `DirOk` (Gaps 19 (a)-(g))
   plus dropping `FinSure` (shape-collapse link).  Tracks A, I, K.
2. The class: `inFragM` / `inFragN` (2.b'): every compiled nomm in a class
   with a raw contract, `RawOptIn` and `OptRef`; today the classes with all
   three are `FragX` only (call-free); the contract alone reaches `NCG`.
   Tracks C, D, J, K; needs M3 first for direct calls.
3. `CgHalts` (3.1): needs a measure nobody has (`FinPushes`).  Track F.
4. `pokeModel` as a whole (1.1, 1.2, 1.6, 4.1, M11): `enc`, the analysis
   link to `anaArm`, `+scc-of`, `%jets`, `%fast`, jetted root, `%dire`
   branch: composition of existing links plus unlinked arms, size not
   measured.  No owner.
5. `answers` / `RootAnswers` (2.h, 3.4): totality of the compile: sweep loop
   of `+compile-scc-in` (no measure, track I) and `+optimize` outside
   `FragX` (track D's input side).
6. `BakeEnds` (3.3): needs a measure nobody has.  No owner.
7. `rawEntry` (2.c): no statement of how to prove it; no owner.
8. `callee` (2.g): `msgAbs`, `shape` (disabled assert).  Track I.
9. `inlAnnot` (2.e): `+inlined` not modelled.  No owner.
10. `stable`, `jetRoot`, `jets`, `fast` (2.h): no owner.
11. Formatting (7.2, 8): `RendRestIs`, `SoftTankIs`, `SkipMsgIs`,
    `EvalMookMsgIs`: pill links of `+scow`, `+smyt`, `+crip`, `+soft`.  No owner.
12. Small: `hinj` (`Straight.toNoun` injective), M8 (`MemoNoCallees` in the
    invariant), 6 and 7.1 (the choice of `lib`): composition only.

Leaves with NO owner: 1.1 `enc`, 1.2 analysis-to-`anaArm`, 1.6, 2.c
`rawEntry`, 2.e `inlAnnot`, 2.h `answers` / `stable` / `jetRoot` / `jets` /
`fast`, 3.3 `BakeEnds`, 3.4 `RootAnswers`, 4.1 `cor` empty, 7.2, 8, M3
restatement, M5 baked n-ary, M8, `hinj`.
