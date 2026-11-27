# LEDGER: what `Full` rests on (track G, 2026-11-27, second pass)

`Full` (`core/Statement.lean`) is proved by `Assembly.full_of` from one
structure, `Assembly.Gap lib pk InvC`, with eight fields.  This file traces
each field down to its OPEN LEAVES.  Every declaration named here is checked
to exist in `lemmas/Glue/AuditGlue.lean` or, for track P's route,
`lemmas/Glue/AuditGlueP.lean` (`#check`), and the theorems of
`lemmas/Glue/` have their axioms printed there (all within `propext`,
`Classical.choice`, `Quot.sound`).  A line that could not be verified is
marked *not checked*; names on a track branch that is not merged are marked
*(branch -x, not merged)*.

Words: PROVED (a theorem, name and file, with its class of inputs), OPEN (no
theorem; stated as a `def … : Prop` where one exists), *composition only*
(follows from proved pieces and a definitional choice, but no theorem is
written yet), LEAF (a `def … : Prop` of `lemmas/Glue/` that names what is
missing, as a statement about the model or about the pill alone).

Branches: A `-a`, C `-c`, D `-d`, F `-e`, I `-i`, J `-b`, K `-g`, P `-p`,
G (this track) `-h`.

## 0. The routes, and the parameters they fix

`full_of` uses, besides the eight fields, only proved facts: `cueRoot`
(`Assembly.lean`), `ovumMold`, `pokeValid`, `listMoldIs`, `pokeDireBad`,
`mookOtherTwo_of`, `rendBaseIs_layer4`, `pokeFrame_corIn`, `pokeIs_of_frame`.

The fields `contract`, `halting`, `invStart`, `invKept` are about a model
`pk : Noun → Ovum → Option (Prod × Noun)` on NOUNS, from a model `pokeS A` on
states lifted by an injective `enc` (`liftPoke`, `liftInv`, `sound_lift`,
`invKept_lift`, `fullAnswers_lift`).  The theorems that produce the three
shapes:

- `PokeM.gap_of` (`Ska/PokeModel.lean`, from `CompHyp`, `AnaHyp`);
- `PokeM.gap_of_comp` (`Ska/PokeAna.lean`, `A.skaPoke = anaArm …`);
- NEW `Glue.gap_of_compM` (`Glue/InvMemo.lean`): the same on the invariant
  `InvSM` (section 4, M8), so that `halting` and the other three use ONE
  invariant;
- track P's `Compiler.gap_of_armP` (`Compiler/PokeLink.lean`) with
  `anaArmP` (`+ska-cole-update`, mismatch P2; no answer on an atom formula,
  P4) for `enc fl`, `invStart` at the pill's `cor`: THE ROUTE NOW
  (`gap_of_comp` does not apply to `anaArmP`);
- NEW `Glue.gap_of_armPM` (`Glue/InvMemoP.lean`): `gap_of_armP` on `InvSM`,
  with `Glue.halting_of_cgMP` for `halting` on the same invariant.

They fix `pk := liftPoke enc (pokeS A)`, `InvC := liftInv enc (InvS lib ref)`
(or `InvSM`), `A.skaPoke` the analysis arm, and `ref : Ref M Map J H` (the
reference compiler, free, tied to `A` by `CompHyp`).  Track P defines `enc
fl` (`Ska/PokeEnc.lean`: the state as the compiler's core, the flags of
`code` a parameter `fl`, mismatch P1), `enc_inj`, `cor_enc fl : cor = enc fl
emptySt`, `cor_enc_gap`.

BUILD CLASHES (found while auditing; no file can import both of a pair):
`Ska/PokeEnc.lean` and `Compiler/OptLinkAlJReg.lean` both declare
`Compiler.unitNoun_id_inj`; `Ska/SccLoopMsg.lean` and `Ska/CompNCJump.lean`
both declare `Comp.isLeaf`.  So the names of P's route are checked in
`Glue/AuditGlueP.lean`, and `Glue/MonoCalls.lean` (which needs
`OptLinkTotalAvail`) keeps its own `straight_toNoun_inj`.  Fix: rename one
of each pair (owners P, H; I, C).

## 1. `pokeModel : PokeModel pk`

Statement: on every compiler core `cr` with `CorIn cr`, and every ovum but a
hot `%jets`, the pill's inner `+poke` (`pokeN`) returns
`(pk cr ov).map fun r => C r.1.toNoun r.2`.  OWNER: track P (since
2026-11-27).

PROVED around it: the frame of `+poke` on every `CorIn` core
(`pokeFrame_corIn`, `pokeIs_of_frame`); validation first (`pokeN_validates`);
`%dire` on a bad bell (`pokeDireBad`).

Leaves (all track P now):
1.1 `enc`: PROVED (`enc`, `enc_inj`, `Compiler.straight_toNoun_inj`; the map
    of `cr`'s axes against `CSt`, README Gaps 23).  Left: every `PokeReach`
    core is in the image (maps are `IsMap mugF`, keys and values decode,
    `code`/`calls`/`seek` share keys, the flags are `fl` of the table: P1).
1.2 `+ska-poke` is `anaArmP` (P2): `pokeN_full_of` (`Compiler/PokeLink.lean`)
    gives `pokeModel` on `%full` with a cell formula from `FullBranchIs`
    (OPEN: `+validate-ovum` on `%full`, the dispatch, the 272-cell branch)
    and five named links `SkaLink`, `JetRootLink`, `SccLink`, `MonoLink`,
    `OptLink` (OPEN).  In `SkaLink`: the analysis part is linked
    (`ska_poke_iff`, `ska_poke_ana_iff_pill`, `analyze_iff`, `fol_loop_iff`,
    `resolve_iff`); `spRest`, the baking half (`+bake-graph`, `new-code`,
    the SCC loop with `+eval-finalized`, the writes of `seek` and `calls`,
    `+ska-cole-update`), has NO link.
1.3 `A.compileUnary` is the pill's `+compile-unary` (299 cells): tracks A,
    I, K.  PROVED: `cu_gate_scc_one_six_ts`, `cu_gate_scc_one_six_fol_ts`
    (one bell, `NoSelfCall`, `SixOk`, `FinSure`, `NoBakeOneC`);
    `cu_gate_scc_one_six_fix` (the same with the `ord` of `+shape-collapse`
    and `FixRet` in place of `FinSure`, track A); with direct
    calls `cu_gate_dir_csi` → `cu_gate_dir_arms` (`Compiler/CompSofPush.lean`,
    class `DirOk`, named hypotheses `CsiNeeds`, `CsiSures` on the product of
    `+compile-scc-in`), `cu_gate_dir_this` (every callee's need `%this` or
    `%none`).  Open: (f) on cell needs (`+sound-far` 329 cells, `+need-soft`
    134 cells: track K, models on branch -g), (g) `nary.cache` threading.
    Its output is `finishLUCM` (`runLCM env true`), which now matches
    `RefSideM.refMono` (M3 closed).
1.4 `A.compileScc` is the pill's `+compile-scc` (61 cells) over
    `+compile-scc-in` (2,519 cells on this pill): track I.  The loop is
    modelled (`SccLoop.lean`); the pill link (`csiFix`) not started.
1.5 `A.optimize` is the pill's `+optimize`: PROVED on `FragX` (track H,
    `optimize_total_finishLUX`, `-LFX`, `opt_gate`).  Track P's `OptLink`.
1.6 `+scc-of` (409 cells by P's count, 430 tree cells by
    `tools/gen/nouns.py`), the jetted root (`JetRootLink`), `%jets` (298
    cells of the branch), `%fast` (288), `+compiled-mono` (115),
    `+compiled-nary` (107), `%dire` (122): track P, not linked.

## 2. `contract : Sound lib pk InvC`

Chain: `Gap.contract` = `(gap_of_comp A hC hA enc henc).1` (or
`gap_of_compM`, or P's `gap_of_armP`); `hC : CompHyp A lib ref`.  Routes to
`CompHyp`:

- `compHyp_of_pieces` (`Ska/CompHypOf.lean`): old (M1, M2, M3);
- `Glue.compHyp_of_piecesO` (`Glue/RawOptIn.lean`): `RawOptIn`, `OptRef`
  in place of `DInvS`, `optEq`, `optAlias`, `optSSA`; classes `Nomm → Prop`,
  `refMono` at `finishLUC`;
- NEW `Glue.compHyp_of_piecesM` (`Glue/MonoCalls.lean`): `CompPiecesM` =
  `CompRestM` (over `RefSideM`: `refMono` at `finishLUCM`, the classes
  `FM : MonoClass = CallEnv → Needs → Bell → Nomm → Prop`, `FN : NaryClass`
  also seeing cape and bake, taken at `D.env … b m` and `refN A ref …`) plus
  `RawOptIn`, `RawMonoD`, `RawNaryD`.  The old route is a special case:
  `compRestM_of_O` (a `CompRestO` on a class of `noDirect` nomms is a
  `CompRestM` on the lifted classes).
- NEW `Glue.compHyp_of_calls`: `CompHyp` from `CompRestM` on the classes
  with calls `MonoCalls`, `NaryCalls` and the two LEAVES `OptInMono`,
  `OptInNary`.

THE CLASSES WITH CALLS (`Glue/MonoCalls.lean`):
- `MonoCalls S lib` = `NCG` (hence `FragUFG`, `FragU`) ∪ `CallTreeDB`
  (track J's `CallTreeD`: direct calls, `QDirect` formula part, at the
  bell's subjects) ∪ `CallTreeAB` (track C) ∪ `TopTreeB` (track C) ∪
  `Six0B` (track C's `Six0`: `%6` with calling tests and nested branches).
  `rawMonoD_calls : RawMonoD S Map lib (MonoCalls S lib)` PROVED.
- `NaryCalls S lib` = `FragUN` ∪ `CallTreeAN` (track J's `CallTreeA` top) ∪
  `CallTreeDNB` (track J's `CallTreeDN`, the `%cal` and `%jmp` direct
  calls), nothing baked.  `rawNaryD_calls` PROVED.
- `noDirect_NCG`, `noDirect_fragUFG`, `six0_noDirect` PROVED (M3's "not
  checked" closed: `NC.noDirect`, `fragUFG_subNC`).

WHICH FIELDS OF `CompPiecesM` ARE DISCHARGED on `MonoCalls` / `NaryCalls`:

| field | status | leaf / theorem | owner |
|---|---|---|---|
| `rawMono`, `rawNary` | PROVED | `rawMonoD_calls`, `rawNaryD_calls` | done |
| `rawOptIn` | LEAF | `OptInMono S Map FM`, `OptInNary S Map FN` (`rawOptIn_of`); PROVED on `FragX` (`optInMono_fragX`, `optInNary_fragX`) | D |
| `optRef` | LEAF | `OptTotalMono S FM`, `OptTotalNary S FN` + `hpill` (`optRef_of_total`); PROVED on `FragX` (`optTotalMono_fragX`, `optTotalNary_fragX`); `hinj` PROVED (`straight_toNoun_inj`; also track P) | H (input side D), P (`hpill` = `OptLink`) |
| `rawEntry` | LEAF | `EntryMono S Map lib FM`, `EntryNary S Map lib FN` (`rawEntry_of`) | none (2.c) |
| `refMono`, `refNary` | OPEN | pill link at `finishLUCM` / `finishLFC` | A, I, K |
| `inFragM`, `inFragN` | OPEN, FALSE today | every compiled nomm in `MonoCalls` / `NaryCalls` | C, J, K |
| `inlAnnot` | OPEN | 2.e | none |
| `callee` | OPEN | `CalleeNeeds`; J's `NeedsRead`, I's `final_keeps` | I, J |
| `unary`, `scc`, `answers`, `stable`, `jetRoot`, `jets`, `fast` | OPEN | 2.h | A, I, K, P |

2.a `refMono` at `finishLUCM`, `refNary` at `finishLFC` (= `runLCM env
    false`, `finishLFC_eq_M`): the pill link of 1.3, 1.4 read as functions.
2.b The raw contract: PROVED on the classes above.  Earlier names:
    `rawMono_fragU`, `rawMono_fragUFG`, `rawMono_NCG`, `rawNary_fragU`,
    `Glue.rawMonoM_fragX`, `finishLUCM_bellContractCallTreeD`,
    `finishLUCM_bellContractCallTreeA`, `finishLUCM_bellContractTopTree`,
    `finishLUC_contractSix0`, `finishLFC_bellContractCallTreeA`,
    `finishLFC_bellContractCallTreeDN`.  `finishLFC_contractTailN` (the
    n-ary direct call at the top) is inside `CallTreeDN`.  Tables:
    `tableOK_classes`, `closed_entry`, `closed_selfCall`, `closed_selfWalk`,
    `closed_pairWalk` (recursion, self and mutual) under `NeedsRead`.
2.b' `inFragM`, `inFragN`: FALSE on real code for every class so far: no
    class has `%11` (hints), `%12`, `%mean`, memo keys, `%10` at goals with
    entries, or baked n-ary code (M5).  Track C (README Gaps 12.35): `%10`
    only at goals without entries (`LOKSE`, `lokSE_tenR`), `%6` with
    branches as hypotheses for the n-ary top (`finishLFC_contractGBN`), the
    tree of J's `R` (`finishLFC_contractRT`); not yet a class with a bell
    contract usable here.  Owners C, J, K.
2.c `rawEntry` (LEAF `EntryMono`, `EntryNary`; no owner).  WHAT IT STATES:
    on the RAW code `s` of a bell (before `+optimize`), entered with `[x]`
    (mono) or the split of `x` (n-ary) for `x` fitting the bell, for every
    oracle, scry gate, state and trace, `Opt.EntryOK = ReadsOK ∧ ArgsOK ∧
    LocalOK` (`Ska/Opt.lean`): on every path from the entry, every real
    read reads a defined register, every argument a pending pass moves is
    defined, and every `%imm`/`%mov`/`%con`/`%hed`/`%tal` reached with no
    pending parameters executes.  It is what `Opt.Keeps` assumes of an
    entry (`bellContract_of_keeps`); it is NOT implied by the contract (on
    a subject where Nock crashes the code may crash by any read).  CLOSEST:
    track D's `OptIn` (`defFirst`: a read of a register WITH a definition
    comes after one; `defOnce`, `passOK`), `runATC_plain` (`Closed`,
    `ArityOK`, `TwoNA` on `PlainN`), D's liveness with calls (`LiveC`,
    `LiveRun`: what is live at the entry).  A PROOF NEEDS: (i) a generic
    lemma on straights, by induction on `Path.FromEntry`: `OptIn` +
    `Closed` (every register read without a definition is a parameter of
    block `0`) + `ArityOK` (the entry gives `nargs` values) + a `%cel`-guard
    property (every `%hed`/`%tal` of a register follows a `%cel` on it or a
    cons into it) → `EntryOK`; (ii) the four static properties of the raw
    code of each class (D has `OptIn` on `FragX`, `Closed`, `ArityOK` on
    `PlainN`; the guard is new).  No pill link: a model fact.  Size: (i)
    is of the size of `optimize_keeps_plain_pickR` (the `Opt*Sim` files), (ii)
    the size of D's `RawInvC*` per class.
2.d `optRef`: see the table; with calls the input side of track H's
    totality (`opt_total_*` need `FragX` because the alias pass reads only
    call-free blocks) is open.
2.e `inlAnnot` (no owner).  WHAT IT STATES: the nomm `D.inl long jets hot b`
    of `+inlined` stands for the bell's formula on its subjects (`Annot lib
    (realOf long.code) (Fits b.less) b.fol nm`).  THE HOON (`+inlined`,
    lines 3304 to 3394, 1,345 cells, calls `+scc-of` 430 cells): a
    structural copy of the code table's nomm in which a direct call
    `[%2 p q [c ~]]` (no memo key, `safe-fol-fol q`, `c` not hot, `c` a
    singleton SCC without a self call, the inlined callee at most
    `inline-max`) becomes `[%7 p m]`, `m` the inlined nomm of `c`
    (recursively, memoized in `inl.cache`); off when `inline-off`.  A PROOF
    NEEDS: a model `inlinedM` of the arm (recursion on the callee with fuel:
    the chain of singleton SCCs is finite); `Annot.mono` (Annot on a smaller
    set of subjects); the case `Annot.direct` → `Annot.inline` (exists:
    `Annot.inline` needs `c` to return the callee's formula on every subject,
    from `safe-fol-fol` and the `direct` premise, and the callee's `Annot`
    on `Img lib P b ⊆ Fits c.less`, from `CodeOK`); an invariant of
    `inl.cache` (every entry is `inlinedM` of its bell on the same table);
    the pill link of the 1,345 cells.  Model side: small (one induction on
    `Annot`); pill side: of the size of `fol_loop_iff`.
2.g `callee : CalleeNeeds (D.env …) (refN A ref …)`: tracks I, J.  I's
    `final_member`, `final_keeps` give (b), (c) under `Hyp` (`kidsOnly`,
    `shape` = the disabled `shape-check` assert, `msgSelf`; `msgAbs` now
    PROVED, `msgOrd_abs`); J's `NeedsRead` is the shape of `final_keeps`.
2.h `unary`, `scc`: tracks A, I, K (with 1.3, 1.4).  `answers` (no owner):
    WHAT IT STATES: from every `InvS` state, `compileStep A st b m` returns
    on every bell on which the reference compiler has a form: `A.sccOf`
    (`+scc-of`, 430 cells) returns, and `compiledMono` (`+compiled-mono`,
    115 cells: cache or `+compile-unary`, 299 cells) or `compiledNary`
    (`+compiled-nary`, 107 cells: cache or `+compile-scc`, 61 cells, then
    `(~(got by m) b)`, a crash unless `b` is in the SCC) returns.  THE
    BLOCKER: the sweep loop of `+compile-scc-in` (2,519 cells) does not end
    in general on the model: track I's `cyc_never` (`Ska/SccLoopCycle.lean`)
    is a member compile meeting `Hyp` under which the loop never returns;
    on the real compiler 145 SCCs all end (at most 5 sweeps,
    `sccstress.py`).  So `answers` needs a property of the member compile
    (I's candidate: `msg` without the cap a join, the compile monotone, the
    shapes bounded by the capes), then totality of `+scc-of` (a finite graph
    search) and of `+optimize` (1.5, `FragX` only).  Size: I's candidate
    property is the open research step; the rest is one totality theorem per
    arm (about 1,000 cells).  `stable`, `jetRoot`, `jets`, `fast`: no owner
    (P's branch map of `+poke` covers their arms).

## 3. `halting : FullAnswers pk InvC`

Chain: `fullAnswers_lift henc` of `FullAnswers (pokeS A) InvC'`:
- NEW `Glue.fullAnswers_of_cgM` (`Glue/InvMemo.lean`): `FullAnswers (pokeS
  A) (InvSM lib ref)` at the analysis fuel `anaFuel env regOf`, from `hC`,
  `hA`, `CgHalts`, `BakeEnds`, `RootAnswers`, with NO hypothesis on `InvB`
  (M8 closed);
- `Glue.fullAnswers_of_cg` (on `InvS`, with `∀ L, InvB lib L →
  MemoNoCallees L.memo`, which `InvB` does not give): superseded;
- `fullAnswers_of_loops` (`Ska/PokeHalt.lean`, `AnaEnds`).

3.1 `CgHalts lib env regOf`: track F.  `finPushes_of_freeze`
    (`Ska/PassFreeze.lean`): `FinPushes` from (i) `FinIdents`, C
    `PassMoves`, R `EvFrozen`; C now PROVED along every chain
    (`passMoves_chain`, `Ska/PassMoves.lean`), so `finPushes_of_freezeC`:
    `FinPushes` from (i) and R alone, given `MemoNoCallees` (which `InvSM`
    carries) and `PassHyp` at the start.  (i) reduced to `FinBranch` and
    `KruskalBT` (stated only) by König (`finIdents_of_kruskal`,
    `Ska/PassIdents.lean`).  OPEN: R (`EvFrozen`), `FinBranch`, the fuel of
    `+run`.
3.2 `MemoNoCallees`: in the invariant `InvSM` (PROVED kept:
    `Glue.pokeS_memo`, `anaArm_memo`; on P's route `pokeS_memoP`,
    `anaArmP_memo`; start: `invSM_init`).  On P's route the halting field is
    `Glue.halting_of_cgMP` (`FullAnswers (liftPoke (enc fl) (pokeS A))
    (liftInv (enc fl) (InvSM lib ref))` from `CgHalts`, `BakeEnds`,
    `RootAnswers`, `hA : A.skaPoke = anaArmP … (anaFuel env regOf) …`).
3.3 `BakeEnds` (the worklist of `+bake-graph` ends within `bf`): OPEN, no
    owner; `bakeLoop_mono`, `bakeLoop_grows`; no measure.
3.4 `RootAnswers` (no owner).  WHAT IT STATES: after the analysis of a
    `%full` poke from an `InvS` state, if the root is not a jetted arm with
    a hot driver, the reference compiler gives the root bell a whole-subject
    form (`ref … r.1 true = some x`).  It needs: the root bell is in the new
    code table (`realOf r.2.1.code r.1 = some nm`, an analysis fact) and
    `finishLUCM env nm` returns on it (the run of `+compile-unary` from an
    empty state: `+comp` returns, `+kerf`, `+to-straight`), for the
    reference read as the pill's compiler: the same totality as `answers`
    for one bell, plus the run of `+comp` (5,590 core axis, the
    `runLCM` model) returning on every nomm the analysis makes.  Size: a
    totality theorem of `runLCM` on the nomms of `+fol-loop` (the model is
    fuelled; the tracks prove contracts GIVEN a result).
3.5 `hC : CompHyp`: section 2.
M9/P3 (fuel): P's `FuelOK`, `fuelOK_anaFuel` (the analysis side).

## 4. `invStart : InvC cor`

CLOSED for `enc fl`: track P's `invStart_cor` (`cor_enc`: axis 14 of `cor`
is `[0 [[0 0 0 0 0 0 0] 0 0 0 0 0] 0 0 0 0 0 0]`, by kernel) on `InvS`, and
the third component of `Glue.gap_of_armPM` on `InvSM` (`invSM_init`).

## 5. `invKept : InvKept pk InvC`

`(gap_of_armPM …).2.1` on `InvSM` (`pokeS_invKept` and `pokeS_memoP`), the
same hypotheses as section 2 (or `gap_of_compM` for `anaArm`).

## 6. `libSlam : SlamIsNock lib`

PROVED for `Glue.libP` (`Glue/LibPill.lean`): `libP_slam` (`slam :=
slamGate nock`).  The compile-side theorems quantify over every `lib`, so
`libP` can be the `lib` of `Full`.

## 7. `libFormat`

For `libP` (`rendBase`: `+scow %p` on `%hand`, `+rend:mook` at the trace `~`
on `%spot` and `%hunk` of a cell, `rendLeaf` elsewhere; `softTank`: the unit
the pill's `(soft tank)` returns; `skipMsg n`: the cord of `+skip` at `yel =
n + 1024`), `libP_format` gives `LibFormat libP` from three LEAVES:
7.1 `RendLeafIs`, `HandIs`: PROVED (`libP_rendLeaf`, `libP_hand`).
7.2 LEAVES about the pill alone (no `lib`), no owner:
    - `RendRestTonFree`: `+rend:mook` on `%spot` and on `%hunk` of a cell does
      not depend on the trace (`mook.rend.hunk` 99 cells, `mook.rend.spot`
      315; they reach `+smyt`, `(soft path)`, `(soft spot)` 148 cells,
      `+scow %ud` in layers 1 to 4);
    - `SoftTankUnit`: `(soft tank)` returns a unit on every noun
      (`soft.gate.battery` 27, `soft.battery` 33, `tank.battery` 241 cells);
    - `SkipMsgTonFree`: the cord of `+skip` returns and does not read the
      trace (`mook.skip.msg` 118 cells, over `+scow %ud` and `+crip`).
    Cells by `tools/gen/nouns.py` (tree count); the entry formulas are small
    but call library arms of layers 1 to 4 (`+scow` is 17 cells calling
    `+co`).  Each leaf is a totality of a printing gate plus independence
    from the sample's trace.

## 8. `mookFormat : EvalMookMsgIs lib`

For `libP`: `libP_evalMook` from `EvalMookSame` (the cord of `+eval-mook`,
`mookMsgF`, `eval_mook.battery` 326 cells, on every `CorIn` core, is that
of `+skip` at layer 4) and `SkipMsgTonFree`.  LEAF, no owner.

## 9. MISMATCHES

M1. `DInvS` vs `OptIn`: RECONCILED (`CompPiecesO`, `CompPiecesM`).
M2. `optEq` with one `sfuel`: RECONCILED (`OptRef`), `hinj` PROVED
    (`straight_toNoun_inj`, also track P's).
M3. `runLC` vs `runLCM env true`, and classes blind to `env`, `N`:
    RECONCILED (`RefSideM`, `RawMonoD` with `MonoClass`, `compRestM_of_O`;
    `NCG`, `FragUFG`, `FragX`, `CallTreeA`, `TopTree`, `Six0` shown
    `noDirect`; `CallTreeD` plugs in directly).
M4. `sccSur` vs `shapeCol`: the model side needs nothing (`RawNary` and
    `RawNaryD` hold for every `ord`); the pill link must output `shapeCol`.
    Track A: `+shape-collapse` linked against `shapeCol` with forks and
    bonds (`fx_gate`, `i12_gate`, `fr_gate`, `oi_gate`, `ic_gate`), and
    `cu_gate_scc_one_six_fix` (`Compiler/CompShapeColRet.lean`): the
    one-bell top with `ord = scOrd fuel p.1 cape` (the `ord` of
    `+shape-collapse`), NO `FinSure`, one hypothesis `FixRet` (the fuel of
    `fixLoop`).  With `RawNaryD` for every `ord` the model side composes:
    M4 is down to `FixRet` (and the `sure.cache` entry `sccSur p.1 cape`,
    which `CsiSures` reads).
M5. Baking: every n-ary class has nothing baked; the compiler bakes.  No
    owner.
M6. `NoSelfCall`, one-bell SCCs: the `cu_gate` tops; model side has
    recursion (`closed_selfWalk`, `closed_pairWalk`), the pill side needs
    `csiFix` (track I).
M7. `callee` and `shape`: `shape` is the disabled `shape-check` assert;
    `msgAbs` PROVED (`msgOrd_abs`); the sweep loop does not end in general
    on the model (`cyc_never`), so a property of the member compile is
    needed (track I).
M8. `MemoNoCallees` not in the invariant: RECONCILED (`InvSM`;
    `gap_of_compM`, `fullAnswers_of_cgM` for `anaArm`; `gap_of_armPM`,
    `fullAnswers_of_cgMP`, `halting_of_cgMP` for `anaArmP`).
M9. Fuel: P3 (`FuelOK`, `fuelOK_anaFuel`).
M10. `FinPushes`: track F reduces it to `EvFrozen` (and (i)).
M11. `pokeModel` over `liftPoke`: track P (`enc`, `cor_enc`).
M12 (P1). The flags `[nomm pure total]` of each `code` entry are not in
    `VarEntry`; `enc` takes them as a parameter; `+compile-unary` reads them;
    the image of `PokeReach` cores needs a model of the flags (open; read
    from the Hoon, not tested on the compiler).
M13 (P2). `+ska-cole-update` reads the new bells, their `seek`, the hot
    rings; `anaArm`'s `jetsOf j reg'` cannot see them, so `anaArm` is not
    the pill; `anaArmP` replaces it.  Consequence: `gap_of_comp`,
    `gap_of_compM`, `fullAnswers_of_loops`, `fullAnswers_of_cgM` are for
    `anaArm`; their `anaArmP` twins: `gap_of_armP`, `gap_of_armPM`,
    `fullAnswers_of_cgMP` (DONE).  `AnaEnds`, `BakeEnds`, `CgHalts` do not
    mention the arm and are unchanged.
M14 (P4). A `%full` with an ATOM formula: the pill crashes in the mold
    `fol=^`, the analysis model answers (`Shape.other` gives `[%0 0]`), so
    `PokeModel` with `anaArm` is false there; `anaArmP` answers nothing on
    an atom.  The pill side (`+validate-ovum` crashes) is not proved.
    `FullAnswers` asks only cell formulas, so halting is unaffected.
M15. Build clashes (section 0): `Compiler.unitNoun_id_inj` (PokeEnc vs
    OptLinkAlJReg), `Comp.isLeaf` (SccLoopMsg vs CompNCJump).  Not a
    statement mismatch, but no file can compose the two sides of a pair.

## 10. OPEN LEAVES, in order of what blocks the most

1. The pill link of `+compile-unary` / `+compile-scc` read as `refMono`,
   `refNary`, `unary`, `scc` (1.3, 1.4, 2.a, 2.h): `csiFix` (1,000 of 2,519
   cells), (f) on cell needs, `FixRet` (A's one-bell top no longer needs
   `FinSure`).  Tracks A, I, K.
2. `answers` / `RootAnswers` (2.h, 3.4): TOTALITY of the compile.  The sweep
   loop does not end in general on the model (`cyc_never`); needs a property
   of the member compile (track I's candidate), then totality of `+scc-of`,
   `runLCM` on analysis nomms, `+optimize` outside `FragX`.  No owner for the
   totality as a whole; I owns the loop.
3. `inFragM` / `inFragN` (2.b'): every compiled nomm in `MonoCalls` /
   `NaryCalls`; missing `%10`, `%11`, `%12`, `%mean`, memo keys, n-ary `%6`,
   baking.  Tracks C, J, K.
4. `OptInMono` / `OptInNary` and `OptTotalMono` / `OptTotalNary` on the
   classes with calls (2.c, 2.d): track D (`OptIn` on `PlainN` not proved),
   track H's input side.
5. `CgHalts` (3.1): `EvFrozen` (track F).
6. `EntryMono` / `EntryNary` (2.c, `rawEntry`): a generic `EntryOK` lemma
   from `OptIn`, `Closed`, `ArityOK`, a `%cel` guard.  NO OWNER.
7. `pokeModel` (1.2 `FullBranchIs` and the five links, `spRest`, 1.6, the
   image of `enc` with M12): track P.
8. `BakeEnds` (3.3): no measure.  NO OWNER.
9. `callee` (2.g): tracks I, J.
10. `inlAnnot` (2.e): `+inlined` (1,345 cells) not modelled.  NO OWNER.
11. `stable`, `jetRoot`, `jets`, `fast` (2.h): NO OWNER.
12. Format (7.2, 8): `RendRestTonFree`, `SoftTankUnit`, `SkipMsgTonFree`,
    `EvalMookSame`.  NO OWNER.
13. M5 (baked n-ary code).  NO OWNER.

Leaves with NO owner: 2.c `rawEntry` (`EntryMono`, `EntryNary`), 2.e
`inlAnnot`, 2.h `answers` (totality beyond I's loop), `stable`, `jetRoot`,
`jets`, `fast`, 3.3 `BakeEnds`, 3.4 `RootAnswers`, 7.2 and 8 (four format
leaves), M5, M15 (the renames).  Owned since the first pass: 1.2, 1.6, M11,
M12 to M14 (track P).  Closed since the first pass: M3, M8 (both arms),
`hinj`, 1.1 (`enc`), 4.1 / `invStart` (`invStart_cor`, `gap_of_armPM`), 6,
7.1.
