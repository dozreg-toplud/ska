# LEDGER: what `Full` rests on (track G, 2026-11-28, thirteenth pass)

`Full` (`core/Statement.lean`) is proved by `Assembly.full_of` from one
structure, `Assembly.Gap lib pk InvC`, with eight fields.  This file traces
each field down to its OPEN LEAVES.  Every declaration named here is checked
to exist in `lemmas/Glue/AuditGlue.lean` (`#check`; track P's route
too, since M15 closed), and the theorems of
`lemmas/Glue/` have their axioms printed there (all within `propext`,
`Classical.choice`, `Quot.sound`).  A line that could not be verified is
marked *not checked*; names on a track branch that is not merged are marked
*(branch -x, not merged)*.  The marks *[255], not checked here* are from
the fourth pass (base 23a62c2).  The sixth pass is at base e4dfa5c (digest
[269]: every track merged through [269]); the names it adds from digest
entries [256] to [269] are checked in `AuditGlue.lean` (section "sixth
pass") unless marked *not checked*.  The seventh pass is at base c9f611e (digest
[272]); its names (digest [270] to [272] and track G's `inlAnnot` files)
are checked in `AuditGlue.lean` (section "seventh pass").  The eighth pass is at
base eb51715 (digest [282]); track G's new names are checked in `AuditGlue.lean`
(section "eighth pass"); names of other tracks from digest [273] to [282] are
*not checked here* (taken from the digest).  The ninth pass is at base 776fe98
(digest [292]); track G's new names are checked in `AuditGlue.lean` (section
"ninth pass"); names of other tracks from digest [283] to [295] are *not
checked here* (taken from the digest and the coordinator).

The tenth pass is at base 34b83be (digest [299]); track G's new names are
checked in `AuditGlue.lean` (section "tenth pass"); names of other tracks
from digest [296] to [299] and the brief are *not checked here*.

The eleventh pass is at base 812e4aa (digest [302]: every track merged
through [302], the FIXED compiler, pill 03d6233e...), with integration
75dffca (track D's leaves at 6e1dff4, track C) merged in; track G's new names are checked in
`AuditGlue.lean` (section "eleventh pass"); the names of other tracks from
digest [296] to [302] cited below were FOUND in the tree at 812e4aa (grep,
file named), not `#check`ed, except track D's four leaves (checked).

The twelfth pass is at base fbf606d (digest [305]); track G's new names are
checked in `AuditGlue.lean` (section "twelfth pass"); names of other tracks
from digest [303] to [305] are *not checked here* (taken from the digest).

The thirteenth pass is at base e4345c23 (digest [314]; K's [315] merge
09681a71 is NOT in this tree).  Its names, and the names of other tracks
from digest [306] to [314] that it cites, are checked in
`lemmas/Glue/AuditGlue13.lean` (a second audit file, so that neither audit
exceeds the 3500M cap); names from [315] are *not checked here*.

## THE ASSEMBLY (thirteenth pass): where `Full` stands, in ONE theorem

`Glue.gap13` (`lemmas/Glue/Assemble13.lean`) proves the WHOLE `Gap` (all
eight fields), and `Glue.full13` proves `Full` from it by `full_of`.  It is
stated for track P's route and for any class pair `FM`, `FN`:

    gap13 Ar ref D (hR : Route13 Ar env jet fold frozen bf regOf jetsOf newOf)
      (hP : PokeLeaves13 Ar env jet fold frozen bf jetsOf newOf)
      (hC : CompLeaves13 S Ar libP ref D FM FN) (hK : ClassLeaves13 S libP FM FN)
      (hH : HaltLeaves13 Ar ref env jet fold frozen bf regOf) (hF : FormatLeaves13) :
      Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar)) (liftInv (enc flagsOf) (InvSM libP ref))

`lib` is `libP`, `pk` is the model on nouns of track P (`enc flagsOf`), and
`InvC` is `InvSM` (the memo invariant of section 3.2).  `Route13` holds only
CHOICES of parameters (the arms of P's route, `anaArmP` at the fuel
`anaFuel`, the four `env` equations, the shape of `regOf`).  The other five
records hold the LEAVES, one field each, listed with owners in section 10.

The class pair enters only through `ClassLeaves13` (the raw contracts, `OptIn`,
the entry and the totality of the pill's `+optimize` on the class).  That
record is closed under union (`classLeaves_or`).  It is PROVED with no leaf on
`FragX` (`classLeaves_fragX`), and on `PlainCalls` (`PlainCallsM = MonoCalls ∩
PlainM`, `PlainCallsN = NaryCalls ∩ PlainNC`) from track D's `KIMid` and the
two totality leaves (`classLeaves_plain`).  So:

- `gap13_fragX`: the class is `FragX`, and no class leaf is left;
- `gap13_fragXPlain`: the class is `FragX ∪ PlainCalls`, the LARGEST union
  for which both the model contract and every other model fact of the class
  exist today, with three class leaves left (`KIMid`, `OptTotalMono` and
  `OptTotalNary` on `PlainCalls`).

The strongest RESTRICTION of `Full` that the pieces support is therefore this
one.  It holds for the pokes of P's route on code whose every compiled nomm
lies in `FragX ∪ PlainCalls`, which is the content of the leaves `inFragM` and
`inFragN`.  Those two are FALSE of the real compiler today, because real
nomms carry hints, memo keys, `%6` with calls and baked n-ary entries.

THE CLASSES (rows) BY PIECE (columns).  A cell is a theorem name, or the
missing leaf with its owner.

| class | pill link of `+run` / `+compile-unary` | model contract (`RawMonoD` / `RawNaryD`) | raw `OptIn` | entry (`EntryMono` / `-Nary`) | optimizer totality |
|---|---|---|---|---|---|
| `FragX` (pure, `%6`) | K's gate on `DirOk` (`cu_gate_dir_sccDS`, `unaryFinish_of_rest5`); `FragX` admits a `%10` at axis 0, `DirOk` does not (A's `NoAx0`) | `rawMonoM_fragX`, `rawNary_fragX` | `optInMono_fragX`, `optInNary_fragX` | `entryMono_fragX`, `entryNary_fragX` (no leaf: `guardMonoX`, `guardNaryX`) | `optTotalMono_fragX`, `optTotalNary_fragX` (H) |
| `PlainCalls` (indirect calls, no `%6`, no direct call, no hint, nothing baked) | `DirOk` (K) | `rawMonoD_calls`, `rawNaryD_calls` restricted | `optInMono_plain`, `optInNary_plain` (D) | `entryMono_plainK`, `entryNary_plain` from `KIMid` (D) | MISSING `OptTotalMono` / `-Nary` (H finished on `FragX`: the alias pass reads only call-free blocks) |
| `MonoCalls ∩ NoSixM` (direct calls, no `%6`) | `DirOk` (K) | `rawMonoD_calls` (`CallTreeDB`) | MISSING `OptInMono` on `NoSixM` (D) | `entryMono_noSixN` from `OptInMono`, `ReadsInMono`, `KIMid`, `KeyUndefC` (D) and `NskEndC` (G) | MISSING |
| `NaryCalls` with direct calls (`CallTreeDNB`) | `DirOk` (K) | `rawNaryD_callTreeDN` | MISSING (D) | MISSING `GuardNaryC` with `%cal` / `%jmp` (G) | MISSING |
| `%6` with calls (`Six0B`) | `DirOk` (K) | `rawMonoD_six0` | MISSING: D's `IL` is false at `%6`, candidate `ATS6` | MISSING (D's `ATS6`) | MISSING |
| C's general relation (`RunOKGen`) | `DirOk` (K) | per example and at the top only (`finishLUC_contractGD`, `exCons_contract`, `runOKGen_cons00`): no `RawMono` class yet | MISSING | MISSING | MISSING |
| hinted (`CallTreeH`, `CallTreeHU`, J's 20 of 39 arms, `contract_spotArm`) | Q: `comp_run_hintC` (`HintOkC`) on `runLCH` | J at `finishLUCH`, NOT at `finishLUCM` (M16) | MISSING | MISSING | MISSING |
| soft calls (`CallEnv.sof`) | I: `csi_gate_ranked_soft` on `runLCS` | MISSING (M20; `runLCS` differs from the Hoon at `+mede`) | MISSING | MISSING | MISSING |
| baked n-ary | A: `bn_gateB` | MISSING (M5) | MISSING | MISSING (map path of `+to-straight`) | MISSING |

MISFITS (pieces that do not fit as stated), in the order found:

1. Track P's top `pokeModel_fullReachP6L` gives `pokeModel` on `%full`
   only.  `PokeModel` asks every non-hot ovum, and P's `OtherKeeps6` says only
   that the other pokes keep `PGood6`.  BRIDGED by a new leaf `PokeOther13`
   (P: `%dire`, `%fast`, `%jets ~` are the model's) and
   `pokeModel_of_fullOther`.
2. Track P's top takes the gate in the OLD record `UnaryGateAt`.  Track K's
   record is `GateRest5` (built into `UnaryGateAtS`, soft members admitted),
   and K's file says that no map leads from the new record to the old one.
   BRIDGED: `monoLinkGood6_of_rest5` (K's record asked at `PGood6` states
   and read at `.good5`) and `pokeModel_fullReachP6K` (P's proof of
   `pokeModel_fullReachP6` with it).  K's own top `pokeModel_fullReachP5S` is
   over `PGood5` and takes `SccOfIs`, which track Q found FALSE as stated.
3. Track P's top takes any fuel with `FuelOK`, `halting_of_cgMP` takes the
   fuel `anaFuel`.  BRIDGED: `Route13` fixes `anaFuel`, and `gap13` uses
   `fuelOK_anaFuel`.
4. THE STATE RESTRICTION (not bridged, not a short lemma).  `CompHyp` asks
   `unary`, `refMono`, `inlAnnot` and the rest on EVERY `InvB` table and
   cache, while the pill facts hold on REACHED states only.  K's record holds
   at `PGood6` states, and there it gives exactly the equality `refMono` /
   `unary` need (`unaryFinish_of_rest5`: the pill's `+compile-unary` is
   `finishLUCM (S := CSet)` of the code table's nomm, on `DirOk`).  Track Q's
   truthful `inlAnnot_of_inv` (from `InlPill` and `InvBSR`) also holds only on
   the states of an invariant, because `InvBS` over every `InvB` state is
   false (`invBS_false`).  The fix is a `CompHyp` relative to an invariant
   `I` of reached states, with `pokeS_sound` and `pokeS_invKept` re-proved
   relative to it and `InvC := liftInv (enc flagsOf) (InvSM ∧ I)`.  That is a
   restatement of the `PokeM` chain (`Ska/PokeModel.lean`), owner G.
5. The pill link fixes `S := CSet`.  `gap13` is generic in `S`, so it is
   used at `S := CSet`.  Fits.
6. M16 (hints) and M20 (soft calls) keep their classes out of
   `ClassLeaves13`, whose contracts are at `finishLUCM` / `finishLFC`.
   Track J's hinted contracts are at `finishLUCH`, and track I's soft model
   `runLCS` disagrees with the Hoon at `+mede` (the compiler is right, see
   below).
7. Track C's contracts in the general relation are not a class.  They are
   proved per example (`exCons_contract`) or at the top
   (`finishLUC_contractGD`), so they do not enter `ClassLeaves13` until C's
   `runOKGen_all` / `contract_all` exists.

DIGEST [306] TO [315] (beyond the table):
- [306], [312] P: `+eval-finalized` linked, the SCC loop rests on Q's
  `SccsLeafAt` alone, then nothing about `+scc-of`, `+tarjan` or the loop is
  assumed (`pokeModel_fullReachP6L` over `PGood6 = PGood5 + ColeDom`).
  FINDING of P: `hJC` was false as stated (`coleCohM_put_bad`), restated
  `JetsOfCole6`.
- [307], [313] F: the pass-loop fix (dab8478) is merged since [300].  On
  the fixed loop `passLoop_returns_k` (one component returns from
  `KruskalBT`, `RunHalts` and a push tree), `PassGrowG` proved.  `CgHalts`
  itself is still open, and `FinBranch` is entangled with the finiteness of
  the identities.
- [307] Q: `tarjanM_spec`, `sccsLeafAt_of_tarjan`, `tarjanExists`,
  `sccImage`, `sccOfKeeps_of`; P's `SccOfIs` FALSE as stated, true form
  `SccOfIsK`.
- [308], [315] K: `cu_gate_dir_sccDS` (soft members), `GateRest5`,
  `pokeModel_fullReachP5S`; at [315] (not in this tree)
  `pokeModel_fullReachP5U` without member gates and without `UnarySccsIs`.
- [309] J: 20 of 39 hinted arms, `contract_spotArm` (both halves at the top
  for Q's real `!:` arm).
- [310] C: `exCons_contract` (unconditional), `runOKGen_cons00`.
- [311] Q: THE `+inlined` BAKE CASE IS SAFE on the real compiler
  (`tools/hoon/annots2.hoon`: the bake leaves `[%0 2]`, which `+inlined`
  drops; `+eval-top` agrees with `+mink` on all 12 subjects).  `KC`,
  `DetK`, `sffOn_of_detK`; `InvBSR` is with track Q and still open (the
  analysis must hand the bake `DetK`).
- [314] I: `csi_gate_ranked_soft`.  The `+mede` MODEL DIFFERENCE is
  REPRODUCED (`tools/hoon/medesoft.hoon`, 5 cases): `+crash-need` asks
  `+soft-ask` at a soft block, the model's `%1` never does.  The
  coordinator checked the real compiler on those five gates against `+mink`
  on 40 subjects (formalization-keep/medemink-2026-11-28.hoon): all 40
  agree, so the compiler is right and the model is wrong.  Track I fixes the
  model (`medeLS`, `runLCS2`).
- `split-max` (track S since [301]) is still OPEN: `+msg-need-ord` is not
  monotone, and a real cycle would make the totality leaf `answers` false.

READ FIRST (twelfth pass, base fbf606d, digest [303] to [305]):
- **`EntryMono` on `PlainM` and `EntryNary` on `PlainNC` rest on `KIMid`
  ALONE**: `entryMono_plainK` (`Glue/SplitDefRun.lean`), `entryNary_plain`
  (`Glue/GuardNaryPlain.lean`), with D's four `*_plain` leaves.  On
  `NoSixM` (direct calls): `entryMono_noSixN` (`Glue/ProxCalls.lean`) from
  D's `OptInMono`, `ReadsInMono`, `KIMid`, the end-state leaf `KeyUndefC`
  (D: no key of `cond` is defined after the top `+kerf`, D's `IL.cond`
  there) and `NskEndC` (G: no split op splits a key).  `EntryNary` on a
  class with direct calls or baked immediates: not done.
- The renaming needs LESS than `ProxEnd`: the `%cel` disjunct of `Want`
  matters only for a register annotated somewhere, and the restricted
  annotation has no key, so `celAnn_renameN` under `RenAN` needs only
  `ProxOKN` (`wr`, and `nsk`: no key is split); the `src` clause (cross
  block, no invariant behind it) is gone.  `ProxEnd` is superseded, not
  proved.  CHECKED (`Glue/ProxPlainCheck.lean`): on all 2,856 `PlainN`
  nomms of `enumCX`, 7 direct calls and 7,920 `enumDX` nomms no key is
  split; 28 hand-made `PlainN` nomms DO test a key with `%cel`
  (`+crash-need` of a bond's need through a proxy), none splits one.
- On `PlainN`, `wr` and `nsk` are D's `IL.cond` (`topU_of`) plus `SDBody`
  (every split register is defined by an earlier op of its body), carried
  through `runLC` by a new frame `KS` (`ks_runLC`, `kernNeed_sd`: the only
  splits are `+kern-need`'s, after its `%mov`).  With direct calls `SDBody`
  FAILS (`+mono-try-call`'s split block) and 64 of the 7,920 `enumDX`
  states split a register with no definition; the invariant for `NskEndC`
  is: a split register is defined earlier in its body, or is no key and
  lies below `re`.
- On `PlainNC` nothing is baked, so the inputs are a run
  (`isRun_needOrdAllocRegs`) and `+to-straight` takes the RENAMING path:
  the map path is needed only with baked immediates.  `+coerce-lazy` is
  carried over `KPA` (`kpa_coerceLazyL`) and `KS`; `nary_noKey` restates
  the step `uD` inside D's `tn_all`.
- Other tracks, digest [303] to [305] (not checked here): D (6e1dff4):
  `splitSpecL`, `intoSpecL`, `liveRun_plain` unconditional, `topSAR_plain`,
  `topSAU_plain`, the four `*_plain` leaves; `IL` FALSE at `%6` as stated
  (183,638 runs), candidate `ATS6` + `PrepRedir`.  C (75dffca): `%6` under
  `%done` on the real result (`six_doneGD`), `runOKGD_sevenG`,
  `runOKGen_sevenGF`, `runOKGen_n1`; the first contracts only the general
  relation gives (`sixCallTest22_contractG`, `seven0Six_contract`); the
  example waits on `runOKGen_cons00`.  K (8cbe387): `comp_run_softChain`
  (`SoftChainOk`: 5 of the 6 soft compiles; r31 `fld` is a `%6` reading
  `+soft-less`), `comp_run_n2_softTailR`, `softBond_spec`,
  `comp_run_n1_nextF`; MODEL QUESTION passed to track I (owner of
  `runLCS`): `+mede` -> `+crash-need` asks `+soft-ask` at a soft block
  while the model's `%1` never asks (not reproduced on the real compiler).

READ FIRST (eleventh pass, base 812e4aa, digest [296] to [302]):
- `StraightA` IS A THEOREM from a sharper named hypothesis: `straightA_of`
  (`Glue/StraightRen.lean`) from `ProxEnd`, the three PROXY FACTS of the
  state the top `+kerf` leaves (`ProxOK`: `wr` no register a block writes
  or takes is a key of `cond`; `cel` a split of a key comes after a `%cel`
  of it in the body; `src` a block that splits or tests a key does not
  write or take its source).  None names the annotation.  So
  `guardMonoC_noSixP`: `GuardMonoC` on `NoSixM` from `KIMid` (D) and
  `ProxEnd`; `entryMono_noSixP`: `EntryMono` on `NoSixM` from D's
  `OptInMono`, `ReadsInMono`, `KIMid` and `ProxEnd`.  CHECKED
  (`Glue/StraightRenCheck.lean`, `#guard`): `ProxOK` holds after the top
  `+kerf` on 7 of 7 direct calls and on ALL 7,920 `enumDX` nomms (5,351
  with proxies).  `wr` is track D's `IL.cond` (`¬ Defd`) at that state.
- FINDING: the old route's fact (`RenOK`: no written register is merged
  with another by `unproxy`) FAILS on 640 of the 7,920 states (an inner
  `+kerf` reads its `%nok` / `%cal` result register through proxies).  The
  general lemma is `celAnn_rename`: `BlocksOKA bs K` and `RenA bs K f`
  (`f` sends no other written register or parameter onto a register whose
  guard matters in the block: annotated, split or `%cel`-tested there)
  give `NoPoison` and `CelAnn` of the renamed code with the renamed
  annotation.  `+chase` carries the annotation back through empty hops
  (`chase_back`, `ann_back`); a `%clq` whose two ends chase to one block
  loses `ClqYes` and gets `CellOut` from its no-end's edge condition.
- TRACK D's LEAVES ARE THEOREMS on the class with INDIRECT calls, no `%6`,
  no direct call, no hint (integration 6e1dff4, `Ska/RawInvCLLeaves.lean`):
  `optInMono_plain : OptInMono S Map PlainM`, `readsInMono_plain`,
  `optInNary_plain : OptInNary S Map PlainNC` (nothing baked),
  `readsInNary_plain`.  For `KIMid`: `kim_split`, `kim_into` PROVED with no
  hypothesis; the run clause only for goals meeting `IL ∧ LG`
  (`kim_run_plainIL`); the `GD`-only form is checked (0 failures on 2,856
  nomms under 7 goals) and is D's next step, with `LzS Q l ↔ kimLz Q l`
  and the DIRECT call in its inductions (to reach `NoSixM`).  So
  `EntryMono` on `PlainM` rests on `KIMid` (D: the run clause, and the
  bridge from D's `kimLz` form of `kim_split` / `kim_into` to `LzS`) and
  `ProxEnd` alone: **`entryMono_plain`** (`Glue/StraightPlain.lean`, on
  this branch after merging integration 75dffca); `EntryNary`
  on `PlainNC` still needs `GuardNaryC` (G, not started).  D also found
  `IL` FALSE at `%6` as stated (`+fork-need`'s `o0` / `o1` hop up to the
  join, `+fork`'s `insertHop` rewrites an old entry block; reached from the
  top only with a call): a candidate `ATS6` holds on every family, an OPEN
  leaf for `%6` with calls.
- M17 is FIXED in the Hoon (dab8478 `ska: the pass loop of +analyze culls
  only when it is stable`, merged 5bf349d at [300]; pill 03d6233e...,
  793,550 bytes, `tools/pillswitch-dab8478.md`).  Track F re-cut and
  re-proved the model (`Ana.passEnd`, `pass_stepW`), keeping the top
  statements (`analyze_iff`, `ska_callgraph_iff`, `cg_run`,
  `skaPoke_sound`); the R / `EvFrozen` route is deleted.  `CgHalts` is
  still a HYPOTHESIS: left are the quiet-pass lemma, `FinPushes` from
  `FinIdents`, `FinBranch` / `KruskalBT`, the fuel of `+run` (track F since
  [302]).
- NEW OPEN QUESTION: `split-max` in the sweep loop (track S since [301], no
  Lean): `+msg-need-ord` is not monotone, because the cut is applied in one
  branch only, so the sweep loop's need may shrink and a cycle is
  conceivable (T, B, G under cape `[[| |] [| |]]` shown to the user; added
  in 3bbfae4 by an earlier session).  Track S searches for a real cycle on
  the real compiler and measures candidate changes on copies.
- Other tracks ([296] to [302]): Q: `+tarjan` modelled and proved correct
  (`tarjanM_spec`, `tjSpec_flop`, equal to the real arm on 222 graphs),
  linked (`tarjanLinkAt_jug`), the miss of `+scc-of` (`sccG_miss_enc`),
  `inlinedM_returns`; `+tarjan` crashes on the EMPTY graph (guarded in
  `+ska-poke`, line 1884; `+scc-of` never passes it one); left: the bridge
  to P's `TarjanSpecN` (`SccsLeafAt`, `TarjanExists`).  A: `+run-shape`,
  all ten corpus cases (`rs_cls8`, `rs_done8`, `rs_n2dW`, `rs_n2iW`,
  `rs_n6DP`).  I: the per-member `%done` step on soft members
  (`mem_done_stepS`, `memGate_done_realS`): all 65 real compiles, soft ones
  included, under `hreq` and the run.  K: `monoLinkGood3_of_gateStr`
  (`UnaryGateAtStr`, no decoding fields), the corpus's soft tail call
  (`callLS_soft_tail`, `comp_run_n2_softTail`).  P:
  `pokeModel_fullReachP5` over `PGood5` (= `PGood4` + `InvB` + `SccsIs` +
  `ColeCoh`), `loopTotal_of`, `htRank_of`, `good5_full_step`;
  `loopLinkAt_flagsOfT` up to `SccsLeafAt`, `EvalFinAt`.  J: the direct
  call in the hinted classes (`lokSH_directF`, `regFT_direct`), 18 of 39.
  F: `InvBS` is FALSE as stated (`invBS_false`); its truthful form
  `InvBSR` (reached states) is OPEN with NO OWNER (track F is on halting).

READ FIRST (tenth pass, base 34b83be, digest [296] to [299]):
- `GuardMonoC` IS A THEOREM on `NoSixM` (no `%6`; direct and indirect
  calls included) under two named hypotheses: `guardMonoC_noSix`
  (`Glue/GuardCallsTop.lean`) from `KIMid` (owed by track D) and
  `StraightA` (track G); `entryMono_noSix`: `EntryMono` on `NoSixM` from
  D's `OptInMono`, `ReadsInMono` and these two.  See 2.c, TENTH PASS.
- FINDING (argued, no witness run): the ninth pass's `KerfA` is FALSE as stated (any `nex` with
  `FL` labels): `+kern-need` of a need with a register twice puts a split
  after a write of its register.  True form: `KerfG` (every sure need of
  the lazy `DN`: distinct registers below `re`), PROVED (`kerfG`).
- Other tracks ([296] to [299], and the brief): K: `monoLinkGood3_of_gate`
  (`MonoLinkGood3` from the gate), decoding (b), the 6 soft calls of the
  corpus are one tail call, `callLS_soft_tail`; I: `NM` decoded
  (`ml_decode`, `csiDec_of_loop`), soft members and `+soft-emit` cut; P: the
  SCC loop `srLoop` linked (`loopLinkAt_flagsOfT`) up to the leaves
  `SccsLeafAt` (`+tarjan`, Q) and `EvalFinAt` (`+eval-finalized`),
  `LoopRunAt` false on an empty SCC list (restated `LoopRunAtT`), `PGood4`;
  C: the top in `RunOKGD`; J: 18 of 39, `SurGBT`, `runOKGBT_sevenG`; D: the
  four leaves owed in the `LRL` form.

READ FIRST (ninth pass, base 776fe98, digest [283] to [295]):
- `rawEntry` WITH CALLS (2.c), `GuardMonoC`: the run-level induction is
  redone over `InvA` as `KPA` (`Glue/GuardCallsA.lean`,
  `Glue/GuardCallsD.lean`): stages `(K, bo, re)`, labels `FL` (below `bo`,
  no annotation) kept along stages, lazy labels `LzL`, lifting lemmas
  `KPA.emit'` / `KPA.addOps'` (the old side condition `BlockOK` plus `FL`
  targets; `+add-ops` only at an `FL` label, so never at a split block).
  PROVED: `kpa_monoBlocks` (from `KerfA`), **`kpa_callDM`** (the direct
  call, from `RunA` of its two parts and `KerfA`), `+copy`, `+past`,
  `runA_top`.  OPEN: `KerfA` (`+kern` in the middle of a run) and `RunA` of
  `runLCM` on the class (the other arms), then the final passes.  CHECKED
  (`Glue/GuardCallsCheck.lean`): `BlocksOKA` (all blocks, the greatest
  annotation) holds at the end of the run, after `+kerf` and on the finished
  code of the seven `CompDirectMCheck` calls (7 of 7) and of one nomm in 8 of
  `enumDX` (990 of 990): 0 failures at every stage, so `CelAnn` survives
  `+kerf` and `+to-straight` there; the whole `enumDX` does not finish within
  the 900 s cap.
- D's leaves (coordinator, [293]): `ArmsL.cons` and `ArmsL.n10` are FALSE
  as stated (`LR` assumes only `IL`, which admits two bonds at one label),
  so `liveRun_plainOf` was vacuous; true forms `LRL` (`LR` plus `LG`:
  `LabUniq`, entries below `bo`), `ArmsLL`, `liveRun_plainOfL`,
  `liveRun_plain_of_specs` (from `SplitSpecL`, `IntoSpecL`: checked, not
  proved); `labRun_plain`, `liveRun_n5`, `liveRun_n2` proved.  `OptInMono`,
  `ReadsInMono`, `OptInNary`, `ReadsInNary` are OWED BY TRACK D in the `LRL`
  form, on code with calls and no `%6`, as `Glue/GuardCalls.lean` states
  them (kept stable).  The `+copy` question (two bonds at one label) is
  CLOSED by check: 0 failures at every copy of 309,850 runs with `%6` and
  hints.
- M17: the author APPROVED the no-cull fix of the pass loop of `+analyze`
  ([286] to [289], no measurable benchmark effect); track F applies it on
  its branch with a new pill (793,550 bytes, sha256 03d6233e...).  PENDING:
  until it merges, `halting` stays false of the pill on integration.
- `InvBS` as stated is FALSE (track F, `invBS_false`: it quantifies over
  every `InvB` state); the truthful leaf is `InvBSR` (reached states).
  `InlPill`: track Q since [286]; every branch of `+inlined` is linked
  (`inl_pill_gate`), `InlPill` itself still needs (a) `D.inl` tied to the
  pill (P), (b) a fuel bound for `inlinedM`, (c) `SccQ` beyond the hit path
  of `+scc-of`, (d) P's `CacheGood.inlKeys` strengthened to `InlCoh`.
- K: `cu_gate_dir_sccH` (nesting closed by height, new hypothesis `HtScc`
  and lower callees); P: `PGood3` (= `PGood2` + `VarsKeys`), flags closed on
  the model (`flagsOf_poke`, `loopLinkAt_flagsOf` from `SccsLeafAt`,
  `LoopRunAt`, `LoopTotal`; needs `PGood4`); A: `+run-shape` modelled (683
  `#guard`s), 5 of 10 cases linked; J: `RegGBT` (runs under `%next
  (lazy-from-reg r)`), 17 of 39; C: `RunOKGen` complete as a definition, the
  top proved in it (`finishLUC_contractGD`), famC failures a harness
  artifact; I: soft calls MODELLED (`runLCS`, `finishLFCS`, 65 of 65), M20
  reduced to the pill step on soft members; Q: `+tarjan` since [291].

READ FIRST (eighth pass, base eb51715, digest [273] to [282]):
- `rawEntry` WITH CALLS (2.c): the path guard is done.  `entryOK_ofK`
  (`Glue/EntryPathD.lean`): `EntryOK` from `DefFirst`, `ReadsIn`, `NoPoison`
  and a must-be-a-cell ANNOTATION `CelAnn bl K` of the labels (an edge into
  a label with `K _ s` is the yes-edge of a `%clq s` whose no-edge goes
  elsewhere, or `s` is a cell at the end of the block); `entryOK_ofP`
  (`Glue/EntryPath.lean`, the one-step form `CelGuardP`) and `entryOK_of`
  are special cases.  CHECKED (`Glue/EntryPathCheck.lean`): 0 failures on
  the raw code of the seven `CompDirectMCheck` calls, of 7,920 direct-call
  nomms made from `enumCX` (mono and n-ary) and of `enumCX`; on OPTIMIZED
  code `CelGuardP` FAILS (2,037 + 1,999 + 949 + 949) but `CelAnn` holds on
  all of it: `+optimize` moves a `%tal` into the yes block of a `%brn`
  whose `%cel` stays in the predecessor (witness `[2 [6 [0 2] [0 3] [0 1]]
  [0 1]]`, no direct call).  Not needed by the chain (`EntryOK` is stated
  on raw code), recorded for the interpreter.
- `EntryMono` / `EntryNary` on the classes with calls follow from three
  named leaves (`entryMono_of`, `entryNary_of`, `Glue/GuardCalls.lean`):
  `OptInMono` (D), `ReadsInMono` (D, new name; `optInput_finishLUX_at` is
  its `FragX` case), `GuardMonoC` (G: `NoPoison` and `CelAnn` of the raw
  output).  Toward `GuardMonoC`: the all-blocks form `BlocksOKA`, the run
  invariant `InvA` (labels and jumps below `bo`), and `mtl_kpa`
  (`Glue/GuardCallsMono.lean`): `+mono-try-call` keeps `InvA`, the
  annotation growing only at its fresh split blocks.
- Track F owns `InvBS` since [282]; `InlPill` has no owner (a new track N).
- Track A's new topic `+run-shape` (3,284 cells, [273]) is under 1.4 / 10.1.

READ FIRST (seventh pass, base c9f611e, digest [270] to [272]):
- `inlAnnot`'s MODEL HALF is PROVED (2.e): `inlinedM` (`Glue/Inline.lean`)
  is checked against the real `+inlined` (`tools/hoon/inldump.hoon`, 20
  pokes, the 29 entries of `inl.cache` equal, 11 with calls inlined; no
  difference), and `inlAnnot_of` gives the field from the pill half
  `InlPill` (no owner) and `InvBS`.  FINDING: the model half as the sixth
  pass stated it (from `CodeOK`) is FALSE: `Annot.direct` does not say that
  the call's formula part RETURNS, which `+inlined` needs when it drops it;
  restated on `CodeOKS` (`AnnotS`, the return at a call with no memo key and
  a `+safe-fol-fol` formula part).  `InvBS` (the analysis gives `CodeOKS`)
  is a new leaf of the analysis, no owner.
- M15 CLOSED again (372dcb9: track I's `csSw_gate`, `csSwG`): `AuditGlue`
  imports `CompSccLoopInd`, `CompSccLoopClose`, `CompSccLoopPrint`,
  `CompSccOfAny`, `CompMonoLink`, `CompSccLoopMemDone`, `CompGen` and checks
  `csi_gate_loop`, `csi_gate_ranked`, `cccMiss_of_loop` and the `_np` forms.
- M18 CLOSED: `printId_pill` (track I), so `csi_gate_loop_np`,
  `csi_gate_loop_d_np`, `csi_gate_ranked_np` carry no `PrintId`.
- Track K's `cu_gate_dir_scc` (callees in SCCs of any size, 1.3) and its
  FINDING: the member invariant of the SCC loop must be `QK` (`AgreeIP` at
  `P ∪ S`), not `AgreeE ∧ Ext` (false mid-loop).
- Track C's `RunOKGen` is ADOPTED for the classes (2.b'), phase F of `%6`
  open.

READ FIRST (sixth pass):
- `halting` is FALSE of the compiler as it is (section 3, M17): the pass
  loop of `+analyze` does not end on `tools/hoon/takecycle.hoon`.  `Full`
  cannot be proved by `full_of` until the Hoon changes.
- `contract` on `FragX`: `rawEntry` has no leaf left (`guardFinalU`,
  `guardFinalF`, `compHyp_of_fragX₃`, 2.c).
- Build clash M15 was REOPENED: two `Compiler.sw_gate` (track I's loop and
  the optimizer link), section 9; closed again in the seventh pass.
- Track I's `PrintId` is TRUE of this pill and provable like `cg_print`
  (1.4, M18): the earlier reading that the pill's `print-comp` slogs was
  wrong.

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

BUILD CLASHES: none left (M15 CLOSED in the fourth pass, reopened in the
sixth by two `Compiler.sw_gate`, CLOSED again by 372dcb9: track I's
`csSw_gate`, `csSwG`; `AuditGlue` imports the loop files).  Track P renamed
its `Compiler.unitNoun_id_inj` to `unitNoun_id_injP`, track I renamed
`Comp.isLeaf` of `Ska/SccLoopMsg.lean` to `ordIsLeaf`.  `AuditGlue.lean` now
imports `PokeEnc`, `PokeLink`, `InvMemoP`, `SccLoopMsg`, `SccLoopCycle`
beside everything else (built as a single target at 3500M), the former
`AuditGlueP.lean` is folded in and removed, and `Glue/MonoCalls.lean`
imports `Ska/PokeEnc.lean` and uses track P's `Compiler.straight_toNoun_inj`
(its own copy, with `needOrd_toNoun_inj` and `tr_toNoun_inj`, is dropped).

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
    Track P [255]: `full_step_enc` (the `%full` poke keeps the image of
    `enc`); next `Good st`, `PokeReachEnc` *([255], not checked here)*.
1.2 `+ska-poke` is `anaArmP` (P2): `pokeN_full_of` (`Compiler/PokeLink.lean`)
    gives `pokeModel` on `%full` with a cell formula from `FullBranchIs`
    (PROVED [247]: `fullBranchIs`, `pokeN_full`, `pokeModel_full`) and
    five named links `SkaLink`, `JetRootLink`, `SccLink`, `MonoLink`,
    `OptLink`.  TWO FINDINGS of track P: `JetRootLink` is FALSE as stated
    (`jetRootLink_false`: `jets` an atom crashes the test; restated
    `JetRootLinkR`), and `OptLink` is FALSE as stated ([255], reproduced on
    the real compiler: `(optimize [[%this ~] 1 ~])` crashes, `+bb-topo`
    reads block 0 with `+got:by`; `tools/hoon/optempty.hoon`), so
    `pokeModel_full` was VACUOUS.  Restated per state: `OptLinkOn OptTotal`
    for `optimizeP` (`optLinkOn_optimizeP`), `jetRootLinkG_of` (given
    `JetsGood`), `sccLink_of` (given `SccImage`), `skaLinkAt_of` (given
    `SpRestAt`), `pokeN_fullAt2`, `pokeModel_fullG` *([255], not checked
    here)*.  In `SkaLink`: the analysis part is linked
    (`ska_poke_iff`, `ska_poke_ana_iff_pill`, `analyze_iff`, `fol_loop_iff`,
    `resolve_iff`); `spRest`, the baking half (`+bake-graph`, `new-code`,
    the SCC loop with `+eval-finalized`, the writes of `seek` and `calls`,
    `+ska-cole-update`), has NO link (`SpRestAt`: 1,120 cells in 12 parts, none linked).
    Track P [260], [264]: `PGood` (the jets noun is seven `IsMap` parts,
    `JetsGood`, `MonoIn Cls`), `good_empty`, `good_full_step`,
    `pokeReachGood`, `pokeModel_fullReach`, `pokeModel_fullReachP`:
    `pokeModel` on `%full` at EVERY reachable core, from the named
    `SpRestGood` (none of its 1,120 cells linked), `SccImage` (reduced to
    `SccImageMiss`: 373 cells and `+tarjan` 837), `MonoLinkGood`,
    `OtherKeeps` (`%dire`, `%jets`, `%fast`), `UnaryKeeps`, `JetsOfGood`;
    `spRest_cut`, `spRest_of_parts` (the baking half cut into parts; 21
    pokes, no difference between model and Hoon).  Decided: the flags need
    a model `flagsOf` and `Closed` in `PGood` (M12).
    EIGHTH PASS, track P [274] *(not checked here)*: linked `newCodeLinkAt`
    (at `codeN = codeNoun fl code`), `datLinkAt`, `srSeek_run`,
    `srCalls_run`, `srK10_run`, `tailLinkAt_of` (from the jets leaf
    `TailEndAt`); `PGood2` = `PGood` + `CodeClosed` + `CacheGood` (K's
    clauses), every clause checked after each of 21 pokes
    (`tools/hoon/invdump.hoon`), `good2_empty`; kept by `%full` checked,
    not proved.  Not linked: `JetLinkAt` (`+cole-match` 557 cells),
    `BakeLinkAt`, `LoopLinkAt` (`flagsOf` undefined; `+tarjan` as one leaf
    `TarjanSpec`), `SpRestAt`.  Open choice: `jetsOf` has no `fl`.
1.3 `A.compileUnary` is the pill's `+compile-unary` (299 cells): tracks A,
    I, K.  PROVED: `cu_gate_scc_one_six_ts`, `cu_gate_scc_one_six_fol_ts`
    (one bell, `NoSelfCall`, `SixOk`, `FinSure`, `NoBakeOneC`);
    `cu_gate_scc_one_six_fix` (the same with the `ord` of `+shape-collapse`
    and `FixRet` in place of `FinSure`, track A); with direct
    calls `cu_gate_dir_csi` → `cu_gate_dir_arms` (`Compiler/CompSofPush.lean`,
    class `DirOk`, named hypotheses `CsiNeeds`, `CsiSures` on the product of
    `+compile-scc-in`), `cu_gate_dir_this` (every callee's need `%this` or
    `%none`), and track K's `cu_gate_dir_code` (`Compiler/CompSofArms.lean`:
    item (f) discharged on `DirOk` from facts of the code table, `SofBell`,
    `SfTable`).  Open: (f) on cell needs outside `DirOk` (`+sound-far` 329
    cells, `+need-soft` 134 cells: track K), (g) `nary.cache` threading.
    Its output is `finishLUCM` (`runLCM env true`), which now matches
    `RefSideM.refMono` (M3 closed).
    Track K [245]: a cache MISS is the normal way an outside callee is
    compiled (measured, `tools/hoon/calleecomp.py`: 37 pokes, 1,050
    `+callee-need` calls, 444 hits, 107 misses, nested `+compile-scc-in` up
    to 6 deep), so the link is THREADED: `ccc_miss`, `CccMiss`,
    `CompRunAtXT`, `crxt_of_x`, `sofBell_code`; [255] `cu_gate_dirT`,
    `cu_gate_dirExt`, `comp_run_dirT` (`Ext` on rests, `…RT` cases by
    `tools/gen/runt.py`; the old theorems are the no-miss case) *([255],
    not checked here)*.  Left: a miss inside the subject or formula of
    another direct call, `CallOkT` per call, the `CccMiss` reduction.
    Track A [250]: the bake model `Ska/BakeNeed.lean` (`needFits`,
    `bakeAll`, `bakeNeed`, `bakeNeedOrd`, `finishLFB`; 34 `#guard`s against
    the real final pass), links `nf_gate`, `bn_all`, `bn_testG`, `bn_loopB`,
    `bn_gateB` (`+bake-need` on every need and sock).  Not done: the top
    without `NoBakeOneO`, `+bake-need-ord` (268 cells).  In 11 real `%full`
    pokes no n-ary entry bakes (`imm` is `~`).
    Track A [258], [266]: `FixRet` is a THEOREM under `NormRun`
    (`fixRet_bound`: `size × wB depth + 1` rounds), and `NormRun` (no `pair
    none none` in a sure need) is a THEOREM on `SixOk` (`normRun_six`, by
    track D's `Clean`); tops `cu_gate_scc_one_six_cl`, `_bake_cl`, `_fol_cl`,
    `_bake_fol_cl` assume nothing on `+shape-collapse`.  Left: `NoSelfCall`,
    `NoAx0` / `FolMade`, `NoBakeOneO` / `BakeRunO`; `+to-straight` with `run`
    `|` (started: `tsr_rer`, `tsr_par`, `tsr_args`, `Compiler/CompStraightRun.lean`).
    Track K [259], [263]: `cu_gate_dirE` (the call's tail threaded, `AgreeE`
    at the final cache, `DirCallsT` recursive in the call's subject and
    formula); `ccc_scc_hit`, `calleeCompiled_one`, `cu_gate_dir_one` (no
    hypothesis on the compile of a one-bell callee); 107 of 107 misses of
    `+callee-compiled` take the `+scc-of` hit path.  Open: `+scc-of` on a
    singleton (409 cells and `+tarjan`, no owner), the general SCC (I),
    `hE0`, `CodeNoRing`, `CodeAna`.
    SEVENTH PASS, track K [271] (`Compiler/CompSccOfAny.lean`,
    `Compiler/CompMonoLink.lean`): `cu_gate_dir_scc`, the gate of
    `+compile-unary` on `DirOk` with callees in SCCs of ANY size, returning
    `finishLUCM env n` with a cache `CA'` that extends `CA` and keeps
    `AgreeE`, `RK`.  Its hypotheses: the state nouns `hgot`, `hv`, `hcl`,
    `hcsi` (the product of `+compile-scc-in`); `hE0 : AgreeE env (cuRest
    CA)`, `hR0 : RK SC0 inl (cuRest CA)` at the cache `+compile-scc-in`
    returned; the class `DirOk n`; the code table `EnvFrom`, `CodeNoRing`,
    `CodeAna`; `SccsGood SC0` (the meaning of `sccs`); `calls` a jug of
    sets; per callee `AnyCallee` (readable at the start, or outside the
    caller's SCC and `OneCallee`, track A's chain, or `SccCallee`, track I's
    loop with `MemGate` holding the nested misses).  Also
    `calleeCompiled_scc`, `envP`, `envP_agree`, `monoRaw_hit`,
    `monoLinkAt_of`, `compileUnaryP_gate`, `PGoodK` (for P: what `PGood`
    must also carry for `hE0`, `hR0`, `SccsGood`).  FINDING (K): `Q :=
    AgreeE env ∧ Ext` is FALSE mid-loop (each member run writes
    `sure.cache`; `nary.cache` gets the members only at the final
    `+uni:by`), so `MemGate` must be stated with `QK` (`AgreeIP` at `P ∪
    S`, `Compiler.QK`); track I's next `MemGate` on `%done` uses it.
    EIGHTH PASS *(not checked here)*: track A [273]: `+to-straight` with
    `run |` linked on every input (`tsr_jmp` .. `tsr_at`, `ts_at_any`,
    `tsAny_holds`); tops `cu_gate_scc_one_six_bake_all` / `_fol_all`
    assume only the state nouns, `SixOk`, `NoAx0` / `FolMade`,
    `NoSelfCall` (no `BakeRunO`).  Track K [280]: all 125 cells of
    `+compiled-mono` linked (`monoMissAt_of`, `monoLinkGood_of_image`);
    the run at `mono |` (`comp_run_dirTN`, `mem_runN`); left: decodings
    (a) `NM` as a `FinMap` of straights (I), (b) `CA'` a `cacheNoun`; the
    `|` miss at `AgreeIP`.
1.4 `A.compileScc` is the pill's `+compile-scc` (61 cells) over
    `+compile-scc-in` (2,519 cells on this pill): track I.  The loop is
    modelled (`SccLoop.lean`).  [251]: `Ranked c` (a bounded rank on
    entries that rises whenever `msg nn vn ≠ vn`; a HYPOTHESIS, argued from
    `+laze-collapse`) gives `loop_total`, `compileSccIn_total` (fuel
    `4·|scc| + |order|·(H+1) + 2`), `quiet_clean`, `cyc_not_ranked`; on the
    real compiler no split falls to `this` (305 SCCs,
    `tools/hoon/sccfall.py`).  The pill link: `csiFix` cut (`csiFix_cut`,
    `tools/gen/csifix.py`), `csf_fix`, `csf_enter`, `csf_trap`,
    `csf_trap_end`, `csf_trap_rec`; open: the loop link end to end.
    Track I [256], [263]: the loop link: `csi_gate_loop` (the pill's
    `+compile-scc-in` as a loop against `compileSccIn c false fuel`, with
    `MemGate`, three modes, the only hypothesis about `+run`),
    `csi_gate_ranked`, `cccMiss_of_loop` (under `Ranked`; checked since the
    seventh pass, M15 closed again).  Side hypotheses
    left: `hlevy`, `hkidsP`, `hdn`, `hdfs` (the DFS, 288 cells), `SccN`,
    `hR0`, and `PrintId` (`Compiler/CompSccLoopSt.lean`: the printer the
    loop pulls is the identity).  `PrintId` is a LEAF ABOUT TO CLOSE: in
    this tree `!@` takes its FIRST branch when the wing is MISSING
    (`?.((feel p.gen) q r)`, `desk/sys/hoon.hoon` line 10132), `comp-verb`
    is not defined, so `print-comp` is `same`: the pill's
    `print_comp.battery` is `[9 97710 [0 511]]`, the pull of `same`, as
    for `print-ska`.  So `PrintId` is provable like `cg_print`
    (`Compiler/SkaCallgraph.lean`); the comment in `CompSccLoopSt.lean` and
    digest [256] ("the pill slogs, the loop runs `(scow %ud counter)`")
    were a misreading (M18).  Track I told.  SEVENTH PASS [271]: PROVED,
    `printId_pill`, and the loop theorems without it: `csi_gate_loop_np`,
    `csi_gate_loop_d_np`, `csi_gate_ranked_np` (M18 closed).  Also
    `mem_gate_done_R` (`Compiler/CompSccLoopMemDone.lean`): `member` on
    `%done` at the gate level for a real SCC, both branches, with the run of
    `+run` at `mono |` and the product of `+coerce-soft` taken as given;
    `%must` / `%may` not linked (`+run-shape` 3,284 cells, `+laze-collapse`
    65, `+laze-may` 145, `+bake-need-ord` 268).
    EIGHTH PASS *(not checked here)*: track I [281]: `MemGate` on `%done`
    is a theorem for `cfgReal` with `QK` (`mem_done_step`,
    `memGate_done_real`, `memGate_done_K`); 65 `%done` compiles, no
    difference; `+coerce-soft` (757 cells) never taken on the corpus;
    MODEL GAP M20 (soft calls).  Track A [273], NEW TOPIC `+run-shape`
    (3,284 cells; what `member` runs in the modes `%must` / `%may`, since
    `dedicated-shape-pass` is defined; no model, no link): it is the
    `%must` / `%may` part of this leaf (`refNary`, `scc` through the member
    compile of `+compile-scc-in`); I's tally: 1,919 entries over 18 (case,
    goal) pairs, 10 nomm cases.  Then `+laze-collapse`, `+laze-may`,
    `+bake-need-ord`.
1.5 `A.optimize` is the pill's `+optimize`: PROVED on `FragX` (track H,
    `optimize_total_finishLUX`, `-LFX`, `opt_gate`).  Track P's `OptLink`.
1.6 `+scc-of` (409 cells by P's count, 430 tree cells by
    `tools/gen/nouns.py`), the jetted root (`JetRootLink`), `%jets` (298
    cells of the branch), `%fast` (288), `+compiled-mono` (115),
    `+compiled-nary` (107), `%dire` (122): track P, not linked.
    `+compiled-mono` LINKED by track K [280] (125 cells, 1.3).

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
| `optRef` | LEAF | `OptTotalMono S FM`, `OptTotalNary S FN` + `hpill` (`optRef_of_total`); PROVED on `FragX` (`optTotalMono_fragX`, `optTotalNary_fragX`); `hinj` PROVED (track P's `Compiler.straight_toNoun_inj`) | H (input side D), P (`hpill` = `OptLink`, restated `OptLinkOn`) |
| `rawEntry` | LEAF | `EntryMono S Map lib FM`, `EntryNary S Map lib FN` (`rawEntry_of`); PROVED on `FragX` with NO leaf (`guardFinalU`, `guardFinalF`, hence `guardMonoX`, `guardNaryX`, `rawEntry_fragX`; `compHyp_of_fragX₃`; generic `entryOK_of`; 2.c); with calls: `entryMono_of` / `entryNary_of` from `OptInMono`/`-Nary` (D), `ReadsInMono`/`-Nary` (D), `GuardMonoC`/`-NaryC` (G; `mtl_kpa`, `kpa_monoBlocks`, `kpa_callDM` over `InvA` (`KPA`); TENTH PASS: `guardMonoC_noSix` on `NoSixM` from the named hypotheses `KIMid` (D) and `StraightA` (G), `entryMono_noSix`; `KerfA` false as stated, `kerfG` proved; ELEVENTH PASS: `StraightA` PROVED from `ProxEnd` (`straightA_of`, `celAnn_rename`), so `guardMonoC_noSixP` from `KIMid` and `ProxEnd`, `entryMono_noSixP`; D's four leaves PROVED on `PlainM` / `PlainNC`, integration 6e1dff4); general `entryOK_ofK` | G, D |
| `refMono`, `refNary` | OPEN | pill link at `finishLUCM` / `finishLFC` | A, I, K |
| `inFragM`, `inFragN` | OPEN, FALSE today | every compiled nomm in `MonoCalls` / `NaryCalls` | C, J, K |
| `inlAnnot` | model half PROVED (`inlAnnot_of`), from two LEAVES | `InlPill` (pill half: `D.inl` is `inlinedM`), `InvBS` (the analysis gives `CodeOKS`); 2.e | none, none |
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
    Track C [248]: `%6` under `%next` by the relation `RunOKLT` / `LOKT` /
    `LOKTE` (`Unwraps`, `Tree1`, `AskNodup`; checked on 29,400 runs), phase
    S reduced (`sixNextSimpleC_plain`).  FINDING: `RunOKLS` is FALSE in
    phase F (15,640 of 15,640 runs: `+fork` re-points the blocks of the
    goal's entries, `GrowU` and `front` fail), so F needs a new relation,
    and 11 of 13 `LOKS` goal lemmas need a fork-aware goal arm.  [255]: the
    first `%6` below the top, `six_nextGB`, `six_nextT`, `fourSix_contract`,
    `threeSix_contract`, `fourSixCall_contract` *([255], not checked
    here)*; left: `TagLSP` for `CallTreeA`, other parents, nested `%6`.
    Track J [252]: HINTS.  The semantics layers already handle hints; the
    compiler side is the new model `runLCH env snd mono`
    (`tools/gen/runlch.py`), `runLCH_eq`, `finishLUCH_eq`, `finishLFCH_eq`,
    `CompHintCheck` (39 formulas, blocks equal to the Hoon's; 780 real runs
    agree with `+mink` / `+mock`), first contract
    `finishLUCH_contractN11s`.  Gap: `Annot.mean` lacks the side conditions
    that `FrameRel.meaf` / `.meac` need.  Track Q (new): the pill link of
    the hint cases of `+run` against `runLCH`.  See M16.
    SIXTH PASS, classes ([256] to [269]).  Track J: `CallTreeH` (=
    `CallTreeD` with hints `n11s`, `n11d` whose tags are not kept, `ClueSafe`)
    and `CallTreeHU` (hints not kept around PURE formulas, `KindU`),
    `lokSH_callTreeH`, `finishLUCH_contractCallTreeHU`; kept STATIC hints at
    the top under `%done` (`n11sKept_done`, `finishLUCH_contractN11sKept`);
    5 of the 39 dumped real formulas are in a class.  Nested results can
    repeat entry labels (4 of 22), so the relations' distinct-labels clause
    must change.  Track C [262]: `tagLSP_callTreeA`, the class `Six1` (`%6`
    at the top or under `[4 p]` / `[3 p]`), `finishLUC_contractSix1`; NO
    other parent admits a `%6` by copy; C, J, D hit the same wall
    (non-flat needs, repeated entry labels), so C's next session designs ONE
    relation `RunOKG` for arbitrary lazy goals.  SEVENTH PASS, track C
    [270] (`Ska/CompGen.lean`): `RunOKGen` = `FrameG` (`LabDisj`, `GrowG` /
    `RepointG`, per-label fronts) + `SemCoreG` (`nec`, `FrontsG`, `sem` /
    `semB` under `AgreeG`); every frame clause holds on 308,850 runs;
    `RunOKLS.toGen`, `FillSemL.cons`, `AgreeG.toLB`.  ADOPTED by the
    coordinator as the one relation of the classes; HOLE: phase F of `%6`
    has no semantic clause yet (`[brz proxy kid0 kid1]`, a precondition on a
    non-input register); C's next session settles it by an executable check
    first.  So M16's restatement (`refMono` at `finishLUCH`) waits on C's
    port of the top to `RunOKGen`.  For the glue, C proposes
    `six1_noDirect`, `rawMonoD_six1`, `Six1B` in `MonoCalls` (*not
    written*).  Track Q [257], [268]: `HintOk` = `DirOk` and every `n11s` /
    `n11d` (kept tags included: `comp_run_n11s_kept`, `comp_run_n11d_kept`),
    `comp_past_if` (`+past-if` linked), `comp_run_hint`, which now takes a
    hypothesis `HintSound` (`Compiler/CompRunHintClass.lean`; trivial on the
    old class, not yet derived from `SfClosed`).  Left for Q: a hint inside
    a direct call, `n12` (318 cells), `mean`.
    EIGHTH PASS *(not checked here)*: track Q [275]: hints inside direct
    calls (`comp_run_n2_directMMH`), class `HintOkC` (`DirOk` + every
    `%11` + `%12` + direct calls with hinted parts, `comp_run_hintC`);
    `HintSound` DERIVED from the table (`hintSound_of_tab`,
    `comp_run_hint_tab`, `comp_run_hint_ana` under `CodeAna` + `CallOk`;
    table checked on 16 real pokes, `tools/hoon/hinttab.hoon`); `%12`
    linked (`comp_run_n12H`); `%mean` cut only.  Track J [276], [280]:
    kept DYNAMIC hints at the top under `%done` with traces (`RunOKGBT`,
    `FrameOK`, `finishLUCH_contractN11dKept`), 12 of the 39 dumped
    formulas with a contract (`contract_d21`, `contract_d14`, `DoneAllT`);
    FINDING sent to C: `RunOKGB` does not compose with a push (three
    requirements on `RunOKGen`).
2.c `rawEntry` (LEAF `EntryMono`, `EntryNary`).  WHAT IT STATES: on the
    RAW code `s` of a bell (before `+optimize`), entered with `[x]` (mono) or
    the split of `x` (n-ary) for `x` fitting the bell, for every oracle, scry
    gate, state and trace, `Opt.EntryOK = ReadsOK ∧ ArgsOK ∧ LocalOK`
    (`Ska/Opt.lean`): on every path from the entry, every real read reads a
    defined register, every argument a pending pass moves is defined, and
    every `%imm`/`%mov`/`%con`/`%hed`/`%tal` reached with no pending
    parameters executes.  It is what `Opt.Keeps` assumes of an entry
    (`bellContract_of_keeps`).
    IS IT TRUE AS STATED: yes, on every subject, fitting or not
    (`Glue/EntryCheck.lean`): along the path of the model's interpreter from
    the entry, on the raw output of both final passes, with 45 subjects
    (atoms where cells are wanted, non-loobean tests included): `enumX`
    183,600 runs per pass, `enumCX` 178,200 runs per pass under four oracles;
    every run ends by `endOf`, none is stuck, no configuration fails a part.
    What guards a `%hed`/`%tal`: the `%cel` that `+kern-need` emits in the
    same op list (`kernBoth`: `mov r d, cel d, hed d rh, .., tal d rt, ..`;
    the head's ops between write fresh registers; 1,824 outputs have a
    `%hed`/`%tal` not right after its `%cel`).  No raw output passes `~`
    (3,360 n-ary outputs pass arguments), so no register is poisoned.
    PROVED (`Glue/Entry.lean`): `entryOK_of`: `EntryOK` from `DefFirst` (a
    field of D's `OptIn`), `Compiler.ReadsIn nargs`, `NoPoison` (no reachable
    jump passes `~`), `CelGuard` (every `%hed s`/`%tal s` of a reachable
    block after a `%cel s` of its body with no write of `s` between) and at
    least `nargs` entry values; one invariant `EInv` kept by every `Step`
    (`einv_step`).  `Closed`, `ArityOK`, `TwoNA` and the liveness at `0` are
    not needed.  On `FragX` (`Glue/EntryFragX.lean`): `DefFirst` and
    `ReadsIn` are D's (`optIn_finishLUX`/`-LFX`, `optInput_finishLUX_at`/
    `-LFX_at`), so `entry_finishLUX`, `entry_finishLFX`, `entryMono_fragX`,
    `entryNary_fragX`, `rawEntry_fragX` and `compHyp_of_fragX'` (`CompHyp`
    from `CompRestOE` = `CompRestO` without `rawEntry`) rest on the two LEAVES
    `GuardMonoX`, `GuardNaryX` (`NoPoison` and `CelGuard` of `finishLU`,
    `finishLF` output).  `EntryNary` needs no relation of the cape to the
    bell: the cape only removes look checks, never a `%cel`.
    FOURTH PASS (`Glue/GuardKern.lean`, `Glue/GuardRun.lean`).  PROVED the
    freshness fact of `+kern-need`: `kernBoth_guard`, `kernLoop_guarded`
    (with track D's `KR`), `kernNeed_guarded`: its ops are a `GuardedBody`.
    Between `cel d` and `tal d rt` lie `hed d rh` (writes the fresh `rh`,
    above `d`) and the head's ops, which write only registers of the head
    need (not `d`: `Distinct`, or `d` fresh for a `%pair`) or registers
    allocated after `d` (`KR.defs`).  PROVED the steps that keep
    `BlocksOK`: `blocksOK_emitted` (a block passing no `~` with a guarded
    body), `addOps_ok` (a guarded list in front: `GuardedBody` is a
    property of a list alone, every guard of the old body lies inside it,
    and `+add-ops` puts one whole `+kern-need` output in front, never a
    part), `blocksOK_insertHop`, `sureLoop_guard` (`+sure-loop`, under D's
    `raw_sureLoop` hypotheses).  Where a `~` comes from: only `+sect`'s
    threading (`sectStep`: a proxy one branch made); on `FragX` a run leaves
    `cond` as it is (D's `KeepX`, field `cnd`), so `+sect` is `SameBlocks`
    (`sect_spec`).
    FIFTH PASS (`Glue/GuardStep.lean` .. `Glue/GuardTop.lean`).  PROVED the
    run-level induction, as an all-blocks invariant with no label
    bookkeeping: `KP P m` (every run of `m` keeps `Inv` = `BlocksOK` and
    `drop = false`, with a result in `P`), the tactic `kpb`, and `KP` of
    every arm `run`/`runL` reaches on `FragX`.  The ops of every `+add-ops`
    of a run have no `%hed`/`%tal` (`NoSplit`, `guardedBody_of_noSplit`;
    the table in `GuardStep.lean`: `+split-need`, `+into-need`,
    `+copy-need-make-ops`, `+crash-need`, `+mede`, `+collapse-lazy-atom`);
    only `+kern-need` makes splits, and no run of `FragX` reaches `+kern`
    (no `+kerf`, the fork of a `%6` is not big).  `run_kp` (first
    fragment), `runX_kp` (`FragX`: `%6` by C's `sixBody_apart`,
    `sixNextSimple_apart`, `forkSure_spec`, `sect_spec` with `KeepR.cnd`,
    `KeepR.size`; the `KeepX` facts need the goal's registers below `re`,
    which holds of every sub-goal: `jmp0`s and fork-fresh registers),
    `runX_blocksOK` (the top run).  So the leaves are now the final passes
    alone, stated exactly from the run's end state: `GuardFinalU`
    (`+kerf`, `+to-straight`), `GuardFinalF` (`+need-ord-alloc-regs`,
    `+coerce-lazy`, the baked constants, `+to-straight`), with
    `guardMonoX_of`, `guardNaryX_of`, `compHyp_of_fragX''`.
    SIXTH PASS (`Glue/GuardFinal.lean`, `Glue/GuardFinalTop.lean`): the
    two final-pass leaves are THEOREMS, `guardFinalU`, `guardFinalF`, so
    `guardMonoX : GuardMonoX`, `guardNaryX : GuardNaryX`, and
    `compHyp_of_fragX₃`: `CompHyp` on `FragX` from `CompRestOE` alone.
    `+kern`: `kernStepG`, `kernListG` carry `BlocksOK` beside track D's `KI`
    (each gate puts one `+kern-need` output in front, guarded by
    `kernLoop_guarded` from `KI`'s facts: the entry's sure need `Distinct`,
    below `sub`, the source register not in it).  `+coerce-lazy`:
    `coerceStepG`, `coerceLazyLG` beside D's `CoI` (`sureLoop_guard`).
    `+to-straight`: `blocksOK_rename` (the renaming path keeps `BlocksOK`
    when the renaming sends no register a body writes onto another,
    `RenOK`; `+chase` returns a jump of the end or the hop of a block,
    `chase_keeps`, by fixpoint induction with no rank).  On the map path
    of `finishLU` the renaming is `renReg ∘ unproxy` (`toStraightF_run`):
    `unproxy` fixes every defined register (no defined register is a key of
    `cond`, `KI`) and sends the others to themselves or to `sub`, which is
    not defined; `renReg` is injective.  On `finishLF` there is no proxy
    (`cond` stays empty) and the renaming is `renReg`.  D's statements were
    usable as they are; nothing was restated.  Examples on a nested `%6`
    (`[6 [0 2] [6 [0 6] [0 3] [0 1]] [1 0]]`) in `GuardFinalTop.lean`.
    With calls: `EntryMono`, `EntryNary` on `MonoCalls` / `NaryCalls` are
    still leaves (the guard holds on `enumCX`; needs D's `OptIn` with calls
    and a run-level `KP` for the call arms).  No pill link: model facts.
    SEVENTH PASS, the first blocker with calls: `entryOK_of`'s hypothesis
    `CelGuard` is FALSE on the raw code of a direct call.  `+mono-try-call`
    guards its split by a `%clq` TERMINATOR of another block, not by a `%cel`
    of the same body: in `Ska/CompDirectMCheck.lean`, case `%dt` (`[8 [1 R]
    [9 2 [0 1]]]`, `#guard`ed equal to the real compiler), block 4 is `[hed 2
    4, tal 2 3]` with no `%cel 2`, reached from block 5 `clq 2 (jmp0 4)
    (jmp0 2)` (also `%dn`: blocks 7 and 8).  So `EntryMono` on `CallTreeDB`
    needs `entryOK_of` with a PATH guard (`EInv` carrying "register `s` is a
    cell" along the yes-edge of `clq s` into a block that splits `s` before
    writing it), then `KP` for the call arms with that guard, then D's
    `OptIn` with calls for `DefFirst` / `ReadsIn` (D: `ArmsL` = `n5`,
    `cons`, `n10`, `n2` left).  Not started.
    EIGHTH PASS (`Glue/EntryPath.lean`, `Glue/EntryPathD.lean`,
    `Glue/EntryPathCheck.lean`, `Glue/GuardCalls.lean`,
    `Glue/GuardCallsMono.lean`).
    - THE PATH GUARD.  `ClqYes f s o` (`f` is `%clq s z w` with `w.there ≠
      o`), `EntryCell bl o s` (`o ≠ 0`, every reachable edge into `o` is a
      `ClqYes _ s o`), `CelGuardP` (every reachable split of `s` has a
      `%cel s` before it in the body, or `EntryCell`, `s` no parameter, no
      write before); `EInvP = EInv ∧ CellP`, `einvP_step`,
      **`entryOK_ofP`** (`CelGuard` is the special case: `celGuardP_of`,
      `entryOK_of'`).  The general form, a data-flow certificate:
      `CellOut K o b s`, `CelAnn bl K` (fields `par`, `zero`, `edge`,
      `split`), `einvK_step`, **`entryOK_ofK`**, `celAnn_of_P`.
    - CHECKED FIRST (`Glue/EntryPathCheck.lean`, `celGuardPB`, `celAnnB` =
      the greatest annotation by a fixed point, `tallyK`): on the seven
      calls of `CompDirectMCheck` the old guard fails on all, the path
      guard holds raw and optimized, and `EntryOK` holds along the path
      (45 subjects, four oracles) raw and optimized; on `enumDX` (the 3,960
      nomms of `enumCX` with every indirect call made direct, to `bellR`
      keeping the formula part and to `bellR2` with `[1 R2]`; 7,920 nomms)
      the raw mono code has a path-only split in all 7,920 and meets
      `CelGuardP` in all; the raw n-ary code (`finishLFC envD`, `%cal` /
      `%jmp`, no `+mono-try-call`) meets the old `CelGuard`; `enumCX`
      (`finishLUC envR`, `naryC`) too.  0 raw failures.
    - THE OPTIMIZER BREAKS `CelGuardP` (and `CelGuard`), not `CelAnn`:
      optimized `enumDX` mono 2,037 of 7,843, n-ary 1,999 of 7,920,
      `enumCX` 949 and 949 of 3,960 fail `CelGuardP` and all meet `CelAnn`.
      Witness `[2 [6 [0 2] [0 3] [0 1]] [0 1]]` (no direct call): block 0
      `[cel 0, hed 0 10] brn 10 7 8`, block 7 `[tal 0 13] hop 6`; the
      `%cel` is in the predecessor.  Not needed by the chain: `EntryOK` is
      a hypothesis on RAW code and `Opt.Keeps` carries the run through
      `+optimize`.  77 of the 7,920 mono codes: `optimizeF 30` returns
      `none`; it is FUEL (the first, 48 blocks, is optimized at fuel 100
      and meets `NoPoison` and `CelAnn`).
    - THE LEAVES with calls (`Glue/GuardCalls.lean`): `entryMono_of`
      (`EntryMono` from `OptInMono`, the new `ReadsInMono`, `GuardMonoC`),
      `entryNary_of` (from `OptInNary`, `ReadsInNary`, `GuardNaryC`);
      `guardMonoC_fragX` (on `FragX` the new leaf is the old one).
      `GuardMonoC` = `NoPoison ∧ ∃ K, CelAnn` of `finishLUCM` output: G.
      `ReadsInMono`, `ReadsInNary` (`ReadsIn` at the argument count; the
      n-ary one with `nargs = countArgs need`): D.  `OptInMono`,
      `OptInNary`: D (`ArmsL`).
    - THE RUN-LEVEL INDUCTION, started (`Glue/GuardCallsMono.lean`):
      `BlocksOKA bl K` (the all-blocks form, `celAnn_of_blocksOKA`,
      `blocksOKA_of_blocksOK`), `InvA K g` (`BlocksOKA`, not dropping,
      every block and jump below `bo`, `K` below `bo`), `emitA` (`+emit`
      with the annotation growing at the fresh label only), `mtl_tail` (the
      split block, then its `%clq`), **`mtl_kpa`**: `monoTryLoop` keeps
      `InvA` with `K'` equal to `K` below the old `bo`, result below `bo`
      without `K'`.  WHY `KP` cannot be reused: `Inv` is `BlocksOK`, which
      is FALSE once a split block exists, so every `KP` lemma is vacuous
      after the first direct call; the arms must be redone over `InvA` with
      the result predicate "below `bo`, no `K`" on goals and results (the
      label bookkeeping the fifth pass avoided: `+emit` takes `bo`, `+re`
      registers; `+insert-hop`, `+add-ops`, `+fork` rewrite existing
      blocks, which keeps `K` only if they never rewrite a split block).
      Not done: `monoBlocks`, `callDM`, the other arms over `InvA`, the
      final passes (`+kerf`, `+to-straight` renaming keeps `CelAnn` along
      `RenOK`).
    NINTH PASS (`Glue/GuardCallsA.lean`, `Glue/GuardCallsD.lean`,
    `Glue/GuardCallsCheck.lean`).
    - `KPA K0 b0 r0 P m`: from `InvA K g` at a stage extending the base
      `(K0, b0, r0)`, every run of `m` ends in `InvA K' g'` at a stage
      extending the start (`XB`: `bo`, `re` grow, `K'` agrees with `K`
      below the old `bo`), with `P K' g'.bo g'.re` of the result.  Inputs
      are stated at the base and stay true (`FL.up`, `LzL.up`, `GFL.up`);
      `KPA.bind'` makes the end stage the base of what follows.
    - The lifting lemmas: `KPA.emit'` (a block meeting the old `BlockOK`
      whose jumps go to `FL` labels keeps `InvA`, `K` unchanged, the new
      label `FL`), `KPA.addOps'` (a guarded list at an `FL` label: not a
      split block, so its splits are `%cel`-guarded; a `CellOut` by `%cel`
      survives the prefix), `KPA.same`, `KPA.re'`, `KPA.mtc` (from
      `mtl_kpa`).  `kpa_copyNeed` is `kp_copyNeed` ported by script with
      asserted replacements.  `+insert-hop` and `+fork` are not needed: on
      code with no `%6` they are not reached (`Ska/CompSimBody.lean`).
    - PROVED: `kpa_simpleNextL`, `kpa_monoBlocks` (from `KerfA`),
      `kpa_copyLazyL` / `kpa_mergeForks` / `kpa_mergeBonds` / `kpa_copyL`,
      `kpa_pastL`, `kpa_needOrd`, `kpa_callTail`, **`kpa_callDM`** (both the
      drop and the `+mono-try-call` path, every goal with `GFL`, from `RunA`
      of the two parts and `KerfA`), `invA_gen0`, `runA_top`.
    - OPEN, in order: `KerfA` (`+kerf` in the middle of a run: `+kern`'s
      `+add-ops` at the lazy's labels, `FL` by `LzL`, needs `kernNeed`'s
      output guarded there, i.e. track D's `KI` mid-run); `RunA` of `runLCM
      env true` on the class (cons, `%0`, `%1`, `%3`, `%4`, `%5`, `%7`,
      `%10`, the indirect call `callL`: the old `GuardX` proofs over `KPA`);
      then `+kerf` and `+to-straight` at the top.
    - CHECKED: `blocksOKAB` (`BlocksOKA` on ALL blocks with the
      greatest annotation, `GuardCallsCheck.lean`) at the three stages of
      `finishLUCM envD` (end of the run, after `+kerf`, finished code):
      0 failures on 7 of 7 `CompDirectMCheck` calls and 990 of 990
      (`enumDX8`, one nomm in 8 of `enumDX`, `#guard`ed); the full 7,920
      timed out at 900 s.  So the run-level target of `RunA` / `runA_top`
      is true there, and the final passes keep the annotation (step 4:
      the renaming of `+to-straight` maps it, no counterexample).
    TENTH PASS (`Glue/GuardCallsB.lean`, `GuardCallsK.lean`,
    `GuardCallsL.lean`, `GuardCallsR.lean`, `GuardCallsTop.lean`,
    `GuardCallsCheckD.lean`).
    - `RunG`: `RunA` for goals whose lazy has `DN` entries (`LzS (DN re)`:
      every sure need, root, forks and bonds, has distinct registers below
      `re`).  PROVED: `kerfG` (`+kerf` mid-run: each gate's `+kern-need`
      is guarded, `kernNeed_guarded`, at an `FL` label), the lazy arms
      (`kpa_splitL`, `kpa_intoL`, `kpa_medeL`, `kpa_collapseLazyAtomL`,
      `lzL_fromL`, `kpa_forl`, `kpa_doneBlocks`, `kpa_bombL`), the calls
      (`kpa_callDMG`, `kpa_callLI`), every arm and **`runG_lcm`**
      (`RunG (runLCM env true sup nm)` on `NoSixC`, the rest fail), the top
      `+kerf` (`top_kerfA`), **`guardMonoC_noSix`**, `entryMono_noSix`.
    - NAMED HYPOTHESES: `KIMid env` (TRACK D: a run of the class, `+split`
      and `+into` keep `LzS (DN re)`; the result's `DN` is what `+kerf`
      needs, the halves' `DN` is what the sub-goals need; CHECKED at the end
      of the top run on 7 of 7 calls and 198 of 198 `enumDX`, one in 40,
      `GuardCallsCheckD.lean`); `StraightA env` (TRACK G: the final pass
      takes `InvA K` with an unannotated start block to a cell annotation of
      the finished code; CHECKED by the third stage of `GuardCallsCheck`).
    - OPEN, in order: `StraightA` (the old `RenOK` route fails as such with
      calls: an inner `+kerf` leaves proxies in `cond` for the register its
      `%nok` / `%cal` writes, so unproxying merges a written register with
      another; rename `K` with the registers and prove `+chase` keeps the
      edge condition); `KIMid` (D); `GuardNaryC` (its run is `runLCM env
      false`: the direct call is `callL`'s `%cal` branch, plus
      `+need-ord-alloc-regs` and `+coerce-lazy`).
    ELEVENTH PASS (`Glue/StraightRen.lean`, `Glue/StraightRenCheck.lean`).
    - The final pass on the run `[sub]` is `renameBlocks` by `f =
      renReg sub 1 ∘ unproxy` (`toStraightF_run`).  PROVED:
      **`celAnn_rename`** (`BlocksOKA bs K` and `RenA bs K f` give
      `NoPoison` and `CelAnn new (fun l s => ∃ s0, K l s0 ∧ f s0 = s)`;
      `RenA`: for every register `s` annotated at, split in or
      `%cel`-tested in a block (`Want`), `f` sends no other register the
      block writes or takes onto `f s`), `chase_back` / `ann_back` (the
      annotation goes back through empty hops), `blocksOKA_start` (the
      unannotated start block moved to `0`), `blocksOKA_np` (the annotation
      restricted to registers that are no keys of `cond`, from `ProxOK`'s
      `wr` and `cel`), `renA_prox` (`ProxOK` gives `RenA` for
      `renReg ∘ unproxy`), **`straightA_of`** (`StraightA` from
      `ProxEnd`), **`guardMonoC_noSixP`**, `entryMono_noSixP`.
    - NAMED HYPOTHESIS `ProxEnd env` (open, track D or G): the state after
      the top `+kerf` meets `ProxOK` (`wr`, `cel`, `src`; above).  `wr` is
      D's `IL.cond` (`¬ Defd`) there; `cel` holds because a key is read
      only by `+kern-need` / `+collapse-lazy-atom` ops at a lazy label,
      which start with the `%cel`; `src` because a kerf's register is
      written only by the `%nok` / `%cal` block emitted after the kerf,
      never in one of its lazy blocks.  CHECKED: 7 of 7, 7,920 of 7,920
      (`tallyP`), the old fact failing on 640.
    - With track D's leaves (integration 6e1dff4, merged here at 75dffca):
      D's class `PlainM` (indirect calls only) is inside `NoSixM`
      (`noSix_of_plain`), so `guardMonoC_plain` and **`entryMono_plain`**
      (`Glue/StraightPlain.lean`): `EntryMono` on `PlainM` from `KIMid` and
      `ProxEnd` alone (D's `optInMono_plain`, `readsInMono_plain`).
    - OPEN, in order: `ProxEnd` (a run invariant on `cond` beside `InvA`:
      every arm, as `KPA` carries `InvA` only); `KIMid`'s run clause in the
      `GD` form (D); `GuardNaryC` (its run is `runLCM env false`; the final
      pass bakes and may take the MAP path, whose renaming is built while
      it runs: `mapBlocks` must be shown to be `renameBlocks` by its final
      map, injective, before `celAnn_rename` applies); `%6` with calls
      (D's `ATS6`).
    - TWELFTH PASS: `ProxEnd` superseded by `ProxOKN` (`wr`, `nsk`) under
      the narrower `RenAN` (`celAnn_renameN`, `renA_proxN`,
      `blocksOKA_npN`, `Glue/ProxPlain.lean`).  On `PlainN`: `proxEndN_of`
      (D's `IL.cond` and `SDBody`), `splitDefEnd_plain` (frame `KS`,
      `Glue/SplitDefBase.lean`, `Glue/SplitDefRun.lean`), so
      **`entryMono_plainK`**: `EntryMono` on `PlainM` from `KIMid` alone.
      `GuardNaryC` on `PlainNC`: **`guardNaryC_plain`** (renaming path,
      `kpa_coerceLazyL`, `ks_coerceLazyL`, `nary_noKey`), so
      **`entryNary_plain`** from `KIMid` alone.  On `NoSixM`:
      `guardMonoC_noSixN`, `entryMono_noSixN` from `KIMid`, `KeyUndefC` (D)
      and `NskEndC` (G).  OPEN: `NskEndC` (the `KS` frame with the direct
      call's arms and the invariant "defined earlier in the body, or no key
      below `re`"), `KeyUndefC` (D's `IL` with the direct call), `KIMid`'s
      run clause in the `GD` form (D), the n-ary pass with baked immediates
      (the map path: `mapBlocks` = `renameBlocks` by its final map), `%6`
      with calls (D's `ATS6`).
2.d `optRef`: see the table; with calls the input side of track H's
    totality (`opt_total_*` need `FragX` because the alias pass reads only
    call-free blocks) is open.
2.e `inlAnnot`.  WHAT IT STATES: the nomm `D.inl long jets hot b` of
    `+inlined` stands for the bell's formula on its subjects (`Annot lib
    (realOf long.code) (Fits b.less) b.fol nm`).  THE HOON (`+inlined`,
    lines 3304 to 3394, calls `+scc-of`): a structural copy of
    `nomm:(~(got by code) b)` on every constructor, in which a direct call
    `[%2 p q [~ c k]]` with `k = ~`, `+safe-fol-fol q`, `c` not hot, `+scc-of
    c` = `{c}`, `c` not in its own `calls`, becomes `[%7 p' m]`, `m` the
    inlined nomm of `c` (recursively, memoized in `inl.cache`), unless
    `nomm-size m` exceeds `inline-max` (48).
    SEVENTH PASS (`Glue/Inline.lean`, `Glue/InlineCheck.lean`,
    `Glue/InlineAnnot.lean`):
    - MODEL: `inlinedM code calls hot single fuel b` (`inlWalk` the trap,
      `nommSize` = `+nomm-size`, `inlOK` the test; no cache: it is the
      function `inl.cache` memoizes; `single c` = "`+scc-of c` is `{c}`";
      fuel: the callee chain goes down the condensation of `calls`, so one
      more than the number of bells of `code` is enough).
    - CHECKED on the real compiler: `tools/hoon/inldump.hoon` (20 pokes in
      a row: 16 through the `%full` branch by hand with an unknown subject,
      4 real `%full`; a small callee, one over `inline-max`, a chain of two,
      a callee whose own inlining takes it over 48, recursive callees, an SCC
      of two, a non-safe formula part, a memoized call, `%9` arms, a `%spot`
      hint), `tools/hoon/inlcheck.py` → `Glue/InlineData.lean`; the 29
      entries of `inl.cache` are `inlinedM` of their bells (`inlFailing =
      []`), 11 with calls inlined.  NO DIFFERENCE.  Not exercised: a hot
      callee (`jets-hot` stays `~`).
    - FINDING (M19): the model half as stated in the sixth pass (from
      `CodeOK`) is FALSE.  `Annot.inline` needs the dropped formula part `q`
      to RETURN on every subject; `Annot.direct` says only "if it returns,
      it is the callee's formula", and `+safe-fol-fol` admits `[%0 a]`.
      Witness (argued, `InlineAnnot.lean` header): `fol = [7 [6 [3 0 1] [1 0
      0 1 0] [1 5]] [2 [0 1] [0 7]]]` knowing nothing, callee `[1 0]`;
      `CodeOK` holds, the inlined nomm returns `0` on an atom where the
      formula crashes.  The real analysis does not make that call direct
      (the join of the two products does not know axis 7).
    - RESTATED and PROVED: `AnnotS` (= `Annot`, and at `direct` with `k =
      none`, `safeFolFol q`: `q` returns on every subject of `P`),
      `CodeOKS`, `AnnotS.toAnnot`; `inlWalk_annot` (ONE induction on the
      `AnnotS` derivation; the inlined call is `Annot.inline`, the callee's
      `Annot` restricted by `Annot.mono` along `Img lib P b ⊆ Fits c.less`);
      `inlinedM_annot` (induction on the fuel = the callee chain; no
      measure, no use of `calls`, `hot`, `single` or the size test);
      `inlAnnot_of`: the field `inlAnnot` from two LEAVES:
      - `InlPill lib D` (the pill half; OWNER track Q since [286]: every
        branch of `+inlined` linked, `inl_pill_gate`, [291]; left: (a) to
        (d) of READ FIRST, ninth pass; the map below, [282]): on every `InvB` state
        `D.inl … b = some nm` gives `inlinedM (realOf long.code) calls hot
        single fuel b = some nm` for some fuel, `calls`, `hot`, `single`;
      - `InvBS M lib` (the analysis half; OWNER track F since [282], with a
        real-compiler check of every direct call with a `+safe-fol-fol`
        formula part first): the code table of every
        `InvB` state meets `CodeOKS` (what `InvB.codeOK` gives, plus the
        return at every droppable direct call; from the analysis's sock at
        the call: the formula is known, so the axes `q` reads exist).
    THE PILL HALF, map for a new track: the arm is `0x5dde` of `K`
    (`Compiler/CompInlined.lean`, body cut by `tools/gen/inlined.py`:
    `inlBodyN` 1,311 cells = `inlGet` 21, `inlHit` 3, `inlMiss` 1,272 =
    `inlHot` 64, `inlGot` 24, `inlAfter` 29, the trap `inlTrap` 1,134 with
    branches cons 59, `%2` 324, `%3` 32, `%4` 32, `%5` 61, `%6` 90, `%7` 61,
    `%10` 63, `%11` 111, `%12` 61, `%mean` 80).  Linked: `inl_body_at`,
    `inlBody_eq`, `inline_off_at` (`|`), `inl_trap_pure` (the walk is the
    identity on a pure nomm and keeps the cache), `inl_gate_miss`,
    `inl_gate_hit`, `inl_gate` under `InlOK` (pure nomms only);
    `safe_fol_fol_pill` (`Compiler/Safe.lean`); `+scc-of` by track K
    (`CompSccOfOne`, `ccc_scc_hit`, `CompSccOfAny`).  Missing: the `%2`
    branch with an `info` (324 cells: `hot`, `+has:in` of `calls`, the
    call of `+scc-of`, the recursion `inlined-loop` into the gate itself,
    which needs an induction on the fuel, `+nomm-size`, no link), the other
    branches on non-pure children (every branch rebuilds; `%11` both
    shapes), and the cache coherence: every entry of `inl.cache` is
    `inlinedM` of its bell on the current table (kept by a miss; the table
    only grows; `%jets`, `%fast` delete or clear entries).  K's
    `cu_gate_dir_scc` and `PGoodK` take `inl : Noun → Option Nomm` as a
    parameter: `InlPill` is what ties it to `D.inl`.
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
    is a member compile meeting `Hyp` under which the loop never returns
    (and it is not `Ranked`: `cyc_not_ranked`; under `Ranked c` the loop
    ends, `loop_total`, [251]);
    on the real compiler 145 SCCs all end (at most 5 sweeps,
    `sccstress.py`).  So `answers` needs a property of the member compile
    (I's candidate: `msg` without the cap a join, the compile monotone, the
    shapes bounded by the capes), then totality of `+scc-of` (a finite graph
    search) and of `+optimize` (1.5, `FragX` only).  Size: I's candidate
    property is the open research step; the rest is one totality theorem per
    arm (about 1,000 cells).  `stable`, `jetRoot`, `jets`, `fast`: no owner
    (P's branch map of `+poke` covers their arms).

2.i WHAT `contract` RESTS ON when every compiled nomm is in `FragX`
    (`compHyp_of_fragX'`, `Glue/EntryFragX.lean`, then `gap_of_armPM`):
    - model facts: `inlAnnot`'s model half is PROVED (`inlAnnot_of`, 2.e)
      from the analysis leaf `InvBS` (no owner: `CodeOKS`, the return of a
      droppable formula part, which `CodeOK` lacks: M19);
      `callee` (2.g, I, J); the totality in `answers` (2.h: `Ranked` of the
      real member compile, track I).  The guard leaves are CLOSED
      (`guardFinalU`, `guardFinalF`; `compHyp_of_fragX₃` needs only
      `CompRestOE`);
    - pill links: `refMono`, `refNary` (2.a: `+compile-unary`,
      `+compile-scc`, now threaded through cache misses, K), `unary`,
      `scc`, `hpill` of `optRef` (P's `OptLink`, false as stated, restated
      `OptLinkOn`; the rest of `optRef` is PROVED on `FragX`,
      `optRef_fragX'`), `inlAnnot`'s pill half `InlPill` (`+inlined`,
      body 1,311 cells, the `%2` branch 324 and the cache coherence open,
      and `+scc-of`, 430; no owner), `stable`, `jetRoot` (`JetRootLinkR`), `jets`,
      `fast`;
    - class membership: `inFragM`, `inFragN` (every nomm the analysis
      compiles is in `FragX`; false in general, 2.b').
    `rawOptIn`, `rawMono`, `rawNary` and `rawEntry` are discharged on
    `FragX` with no leaf.

## 3. `halting : FullAnswers pk InvC`

ELEVENTH PASS: M17 is FIXED (dab8478, merged at digest [300], pill
03d6233e...; see M17).  The paragraph below describes the OLD compiler; on
the fixed one `halting` rests on `CgHalts` (track F: the quiet-pass lemma,
`FinPushes` from `FinIdents`, `FinBranch` / `KruskalBT`, the fuel of
`+run`).

FALSE OF THE OLD COMPILER (digest [265], M17).  The pass loop of
`+analyze` does not end on `tools/hoon/takecycle.hoon`: one `%full` poke on
the fresh core (subject 0, a hand-built formula: a root with a 3-slot shift
register, two relay chains of lengths 2 and 4 feeding complement sites;
`%rec` takeovers at a constant-subject site of the root after `+cull`).
Reproduced by the coordinator (`runhoon.sh takecycle.hoon 240`: `%poke-1`,
no `%poke-1-returned`, exit 124); instrumented, the root identity runs
7,283 passes with the `%st` hash periodic (period 18 from pass 7).  So
`EvFrozen`, `FinPushes`, `CgHalts`, hence `Halts`, are FALSE, and for any
`pk` that meets `pokeModel` (1) the poke has no answer at `cor`, where
`InvC` holds (section 4): `halting` is false as stated until the Hoon
changes (the user's decision; track F's candidates: keep the member's datum
on `+cull` and restart a re-push from it, or cull only at the end of the
pass loop).  What depends on it: the field `halting`, hence `Full` through
`full_of`; the hypothesis `CgHalts` of `fullAnswers_of_cgM`,
`fullAnswers_of_cgMP`, `halting_of_cgMP` (the theorems stay true, their
hypothesis cannot be met); 3.1 entirely.  Not affected: `contract`,
`invStart`, `invKept`, `libSlam`, `libFormat`, `mookFormat`, `pokeModel`
(no field but `halting` asks the analysis to end), and 3.3, 3.4 as
statements.

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
    `+run`.  Track F [249]: 66 cores designed for a `%rec` takeover cycle
    of a persistent member's transient callees
    (`tools/hoon/passmeasure-take.py`): all return, at most 10 passes, no
    `%st` recurrence, no re-push; the mechanism is argued from the Hoon,
    not proved, and there is no Lean yet (next: `Covers`, one covering
    claim, `EvFrozen` and `FinBranch` from it).  SUPERSEDED by [265]:
    `takecycle.hoon` is a `%rec` takeover cycle that never ends, so R is
    FALSE (section 3 head, M17).  Track F's next session (no Lean): the
    mechanism table, a minimal witness, candidate fixes measured on COPIES
    of the Hoon, a recommendation with a diff not applied.
    EIGHTH PASS, track F [279] *(tools only)*: the CAUSE of the cycle (a
    culled member re-pushed from the bunt takes a sibling's kid over by
    `%rec`); minimal witness `tools/hoon/takemin.hoon`; three fixes on
    copies (`tools/hoon/passfix.py --fix keep|endcull|late`), RECOMMENDED
    `endcull` (no cull inside the pass loop; termination from `FinIdents`
    and a quiet-pass bound, `EvFrozen` unnecessary), not applied; the
    coordinator's checks pass (`takecycle.hoon` returns with it; 21 pokes
    identical).  WAITING for the user's decision (M17).
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
    (track P's `Compiler.straight_toNoun_inj`, used by `MonoCalls`).
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
M5. Baking: every n-ary class has nothing baked; the compiler bakes.  Owner:
    track A (since 2026-11-27).
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
M10. `FinPushes`: track F reduces it to `EvFrozen` (and (i)); both FALSE
    of the current compiler (M17).
M11. `pokeModel` over `liftPoke`: track P (`enc`, `cor_enc`).
M12 (P1). The flags `[nomm pure total]` of each `code` entry are not in
    `VarEntry`; `enc` takes them as a parameter; `+compile-unary` reads them;
    the image of `PokeReach` cores needs a model of the flags (open; read
    from the Hoon, not tested on the compiler).  Decided [264]: a model
    `flagsOf` and `Closed` in `PGood` (track P).
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
M15. Build clashes (section 0): CLOSED in the fourth pass (P's
    `unitNoun_id_injP`, I's `ordIsLeaf`; `AuditGlueP` folded into
    `AuditGlue`; `MonoCalls` uses P's `straight_toNoun_inj`).  No clash left
    among the files `AuditGlue` imports.  REOPENED in the sixth pass:
    `Formalization.Compiler.sw_gate` is declared both in
    `Compiler/CompSccLoopStep.lean` (track I, the sweep step; imported by
    `CompSccLoopInd`, hence `CompSccLoopClose`) and in
    `Compiler/OptLinkSwGate.lean` (the optimizer link), so no file can import
    both; `AuditGlue` leaves out I's loop files.  Fix: track I renames its
    `sw_gate` (e.g. `sweep_gate`).  CLOSED in the seventh pass: 372dcb9 renamed
    track I's `sw_gate` to `csSw_gate` and `swG` to `csSwG`; `AuditGlue`
    imports the loop files and checks the three theorems.
M16 (in the making). Hints: track J's `runLCH env snd mono` is a THIRD model
    of `+run` beside `runLC` and `runLCM env true` (the hint cases are its
    only difference: `runLCH_eq`, `finishLUCH_eq`, `finishLFCH_eq`).  The
    glue states `refMono` at `finishLUCM` and the classes over `runLCM`, so
    once the analysis's nomms with `%11` are in a class, `RefSideM.refMono`,
    `RawMonoD`, `RawNaryD` and `inFragM` / `inFragN` must be restated at
    `finishLUCH` / `finishLFCH` (with an `_of` lemma from the hint-free
    classes, as `compRestM_of_O` did for M3), and track Q's pill link must
    land on `runLCH`.  Owners: J (model), Q (pill), G (glue).  Sixth pass:
    Q's `comp_run_hint` covers every `n11s` / `n11d` (kept tags too) under a
    NEW hypothesis `HintSound` (not yet derived from `SfClosed`), so the
    restated `refMono` at `finishLUCH` will carry it; J's classes
    `CallTreeH`, `CallTreeHU` hold 5 of the 39 real formulas.  Not restated
    yet (the glue waits for C's `RunOKG`, 2.b').
    EIGHTH PASS: Q's `HintSound` is derived from the table
    (`hintSound_of_tab`, [275]), so the restated `refMono` at
    `finishLUCH` carries `CodeAna` and `CallOk` instead.
M17. `halting` is FALSE of the current compiler (digest [265], section 3):
    the pass loop of `+analyze` does not end on `tools/hoon/takecycle.hoon`.
    `CgHalts`, `EvFrozen`, `FinPushes`, `Halts` are false.  A Hoon change
    (the user's decision) is needed before `Full` can be proved.  NINTH
    PASS: the author APPROVED the no-cull fix ([286] to [289]: cull only
    when stable; no measurable benchmark effect); track F applies it on its
    branch (new pill 793,550 bytes, sha256 03d6233e..., `pillswitch` note,
    model of the pass loop changed in place, then halting on the new loop).
    PENDING, not done: until it merges, M17 stands on integration.
    ELEVENTH PASS: FIXED.  Hoon commit dab8478 (the `endcull` hunk and
    three comments), merged 5bf349d at [300]; pill sha256 03d6233e...,
    793,550 bytes, names switched by `tools/pillswitch-dab8478.md`; arms
    whose Nock changed: the `$` of the pass loop, and five arms with
    unchanged source whose `?=` over hint tags is reordered (`+know`, arm
    14302 of `ana`, `+hinted`, `comp-run-shape`, `comp-run`).  Track F
    re-cut `Ana.passEnd` and re-proved `pass_stepW`, keeping `analyze_iff`,
    `ska_callgraph_iff`, `cg_run`, `skaPoke_sound`; the R / `EvFrozen` and
    `passOn_moves` routes are deleted.  `CgHalts` stays a hypothesis
    (section 3).
M18. `PrintId` (track I's loop theorems) rested on a misreading: `!@` takes
    its FIRST branch when the wing is MISSING (`desk/sys/hoon.hoon` line
    10132), so with `comp-verb` not defined `print-comp` is `same`
    (`print_comp.battery = [9 97710 [0 511]]`) and `PrintId` is provable
    like `cg_print` (1.4).  No entry of this ledger said the pill slogs;
    the misreading was in `Compiler/CompSccLoopSt.lean`'s comment and
    digest [256] (corrected in [269]).  CLOSED in the seventh pass:
    `printId_pill`, `csi_gate_loop_np`, `csi_gate_ranked_np` (track I).
M19. `inlAnnot` from `CodeOK` is FALSE (2.e): `Annot.direct` lacks the
    return of the formula part that `+inlined` drops.  Restated on
    `CodeOKS` / `AnnotS` (`Glue/InlineAnnot.lean`); the analysis must give
    `InvBS`.
M20 (eighth pass, track I [281]). `runLC` / `runLCM` do NOT cover SOFT
    calls (`CallEnv.sof`): 6 of the 65 dumped `%done` member compiles
    (`%swap`, `%fld`, `%rot3`) take the soft-call path, so `refMono` /
    `refNary` at `finishLUCM` / `finishLFC` are false on them until the
    model has soft calls (track I's running session), and the classes
    (`inFragM`, `inFragN`) must exclude or model them.  Owner I.

## 10. OPEN LEAVES, in order of what blocks the most

1. The pill link of `+compile-unary` / `+compile-scc` read as `refMono`,
   `refNary`, `unary`, `scc` (1.3, 1.4, 2.a, 2.h): THREADED through cache
   misses (K: `CallOkT`, `CccMiss`), `csiFix` (cut, I), (f) on cell needs,
   `FixRet`, `+bake-need-ord` (A).  Tracks A, I, K.  Under it, NEW
   (eighth pass): `+run-shape` (3,284 cells, the member compile of
   `+compile-scc-in` in the modes `%must` / `%may`; no model, no link):
   track A since [273]; and the soft calls the model lacks (M20, I).
   NINTH PASS: `+tarjan` (`SccsLeafAt`, the miss path of `+scc-of`, the fuel
   bound of `inlinedM`): track Q since [291]; the soft members in the pill
   (`+soft-done`, `+soft-emit`, `mem_done_stepS`, `NM` decoding): track I.
2. `answers` / `RootAnswers` (2.h, 3.4): TOTALITY of the compile.  The
   sweep loop ends under `Ranked c` (`loop_total`); `Ranked` of the real
   member compile is argued, not proved (I); then totality of `+scc-of`,
   `runLCM` on analysis nomms, `+optimize` outside `FragX` (and on empty
   code, P's `OptLink` finding).  No owner for the totality as a whole.
3. `inFragM` / `inFragN` (2.b'): every compiled nomm in `MonoCalls` /
   `NaryCalls`; missing `%10`, `%11` (J, Q: M16), `%12`, `%mean`, memo
   keys, `%6` below the top (C: phase F needs a new relation), baking.
   Tracks C, J, K, Q.
4. `OptInMono` / `OptInNary`, `ReadsInMono` / `ReadsInNary` and
   `OptTotalMono` / `OptTotalNary` on the classes with calls (2.c, 2.d):
   track D in the `LRL` form (`ArmsL.cons` / `.n10` FALSE as stated, [293];
   `liveRun_plain_of_specs` from `SplitSpecL`, `IntoSpecL`), track H's
   input side.  ELEVENTH PASS: the four are THEOREMS on D's class `PlainM`
   / `PlainNC` (indirect calls, no `%6`, no direct call, no hint;
   integration 6e1dff4); with direct calls and `%6` they stay D's (`IL`
   false at `%6`, candidate `ATS6`).  `GuardMonoC` (2.c): a theorem on
   `NoSixM` from `KIMid` (track D: `kim_split`, `kim_into` proved; the run
   clause in the `GD` form checked, D's next step) and `ProxEnd` (the proxy
   facts after the top `+kerf`, open: track D or G; checked on 7 + 7,920)
   (`guardMonoC_noSixP`; `StraightA` is `straightA_of`).  `GuardNaryC`:
   not started (the map path of `+to-straight`).  TWELFTH PASS: on `PlainM` /
   `PlainNC` both entry leaves rest on `KIMid` alone (`entryMono_plainK`,
   `entryNary_plain`); on `NoSixM` `GuardMonoC` rests on `KIMid`,
   `KeyUndefC` (D) and `NskEndC` (G) (`guardMonoC_noSixN`).
5. `CgHalts` (3.1): M17 FIXED (dab8478, merged at [300]); on the fixed
   loop `CgHalts` is a hypothesis: the quiet-pass lemma, `FinPushes` from
   `FinIdents`, `FinBranch` / `KruskalBT`, the fuel of `+run` (track F).
   NEW OPEN QUESTION (track S, [301]): `split-max` in the sweep loop
   (`+msg-need-ord` is not monotone: the cut is applied in one branch
   only); a real cycle would make the sweep loop's totality false.
6. `pokeModel` (1.2): `OptLinkOn`, `JetRootLinkR`, `SccImage`, `SpRestAt`
   (1,120 cells), `PokeReachEnc`, the image of `enc` with M12: track P.
7. `GuardFinalU` / `GuardFinalF` (2.c): CLOSED in the sixth pass
   (`guardFinalU`, `guardFinalF`).  Left of `rawEntry`: the classes with
   calls.  EIGHTH PASS: `EntryMono` on a class with calls rests on
   `OptInMono` (D), `ReadsInMono` (D) and `GuardMonoC` (G: `NoPoison` and
   a cell annotation `CelAnn` of `finishLUCM` output; `mtl_kpa` proved, the
   other arms over `InvA` and the final passes open); `entryMono_of`,
   `entryNary_of`.  Tracks G, D.
8. `BakeEnds` (3.3): no measure.  NO OWNER.
9. `callee` (2.g): tracks I, J.
10. `inlAnnot` (2.e): model half PROVED (`inlAnnot_of`), two leaves:
    - `InvBS M lib` (the analysis gives `CodeOKS`: at every direct call
      with no memo key and a `+safe-fol-fol` formula part, that part
      returns; from the sock at the call knowing the formula, M19).  FALSE
      as stated (`invBS_false`: it quantifies over every `InvB` state); the
      truthful leaf `InvBSR` (reached states) is OPEN with NO OWNER since
      [302] (track F is on halting).
    - `InlPill lib D` (the pill half: on every `InvB` state `D.inl … b =
      some nm` gives `inlinedM (realOf long.code) calls hot single fuel b
      = some nm`).  NO OWNER (a new track N, [282]).  MAP (seventh pass):
      the arm is `0x5dde` of `K` (`Compiler/CompInlined.lean`, body cut by
      `tools/gen/inlined.py`); `inlBodyN` 1,311 cells = `inlGet` 21,
      `inlHit` 3, `inlMiss` 1,272 (`inlHot` 64, `inlGot` 24, `inlAfter`
      29, the trap `inlTrap` 1,134: cons 59, `%2` 324, `%3` 32, `%4` 32,
      `%5` 61, `%6` 90, `%7` 61, `%10` 63, `%11` 111, `%12` 61, `%mean`
      80).  Linked: `inl_body_at`, `inlBody_eq`, `inline_off_at`,
      `inl_trap_pure`, `inl_gate_miss`, `inl_gate_hit`, `inl_gate` (pure
      nomms under `InlOK`), `safe_fol_fol_pill`, `+scc-of` (K:
      `CompSccOfOne`, `ccc_scc_hit`, `CompSccOfAny`).  Missing: the `%2`
      branch with an `info` (`hot`, `+has:in` of `calls`, `+scc-of`, the
      recursion `inlined-loop` into the gate, by induction on the fuel,
      `+nomm-size` unlinked), the other branches on non-pure children, the
      cache coherence (every entry of `inl.cache` is `inlinedM` of its bell
      on the current table).  First: `inlWalk` equal to the `%2` branch,
      the fuel IH as the gate's own recursion.  K's `cu_gate_dir_scc` and
      `PGoodK` take `inl` as a parameter; `InlPill` ties it to `D.inl`.
11. `stable`, `jetRoot`, `jets`, `fast` (2.h): NO OWNER.
12. Format (7.2, 8): `RendRestTonFree`, `SoftTankUnit`, `SkipMsgTonFree`,
    `EvalMookSame`.  NO OWNER.
13. M5 (baked n-ary code): track A (bake model and `bn_gateB` exist; no
    real poke bakes).
14. M16 (hints, `runLCH`): J, Q, G; Q's `HintSound` derived from the
    table (`hintSound_of_tab`, [275]).
15. `PrintId` (1.4, M18): CLOSED (`printId_pill`, track I).
16. M20 (soft calls not in `runLC`, [281]): track I; the model now has them
    (`runLCS`, `finishLFCS`, [288], [294]); the pill step on soft members is
    left.

Leaves with NO owner (eleventh pass: `InvBSR`, the true form of the false
`InvBS`, since track F moved to halting; ninth pass: `InlPill` is track
Q's since [286]): 2.h `answers` (totality beyond I's
loop), `stable`, `jetRoot`, `jets`, `fast`, 3.3 `BakeEnds`, 3.4
`RootAnswers`, 7.2 and 8 (four format leaves).  Taken in the fourth pass:
2.c `GuardMonoX`, `GuardNaryX` (track G).  M5 is track A's since
2026-11-27.  Owned since the first pass: 1.2, 1.6, M11, M12 to M14 (track
P).  Closed since the first pass: M3, M8 (both arms), `hinj`, 1.1 (`enc`),
4.1 / `invStart` (`invStart_cor`, `gap_of_armPM`), 6, 7.1, M15 (fourth
pass).  Reduced in the third pass: `rawEntry` on `FragX` to `GuardMonoX`,
`GuardNaryX`; in the fourth: those two to the run-level induction and
`+to-straight`.  Found false since the third pass: P's `JetRootLink` and
`OptLink` as stated (restated), C's `RunOKLS` in phase F, and (sixth pass)
`halting` itself (M17: `CgHalts`, `EvFrozen`, `FinPushes` false of the
compiler as it is).  Closed in the sixth pass: 2.c on `FragX` (no guard
leaf).  Corrected in the sixth pass: `PrintId` is true of the pill (M18).
