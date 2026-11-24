The switch to the pill of af5cc39
=================================

The Hoon commit af5cc39 changes one arm, +crash-need of the door of +comp:
its fill no longer writes the register that holds the atom.  The pill
changes from sha256 76ea362e..., 793,137 bytes (Hoon at 1813f09) to sha256
b041a7ca..., 793,205 bytes (Hoon at af5cc39).  Branch
dozreg/formalization-ska-pill2, commits 5cdf801 (the regenerated files),
57e1a73 (the model), 11cfa2e (the links), cb79826 (a new guard), and the
commit of this note.

Hash names that changed
-----------------------

49 names, one pair per line, old name then new name.  3 are helper nouns
of lemmas/Pill/Arm/Comp.lean (comp.h...), 46 are bulk nouns of
lemmas/Pill/Nouns/P013.lean and P014.lean (nh...).  A pair marked * is a
noun whose own content changed; every other new noun is the old one with
its parts renamed by this same list (checked by walking both nouns, the
helpers expanded).  The helpers of Comp.lean are parts of the battery of
the door that hold +crash-need: comp.h4a9969705bb3 at door axis 6,
comp.hc84d4d9497c4 at 53, comp.h5a56e6ccb9f1 at 13655.

comp.h5aea88270577 comp.hc84d4d9497c4
comp.hba38ce3a6468 comp.h4a9969705bb3
comp.hdc09cd4df80a comp.h5a56e6ccb9f1   *
nh0017724b4518 nh88e1806e12d0
nh0b46c03be951 nhc118376bf91a
nh1107ecd32627 nhb956e3c30912
nh1c5e13aa3e55 nheef2f8393a62
nh26615bc16076 nhb8e43fc45e4f   *
nh2a19b391072d nh5b16f3ec568c
nh2f7618397fea nh4823b63b21c6
nh3cbfa0f354fd nh81fb3eb8422c
nh462b8d7643e7 nh32c1822f7e0f
nh533947b4f1d2 nh5c4a78cd8d6a
nh53ad2f19f110 nh7aba986f6ec7
nh544abbad6fa8 nh26165e661271
nh551e995603e9 nha199626bb59a
nh58984ad6cdbd nh6e49f3724ff1
nh58fd62bc0f79 nhc281f4bb0556   *
nh5917569ab57e nhc4a4015e6269
nh5e40544608f8 nhcdbe4bee147b
nh70706708267e nh4efe1e6a9381
nh726373f40abe nh358c83558da3
nh7356eda9a6cd nh11ccf4db33b1
nh7394a78973b1 nh25fd0aa288ed
nh7e2d3c2ae8f1 nhf25a78e05ad4
nh7e88654d3427 nhf540b1031d53
nh7fd175c9f72e nh27ddfe873bcc
nh8f220f8ba103 nh332bec2ffb23
nh942bd41d3fd5 nh80f5232f0e23
nh95216dda20ce nhf3f3a62a8303
nh9e8818bbc89a nh87b386b39017
nha931d30ea2e5 nhc453aa43c9a2
nhae6ee67a6e04 nhd0bed13e43e8
nhb68ff0ff5299 nh258d2d6e6829
nhb7aa1466df71 nhd914965c25ef
nhbcd980201e15 nh8442931ba93a
nhc5b6e91b2b76 nh47c58a0a0766
nhc6072d395fc8 nh17f8dfee5d8c
nhc7ffeb36eed9 nh2c8c9c6b5a53
nhcc9ee5e7ba22 nh6ca9f76c6c7a
nhd3b778e0da35 nhb5474b665d7c
nhdcddefc00bbf nh5e867c500267
nhe0849c310536 nh96f3de701458
nhea4115f9383e nhb1458986b825
nheef47532c119 nh0450db1bd84a
nhf36d3d5d1dee nh1c404321d03c
nhf4192283fc0a nh0ff8f599c95a
nhf4e35d52d9f0 nh34d02a29f5a0
nhfe4ab3bbd021 nhefca341e11b8

What the marked nouns are:

comp.hdc09cd4df80a: the part of the door's battery at axis 13655, whose
head is the arm +crash-need (door axis 27310); the Nock of +crash-need is
new (a +murn over +flatten-need with a gate that skips the atom's
register, in place of the +turn).
nh58fd62bc0f79: the Hoon of +crash-need inside the type of the door that
the pill holds.
nh26615bc16076: a part of the optimizer's arm +get-idom (axis 44 of optC)
that holds a %fork type of the door; the fork set changed order because
the member types changed.  This is why the optimizer's battery
nh58984ad6cdbd (now nh6e49f3724ff1) changed name, though no arm of the
optimizer changed in the Hoon.

New names with no old counterpart: comp.h2a90c4a04817 (the pull
[9 25030634 0 4194303] of +murn, which +crash-need now shares with another
arm of the door), nh5c49f18fae22, nhc6b0de3224e7 (parts of the new type).
Names that stay: every named noun (comp.door, whose content changed at
+crash-need, comp.*.arm, cor, ana, interp, core, trap, root, layer*, the
arms of Facts.lean); nh3d89e8d5f4f5 (the battery of K) and
nh15c74912d225 (the battery of compTypes) are unchanged, so compK and
compTypes keep their definitions.  nhdf8bb6f4032e
keeps its name and content; its text now names the new shared part
nh5c49f18fae22.  No axis moved.

Before the switch, the only old name used outside lemmas/Pill was
nh58984ad6cdbd (lemmas/Compiler/OptLinkBase.lean, tools/gen/optlink.py,
README.md).

Files edited by hand
--------------------

lemmas/Ska/CompModel.lean: crashNeed on a register atom (Sum.inr p) fills ((flattenNeed ned).filter (· != p)).map imm0, the immediate case unchanged; new lemma crashFill_sub (that fill is a sublist of the old one).
lemmas/Ska/CompBelowRun.lean: keeps_crashNeed, register branch, goes through crashFill_sub.
lemmas/Ska/CompAboveRun.lean: keepsA_crashNeed, register branch, goes through crashFill_sub.
lemmas/Ska/CompFootRun.lean: wr_crashNeed, register branch, goes through crashFill_sub.
lemmas/Ska/CompCollapseGate.lean: the witness list of collapseGate_crash is the filtered fill.
lemmas/Compiler/CompMedeLink.lean: crnG, crnBat, crnArm are the new Nock of +crash-need (written out by a walk from slot 27310 of comp.door that reproduces the old nouns exactly; no script of tools/gen made them); new crnFill, crnF, crn_filterMap, crn_murn_arm; crn_fill restated over +murn (below); comp_crash_need keeps its statement.
lemmas/Compiler/OptLinkBase.lean: optC is C nh6e49f3724ff1 compK (was nh58984ad6cdbd), definition and header.
tools/gen/optlink.py: the battery's name in the docstring only (the script reads optC by axis).
lemmas/Ska/CompWhole.lean: two new #guards on [10 [6 0 1] 5 [0 6] 0 1] (finishLU, finishLF), dumped by the new tools/hoon/crashdump.hoon.
README.md: the pill's sha256, size and commit, the cue numbers, the battery name of optC, the row of CompMedeLink.lean.
tools/hoon/README.md: crashdump.hoon, and ssacheck.hoon on af5cc39.

The statement that changed: crn_fill (CompMedeLink.lean).
  old: crn_fill (ned : Need) (bc : Noun) :
         nock (C turn.battery (C (C (listNoun A (flattenNeed ned))
           (C crnG (C (A 0) bc))) layer2)) turn.battery
         = some (listNoun Pole.toNoun ((flattenNeed ned).map fun y => Pole.imm (A 0) y))
  new: crn_fill (atom : Sum Nat Nat) (ned : Need) (B o rest : Noun) :
         nock (C murn.battery (C (C (listNoun A (flattenNeed ned))
           (C crnG (C (A 0) (C B (C (C o (C (crnAtomNoun atom) ned.toNoun)) rest)))))
           layer2)) murn.battery
         = some (listNoun Pole.toNoun (crnFill atom ned))
The definition crashNeed changed as above; no theorem statement that
mentions crashNeed changed.

Merging files written against the old pill
------------------------------------------

A mechanical rename is enough for a file that names these nouns only as
references: run a whole-word sed of the 49 pairs above (for example
sed -E 's/\bnh58984ad6cdbd\b/nh6e49f3724ff1/g' per pair) over the new
files, never over lemmas/Pill (regenerated).  Of the old names, a file
written by hand is likely to meet only nh58984ad6cdbd (the optimizer's
battery, as in optC); a kernel_rfl fact on a renamed noun holds of the new
noun, except for the three marked ones, where the content differs.

A rename is not enough, and the file must be fixed by hand, when it:
1. writes out Nock that contains +crash-need (a copy of the old crnBat or
   crnG, or of slot 27310 of comp.door): take the new nouns from
   CompMedeLink.lean;
2. uses crn_fill (new arguments and conclusion, above) or reads crnG as
   the old +turn gate;
3. unfolds crashNeed on a register atom and expects the fill
   (flattenNeed ned).map (fun x => Pole.imm (A 0) x): the fill is now the
   filtered list; crashFill_sub gives the old facts on it (RegsIn, OpsWr
   and the like, as keeps_crashNeed does);
4. states a #guard whose blocks contain a crash block of +crash-need on a
   register (cel a followed by imm 0 a): the new model drops the imm 0 a,
   so the guard must be dumped again from the compiler of af5cc39;
5. relies on the content of a marked noun (comp.hdc09cd4df80a, which
   holds +crash-need, the type nh58fd62bc0f79, the part nh26615bc16076
   of +get-idom).
None of the files on this branch other than those listed above needed
more than the rename.
