The switch to the pill of f7e95af
=================================

Two Hoon commits: ea6413d (`+mink` of hoon.hoon runs a dynamic hint whose tag
is a cell) and f7e95af (`+fol-loop` compiles such a hint as under the tag
`%$`).  The pill changes from sha256 b041a7ca..., 793,205 bytes (Hoon at
af5cc39) to sha256 75012450..., 793,354 bytes.

The generator changed with it: the pill is now made by the hoon.hoon it
holds.  The kernel of the harness (or of the ship) builds
`desk/sys/hoon.hoon`, and the gate that makes the pill is compiled against
that core and run in it (`desk/gen/steel-pill.hoon`; for the harness,
`steel-gen-own-hoon.vere.patch`).  The trap keeps the core that ran `+swat`,
so a pill made by the harness's own hoon.hoon held two hoon.hoons, whose type
nouns jam shared only while the two texts were the same: the first pill of
f7e95af, made the old way, was 799,710 bytes (sha256 8424a26c...).  Both
pills build the same core; only the trap differs.

Arms whose Nock changed: `mink.loop` (one cell test less) and the `$` of
`+fol-loop` (one case more).  Every other changed noun is a battery or a
quoted core that holds one of them, except the battery of `+hinted` (arm
`96116` of `K`): its source is the same, but `?=(hint-dynamic tag)` tests the
ten tags in another order (`hdBat` of `Compiler/CompPastLink.lean`).

Hash names that changed, among those the hand-written files use
---------------------------------------------------------------

One pair per line, old name then new name: the battery of the optimizer's
core (`optC`, slot 62 of `cor`) and the battery of `K` (`compK`, slot 126).

nh6e49f3724ff1 nhd6b9320ed1b6
nh3d89e8d5f4f5 nhe0b859c3d8aa
