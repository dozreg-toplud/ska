The switch to the pill of f7e95af
=================================

Two Hoon commits: ea6413d (`+mink` of hoon.hoon runs a dynamic hint whose tag
is a cell) and f7e95af (`+fol-loop` compiles such a hint as under the tag
`%$`).  The pill changes from sha256 b041a7ca..., 793,205 bytes (Hoon at
af5cc39) to sha256 8424a26c..., 799,710 bytes.  6,369 of the 6,505 bytes are
the first divergence of `desk/sys/hoon.hoon` from the hoon.hoon of the
harness that builds the pill: the trap keeps the core of that hoon as the
context of `+swat`, and until now jam shared its type nouns with those of the
desk's hoon.hoon.

Arms whose Nock changed: `mink.loop` (one cell test less) and the `$` of
`+fol-loop` (one case more).  Every other changed noun is a battery or a
quoted core that holds one of them.

Hash names that changed, among those the hand-written files use
---------------------------------------------------------------

One pair per line, old name then new name: the battery of the optimizer's
core (`optC`, slot 62 of `cor`) and the battery of `K` (`compK`, slot 126).

nh6e49f3724ff1 nhd6b9320ed1b6
nh3d89e8d5f4f5 nhe0b859c3d8aa
