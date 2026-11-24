import lemmas.Compiler.FolLoopConv

/-!
# The `|%` core of `+ska-callgraph`

The core `K` in which `+analyze` and `+run` run is
`[K_bat [st' [cg_bat [cg_sample ana]]]]`: its battery `kc.k_bat` (K_bat) holds
`+pop` at slot `2`, `+cull` at `6`, `+above` at `14`, `+analyze` at `60`,
`+sweep` at `61`, `+dirty` at `62` and `+run` at `63`, so they are the arms
`4`, `10`, `22`, `92`, `93`, `94`, `95` of `K`.

The nouns here are printed by `tools/pill2lean.py` (the names `ska_cg.*` of
its next regeneration) and kept in this file until the nouns are regenerated;
`kc_bat_at` ties them to the pill: `K_bat` is the noun at axis `2799357` of
`ana`, inside the gate `+ska-callgraph` (arm `341` of `ana`).

`runRest_kc` gives the layout facts `hana`, `hK`, `hKa` of `FolLoopConv.lean`
for the rest of the trap's subject as `+run` builds it.  `above_gate`: the
gate `+above` computes `Ana.above` on every stack, in every context.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-! ## The nouns -/

def kc.above.battery : Noun := C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x6b636174732d616b73))) (C (A 0) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 26)))) (C (C (C (A 0) (A 12)) (C (A 1) (A 0))) (C (C (A 0) (A 26)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 13) (C (A 0) (A 27))) (C (A 0) (A 1))))))))))))
def kc.above.arm : Noun := C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0))) (C (C (A 1) kc.above.battery) (C (A 0) (A 1))))
def kc.cull.loop : Noun := C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 29))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1018)) (C (A 0) (A 60)))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 0) (A 13))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))))))
def kc.cull.gate : Noun := C (A 10) (C (C (A 510) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 7678))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 0) (A 13)))))))
def kc.cull.battery : Noun := C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 478)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (C (A 0) (A 28)) (C (A 1) (A 0))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) kc.cull.loop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 175) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 0) (A 125)) (C (A 7) (C (C (A 10) (C (C (A 0xfbfff) (C (A 8) (C (C (A 9) (C (A 36) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1fbfff)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 92) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 2014) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4062)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 8062) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 175) (C (A 10) (C (C (A 6) (C (A 0) (A 16254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 186) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 125))) (C (C (A 1) kc.cull.gate) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))))))))))))))
def kc.cull.arm : Noun := C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))))))))))) (C (C (A 1) kc.cull.battery) (C (A 0) (A 1))))
def kc.dirty.gate : Noun := C (A 8) (C (C (A 9) (C (A 38) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 65022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0) (A 0))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 3)))))) (C (A 0) (A 30)))) (C (A 0) (A 2)))))))
def kc.dirty.battery : Noun := C (A 8) (C (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 7678))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0) (A 0))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 0) (A 60)))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) kc.dirty.gate) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))))
def kc.dirty.arm : Noun := C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))))))))))) (C (C (A 1) kc.dirty.battery) (C (A 0) (A 1))))
def kc.pop.battery : Noun := C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 222)))) (C (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x6b636174732d616b73))) (C (A 0) (A 0)))) (C (A 0) (A 222))))))) (C (A 7) (C (C (A 10) (C (C (A 478) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 238) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 7678) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 15870))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 380) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x64696f76)) (C (A 0) (A 380)))) (C (C (A 1) (C (A 1) (A 0))) (C (A 0) (A 380)))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 122) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 246) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 84) (C (A 0) (A 511)))) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 502)) (C (C (A 0) (A 14)) (C (A 0) (A 6))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 60)))) (C (C (A 0) (A 61)) (C (A 9) (C (A 2) (C (A 0) (A 7))))))))))))))))))))))))))
def kc.pop.arm : Noun := C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))))))))))) (C (C (A 1) kc.pop.battery) (C (A 0) (A 1))))
def kc.sweep.gate : Noun := C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 502)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 0) (A 13))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))
def kc.sweep.loop : Noun := C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 57)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 29))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 0) (A 6)))) (C (A 0) (A 1)))))))) (C (A 8) (C (C (A 0) (A 114)) (C (A 8) (C (C (C (C (A 0) (A 120)) (C (A 0) (A 243))) (C (A 0) (A 61))) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 8186))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 2))) (C (A 0) (A 7)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 6)) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 0) (A 7))))))))))))))))))))
def kc.sweep.battery : Noun := C (A 8) (C (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) kc.sweep.gate) (C (A 0) (A 1))))) (C (A 8) (C (C (C (A 0) (A 28)) (C (A 1) (C (A 0) (A 0)))) (C (A 8) (C (C (C (C (A 0) (A 60)) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2))))))))) (C (A 1) (A 0))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) kc.sweep.loop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))))
def kc.sweep.arm : Noun := C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))))))) (C (C (A 1) kc.sweep.battery) (C (A 0) (A 1))))
def kc.k_bat : Noun := C kc.pop.arm (C kc.cull.arm (C kc.above.arm (C (C ska_analyze.arm kc.sweep.arm) (C kc.dirty.arm ska_run.arm))))

/-! ## Their place in the pill -/

/-- `K_bat` is the pill's: the noun at axis `2799357` of `ana`. -/
theorem kc_bat_at : slot? 2799357 ana = some kc.k_bat := by kernel_rfl

theorem kc_analyze_at : slot? 60 kc.k_bat = some ska_analyze.arm := by kernel_rfl

theorem kc_run_at : slot? 63 kc.k_bat = some ska_run.arm := by kernel_rfl

/-- The layout facts of `FolLoopConv.lean` for the rest of the trap's subject
that `+run` builds in the core `K`. -/
theorem runRest_kc (bus data runBat idn stK cgBat cgS : Noun) :
    slot? 511 (runRest bus data runBat idn kc.k_bat stK cgBat cgS) = some ana ∧
    slot? 31 (runRest bus data runBat idn kc.k_bat stK cgBat cgS)
      = some (C kc.k_bat (C stK (C cgBat (C cgS ana)))) ∧
    slot? 92 (C kc.k_bat (C stK (C cgBat (C cgS ana)))) = some ska_analyze.arm :=
  ⟨runRest_ana .., runRest_K .., runRest_Ka kc_analyze_at _⟩

/-! ## `+above` -/

theorem identNoun_eq_iff (a b : Ident) : identNoun a = identNoun b ↔ a = b :=
  ⟨TKey.enc_inj a b, fun h => h ▸ rfl⟩

/-- `+above`: the functions on the stack above and including `id`, latest
first, as `Ana.above`; it crashes when `id` is not on the stack.  It reads
nothing from its context `c`. -/
theorem above_gate (c : Noun) (id : Ident) : ∀ stk : List Ident,
    nock (C kc.above.battery (C (C (identNoun id) (listNoun identNoun stk)) c)) kc.above.battery
      = (Ana.above id stk).map (listNoun identNoun)
  | [] => by
    nock_open kc.above.battery
    simp [nock_exec, listNoun, Ana.above]
  | i :: stk => by
    have ih := above_gate c id stk
    nock_open kc.above.battery
    by_cases h : id = i
    · subst h
      simp [nock_exec, listNoun, Ana.above, eqCode]
    · have h' : identNoun id ≠ identNoun i := fun e => h ((identNoun_eq_iff _ _).1 e)
      simp [nock_exec, listNoun, Ana.above, eqCode, h, h', ih]
      cases Ana.above id stk <;> simp [listNoun]

end Compiler
end Formalization
