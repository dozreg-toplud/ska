import lemmas.CueWords
import lemmas.KernelRfl

/-!
A kernel-checked run of `cue` on a small jam: a sub-noun of the steel pill
(sha256 5dbc617e...), jammed by tools/nouns.py.  The kernel evaluates `cue`
and compares the result with `root`.

The same check on the whole pill does not fit in memory: the kernel keeps
every intermediate term (3.4 GB for a noun of 2,000 cells, over 6 GB for 8,000).
-/

namespace Formalization
namespace CueExample

open Nock Nock.Words

def words0 : List Nat := [0x7b6bc059, 0xb9fc0793, 0x2379b333, 0xe4c5f018, 0x7c05e6e8, 0x7631b1b1, 0x8c6c5f01, 0x1c3c1e6e, 0xe6c2c5f0, 0x7b77c0ca, 0x10d773ab, 0x43c5c1c2, 0xd7f01bf0, 0x35e0d0e8, 0xcdf03f84, 0x1cec2d8, 0x6d8e6e9f, 0x631fc05e, 0xf01793a3, 0xe6e8e8d7, 0x7f01c7c1, 0x5d8c6dcc, 0x734bbfc0, 0xb6bc073b, 0x9435b3ba, 0x6be50da4, 0xf06c050d, 0x59435ab0, 0x50dc9c19, 0xaf943692, 0xda49435, 0x50d6be5, 0x6ab1706c, 0x1ba3bfc0, 0xc9f01763, 0x35e6e8e8, 0xc7c1b014, 0xc1b01436, 0x9250d6c9, 0x6c050d6, 0xb937b23c, 0x50f4050d, 0xa49437ee, 0x1b01435, 0x6d0e8d8f, 0xe1b1e9c3, 0xbc056944, 0xa37937b3, 0xb751c36c, 0x48437371, 0x86e38c36, 0xfa30ddd1, 0x6b14286b, 0x8f832b28, 0x86b89287, 0x793832b2, 0xce1de128, 0xfc70d583, 0x386d946c, 0x6e6e367e, 0x7186c908, 0x1bba30dc, 0x9c35840e, 0xe80a1b13, 0xe02fe0a1, 0x91b985cf, 0xf80d9b83, 0xf4647477, 0x1d1dfe02, 0xf086bcdd, 0x7461f80f, 0xb2876d6f, 0x610386ba, 0xd88390d, 0x19c38af9, 0xc0bc86b0, 0x386e66e0, 0x4e70d610, 0xb98fe02c, 0x912bcdd1, 0x436d5943, 0x590d671e, 0xd019c39f, 0x4b38f21a, 0x1bab286b, 0xd12b38f2, 0xd6d5943, 0x3c86c067, 0x56b21ace, 0x36a03387, 0xe43671e4, 0x5650d69e, 0x359c590f, 0xb487019c, 0xab21b50, 0x1b24121b, 0x4a1b02b2, 0xeb1386d2, 0x721d2070, 0x154f]
def words : List Nat := List.flatten [words0]
def n1718 : Noun := C (A 0x65736162) (A 0x6e756f6e)
def n12353 : Noun := C (A 0x6c636362) (C (C (A 0x73746362) (C (A 97) n1718)) (C (C (A 0x73746362) (C (A 98) n1718)) (A 0)))
def n1419 : Noun := C (A 0x65736162) (A 0x67616c66)
def n12430 : Noun := C (A 0x676e6977) (C (A 0x67756d) (A 0))
def n1231 : Noun := C (A 97) (A 0)
def n1232 : Noun := C (A 0x676e6977) n1231
def n12432 : Noun := C (A 0x6c636e63) (C n12430 (C n1232 (A 0)))
def n1246 : Noun := C (A 98) (A 0)
def n1247 : Noun := C (A 0x676e6977) n1246
def n1302 : Noun := C n1247 (A 0)
def n12439 : Noun := C (A 0x6c636e63) (C n12430 n1302)
def n1236 : Noun := C (A 0x676e6977) (C (A 99) (A 0))
def n11271 : Noun := C (A 0x676e6977) (C (A 100) (A 0))
def n1303 : Noun := C n1232 n1302
def n1301 : Noun := C (A 0x676e6977) (C (A 0x68746c) (A 0))
def n12454 : Noun := C (A 0x6c637477) (C (C (A 0x73747464) (C n1236 n11271)) (C (C (A 0x6c636e63) (C (C (A 0x676e6977) (C (A 0x726f64) (A 0))) n1303)) (C (A 0x6c636e63) (C n1301 (C n1236 (C n11271 (A 0)))))))
def n11179 : Noun := C (A 0x646e6173) (C (A 102) (A 0))
def n1221 : Noun := C (A 0x65736162) (C (A 0x6d6f7461) (A 0))
def n12357 : Noun := C (A 0x73747477) (C n1221 n1246)
def n4 : Noun := C (A 0) (A 2)
def n12360 : Noun := C (A 0x73746e63) (C (C n4 n1231) (A 0))
def n11297 : Noun := C (A 0x73746e63) (C (C n4 n1246) (A 0))
def n44 : Noun := C (A 0) (A 0)
def n13 : Noun := C (A 0) (A 3)
def root : Noun := C (A 0) (C (C (A 0x726f6d) (C (A 0x73666773) (C (A 0x726f6d) (C (A 0x73747262) (C n12353 (C (A 0x7068746b) (C n1419 (C (A 0x736c7374) (C (C (A 0x72746c63) (C (C (A 0x7374746b) (C (A 99) (C (A 0x6c636e63) (C n12430 (C n12432 (A 0)))))) (C (C (A 0x7374746b) (C (A 100) (C (A 0x6c636e63) (C n12430 (C n12439 (A 0)))))) (A 0)))) n12454))))))))) (C (C (C (A 0x726f67) (C (A 0x73666773) (C (A 0x726f67) (C (A 0x73747262) (C n12353 (C (A 0x7068746b) (C n1419 (C (A 0x736c7374) (C (C (A 0x72746c63) (C (C (A 0x7374746b) (C (A 99) n12432)) (C (C (A 0x7374746b) (C (A 100) n12439)) (A 0)))) n12454))))))))) (C (C (C (A 0x726f64) (C (A 0x73666773) (C (A 0x726f64) (C (A 0x73747262) (C n12353 (C (A 0x7068746b) (C n1419 (C (A 0x6c637477) (C (C (A 0x73747464) (C n1232 n1247)) (C n11179 (C (A 0x74647477) (C (C (A 0x73747477) (C n1221 n1231)) (C (C (A 0x6c637477) (C n12357 (C (C (A 0x646e6173) (C (A 102) (A 1))) (C (A 0x6c637477) (C (C (A 0x73747464) (C n12360 n11297)) (C (C (A 0x73746e63) (C n44 (C (C n1231 (C (A 0x73746e63) (C (C n13 n1231) (A 0)))) (C (C n1246 (C (A 0x73746e63) (C (C n13 n1246) (A 0)))) (A 0))))) (C (A 0x73746e63) (C n44 (C (C n1231 n12360) (C (C n1246 n11297) (A 0))))))))))) (C (A 0x74647477) (C n12357 (C n11179 (C (A 0x6c636e63) (C n1301 n1303)))))))))))))))))) n44) (A 0))) (A 0)))
theorem cue_words : cue words = some root := by kernel_rfl

end CueExample
end Formalization
