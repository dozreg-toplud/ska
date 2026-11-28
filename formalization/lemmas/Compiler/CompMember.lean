import lemmas.Compiler.CompSureOf

/-!
# The gate `member` of `+compile-scc-in` on its final pass

The gate `member` (`%compile-scc-fn`, axis `358182910` of `K`, `mem_at`, its
body `memBody`) is built in `+compile-scc-in` on the subject `memCtx`:
`[done kids map-local csi [[scc long-ska jets-hot cache] K]]`, the pushes of
`done`, `kids` and `=|  map-local` on the core of `+compile-scc-in`.  Its
sample is `[b mode keep map-local top cache]` (`memSam`).  The body, cut by
`tools/gen/member.py`:

1. `done` is pushed as `=(%done mode)`, then `?>  ?=(^ less.b)`;
2. `memComp`: the door `comp` (`+comp`, arm `5590` of `K`, on `[scc long-ska
   jets-hot map-local top b]`), `memDoor`;
3. `memInl`: `(inlined b long-ska jets-hot cache)` (arm `0x5dde` of `K`,
   `inl_at`, its body `inlBody` left as a slot of the pill), and the `=^`
   into the gate's `cache` (`memR2`);
4. the `=|` of `gen` and `=.  cache.gen  cache` (as in `+compile-unary`,
   `cu_entry_step`);
5. `memRes`: the `!@` of `dedicated-shape-pass`, `?.  done`, whose `&`
   branch `memFinal` is the final pass: `mode.gen` set to `%run` (already
   so), `memRun` (`+run` on `[| nomm [%done ~] ~ ~]`), `memCs`
   (`+collapse-shape`), `memBak` (`+bake-need`), `memSur` (`+sure-of`
   of `[(need-to-ordered ned.sure.laz) lok.sure.laz]`) and `memTuple`
   (`[[need-new laz ned-final bak o sur] gen]`);
6. `memAfter`: the `=^` of `res`, `=.  cache  cache.gen`, `memWas`
   (`+get:by` of `sure.cache` at `b`), `memSurK`, `memPut` (`+put:by` of
   `sure.cache`), `memMoved` (`+fall`), the push of `finish` (`finArm`),
   and `memProd`: `s-previous` (`+get:by` of `map-local`), then `memNew`
   on `~`, `memOld` otherwise.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The branch of the shape passes (`?.  done`), not run on the final pass. -/
def memShape : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 0xabee) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f64) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7473756d)) (C (A 0) (A 1018)))) (C (C (A 8) (C (C (A 9) (C (A 0x15d7a) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 4080)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x2eeeb) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 4080)))) (C (A 0) (A 2))))))))))) (C (A 8) (C (C (A 9) (C (A 1398) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 4088)))) (C (A 0) (A 2)))))))))) (C (C (C (A 0) (A 2)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 0x2bae) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 8176)))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 14)))))))))))))

/-- `(~(run comp gen) | nomm [%done ~] ~ ~)`. -/
def memRun : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 3071) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 1)))) (C (C (A 0) (A 14)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f64) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))))))) (C (A 0) (A 2))))))))))

/-- `(~(collapse-shape comp gen) nex cape.less.b)`. -/
def memCs : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 0) (A 30)) (C (A 9) (C (A 1526) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 4080)))) (C (A 0) (A 2))))))))))

/-- `(bake-need ned-final less.b)`. -/
def memBak : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x5ddd4) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 0) (A 4088)))) (C (A 0) (A 2))))))))

/-- `(sure-of [(need-to-ordered ned.sure.laz) lok.sure.laz] cape.less.b)`. -/
def memSur : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2bae) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 232))) (C (A 0) (A 2)))))))) (C (A 0) (A 105))))) (C (A 0) (A 0x3ff0)))) (C (A 0) (A 2))))))))

/-- `[[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]`. -/
def memTuple : Noun :=
  (C (C (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 58)) (C (C (A 0) (A 28)) (C (C (A 0) (A 6)) (C (C (A 0) (A 59)) (C (A 0) (A 2))))))) (C (A 0) (A 62)))

/-- The `=^` of `+collapse-shape`, `bak`, `sur` and the tuple. -/
def memF3 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C memBak (C (A 8) (C memSur memTuple))))))))

/-- The `=^` of the run, then `+collapse-shape` and the rest. -/
def memF2 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C memCs memF3))))))))

/-- The final pass: `mode.gen` set to `%run`, the run and the rest. -/
def memFinal : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 46) (C (A 1) (A 0x6e7572))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C memRun memF2))))))

/-- The `!@` of `dedicated-shape-pass`: `?.  done` with the shape passes and the final pass. -/
def memRes : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 0) (A 30)) (C memFinal memShape)))))

/-- `was`: `(~(get by sure.cache) b)`. -/
def memWas : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fdff))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1020))) (C (A 0) (A 2))))))))

/-- `sur`: `?:(&(keep ?=(^ was)) u.was sur)`. -/
def memSurK : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 0) (A 4086)) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 5)) (C (A 0) (A 223)))))

/-- `=.  sure.cache  (~(put by sure.cache) b sur)`. -/
def memPut : Noun :=
  (C (A 10) (C (C (A 0x7fdff) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffdff))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4092)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

/-- `moved`: `!=(sur (fall was [%none ~]))`. -/
def memMoved : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 8) (C (C (A 9) (C (A 3007) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))))) (C (A 0) (A 2)))))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))

/-- The product when `map-local` has no straight of `b`. -/
def memNew : Noun :=
  (C (C (A 6) (C (C (A 0) (A 14)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 252))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 504)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 505)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7ffc)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 5)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffee))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7ffc)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 0x3ffdf))))

/-- The product when `map-local` has a straight of `b`. -/
def memOld : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2baf6) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 508)) (C (C (A 0) (A 26)) (C (A 0) (A 0x1fff0))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (C (A 6) (C (C (A 0) (A 30)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 26)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffee))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0xfffc)) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 508)))) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 0) (A 2))))))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 0x7ffdf))))))))

/-- `s-previous`: `(~(get by map-local) b)`. -/
def memSprev : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffee))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffc))) (C (A 0) (A 2))))))))

/-- After the push of `finish`: `s-previous` and the product. -/
def memProd : Noun :=
  (C (A 8) (C memSprev (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C memNew memOld)))))

/-- After the final pass: the `=^` of `res`, the `sure.cache` updates, the push of `finish`, the product. -/
def memAfter : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 8159) (C (A 0) (A 1790))) (C (A 0) (A 1)))) (C (A 8) (C memWas (C (A 8) (C memSurK (C (A 7) (C memPut (C (A 8) (C memMoved (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C finArm memProd))))))))))))))))))

/-- After the `=.  cache.gen  cache`: the final pass and the rest. -/
def memR3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C memRes memAfter))))))

/-- `(inlined b long-ska jets-hot cache)`. -/
def memInl : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5dde) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 8186)) (C (C (A 0) (A 0x3ff6)) (C (A 0) (A 2015)))))) (C (A 0) (A 2))))))))))

/-- The `=^` of `+inlined`, the `=|` of `gen`, `=.  cache.gen  cache`. -/
def memR2 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 2015) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 1) cuBunt) (C (A 7) (C (C (A 10) (C (C (A 766) (C (A 0) (A 4063))) (C (A 0) (A 1)))) memR3))))))))

/-- After the push of `comp`: `+inlined` and the rest. -/
def memR1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C memInl memR2))))

/-- `(comp scc long-ska jets-hot map-local top b)`. -/
def memComp : Noun :=
  (C (A 8) (C (C (A 9) (C (A 5590) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2044)) (C (C (A 0) (A 4090)) (C (C (A 0) (A 8182)) (C (C (A 0) (A 494)) (C (C (A 0) (A 990)) (C (A 0) (A 60)))))))) (C (A 0) (A 2))))))))

/-- The gate body of `member`. -/
def memBody : Noun :=
  (C (A 8) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 26)))) (C (A 6) (C (C (A 3) (C (A 0) (A 56))) (C (C (A 8) (C memComp memR1)) (C (A 0) (A 0)))))))

/-- Its sample bunt. -/
def memBunt : Noun :=
  (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0x656e6f64) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))

/-- Its `%fast` hint. -/
def memHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6e662d6363732d656c69706d6f63) (C (C (A 0) (A 0xfffff)) (A 0))))) (C (A 0) (A 1))))


/-- The arm `member` in `+compile-scc-in`. -/
def memArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) memBunt) (C (C (A 1) memBody) (C (A 0) (A 1))))) memHint)

/-- `member` in `K`, inside the arm `+compile-scc-in` (arm `2732`). -/
theorem mem_at : slot? 358182910 compK = some memArm := by kernel_rfl

/-- The sample bunt of `+inlined`. -/
def inlBunt : Noun :=
  (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))

/-- Its `%fast` hint. -/
def inlHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x64656e696c6e69) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))


/-- The arm `+inlined` of `K` (arm `0x5dde`), not linked. -/
noncomputable def inlArm : Noun := (slot? 0x5dde compK).getD (A 0)
/-- Its gate body. -/
noncomputable def inlBody : Noun := (slot? 109 inlArm).getD (A 0)

theorem inl_at : slot? 0x5dde compK
    = some (C (A 7) (C (C (A 8) (C (C (A 1) inlBunt) (C (C (A 1) inlBody) (C (A 0) (A 1))))) inlHint)) := by
  kernel_rfl

/-! ## The subjects -/

/-- The sample of `member`: `[b mode keep map-local top cache]`. -/
def memSam (B MODE KEEP ML TOP CACHE : Noun) : Noun := C B (C MODE (C KEEP (C ML (C TOP CACHE))))

/-- The context of `member` in `+compile-scc-in`: `done`, `kids` and
`map-local` pushed on the core `[csi [[scc long-ska jets-hot cache] K]]` of
`+compile-scc-in`. -/
def memCtx (DN KIDS ML0 CB SCC LONG JH CACHE0 : Noun) : Noun :=
  C DN (C KIDS (C ML0 (C CB (C (C SCC (C LONG (C JH CACHE0))) compK))))

/-- The context of the door `comp`: the gate `+comp` with the sample
`[scc long-ska jets-hot map-local top b]`. -/
def memDCtx (SCC LONG JH ML TOP B : Noun) : Noun := C cgBat (C (C SCC (C LONG (C JH (C ML (C TOP B))))) compK)

/-- The subject after the push of `done` on the final pass (`mode` is
`%done`), with the gate's `cache` at `CACHE`. -/
def memS0 (B KEEP ML TOP CACHE CTX : Noun) : Noun :=
  C (A 0) (C memBody (C (memSam B (A 0x656e6f64) KEEP ML TOP CACHE) CTX))

/-- The subject after the `=^` of `+inlined`: the nomm, the door, `memS0`. -/
def memS3 (NM DCTX S0 : Noun) : Noun := C NM (C (C comp.door (C cuBunt DCTX)) S0)

/-! ## The entry -/

/-- The `=|` of `gen` and `=.  cache.gen  cache`: the subject `S` with
`cache` at axis `2015` becomes `[genNoun genEntry (cuRest cache) S]`. -/
theorem mem_entry_step (S R cache : Noun) (hc : slot? 2015 S = some cache) :
    nock S (C (A 8) (C (C (A 1) cuBunt) (C (A 7) (C (C (A 10) (C (C (A 766) (C (A 0) (A 4063)))
      (C (A 0) (A 1)))) R))))
      = nock (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest cache)) S) R := by
  simp only [nock_exec, hc, Option.bind_some]
  rfl

/-- **From the gate to the final pass**: `done`, the `?>`, the door `comp`,
`+inlined` (the hypothesis `hinl`: it returns `[NM CA]`), the edit of the
gate's `cache` to `CA`, the `=|` of `gen` and `=.  cache.gen  cache`. -/
theorem mem_entry (B KEEP ML TOP CACHE DN KIDS ML0 CB SCC LONG JH CACHE0 NM CA : Noun)
    (hb : ∃ c d f, B = C (C c d) f)
    (hinl : nock (C inlBody (C (C B (C LONG (C JH CACHE))) compK)) inlBody = some (C NM CA)) :
    nock (C memBody (C (memSam B (A 0x656e6f64) KEEP ML TOP CACHE) (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))
        memBody
      = nock (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA))
          (memS3 NM (memDCtx SCC LONG JH ML TOP B)
            (memS0 B KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))) memR3 := by
  obtain ⟨c, d, f, rfl⟩ := hb
  have he := mem_entry_step (memS3 NM (memDCtx SCC LONG JH ML TOP (C (C c d) f))
    (memS0 (C (C c d) f) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) memR3 CA
    (by simp [memS3, memS0, memSam, nock_exec])
  rw [← he]
  have hia := inl_at
  have hca := cu_comp_at
  conv => { lhs; arg 2; unfold memBody }
  simp only [memS3, memS0, memSam, memCtx, memDCtx]
  generalize compK = KC at hia hca hinl ⊢
  simp [nock_exec, memComp, memR1, memInl, memR2, hia, hca, cu_cg_slam, hinl, inlHint, eqCode_self]

/-! ## The `=^` of `res` and the test `?.  done` -/

/-- `memR3`: the pass, then `memAfter` on its product. -/
theorem mem_r3 (S : Noun) : nock S memR3 = (nock S memRes).bind fun R => nock (C R S) memAfter := by
  unfold memR3
  generalize memRes = RS
  generalize memAfter = AF
  simp [nock_exec]

/-- On the final pass (`done`, axis `30`, is `&`), `memRes` is `memFinal`. -/
theorem mem_res (GN NM DCTX B KEEP ML TOP CA CTX : Noun) :
    nock (C GN (memS3 NM DCTX (memS0 B KEEP ML TOP CA CTX))) memRes
      = nock (C GN (memS3 NM DCTX (memS0 B KEEP ML TOP CA CTX))) memFinal := by
  conv => { lhs; arg 2; unfold memRes }
  generalize memFinal = F
  generalize memShape = SH
  simp [nock_exec, memS3, memS0]

/-! ## The calls of the final pass -/

/-- The run: `(~(run comp gen) | nomm [%done ~] ~ ~)` is the `$` arm of
`+run` on the door with `gen`. -/
theorem mem_run_call (GN NM DCTX S0 : Noun) :
    nock (C GN (memS3 NM DCTX S0)) memRun
      = nock (crSubj (A 1) NM (C (A 0x656e6f64) (A 0)) (A 0) (A 0) (C comp.door (C GN DCTX))) crDol := by
  have hr := comp_run_at
  unfold memS3
  conv => { lhs; arg 2; unfold memRun }
  generalize comp.door = Dr at hr ⊢
  simp [nock_exec, hr, crArm, crB, crBat, crSubj]

/-- `+collapse-shape` of the door with `gen` on `[nex cape.less.b]`. -/
theorem mem_cs_call (NEXN G1N NM DCTX CAPE DATA FOL KEEP ML TOP CA CTX : Noun) :
    nock (C NEXN (C G1N (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA CTX)))) memCs
      = nock (C csBody (C (C NEXN CAPE) (C comp.door (C G1N DCTX)))) csBody := by
  have hc := cs_at
  unfold memS3 memS0 memSam
  conv => { lhs; arg 2; unfold memCs }
  generalize comp.door = Dr at hc ⊢
  simp [nock_exec, hc, csHint]

/-- `+bake-need` of `ned-final` and `less.b`. -/
theorem mem_bak_call (NF LZ O NEXN G2 NM DCTX CAPE DATA FOL KEEP ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 : Noun) :
    nock (C (C NF (C LZ O)) (C NEXN (C G2 (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))) memBak
      = nock (C bnBody (C (C NF (C CAPE DATA)) compK)) bnBody := by
  have hb := bn_at
  unfold memS3 memS0 memSam memCtx
  unfold memBak
  generalize compK = KC at hb ⊢
  simp [nock_exec, hb, bn_arm]

/-- `+sure-of` of `[(need-to-ordered ned.sure.laz) lok.sure.laz]` and
`cape.less.b`. -/
theorem mem_sur_call (BAK NF LNED LLOK LREST O NEXN G2 NM DCTX CAPE DATA FOL KEEP ML TOP CA DN KIDS ML0 CB SCC LONG
    JH CACHE0 : Noun) :
    nock (C BAK (C (C NF (C (C (C LNED LLOK) LREST) O)) (C NEXN (C G2 (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))) memSur
      = (nock (C ntaBody (C LNED compK)) ntaBody).bind fun NO =>
          nock (C soBody (C (C (C NO LLOK) CAPE) compK)) soBody := by
  have hs := so_at
  have hn := nta_at
  unfold memS3 memS0 memSam memCtx
  unfold memSur
  generalize compK = KC at hs hn ⊢
  cases e : nock (C ntaBody (C LNED KC)) ntaBody with
  | none => simp [nock_exec, hs, hn, so_arm, ntaHint, e]
  | some NO => simp [nock_exec, hs, hn, so_arm, ntaHint, e]

/-- The tuple `[[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]`. -/
theorem mem_tuple_call (SUR NEDB IMM NF LZ O NEXN G2 NM DCTX B KEEP ML TOP CA DN KIDS ML0 CB SCC LONG JH
    CACHE0 : Noun) :
    nock (C SUR (C (C NEDB IMM) (C (C NF (C LZ O)) (C NEXN (C G2 (memS3 NM DCTX
        (memS0 B KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))))) memTuple
      = (nock (C ntaBody (C NEDB compK)) ntaBody).map fun NN =>
          C (C NN (C LZ (C NF (C (C NEDB IMM) (C O SUR))))) G2 := by
  have hn := nta_at
  unfold memS3 memS0 memSam memCtx
  unfold memTuple
  generalize compK = KC at hn ⊢
  cases e : nock (C ntaBody (C NEDB KC)) ntaBody with
  | none => simp [nock_exec, hn, ntaHint, e]
  | some NN => simp [nock_exec, hn, ntaHint, e]

/-! ## The final pass -/

/-- **The final pass of `member`** (`memFinal`, the `&` branch of `?.  done`)
from the subject `[gen S3]`, given the products of the calls as nouns: the
run (`hrun`), `+collapse-shape` (`hcs`), `+bake-need` (`hbn`, nothing
baked), `+need-to-ordered` of `ned.sure.laz` (`hn1`), `+sure-of` (`hso`) and
`+need-to-ordered` of `ned-final` (`hn2`).  It returns `[res gen]`, the
tuple `[need-new laz ned-final bak o sur]` and the state after
`+collapse-shape`. -/
theorem mem_final (GN NM DCTX CAPE DATA FOL KEEP ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 : Noun)
    (NEXN G1N NF LNED LLOK LREST O G2 NO SUR NN : Noun)
    (hmode : edit? 46 (A 0x6e7572) (C GN (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))
      = some (C GN (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
    (hrun : nock (crSubj (A 1) NM (C (A 0x656e6f64) (A 0)) (A 0) (A 0) (C comp.door (C GN DCTX))) crDol
      = some (C NEXN G1N))
    (hcs : nock (C csBody (C (C NEXN CAPE) (C comp.door (C G1N DCTX)))) csBody
      = some (C (C NF (C (C (C LNED LLOK) LREST) O)) G2))
    (hbn : nock (C bnBody (C (C NF (C CAPE DATA)) compK)) bnBody = some (C NF (A 0)))
    (hn1 : nock (C ntaBody (C LNED compK)) ntaBody = some NO)
    (hso : nock (C soBody (C (C (C NO LLOK) CAPE) compK)) soBody = some SUR)
    (hn2 : nock (C ntaBody (C NF compK)) ntaBody = some NN) :
    nock (C GN (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))) memFinal
      = some (C (C NN (C (C (C LNED LLOK) LREST) (C NF (C (C NF (A 0)) (C O SUR))))) G2) := by
  conv => { lhs; arg 2; unfold memFinal }
  simp [nock_exec, memF2, memF3, hmode, mem_run_call, hrun, mem_cs_call, hcs, mem_bak_call, hbn, mem_sur_call, hn1,
    hso, mem_tuple_call, hn2]

/-! ## After the final pass: the updates of `sure.cache` and the push of `finish` -/

/-- `sur` of `member` after the pass: `u.was` when `keep` and `was` is
`[~ u]`, the `sur` of the pass otherwise. -/
def memSurKN (keep : Bool) (WAS SUR : Noun) : Noun :=
  if keep then (match WAS with | Noun.cell _ u => u | _ => SUR) else SUR

/-- `(fall was [%none ~])`. -/
def fallNone (WAS : Noun) : Noun :=
  match WAS with
  | Noun.cell _ u => u
  | _ => C (A 0x656e6f6e) (A 0)

/-- `moved`: `!=(sur (fall was [%none ~]))`. -/
def memMovedN (keep : Bool) (WAS SUR : Noun) : Noun :=
  if memSurKN keep WAS SUR = fallNone WAS then A 1 else A 0

/-- The cache `[nary mono sccs inl sure]`. -/
def cacheN (C1 C2 C3 C4 SURE : Noun) : Noun := C C1 (C C2 (C C3 (C C4 SURE)))

/-- **From the end of the final pass to the push of `finish`**: the `=^` of
`res` into `gen`, `=.  cache  cache.gen` (the cache of the state `G2`, with
`sure.cache` at `SURE`), `was` (`+get:by` of `sure.cache` at `b`, `hwas`),
`sur` (`memSurKN`), the put of `sur` at `b` (`hput`, the new `sure.cache`
`SURE'`), `moved` (`memMovedN`), and the gate `finish` pushed on the subject
`finCtx`: `moved`, `sur`, `was`, the tuple, `gen` and the rest, whose cache is
the new one. -/
theorem mem_after (NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 GN NM DCTX CAPE DATA FOL : Noun) (keep : Bool)
    (ML TOP CA0 C1 C2 C3 C4 SURE DN KIDS ML0 CB SCC LONG JH CACHE0 WAS SURE' : Noun)
    (hG2 : slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE))
    (hwas : getF mugF (C (C CAPE DATA) FOL) SURE = some WAS) (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C CAPE DATA) FOL) (memSurKN keep WAS SUR) SURE = some SURE') :
    nock (C (C (C NN (C LZ (C NF (C (C NEDB IMM) (C (A o) SUR))))) G2)
        (C GN (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) (loob keep) ML TOP CA0
          (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))) memAfter
      = nock (C (C finBody (C (A 0) (finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS NN LZ NF NEDB IMM
            o SUR G2 (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) (loob keep) ML TOP (cacheN C1 C2 C3 C4 SURE')
              (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
          (finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS NN LZ NF NEDB IMM
            o SUR G2 (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) (loob keep) ML TOP (cacheN C1 C2 C3 C4 SURE')
              (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))) memProd := by
  have hg := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _ hwas
  have hL := compK_layer2
  have hfa := fin_arm
  unfold memAfter memWas memSurK memPut memMoved
  unfold memS3 memS0 memSam memCtx finCtx cacheN at *
  generalize compK = KC at hL ⊢
  rcases hw with rfl | ⟨u, rfl⟩ <;> cases keep <;>
  simp only [memMovedN, memSurKN, fallNone, Bool.false_eq_true, ↓reduceIte] at hput ⊢ <;>
  have hp := put_gate layer2 gorIn_morIn_layer2 _ _ _ _ hput <;>
  (try split) <;>
  simp_all [nock_exec, by.arm_at, by_arm, by.get.arm_at, get_arm, by.put.arm_at, put_arm,
    fall.arm_at, fall_arm, fall_gate_nil, fall_gate_some, loob, nock_ite]

/-! ## The product -/

/-- `chg` with `top` empty: `moved`, or `need-new` is not `[%none ~]`. -/
def memChgN (MOVED NN : Noun) : Noun :=
  if MOVED = A 0 then A 0 else if C (A 0x656e6f6e) (A 0) = NN then A 1 else A 0

/-- **The product of `member`** when `map-local` and `top` are empty (the
final pass of an SCC of one bell): `s-previous` is `~`, and the gate returns
`[chg (~(put by ~) b (finish ~)) cache]`, with the straight of `finish ~`
(`hfin` gives it as a noun, `none` when `finish` crashes). -/
theorem mem_prod_new (MOVED SUR' WAS NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 NM DCTX CAPE DATA FOL KEEP
    CA DN KIDS ML0 CB SCC LONG JH CACHE0 : Noun) (hmv : MOVED = A 0 ∨ MOVED = A 1) (hnn : ∃ p q, NN = C p q) :
    nock (C (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP (A 0) (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
        (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP (A 0) (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
        memProd
      = (nock (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP (A 0) (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
          finBody).map fun ST => C (memChgN MOVED NN) (C (C (C (C (C CAPE DATA) FOL) ST) (C (A 0) (A 0))) CA) := by
  have hL := compK_layer2
  have hg0 := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (C (C CAPE DATA) FOL) (A 0) (A 0)
    rfl
  have hgut := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
    (C (C CAPE DATA) FOL) (C (A 0x656e6f6e) (A 0)) (A 0) (A 0) rfl (Or.inl rfl)
  simp only [if_true] at hgut
  generalize hF : finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP (A 0) (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = FC
  have hFC := hF
  unfold finCtx memS3 memS0 memSam memCtx at hFC
  obtain ⟨np, nq, rfl⟩ := hnn
  cases e : nock (C finBody (C (A 0) FC)) finBody with
  | none =>
    have hp := fun ST => put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) ST (A 0)
      (C (C (C (C CAPE DATA) FOL) ST) (C (A 0) (A 0))) rfl
    subst hFC
    unfold memProd memSprev memNew
    generalize compK = KC at hL e ⊢
    generalize finBody = FB at e ⊢
    rcases hmv with rfl | rfl <;>
    by_cases h1 : A 0x656e6f6e = np <;> by_cases h2 : A 0 = nq <;> (try subst h1) <;> (try subst h2) <;>
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg0, by.gut.arm_at, gut_arm, hgut,
      by.put.arm_at, put_arm, hp, e, memChgN, nock_ite, *]
  | some ST =>
    have hp := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) ST (A 0)
      (C (C (C (C CAPE DATA) FOL) ST) (C (A 0) (A 0))) rfl
    subst hFC
    unfold memProd memSprev memNew
    generalize compK = KC at hL e ⊢
    generalize finBody = FB at e ⊢
    rcases hmv with rfl | rfl <;>
    by_cases h1 : A 0x656e6f6e = np <;> by_cases h2 : A 0 = nq <;> (try subst h1) <;> (try subst h2) <;>
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg0, by.gut.arm_at, gut_arm, hgut,
      by.put.arm_at, put_arm, hp, e, memChgN, nock_ite, *]

end Compiler
end Formalization
