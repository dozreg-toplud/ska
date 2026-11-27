import lemmas.Compiler.CompSccOfAnyDefs
import lemmas.Compiler.PokeLinkGood

/-!
# `+compiled-mono` linked: `MonoLinkAt` from the gate of `+compile-unary` (README Gaps 19 (g))

`+compiled-mono` (arm `10` of axis `3` of the core, 125 cells with its gate, map
`tools/gen/monolink.py`) is the gate `[monoBat [bunt core]]` whose battery is
`[8 GET [6 TEST MISS HIT]]`: `s=(~(get by mono.cache.state) b)`; on a hit `[u.s cache.state]`;
on a miss the slam of `+compile-unary` (arm `2810` of `K`, axis `7` of the library) on
`[b scc [code jets calls]:long-ska jets-hot cache]`, the write of the cache it returns, and
`(~(put by mono.cache) b straight)`.

* `monoArm_eq`, `cuArm_at`: the two arms, kernel facts;
* `monoRaw_hit`: the arm on every encoded state, the hit; `MonoMissAt`: the miss, named;
* `cuG`, `cuResNoun`, `UnaryImageAt` (the gate's product on the encoded sample, when it returns,
  is the noun of a model result: a straight, a map of straights, a cache), `compileUnaryP` (the
  pill's `+compile-unary` read back, as `sccOfP` reads `+scc-of`);
* **`monoLinkAt_of`**: `MonoLinkAt` at a state from `UnaryImageAt` and `MonoMissAt` there, for
  any `Ar` whose `compileUnary` is `compileUnaryP` (the hit branch and the glue are proved);
* **`compileUnaryP_gate`**: the straight `compileUnaryP` returns is `finishLUCM env n`, from the
  conclusion of `cu_gate_dir_scc` (the content of the link: the model's whole-subject compile);
* `PGoodK`: what track P's `PGood` must also carry for the hypotheses `hE0`, `hR0` and `SccsGood`
  of `cu_gate_dir_scc` (before the poke's own `+compile-scc-in`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.Comp SkaModel.PokeM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The arms -/

/-- `s=(~(get by mono.cache.state) b)`. -/
def monoGetF : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 4194303)))) (C (A 9) (C (A 764) (C (A 10)
    (C (C (A 6) (C (A 0) (A 2014))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28)))
    (C (A 0) (A 2)))))))

/-- `?=(@ s)` as `?^`. -/
def monoTestF : Noun := C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))

/-- The sample `[b scc [code jets calls]:long-ska jets-hot cache]`. -/
def monoSamF : Noun :=
  C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 28)) (C (C (A 0) (A 29)) (C (C (A 7) (C (C (A 0) (A 250))
    (C (C (A 0) (A 14)) (C (C (A 0) (A 2)) (C (A 0) (A 30)))))) (C (C (A 0) (A 502)) (C (A 0) (A 503)))))))

/-- `(~(put by mono.cache) b straight)`. -/
def monoPutF : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 16777215)))) (C (A 9) (C (A 340) (C (A 10)
    (C (C (A 6) (C (A 0) (A 8158))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (C (A 0) (A 124)) (C (A 0) (A 12)))) (C (A 0) (A 2)))))))

/-- The miss: the slam of `+compile-unary` (on the sample `monoSamF`), the write of `cache`, the
`+put:by` (`monoPutF`). -/
def monoMissF : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 2810) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 28)) (C (C (A 0) (A 29)) (C (C (A 7) (C (C (A 0) (A 250)) (C (C (A 0) (A 14)) (C (C (A 0) (A 2)) (C (A 0) (A 30)))))) (C (C (A 0) (A 502)) (C (A 0) (A 503))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1015) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 0) (A 4)) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 16777215)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 8158))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 12)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1015)))))))))))))

/-- `[u.s cache.state]`. -/
def monoHitF : Noun := C (C (A 0) (A 5)) (C (A 0) (A 503))

/-- The battery of `+compiled-mono`. -/
def monoBat : Noun := C (A 8) (C monoGetF (C (A 6) (C monoTestF (C monoMissF monoHitF))))

def monoBunt : Noun := C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0)

/-- **The arm `10` of the core at axis `3`**, a kernel fact. -/
theorem monoArm_eq : slot? 10 (C corB6 (A 0)) = some (C (A 8) (C (C (A 1) monoBunt) (C (C (A 1) monoBat) (C (A 0) (A 1))))) := by
  kernel_rfl

theorem slot10_corB6 (X : Noun) : slot? 10 (C corB6 X) = slot? 10 (C corB6 (A 0)) := rfl

/-- The sample bunt of `+compile-unary`'s gate. -/
noncomputable def cuArmBunt : Noun := (slot? 89941 compK).getD (A 0)

def cuHint : Noun :=
  C (A 1953718630) (C (A 1) (C (A 9622006742771974117872848695139) (C (C (A 0) (A 32767)) (A 0))))

/-- **The arm `2810` of `K`** (`+compile-unary`), a kernel fact. -/
theorem cuArm_at : slot? 2810 compK = some (C (A 7) (C (C (A 8) (C (C (A 1) cuArmBunt) (C (C (A 1) cuGB) (C (A 0) (A 1)))))
    (C (A 11) (C cuHint (C (A 0) (A 1)))))) := by kernel_rfl

theorem corLib_compK : slot? 7 corLib = some compK := by rw [corLib_sccCore, sccCore_compK]

/-! ## The arm on encoded states -/

/-- The gate of `+compile-unary` slammed on a sample. -/
def cuG (SAM : Noun) : Option Noun := nock (C cuGB (C SAM compK)) cuGB

/-- The sample `+compiled-mono` builds on an encoded state. -/
noncomputable def monoSam (fl : Flags) (st : PSt) (func sc : Noun) : Noun :=
  cuSam func sc (codeNoun fl st.long.code) (C st.jets (callsNoun st.long)) st.hot (cacheNoun st.cache)

theorem enc_slot3 (fl : Flags) (st : PSt) : slot? 3 (enc fl st) = some (C corB6 (C (stNoun fl st) corLib)) := by
  simp [enc, nock_exec]

/-- **The hit**: `mono.cache` has `u` for `func`. -/
theorem monoRaw_hit (fl : Flags) (st : PSt) (func sc u : Noun)
    (h : getF mugF func (st.cache.mono.toNoun Straight.toNoun) = some (C (A 0) u)) :
    monoRaw (enc fl st) func sc = some (C u (cacheNoun st.cache)) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := get_gate layer2 hgc func _ _ h
  have hL := corLib_hoon
  have ha := monoArm_eq
  rw [← slot10_corB6 (C (stNoun fl st) corLib)] at ha
  simp only [monoRaw, enc_slot3, Option.bind_some, gateAt, ha]
  unfold slamG monoBat monoGetF monoTestF monoHitF
  simp [nock_exec, stNoun, cacheNoun, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hL]

/-! ## The pill's `+compile-unary` read back -/

/-- The noun of a result of `+compile-unary`: `[[straight n-ary] cache]`. -/
noncomputable def cuResNoun (r : (Straight (TreapMap mugF) × FinMap Bell (Straight (TreapMap mugF))) ×
    Cache FinMap (TreapMap mugF) (Noun × Noun)) : Noun :=
  C (C r.1.1.toNoun (r.1.2.toNoun Straight.toNoun)) (cacheNoun r.2)

/-- **`+compile-unary` read back** on the encoded sample: the model result whose noun the gate
returns, when there is one. -/
noncomputable def compileUnaryP (fl : Flags) (b : Bell) (sc : FinMap Bell Unit) (L : LongB FinMap) (j h : Noun)
    (c : Cache FinMap (TreapMap mugF) (Noun × Noun)) :
    Option ((Straight (TreapMap mugF) × FinMap Bell (Straight (TreapMap mugF))) × Cache FinMap (TreapMap mugF) (Noun × Noun)) :=
  open Classical in
  if hx : ∃ r, cuG (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl L.code) (C j (callsNoun L)) h (cacheNoun c))
      = some (cuResNoun r) then some (Classical.choose hx) else none

/-- **The miss branch of `+compiled-mono` at a state** (named; the hit is `monoRaw_hit`): when
`mono.cache` has no entry for `b`, the arm returns `[straight cache]` with the cache `+compile-unary`
returned and `b` put into its `mono`, and it crashes when the gate of `+compile-unary` does.  The
pushes are those of `monoMissF` (the call `[9 2810 [0 255]]` on `monoSamF`, the edit at `1015`,
`monoPutF` with `put_gate`); one `simp` over them did not close (README Gaps 19 (g)). -/
def MonoMissAt (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit) : Prop :=
  getF mugF b.toNoun (st.cache.mono.toNoun Straight.toNoun) = some (A 0) →
    (cuG (monoSam fl st b.toNoun (FinMap.setNoun sc)) = none → monoRaw (enc fl st) b.toNoun (FinMap.setNoun sc) = none) ∧
    ∀ r, cuG (monoSam fl st b.toNoun (FinMap.setNoun sc)) = some (cuResNoun r) →
      monoRaw (enc fl st) b.toNoun (FinMap.setNoun sc) =
        some (C r.1.1.toNoun (cacheNoun { r.2 with mono := FinMap.put r.2.mono b r.1.1 }))

/-- **The image of `+compile-unary` at a state** (the analogue of `SccImage`): the gate's product
on the encoded sample, when it returns, is the noun of a model result.  `cu_gate_dir_scc` gives
the product `[[st NM] CA']`; what is left is that `NM` (track I's `M`) and `CA'` decode. -/
def UnaryImageAt (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit) : Prop :=
  ∀ out, cuG (monoSam fl st b.toNoun (FinMap.setNoun sc)) = some out → ∃ r, out = cuResNoun r

theorem enc_edit119 (fl : Flags) (st : PSt) (c : Cache FinMap (TreapMap mugF) (Noun × Noun)) :
    edit? 119 (cacheNoun c) (enc fl st) = some (enc fl { st with cache := c }) := by
  simp [enc, stNoun, cacheNoun, nock_exec]

/-- **`MonoLinkAt` from the image of `+compile-unary`** (the 125 cells of `+compiled-mono`
linked): for every `Ar` whose `compileUnary` is the pill's read back. -/
theorem monoLinkAt_of (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (hA : Ar.compileUnary = compileUnaryP fl) (st : PSt) (b : Bell) (sc : FinMap Bell Unit)
    (hU : UnaryImageAt fl st b sc) (hM : MonoMissAt fl st b sc) : MonoLinkAt fl Ar st b sc := by
  unfold MonoLinkAt monoP compiledMono
  have hgt := FinMap.getF_toNoun Straight.toNoun st.cache.mono b
  cases e : Treap.get st.cache.mono b with
  | some s =>
    have e' : FinMap.get st.cache.mono b = some s := e
    rw [e'] at hgt
    rw [monoRaw_hit fl st b.toNoun (FinMap.setNoun sc) s.toNoun hgt]
    simp only [Option.bind_some, Option.map_some]
    rw [enc_edit119]
    rfl
  | none =>
    have e' : FinMap.get st.cache.mono b = none := e
    rw [e'] at hgt
    rw [hA]
    unfold compileUnaryP
    by_cases hx : ∃ r, cuG (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long))
        st.hot (cacheNoun st.cache)) = some (cuResNoun r)
    · rw [dif_pos hx]
      have hr := Classical.choose_spec hx
      generalize Classical.choose hx = r at hr
      rw [(hM hgt).2 r hr]
      simp only [Option.bind_some, Option.map_some]
      rw [enc_edit119]
      rfl
    · rw [dif_neg hx]
      cases hc : cuG (monoSam fl st b.toNoun (FinMap.setNoun sc)) with
      | none =>
        rw [(hM hgt).1 hc]
        rfl
      | some out =>
        obtain ⟨r, rfl⟩ := hU out hc
        exact absurd ⟨r, hc⟩ hx

/-! ## The content: the straight is the model's -/

/-- **The straight of `compileUnaryP` is `finishLUCM env n`**: whenever the gate returns
`[[st NM] CA']` with `st` the model's straight (the conclusion of `cu_gate_dir_scc` on the encoded
sample), the result read back holds that straight (`straight_toNoun_inj`). -/
theorem compileUnaryP_gate (fl : Flags) (b : Bell) (sc : FinMap Bell Unit) (L : LongB FinMap) (j h : Noun)
    (c : Cache FinMap (TreapMap mugF) (Noun × Noun)) (env : CallEnv) (n : Nomm) (NM CA' : Noun)
    (hg : cuG (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl L.code) (C j (callsNoun L)) h (cacheNoun c))
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA')
    (r : (Straight (TreapMap mugF) × FinMap Bell (Straight (TreapMap mugF))) × Cache FinMap (TreapMap mugF) (Noun × Noun))
    (hr : compileUnaryP fl b sc L j h c = some r) :
    finishLUCM (S := CSet) (Map := TreapMap mugF) env n = some r.1.1 := by
  unfold compileUnaryP at hr
  split at hr
  · rename_i hx
    cases hr
    have hs := Classical.choose_spec hx
    generalize Classical.choose hx = r0 at hs ⊢
    rw [hg] at hs
    cases e : finishLUCM (S := CSet) (Map := TreapMap mugF) env n with
    | none => rw [e] at hs; cases hs
    | some st =>
      rw [e] at hs
      simp only [Option.map_some, Option.some.injEq, cuResNoun, Noun.cell.injEq] at hs
      rw [straight_toNoun_inj hs.1.1]
  · cases hr

/-! ## What `PGood` must also carry -/

/-- **The clauses track P's `PGood` must add for `cu_gate_dir_scc`** (README Gaps 19 (g)), at the
state `+compiled-mono` is called on (after the poke's `+scc-of`): the invariant `AgreeE` on the
encoded cache for the poke's `env` (`sure` a map, every key of `sure` a key of `nary`, the needs
and sure needs of the entries `env`'s: free by `enc` for `nary`, which is `FinMap.toNoun` of
straights, a statement on the raw noun `sure`), the rest predicate `RK` (`sccs` is the
encoded `sccs`, `inl` a map whose entries are the nomms of `+inlined`, `nary`'s keys a union of
whole SCCs), the meaning of `sccs` (`SccsGood`, `+tarjan`), and `calls` a jug.  Track I's loop on
the poke's SCC carries them to the cache `CA` of `hcsi`, where `cu_gate_dir_scc` takes them as
`hE0`, `hR0`. -/
structure PGoodK (env : CallEnv) (inl : Noun → Option Nomm) (st : PSt) : Prop where
  agree : AgreeE env (cuRest (cacheNoun st.cache))
  rest : RK (sccsNoun st.cache.sccs) inl (cuRest (cacheNoun st.cache))
  sccs : SccsGood (sccsNoun st.cache.sccs)
  calls : IsMap mugF (callsNoun st.long) ∧ ∀ k v, Get (callsNoun st.long) k v → IsSet mugF v

end Compiler
end Formalization
