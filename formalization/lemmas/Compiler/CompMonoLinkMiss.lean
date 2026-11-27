import lemmas.Compiler.CompMonoLink

/-!
# The miss branch of `+compiled-mono` (README Gaps 19 (g))

`monoMissF` is `[7 [0 1] [8 [7 [0 1] monoSlamF] monoTailF]]`, cut here into its three pushes,
one lemma each:
* `mono_slam`: the slam `[9 2810 [0 255]]` of `+compile-unary` (arm `2810` of `K`, `cuArm_at`)
  on the sample `monoSamF`: `cuG (monoSam ..)`;
* `mono_tail`: the edit of `cache` at `1015` with the product's cache, and `monoPutF`
  (`+put:by` of `mono`, `put_gate`): `[straight cache']` with `mono` of the new cache put;
* `monoRaw_miss`: the arm on a miss (`getF` of `mono` gives `~`) is the slam, then the tail;
* **`monoMissAt_of`**: `MonoMissAt` at every state (`putF_toNoun`);
* `unaryImageAt_of_gate`: `UnaryImageAt` from the gate's product in the form of
  `cu_gate_dir_scc` (`[[st NM] CA']`), when `NM` decodes as a map of straights and `CA'` as a cache;
* **`monoLinkGood_of_image`**: track P's `MonoLinkGood` from `Ar.compileUnary = compileUnaryP fl` and
  `UnaryImageAt` at every `PGood` state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.Comp SkaModel.PokeM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The slam of `+compile-unary` on `monoSamF`. -/
def monoSlamF : Noun :=
  C (A 8) (C (C (A 9) (C (A 2810) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) monoSamF) (C (A 0) (A 2)))))))

/-- The write of `cache` at `1015` and `[straight (~(put by mono) b straight)]`. -/
def monoTailF : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 1015) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
    (C (C (A 0) (A 4)) (C (A 10) (C (C (A 6) monoPutF) (C (A 0) (A 1015))))))))

theorem monoMissF_eq : monoMissF = C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) monoSlamF))
    monoTailF))) := rfl

/-- The subject of `monoBat` on the sample `[func sc]`. -/
noncomputable def monoS0 (fl : Flags) (st : PSt) (func sc : Noun) : Noun :=
  C monoBat (C (C func sc) (C corB6 (C (stNoun fl st) corLib)))

/-- **The slam of `+compile-unary`** (`[9 2810 [0 255]]` and the sample `monoSamF`) on the
subject `[s monoS0]`, for any `s`. -/
theorem mono_slam (fl : Flags) (st : PSt) (func sc s : Noun) :
    nock (C s (monoS0 fl st func sc)) monoSlamF = cuG (monoSam fl st func sc) := by
  have hK := corLib_compK
  have ha := cuArm_at
  unfold cuG monoSam cuSam
  unfold monoSlamF monoSamF monoS0
  generalize cuArmBunt = BU at ha ⊢
  generalize cuGB = G at ha ⊢
  generalize compK = KC at hK ha ⊢
  generalize corLib = LIB at hK ⊢
  simp [nock_exec, stNoun, longNoun, callsNoun, hK, ha, cuHint]

/-- **The tail of the miss**: on `[[ST NM] CA']` (`CA'` a cache `[NR MO REST]`), the write of
`cache` and the `+put:by` of `mono`. -/
theorem mono_tail (fl : Flags) (st : PSt) (func sc s ST NM NR MO REST MO' : Noun)
    (hp : putF mugF func ST MO = some MO') :
    nock (C (C (C ST NM) (C NR (C MO REST))) (C s (monoS0 fl st func sc))) monoTailF
      = some (C ST (C NR (C MO' REST))) := by
  have hL := corLib_hoon
  have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 func ST MO MO' hp
  unfold monoTailF monoPutF monoS0
  simp [nock_exec, stNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hpg]

/-- The push of `s=(~(get by mono.cache.state) b)` on a miss. -/
theorem mono_get (fl : Flags) (st : PSt) (func sc : Noun)
    (h : getF mugF func (st.cache.mono.toNoun Straight.toNoun) = some (A 0)) :
    nock (monoS0 fl st func sc) monoGetF = some (A 0) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := get_gate layer2 hgc func _ _ h
  have hL := corLib_hoon
  unfold monoS0 monoGetF
  simp [nock_exec, stNoun, cacheNoun, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hL]

theorem monoBat_eq : monoBat = C (A 8) (C monoGetF (C (A 6) (C monoTestF (C monoMissF monoHitF)))) := rfl

/-- **The arm on a miss**: the slam, then the tail on its product. -/
theorem monoRaw_miss (fl : Flags) (st : PSt) (func sc : Noun)
    (h : getF mugF func (st.cache.mono.toNoun Straight.toNoun) = some (A 0)) :
    monoRaw (enc fl st) func sc = (cuG (monoSam fl st func sc)).bind fun out =>
      nock (C out (C (A 0) (monoS0 fl st func sc))) monoTailF := by
  have ha := monoArm_eq
  rw [← slot10_corB6 (C (stNoun fl st) corLib)] at ha
  have hget := mono_get fl st func sc h
  have hs := mono_slam fl st func sc (A 0)
  have h0 : monoRaw (enc fl st) func sc = nock (monoS0 fl st func sc) monoBat := by
    simp only [monoRaw, enc_slot3, Option.bind_some, gateAt, ha]
    unfold slamG monoS0
    simp [nock_exec]
  rw [h0, monoBat_eq, monoMissF_eq]
  generalize monoS0 fl st func sc = S0 at hget hs ⊢
  generalize monoSlamF = SL at hs ⊢
  generalize monoTailF = TL
  unfold monoTestF
  cases e : cuG (monoSam fl st func sc) with
  | none =>
    rw [e] at hs
    simp [nock_exec, hget, hs]
  | some out =>
    rw [e] at hs
    simp [nock_exec, hget, hs]

/-- **`MonoMissAt` holds at every state**: the miss branch of `+compiled-mono` is the slam of
`+compile-unary`, the write of its cache and the `+put:by` of `mono` (`putF_toNoun`). -/
theorem monoMissAt_of (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit) : MonoMissAt fl st b sc := by
  intro h
  rw [monoRaw_miss fl st b.toNoun (FinMap.setNoun sc) h]
  refine ⟨fun hc => by rw [hc]; rfl, fun r hr => ?_⟩
  rw [hr, Option.bind_some]
  have hp := FinMap.putF_toNoun Straight.toNoun r.2.mono b r.1.1
  exact mono_tail fl st b.toNoun (FinMap.setNoun sc) (A 0) r.1.1.toNoun (r.1.2.toNoun Straight.toNoun)
    (r.2.nary.toNoun Straight.toNoun) (r.2.mono.toNoun Straight.toNoun)
    (C (r.2.sccs.toNoun FinMap.setNoun) (C r.2.rest.1 r.2.rest.2)) _ hp

/-- **`UnaryImageAt` from the gate** (the conclusion of `cu_gate_dir_scc` on the encoded sample,
`cuG` being its `nock (C cuGB (C SAM compK)) cuGB`): the product `[[st NM] CA']` is the noun of a
model result when `NM` is the noun of a map of straights (track I's `M`) and every `CA'` the gate
may return (`P`) is the noun of a cache. -/
theorem unaryImageAt_of_gate (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit) (env : CallEnv) (n : Nomm)
    (NM : Noun) (P : Noun → Prop)
    (hg : ∃ CA', P CA' ∧ cuG (monoSam fl st b.toNoun (FinMap.setNoun sc))
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun s => C (C s.toNoun NM) CA')
    (hNM : ∃ m : FinMap Bell (Straight (TreapMap mugF)), NM = m.toNoun Straight.toNoun)
    (hCA : ∀ CA', P CA' → ∃ c : Cache FinMap (TreapMap mugF) (Noun × Noun), CA' = cacheNoun c) :
    UnaryImageAt fl st b sc := by
  intro out ho
  obtain ⟨CA', hP, hg⟩ := hg
  rw [hg] at ho
  obtain ⟨m, rfl⟩ := hNM
  obtain ⟨c, rfl⟩ := hCA CA' hP
  cases e : finishLUCM (S := CSet) (Map := TreapMap mugF) env n with
  | none => rw [e] at ho; cases ho
  | some s =>
    rw [e] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    exact ⟨((s, m), c), ho.symm⟩

/-- **`MonoLinkGood` (track P's hypothesis) from the image of `+compile-unary`**: the 125 cells of
`+compiled-mono` are linked (`monoLinkAt_of`, `monoMissAt_of`), so what is left is that `Ar` reads
`+compile-unary` back (`hA`, by the choice of `Ar`) and that the gate's product decodes at every
`PGood` state (`UnaryImageAt`, from `unaryImageAt_of_gate` and `cu_gate_dir_scc`). -/
theorem monoLinkGood_of_image (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hA : Ar.compileUnary = compileUnaryP fl)
    (hU : ∀ st b sc, PGood Cls st → UnaryImageAt fl st b sc) : MonoLinkGood fl Ar Cls :=
  fun st b sc hg => monoLinkAt_of fl Ar hA st b sc (hU st b sc hg) (monoMissAt_of fl st b sc)

end Compiler
end Formalization
